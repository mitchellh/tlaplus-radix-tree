This module verifies the SeekLowerBound algorithm in the go-immutable-radix
Go library (https://github.com/hashicorp/go-immutable-radix).

------------------------ MODULE RadixSeekLowerBound ------------------------
EXTENDS FiniteSets, Integers, Sequences, TLC

\* Set of characters to use for the alphabet of generated strings.
CONSTANT Alphabet

\* CmpOp is the comparison operator for ordered iteration. This should be TRUE
\* if the first value is less than the second value. This is called on a single
\* element of a sequence.
CONSTANT CmpOp(_,_)

\* Length of input strings generated
CONSTANT MinLength, MaxLength
ASSUME 
  /\ {MinLength, MaxLength} \subseteq Nat
  /\ MinLength <= MaxLength

\* Number of unique elements to construct the radix tree with. This
\* is a set of numbers so you can test with inputs of multiple sizes.
CONSTANT ElementCounts
ASSUME ElementCounts \subseteq Nat

INSTANCE RadixTrees
INSTANCE RadixIterator
  
\* Inputs is the set of input strings valid for the tree.
Inputs == UNION { [1..n -> Alphabet]: n \in MinLength..MaxLength }

\* InputSets is the full set of possible inputs we can send to the radix tree.
InputSets == { T \in SUBSET Inputs: Cardinality(T) \in ElementCounts }

-----------------------------------------------------------------------------

\* TRUE iff the sequence s contains no duplicates. Copied from CommunityModules.
isInjective(s) == \A i, j \in DOMAIN s: (s[i] = s[j]) => (i = j)

\* Converts a set to a sequence that contains all the elements of S exactly once.
\* Copied from CommunityModules.
setToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : isInjective(f)

\* bytes.Compare in Go
RECURSIVE GoBytesCompare(_,_)     
GoBytesCompare(X, Y) ==
  CASE X = Y           -> 0
    [] Len(X) = 0      -> -1
    [] Len(Y) = 0      -> 1
    [] OTHER -> 
      IF X[1] = Y[1] 
        THEN GoBytesCompare(Tail(X), Tail(Y))
        ELSE IF CmpOp(X[1], Y[1]) THEN -1 ELSE 1

\* CmpSeq compares two full inputs whereas CmpOp compares only a single element
\* of the alphabet.
CmpSeq(X, Y) == GoBytesCompare(X, Y) <= 0

\* CmpGte is checks if X >= Y
CmpGte(X, Y) == X = Y \/ ~CmpOp(X, Y)
        
\* Sorted edges based on CmpOp
SortedEdgeLabels(Node) == SortSeq(setToSeq(DOMAIN Node.Edges), CmpOp)
 
\* Returns the index of the first edge 
GetLowerBoundEdgeIndex(Node, Label) ==
  IF ~\E e \in DOMAIN Node.Edges: e = Label \/ ~CmpOp(e, Label) THEN 0
    \* if there is no lower bound edge, return 0
  ELSE LET
    e == SortedEdgeLabels(Node)
      \* sorted edges
  IN CHOOSE idx \in 1..Len(e): \* find the index
    /\ CmpGte(e[idx], Label)   \* >= to our search label
    /\ \/ idx = 1              \* and its the first element that is gte
       \/ CmpOp(e[idx-1], Label)

-----------------------------------------------------------------------------

\* The expected value is the sorted set of all inputs where the element 
\* is greater than or equal to the given key.
\*
\* EXPLANATION: 
\*   1. We convert the input set to a sequence
\*   2. Sort the input sequence, this is all inputs sorted now.
\*   3. Select the subset of the input sequence where it satisfies our comparison.
\*      The sequence now only has elements greater than or equal to our key
Expected(input, key) == 
  SelectSeq(SortSeq(setToSeq(input), CmpSeq), LAMBDA elem: CmpSeq(key, elem))
  
(*--algorithm seek_lower_bound
variables 
  stack = <<>>,
  input \in InputSets,
  key \in Inputs,
  root = RadixTree(input),
  node = {},
  search = {},
  result = {},
  prefixCmp = "UNSET";

\* This entire algorith is almost 1:1 translated where possible from the
\* actual implementation in iter.go. That's the point: we're trying to verify
\* our algorithm is correct for all inputs.
\*
\* Source: https://github.com/hashicorp/go-immutable-radix/blob/f63f49c0b598a5ead21c5015fb4d08fe7e3c21ea/iter.go#L77
begin
  \* I could've just set these variables in the initializer above but
  \* to better closely match the algorithm, I reset them here.
Begin:
  stack := <<>>;
  node := root;
  search := key;

Seek:
  while TRUE do
    if Len(node.Prefix) < Len(search) then
      prefixCmp := GoBytesCompare(node.Prefix, SubSeq(search, 1, Len(node.Prefix)));
    else
      prefixCmp := GoBytesCompare(node.Prefix, search);
    end if;
        
    if prefixCmp < 0 then
      goto Result;
    elsif prefixCmp > 0 then
    RecurseMin:
      while Len(node.Value) = 0 do
        with 
          labels = SortedEdgeLabels(node),
          edges  = [ n \in 1..Len(labels) |-> node.Edges[labels[n]] ]
        do
          if Len(edges) > 0 then
            stack := stack \o SubSeq(edges, 2, Len(edges));
            node := edges[1];
          else
            \* shouldn't be possible
            goto Result;
          end if;
        end with; 
      end while;
      
      stack := stack \o <<node>>;
      goto Result;
    end if;
    
  Search:
    if Len(node.Value) > 0 then
      if GoBytesCompare(node.Value, key) < 0 then
        goto Result;
      end if;
      
    SearchMatch:
      stack := stack \o <<node>>;
      goto Result;
    end if;
    
  Consume:
    if Len(node.Prefix) > Len(search) then
      search := <<>>;
    else
      search := SubSeq(search, Len(node.Prefix)+1, Len(search))
    end if;
    
    with 
      idx = GetLowerBoundEdgeIndex(node, search[1]), 
      labels = SortedEdgeLabels(node),
      edges = [ n \in 1..Len(labels) |-> node.Edges[labels[n]] ]
    do
      if idx = 0 then
        goto Result;
      else
        if idx+1 <= Len(edges) then
          stack := stack \o SubSeq(edges, idx+1, Len(edges));
        end if;

        node := edges[idx];
      end if;
    end with;
    
  end while;
  
Result:
  result := Iterate(stack);
  
CheckResult:
  assert result = Expected(input, key);
end algorithm; *)

-----------------------------------------------------------------------------

\* !!! NOTE !!! The rest of the file is auto-generated based on the PlusCal
\* above. For those who are reading this to learn TLA+/PlusCal, you can stop
\* reading here.

\* BEGIN TRANSLATION (chksum(pcal) = "c021d80a" /\ chksum(tla) = "20123e42")
VARIABLES stack, input, key, root, node, search, result, prefixCmp, pc

vars == << stack, input, key, root, node, search, result, prefixCmp, pc >>

Init == (* Global variables *)
        /\ stack = <<>>
        /\ input \in InputSets
        /\ key \in Inputs
        /\ root = RadixTree(input)
        /\ node = {}
        /\ search = {}
        /\ result = {}
        /\ prefixCmp = "UNSET"
        /\ pc = "Begin"

Begin == /\ pc = "Begin"
         /\ stack' = <<>>
         /\ node' = root
         /\ search' = key
         /\ pc' = "Seek"
         /\ UNCHANGED << input, key, root, result, prefixCmp >>

Seek == /\ pc = "Seek"
        /\ IF Len(node.Prefix) < Len(search)
              THEN /\ prefixCmp' = GoBytesCompare(node.Prefix, SubSeq(search, 1, Len(node.Prefix)))
              ELSE /\ prefixCmp' = GoBytesCompare(node.Prefix, search)
        /\ IF prefixCmp' < 0
              THEN /\ pc' = "Result"
              ELSE /\ IF prefixCmp' > 0
                         THEN /\ pc' = "RecurseMin"
                         ELSE /\ pc' = "Search"
        /\ UNCHANGED << stack, input, key, root, node, search, result >>

Search == /\ pc = "Search"
          /\ IF Len(node.Value) > 0
                THEN /\ IF GoBytesCompare(node.Value, key) < 0
                           THEN /\ pc' = "Result"
                           ELSE /\ pc' = "SearchMatch"
                ELSE /\ pc' = "Consume"
          /\ UNCHANGED << stack, input, key, root, node, search, result, 
                          prefixCmp >>

SearchMatch == /\ pc = "SearchMatch"
               /\ stack' = stack \o <<node>>
               /\ pc' = "Result"
               /\ UNCHANGED << input, key, root, node, search, result, 
                               prefixCmp >>

Consume == /\ pc = "Consume"
           /\ IF Len(node.Prefix) > Len(search)
                 THEN /\ search' = <<>>
                 ELSE /\ search' = SubSeq(search, Len(node.Prefix)+1, Len(search))
           /\ LET idx == GetLowerBoundEdgeIndex(node, search'[1]) IN
                LET labels == SortedEdgeLabels(node) IN
                  LET edges == [ n \in 1..Len(labels) |-> node.Edges[labels[n]] ] IN
                    IF idx = 0
                       THEN /\ pc' = "Result"
                            /\ UNCHANGED << stack, node >>
                       ELSE /\ IF idx+1 <= Len(edges)
                                  THEN /\ stack' = stack \o SubSeq(edges, idx+1, Len(edges))
                                  ELSE /\ TRUE
                                       /\ stack' = stack
                            /\ node' = edges[idx]
                            /\ pc' = "Seek"
           /\ UNCHANGED << input, key, root, result, prefixCmp >>

RecurseMin == /\ pc = "RecurseMin"
              /\ IF Len(node.Value) = 0
                    THEN /\ LET labels == SortedEdgeLabels(node) IN
                              LET edges == [ n \in 1..Len(labels) |-> node.Edges[labels[n]] ] IN
                                IF Len(edges) > 0
                                   THEN /\ stack' = stack \o SubSeq(edges, 2, Len(edges))
                                        /\ node' = edges[1]
                                        /\ pc' = "RecurseMin"
                                   ELSE /\ pc' = "Result"
                                        /\ UNCHANGED << stack, node >>
                    ELSE /\ stack' = stack \o <<node>>
                         /\ pc' = "Result"
                         /\ node' = node
              /\ UNCHANGED << input, key, root, search, result, prefixCmp >>

Result == /\ pc = "Result"
          /\ result' = Iterate(stack)
          /\ pc' = "CheckResult"
          /\ UNCHANGED << stack, input, key, root, node, search, prefixCmp >>

CheckResult == /\ pc = "CheckResult"
               /\ Assert(result = Expected(input, key), 
                         "Failure of assertion at line 185, column 3.")
               /\ pc' = "Done"
               /\ UNCHANGED << stack, input, key, root, node, search, result, 
                               prefixCmp >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Begin \/ Seek \/ Search \/ SearchMatch \/ Consume \/ RecurseMin
           \/ Result \/ CheckResult
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Thu Jul 01 22:21:38 PDT 2021 by mitchellh
\* Created Thu Jul 01 10:43:00 PDT 2021 by mitchellh
