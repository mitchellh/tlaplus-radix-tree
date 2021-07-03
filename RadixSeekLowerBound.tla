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

\* CmpGte checks if X >= Y
CmpGte(X, Y) == X = Y \/ ~CmpOp(X, Y)
        
\* Sorted edge labels based on CmpOp.
SortedEdgeLabels(Node) == SortSeq(setToSeq(DOMAIN Node.Edges), CmpOp)
 
\* Returns the index of the first element that is greater than or equal to
\* to the search label.
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
  iterStack = <<>>,
  input \in InputSets,
  key \in Inputs,
  root = RadixTree(input),
  node = {},
  search = {},
  result = {},
  prefixCmp = "UNSET";
  
\* findMin as implemented in Go
procedure findMin() begin
FindMin:
  while Len(node.Value) = 0 do
    with 
      labels = SortedEdgeLabels(node),
      edges  = [ n \in 1..Len(labels) |-> node.Edges[labels[n]] ]
    do
      if Len(edges) > 1 then
        iterStack := iterStack \o SubSeq(edges, 2, Len(edges));
      end if;
      
      if Len(edges) > 0 then
        \* recurse again
        node := edges[1];
      else
        \* shouldn't be possible
        return;
      end if;
    end with; 
  end while;
      
  iterStack := iterStack \o <<node>>;
  return;
end procedure;


\* This entire algorith is almost 1:1 translated where possible from the
\* actual implementation in iter.go. That's the point: we're trying to verify
\* our algorithm is correct for all inputs.
\*
\* Source: https://github.com/hashicorp/go-immutable-radix/blob/f63f49c0b598a5ead21c5015fb4d08fe7e3c21ea/iter.go#L77
begin
  \* I could've just set these variables in the initializer above but
  \* to better closely match the algorithm, I reset them here.
Begin:
  iterStack := <<>>;
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
      call findMin();
      goto Result;
    end if;
    
  Search:
    if Len(node.Value) > 0 /\ node.Value = key then
      iterStack := iterStack \o <<node>>;
      goto Result;
    end if;
    
  Consume:
    search := SubSeq(search, Len(node.Prefix)+1, Len(search));
    
    if Len(search) = 0 then
      call findMin();
      goto Result;
    end if;
  
  NextEdge:
    with 
      idx = GetLowerBoundEdgeIndex(node, search[1]), 
      labels = SortedEdgeLabels(node),
      edges = [ n \in 1..Len(labels) |-> node.Edges[labels[n]] ]
    do
      if idx = 0 then
        goto Result;
      else
        if idx+1 <= Len(edges) then
          iterStack := iterStack \o SubSeq(edges, idx+1, Len(edges));
        end if;

        node := edges[idx];
      end if;
    end with;
    
  end while;
  
Result:
  result := Iterate(iterStack);
  
CheckResult:
  assert result = Expected(input, key);
end algorithm; *)

-----------------------------------------------------------------------------

\* !!! NOTE !!! The rest of the file is auto-generated based on the PlusCal
\* above. For those who are reading this to learn TLA+/PlusCal, you can stop
\* reading here.

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-cb91b4d39230aef775d25233214cbd22
VARIABLES iterStack, input, key, root, node, search, result, prefixCmp, pc, 
          stack

vars == << iterStack, input, key, root, node, search, result, prefixCmp, pc, 
           stack >>

Init == (* Global variables *)
        /\ iterStack = <<>>
        /\ input \in InputSets
        /\ key \in Inputs
        /\ root = RadixTree(input)
        /\ node = {}
        /\ search = {}
        /\ result = {}
        /\ prefixCmp = "UNSET"
        /\ stack = << >>
        /\ pc = "Begin"

FindMin == /\ pc = "FindMin"
           /\ IF Len(node.Value) = 0
                 THEN /\ LET labels == SortedEdgeLabels(node) IN
                           LET edges == [ n \in 1..Len(labels) |-> node.Edges[labels[n]] ] IN
                             /\ IF Len(edges) > 1
                                   THEN /\ iterStack' = iterStack \o SubSeq(edges, 2, Len(edges))
                                   ELSE /\ TRUE
                                        /\ UNCHANGED iterStack
                             /\ IF Len(edges) > 0
                                   THEN /\ node' = edges[1]
                                        /\ pc' = "FindMin"
                                        /\ stack' = stack
                                   ELSE /\ pc' = Head(stack).pc
                                        /\ stack' = Tail(stack)
                                        /\ node' = node
                 ELSE /\ iterStack' = iterStack \o <<node>>
                      /\ pc' = Head(stack).pc
                      /\ stack' = Tail(stack)
                      /\ node' = node
           /\ UNCHANGED << input, key, root, search, result, prefixCmp >>

findMin == FindMin

Begin == /\ pc = "Begin"
         /\ iterStack' = <<>>
         /\ node' = root
         /\ search' = key
         /\ pc' = "Seek"
         /\ UNCHANGED << input, key, root, result, prefixCmp, stack >>

Seek == /\ pc = "Seek"
        /\ IF Len(node.Prefix) < Len(search)
              THEN /\ prefixCmp' = GoBytesCompare(node.Prefix, SubSeq(search, 1, Len(node.Prefix)))
              ELSE /\ prefixCmp' = GoBytesCompare(node.Prefix, search)
        /\ IF prefixCmp' < 0
              THEN /\ pc' = "Result"
                   /\ stack' = stack
              ELSE /\ IF prefixCmp' > 0
                         THEN /\ stack' = << [ procedure |->  "findMin",
                                               pc        |->  "Result" ] >>
                                           \o stack
                              /\ pc' = "FindMin"
                         ELSE /\ pc' = "Search"
                              /\ stack' = stack
        /\ UNCHANGED << iterStack, input, key, root, node, search, result >>

Search == /\ pc = "Search"
          /\ IF Len(node.Value) > 0 /\ node.Value = key
                THEN /\ iterStack' = iterStack \o <<node>>
                     /\ pc' = "Result"
                ELSE /\ pc' = "Consume"
                     /\ UNCHANGED iterStack
          /\ UNCHANGED << input, key, root, node, search, result, prefixCmp, 
                          stack >>

Consume == /\ pc = "Consume"
           /\ search' = SubSeq(search, Len(node.Prefix)+1, Len(search))
           /\ IF Len(search') = 0
                 THEN /\ stack' = << [ procedure |->  "findMin",
                                       pc        |->  "Result" ] >>
                                   \o stack
                      /\ pc' = "FindMin"
                 ELSE /\ pc' = "NextEdge"
                      /\ stack' = stack
           /\ UNCHANGED << iterStack, input, key, root, node, result, 
                           prefixCmp >>

NextEdge == /\ pc = "NextEdge"
            /\ LET idx == GetLowerBoundEdgeIndex(node, search[1]) IN
                 LET labels == SortedEdgeLabels(node) IN
                   LET edges == [ n \in 1..Len(labels) |-> node.Edges[labels[n]] ] IN
                     IF idx = 0
                        THEN /\ pc' = "Result"
                             /\ UNCHANGED << iterStack, node >>
                        ELSE /\ IF idx+1 <= Len(edges)
                                   THEN /\ iterStack' = iterStack \o SubSeq(edges, idx+1, Len(edges))
                                   ELSE /\ TRUE
                                        /\ UNCHANGED iterStack
                             /\ node' = edges[idx]
                             /\ pc' = "Seek"
            /\ UNCHANGED << input, key, root, search, result, prefixCmp, stack >>

Result == /\ pc = "Result"
          /\ result' = Iterate(iterStack)
          /\ pc' = "CheckResult"
          /\ UNCHANGED << iterStack, input, key, root, node, search, prefixCmp, 
                          stack >>

CheckResult == /\ pc = "CheckResult"
               /\ Assert(result = Expected(input, key), 
                         "Failure of assertion at line 194, column 3.")
               /\ pc' = "Done"
               /\ UNCHANGED << iterStack, input, key, root, node, search, 
                               result, prefixCmp, stack >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == findMin \/ Begin \/ Seek \/ Search \/ Consume \/ NextEdge \/ Result
           \/ CheckResult
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-3849a00086ed28d49f404334fb3cdff9

=============================================================================
\* Modification History
\* Last modified Fri Jul 02 08:15:31 PDT 2021 by mitchellh
\* Created Thu Jul 01 10:43:00 PDT 2021 by mitchellh
