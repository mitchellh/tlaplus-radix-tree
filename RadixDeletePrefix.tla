This module verifies the correctness of the algorith used to implement 
DeletePrefix in the go-immutable-radix project. 
(https://github.com/hashicorp/go-immutable-radix)

-------------------------- MODULE RadixDeletePrefix --------------------------
EXTENDS FiniteSets, Integers, Sequences, TLC
INSTANCE RadixTrees

\* Set of characters to use for the alphabet of generated strings.
CONSTANT Alphabet

\* Length of input strings generated
CONSTANT MinLength, MaxLength
ASSUME 
  /\ {MinLength, MaxLength} \subseteq Nat
  /\ MinLength <= MaxLength
  /\ MinLength > 0

\* Number of unique elements to construct the radix tree with. This
\* is a set of numbers so you can test with inputs of multiple sizes.
CONSTANT ElementCounts
ASSUME ElementCounts \subseteq Nat

\* Inputs is the set of input strings valid for the tree.
Inputs == UNION { [1..n -> Alphabet]: n \in MinLength..MaxLength }

\* InputSets is the full set of possible inputs we can send to the radix tree.
InputSets == { T \in SUBSET Inputs: Cardinality(T) \in ElementCounts }

-----------------------------------------------------------------------------

\* TRUE iff seq is prefixed with prefix.
HasPrefix(seq, prefix) ==
  /\ Len(seq) >= Len(prefix)
  /\ \A i \in 1..Len(prefix): seq[i] = prefix[i]

\* Remove prefix from seq.
TrimPrefix(seq, prefix) == [ i \in 1..(Len(seq)-Len(prefix)) |-> seq[i+Len(prefix)] ]

-----------------------------------------------------------------------------

\* DeletePrefix should be equivalent to the tree without inputs that have that prefix.
\* This purposely doesn't model the "delete" algorithm at all: only the end result
\* of what the tree should contain.
ExpectedTree(input, prefix) == RadixTree({ value \in input: ~HasPrefix(value, prefix) })

(*--algorithm delete_prefix
variables 
  input \in InputSets,
  prefix \in Inputs,
  root = RadixTree(input),
  newChild = <<>>,
  search = {},
  result = {};
  
define
  \* We determine if newChild is "nil" by checking if it has the empty domain,
  \* since a non-null child will be a function with domains prefix, value, etc.
  NewChildNull == DOMAIN newChild = {}
end define;

\* Precondition: Len(n.Edges) = 1
procedure mergeChild(n = <<>>)
begin
MergeChild:
  with 
    label = CHOOSE x \in DOMAIN n.Edges: TRUE, \* we know we have only one edge 
    child = n.Edges[label]
  do
    n.Prefix := n.Prefix \o child.Prefix ||
    n.Value := child.Value ||
    n.Edges := child.Edges;
  end with;
  
ExitMergeChild:
  return;
end procedure;
  
procedure deletePrefix(n = <<>>, nRoot = FALSE) 
variables searchLabel = <<>>;
begin
DeletePrefix:
  \* Check for key exhaustion
  if Len(search) = 0 then
    newChild := [
      Prefix |-> n.Prefix,
      Value  |-> <<>>,
      Edges  |-> <<>>
    ];
    return;
  end if;
  
FindEdge:
  \* Look for an edge
  searchLabel := search[1];
  if ~searchLabel \in DOMAIN n.Edges then
  NoEdge:
    newChild := <<>>;
    return;
  end if;
  
ConsumeAndRecurse:
  with child = n.Edges[searchLabel] do
    if ~HasPrefix(child.Prefix, search) /\ ~HasPrefix(search, child.Prefix) then
      newChild := <<>>;
      return;
    else
      \* Consume the search prefix
      if Len(child.Prefix) > Len(search) then
        search := <<>>;
      else
        search := SubSeq(search, Len(child.Prefix)+1, Len(search))
      end if;
      
      call deletePrefix(child, FALSE);
    end if;
  end with;
  
ExitIfNoChild:
  if NewChildNull then
    newChild := <<>>;
    return;
  end if;
  
ModifyNode:
  if Len(newChild.Value) = 0 /\ Cardinality(DOMAIN newChild.Edges) = 0 then
    n.Edges := [ label \in DOMAIN n.Edges \ {searchLabel} |-> n.Edges[label] ];
   
    if ~nRoot /\ Cardinality(DOMAIN n.Edges) = 1 /\ Len(n.Value) = 0 then
      call mergeChild(n);
    end if;
  else 
    n.Edges[searchLabel] := newChild
  end if;
  
ReturnDeletePrefix:
  newChild := n;
  return;
end procedure;

\* This entire algorith is almost 1:1 translated where possible from the
\* actual implementation in iter.go. That's the point: we're trying to verify
\* our algorithm is correct for all inputs.
begin
Begin:
  search := prefix;
  call deletePrefix(root, TRUE);
  
SetNewRoot:
  if ~NewChildNull then
    root := newChild;
  end if;
  
AssertExpected:
  \* check our expected values 
  with 
    actual = Range(root),
    expected = Range(ExpectedTree(input, prefix))
  do
    if actual # expected then
      print <<"value check", "actual", actual, "expected", expected>>;
      assert FALSE;
    end if;
  end with;
  
  \* check our expected tree structure for an optimal structure
  (*
  with 
    actual = root,
    expected = ExpectedTree(input, prefix)
  do
    if actual # expected then
      print <<"tree check", "actual", actual, "expected", expected>>;
      assert FALSE;
    end if;
  end with;
  *)
end algorithm; *)

-----------------------------------------------------------------------------

\* !!! NOTE !!! The rest of the file is auto-generated based on the PlusCal
\* above. For those who are reading this to learn TLA+/PlusCal, you can stop
\* reading here.

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-4cfdd22a8561a6e90f5abd27401fce60
\* Parameter n of procedure mergeChild at line 63 col 22 changed to n_
VARIABLES input, prefix, root, newChild, search, result, pc, stack

(* define statement *)
NewChildNull == DOMAIN newChild = {}

VARIABLES n_, n, nRoot, searchLabel

vars == << input, prefix, root, newChild, search, result, pc, stack, n_, n, 
           nRoot, searchLabel >>

Init == (* Global variables *)
        /\ input \in InputSets
        /\ prefix \in Inputs
        /\ root = RadixTree(input)
        /\ newChild = <<>>
        /\ search = {}
        /\ result = {}
        (* Procedure mergeChild *)
        /\ n_ = <<>>
        (* Procedure deletePrefix *)
        /\ n = <<>>
        /\ nRoot = FALSE
        /\ searchLabel = <<>>
        /\ stack = << >>
        /\ pc = "Begin"

MergeChild == /\ pc = "MergeChild"
              /\ LET label == CHOOSE x \in DOMAIN n_.Edges: TRUE IN
                   LET child == n_.Edges[label] IN
                     n_' = [n_ EXCEPT !.Prefix = n_.Prefix \o child.Prefix,
                                      !.Value = child.Value,
                                      !.Edges = child.Edges]
              /\ pc' = "ExitMergeChild"
              /\ UNCHANGED << input, prefix, root, newChild, search, result, 
                              stack, n, nRoot, searchLabel >>

ExitMergeChild == /\ pc = "ExitMergeChild"
                  /\ pc' = Head(stack).pc
                  /\ n_' = Head(stack).n_
                  /\ stack' = Tail(stack)
                  /\ UNCHANGED << input, prefix, root, newChild, search, 
                                  result, n, nRoot, searchLabel >>

mergeChild == MergeChild \/ ExitMergeChild

DeletePrefix == /\ pc = "DeletePrefix"
                /\ IF Len(search) = 0
                      THEN /\ newChild' =             [
                                            Prefix |-> n.Prefix,
                                            Value  |-> <<>>,
                                            Edges  |-> <<>>
                                          ]
                           /\ pc' = Head(stack).pc
                           /\ searchLabel' = Head(stack).searchLabel
                           /\ n' = Head(stack).n
                           /\ nRoot' = Head(stack).nRoot
                           /\ stack' = Tail(stack)
                      ELSE /\ pc' = "FindEdge"
                           /\ UNCHANGED << newChild, stack, n, nRoot, 
                                           searchLabel >>
                /\ UNCHANGED << input, prefix, root, search, result, n_ >>

FindEdge == /\ pc = "FindEdge"
            /\ searchLabel' = search[1]
            /\ IF ~searchLabel' \in DOMAIN n.Edges
                  THEN /\ pc' = "NoEdge"
                  ELSE /\ pc' = "ConsumeAndRecurse"
            /\ UNCHANGED << input, prefix, root, newChild, search, result, 
                            stack, n_, n, nRoot >>

NoEdge == /\ pc = "NoEdge"
          /\ newChild' = <<>>
          /\ pc' = Head(stack).pc
          /\ searchLabel' = Head(stack).searchLabel
          /\ n' = Head(stack).n
          /\ nRoot' = Head(stack).nRoot
          /\ stack' = Tail(stack)
          /\ UNCHANGED << input, prefix, root, search, result, n_ >>

ConsumeAndRecurse == /\ pc = "ConsumeAndRecurse"
                     /\ LET child == n.Edges[searchLabel] IN
                          IF ~HasPrefix(child.Prefix, search) /\ ~HasPrefix(search, child.Prefix)
                             THEN /\ newChild' = <<>>
                                  /\ pc' = Head(stack).pc
                                  /\ searchLabel' = Head(stack).searchLabel
                                  /\ n' = Head(stack).n
                                  /\ nRoot' = Head(stack).nRoot
                                  /\ stack' = Tail(stack)
                                  /\ UNCHANGED search
                             ELSE /\ IF Len(child.Prefix) > Len(search)
                                        THEN /\ search' = <<>>
                                        ELSE /\ search' = SubSeq(search, Len(child.Prefix)+1, Len(search))
                                  /\ /\ n' = child
                                     /\ nRoot' = FALSE
                                     /\ stack' = << [ procedure |->  "deletePrefix",
                                                      pc        |->  "ExitIfNoChild",
                                                      searchLabel |->  searchLabel,
                                                      n         |->  n,
                                                      nRoot     |->  nRoot ] >>
                                                  \o stack
                                  /\ searchLabel' = <<>>
                                  /\ pc' = "DeletePrefix"
                                  /\ UNCHANGED newChild
                     /\ UNCHANGED << input, prefix, root, result, n_ >>

ExitIfNoChild == /\ pc = "ExitIfNoChild"
                 /\ IF NewChildNull
                       THEN /\ newChild' = <<>>
                            /\ pc' = Head(stack).pc
                            /\ searchLabel' = Head(stack).searchLabel
                            /\ n' = Head(stack).n
                            /\ nRoot' = Head(stack).nRoot
                            /\ stack' = Tail(stack)
                       ELSE /\ pc' = "ModifyNode"
                            /\ UNCHANGED << newChild, stack, n, nRoot, 
                                            searchLabel >>
                 /\ UNCHANGED << input, prefix, root, search, result, n_ >>

ModifyNode == /\ pc = "ModifyNode"
              /\ IF Len(newChild.Value) = 0 /\ Cardinality(DOMAIN newChild.Edges) = 0
                    THEN /\ n' = [n EXCEPT !.Edges = [ label \in DOMAIN n.Edges \ {searchLabel} |-> n.Edges[label] ]]
                         /\ IF ~nRoot /\ Cardinality(DOMAIN n'.Edges) = 1 /\ Len(n'.Value) = 0
                               THEN /\ /\ n_' = n'
                                       /\ stack' = << [ procedure |->  "mergeChild",
                                                        pc        |->  "ReturnDeletePrefix",
                                                        n_        |->  n_ ] >>
                                                    \o stack
                                    /\ pc' = "MergeChild"
                               ELSE /\ pc' = "ReturnDeletePrefix"
                                    /\ UNCHANGED << stack, n_ >>
                    ELSE /\ n' = [n EXCEPT !.Edges[searchLabel] = newChild]
                         /\ pc' = "ReturnDeletePrefix"
                         /\ UNCHANGED << stack, n_ >>
              /\ UNCHANGED << input, prefix, root, newChild, search, result, 
                              nRoot, searchLabel >>

ReturnDeletePrefix == /\ pc = "ReturnDeletePrefix"
                      /\ newChild' = n
                      /\ pc' = Head(stack).pc
                      /\ searchLabel' = Head(stack).searchLabel
                      /\ n' = Head(stack).n
                      /\ nRoot' = Head(stack).nRoot
                      /\ stack' = Tail(stack)
                      /\ UNCHANGED << input, prefix, root, search, result, n_ >>

deletePrefix == DeletePrefix \/ FindEdge \/ NoEdge \/ ConsumeAndRecurse
                   \/ ExitIfNoChild \/ ModifyNode \/ ReturnDeletePrefix

Begin == /\ pc = "Begin"
         /\ search' = prefix
         /\ /\ n' = root
            /\ nRoot' = TRUE
            /\ stack' = << [ procedure |->  "deletePrefix",
                             pc        |->  "SetNewRoot",
                             searchLabel |->  searchLabel,
                             n         |->  n,
                             nRoot     |->  nRoot ] >>
                         \o stack
         /\ searchLabel' = <<>>
         /\ pc' = "DeletePrefix"
         /\ UNCHANGED << input, prefix, root, newChild, result, n_ >>

SetNewRoot == /\ pc = "SetNewRoot"
              /\ IF ~NewChildNull
                    THEN /\ root' = newChild
                    ELSE /\ TRUE
                         /\ root' = root
              /\ pc' = "AssertExpected"
              /\ UNCHANGED << input, prefix, newChild, search, result, stack, 
                              n_, n, nRoot, searchLabel >>

AssertExpected == /\ pc = "AssertExpected"
                  /\ LET actual == Range(root) IN
                       LET expected == Range(ExpectedTree(input, prefix)) IN
                         IF actual # expected
                            THEN /\ PrintT(<<"value check", "actual", actual, "expected", expected>>)
                                 /\ Assert(FALSE, 
                                           "Failure of assertion at line 162, column 7.")
                            ELSE /\ TRUE
                  /\ pc' = "Done"
                  /\ UNCHANGED << input, prefix, root, newChild, search, 
                                  result, stack, n_, n, nRoot, searchLabel >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == mergeChild \/ deletePrefix \/ Begin \/ SetNewRoot \/ AssertExpected
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-3f5a03aa27274374d34aca49ae1849de


=============================================================================
\* Modification History
\* Last modified Fri Jul 02 11:44:17 PDT 2021 by mitchellh
\* Created Wed Jun 30 10:05:52 PDT 2021 by mitchellh
