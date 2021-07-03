This module verifies the correctness of the algorith used to implement 
SeekPrefix in the go-immutable-radix project. 
(https://github.com/hashicorp/go-immutable-radix)

SeekPrefix should move the iterator to the first value that has a certain
prefix. All subsequent values should have that prefix, but no other ordering
guarantees are made.

-------------------------- MODULE RadixSeekPrefix --------------------------
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

\* SeekPrefix in pure TLA+ for verification purposes.
Expected(root, search) == { value \in Range(root): HasPrefix(value, search) }

(*--algorithm seek_prefix
variables 
  stack = <<>>,
  input \in InputSets,
  prefix \in Inputs,
  root = RadixTree(input),
  node = {},
  search = {},
  result = {};

\* This entire algorith is almost 1:1 translated where possible from the
\* actual implementation in iter.go. That's the point: we're trying to verify
\* our algorithm is correct for all inputs.
\*
\* Source: https://github.com/hashicorp/go-immutable-radix/blob/f63f49c0b598a5ead21c5015fb4d08fe7e3c21ea/iter.go#L16
begin
  \* I could've just set these variables in the initializer above but
  \* to better closely match the algorithm, I reset them here.
Begin:
  stack := <<>>;
  node := root;
  search := prefix;

Seek:
  while TRUE do
    if Len(search) = 0 then
      goto Result;
    end if;
  
  CheckEdge:
    if ~(search[1] \in DOMAIN node.Edges) then
      goto NoMatch;
    end if;
    
  GetEdge:
    node := node.Edges[search[1]];
  
  CheckPrefix:
    if HasPrefix(search, node.Prefix) then
      search := TrimPrefix(search, node.Prefix);
    elsif HasPrefix(node.Prefix, search) then
      goto Result;
    else
      goto NoMatch;
    end if;
  end while;
    
NoMatch:
  result := {};
  goto CheckResult;
  
Result:
  result := Range(node);
  
CheckResult:
  assert result = Expected(root, prefix);
end algorithm; *)

-----------------------------------------------------------------------------

\* !!! NOTE !!! The rest of the file is auto-generated based on the PlusCal
\* above. For those who are reading this to learn TLA+/PlusCal, you can stop
\* reading here.

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-a964e2a12a4a65ec8be338cb28ad3c5c
VARIABLES stack, input, prefix, root, node, search, result, pc

vars == << stack, input, prefix, root, node, search, result, pc >>

Init == (* Global variables *)
        /\ stack = <<>>
        /\ input \in InputSets
        /\ prefix \in Inputs
        /\ root = RadixTree(input)
        /\ node = {}
        /\ search = {}
        /\ result = {}
        /\ pc = "Begin"

Begin == /\ pc = "Begin"
         /\ stack' = <<>>
         /\ node' = root
         /\ search' = prefix
         /\ pc' = "Seek"
         /\ UNCHANGED << input, prefix, root, result >>

Seek == /\ pc = "Seek"
        /\ IF Len(search) = 0
              THEN /\ pc' = "Result"
              ELSE /\ pc' = "CheckEdge"
        /\ UNCHANGED << stack, input, prefix, root, node, search, result >>

CheckEdge == /\ pc = "CheckEdge"
             /\ IF ~(search[1] \in DOMAIN node.Edges)
                   THEN /\ pc' = "NoMatch"
                   ELSE /\ pc' = "GetEdge"
             /\ UNCHANGED << stack, input, prefix, root, node, search, result >>

GetEdge == /\ pc = "GetEdge"
           /\ node' = node.Edges[search[1]]
           /\ pc' = "CheckPrefix"
           /\ UNCHANGED << stack, input, prefix, root, search, result >>

CheckPrefix == /\ pc = "CheckPrefix"
               /\ IF HasPrefix(search, node.Prefix)
                     THEN /\ search' = TrimPrefix(search, node.Prefix)
                          /\ pc' = "Seek"
                     ELSE /\ IF HasPrefix(node.Prefix, search)
                                THEN /\ pc' = "Result"
                                ELSE /\ pc' = "NoMatch"
                          /\ UNCHANGED search
               /\ UNCHANGED << stack, input, prefix, root, node, result >>

NoMatch == /\ pc = "NoMatch"
           /\ result' = {}
           /\ pc' = "CheckResult"
           /\ UNCHANGED << stack, input, prefix, root, node, search >>

Result == /\ pc = "Result"
          /\ result' = Range(node)
          /\ pc' = "CheckResult"
          /\ UNCHANGED << stack, input, prefix, root, node, search >>

CheckResult == /\ pc = "CheckResult"
               /\ Assert(result = Expected(root, prefix), 
                         "Failure of assertion at line 104, column 3.")
               /\ pc' = "Done"
               /\ UNCHANGED << stack, input, prefix, root, node, search, 
                               result >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Begin \/ Seek \/ CheckEdge \/ GetEdge \/ CheckPrefix \/ NoMatch
           \/ Result \/ CheckResult
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-513823b550d282baa457ca6b713fe5f1


=============================================================================
\* Modification History
\* Last modified Wed Jun 30 12:04:00 PDT 2021 by mitchellh
\* Created Wed Jun 30 10:05:52 PDT 2021 by mitchellh
