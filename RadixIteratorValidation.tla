---------------------- MODULE RadixIteratorValidation ----------------------
EXTENDS FiniteSets, Integers, RadixTrees, Sequences, TLC

\* Set of characters to use for the alphabet of generated strings.
CONSTANT Alphabet

\* CmpOp is the comparison operator for ordered iteration. This should be TRUE
\* if the first value is less than the second value.
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
  
\* Inputs is the set of input strings valid for the tree.
Inputs == UNION { [1..n -> Alphabet]: n \in MinLength..MaxLength }

\* InputSets is the full set of possible inputs we can send to the radix tree.
InputSets == { T \in SUBSET Inputs: Cardinality(T) \in ElementCounts }

\* InputTrees is a set of two trees for all inputs used to test iteration
\* of multiple trees.
InputTrees == { <<RadixTree(input1), RadixTree(input2)>>: input1, input2 \in InputSets }

-----------------------------------------------------------------------------

\* TRUE iff the sequence s contains no duplicates. Copied from CommunityModules.
LOCAL isInjective(s) == \A i, j \in DOMAIN s: (s[i] = s[j]) => (i = j)

\* Converts a set to a sequence that contains all the elements of S exactly once.
\* Copied from CommunityModules.
LOCAL setToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : isInjective(f)

-----------------------------------------------------------------------------

INSTANCE RadixIterator

\* Expected result given an input set is the sorted input set.
Expected(input) == 
  SortSeq(setToSeq(input), 
    LAMBDA x, y:
      \/ Len(x) < Len(y)
      \/ /\ Len(x) = Len(y)
         /\ \A i \in DOMAIN x: CmpOp(x[i], y[i]) \/ x[i] = y[i])

\* The iteration of a tree should be just its sorted inputs.
IterateIsSortedInput == 
  \A input \in InputSets:
    LET 
      actual == Iterate(<<RadixTree(input)>>)
      
      \* CmpOp operates on individual elements so we have to write a LAMBDA here
      \* that performs per-element. We expect CmpOp to be a LESS THAN operation.
      \* The logic below does not work for GREATER THAN operations (\A would have
      \* to be \E).
      expected == Expected(input)
    IN 
      IF actual # expected
      THEN Print(<<"actual: ", actual, "expected: ", expected, "input: ", input>>, FALSE)
      ELSE TRUE
    
\* The iteration of two things in a stack should have the results of the
\* first element then the results of the second.  
IterateMultiple ==
  \A stack \in InputTrees:
    LET 
      actual == Iterate(stack)
      
      \* CmpOp operates on individual elements so we have to write a LAMBDA here
      \* that performs per-element. We expect CmpOp to be a LESS THAN operation.
      \* The logic below does not work for GREATER THAN operations (\A would have
      \* to be \E).
      expected == Expected(Range(stack[2])) \o Expected(Range(stack[1]))
    IN 
      IF actual # expected
      THEN Print(<<"actual: ", actual, "expected: ", expected, "stack: ", stack>>, FALSE)
      ELSE TRUE

\* The expression that should be checked for validity in the model.
Valid == 
  /\ IterateIsSortedInput
  /\ IterateMultiple

=============================================================================
\* Modification History
\* Last modified Thu Jul 01 19:06:11 PDT 2021 by mitchellh
\* Created Thu Jul 01 09:57:41 PDT 2021 by mitchellh
