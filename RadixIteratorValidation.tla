---------------------- MODULE RadixIteratorValidation ----------------------
EXTENDS FiniteSets, Integers, RadixTrees, Sequences, SequencesExt, TLC, Inputs

\* CmpOp is the comparison operator for ordered iteration. This should be TRUE
\* if the first value is less than the second value.
CONSTANT CmpOp(_,_)

\* InputTrees is a set of two trees for all inputs used to test iteration
\* of multiple trees.
InputTrees == { <<RadixTree(input1), RadixTree(input2)>>: input1, input2 \in InputSets }

-----------------------------------------------------------------------------

INSTANCE RadixIterator

\* Expected result given an input set is the sorted input set.
Expected(input) == 
  SortSeq(SetToSeq(input), 
    LAMBDA x, y:
      \/ Len(x) < Len(y)
      \/ /\ Len(x) = Len(y)
         /\ \A i \in DOMAIN x: CmpOp(x[i], y[i]) \/ x[i] = y[i])

\* The iteration of a tree should be just its sorted inputs.
IterateIsSortedInput == 
  \A input \in InputSets:
    LET 
      actual == Iterate(<<RadixTree(input)>>)
      expected == Expected(input)
    IN 
      IF actual # expected
      THEN Print(<<"actual: ", actual, "expected: ", expected, "input: ", input>>, FALSE)
      ELSE TRUE
    
\* The iteration of two things in a stack should have the results of the
\* second element followed by the first (FIFO).
IterateMultiple ==
  \A stack \in InputTrees:
    LET 
      actual == Iterate(stack)
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
\* Last modified Fri Jul 02 08:13:53 PDT 2021 by mitchellh
\* Created Thu Jul 01 09:57:41 PDT 2021 by mitchellh
