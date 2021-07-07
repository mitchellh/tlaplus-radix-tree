This module specifies the iterator structure used in the go-immutable-radix
project (https://github.com/hashicorp/go-immutable-radix/).

The iterator is meant to seek to some point in a radix tree and read all
the subsequent values until it is over. Many algorithms make use of this
"ordered read" property. This module specifies only the "read next" algorithm
used by go-immutable-radix. From here, modules such as RadixSeekLowerBound,
RadixSeekPrefix, etc. refine this module further to verify their own algorithms.

--------------------------- MODULE RadixIterator ---------------------------
LOCAL INSTANCE RadixTrees
LOCAL INSTANCE Sequences
LOCAL INSTANCE SequencesExt
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Integers
LOCAL INSTANCE TLC

\* CmpOp is the comparison operator for ordered iteration. This should be TRUE
\* if the first value is less than the second value.
CONSTANT CmpOp(_,_)

-----------------------------------------------------------------------------

\* Internal logic for Iterate.
RECURSIVE iterate(_, _)
iterate(T, prefix) == 
  LET 
    current == IF Len(T.Value) > 0 THEN <<T.Value>> ELSE <<>>
      \* current value of node (if exists)
      
    orderedEdges == SortSeq(SetToSeq(DOMAIN T.Edges), CmpOp)
      \* ordering that we'll visit edges
      
    children == [i \in 1..Len(orderedEdges) |-> 
      iterate(T.Edges[orderedEdges[i]], prefix \o T.Prefix)]
      \* children values, this is a tuple of tuples

    flatChildren == FoldLeft(LAMBDA x, y: x \o y, <<>>, children)
      \* children as a single tuple of values
  IN current \o flatChildren

\* Iterate implements the core iteration algorithm. Given a sequence of nodes
\* this will return a sequence (not a set, since this is ordered) of keys that
\* are visited in the tree.
Iterate(Stack) == 
  FoldLeft(LAMBDA x, y: x \o y, 
           <<>>,
           [i \in 1..Len(Stack) |-> iterate(Stack[Len(Stack)-i+1], <<>>)])

=============================================================================
\* Modification History
\* Last modified Fri Jul 02 08:12:17 PDT 2021 by mitchellh
\* Created Tue Jun 29 19:49:11 PDT 2021 by mitchellh
