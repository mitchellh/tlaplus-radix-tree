This module specifies the iterator structure used in the go-immutable-radix
project (https://github.com/hashicorp/go-immutable-radix/).

The iterator is meant to seek to some point in a radix tree and read all
the subsequent values until it is over. It supports seeking by prefix
and by lower bound. 

--------------------------- MODULE RadixIterator ---------------------------
LOCAL INSTANCE RadixTrees
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Integers
LOCAL INSTANCE TLC

\* CmpOp is the comparison operator for ordered iteration. This should be TRUE
\* if the first value is less than the second value.
CONSTANT CmpOp(_,_)

-----------------------------------------------------------------------------

\* TRUE iff the sequence s contains no duplicates. Copied from CommunityModules.
LOCAL isInjective(s) == \A i, j \in DOMAIN s: (s[i] = s[j]) => (i = j)

\* Converts a set to a sequence that contains all the elements of S exactly once.
\* Copied from CommunityModules.
LOCAL setToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : isInjective(f)

\* Copied from CommunityModules.
LOCAL mapThenFoldSet(op(_,_), base, f(_), choose(_), S) ==
  LET iter[s \in SUBSET S] ==
        IF s = {} THEN base
        ELSE LET x == choose(s)
             IN  op(f(x), iter[s \ {x}])
  IN  iter[S]

\* foldLeft folds op on all elements of seq from left to right, starting
\* with the first element and base. Copied from CommunityModules. 
LOCAL foldLeft(op(_, _), base, seq) == 
  mapThenFoldSet(LAMBDA x,y : op(y,x), base,
                 LAMBDA i : seq[i],
                 LAMBDA s: CHOOSE i \in s : \A j \in s: i >= j,
                 DOMAIN seq)

-----------------------------------------------------------------------------

\* Internal logic for Iterate.
RECURSIVE iterate(_, _)
iterate(T, prefix) == 
  LET 
    current == IF T.Value THEN <<prefix \o T.Prefix>> ELSE <<>>
      \* current value of node (if exists)
      
    orderedEdges == SortSeq(setToSeq(DOMAIN T.Edges), CmpOp)
      \* ordering that we'll visit edges
      
    children == [i \in 1..Len(orderedEdges) |-> 
      iterate(T.Edges[orderedEdges[i]], prefix \o T.Prefix)]
      \* children values, this is a tuple of tuples

    flatChildren == foldLeft(LAMBDA x, y: x \o y, <<>>, children)
      \* children as a single tuple of values
  IN current \o flatChildren

\* Iterate implements the core iteration algorithm. Given a sequence of nodes
\* this will return a sequence (not a set, since this is ordered) of keys that
\* are visited in the tree.
Iterate(Stack) == iterate(Stack[1], <<>>) \* TODO doesn't do the whole stack!

=============================================================================
\* Modification History
\* Last modified Wed Jun 30 10:02:47 PDT 2021 by mitchellh
\* Created Tue Jun 29 19:49:11 PDT 2021 by mitchellh
