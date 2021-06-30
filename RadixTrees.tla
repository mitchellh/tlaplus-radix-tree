This module contains operations for working with radix trees. A radix tree
is a data structure for efficient storage and lookup of values that often
share prefixes, typically used with strings.

A common question when I show this to people is: how do I add to the tree?
delete? update? For these, grab the Range of the tree, use set logic to 
add/remove any elements, and construct a new tree with RadixTree.

For educational purposes, I've heavily commented all the operations. I 
recommend using the constant expression evaluator to try the building blocks
to learn how things work if you're confused. That's how I learned.

----------------------------- MODULE RadixTrees -----------------------------
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Sequences
LOCAL INSTANCE Integers

-----------------------------------------------------------------------------

\* Helpers that aren't Radix-tree specific.

\* shortestSeq returns the shortest sequence in a set.
LOCAL shortestSeq(set) == 
  CHOOSE seq \in set:
    \A other \in set:
      Len(seq) <= Len(other)

\* Filter the sequence to only return the values that start with c.
LOCAL filterPrefix(set, c) == { seq \in set: seq[1] = c }

\* Strip the prefix from each element in set. This assumes that each
\* element in set already starts with prefix. Empty values will not
\* be returned.
LOCAL stripPrefix(set, prefix) == 
  { SubSeq(seq, Len(prefix)+1, Len(seq)): seq \in set \ {prefix} }

\* Returns the set of first characters of a set of char sequences.
LOCAL firstChars(set) == { seq[1]: seq \in set }

\* Find the longest shared prefix of a set of sequences. Sequences can
\* be different lengths, but must have comparable types.
\* i.e. longestPrefix({1,2},{1,2,3},{1,2,5}) == {1,2}
LOCAL longestPrefix(set) ==
  \* Every item must at least have a common first character otherwise
  \* the longest prefix is surely empty
  IF \A x \in set, y \in set: 
    /\ Len(x) >= 1
    /\ Len(y) >= 1
    /\ x[1] = y[1]
  THEN 
  LET
    seq == shortestSeq(set)
    end == CHOOSE end \in 1..Len(seq):
      /\ \A i \in 1..end:
        \A x, y \in set: x[i] = y[i]
      /\ \/ Len(seq) <= end \* we're at the end 
         \/ \E x, y \in set: x[end+1] /= y[end+1] \* or there is no longer prefix
  IN SubSeq(seq, 1, end)
  ELSE <<>>
  
-----------------------------------------------------------------------------

\* Radix tree helpers
  
RECURSIVE range(_, _)
LOCAL range(T, prefix) == 
  LET 
    current == IF Len(T.Value) > 0 THEN {T.Value} ELSE {}
      \* current value of node (if exists)
      
    children == UNION { 
      range(T.Edges[edge], prefix \o T.Prefix): 
      edge \in DOMAIN T.Edges 
    }
      \* child values for each edge. this creates a set of sets
      \* so we call union to flatten it.
  IN current \cup children
  
\* Returns the constructed radix tree for the set of keys Keys. 
RECURSIVE radixTree(_,_)
radixTree(Keys, Base) == 
  IF Keys = {} THEN {} \* base case, no keys empty tree
  ELSE LET
    prefix == longestPrefix(Keys) 
      \* longest shared prefix
    base == Base \o prefix
      \* our new base
    keys == stripPrefix(Keys, prefix) 
      \* keys for children, prefix stripped
    edgeLabels == firstChars(stripPrefix(Keys, prefix))
      \* labels for each edge (single characters)
  IN [
    Prefix |-> prefix, 
    Value |-> IF prefix \in Keys THEN base ELSE <<>>,
    Edges |-> [L \in edgeLabels |-> radixTree(filterPrefix(keys, L), base)]
  ]

-----------------------------------------------------------------------------

\* Returns the constructed radix tree for the set of keys Keys. 
RadixTree(Keys) == 
  LET 
    edgeLabels == firstChars(Keys) 
  IN [
    \* The root of a radix tree is always a non-value that only has outward
    \* edges to the first sets of values.
    Prefix |-> <<>>,
    Value  |-> <<>>,
    Edges  |-> [L \in edgeLabels |-> radixTree(filterPrefix(Keys, L), <<>>)]
  ]

\* Range returns all of the values that are in the radix tree T.
Range(T) == range(T, <<>>)

=============================================================================
\* Modification History
\* Last modified Wed Jun 30 11:33:25 PDT 2021 by mitchellh
\* Created Mon Jun 28 08:08:13 PDT 2021 by mitchellh
