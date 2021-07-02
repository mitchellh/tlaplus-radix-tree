------------------------ MODULE RadixTreesValidation ------------------------
EXTENDS FiniteSets, Integers, RadixTrees, Sequences, TLC

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

\* All leaf nodes should be values, there is no such thing as a leaf
\* node that doesn't represent a value.
RECURSIVE LeafsAreValues(_)
LeafsAreValues(T) ==
  \/ /\ Cardinality(DOMAIN T.Edges) > 0 \* if it has edges, its leaves must be values
     /\ \A e \in DOMAIN T.Edges: LeafsAreValues(T.Edges[e])
  \/ /\ Cardinality(DOMAIN T.Edges) = 0 \* if it has no edges, it must be a value
     /\ Len(T.Value) > 0
     
-----------------------------------------------------------------------------

\* The range of a radix tree should be the set of its inputs.
RangeIsInput == 
  \A input \in InputSets:
    LET actual == Range(RadixTree(input))
    IN 
      IF actual # input
      THEN Print(<<actual, input, RadixTree(input)>>, FALSE)
      ELSE TRUE
      
AllLeafsAreValues ==
  \A input \in InputSets:
    LET actual == LeafsAreValues(RadixTree(input))
    IN \/ actual
       \/ Print(<<actual, input, RadixTree(input)>>, FALSE)

\* The expression that should be checked for validity in the model.
Valid == 
  /\ RangeIsInput
  /\ AllLeafsAreValues

=============================================================================
\* Modification History
\* Last modified Fri Jul 02 08:26:43 PDT 2021 by mitchellh
\* Created Tue Jun 29 08:02:38 PDT 2021 by mitchellh
