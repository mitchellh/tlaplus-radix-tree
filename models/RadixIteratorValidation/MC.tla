---- MODULE MC ----
EXTENDS RadixIteratorValidation, TLC

\* RadixIterator!Range clashes with Functions!Range, thus INSTANCE here.
F == INSTANCE Functions

Order ==
    CHOOSE f \in [Alphabet -> 1..Cardinality(Alphabet)] : F!IsInjective(f)

CmpOpImpl(X, Y) == 
    Order[X] < Order[Y]

ASSUME PrintT(Valid)
=============================================================================
