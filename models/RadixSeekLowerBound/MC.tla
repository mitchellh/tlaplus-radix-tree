---- MODULE MC ----
EXTENDS RadixSeekLowerBound, TLC

F == INSTANCE Functions

Order ==
    CHOOSE f \in [Alphabet -> 1..Cardinality(Alphabet)] : F!IsInjective(f)

CmpOpImpl(X, Y) == 
    Order[X] < Order[Y]
=============================================================================
