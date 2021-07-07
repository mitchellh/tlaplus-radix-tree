---- MODULE MC ----
EXTENDS RadixSeekLowerBound, TLC

Order ==
    CHOOSE f \in [Alphabet -> 1..Cardinality(Alphabet)] : isInjective(f)

CmpOpImpl(X, Y) == 
    Order[X] < Order[Y]
=============================================================================
