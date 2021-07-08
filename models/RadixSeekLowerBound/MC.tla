---- MODULE MC ----
EXTENDS RadixSeekLowerBound, TLC

F == INSTANCE Functions

Order ==
    CHOOSE f \in [Alphabet -> 1..Cardinality(Alphabet)] : F!IsInjective(f)

CmpOpImpl(X, Y) == 
    Order[X] < Order[Y]

PrintExpected == 
    [
        node |-> node
        ,prefixCmp |-> prefixCmp
        ,root |-> root
        ,search |-> search
        ,pc |-> pc
        ,input |-> input
        ,iterStack |-> iterStack
        ,key |-> key
        ,stack |-> stack
        ,result |-> result
        ,expected |-> Expected(input, key)
    ]
=============================================================================
