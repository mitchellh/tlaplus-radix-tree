---- MODULE MC ----
EXTENDS RadixIteratorValidation, TLC

CmpOpImpl(X, Y) == X < Y
ASSUME PrintT(Valid)
=============================================================================
