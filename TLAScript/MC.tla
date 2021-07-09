---- MODULE MC ----
EXTENDS TLC, IOUtils, Naturals

\* TODO: atos and atoi re-evaluated over and over again?

\* TODO: ToString(0..2) = "0..2" and ToString({0,1,2}) ="{0,1,2}",
\*       which are both unequal to {0, 1, 2} (note the whitespaces)
\*       coming from CHOOSE s \in SUSBET ...: ToString(s)

atoi(str) ==
    \* TODO This could be defined in IOUtils with an unbound choose from NAT
    \*      and overriden with a module override that converts the string
    \*      to an IntValue and returns an undefined value if it fails.
    CHOOSE n \in 0..2^16: ToString(n) = str

atos(str) ==
    \* TODO: 0..2^16 is computationally too expensive!
    \*       Is this only the case that the predicate doesn't match or is TLC
    \*       indeed eagerly enumerating the  SUBSET (..)  first?
    \* TODO: What about sets of non-integer elements?
    \*       atos(str, S) == CHOOSE s \in S: ToString(s) = str
    \*       However, this makes it impossible to come up with a module override,
    \*       because S can be any set such as the union of Nat and STRING.
    CHOOSE s \in SUBSET (0..2^8): ToString(s) = str

\* TODO atof (a string to function)

\* TODO atos and atof would become easy iff TLC would dynamically parse TLA+ expressions.

-----------------------------------------------------------------------------

VARIABLES iterStack, input, key, root, node, search, result, prefixCmp, pc, 
          stack

CmpOpImpl(X, Y) == X < Y

INSTANCE RadixSeekLowerBound
WITH
  CmpOp <- CmpOpImpl,

\*   MinLength <- 1,
\*   MaxLength <- 2,
\*   Alphabet <- {0,1,2},
\*   ElementCounts <- {2,3}

  MinLength <- atoi(IOEnv.MinLength),
  MaxLength <- atoi(IOEnv.MaxLength),
  Alphabet <- atos(IOEnv.Alphabet),
  ElementCounts <- atos(IOEnv.ElementCounts)

=============================================================================

----- CONFIG MC -----
SPECIFICATION Spec
======