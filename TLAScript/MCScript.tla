---- MODULE MCScript ----
EXTENDS TLC, IOUtils, Naturals


ASSUME
    LET Envs == 
            {  
                {
                    <<"MinLength", ToString(i)>>,
                    <<"MaxLength", ToString(i+1)>>,
                    \* TODO: The whitespaces in the definition of the sets are significant. :-(
                    \*       Without the whitespaces, the sets are not recognized as sets.
                    <<"Alphabet", ToString({0, 1, 2})>>,
                    <<"ElementCounts", ToString({2, 3})>>
                }
            : i \in 0..1
            } 
        Cmd == <<"java",
                 \* Terminate each run after 60 seconds.
                 \* TODO Terminate also _during_ the generation of initial states.
                 "-Dtlc2.TLC.stopAfter=60",
                 "-jar", "/opt/toolbox/tla2tools.jar", 
                 "-tool", "-config", "MC.tla",
                 "MC">>
    IN \A Env \in Envs:
            \* First, print the configuration that TLC is going to check.
            /\ PrintT(Env)
            \* Print TLC's exit value.
            \* TODO: This should stream TLC's output and not stall until the
            \*       sub-process terminates.  Alternatively, figure something 
            \*       out via nohup/tee/... .
            \* TODO: In addition to setting the process' exit value, TLC should 
            \*       also write a proper message to stderr. For example, stderr
            \*       could equal the name of the generated trace spec?!
            /\ PrintT(IOEnvExec(Env, Cmd).stderr)

-----------------------------------------------------------------------------
\* This is a dummy spec to make TLC accept this specification and not complain
\* about a missing behavior spec _before_ it evaluates the assumption above.

VARIABLE x

Spec ==
    x = TRUE /\ [][UNCHANGED x]_x

=============================================================================

----- CONFIG MCScript -----
SPECIFICATION Spec
======