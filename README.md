# TLA+ Specifications for Radix Trees

This repository includes TLA+ specifications and models for
[Radix trees](https://en.wikipedia.org/wiki/Radix_tree) and algorithms
on Radix trees. The focus of this repository is specifically on specifying
the behavior of the  [hashicorp/go-immutable-radix](https://github.com/hashicorp/go-immutable-radix)
Go library. However, many modules are fairly generic and could easily be
adapted to any Radix implementation.

## CLI Usage

You can always import these specifications and models directly into TLA+ Toolbox.
I also have `make` targets for executing via the CLI. These expect that you
have `pcal` and `tlc2` setup as scripts or aliases to execute the respective
commands in `tlatools.jar`. If you have no idea what I'm talking about, stick
with TLA+ Toolbox for now.

If you're a Nix user, this repository has a `shell.nix` that sets everything up.

### Executing a Model

To execute a model:

    $ make tlc SPEC_NAME=RadixTreesValidation

This will run `tlc2` against the model defined in `models/RadixTreesValidation/MC.tla`.
By default this uses `MC.tla`, but if a specification has multiple models, you
can execute it by specifying `MODEL_NAME` in addition to `SPEC_NAME`.

Example:

```shell-session
$ make tlc SPEC_NAME=RadixTreesValidation
TLC2 Version 2.15 of Day Month 20?? (rev: ${git.shortRevision})
Running breadth-first search Model-Checking with fp 79 and seed 1841139739546182859 with 1 worker on 8 cores with 3660MB heap and 64MB offheap memory (Linux 5.10.40 amd64, Oracle Corporation 1.8.0_272 x86_64, MSBDiskFPSet, DiskStateQueue).
Parsing file /home/mitchellh/code/go/src/github.com/mitchellh/tla-go-immutable-radix/models/RadixTreesValidation/MC.tla
Parsing file /home/mitchellh/code/go/src/github.com/mitchellh/tla-go-immutable-radix/RadixTreesValidation.tla
Parsing file /tmp/TLC.tla
Parsing file /tmp/FiniteSets.tla
Parsing file /tmp/Integers.tla
Parsing file /home/mitchellh/code/go/src/github.com/mitchellh/tla-go-immutable-radix/RadixTrees.tla
Parsing file /tmp/Sequences.tla
Parsing file /tmp/Naturals.tla
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module Integers
Semantic processing of module RadixTrees
Semantic processing of module TLC
Semantic processing of module RadixTreesValidation
Semantic processing of module MC
Starting... (2021-07-04 14:35:49)
TRUE
Computing initial states...
Finished computing initial states: 0 distinct states generated at 2021-07-04 14:35:49.
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 0.0
0 states generated, 0 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 1.
Finished in 01s at (2021-07-04 14:35:49)
```
