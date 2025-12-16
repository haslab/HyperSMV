# HyperSMV

This repository contains HyperSMV, short for model checking of multiple SMV models with regard to joint hyperproperties.
The HyperSMV tool receives a set of SMV models, together with a hyper formula, and calls underlying solvers.

## Install

Make sure that you have Haskell (GHC + cabal) installed. See [ghcup](https://www.haskell.org/ghcup/install/) for instructions.
Then, simply run:

```
cabal install
```

## Run

### Complete model checking

To perform complete model checkhing (with loops), we convert SMV models explicit-state systems, and resort to [AutoHyper](https://github.com/AutoHyper/AutoHyper). You may run the following command:

```
hypersmv ah --input=A.smv --input=B.smv --informula=formula.ah 
````

where `--input` describes the input SMV files and `--informula` describes the input hyper formula.

### Bounded model checking

We also support bounded model checking (without loops) via QBF solvers, following [HyperQB](https://github.com/HyperQB/HyperQB). You may run the following command:

```
hypersmv qbf --input=A.smv --input=B.smv --informula=formula.ah --sem=pos -k=7
```

This time, we need to specify a maximum unrolling bound for BMC (`-k`) and a finite BMC semantics for infinite inference (`--sem`).
