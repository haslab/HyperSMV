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

`hypersmv` has four modes (`ah`, `qbf`, `tomc`, `toalloy`), summarized below. Every mode accepts
`--input`/`-i` one or more SMV files (one per formula quantifier, in order -- repeat a file when
several quantifiers share the same model) and `--informula`/`-I` a HyperLTL formula file over
them. Run `hypersmv <mode> --help` for the full flag list.

### Complete model checking (`ah`)

Converts the SMV models to explicit-state systems and solves via
[AutoHyper](https://github.com/AutoHyper/AutoHyper) -- full LTL, including loops:

```
hypersmv ah --input=A.smv --input=B.smv --informula=formula.ah
```

### Bounded model checking (`qbf`)

Encodes a bounded unrolling as QBF and solves via a QCIR solver (default
[quabs](https://github.com/ltentrup/quabs)), following
[HyperQB](https://github.com/HyperQB/HyperQB), no loops:

```
hypersmv qbf --input=A.smv --input=B.smv --informula=formula.ah --sem=pes -k=7
```

Requires an unrolling bound (`-k`) and a finite BMC semantics for infinite inference (`--sem`:
`pes` or `opt`). 

### Generic dispatch (`tomc`)

Picks a backend (AutoHyper, HyperQube, or QCIR/QBF) via `-H` and writes SMV/formula output for it
instead of solving directly, when you want the translated input rather than a verdict:

```
hypersmv tomc --input=A.smv --input=B.smv -H=AutoHyper --informula=formula.ah --outformula=out.ah
```

`--output` takes one file per `--input` (the translated SMV models); `--outformula` the translated
formula. Shares `ah`/`qbf`'s solving flags since the same translation pipeline feeds all three.

### Export to Alloy (`toalloy`)

Converts SMV models to Alloy models, one `--output` per `--input`:

```
hypersmv toalloy --input=A.smv --output=A.als
```

It can also translate a HyperLTL formula into an Alloy `check` block, over the same `--input`
models used to build them:

```
hypersmv toalloy --input=A.smv --input=B.smv --informula=formula.ah --outformula=formula.als -k=10 -e=1
```

`-k` sets the `check`'s `for N steps` scope and `-e`/`--alloyexpect` its `expect` bit (1 if a
satisfying instance is expected, 0 otherwise). 