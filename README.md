To install:

```
cabal install
```

To run, e.g., to prepare inputs for AutoHyper:

```
hypersmv tomc -i A.smv -i B.smv -o A.exp -o B.exp -H=AutoHyper -I formula.ah -O formula.ah
````

where -i describes the input SMV files, -o describes the output explicit state files, and -I and -O respectively denote the input/output hyper formulas.