# Incorrectness and Adversarial Logic in Rocq

This repository contains an encoding of [Incorrectness Logic](https://dl.acm.org/doi/10.1145/3371078) in Rocq.
It will eventually contain an encoding of [Adversarial Logic](https://dl.acm.org/doi/10.1007/978-3-031-22308-2_19) as well.

## Milestones

- [x] [Encoding IL triples and inference rules](https://github.com/CharlesAverill/ILAL/blob/2b06f479473721cdffc1a9e6d67325387e9af402/theories/IL.v#L31)
- [x] [Soundness of IL](https://github.com/CharlesAverill/ILAL/blob/2b06f479473721cdffc1a9e6d67325387e9af402/theories/IL.v#L456)
    This proof was relatively simple once an apt encoding of the denotational semantics presented in the paper was found.
    There are some slight differences in the DS presented here: primarily the rules for `C*`, which have been expanded from one
    computational definition in the paper to two base rules for `ok` and `er` executions, and one inductive rule.
- [ ] Completeness of IL
- [ ] Encoding AL triples and inference rules
- [ ] Soundness of AL
- [ ] Completeness of AL

## Building

```bash
# Install Dependencies
opam switch create rocq 4.14.1
opam pin add rocq-runtime 9.1.0
opam install rocq-prover dune

# Clone and build
git clone https://github.com/CharlesAverill/ILAL && cd ILAL
dune build
```
