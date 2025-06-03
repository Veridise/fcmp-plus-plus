# Full-Chain Membership Proofs

An implementation of the membership proof from
[FCMP++](https://github.com/kayabaNerve/fcmp-ringct/blob/develop/fcmp%2B%2B.pdf),
which inputs a re-randomized key, re-randomized linking tag generator, a
Pedersen commitment to the linking tag generator, and an amount commitment
before verifying there is a known de-re-randomization for a member of a Merkle
tree.

## Picus

A translator from the circuit abstraction to [Veridise](https://veridise.com)'s [Picus V2 DSL](https://docs.veridise.com).

To generate the Picus-verified circuits in the `out/` directory, run the following command. The translator is unoptimized, and takes 3-5 minutes on an M1 Macbook Pro.
```bash
cargo run picus_circuits
```
