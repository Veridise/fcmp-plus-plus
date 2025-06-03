# Generalized Bulletproofs Circuit Abstraction

A circuit abstraction around `generalized-bulletproofs`.

# Picus Translator

A translator from the circuit abstraction to [Veridise](https://veridise.com)'s [Picus V2 DSL](https://docs.veridise.com) is provided in [src/picus](./src/picus/).

See [the fcmps README](../README.md) for instructions on how to run the translator.

The individual circuits are instantiated in [src/bin/picus_circuits.rs](./src/bin/picus_circuits.rs).