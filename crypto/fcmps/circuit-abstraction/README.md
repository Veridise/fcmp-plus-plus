# Generalized Bulletproofs Circuit Abstraction

A circuit abstraction around `generalized-bulletproofs`.

# Picus Translator

A translator from the circuit abstraction to [Veridise](https://veridise.com)'s [Picus V2 DSL](https://docs.veridise.com) is provided in [src/picus](./src/picus/).
To validate your setup is working, try running
```bash
cd src/picus
cargo test
```

See [the fcmps README](../README.md) for instructions on how to run the translator.