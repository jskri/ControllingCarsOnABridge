# Controlling cars on a bridge

Models of controlling cars on a one-way brige between mainland and an island.

This example is interesting because it solves the problem in a top-down
approach, introducing a succession of more and more refined models. Each refined
model introduces new details, which keeps the modelling task manageable.

Invariants and refinements are proved.

The [original models](https://www.event-b.org/A_ch2.pdf) use the Event-B
formalism. We adapt them here to
[TLA+](https://lamport.azurewebsites.net/tla/tla.html) (which is very close) and
to [Isabelle](https://isabelle.in.tum.de/) (which is less close).

For now, the TLA+ models go up to the second refinement, while the isabelle
models go up to the first.

The TLA+ models require the [TLA+ proof
manager](https://github.com/tlaplus/tlapm) version 1.5.0.

The isabelle models have been tested with
[Isabelle2024/HOL](https://isabelle.in.tum.de/installation.html).

