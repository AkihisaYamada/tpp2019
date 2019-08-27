Let us formalize simple Turing machines operating on cyclic tapes.

Let Σ be a finite set of (more than one) symbols.
Our machine *M* will be specified by
the finite set *Q* of states,
initial state *q*<sub>0</sub> in *Q*, and
the function Δ : *Q* × Σ → (*Q* ∪ {H}) × Σ × {left,right}.
With Δ(*q*,*a*) = (*q'*, *a*', *d*)
we mean that
if the machine state is *q* and the tape head reads symbol *a*,
then the symbol under the head will be replaced by *a*',
the head will be moved one symbol to the *d* (left or right),
the machine halts if *q*' = H and moves to state *q*' otherwise.

1. Please define such machines (e.g. as a datatype) and the one-step computation
(as a function or a relation)
that takes current configuration and gives the next configuration.

2. Let *a*<sub>0</sub> ∈ Σ.
Please define a machine that,
given an arbitrary cyclic tape of an arbitrary length, 
every computation sequence from the initial state halts,
and the resulting tape contains only *a*<sub>0</sub>.

