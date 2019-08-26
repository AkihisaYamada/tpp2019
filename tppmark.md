Let us formalize simple Turing machines operating on cyclic tapes.

Let Σ = {0,...,n} be a finite set of symbols (where n ≥ 1).
Our machine *M* will be specified by
the finite set *Q* of states,
initial state *q*<sub>i</sub> in *Q*, and
the function Δ : *Q* × Σ → (*Q* ∪ {H}) × Σ × {left,right}.
With Δ(*q*,*a*) = (*q'*, *a*', *d*)
we mean that
if the machine state is *q* and the tape head reads symbol *a*,
then the symbol under the head will be replaced by *a*',
the head will be moved one symbol to the *d* (left or right),
the machine halts if *q*' = H and moves to state *q*' otherwise.

1. Please define one-step computation function (or relation) that takes
current configuration and returns the next configuration.

2. Please define a machine *M*<sub>0</sub> that, given an arbitrary cyclic tape, 
