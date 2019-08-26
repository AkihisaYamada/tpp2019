Let us formalize a simple deterministic Turing machine on a cyclic tape.
Let Σ be a finite set of symbols.
Our machine *M* will be specified by
the finite set *Q* of states,
initial state *q*<sub>i</sub> in *Q*,
final state *q*<sub>f</sub> in *Q*, and
the function Δ : *Q* × Σ → *Q* × Σ × {left,right}.
With Δ(*q*,*a*) = (*q'*, *a*', *d*)
we mean that
if the machine state is *q* and the tape head reads symbol *a*,
then the next state will be *q*', the symbol under the head will be replaced by *a*',
and head will be moved one symbol to the *d* (left or right).

1. Please give a formal definition (e.g., datatype) of such machines and configurations.
