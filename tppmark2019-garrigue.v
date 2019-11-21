From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.

Section TM.

Inductive Dir := Left | Right.
Variables State Char : Type.
Record point := mkPt {state: State; current: Char; tape: seq Char}.

(* Final state determined by transition function *)
Variable trans : State -> Char -> option (State * Char * Dir).

(* Transition + tape move *)
Definition step (p : point) :=
  match trans (state p) (current p) with
  | Some (st, ch, dr) =>
    let: (next, tp) :=
       let tp := tape p in
       match dr with
       | Left  => (last ch tp, belast ch tp)
       | Right => if tp is h :: t then (h, rcons t ch) else (ch, nil)
       end
    in
    Some (mkPt st next tp)
  | None => None
  end.

(* Returns (point, true) if final state, false otherwise *)
Fixpoint run p n :=
  if n is n.+1 then
    if step p is Some p then run p n else (p, true)
  else (p, false).

End TM.

Section Erase.

Definition Char := option bool. (* 3 symbols *)
Inductive State := I1 | I2 | L | R | S.

(* Start with I1, then cycles I2 -> L -> R -> I2 (moving Some false)
   until (Some true) is erased by cycle *)
Definition trans st ch :=
  match st, ch with
  | I1, _         => Some (I2, Some true, Right)
  | I2, _         => Some (L, Some false, Left)
  | L, None       => Some (L, None, Left)
  | L, Some true  => Some (R, Some true, Right)
  | L, Some false => Some (S, None, Right)
  | R, None       => Some (R, None, Right)
  | R, Some _     => Some (I2, None, Right)
  | S, _          => None
  end.

Notation step := (step trans).
Notation run := (run trans).

Lemma ltn_subadd1 m l : m < l -> l - m = (l - m.+1).+1.
Proof. rewrite -subn_gt0 => /subnK <-; by rewrite -subnDA !addn1. Qed.

Lemma nseq_rcons {A} n (a : A) : nseq n.+1 a = rcons (nseq n a) a.
Proof. elim: n => // n; rewrite -addn1 => /= {1}->; by rewrite addn1. Qed.

Lemma runR l n tp :
  run (mkPt R None (nseq l None ++ tp)) (l + n) =
  run (mkPt R None (tp ++ nseq l None)) n.
Proof.
set m := {1 2}l; have Hm: m <= l by [].
rewrite {1}(_ : tp = tp ++ nseq (l-m) None); last by rewrite subnn cats0.
elim: m Hm => [|m IH] Hm; first by rewrite subn0.
by rewrite -(IH (ltnW Hm)) addSn /= !rcons_cat (ltn_subadd1 Hm) nseq_rcons.
Qed.

Definition rcons_simp := (last_rcons, belast_rcons).

Lemma runL tp l n :
  run (mkPt L None (tp ++ nseq l None)) (l + n) =
  run (mkPt L None (nseq l None ++ tp)) n.
Proof.
set m := {1 2}l; have Hm: m <= l by [].
rewrite {1}(_ : tp = nseq (l-m) None ++ tp); last by rewrite subnn.
elim: m Hm => [|m IH] Hm; first by rewrite subn0 cats0.
rewrite nseq_rcons addSn [LHS]/= !last_cat belast_cat !rcons_simp.
by rewrite -cat_rcons -lastI -(IH (ltnW Hm)) (ltn_subadd1 Hm).
Qed.

(* Starting from state I1, we eventually stop with an empty tape *)
Theorem erase_ok p : state p = I1 ->
  exists n, run p n = (mkPt S None (nseq (size (tape p)) None), true).
Proof.
case: p => st cr [|h tp] /= -> {st}.
  by exists 4.
set l := size tp.
suff: forall tp, size tp <= l -> exists n,
    run (mkPt L (Some true) (nseq (l - size tp) None ++ Some false :: tp)) n
    = (mkPt S None (nseq l.+1 None), true).
  case/(_ tp) => //= n <-.
  exists n.+2; by rewrite /= !rcons_simp subnn.
move: l => l {tp}.
elim => [_|c tp IH /= Hsz].
  exists (l+(l.+3+3)).
  case: l => // l.
  rewrite !addSn /= rcons_cat runR /= !rcons_simp /= !rcons_simp.
  by rewrite (runL [::_;_]) /= -cat_rcons cats1 !rcons_simp /= -!nseq_rcons.
have{}/IH [n <-] := ltnW Hsz.
rewrite (ltn_subadd1 Hsz); set m := l - _.
exists (m + (m.+2 + n.+2)).
case: {l Hsz} m => [|m]; first by do 2 rewrite /= !rcons_simp.
rewrite !addSn /= rcons_cat runR /= !rcons_simp rcons_cat -nseq_rcons -addSnnS.
by rewrite -cat_cons runL /= last_cat /= -rcons_cons -rcons_cat !rcons_simp.
Qed.

End Erase.
