From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.

Section TM.

Inductive Dir : Set := Left | Right.
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
       | Left => (last ch tp, belast ch tp)
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
pose m := l.
rewrite -{1 2}/m -{1}(cats0 tp).
rewrite {1}(_ : nil = nseq (l-m) None); last by rewrite subnn.
have Hm: m <= l by [].
elim: m Hm => [|m IH] Hm.
  by rewrite subn0.
rewrite -(IH (ltnW Hm)) addSn /= -cats1 -!catA /=.
by rewrite (ltn_subadd1 Hm) nseq_rcons cats1.
Qed.

Definition rcons_simp := (last_rcons, belast_rcons).

Lemma runL tp l n :
  run (mkPt L None (tp ++ nseq l None)) (l + n) =
  run (mkPt L None (nseq l None ++ tp)) n.
Proof.
pose m := l.
rewrite -{1 2}/m.
rewrite [in LHS](erefl : tp = nil ++ tp).
rewrite {1}(_ : nil = nseq (l-m) None); last by rewrite subnn.
have Hm: m <= l by [].
elim: m Hm => [|m IH] Hm.
  by rewrite subn0 cats0.
rewrite nseq_rcons addSn [LHS]/= !last_cat belast_cat [LHS]/= !rcons_simp.
by rewrite -cat1s catA cats1 -lastI -(IH (ltnW Hm)) (ltn_subadd1 Hm).
Qed.

(* Starting from state I1, we eventually stop with an empty tape *)
Theorem erase_ok p : state p = I1 ->
  exists n, run p n = (mkPt S None (nseq (size (tape p)) None), true).
Proof.
destruct p as [st cr [|h tp]] => /= -> {st}.
  by exists 4.
set l := size tp.
suff: forall tp',
    size tp' <= l ->
    let p1 := mkPt L (Some true) (nseq (l - size tp') None ++ Some false :: tp')
    in exists n, run p1 n = (mkPt S None (nseq l.+1 None), true).
  move/(_ tp (leqnn _)) => /= [n Hrun].
  exists n.+2 => /=.
  by rewrite !rcons_simp -Hrun subnn.
clearbody l => {tp}.
elim => [_|c tp IH Hsz] p1.
  rewrite {}/p1 /= subn0.
  exists (l+l+6).
  case: l => // l.
  rewrite 2!addSn [_+_]lock /= -lock -addnA -cats1 -catA /=.
  rewrite runR addSn /= 3!addnS /= !rcons_simp.
  rewrite -rcons_cons /= !rcons_simp (runL [:: _; _]) /=.
  by rewrite -cat1s catA cats1 !rcons_simp /= cats1 -!nseq_rcons.
case/IH: (ltnW Hsz) => n <- {IH}.
pose m := l - (size tp).+1.
exists (m.+1 + m.+3 + n).
rewrite {}/p1 addSn (ltn_subadd1 Hsz) [size _]/= -/m.
move H: m => [|m'].
  by do 2 rewrite /= !rcons_simp.
rewrite addSnnS /= -addnE -addnA rcons_cat runR.
rewrite addSnnS /= !rcons_simp -addnE.
rewrite rcons_cat -nseq_rcons -addSnnS -cat1s catA runL /=.
rewrite last_cat /= last_rcons.
by rewrite -rcons_cons -rcons_cat belast_rcons.
Qed.

End Erase.
