(* TPPmark2019 solution by Mitsuharu Yamamato *)
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TPPmark2019.

Section Definitions.

(* Problem 1 *)

Variant direction := left | right.

Variables (state symbol : finType).

Record turing_machine :=
  TuringMachine {
      transition : state -> symbol -> option (state * symbol * direction);
      initial : state;
    }.

Definition cyclic_tape : Type := symbol * seq symbol.
Definition configuration : Type := state * cyclic_tape.

(* Problem 2 *)

Variable m : turing_machine.

Definition step (c : configuration) : option configuration :=
  let: (q, (x, s)) := c in
  if m.(transition) q x is Some (q', x', d)
  then Some (q', match d with
                 | left =>  (last x' s, belast x' s)
                 | right => (head x' s, behead (rcons s x'))
                 end)
  else None.

(* Problem 3 *)

Definition halts (t : cyclic_tape) :=
  exists n, iter n (obind step) (Some (m.(initial), t)) = None.

Definition reachable (c c': configuration) :=
  exists n, iter n (obind step) (Some c) = Some c'.

End Definitions.

(* Problem 4 *)

Section ZeroClear.

Variant zcstate := zcinit0 | zcinit1 | zcinit2 | zcinit3
                   | zcforw0 | zcforw1 | zcback0.

Variant zcsymbol := zc0 | zc1.

Definition zctrans q x :=
  match q, x with
  | zcinit0, _   => Some (zcinit1, zc1, right)
  | zcinit1, zc1 => Some (zcinit2, zc0, left)
  | zcinit1, _   => Some (zcforw0, zc1, right)
  | zcinit2, zc1 => Some (zcinit3, zc1, right)
  | zcinit2, _   => None
  | zcinit3, _   => Some (zcforw0, zc1, right)
  | zcforw0, zc1 => Some (zcforw1, zc0, right)
  | zcforw0, _   => Some (zcforw0, zc0, right)
  | zcforw1, zc1 => Some (zcback0, zc1, left)
  | zcforw1, _   => Some (zcforw0, zc0, right)
  | zcback0, zc1 => Some (zcinit2, zc0, left)
  | zcback0, _   => Some (zcback0, zc0, left)
  end.

Definition zcstate2o (q : zcstate) : 'I_7 :=
  match q with
  | zcinit0 => inord 4 | zcinit1 => inord 3 | zcinit2 => inord 2
  | zcinit3 => inord 1 | zcforw0 => inord 0
  | zcforw1 => inord 6 | zcback0 => inord 5
  end.

Definition o2zcstate (o : 'I_7) : option zcstate :=
  match val o with
  | 4 => Some zcinit0 | 3 => Some zcinit1 | 2 => Some zcinit2
  | 1 => Some zcinit3 | 0 => Some zcforw0
  | 6 => Some zcforw1 | 5 => Some zcback0
  | _ => None
  end.

Lemma pcan_zcstateo7 : pcancel zcstate2o o2zcstate.
Proof. by case; rewrite /o2zcstate /= inordK. Qed.

Definition zcstate_eqMixin := PcanEqMixin pcan_zcstateo7.
Canonical zcstate_eqType := EqType zcstate zcstate_eqMixin.
Definition zcstate_choiceMixin := PcanChoiceMixin pcan_zcstateo7.
Canonical zcstate_choiceType := ChoiceType zcstate zcstate_choiceMixin.
Definition zcstate_countMixin := PcanCountMixin pcan_zcstateo7.
Canonical zcstate_countType := CountType zcstate zcstate_countMixin.
Definition zcstate_finMixin := PcanFinMixin pcan_zcstateo7.
Canonical zcstate_finType := FinType zcstate zcstate_finMixin.

Definition zcsymbol2b (x : zcsymbol) : bool :=
  match x with | zc0 => false | zc1 => true end.

Definition b2zcsymbol (b : bool) : zcsymbol :=
  if b then zc1 else zc0.

Lemma can_zcsymbolb : cancel zcsymbol2b b2zcsymbol.
Proof. by case. Qed.

Definition zcsymbol_eqMixin := CanEqMixin can_zcsymbolb.
Canonical zcsymbol_eqType := EqType zcsymbol zcsymbol_eqMixin.
Definition zcsymbol_choiceMixin := CanChoiceMixin can_zcsymbolb.
Canonical zcsymbol_choiceType := ChoiceType zcsymbol zcsymbol_choiceMixin.
Definition zcsymbol_countMixin := CanCountMixin can_zcsymbolb.
Canonical zcsymbol_countType := CountType zcsymbol zcsymbol_countMixin.
Definition zcsymbol_finMixin := CanFinMixin can_zcsymbolb.
Canonical zcsymbol_finType := FinType zcsymbol zcsymbol_finMixin.

Definition zc := {| transition := zctrans; initial := zcinit0 |}.

(* Problem 5 *)

Definition zcconfig := configuration [finType of zcstate] [finType of zcsymbol].

Fixpoint trace {state symbol : finType}
         (m : turing_machine state symbol) c fuel :=
  if fuel is fuel'.+1 then
    c :: if step m c is Some c' then trace m c' fuel' else [::]
  else [::].

Definition zcweight (c : zcconfig) :=
  let: (q, (x, s)) := c in
  (count_mem zc1 (match q with
                 | zcinit0 => zc1 :: if s is _ :: s' then zc1 :: s' else [::]
                 | zcinit1 => zc1 :: s
                 | zcinit2 =>   x :: if s is _ :: s' then zc1 :: s' else [::]
                 | zcinit3 => zc1 :: s
                 | _       =>   x :: s
                 end) * (ord_max : returnType zcstate2o).+1
   + zcstate2o q) * (size s).+1
  + match q with
    | zcforw0 => size s - index zc1 (rev s)
    | zcback0 => index zc1 (rev (behead (rcons s x)))
    | _       => 0
    end.

Compute let c := (zcinit0, (zc0, [:: zc0; zc1; zc0; zc1; zc1]))
        in trace zc c (zcweight c).
     (* = [:: (zcinit0, (zc0, [:: zc0; zc1; zc0; zc1; zc1])); *)
     (*       (zcinit1, (zc0, [:: zc1; zc0; zc1; zc1; zc1])); *)
     (*       (zcforw0, (zc1, [:: zc0; zc1; zc1; zc1; zc1])); *)
     (*       (zcforw1, (zc0, [:: zc1; zc1; zc1; zc1; zc0])); *)
     (*       (zcforw0, (zc1, [:: zc1; zc1; zc1; zc0; zc0])); *)
     (*       (zcforw1, (zc1, [:: zc1; zc1; zc0; zc0; zc0])); *)
     (*       (zcback0, (zc0, [:: zc1; zc1; zc1; zc0; zc0])); *)
     (*       (zcback0, (zc0, [:: zc0; zc1; zc1; zc1; zc0])); *)
     (*       (zcback0, (zc0, [:: zc0; zc0; zc1; zc1; zc1])); *)
     (*       (zcback0, (zc1, [:: zc0; zc0; zc0; zc1; zc1])); *)
     (*       (zcinit2, (zc1, [:: zc0; zc0; zc0; zc0; zc1])); *)
     (*       (zcinit3, (zc0, [:: zc0; zc0; zc0; zc1; zc1])); *)
     (*       (zcforw0, (zc0, [:: zc0; zc0; zc1; zc1; zc1])); *)
     (*       (zcforw0, (zc0, [:: zc0; zc1; zc1; zc1; zc0])); *)
     (*       (zcforw0, (zc0, [:: zc1; zc1; zc1; zc0; zc0])); *)
     (*       (zcforw0, (zc1, [:: zc1; zc1; zc0; zc0; zc0])); *)
     (*       (zcforw1, (zc1, [:: zc1; zc0; zc0; zc0; zc0])); *)
     (*       (zcback0, (zc0, [:: zc1; zc1; zc0; zc0; zc0])); *)
     (*       (zcback0, (zc0, [:: zc0; zc1; zc1; zc0; zc0])); *)
     (*       (zcback0, (zc0, [:: zc0; zc0; zc1; zc1; zc0])); *)
     (*       (zcback0, (zc0, [:: zc0; zc0; zc0; zc1; zc1])); *)
     (*       (zcback0, (zc1, [:: zc0; zc0; zc0; zc0; zc1])); *)
     (*       (zcinit2, (zc1, [:: zc0; zc0; zc0; zc0; zc0])); *)
     (*       (zcinit3, (zc0, [:: zc0; zc0; zc0; zc0; zc1])); *)
     (*       (zcforw0, (zc0, [:: zc0; zc0; zc0; zc1; zc1])); *)
     (*       (zcforw0, (zc0, [:: zc0; zc0; zc1; zc1; zc0])); *)
     (*       (zcforw0, (zc0, [:: zc0; zc1; zc1; zc0; zc0])); *)
     (*       (zcforw0, (zc0, [:: zc1; zc1; zc0; zc0; zc0])); *)
     (*       (zcforw0, (zc1, [:: zc1; zc0; zc0; zc0; zc0])); *)
     (*       (zcforw1, (zc1, [:: zc0; zc0; zc0; zc0; zc0])); *)
     (*       (zcback0, (zc0, [:: zc1; zc0; zc0; zc0; zc0])); *)
     (*       (zcback0, (zc0, [:: zc0; zc1; zc0; zc0; zc0])); *)
     (*       (zcback0, (zc0, [:: zc0; zc0; zc1; zc0; zc0])); *)
     (*       (zcback0, (zc0, [:: zc0; zc0; zc0; zc1; zc0])); *)
     (*       (zcback0, (zc0, [:: zc0; zc0; zc0; zc0; zc1])); *)
     (*       (zcback0, (zc1, [:: zc0; zc0; zc0; zc0; zc0])); *)
     (*       (zcinit2, (zc0, [:: zc0; zc0; zc0; zc0; zc0]))] *)
     (* : seq (configuration zcstate_finType zcsymbol_finType) *)

Compute let c := (zcinit0, (zc0, [::]))
        in trace zc c (zcweight c).
     (* = [:: (zcinit0, (zc0, [::])); (zcinit1, (zc1, [::])); *)
     (*       (zcinit2, (zc0, [::]))] *)
     (* : seq (configuration zcstate_finType zcsymbol_finType) *)

Compute let c := (zcinit0, (zc0, [:: zc1]))
        in trace zc c (zcweight c).
     (* = [:: (zcinit0, (zc0, [:: zc1])); (zcinit1, (zc1, [:: zc1])); *)
     (*       (zcinit2, (zc1, [:: zc0])); (zcinit3, (zc0, [:: zc1])); *)
     (*       (zcforw0, (zc1, [:: zc1])); (zcforw1, (zc1, [:: zc0])); *)
     (*       (zcback0, (zc0, [:: zc1])); (zcback0, (zc1, [:: zc0])); *)
     (*       (zcinit2, (zc0, [:: zc0]))] *)
     (* : seq (configuration zcstate_finType zcsymbol_finType) *)

(* Problem 6 *)

(*
(zcinit0, ..* )
  . -> (zcinit1, 1, right)
    .\..* = .*
    next: (zcinit1, .*1) = (zcinit1, 1) | (zcinit1, .+1)

(zcinit1, 1)
  0 -> (zcforw0, 1, right)
    0\1 = {}
  1 -> (zcinit2, 0, left)
    1\1 = ""
    next: (zcinit2, 0) <= (zcinit2, 0+)
(zcinit1, .+1)
  0 -> (zcforw0, 1, right)
    0\.+1 = .*1
    next: (zcforw0, .*11) <= (zcforw0, .*110* )
  1 -> (zcinit2, 0, left)
    1\.+1 = .*1
    next: (zcinit2, 10.* )

(zcinit2, 10.* )
  0 -> accept
    0\10.* = {}
  1 -> (zcinit3, 1, right)
    1\10.* = 0.*
    next: (zcinit3, 0.*1)
(zcinit2, 0+ )
  0 -> accept
    0\0+ = 0*
  1 -> (zcinit3, 1, right)
    1\0+ = {}

(zcinit3, 0.*1)
  . -> (zcforw0, 1, right)
    .\.+1 = .*1
    next: (zcforw0, .*11) <= (zcforw0, .*110* )

(zcforw0, 110* )
  0 -> (zcforw0, 0, right)
    0\110* = {}
  1 -> (zcforw1, 0, right)
    1\110* = 10*
    next: (zcforw1, 10+)
(zcforw0, .+110* )
  0 -> (zcforw0, 0, right)
    0\.+110* = .*110*
    next: (zcforw0, .*110+) = (zcforw0, 110* ) | (zcforw0, .+110* )
  1 -> (zcforw1, 0, right)
    1\.+110* = .*110*
    next: (zcforw1, .*110+) = (zcforw1, 110+) | (zcforw1, .+110+)

(zcforw1, 110+)
  0 -> (zcforw0, 0, right)
    0\110+ = {}
  1 -> (zcback0, 1, left)
    1\110+ = 10+
    next: (zcback0, 0110* ) <= (zcback0, 0.*110* )
(zcforw1, .+110+)
  0 -> (zcforw0, 0, right)
    0\.+110+ = .*110+
    next: (zcforw0, .*1100+) <= (zcforw0, 110* ) | (zcforw0, .+110* )
  1 -> (zcback0, 1, left)
    1\.+110+ = .*110+
    next: (zcback0, 01.*110* ) <= (zcback0, 0.*110* )
(zcforw1, 10+)
  0 -> (zcforw0, 0, right)
    0\10+ = {}
  1 -> (zcback0, 1, left)
    1\10+ = 0+
    next: (zcback0, 010* ) <= (zcback0, 0+10* )

(zcback0, 0.*110* )
  0 -> (zcback0, 0, left)
    0\0.*110* = .*110* = .*110+|.*11
    next: (zcback0, 00.*110* ) <= (zcback0, 0.*110* )
    next: (zcback0, 10.*1)
  1 -> (zcinit2, 0, left)
    1\0.*110* = {}
(zcback0, 0+10* )
  0 -> (zcback0, 0, left)
    0\0+10* = 0*10* = 0*10+ | 0*1
    next: (zcback0, 00+10* ) <= (zcback0, 0+10* )
    next: (zcback0, 10+)
  1 -> (zcinit2, 0, left)
    1\0+10* = {}
(zcback0, 10.*1)
  0 -> (zcback0, 0, left)
    0\10.*1 = {}
  1 -> (zcinit2, 0, left)
    1\10.*1 = 0.*1
    next: (zcinit2, 100.* ) <= (zcinit2, 10.* )
(zcback0, 10+)
  0 -> (zcback0, 0, left)
    0\10+ = {}
  1 -> (zcinit2, 0, left)
    1\10+ = 0+
    next: (zcinit2, 00+) <= (zcinit2, 0+)
*)

Variant zcinv : zcconfig -> Prop :=
| ZCInvInit0 x s                (* ..* *)
  : zcinv (zcinit0, (x,   s))
| ZCInvInit1A                   (* 1 *)
  : zcinv (zcinit1, (zc1, [::]))
| ZCInvInit1B x s               (* .+1 *)
  : zcinv (zcinit1, (x,   rcons s zc1))
| ZCInvInit2A s                 (* 10.* *)
  : zcinv (zcinit2, (zc1, zc0 :: s))
| ZCInvInit2B n                 (* 0+ *)
  : zcinv (zcinit2, (zc0, nseq n zc0))
| ZCInvInit3 s                  (* 0.*1 *)
  : zcinv (zcinit3, (zc0, rcons s zc1))
| ZCInvForw0A n                 (* 110* *)
  : zcinv (zcforw0, (zc1, zc1 :: nseq n zc0))
| ZCInvForw0B x s n             (* .+110* *)
  : zcinv (zcforw0, (x,   s ++ zc1 :: zc1 :: nseq n zc0))
| ZCInvForw1A n                 (* 110+ *)
  : zcinv (zcforw1, (zc1, zc1 :: nseq n.+1 zc0))
| ZCInvForw1B x s n             (* .+110+ *)
  : zcinv (zcforw1, (x,   s ++ zc1 :: zc1 :: nseq n.+1 zc0))
| ZCInvForw1C n                 (* 10+ *)
  : zcinv (zcforw1, (zc1, nseq n.+1 zc0))
| ZCInvBack0A s n               (* 0.*110* *)
  : zcinv (zcback0, (zc0, s ++ zc1 :: zc1 :: nseq n zc0))
| ZCInvBack0B n1 n2             (* 0+10* *)
  : zcinv (zcback0, (zc0, nseq n1 zc0 ++ zc1 :: nseq n2 zc0))
| ZCInvBack0C s                 (* 10.*1 *)
  : zcinv (zcback0, (zc1, zc0 :: rcons s zc1))
| ZCInvBack0D n                 (* 10+ *)
  : zcinv (zcback0, (zc1, nseq n.+1 zc0)).

Lemma rcons_nseq (T : Type) n (x : T) : rcons (nseq n x) x = x :: nseq n x.
Proof. by rewrite -cats1 cat_nseq /ncons -iterSr. Qed.

Lemma last_nseq (T : Type) n (x : T) : last x (nseq n x) = x.
Proof. by move: (lastI x (nseq n x)); rewrite -rcons_nseq => /rcons_inj []. Qed.

Lemma belast_nseq (T : Type) n (x : T) : belast x (nseq n x) = nseq n x.
Proof. by move: (lastI x (nseq n x)); rewrite -rcons_nseq => /rcons_inj []. Qed.

Lemma zcinv_invariant c : zcinv c ->
                          if step zc c is Some c' then zcinv c' else True.
Proof.
  case=> [x [|x1 s]||[] [|x s]|s||[|x1 s]|n|[] [|x s] n
          |n|[] [|x s] n|n|s [|n]|n1 [|n2]|s|n] //=; try by constructor.
  - exact: (ZCInvInit2B 0).
  - exact: (ZCInvForw0A 0).
  - by rewrite -!cats1 -catA /=; apply: (ZCInvForw0B _ _ 0).
  - by rewrite last_rcons; constructor.
  - exact: (ZCInvForw0A 0).
  - by rewrite -!cats1 -catA /=; apply: (ZCInvForw0B _ _ 0).
  - by rewrite rcons_nseq; constructor.
  - by rewrite rcons_nseq; apply: (ZCInvForw0A _.+1).
  - by rewrite rcons_cat !rcons_cons rcons_nseq; apply: (ZCInvForw0B _ _ _.+1).
  - by rewrite rcons_nseq; constructor.
  - by rewrite rcons_cat !rcons_cons rcons_nseq; constructor.
  - by rewrite last_nseq belast_nseq; apply: (ZCInvBack0A [::]).
  - by rewrite rcons_nseq; apply: (ZCInvForw0A _.+2).
  - by rewrite rcons_cat !rcons_cons rcons_nseq; apply: (ZCInvForw0B _ _ _.+2).
  - by rewrite last_nseq belast_nseq; apply: (ZCInvBack0A [:: _]).
  - rewrite -rcons_nseq last_cat belast_cat /= last_rcons belast_rcons.
    by rewrite -cat1s -[last _ _ :: _]cat1s !catA; constructor.
  - by rewrite last_nseq belast_nseq; apply: (ZCInvBack0B 0).
  - by rewrite last_cat belast_cat /= -cat1s catA !cats1 -lastI; constructor.
  - rewrite -rcons_nseq last_cat belast_cat /= last_rcons belast_rcons.
    by rewrite -cat1s -[last _ _ :: _]cat1s !catA; constructor.
  - by rewrite cats1 last_rcons belast_rcons; constructor.
  - rewrite -rcons_nseq last_cat belast_cat /= last_nseq belast_nseq.
    rewrite last_rcons belast_rcons -cat1s catA cats1 rcons_nseq.
    by rewrite -[_ :: _]/(nseq _.+1 _); constructor.
  - by rewrite last_rcons belast_rcons; constructor.
  - by rewrite last_nseq belast_nseq; apply: (ZCInvInit2B _.+1).
Qed.

Theorem zc_partially_correct t c :
  reachable zc (zc.(initial), t) c ->
  step zc c = None ->
  let: (q, (x, s)) := c in x = zc0 /\ forall y, y \in s -> y = zc0.
Proof.
  move=> c_reach.
  suff: zcinv c.
  { case=> [||[]|||||[]||[]|||||] // [|n] _; split=> // y; rewrite mem_nseq.
    by case: eqP. }
  case: c_reach => n; elim: n => [|n IHn] /= in c *.
  - by case: t c => x s [q [x' s']] [<- <- <-]; constructor.
  - set it := iter _ _ _; case E: it => [c'|] //= step_some.
    by move/IHn/zcinv_invariant: E; rewrite step_some.
Qed.

Lemma zcinv_tape_short_init q x :
  zcinv (q, (x, [::])) -> q \in [:: zcinit0; zcinit1; zcinit2].
Proof.
  by case E: _ / => [? ?||? ?|||[|? ?]||_ [|? ?]||_ [|? ?]||[|? ?]|[|?]||] //=;
     case: E => ->; rewrite !inE eqxx ?orbT.
Qed.

Lemma zcweight_decreasing c :
  zcinv c -> if step zc c is Some c' then zcweight c' < zcweight c else true.
Proof.
  case: c => q [x [| y s]];
    first by move/zcinv_tape_short_init; rewrite !inE => /or3P [] /eqP ->;
             [ |case: x..]; rewrite /= ?inordK.
  case: q; [ |case: x|case: x| |case: x..]; rewrite /= ?inordK // => inv.
  - (* zcinit0 -> zcinit1 *)
    rewrite size_rcons -cats1 count_cat [count_mem _ _ + _]addnC !addn0.
    by rewrite ltn_mul2r ltn_add2l.
  - (* zcinit1 -> zcforw0 *)
    rewrite size_rcons -cats1 count_cat [count_mem _ _ + _]addnC addnCA.
    rewrite !addn0 [(_ + 3) * _]mulnDl ltn_add2l.
    rewrite (leq_ltn_trans (leq_subr _ _)) // -{1}[_.+1]addn0 mulSn.
    by rewrite leq_add2l.
  - (* zcinit1 -> zcinit2 *)
    rewrite size_belast -[(y == _) + _]/(count_mem _ (_ :: _)) [y :: s]lastI.
    rewrite -cats1 count_cat /= !addn0 addnCA [_ + count_mem _ _]addnC.
    by rewrite ltn_mul2r ltn_add2l.
  - (* zcinit2 -> zcinit3 *)
    rewrite size_rcons -cats1 count_cat [count_mem _ _ + _]addnC !addn0.
    by rewrite ltn_mul2r ltn_add2l.
  - (* zcinit3 -> zcforw0 *)
    rewrite size_rcons -cats1 count_cat /= !addn0 [_ + 1]addnC addnCA.
    by rewrite [(_ + 1) * _]mulnDl mul1n ltn_add2l rev_cat.
  - (* zcforw0 -> zcforw0 *)
    rewrite add0n -cats1 count_cat size_cat /= !addn0 addn1 ltn_add2l.
    rewrite rev_cat /= rev_cons -cats1 index_cat mem_rev ifT.
    + by rewrite ltn_sub2l // ltnS (leq_trans (index_size _ _)) // size_rev.
    + case E: _ / inv => [|||||||? [|? s1] n|||||||] //; case: E => _ _ ->.
      * by rewrite inE.
      * by rewrite mem_cat inE eqxx orbT.
  - (* zcforw0 -> zcforw1 *)
    rewrite size_rcons -cats1 count_cat /= !addn0 [1 + _]addnC.
    rewrite !mulnDl mul1n -[_ + 7 * _ + _]addnA ltn_add2l.
    by rewrite (leq_trans _ (leq_addr _ _)) // ltn_mul2r.
  - (* zcforw1 -> zcforw0 *)
    rewrite size_rcons -cats1 count_cat /= !addn0 add0n [(_ + 6) * _]mulnDl.
    by rewrite ltn_add2l (leq_ltn_trans (leq_subr _ _)) // leq_pmull.
  - (* zcforw1 -> zcback0 *)
    rewrite size_belast -[(y == _) + _]/(count_mem _ (_ :: _)) [y :: s]lastI.
    rewrite -cats1 count_cat /= !addn0 addnCA [(_ == zc1) + _]addnC.
    rewrite -{3}[6]/(5 + 1) [_ + (5 + 1)]addnA [(_ + 1) * _]mulnDl ltn_add2l.
    by rewrite cats1 -lastI (leq_ltn_trans (index_size _ _)) ?size_rev ?mul1n.
  - (* zcback0 -> zcback0 *)
    rewrite size_belast -[(y == _) + _]/(count_mem _ (_ :: _)) [y :: s]lastI.
    rewrite -cats1 count_cat /= addn0 [(_ == zc1) + _]addnC ltn_add2l.
    rewrite -cats1 !rev_cat /=.
    case E: _ / inv => [|||||||||||s1 [|n]|n1 [|n2]||] //; case: E.
    + by rewrite lastI -cat1s catA cats1 => /rcons_inj [_ ->].
    + rewrite -rcons_nseq; case: s1 => [|x s1] /= [-> ->] /=.
      * rewrite last_rcons /= !rev_cons rev_rcons belast_rcons rev_cons.
        by rewrite -!cats1 -catA /= !index_cat; case: ifP.
      * rewrite last_cat belast_cat /= last_rcons belast_rcons /=.
        rewrite -/([:: _; _] ++ (zc1 :: nseq _ _)) catA.
        rewrite -/([:: _] ++ (zc1 :: rcons _ _)) catA.
        rewrite !rev_cat !index_cat !mem_rev !inE !eqxx !orTb.
        by rewrite -cats1 -cat_cons rev_cat.
    + by rewrite lastI cats1 => /rcons_inj [_ ->].
    + rewrite -rcons_nseq; case: n1 => [|n1] /= [-> ->].
      * rewrite last_rcons belast_rcons /= rev_rcons rev_cons /=.
        rewrite -cats1 index_cat addn0; case: ifP => //= _.
        move: (index_size zc1 (rev (nseq n2 zc0))); rewrite leq_eqVlt.
        by rewrite index_mem mem_rev mem_nseq andbF orbF => /eqP ->.
      * rewrite last_cat belast_cat /= last_rcons belast_rcons /=.
        rewrite -/([:: _] ++ (zc1 :: nseq _ _)) catA.
        rewrite -/(_ ++ (zc1 :: rcons _ _)).
        rewrite !rev_cat !index_cat !mem_rev !inE !eqxx !orTb.
        by rewrite -cats1 -cat_cons rev_cat.
  - (* zcback0 -> zcinit2 *)
    rewrite size_belast addn0 -[(y == _) + _]/(count_mem _ (y :: s)) lastI.
    rewrite -cats1 count_cat /= addn0 addnCA [(_ == zc1) + _]addnC.
    by rewrite (leq_trans _ (leq_addr _ _)) // ltn_mul2r ltn_add2l.
Qed.

Theorem zc_halts t : halts zc t.
Proof.
  have: zcinv (zc.(initial), t) by case: t; constructor.
  rewrite /halts; move: zc.(initial) => q.
  elim: zcweight {-2}q {-2}t (leqnn (zcweight (q, t))) => {q t} [|w IHw] q t.
  - move=> weight_le_0 /zcweight_decreasing.
    by case: zcweight weight_le_0 => // _; case E: step => // _; exists 1.
  - move=> zcw_le_w1 inv; move: (zcweight_decreasing inv).
    case E: step => [[q' t']|]; last by exists 1.
    move/zcinv_invariant: inv; rewrite E => inv.
    move/leq_trans/(_ zcw_le_w1); rewrite ltnS => /IHw/(_ inv) [n].
    by rewrite -E => <-; exists n.+1; rewrite iterSr.
Qed.

End ZeroClear.

End TPPmark2019.
