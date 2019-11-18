(* Solution to TPPMark 2019 by Keisuke Nakano *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.

Infix "∺" := rcons (at level 60).

Lemma mem_cat_first {T:eqType} (x:T) (s:seq T):
  x \in s -> exists s1 s2, (x \notin s1) && (s == s1 ++ x :: s2).
Proof.
  elim s=>//; move:s=>_ y s IH.
  case:(eqVneq x y)=>[->_//=|/negP nxy].
  -{ by exists[::], s=>/=. }
  -{ rewrite in_cons=>/orP[]///IH[s1][s2]/andP[nxs1]/eqP->; exists(y::s1),s2=>//=.
     by apply/andP; split; rewrite//in_cons; move:nxy=>/negP?; apply/norP; split. }
Qed.


(* Configuration *)
Section Config.
  Context {Q Σ: finType}.
  
  Record config: Type := {
    _state : Q      ; (* current state *)
    _tape  : seq Σ ; (* circular tape as a list whose head is pointed *)
  }.
  (* [config] as [eqType] *)
  Definition config_val c := (_state c, _tape c).
  Lemma config_val_inj: injective config_val.
  Proof. by do 2 case => ? ?; injection 1=>->->. Qed.
  Canonical config_eqType := EqType config (InjEqMixin config_val_inj).
End Config.

Notation "{ q @ tape }" := ({| _state := q ; _tape := tape |}) (at level 2).


(* Directionn of the head *)
Section Direction.
  Inductive direction: Type := stay | movL | movR.

  (* [direction] as [eqType] *)
  Definition direction_val d := match d with stay => 0 | movL => 1 | movR => 2 end.
  Lemma direction_val_inj: injective direction_val. Proof. by do 2 case. Qed.
  Canonical direction_eqType := EqType direction (InjEqMixin direction_val_inj).
End Direction.


Section Base.
  Context {Q Σ: finType}.

  (* (Non-determistic) transition *)
  Section Transition.
    Definition transition := Q -> Σ -> Q -> Σ -> direction -> Prop.

    Variable δ: transition.

    Section Step.
      (* A step induced by transition *)
      Inductive step: config -> config -> Prop :=
      | step_stay q1 s1 q2 s2 tape:
          δ q1 s1 q2 s2 stay -> step { q1 @ s1::tape } { q2 @ s2::tape }
      | step_left q1 s1  q2 s2 tape:
          δ q1 s1 q2 s2 movL -> step { q1 @ s1::tape } { q2 @ rotr 1 (s2::tape) }
      | step_right q1 s1 q2 s2 tape:
          δ q1 s1 q2 s2 movR -> step { q1 @ s1::tape } { q2 @ rot 1 (s2::tape) }.

      (* Reflexive transitive closure of step *)
      Inductive many_steps: nat -> config -> config -> Prop :=
      | ms_self c: many_steps 0 c c
      | ms_more n c1 c2 c3:
          step c1 c2 -> many_steps n c2 c3 -> many_steps n.+1 c1 c3.
      
      Lemma many_steps_trans n m c1 c2 c3:
        many_steps n c1 c2 -> many_steps m c2 c3 -> many_steps (n+m) c1 c3.
      Proof.
        move:c1; elim n.
        -{ by move=>?; inversion 1. }
        -{ move:n=>_ n IH ?; rewrite addSn; inversion 1 as[|????? ms02].
           move/(IH _ ms02); econstructor; eassumption. }
      Qed.
 
      Lemma many_steps_last n c1 c2 c3:
        many_steps n c1 c2 -> step c2 c3 -> many_steps n.+1 c1 c3.
      Proof.
        rewrite-addn1; move=>c1c2 ?; apply/(many_steps_trans c1c2).
        by econstructor; [eassumption|constructor].
      Qed.
      
      Lemma many_steps_inv n m c1 c2:
        n < m -> many_steps m c1 c2 ->
      exists c, many_steps n c1 c /\ many_steps (m-n) c c2.
      Proof.
        move:m c1; elim n=>//=.
        -{ by move=>m c1 _ ?; exists c1; rewrite subn0; split; [constructor|]. }
        -{ move:n=>_ n IH [|m]// c1 ltnm; inversion 1 as[|????? ms32].
           move:{IH}(IH _ _ ltnm ms32)=>[c][].
           exists c; split; [econstructor; eassumption|assumption]. }
      Qed.

      Lemma size_many_steps n c1 c2:
        many_steps n c1 c2 -> size(_tape c1) == size(_tape c2).
      Proof.
        move: c1; elim n.
        -{ by move=>?; inversion 1. }
        -{ by move:n=>_ n IH ?; inversion 1 as [|???? [] ms02];
              move:(IH _ ms02)=>/eqP<-/=; rewrite?size_rotr?size_rot/=. }
      Qed.
    End Step.

    Section Determinism.
      Definition δ_deterministic := 
        forall q s q1 s1 d1 q2 s2 d2,
          δ q s q1 s1 d1 -> δ q s q2 s2 d2 -> (q1==q2) && (s1==s2) && (d1==d2).
      
      Variable det: δ_deterministic.

      Lemma det_many_steps n c c1 c2:
        many_steps n c c1 -> many_steps n c c2 -> c1 == c2.
      Proof.
        move:c; elim n.
        -{ by move=>c; do 2 inversion 1. }
        -{ move:n=>_ n IH; inversion_clear 1 as[|?? c3? st3 ms31];
             inversion 1 as[|?? c4? st4 ms42]; move:ms31 ms42.
           rewrite(_:c3=c4); first apply IH.
           by move:st3 st4; inversion 1 as[????? d3|????? d3|????? d3];
              inversion 1 as[????? d4|????? d4|????? d4];
              move:(det d3 d4)=>/andP[/andP[/eqP->/eqP->]/eqP]. }
      Qed.

      Definition no_more_step c := forall c1, ~ step c c1.
      Definition run_to_stop n c1 c2 := many_steps n c1 c2 /\ no_more_step c2.

      Lemma det_stop c n1 c1 n2 c2:
        run_to_stop n1 c c1 -> run_to_stop n2 c c2 -> (n1 == n2) && (c1 == c2).           Proof.
        wlog: n1 n2 c1 c2 / n1<= n2. {
          case_eq(n1<=n2)=>le12; first by apply.
          have:n2<=n1 by move:le12=>/negP/negP; rewrite-ltnNge; apply ltnW.
          move=>le21 H r1 r2; move:(H _ _ _ _ le21 r2 r1)=>/andP[]/eqP->/eqP->.
          by apply/andP. }
        rewrite leq_eqVlt=>/orP[/eqP->|lt12][ms1 ns1][ms2 ns2].
        -{ by move:(det_many_steps ms2 ms1)=>/eqP->; apply/andP=>[]. }
        -{ move:(many_steps_inv lt12 ms2)=>[c0][ms0 ms12]; exfalso.
           move:(det_many_steps ms1 ms0)lt12 ms12=>/eqP E; subst.
           rewrite-subn_gt0; move:(n2-n1)=>[|k]//_; inversion 1.
           eapply ns1; eassumption. }
      Qed.
    End Determinism.

  End Transition.

End Base.


(* Definition of cyclic turing machines *)
Record cyclicTM: Type := { 
  Q: finType;			(* set of states *)
  Σ: finType;			(* set of symbols *)
  δ:> @transition Q Σ;	(* transition (which TM itself will be used as) *)
  q0: Q;			(* initial state *)
  qf: Q;			(* final state and its condition *) 
  input_tape: seq Σ;		(* initial tape *)
}.
Arguments input_tape: clear implicits.

Section Run.

  Variable M: cyclicTM.

  Inductive reachable n: config -> Prop :=
  | reachable_to c:
      many_steps M n { q0 M @ input_tape M } c -> reachable n c.

  Definition run n tape: Prop := reachable n { qf M @ tape }.
  Definition terminating: Prop := exists n0, forall n c, n0 < n -> ~ reachable n c.
  Definition no_stuck: Prop :=
    forall n c, reachable n c -> no_more_step M c -> _state c == qf M.
  Definition deterministic := δ_deterministic M.

End Run.

Arguments run: clear implicits.
Arguments reachable: clear implicits.

(* **** Solution **** *)
Section SolutionMachine.

  (* set of states *)
  Section States.

    Inductive Q_zc:Type := q_in | q_fn | q_pr | q_cl | q_bk | q_ck.

    Section Embedding.
      Definition q2ord (q:Q_zc): 'I_6.
        by apply Ordinal with
            (match q with q_in=>0|q_fn=>1|q_pr=>2|q_cl=>3|q_bk=>4|q_ck=>5 end);
           case q.
      Defined.
      Definition ord2q (o:'I_6): Q_zc.
        by case o=>m ltm6;
           apply(match m with 0=>q_in|1=>q_fn|2=>q_pr|3=>q_cl|4=>q_bk|_=>q_ck end).
      Defined.
      Definition q_cancel: cancel q2ord ord2q. by case. Defined.
    End Embedding.

    (* to be eqType and finType *)
    Definition q_eq q1 q2 := q2ord q1 == q2ord q2.
    Definition q_eqP: Equality.axiom q_eq. by do 2 case; constructor. Defined.
    Canonical Q_zc_eqType     := EqType Q_zc (EqMixin q_eqP).
    Canonical Q_zc_choiceType := ChoiceType Q_zc (CanChoiceMixin q_cancel).
    Canonical Q_zc_countType  := CountType Q_zc (CanCountMixin q_cancel).
    Canonical Q_zc_finType    := FinType Q_zc (CanFinMixin q_cancel).
  End States.

  (* [zc_card]: the number of symbols.
   * From the problem description, we assume that at least two symbols:
   *   _0 [zero] for zero clear;
   *   _1 [one]  for one of the symbols other than zero.
   * Otherwise, problem becomes meaningless. *)
  Parameter (zc_card:nat) (zc_ax: 1 < zc_card).

  Section Symbols.
    Definition Σ_zc: predArgType := 'I_zc_card.
    Definition _0: Σ_zc. by apply Ordinal with 0; move:zc_ax; auto. Defined.
    Definition _1: Σ_zc. by apply Ordinal with 1; move:zc_ax; auto. Defined.
  End Symbols.

  Section Transition.
    Inductive δ_zc: transition :=
    | δ_zc_init s:		δ_zc q_in  s q_pr _1 movR
    | δ_zc_start s:		δ_zc q_pr  s q_cl _0 movR
    | δ_zc_found:		δ_zc q_cl _1 q_bk _0 movL
    | δ_zc_clear s: s != _1 ->	δ_zc q_cl  s q_cl _1 movR
    | δ_zc_back:		δ_zc q_bk _1 q_bk _0 movL
    | δ_zc_check:		δ_zc q_bk _0 q_ck _0 movL
    | δ_zc_done:		δ_zc q_ck _0 q_fn _0 stay
    | δ_zc_notyet:		δ_zc q_ck _1 q_pr _1 movR.
  End Transition.

  (* definition of zero-clear cyclic Turing machine *)
  Definition zero_clear_CTM tape0: cyclicTM := Build_cyclicTM δ_zc q_in q_fn tape0.

End SolutionMachine.


Ltac try_step :=
  econstructor; [solve[repeat constructor=>//]|] => /=;
  try(rewrite/rotr/rot/=;
      match goal with |- many_steps _ _ ?e _ =>
        tryif match e with context[take _ _] => idtac | _ => fail end 
        then fail else idtac e
      end).

Section HowItWorks.

  Axiom zc_ax2: 2 < zc_card. (* to make examples interesting *) 
  Definition _2: Σ_zc. by apply Ordinal with 2, zc_ax2. Defined.

  Ltac run_check := eexists; constructor => //=; repeat try_step; constructor.  

  Example how_works_for_01210201_: 
    exists n, run (zero_clear_CTM [:: _0; _1; _2; _1; _0; _2; _0; _1]) n
                              [:: _0; _0; _0; _0; _0; _0; _0; _0].
  Proof. run_check. Qed.

  Example how_works_for_21_: 
    exists n, run (zero_clear_CTM [:: _2; _1]) n
                              [:: _0; _0].
  Proof. run_check. Qed.

  Example how_works_for_2_: 
    exists n, run (zero_clear_CTM [:: _2]) n
                              [:: _0].
  Proof. run_check. Qed.

End HowItWorks.


Section Correctness.
  
  (* Suppose that the input tape [tape0] has length greater than 1. *)

  Variable (tape0: seq Σ_zc) (zc_tape_ax: 0 < size tape0).

  Let zc_CTM := zero_clear_CTM tape0.
  Let zc_many_steps := many_steps zc_CTM.

  Lemma zc_det: deterministic zc_CTM.
  Proof. by intros; do 2 inversion 1=>//; subst; exfalso; move: H0=>/eqP. Qed.

  Definition map_0s (tape:seq Σ_zc):= map (fun _=>_0) tape.

  Lemma zc_cl_to_bk tape1 tape2 s:
    _1 \notin tape1 ->
    exists n, zc_many_steps n { q_cl @ tape1 ++ _1 :: tape2 ∺ s }
                          { q_bk @ s :: map_0s tape1 ++ _0 :: tape2 }.
  Proof.
    move:s tape2; elim tape1=>//.
    -{ intros; exists 1; try_step; rewrite-rcons_cons rotr1_rcons; constructor. }
    -{ move:tape1=>_ ? ? IH s tape2.
       rewrite in_cons eq_sym cat_cons=>/norP[]?/(IH _1(tape2∺s))[n IHn].
       exists(n.+2); try_step; rewrite rot1_cons rcons_cat rcons_cons.
       eapply many_steps_last; first eassumption.
       rewrite-rcons_cons-rcons_cat-(rotr1_rcons s); do 2 constructor. }
  Qed.

  Lemma zc_bk_to_cl tape1:
    zc_many_steps 3 { q_bk @ _0 :: tape1 ∺ _1 }
                    { q_cl @ tape1 ∺ _1 ∺ _0 }.
  Proof.
    try_step; rewrite-rcons_cons rotr1_rcons.
    try_step. rewrite cats1.
    try_step; rewrite rot1_cons; constructor.
  Qed.

  Lemma zc_cl_to_cl_one tape1:
    _1 \in tape1 ->
    exists n tape2, zc_many_steps n { q_cl @ tape1 ∺ _1 ∺ _0 }
                                { q_cl @ tape2 ∺ _1 ∺ _0 } /\
                count_mem _1 tape2 < count_mem _1 tape1.
  Proof.
    move/mem_cat_first
      =>[tape11][tape12]/andP[]/(zc_cl_to_bk(tape12∺_1)_0).
    rewrite-rcons_cons-rcons_cons-rcons_cat-rcons_cat=>[[? clbk]]/eqP->.
    move:clbk; rewrite-rcons_cons-rcons_cat=>clbk.
    move:(many_steps_trans clbk (zc_bk_to_cl _))=>?.
    eexists; eexists; split; first eassumption.
    rewrite 2!count_cat/=2!addnA ltn_add2r addn0.
    have->:(count_mem _1 (map_0s tape11)=0) by clear; elim tape11=>//=.
    by rewrite addn_gt0; apply/orP; right.
  Qed.

  Lemma zc_cl_to_cl_ones tape1:
    exists n tape2, zc_many_steps n { q_cl @ tape1 ∺ _1 ∺ _0 }
                                { q_cl @ tape2 ∺ _1 ∺ _0 } /\ _1 \notin tape2.
  Proof.
    remember(count_mem _1 tape1) as k eqn:E.
    move:E (leqnn k)=>{1}->; move:tape1; elim k=>/=.
    -{ move=>tape1; rewrite leqn0=>cntz.
       by exists 0, tape1; split; first constructor; move:cntz=>/eqP/count_memPn. }
    -{ move:k=>_ k IH tape1 cnSk.
       case_eq(_1\in tape1)=>/negP/negP otp1;
         last by exists 0, tape1; split; first constructor.
       move:(zc_cl_to_cl_one otp1)=>[n][tape2][]clcl12 Lt.
       move:ltnS{Lt cnSk}(leq_trans Lt cnSk)=>->/IH[m][tape3][]clcl23?.
       exists(n+m),tape3; split; last done; apply(many_steps_trans clcl12 clcl23). }
  Qed.

  Lemma zc_zero_clear tape:
    0 < size tape -> exists n, zc_many_steps n { q_in @ tape } { q_fn @ map_0s tape }.
  Proof.
    case:tape=>[|s1//[//|s2 tape]]//=_;
      first by eexists; repeat try_step; constructor.
    have incl:(zc_many_steps 2 { q_in @ [:: s1,s2&tape] } { q_cl @ tape ∺ _1 ∺ _0})
      by do 2(try_step; rewrite/rot/=);rewrite take0 drop0 cats1 cats1; constructor.
    move:(zc_cl_to_cl_ones tape)=>[?][tape1][clcl].
    move/(zc_cl_to_bk nil _0);rewrite/=-3!cat_rcons 2!cats0-rcons_cons=>[[? clbk]].
    have bkfn:(zc_many_steps 2 { q_bk @ (_0 :: map_0s tape) ∺ _0 }
                               { q_fn @ [:: _0, _0 & map_0s tape]})
      by rewrite rcons_cons; try_step;
         rewrite-rcons_cons rotr1_rcons; try_step; constructor.
    eexists; eapply(many_steps_trans incl);
             eapply(many_steps_trans clcl); eapply(many_steps_trans clbk).
    rewrite(_:map_0s tape1 = map_0s tape); first eassumption.
    have size12:(size tape==size tape1)
      by move:(size_many_steps clcl); rewrite 4!size_rcons 2!eqSS.
    move:size12; clear; move:tape; elim tape1=>/=.
    - by move=>?; rewrite size_eq0=>/eqP->.
    - by move:tape1=>_ _ ? IH[|??]//=; rewrite eqSS=>/IH->.
  Qed.

  Lemma zc_final c: _state c == q_fn -> no_more_step zc_CTM c.
  Proof. by case:c=>q ?/=/eqP->c1; inversion 1; inversion H3. Qed.

  Lemma zc_reachable:
    exists n, reachable zc_CTM n { q_fn @ map_0s tape0 }.
  Proof. by move:(zc_zero_clear zc_tape_ax)=>[n ?]; exists n; constructor. Qed.

  Lemma zc_run: exists n, run zc_CTM n (map_0s tape0).
  Proof. by move:zc_reachable=>[m]; inversion 1; exists m; constructor. Qed.

  Theorem zc_terminating: terminating zc_CTM.
  Proof.
    move:zc_reachable=>[n0]; inversion_clear 1 as[? msn0]; exists n0 => n c ltn0n.
    inversion 1 as[? msn]; move:(many_steps_inv ltn0n msn)=>[?][ms].
    move:(det_many_steps zc_det ms msn0)=>/eqP->.
    move:ltn0n; rewrite-subn_gt0; move:(n-n0)=>[//|k _]; inversion 1 as[|???? sfn].
    by move:sfn; eapply zc_final.
  Qed.

  Theorem zc_no_stuck: no_stuck zc_CTM.
  Proof.
    move=>n c [] cf msc nsc; move:zc_reachable=>[?]; inversion 1 as[? ms].
    have ns0:(no_more_step zc_CTM { q_fn @ map_0s tape0 }) by apply zc_final.
    by move:(det_stop zc_det (conj msc nsc)(conj ms ns0))=>/andP[_]/eqP->/=.
  Qed.

  Theorem zc_correctness n tape: 
    run zc_CTM n tape -> tape == map_0s tape0.
  Proof.
    move:zc_run=>[m]; inversion 1 as[? ms]; inversion 1 as[? ms0].
    have ns:(no_more_step zc_CTM { qf zc_CTM @ map_0s tape0 }) by apply zc_final.
    have ns0:(no_more_step zc_CTM { qf zc_CTM @ tape }) by apply zc_final.
    by move:(det_stop zc_det (conj ms ns) (conj ms0 ns0))=>/andP[_]/eqP[]->.
  Qed.

End Correctness.

