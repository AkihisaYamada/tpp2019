From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
Require Coq.omega.Omega.
Import ListNotations.

Inductive bit : Type :=
| zero
| one.

Inductive tapechar : Type :=
| b (bi : bit)
| null.

Notation "'ONE'" := (b one).
Notation "'ZERO'" := (b zero).

(* ONE or ZERO  is written, or nothing is written (null) on a tape *)

Inductive mvstatus : Type :=
| r
| l
.


Inductive rewritestatus : Type :=
| rewr (b : bit)
| nothing
.

(* A machine can rewrite the tape to ONE or ZERO. 
   A machine doesn't have to rewrite the tape.  *)

Definition trans_func {states:Type}: Type := states -> option tapechar -> states*rewritestatus*mvstatus.

Inductive Machine {states : Type} : Type :=
| machine (func : @trans_func states) (init : states) (halt : states).

Definition m_func {states : Type} (m : @Machine states) : @trans_func states :=
  match m with
  | machine f _ _ => f
  end.

Definition m_init {states : Type} (m : @Machine states) : states :=
  match m with
  | machine _ s _ => s
  end.

Definition m_halt {states : Type} (m : @Machine states) : states :=
  match m with
  | machine _ _ s => s
  end.

Definition tape : Type := list tapechar.

(* Let [a0;...;an] be a tape.
   the left of ai is ai-1 ( if i = 0 then the left of ai is an )
   the right of ai is ai+1 ( if i = n then the right ai is a0 )
 *)

Fixpoint rem_tape_do (t : tape) (pos : nat) (bi : bit) : tape :=
  match t with
  | [] => []
  | h::t' =>
    match pos with
    | O => (b bi)::t'
    | S pos' => h::rem_tape_do t' pos' bi
    end
  end.

Definition remake_tape (t : tape) (pos : nat) (rs : rewritestatus) : tape :=
  match rs with
  | nothing => t
  | rewr bi => rem_tape_do t pos bi
  end.

Definition new_pos (len : nat) (ms : mvstatus) (pos : nat) : nat :=
  match ms with
  | r => if (S pos =? len) then O
         else S pos
  | l => match pos with
         | O => (len - 1)
         | S pos' => pos'
         end
  end.


Definition one_step_func {states : Type} (l : tape) (m : @Machine states) (s : states) (pos : nat)
  : tape*states*nat  :=
  match m with
  | machine func init halt
    => match (func s (nth_error l pos)) with
       | (s',rs,ms) =>
         (remake_tape l pos rs , s' , new_pos (length l) ms pos)
       end
  end.
  
(* one_step_func returnes
    the new tape
and the new states
and the new position
 *)

(* we haven't concidered about "halt"
   So, we need to make the "halt state" *)

Definition pick_tape {X Y Z :Type} (t : X*Y*Z) : X :=
  match t with
  | (x,_,_) => x
  end.

Definition pick_state {X Y Z :Type} (t : X*Y*Z) : Y :=
  match t with
  | (_,y,_) => y
  end.

Definition pick_pos {X Y Z :Type} (t : X*Y*Z) : Z :=
  match t with
  | (_,_,z) => z
  end.

Fixpoint nth_step {states : Type} (l : tape) (m : @Machine states) (s : states) (pos : nat) (n : nat)
  : tape*states*nat :=
  match n with
  | O => (l,s,pos)
  | S n' => match m with
            | machine func init halt
              => match (one_step_func l m s pos) with
                 | (newl,news,newpos) => nth_step newl m news newpos n'
                 end
            end
  end.

Fixpoint nth_step2 {states : Type} (l : tape) (m : @Machine states) (s : states) (pos : nat) (n : nat)
  : tape*states*nat :=
  match n with
  | O => (l,s,pos)
  | S n' => match m with
            | machine func init halt
              => match (nth_step2 l m s pos n') with
                 | (nt,ns,np) => one_step_func nt m ns np
                 end
            end
  end.

(* nth_step and nth_step2 ncompute n times *)

Fixpoint nth_step_display {states : Type} (l : tape) (m : @Machine states) (s : states) (pos : nat) (n : nat)
  : list (tape*states*nat) :=
  match n with
  | O => [(l,s,pos)]
  | S n' => match m with
              machine func init halt
              => match (one_step_func l m s pos) with
                 | (l',s',pos') => (l,s,pos)::nth_step_display l' m s' pos' n'
                 end
            end
  end.



(* now let's proove nth_step = nth_step2 *)

Lemma nth_step_equal_lem : forall k (states :Type) l m (s : states) pos n,
    n <= k ->
    nth_step l m s pos n = nth_step2 l m s pos n.
Proof.
  intros k.
  induction k as [|k' IH]; intros states l m s pos n H0.
  - destruct n. + reflexivity. + apply Nat.nle_succ_0 in H0. destruct H0.
  - destruct n as [|n'] eqn:E; try reflexivity.
    simpl. destruct m eqn:Em. apply Peano.le_S_n in H0.
    assert (H0':n' <= k'); try assumption.
    assert (H0'':n' <= k'); try assumption.
    apply (IH _ l m s pos) in H0. rewrite <- Em in *. rewrite <- H0.
    destruct (one_step_func l m s pos) as [[newl news] newpos] eqn:Eone.
    apply (IH _ newl m news newpos) in H0'. rewrite H0'. destruct n' as[|n''] eqn:En'.
    + simpl. symmetry. apply Eone.
    + assert (n'' <= k') as L2.
      { apply (le_trans _ (S n'')).
        + apply le_S. apply le_n. + apply H0''. }
      simpl. rewrite Em. rewrite <- Em.
      rewrite Eone. apply (IH _ newl m news newpos) in L2.
      rewrite L2. reflexivity.
Qed.

Lemma nth_step_equal : forall (states :Type) l m (s : states) pos n,
    nth_step l m s pos n = nth_step2 l m s pos n.
Proof.
  intros states l m s pos n; apply (nth_step_equal_lem n); apply le_n.
Qed.

Inductive machine_stop {states : Type} (l : tape) (m : @Machine states)
          (s : states) (pos : nat) : Prop :=
| stop (H : s = m_halt m) : machine_stop l m s pos
| continue  : forall l' s' pos',
    one_step_func l m s pos = (l',s',pos') ->
    machine_stop l' m s' pos'-> machine_stop l m s pos .

Theorem machine_stop_if_finish : forall (states : Type) m
                                         (a : states) (t : tape) (pos : nat),
    (exists n : nat, pick_state (nth_step t m a pos n) = m_halt m) ->
    machine_stop t m a pos.
Proof.
  intros states m a t pos [n H].
  generalize dependent pos. generalize dependent t. generalize dependent a.
  induction n as[|n' IH]; intros a t pos H.
  - simpl in H. rewrite H. apply stop. reflexivity.
  - unfold nth_step in H. destruct (one_step_func t m a pos) as[x1 np] eqn:E2.
    destruct x1 as[nt ns] eqn:E3. destruct m as [func init halt] eqn:Em.
    simpl in H. apply continue  in E2. apply E2. apply IH. apply H.
Qed.

Theorem finish_if_machine_stop : forall (states : Type) m
                                        (a : states) (t : tape) (pos : nat),
    machine_stop t m a pos ->
    exists n : nat, pick_state (nth_step t m a pos n) = m_halt m.
Proof.
  intros state m a t pos H0.
  induction H0 as [t m s pos H | t m a  pos l' s' pos' H0 H1 IH].
  - exists 0. rewrite H. reflexivity.
  - destruct IH as [n IH]. exists (S n). destruct m as [func init halt] eqn:E.
    unfold nth_step. rewrite H0. apply IH.
Qed.

(*Definition machine_stop_by_func (states : Type) (m : @Machine states) (l : tape) :
    exists n:nat, pick_state (nth_step l m (m_init m) 0 n) = m_halt m. Abort.*)

(* we assume that the length of the tape is grater than 1 *)

Inductive all_clear_states : Type :=
| a0 (* initial state *)
| a0'
| a0''
| a_go_right
| a_1_left (* rewrite to 1 *)
| a_0_left
| a_check
| a_restart (* read 1 and go right *)
| a_restart'
| a_reflesh (* the next states is a_go_right *)
| a_finish
| a_finish_loop. (* halt state *)

Definition all_clear_trans_func (s : all_clear_states) (t : option tapechar)
  : all_clear_states*rewritestatus*mvstatus :=
  match t with
  | None => (a_finish_loop,nothing,r)
  | Some c =>
    match s with
    | a0 => (a0',rewr zero,r)
    | a0' => (a0'',rewr one,r)
    | a0'' => (a_go_right,rewr zero,r)
    | a_go_right => match c with
                    | b one => (a_1_left,nothing,l)
                    | b zero => (a_go_right,nothing,r)
                    | null => (a_go_right,rewr zero,r)
                    end
    | a_1_left => (a_0_left,rewr one,l)
    | a_0_left => match c with
                  | b one => (a_check,nothing,l)
                  | _ => (a_0_left,nothing,l)
                  end
    | a_check => match c with
                 | b one => (a_finish,rewr zero,r)
                 | _ => (a_restart,nothing,r)
                 end
    | a_restart => (a_restart',nothing,r)
    | a_restart' => match c with
                    | b one => (a_reflesh,rewr zero,r)
                    | _ => (a_restart',nothing,r)
                    end
    | a_reflesh => (a_go_right,rewr zero,r)
    | a_finish => (a_finish_loop,rewr zero,r)
    | a_finish_loop => (a_finish_loop,nothing,r)
    end
  end.

Definition zero_clear_machine :=
  machine all_clear_trans_func a0 a_finish_loop.

Fixpoint list_maker {X:Type} (x:X) (n:nat) : list X :=
  match n with
  | O => []
  | S n' => x::list_maker x n'
  end.

Compute (nth_step
              [b zero;b zero;b zero;null;b one;null;b zero;b one;b zero;null]
              zero_clear_machine
              (m_init zero_clear_machine)
              0
              46).

Compute (nth_step_display
              [b zero;b zero;b zero;null;b one;null;b zero;b one;b zero;null]
              zero_clear_machine
              (m_init zero_clear_machine)
              0
              46).


Example zero_clear_example :
  exists n, nth_step
              [b zero;b zero;b zero;null;b one;null;b zero;b one;b zero;null]
              zero_clear_machine
              (m_init zero_clear_machine)
              0
              n
            = (list_maker (b zero) 10,m_halt zero_clear_machine,2).
Proof. exists 46. reflexivity. Qed.

Theorem finish_loop_without_change_the_tape : forall n m t,
    pick_state (nth_step t zero_clear_machine a_finish_loop m n) =
    a_finish_loop /\
    pick_tape (nth_step t zero_clear_machine a_finish_loop m n) =
    t.
Proof.
  intros n.
  induction n as[|n' IH]; intros m t.
  - split; reflexivity.
  - destruct (S m =? length t) eqn:E.
    + (*rewrite <- (IH 0 t). *)
      assert (nth_step t zero_clear_machine a_finish_loop m (S n') =
              nth_step t zero_clear_machine a_finish_loop 0 n') as L.
      { simpl. unfold all_clear_trans_func. simpl. apply beq_nat_true in E. rewrite <- E.
        destruct (nth_error t m); simpl; rewrite Nat.eqb_refl; reflexivity. }
      rewrite L. apply IH.
    + simpl. unfold all_clear_trans_func. destruct (nth_error t m); simpl; apply IH.
Qed.

Theorem length2_stop_clear : forall (t:tape),
    length t = 2 -> nth_step t zero_clear_machine
                             (m_init zero_clear_machine)
                             0
                             8 = ([ZERO;ZERO],a_finish_loop,0).
Proof.
  intros t H.
  destruct t as [| x1 t']; try discriminate.
  destruct t' as [|x2 t'']; try discriminate.
  destruct t'' ; try discriminate. reflexivity.
Qed.

Theorem length3_stop_clear : forall (t:tape),
    length t = 3 -> nth_step t  zero_clear_machine
                             (m_init zero_clear_machine)
                             0
                             10 = ([ZERO;ZERO;ZERO],a_finish_loop,2).
Proof.
  intros t H.
  destruct t as [| x1 t']; try discriminate.
  destruct t' as [|x2 t'']; try discriminate.
  destruct t'' as [|x3 t''']; try discriminate.
  destruct t'''; try discriminate. reflexivity.
Qed.

Lemma one_step_back : forall (t:tape) (n:nat) (states : Type) m (s:states) p r2 s2 p2,
    nth_step t m s p (S n) = (r2,s2,p2) ->
    exists r' s' p',
      nth_step t m s p n = (r',s',p') /\
      one_step_func r' m s' p' = (r2,s2,p2).
Proof.
  intros t n states m s p r2 s2 p2 H1.
  rewrite nth_step_equal in H1. simpl in H1.
  destruct (nth_step2 t m s p n) as [[nt ns] np] eqn:En.
  exists nt. exists ns. exists np. rewrite nth_step_equal.
  split. - apply En. - destruct m. apply H1.
Qed.

Lemma n_m_step : forall (t:tape) (n1 n2:nat) (states : Type) m (s:states) (p:nat)
                        t2 s2 p2 t3 s3 p3,
  nth_step t m s p n1 = (t2,s2,p2) ->
  nth_step t2 m s2 p2 n2 = (t3,s3,p3) ->
  nth_step t m s p (n1 + n2) = (t3,s3,p3).
Proof.
  intros t n1. generalize dependent t.
  induction n1 as [|n1' IH];
    intros t n2 states m s p t2 s2 p2 t3 s3 p3 H0 H1.
  - simpl. 
    injection H0 as L1 L2 L3.
    subst. apply H1.
  - simpl in H0. simpl.
    destruct m as [func init halt] eqn:Em. rewrite <- Em in *.
    destruct (one_step_func t m s p ) as [[t' s'] p'] eqn:Eone.
    rewrite (IH _ _ _ _ _ _ _ _ _ _ _ _ H0 H1).
    reflexivity.
Qed.

Lemma nth_error_equiv_lem : forall (X:Type) (l:list X) (n:nat),
    nth_error l n = None <->
    length l <= n.
Proof.
  intros X l n.
  generalize dependent l.
  induction n as [|n' IH]; intros l.
  - split.
    + intros H. destruct l; try discriminate. simpl. apply le_n.
    + intros H. destruct l; try reflexivity. simpl in H. apply Nat.nle_succ_0 in H.
      contradiction.
  - split.
    + intros H.
      destruct l as[|h l'].
      * simpl. apply le_0_n.
      * simpl in H. simpl. apply le_n_S. apply IH. apply H.
    + intros H. destruct l as[|h l']; try reflexivity. simpl. apply IH.
      simpl in H. apply le_S_n in H. apply H.
Qed.

Lemma remake_length_not_change : forall t pos rs t',
    pos < length t ->
    remake_tape t pos rs = t' ->
    length t = length t'.
Proof.
  intros t pos rs.
  generalize dependent t.
  destruct rs as [[]|] eqn:Ers.
  - simpl.
    induction pos as[|pos' IH]; intros t t'; simpl; intros H0 H1.
    + unfold rem_tape_do in H1.
      destruct t.
      * apply Nat.nle_succ_0 in H0. contradiction.
      * rewrite <- H1. reflexivity.
    + destruct t as[|h tail] eqn:Et.
      * apply Nat.nle_succ_0 in H0. contradiction.
      * simpl in H0. simpl in H1. apply le_S_n in H0. rewrite <- H1.
        simpl. apply f_equal. apply IH.
        { apply H0. } { reflexivity. }
  - simpl.
    induction pos as[|pos' IH]; intros t t'; simpl; intros H0 H1.
    + unfold rem_tape_do in H1.
      destruct t.
      * apply Nat.nle_succ_0 in H0. contradiction.
      * rewrite <- H1. reflexivity.
    + destruct t as[|h tail] eqn:Et.
      * apply Nat.nle_succ_0 in H0. contradiction.
      * simpl in H0. simpl in H1. apply le_S_n in H0. rewrite <- H1.
        simpl. apply f_equal. apply IH.
        { apply H0. } { reflexivity. }
  - intros t t' H1 H2. subst. reflexivity.
Qed.

Lemma one_step_func_pos : forall (states:Type) (t:tape) m (s:states) pos r2 s2 p2,
    pos < length t ->
    one_step_func t m s pos = (r2,s2,p2) ->
    length t = length r2 /\ p2 < length t.
Import Coq.omega.Omega.
Proof.
  intros states t m s pos r2 s2 p2 H0 H1.
  destruct m as [func init halt] eqn:Em.
  unfold one_step_func in H1.
  destruct (func s (nth_error t pos)) as [[s' rs] ms].
  injection H1 as L1 L2 L3.
  split.
  - apply (remake_length_not_change _ _ _ _ H0 L1).
  - unfold new_pos in L3. apply le_lt_or_eq in H0.
    destruct H0 as [H0|H0].
    + destruct ms.
      * destruct (S pos =? length t) eqn:E; omega.
      * destruct pos; omega.
    + destruct ms.
      * destruct (S pos =? length t) eqn:E. { omega. }
        { apply Nat.eqb_eq in H0. rewrite H0 in E.
          discriminate. }
      * destruct pos; omega.
Qed.

Lemma length_pos_lem : forall (states:Type) (t:tape) (n:nat) m (s:states) pos r2 s2 p2,
    t <> [] -> pos < length t ->
    nth_step t m
             s
             pos
             n = (r2,s2,p2) ->
    length t = length r2 /\ p2 < length t.
Proof.
  intros states t n. generalize dependent t.
  induction n as[|n' IH]; intros t.
  - simpl. intros m s pos r2 s2 p2 H0 H0' H1. injection H1 as H2 H3 H4.
    subst. split; try reflexivity.
    destruct r2. + exfalso. apply H0. reflexivity. + apply H0'.
  - intros m s pos r2 s2 p2 H0 H0' H1. apply one_step_back in H1.
    destruct H1 as [r' [s' [p' [H1 H2]]]]. apply (IH _ _ _ _ _ _ _ H0 H0') in H1.
    destruct H1 as [H1' H1''].
    assert (r' <> []) as L2.
    { destruct r'; destruct t; try discriminate.
      apply H0. }
    rewrite H1' in H1''. rewrite H1'. apply (one_step_func_pos _ _ _ _ _ _ _ _ H1'' H2).
Qed.

Lemma rewrite_tape_lem : forall t n bi t',
    t <> [] -> n < length t ->
    rem_tape_do t n bi = t' ->
    (forall l, l < n -> nth_error t l = nth_error t' l) /\
    (forall l, n < l -> l < length t -> nth_error t l = nth_error t' l) /\
    nth_error t' n = Some (b bi).
Proof.
  intros t n.
  generalize dependent t.
  induction n as [|n' IH]; intros t bi t' H9 H1 H2.
  - destruct t eqn:E.
    + exfalso. apply H9. reflexivity.
    + simpl in H2. destruct t'; try discriminate. injection H2 as H3 H4.
      split.
      { intros l H5. apply Nat.nle_succ_0 in H5. contradiction. }
      split.
      { intros l H5 H6. rewrite H4.
        destruct l; try apply Nat.nle_succ_0 in H5; try contradiction.
        reflexivity. }
      { subst. reflexivity. }
  - destruct t as [|ht tt] eqn:Et; try contradiction.
    destruct t' as [|ht' tt'] eqn:Et'; try discriminate.
    simpl in H2. injection H2 as H3.
    destruct tt as [|ht2 tt2] eqn:Ett.
    + simpl in H1. apply le_S_n in H1. apply Nat.nle_succ_0 in H1. contradiction.
    + rewrite <- Ett in *. 
      assert (tt <> []) as L1.
      { rewrite Ett. intros H6. discriminate. }
      simpl in H1. apply le_S_n in H1. apply (IH _ _ _ L1 H1) in H as [H'1 [H'2 H'3]].
      split.
      { intros l H4.
        apply le_lt_or_eq in H4.
        destruct H4 as [H4 | H4].
        - apply le_S_n in H4.
          destruct l as [|l'] eqn:El.
          + rewrite H3. reflexivity.
          + simpl. apply H'1. omega.
        - injection H4 as H4'.
          rewrite H4'. destruct n' as [|n''] eqn:En'; try (subst; reflexivity).
          simpl. apply H'1. apply le_n. }
      split.
      { intros l H4 H5.
        destruct l as[|l'] eqn:El; try (apply Nat.nle_succ_0 in H4; contradiction).
        simpl. apply H'2; apply le_S_n; assumption. } { assumption. }
Qed.

Lemma a_go_left_for_case_ONE1 :forall n' n'' t m',
    forall (result : tape) (state : all_clear_states) (pos : nat),
       nth_step t zero_clear_machine (m_init zero_clear_machine) 0 m' =
       (result, state, pos) -> n' = S n'' -> 3 <= n' ->
       (exists k,
         (forall l : nat, 3 <= l -> l < k -> nth_error result l = Some ZERO) /\
         (forall l : nat, k < l -> l < length t ->
                          nth_error result l = nth_error t l) /\
         nth_error result k = Some ONE /\
         state = a_0_left /\
         pos = n'' /\
         nth_error result 0 = Some ZERO /\ nth_error result 1 = Some ONE /\
         nth_error result 2 = Some ZERO /\
         S n' < length t /\
         t <> [] /\ n' <= k ) ->
       exists m, forall (result' : tape) (state' : all_clear_states) (pos' : nat),
           nth_step t zero_clear_machine (m_init zero_clear_machine) 0 m =
           (result', state', pos') ->
           pos' = n'' /\
           result = result' /\
           state' = a_restart'.
(* goes to the 0posision and come back *)
Proof.
  intros n'.
  induction n' as [|n''2 IH].
  - intros. discriminate.
  - (* n' = S n'' *)
    intros n'' t m' result state pos H0 H1 H2 [k H3]. injection H1 as H1. subst n''2.
    destruct H3 as [L1 [L2 [L [L4 [L5 [L6 [L7 [L8 [L9 [L10 L11]]]]]]]]]].
    apply le_lt_or_eq in H2.
    (* 3 < n' or 3 = n' *)
    apply or_comm in H2.
    destruct H2 as [H2|H2].
    
    (* case 3 = S n' *)
    + injection H2 as H2.
      exists (m' + 4).
      assert (nth_step result zero_clear_machine
                       state pos 4
              = (result,a_restart',pos)) as T1.
      { rewrite L5. rewrite <- H2.
        assert (length t = length result) as L12.
      { apply (length_pos_lem _ _ _ _ _ _ _ _ _ L10) in H0.
        - destruct H0; assumption.
        - destruct t; try contradiction.
          simpl. apply le_n_S. apply le_0_n. }
      rewrite L12 in L9. rewrite <- H2 in L9.
        destruct result as [|x0 [|x1 [|x2 [|x3 [|x4 resulttail]]]]] eqn:Et; simpl in L9;
        try (simpl in L9;
             repeat (
                 try (apply Nat.nle_succ_0 in L9; contradiction);
                 try apply le_S_n in L9)).
        rewrite L4. simpl in L6. simpl in L7. simpl in L8.
        injection L6 as L6. injection L7 as L7. injection L8 as L8.
        rewrite L6,L7,L8. simpl. reflexivity. }
      intros result' state' pos' T2.
      rewrite (n_m_step _ _ _ _ _ _ _ _ _ _ _ _ _ H0 T1) in T2.
      injection T2 as T2' T2'' T2'''.
      subst. split; try reflexivity; try split; try reflexivity.

      (* case 3 < S n' 
         hence, 3 <= n' *)
    + apply le_S_n in H2.
      destruct n'' as [|n'''] eqn:En'';
        try (apply Nat.nle_succ_0 in H2; contradiction).
      rewrite <- En'' in *.
      destruct pos as [|pos'] eqn:Epos;
        try (rewrite <- L5 in H2; apply Nat.nle_succ_0 in H2; contradiction).
      (* first, compute S m' steps for IH *)
      assert (
          forall result2 state2 pos2,
                 nth_step t zero_clear_machine (m_init zero_clear_machine) 0 (S m')
                 = (result2,state2,pos2) ->
                 result = result2 /\ state = state2 /\ pos' = pos2) as T1.
      { intros result2 state2 pos2 R1. rewrite nth_step_equal in R1.
        simpl in R1. simpl in H0. rewrite <- nth_step_equal in R1. rewrite H0 in R1.
        assert (nth_error result pos = Some ZERO) as R2.
        { apply L1.
          - rewrite Epos. rewrite L5. apply H2.
          - rewrite Epos. rewrite L5. apply L11. }
        rewrite Epos in R2. rewrite R2 in R1. rewrite L4 in R1. simpl in R1.
        injection R1 as R1' R1'' R1'''. subst.
        split; try reflexivity; try split; try reflexivity. }
      destruct (nth_step t zero_clear_machine (m_init zero_clear_machine)
                         0 (S m')) as [[result2 state2] pos2] eqn:ESm'.
      destruct (T1 result2 state2 pos2) as [T2 [T3 T4]]; try reflexivity.
      subst result2. subst state2. subst pos2.
      
      (* make an assert for IH *)
      assert (
          exists k : nat,
            (forall l : nat, 3 <= l -> l < k -> nth_error result l = Some ZERO) /\
            (forall l : nat, k < l -> l < length t
                             -> nth_error result l = nth_error t l) /\
            nth_error result k = Some ONE /\
            state = a_0_left /\
            pos' = n''' /\
            nth_error result 0 = Some ZERO /\
            nth_error result 1 = Some ONE /\
            nth_error result 2 = Some ZERO /\ S n'' < length t /\ t <> [] /\ n'' <= k)
        as T2.
      {
        exists k.
        repeat (try split; try assumption).
        * rewrite En'' in L5. injection L5 as L5. apply L5.
        * apply le_trans with (S (S (S n'')));
            try (apply le_S; apply le_n); try assumption.
        * apply (le_trans _ (S n'') _); omega. }
      apply (IH _ _ _ _ _ _ ESm' En'' H2) in T2. destruct T2 as [m_2 T2].
      destruct (nth_step t zero_clear_machine (m_init zero_clear_machine)
                         0 m_2) as [[result_3 state_3] pos_3] eqn:Em_2.
      destruct (T2 result_3 state_3 pos_3) as [T3 [T4 T5]]; try reflexivity.
      subst pos_3. subst result_3. subst state_3.
      assert (
          forall result3 state3 pos3,
                 nth_step t zero_clear_machine (m_init zero_clear_machine) 0 (S m_2)
                 = (result3,state3,pos3) ->
                 result = result3 /\ state3 = a_restart' /\ pos = pos3) as J1.
      { intros result3 state3 pos3 J2.
        rewrite nth_step_equal in J2.
        simpl in J2. rewrite <- nth_step_equal in J2. simpl in Em_2.
        rewrite Em_2 in J2.
        assert (nth_error result n''' = Some ZERO) as J3.
        { apply le_lt_or_eq in H2.
          destruct H2 as [H2|H2].
          - apply L1.
            + rewrite En'' in H2. apply le_S_n. apply H2.
            + rewrite En'' in L11. apply le_trans with (S (S n''')); try assumption.
              apply le_S. apply le_n.
          - rewrite En'' in H2. injection H2 as H2. rewrite <- H2. apply L8. }
        rewrite J3 in J2. simpl in J2.
        assert (length t = length result) as L12.
        { apply (length_pos_lem _ _ _ _ _ _ _ _ _ L10) in H0.
          - destruct H0; assumption.
          - destruct t; try contradiction.
            simpl. apply le_n_S. apply le_0_n. }
        assert (exists ls', length result = S ls') as J4.
        { destruct t; try contradiction. destruct result as [|h re']; try discriminate.
          exists (length re'). reflexivity. }
        destruct J4 as [ls' J4]. rewrite J4 in J2.
        assert (n''' < ls') as J5.
        { apply le_S_n. rewrite <- J4. rewrite <- L12. rewrite <- En''.
          apply (le_trans _ (S (S (S n'')))); omega. }
        destruct (n''' =? ls') eqn:Enls.
        - apply Nat.eqb_eq in Enls. omega.
        - injection J2 as J2 J2' J2''. rewrite J2. rewrite <- J2'. rewrite <- J2''.
          rewrite Epos. rewrite L5. rewrite En''.
          split; try reflexivity; try (split; reflexivity). }
      exists (S m_2). intros result4 state4 pos4 J2.
      destruct (J1 _ _ _ J2) as [J1' [J1'' J1''']].
      rewrite J1'. rewrite J1''. rewrite <- J1'''. rewrite Epos. rewrite L5.
      split; try reflexivity; try (split; reflexivity).
Qed.

Proposition a_go_left_lemma1 : forall (n : nat) (t : tape),
    3 <= n -> n < length t ->
    exists m : nat, forall result state pos,
        nth_step t zero_clear_machine
               (m_init zero_clear_machine)
               0
               m = (result,state,pos) ->
        (forall l : nat,
            3 <= l -> l <= n -> nth_error result l = Some ZERO) /\
        (forall l : nat,
            n < l -> l < length t -> nth_error result l = nth_error t l) /\
        state = a_go_right /\
        (S n = length t -> pos = 0) /\
        (S n < length t -> pos = S n) /\
        nth_error result 0 = Some ZERO /\
        nth_error result 1 = Some ONE /\
        nth_error result 2 = Some ZERO.
Proof.
  intros n t.
  induction n as [| n' IH].
  - intros H. apply le_n_0_eq in H. discriminate.
  - intros H0 H1.
    assert (t<>[]) as Ltnotnull.
    { destruct t.
      - simpl in H1. apply Nat.nle_succ_0 in H1. contradiction.
      - intros. discriminate. }
    apply le_lt_or_eq in H0. (* 3 <= S n' -> 3 < S n' \/ 3 = S n'*)
    apply or_comm in H0.
    destruct H0 as [H0 | H0].
    (* case 3 = S n' ( = n ) *)
    + rewrite <- H0 in *. clear H0.
      destruct t as [|x1 t'] eqn:Et.
      { simpl in H1. apply Nat.nle_succ_0 in H1. contradiction. }
      destruct t' as [|x2 t''] eqn:Et'.
      { simpl in H1. omega. }
      destruct t'' as [|x3 t'''] eqn:Et''; try (simpl in H1; omega).
      destruct t''' as [|x4 t''''] eqn:Et'''; try (simpl in H1; omega).
      destruct x4 as [[|]|] eqn:Ex4; [exists 4|exists 10|exists 4].
      * (* case x4 = ZERO *)
        intros result state pos H2. simpl in H2. injection H2 as P1 P2 P3.
        split.
        { intros l L1 L2. assert (l = 3) as L3; try omega.
          rewrite L3, <- P1. reflexivity. }
        split.
        { intros l L1 L2.
          destruct result as [|r1 [|r2 [|r3[|r4 result'''']]]]; try discriminate.
          injection P1 as T1 T2 T3 T4. rewrite H.
          assert (exists l', l = S (S (S (S l')))) as L3.
          { destruct l as [|[|[|[|l']]]]; try omega. exists l'. reflexivity. }
          destruct L3 as [l' L3]. rewrite L3. reflexivity. }
        split.
        { rewrite P2. reflexivity. }
        split.
        { intros L1. destruct t''''; try discriminate.
          simpl in P3. rewrite P3. reflexivity. }
        split.
        { intros L1.
          destruct t''''.
          - simpl in L1. apply Nat.nle_succ_diag_l in L1. contradiction.
          - simpl in P3. rewrite P3. reflexivity. }
        rewrite <- P1. split; try split; reflexivity.
      * (* case x4 = ONE *)
        intros result state pos H2. simpl in H2. injection H2 as P1 P2 P3.
        split.
        { intros l L1 L2. assert (l = 3) as L3; try omega. rewrite L3, <- P1. reflexivity. }
        split.
        { intros l L1 L2.
          destruct result as [|r1 [|r2 [|r3[|r4 result'''']]]]; try discriminate.
          injection P1 as T1 T2 T3 T4. rewrite H.
          assert (exists l', l = S (S (S (S l')))) as L3.
          { destruct l as [|[|[|[|l']]]]; try omega. exists l'. reflexivity. }
          destruct L3 as [l' L3]. rewrite L3. reflexivity. }
        split.
        { rewrite P2. reflexivity. }
        split.
        { intros L1. destruct t''''; try discriminate.
          simpl in P3. rewrite P3. reflexivity. }
        split.
        { intros L1.
          destruct t''''.
          - simpl in L1. apply Nat.nle_succ_diag_l in L1. contradiction.
          - simpl in P3. rewrite P3. reflexivity. }
        rewrite <- P1. split; try split; reflexivity.
      * (* case x4 = null *)
        intros result state pos H2. simpl in H2. injection H2 as P1 P2 P3.
        split.
        { intros l L1 L2. assert (l = 3) as L3; try omega. rewrite L3, <- P1. reflexivity. }
        split.
        { intros l L1 L2.
          destruct result as [|r1 [|r2 [|r3[|r4 result'''']]]]; try discriminate.
          injection P1 as T1 T2 T3 T4. rewrite H.
          assert (exists l', l = S (S (S (S l')))) as L3.
          { destruct l as [|[|[|[|l']]]]; try omega. exists l'. reflexivity. }
          destruct L3 as [l' L3]. rewrite L3. reflexivity. }
        split.
        { rewrite P2. reflexivity. }
        split.
        { intros L1. destruct t''''; try discriminate.
          simpl in P3. rewrite P3. reflexivity. }
        split.
        { intros L1.
          destruct t''''.
          - simpl in L1. apply Nat.nle_succ_diag_l in L1. contradiction.
          - simpl in P3. rewrite P3. reflexivity. }
        rewrite <- P1. split; try split; reflexivity.

    (* case 3 < S n' (hence 3 <= n' ^ ^ ) *)

    + apply Peano.le_S_n in H0.
      assert (L3len':3 <= n'); try apply H0.
      apply IH in H0 as [m' H2]; 
        try (apply (le_trans _ ((S (S n'))));
             try (apply le_S; apply le_n); try apply H1).
      clear IH.
      (* n' < length t was prooved already ^ ^ *)
      
      destruct (nth_error t (S n')) as [[[|]|]|] eqn:E.
      (* case analysis by a_Sn (t = [a0; ... ; a_Sn; ... ]) *)
      * (* case a_Sn = ZERO *)
        exists (S m'). intros result state pos H10.
        apply one_step_back in H10. destruct H10 as [result' [state' [pos' [H10' H10'']]]].
        assert (nth_step t zero_clear_machine (m_init zero_clear_machine) 0 m' =
         (result', state', pos')) as L10; try apply H10'.
        apply H2 in H10' as [H15 [H16 [H17 [H18 [H19 H20]]]]]. rewrite H17 in H10''.
        assert (S n' < length t) as L1; try assumption. apply H19 in L1.
        rewrite L1 in H10''. assert (n' < S n') as L2; try apply le_n.
        assert (S n' < length t) as L3; try assumption. apply (H16 (S n') L2) in L3.
        assert (
            one_step_func result' zero_clear_machine a_go_right (S n') =
          (result, state, pos)) as Lone_step; try apply H10''.
        simpl in H10''. assert (nth_error result' (S n') = nth_error t (S n')) as Lresult_t;
          try apply L3. simpl in L3. rewrite L3 in H10''.
        assert (nth_error t (S n') = Some ZERO) as Lnth_t; try apply E.
        simpl in E. rewrite E in H10''. simpl in H10''. injection H10'' as L4 L5 L6.
        split.
        (* split 1 *)
        { intros l' H11 H12. apply le_lt_or_eq in H12. destruct H12 as [H12| H12].
          (* case 3 <= l' <= n' (i.e. this case is included IH) and
                       l' = S n' (one_step after) *)
          { apply Peano.le_S_n in H12. rewrite <- L4. apply (H15 _ H11 H12). }
          (* case l' = S n' *)
          { rewrite H12. rewrite <- L4. simpl. rewrite L3. rewrite E. reflexivity. } }
        split.
        (* split 2 *)
        { intros l H3 H4.
          assert (n' < l) as L7.
          { apply (le_trans _ (S n')); try apply le_n. 
            apply (le_trans _ (S (S n'))); try (apply le_S;apply le_n); try apply H3. }
          apply (H16 l L7) in H4. rewrite <- H4. subst. reflexivity. }
        split.
        (* split 3 *)
        { subst.  reflexivity. }
        split.
        (* split 4 *)
        { intros H11. rewrite <- L1 in H11. rewrite <- L1 in Lone_step.          
          simpl in Lone_step. rewrite L4 in Lone_step. rewrite L4 in Lresult_t.
          rewrite L1 in Lone_step. rewrite Lresult_t in Lone_step.
          rewrite Lnth_t in Lone_step. unfold new_pos in Lone_step.
          assert (0 < length t) as P1.
          { destruct t.
            - discriminate.  - simpl. apply Peano.le_n_S. apply Peano.le_0_n. }            
            destruct (length_pos_lem _ _ _ _ _ _ _ _ _ Ltnotnull P1 L10) as [LL1 LL2].
            rewrite L4 in LL1. rewrite <- LL1 in Lone_step. rewrite <- H11 in Lone_step.
            rewrite L1 in Lone_step. simpl in Lone_step. rewrite Nat.eqb_refl in Lone_step.
            injection Lone_step as J1 J2. symmetry. apply J2. }
        split.
        (* split 5 *)
        { intros H11. rewrite <- L1 in H11. rewrite <- L1 in Lone_step.          
          simpl in Lone_step. rewrite L4 in Lone_step. rewrite L4 in Lresult_t.
          rewrite L1 in Lone_step. rewrite Lresult_t in Lone_step.
          rewrite Lnth_t in Lone_step. unfold new_pos in Lone_step.
          assert (0 < length t) as P1.
          { destruct t.
            - discriminate. - simpl. apply Peano.le_n_S. apply Peano.le_0_n. }            
            destruct (length_pos_lem _ _ _ _ _ _ _ _ _ Ltnotnull P1 L10) as [LL1 LL2].
            rewrite L4 in LL1. rewrite <- LL1 in Lone_step. rewrite L1 in H11.
            assert (S (S n') =? length t = false) as P2.
            { apply Nat.eqb_neq. intros H11'. rewrite H11' in H11.
              apply Nat.nle_succ_diag_l in H11. apply H11. }
            rewrite P2 in Lone_step. simpl in Lone_step. injection Lone_step as P3 P4.
            symmetry. apply P4. }
        rewrite <- L4. apply H20.
      * (* case a_Sn = ONE *)
        destruct (nth_step t zero_clear_machine
                           (m_init zero_clear_machine) 0 m')
          as [[result' state'] pos'] eqn:Em'th.
        destruct (H2 result' state' pos') as [L1 [L2 [L3 [L4 [L5 L6]]]]];
          try reflexivity.
        clear H2. (* let's compute a one step *)
        assert (
            forall (result : tape) (state : all_clear_states) (pos : nat),
              nth_step t zero_clear_machine (m_init zero_clear_machine) 0 (S m') =
              (result, state, pos) ->
              state = a_1_left /\
              pos = n'/\ result = result' /\
              nth_error result 0 = Some ZERO /\ nth_error result 1 = Some ONE /\
              nth_error result 2 = Some ZERO) as H2'.
        { intros result state pos H0. rewrite nth_step_equal in H0.
          simpl in H0. rewrite <- nth_step_equal in H0. simpl in Em'th.
          rewrite Em'th in H0. apply L5 in H1 as H1'.
          assert (nth_error result' pos' = Some ONE) as L7.
          { rewrite <- E. rewrite H1'. apply L2. - apply le_n. - apply H1. }
          rewrite L7 in H0. rewrite L3 in H0.
          simpl in H0. rewrite H1' in H0. injection H0 as H0' H0'' H0'''.
          split; try split; try split; try subst; try reflexivity; try assumption.
          }
        destruct (nth_step t zero_clear_machine
                           (m_init zero_clear_machine) 0 (S m'))
          as [[result'' state''] pos''] eqn:ESm'th.
        destruct (H2' result'' state'' pos'') as [R1 [R2 [R3 [R4 [R5 R6]]]]];
          try reflexivity. clear H2'.
        assert (exists n'', n' = S n'') as Ln'.
        { destruct n' as[|n''].
          - apply Nat.nle_succ_0 in L3len'. contradiction.
          - exists n''. reflexivity. }
        destruct Ln' as [n'' Ln'].
        assert ( (* let's compute one more step *)
            forall (result : tape) (state : all_clear_states) (pos : nat),
              nth_step t zero_clear_machine (m_init zero_clear_machine) 0 (S (S m')) =
              (result,state,pos) ->
              (forall l : nat, 3 <= l -> l < n' -> nth_error result l = Some ZERO) /\
              (forall l : nat, n' < l -> l < length t ->
                               nth_error result l = nth_error t l) /\
              nth_error result n' = Some ONE /\
              state = a_0_left /\
              pos = n'' /\
              nth_error result 0 = Some ZERO /\ nth_error result 1 = Some ONE /\
              nth_error result 2 = Some ZERO) as H2''.
        { intros result state pos H0. rewrite nth_step_equal in H0.
          assert (exists d, d = S m') as Sm'd; try exists (S m'); try reflexivity.
          destruct Sm'd as [d Sm'd]. rewrite <- Sm'd in H0. simpl in H0. 
          rewrite <- nth_step_equal in H0. rewrite Sm'd in H0. rewrite <- Sm'd in ESm'th.
          simpl in ESm'th. rewrite Sm'd in ESm'th. rewrite ESm'th in H0. subst result''.
          rewrite L1 in H0.
          - rewrite R1 in H0. simpl in H0.
            destruct pos'' as [|pos'''] eqn:Epos''.
            + rewrite <- R2 in *. apply Nat.nle_succ_0 in L3len'. contradiction.
            + injection H0 as T1 T2 T3. rewrite R2 in *.
              apply length_pos_lem in ESm'th as [T5 T6];
                try assumption;
                try( destruct t; try contradiction; simpl;
                  apply le_n_S; apply Peano.le_0_n).
              assert (result' <> []) as T4.
              {  destruct t; try contradiction.
                 intros T7. destruct result'; discriminate. }
              rewrite T5 in T6.
              apply (rewrite_tape_lem _ _ _ _ T4 T6) in T1 as [T1'1 [T1'2 T1'3]].
              split.
              { intros l J1 J2. rewrite <- T1'1 by apply J2.
                apply (L1 l J1). apply le_trans with (S l).
                - apply le_S. apply le_n. - apply J2. }
              split.
              { intros l J1 J2. rewrite T5 in J2. rewrite <- (T1'2 l J1 J2).
                rewrite <- T5 in J2. apply (L2 l J1 J2). }
              split. { apply T1'3. }
              split. { subst; reflexivity. }
              split.
              { rewrite Ln' in R2. rewrite <- T3.
                injection R2; intros; assumption. }
              split; try split; try (rewrite <- T1'1; try assumption);
                try apply le_trans with 3 try omega; try omega.
          - omega. - omega. } (* H2'' is defined *)
        (* 2 steps were computed from m' *)
        destruct (nth_step t zero_clear_machine
                           (m_init zero_clear_machine)
                           0 (S (S m'))) as [[result_2 state_2] pos_2] eqn:ESSm'.
        destruct (H2'' result_2 state_2 pos_2)
          as [T1 [T2 [T3 [T4 [T5 T6]]]]]; try reflexivity.
        clear H2''.
        (** 2 steps after m'' was computed **)
        (** result_2 state_2 pos_2 **)

        assert (
            exists m, forall (result' : tape) (state' : all_clear_states) (pos' : nat),
                nth_step t zero_clear_machine (m_init zero_clear_machine) 0 m =
                (result', state', pos') ->
                pos' = n'' /\
                result_2 = result' /\
                state' = a_restart') as H2.
        { apply (a_go_left_for_case_ONE1 n' n'' t (S (S m')) result_2 state_2 pos_2);
            try assumption.
          exists n'. destruct T6 as [T6 [T7 T8]].
          repeat (try split; try assumption). apply le_n. }
        destruct H2 as [m_3 H2].
        destruct (nth_step t zero_clear_machine
                           (m_init zero_clear_machine) 0 m_3)
          as [[result_3 state_3] pos_3] eqn:Em_3.
        (* after m_3 steps, the head of machine came back with 
            a_restart' *)
        destruct (H2 result_3 state_3 pos_3) as [U1 [U2 U3]]; try reflexivity.
        subst pos_3. subst result_3. destruct T6 as [T6 [T7 T8]].

        (* let's compute 3 steps *)

        assert (forall (result4 : tape) (state4: all_clear_states) (pos4 : nat),
                   nth_step t zero_clear_machine (m_init zero_clear_machine)
                            0 (S m_3) = (result4,state4,pos4) ->
                   pos4 = n' /\ result4 = result_2 /\ state4 = a_restart') as P1.
        { intros result4 state4 pos4 P2.
          rewrite nth_step_equal in P2. simpl in P2.
          rewrite <- nth_step_equal in P2. simpl in Em_3. rewrite Em_3 in P2.
          assert (nth_error result_2 n'' = Some ZERO) as P3.
          { apply le_lt_or_eq in L3len'.
            destruct L3len' as [L3len'|L3len'].
            - apply T1.
              + rewrite Ln' in L3len'. apply le_S_n in L3len'. assumption.
              + rewrite Ln'. apply le_n.
            - rewrite Ln' in L3len'. injection L3len' as L3len'.
              rewrite <- L3len'. assumption. }
          rewrite P3 in P2. rewrite U3 in P2. simpl in P2.
          assert (length t = length result_2) as P4.
          { apply (length_pos_lem _ t m_3 zero_clear_machine a0 0
                                  result_2 state_3 n''); try assumption.
            destruct t; try contradiction. simpl.
            apply le_n_S. apply le_0_n. }
          rewrite <- P4 in P2. destruct t as [|h t0] eqn:Et; try contradiction. simpl in P2.
          assert (n'' < length t0) as P5.
          { simpl in H1. apply le_S_n in H1. omega. }
          destruct (n'' =? length t0) eqn:Eeqb.
          - apply Nat.eqb_eq in Eeqb. omega.
          - injection P2 as P2' P2'' P2'''.
            subst. split; try reflexivity; split; try reflexivity. }
        destruct (nth_step t zero_clear_machine (m_init zero_clear_machine)
                           0 (S m_3)) as [[result4 state4] pos4] eqn:ESm_3.
        destruct (P1 result4 state4 pos4) as [P2 [P3 P4]]; try reflexivity.
        subst result4. subst state4. subst pos4.
        clear P1. clear H2. clear Em_3. clear ESSm'. clear R4. clear R5. clear R6.
        clear ESm'th. clear L1. clear L2. clear L3.

        (* next step *)

        assert (
            forall (result4 : tape) (state4 : all_clear_states) (pos4 : nat),
              nth_step t zero_clear_machine (m_init zero_clear_machine) 0 (S (S m_3)) =
              (result4,state4,pos4) ->
              (forall l : nat, 3 <= l -> l <= n' -> nth_error result4 l = Some ZERO) /\
              (forall l : nat, n' < l -> l < length t ->
                               nth_error result4 l = nth_error t l) /\
              state4 = a_reflesh /\
              pos4 = S n' /\
              nth_error result4 0 = Some ZERO /\ nth_error result4 1 = Some ONE /\
              nth_error result4 2 = Some ZERO) as H2''.
        { intros result4 state4 pos4 K1.
          assert (S (S m_3) = (S m_3) + 1) as K2; try omega.
          rewrite K2 in K1. rewrite nth_step_equal in K1.
          simpl in K1. rewrite <- plus_n_Sm in K1.
          rewrite <- plus_n_O in K1. rewrite <- nth_step_equal in K1.
          assert (m_init zero_clear_machine = a0) as K3; try reflexivity.
          rewrite K3 in ESm_3. rewrite ESm_3 in K1. rewrite T3 in K1. simpl in K1.
          assert (length t = length result_2) as K4.
          { apply (length_pos_lem _ t (S m_3) zero_clear_machine a0 0
                                  result_2 a_restart' n'); try assumption.
            destruct t; try contradiction. simpl. apply le_n_S. apply le_0_n. }
          rewrite <- K4 in K1. destruct t as [|h t0] eqn:Et; try contradiction. simpl in K1.
          assert (n' < length t0) as K5.
          { simpl in H1. omega. }
          destruct (n' =? length t0) eqn:Eeqb.
          - apply Nat.eqb_eq in Eeqb. omega.
          - injection K1 as K1' K1'' K1'''. rewrite <-  Et in *.
            assert (n' < length result_2) as K6; try omega. assert (result_2 <> []) as K7.
            { destruct result_2; try discriminate. }
            apply (rewrite_tape_lem result_2 n' zero result4 K7) in K6 as [K8 [K9 K10]];
              try assumption.
            split.
            { intros l K11 K12. apply le_lt_or_eq in K12.
              destruct K12 as [K12|K12].
              - rewrite <- K8 by apply K12. apply (T1 _ K11 K12).
              - rewrite K12. assumption. }
            split.
            { intros l K11 K12. rewrite K4 in K12. rewrite <- (K9 _ K11 K12).
              rewrite <- K4 in K12. apply (T2 _ K11 K12). }
            split. { rewrite K1''. reflexivity. }
            split. { rewrite K1'''. reflexivity. }
            split; try split;
              rewrite <- K8; try assumption; try omega. }
        destruct (nth_step t zero_clear_machine (m_init zero_clear_machine)
                           0 (S (S m_3))) as [[result4 state4] pos4] eqn:ESSm_3.
        destruct (H2'' result4 state4 pos4) as [K1 [K2 [K3 [K4 [K5 [K6 K7]]]]]];
          try reflexivity.
        clear H2''. clear ESm_3. clear T1. clear T3. clear T4. clear T2. clear T5.
        clear T6. clear T7. clear T8. clear U3. clear pos_2. clear result_2.
        clear state_2. clear state_3. clear Ln'. clear n''. clear R2. clear R1.
        clear state''. clear R3. clear result''. clear Em'th. clear pos''.
        clear L4. clear L5. clear L6. clear result'. clear state'. clear pos'.

        (* let's compute the final step ^ ^ *)

        exists (S (S (S m_3))).
        intros result state pos G1.
        assert (S (S (S m_3)) = S m_3 + 2) as G2; try omega.
        rewrite G2 in G1. rewrite nth_step_equal in G1.
        simpl in G1.
        assert (m_3 + 2 = S (S m_3)) as G3; try omega.
        rewrite G3 in G1.
        assert (m_init zero_clear_machine = a0) as G4; try reflexivity.
        rewrite G4 in ESSm_3. rewrite <- nth_step_equal in G1.
        rewrite ESSm_3 in G1.
        assert (nth_error result4 pos4 = Some ONE) as G5.
        { rewrite K2.
          - rewrite K4. assumption.
          - rewrite K4. apply le_n.
          - rewrite K4. assumption. }
        rewrite G5 in G1. rewrite K3 in G1. simpl in G1.
        assert (length t = length result4) as G6.
          { apply (length_pos_lem _ t (S (S m_3)) zero_clear_machine a0 0
                                  result4 state4 pos4); try assumption.
            destruct t; try contradiction. simpl.
            apply le_n_S. apply le_0_n. }
          rewrite <- G6 in G1.
          destruct t as[|h t0] eqn:Et; try contradiction. simpl in G1.
          rewrite <- Et in *. injection G1 as G1' G1'' G1'''.
          assert (result4 <> []) as G7. { destruct result4; discriminate. }
          assert (pos4 < length result4) as G8.
          { rewrite K4. rewrite <- G6. assumption. }
          apply (rewrite_tape_lem result4 pos4 zero result G7 G8) in G1' as [G9 [G10 G11]].
          subst pos4.
          split.
          { intros l G12 G13. apply le_lt_or_eq in G13.
            destruct G13 as[G13|G13].
            - rewrite <- G9 by apply G13. apply le_S_n in G13. apply (K1 l G12 G13).
            - rewrite G13. apply G11. }
          split.
          { intros l G12 G13. rewrite G6 in G13.
            rewrite <- (G10 l G12 G13). rewrite <- G6 in G13.
            assert (n' < l) as G14; try omega. apply (K2 l G14 G13). }
          split. { rewrite G1''. reflexivity. }
          split.
          { rewrite Et. simpl. intros G12. injection G12 as G12. apply Nat.eqb_eq in G12.
            rewrite G12 in G1'''. rewrite G1'''. reflexivity. }
          split.
          { rewrite Et. simpl. intros G12. apply le_S_n in G12.
            destruct (S n' =? length t0) eqn:Eeqb.
            - apply Nat.eqb_eq in Eeqb. omega.
            - rewrite G1'''. reflexivity. }
          split; try split;
            rewrite <- G9; try assumption; try omega.

          (* case a_Sn' = null *)
      * exists (S m').
        intros result' state' pos' K1.
        destruct (nth_step t zero_clear_machine (m_init zero_clear_machine)
                           0 m') as [[result state] pos] eqn:Em'.
        destruct (H2 result state pos) as[L1 [L2 [L3 [L4 [L5 [L6 [L7 L8]]]]]]];
          try reflexivity.
        clear H2. rewrite nth_step_equal in K1. simpl in K1.
        rewrite <- nth_step_equal in K1. simpl in Em'. rewrite Em' in K1.
        apply L5 in H1 as L5'.
        assert (nth_error result pos = Some null) as L9.
        { subst pos. assert (n' < S n') as L9; try apply le_n.
          rewrite (L2 (S n') L9 H1). assumption. }
        rewrite L9 in K1. rewrite L3 in K1. simpl in K1.
        assert (length t = length result) as L10.
          { apply (length_pos_lem _ t m' zero_clear_machine a0 0
                                  result state pos); try assumption.
            destruct t; try contradiction. simpl. apply le_n_S. apply le_0_n. }
          rewrite <- L10 in K1. destruct t as[|h t0] eqn:Et; try contradiction.
          simpl in K1. injection K1 as K1' K1'' K1'''.
          assert (result <> []) as L11. { destruct result; try discriminate. }
          assert (pos < length result) as L12.
          { rewrite L5'. rewrite <- L10. assumption. }
          apply (rewrite_tape_lem result pos zero result' L11 L12) in K1'
            as [L13 [L14 L15]].
          split.
          { intros l L16 L17. apply le_lt_or_eq in L17.
            destruct L17 as [L17|L17].
            - apply le_S_n in L17. rewrite <- (L1 l L16 L17). symmetry. rewrite L5' in *.
              apply L13. apply le_n_S. apply L17.
            - rewrite L17. rewrite L5' in L15. apply L15. }
          split.
          { intros l L16 L17. rewrite <- Et in *. assert (n' < l) as L18; try omega.
            rewrite <- (L2 l L18 L17). symmetry. rewrite L5' in *. rewrite L10 in L17.
            apply (L14 l L16 L17). }
          split; try (subst; reflexivity).
          split.
          { intros L16. simpl in L16. injection L16 as L16. apply Nat.eqb_eq in L16.
            rewrite L5' in K1'''. rewrite L16 in K1'''. rewrite K1'''. reflexivity. }
          split.
          { intros L16. simpl in L16. rewrite L5' in *.
            destruct (S n' =? length t0) eqn:Eeqb.
            - apply Nat.eqb_eq in Eeqb. omega.
            - rewrite K1'''. reflexivity. }
          split; try split;
            rewrite <- L13; try assumption; try omega.
          
          (* the last pattern doesn't happen *)
      * apply nth_error_equiv_lem in E. omega.
Qed.

Lemma check_marked_lem : forall (t:tape) (n':nat),
    3 < length t -> length t = S n' ->
    exists k, forall (result:tape) (state:all_clear_states) (pos:nat),
        nth_step t zero_clear_machine (m_init zero_clear_machine)
                 0 k = (result,state,pos) ->
        (forall l, 2 <= l -> l < length t -> nth_error result l = Some ZERO) /\
        state = a_0_left /\
        pos = n' /\
        nth_error result 0 = Some ONE /\
        nth_error result 1 = Some ONE.
Proof.
  intros t n' H0 H1. assert (3 <= n') as L1; try omega.
  assert (n' < length t) as L2; try omega. apply (a_go_left_lemma1 n' t L1) in L2 as L2'.
  destruct L2' as [m L2'].
  destruct (nth_step t zero_clear_machine (m_init zero_clear_machine) 0 m)
    as [[result0 state0] pos0] eqn:Em.
  destruct (L2' result0 state0 pos0) as [L3 [L4 [L5 [L6 [L7 [L8 [L9 L10]]]]]]];
    try reflexivity. clear L2'. symmetry in H1.
  apply L6 in H1 as H1'. simpl in Em.
  assert (length t = length result0) as L11.
  { apply (length_pos_lem _ t m zero_clear_machine a0 0
                          result0 state0 pos0); try assumption; try omega.
    destruct t; try simpl in H0; try omega; try discriminate. }
  

  destruct result0 as [|r0 [|r1 result0']] eqn:Eresult; try discriminate.
  simpl in L8. simpl in L9. injection L8 as L8. injection L9 as L9.
  exists (S (S (S m))). intros result state pos K1.
  destruct (nth_step result0 zero_clear_machine state0 pos0  3)
           as [[result' state'] pos'] eqn:Em3.
  assert ((result,state,pos) = (result',state',pos')) as K3.
  { assert (S (S (S m)) = m + 3) as K3; try omega.
    rewrite K3 in K1. rewrite <- K1. rewrite <- Eresult in Em.
    apply (n_m_step _ _ _ _ _ _ _ _ _ _ _ _ _ Em Em3). }
  injection K3 as K3' K3'' K3'''. subst result'. subst state'. subst pos'.
  rewrite L5, Eresult, H1' in Em3. rewrite L8,L9 in Em3. simpl in Em3.
  rewrite <- Eresult in *. injection Em3 as K4 K5 K6.
  destruct result as [|x0 [|x1 result']] eqn:Er; try discriminate. injection K4 as K7 K8 K9.
  split.
  { intros l K10 K11. apply le_lt_or_eq in K10.
    destruct K10 as [K10|K10].
    - assert (l <= n') as K12; try omega. rewrite <- (L3 l K10 K12). rewrite Eresult.
      rewrite K9. destruct l as [|[|l']] eqn:El; try omega. reflexivity.
    - destruct l as [|[|l']] eqn:El; try omega. simpl. rewrite <- K9.
      rewrite Eresult in L10. injection K10 as K10. rewrite <- K10. rewrite <- L10.
      reflexivity. }
  split. { rewrite <- K5. reflexivity. }
  split.
  { apply eq_add_S. rewrite H1. rewrite <- K6.
    replace (S (S (length result0'))) with (length (r0::r1::result0'));
      try reflexivity. rewrite <- Eresult. rewrite L11. reflexivity. }
  rewrite <- K7,<- K8. split; reflexivity.
Qed.

Lemma all_clear_final_steps : forall n t,
    3 <= n -> n < length t ->
    (exists m, forall result state pos,
          nth_step t zero_clear_machine
                   (m_init zero_clear_machine)
                   0
                   m = (result,state,pos) ->
          (forall l, 2 <= l -> l < length t -> nth_error result l = Some ZERO) /\
          state = a_0_left /\
          pos = n /\
          nth_error result 0 = Some ONE /\
          nth_error result 1 = Some ONE) ->
    exists k, forall gresult gstate gpos,
        nth_step t zero_clear_machine
                 (m_init zero_clear_machine)
                 0 k = (gresult,gstate,gpos) ->
        (forall l, l < length t -> nth_error gresult l = Some ZERO) /\
        gstate = a_finish_loop /\
        gpos = 2.
Proof.
  intros n t.
  induction n as [|n0 IH]; intros H1 H2 [m H3]; try omega.
  
  (* case n = S n0 *)
  destruct (nth_step t zero_clear_machine (m_init zero_clear_machine)
                     0 m) as [[result0 state0] pos0] eqn:Em.
  destruct (H3 result0 state0 pos0) as [T1 [T2 [T3 [T4 T5]]]];
    try reflexivity. clear H3.
  apply le_lt_or_eq in H1.
  apply or_comm in H1.
  destruct H1 as [H1|H1].

  (* S n0 = 3 *)
  - injection H1 as H1. subst n0. subst pos0.
    subst state0.
    assert (length t = length result0) as T6.
  { apply (length_pos_lem _ t m zero_clear_machine a0 0
                          result0 a_0_left 3); try assumption; try omega.
    destruct t; try simpl in H2; try omega; try discriminate. }
  rewrite T6 in H2.
  destruct result0 as [|x0 [|x1 [|x2 [|x3 result0']]]] eqn:Er0; try (simpl in H2; omega).
  simpl in T4. simpl in T5. injection T4 as T4. injection T5 as T5.
  subst x0. subst x1. rewrite <- T6 in H2.
  assert (Some x2 = Some ZERO /\ Some x3 = Some ZERO) as T7.
  { split; [rewrite <- (T1 2)|rewrite <- (T1 3)]; try omega; try reflexivity. }
  destruct T7 as [T7 T8]. injection T7 as T7. injection T8 as T8.
  subst x2. subst x3.
  exists (S (S (S (S (S m))))).
  intros gresult gstate gpos L1.
  assert (
      nth_step result0 zero_clear_machine a_0_left
               3 5 = (ZERO::ZERO::ZERO::ZERO::result0',a_finish_loop,2)) as L2.
  { rewrite Er0. simpl. reflexivity. }
  assert (
    (gresult,gstate,gpos) =
    (ZERO::ZERO::ZERO::ZERO::result0',a_finish_loop,2)) as L3.
  { rewrite <- L1.
    assert (S (S (S (S (S m)))) = m + 5) as L4; try omega.
    rewrite L4. rewrite Er0 in L2.
    apply (n_m_step _ _ _ _ _ _ _ _ _ _ _ _ _ Em L2 ). }
  injection L3 as L4 L5 L6.
  split.
  { intros l L7.
    destruct l as [|[| l']] eqn:El; try (rewrite L4; reflexivity).
    assert (2 <= l) as L8; try omega.
    rewrite <- El in L7.
    rewrite <- (T1 l L8 L7).
    rewrite El.
    destruct gresult as [|g1 [|g2 gresult']] eqn:Egr; try discriminate.
    injection L4 as L4 L4' L4''.
    rewrite  L4''. reflexivity. }
  rewrite L5,L6. split; reflexivity.

  (* 3 < S n0 (i.e. 3 <= n0 *)
  - assert (n0 < length t) as L1; try omega.
    apply le_S_n in H1.
    apply (IH H1 L1). clear IH.
    exists (S m).
    intros result state pos L2.
    rewrite nth_step_equal in L2.
    simpl in L2. rewrite <- nth_step_equal in L2.
    simpl in Em. rewrite Em in L2.
    assert (nth_error result0 pos0 = Some ZERO) as L3.
    { rewrite T3. assert (2 <= S n0) as L4; try omega.
      apply (T1 (S n0) L4 H2). }
    rewrite L3 in L2. rewrite T2 in L2. simpl in L2.
    rewrite T3 in L2. injection L2 as L2 L2' L2''.
    rewrite <- L2, <- L2', <- L2''.
    repeat (try split; try assumption; try reflexivity).
Qed.

Lemma zero_clear_stop_length_gt_3 : forall (t:tape),
    3 < length t ->
    exists m result,
      nth_step t zero_clear_machine (m_init zero_clear_machine)
               0 m = (result,a_finish_loop,2) /\
      (forall l, l < length t -> nth_error result l = Some ZERO).
Proof.
  intros t H1.
  assert (exists n', length t = S n') as L1.
  { destruct t as[|h t'] eqn:Et; try (simpl in H1;omega).
    exists (length t'). reflexivity. }
  destruct L1 as [n' L1].
  assert(
      exists m', forall result state pos,
          nth_step t zero_clear_machine
                   (m_init zero_clear_machine)
                   0
                   m' = (result,state,pos) ->
          (forall l, 2 <= l -> l < length t -> nth_error result l = Some ZERO) /\
          state = a_0_left /\
          pos = n' /\
          nth_error result 0 = Some ONE /\
          nth_error result 1 = Some ONE) as L2.
  { apply check_marked_lem; try omega. }
  assert (3 <= n') as L3; try omega.
  assert (n' < length t) as L4; try omega.
  apply (all_clear_final_steps _ _ L3 L4) in L2.
  destruct L2 as [k L2].
  destruct (nth_step t zero_clear_machine (m_init zero_clear_machine) 0 k)
    as [[gresult gstate] gpos] eqn:Ek.
  destruct (L2 gresult gstate gpos) as [L5 [L6 L7]];
    try reflexivity.
  exists k. exists gresult. subst gstate. subst gpos.
  split; assumption.
Qed.

Lemma all_clear_equiv : forall (X:Type) (t:list X) (x:X),
    t <> [] ->
    (forall l, l < length t -> nth_error t l = Some x) <->
    t = list_maker x (length t).
Proof.
  intros X t x H1.
  induction t as [|h0 t' IH]; try contradiction.
  destruct t' as [|h1 t''] eqn:Et'.
  - simpl.
    split.
    + intros H.
      assert (0 < 1) as L1; try omega.
      apply H in L1. simpl in L1. injection L1 as L1.
      rewrite L1. reflexivity.
    + intros H. injection H as H. rewrite H.
      intros l H2.
      destruct l; try omega.
      reflexivity.
  - assert (h1::t'' <> []) as L1; try discriminate.
    apply IH in L1. clear IH. destruct L1 as [L1 L1'].
    split.
    + intros H2. simpl. rewrite L1.
      * simpl.
        assert (0 < length (h0::h1::t'')) as L2; try (simpl;omega).
        apply H2 in L2. simpl in L2. injection L2 as L2.
        rewrite L2. reflexivity.
      * intros l H3.
        assert (S l < length (h0::h1::t'')) as L2; try (simpl in *;omega).
        apply H2 in L2. apply L2.
    + simpl. intros H3. injection H3 as H3 H3' H3''.
      rewrite H3,H3'. intros l H4. rewrite H3''.
      destruct l as[|l'] eqn:El.
      * reflexivity.
      * simpl in L1'. apply le_S_n in H4.
        assert (h1::t'' = x::list_maker x (length t'')) as L2.
        { rewrite H3'. rewrite <- H3''. reflexivity. }
        apply (L1' L2) in H4. simpl. rewrite <- L2. apply H4.
Qed.


(*** The main statement is following ***)
(*** case length t = 2 has been prooved above ***)

Theorem zero_clear_stop_theorem : forall t : tape,
    3 <= length t ->
    exists m,
      nth_step t zero_clear_machine (m_init zero_clear_machine) 0 m
      = (list_maker ZERO (length t),a_finish_loop,2).
Proof.
  intros t H0.
  destruct t as [|x0 [|x1 [|x2 [|x3 t']]]] eqn:Et;
    try (simpl in H0; omega).
  
  (* case length t = 3 *)
  - exists 10. reflexivity.
  (* case 3 < length t *)
  - assert (3 < length t) as L1; try (rewrite Et;simpl;omega).
    rewrite <- Et in *. apply zero_clear_stop_length_gt_3 in L1.
    destruct L1 as [m [result [L2 L3]]].
    assert (length t = length result) as L4.
    { apply (length_pos_lem _ t m zero_clear_machine a0 0
                            result a_finish_loop 2); try apply L2; try omega.
      intros H. rewrite H in Et. discriminate. }
    exists m. rewrite L4 in L3.
    assert (result <> []) as L5.
    { destruct result; rewrite Et in L4; try discriminate. }
    apply (all_clear_equiv _ _ _ L5) in L3. rewrite L4. rewrite <- L3. apply L2.
Qed.

(** The another version of the main statement **)

Theorem zero_clear_stop_theorem2 : forall t : tape,
    2 <= length t ->
    exists m,
      pick_tape
        (nth_step t zero_clear_machine (m_init zero_clear_machine) 0 m)
      = list_maker ZERO (length t) /\
      machine_stop t zero_clear_machine (m_init zero_clear_machine) 0.
Proof.
  intros t H0.
  destruct t as [|x0 [|x1 [|x2 t']]] eqn:Et;
    try (simpl in H0; omega).
  - exists 8.
    split. + reflexivity. + apply machine_stop_if_finish. exists 8. reflexivity.
  - assert (3 <= length t) as L0. { rewrite Et. simpl. omega. }
    apply zero_clear_stop_theorem in L0. rewrite <- Et. destruct L0 as [m L0]. exists m.
    split.
    + rewrite L0. reflexivity.
    + apply machine_stop_if_finish. exists m. rewrite L0. reflexivity.
Qed.

