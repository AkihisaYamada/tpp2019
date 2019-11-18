From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ********************* *)
Section TuringDef.
  Variable T Q:Type.

  Definition Turing1step (prog:Q -> T -> Q * T * bool)
             (x:Q * T * seq T) : Q * T * seq T :=
    let fx := prog x.1.1 x.1.2 in
    if fx.2 then (fx.1.1, head fx.1.2 x.2, behead (rcons x.2 fx.1.2))
    else (fx.1.1, last fx.1.2 x.2, belast fx.1.2 x.2).

  Variable (acc:Q).

  Inductive TuringHalt (prog:Q -> T -> Q * T * bool) x : Prop :=
  | TuringHalt_acc of x.1.1 = acc
  | TuringHalt_1step of TuringHalt prog (Turing1step prog x).

End TuringDef.
Section zclear.
  Variable T:eqType.
  Variable zero a b:T.
  Hypothesis Huniq : uniq [:: a; b; zero].

  Inductive Q : Type := Qinit | Qleft | Qright | Qleft2 | Qacc.

  Definition zclear (q:Q)(t:T) : Q * T * bool :=
    match q with
    | Qinit => (Qleft, a, true)
    | Qleft => if t == a then (Qright, b, false)
               else (Qleft, zero, true)
    | Qright => if t == b then (Qacc, zero, false)
                else if t == a then (Qleft2, a, true)
                     else (Qright, zero, false)
    | Qleft2 => if t == b then (Qleft, zero, true)
                else (Qleft2, zero, true)
    | Qacc => (Qacc, zero, true)
    end.

  Notation rmzero := (filter (fun t => t != zero)).
  Definition lhead := (head zero \o rmzero).
  Definition rhead := (last zero \o rmzero).

  Definition zclear_valid (x:Q * T * seq T) :=
    match x.1.1 with
    | Qinit => true
    | Qleft => rhead (x.1.2 :: x.2) == a
    | Qright => (lhead (rcons x.2 x.1.2) == b)
                  && let r := rhead (rcons x.2 x.1.2) in
                     ((r == a) ||
                      (r == b) && (size (rmzero (rcons x.2 x.1.2)) == 1))
    | Qleft2 => (lhead (x.1.2 :: x.2) == b) && (rhead (x.1.2 :: x.2) == a)
    | Qacc => all (fun t => t == zero) (rcons x.2 x.1.2)
    end.

  Lemma zclear_valid_1step (x:Q * T * seq T) :
    zclear_valid x -> zclear_valid (Turing1step zclear x).
  Proof.
    move /and3P: Huniq =>[]. rewrite !inE negb_or =>/andP[] Hab Haz Hbz _.
    rewrite /zclear_valid /Turing1step. case : x.1.1 =>[_||||]//=.
    - by rewrite -headI /rhead /= filter_rcons Haz last_rcons.
    - case Ha : (x.1.2 == a) =>/=.
      + rewrite -lastI /lhead /= Hbz /= eq_refl /rhead.
        move /eqP : Ha =>->/=. rewrite Haz Hbz /=.
        case : (rmzero x.2) =>[|t s /=/eqP->]; by rewrite !eq_refl ?orbT.
      + rewrite -headI /rhead /= filter_rcons eq_refl /=.
        case : ifP =>//=. case : (rmzero x.2)=>//=. by rewrite Ha.
    - case Hb : (x.1.2 == b) =>/andP[]/=.
      + move /eqP : Hb (Hab)=>->. rewrite -lastI /lhead /rhead /= filter_rcons.
        rewrite Hbz last_rcons !eq_refl size_rcons eq_sym =>/negbTE ->_/=/eqP[].
        elim : x.2 =>[|t s IHs]//=. case : ifP =>// /eqP->. by rewrite eq_refl.
      + case Ha : (x.1.2 == a) =>/=.
        * move /eqP : Ha =>->. rewrite -headI /rhead /= filter_rcons Haz.
            by rewrite last_rcons eq_refl =>->.
        * rewrite -lastI /lhead /rhead /= eq_refl /= filter_rcons.
          case : ifP =>[|_->]//=. by rewrite last_rcons Ha Hb.
    - case Hb : (x.1.2 == b) =>/andP[]/=.
      * move /eqP : Hb =>->. rewrite -headI /rhead /= filter_rcons eq_refl Hbz.
        case : (rmzero x.2) (Hab) =>//= /negbTE. by rewrite eq_sym =>->.
      * rewrite -headI /rhead /lhead /= filter_rcons eq_refl.
        case : ifP =>[|_->->]//=. by rewrite Hb.
    - case : x.2 =>[|s t]/=; rewrite ?eq_refl // !all_rcons =>/and3P[]->_->.
        by rewrite eq_refl.
  Qed.

  Lemma mem_lhead (t:T) (s:seq T) : t != zero -> lhead s == t -> t \in s.
  Proof.
    rewrite /lhead => Ht /= Hs. move /eqP : Hs Ht =><-/=.
    elim : s =>[|t' s IHs]/=; first by rewrite eq_refl.
    case : ifP; rewrite /= ?mem_head // in_cons =>_/IHs ->.
      by rewrite orbT.
  Qed.

  Lemma mem_rhead (t:T) (s:seq T) : t != zero -> rhead s == t -> t \in s.
  Proof.
    rewrite /rhead => Ht /= Hs. move /eqP : Hs Ht =><-/=.
    elim /last_ind : s =>[|s t' IHs]/=; rewrite ?eq_refl // filter_rcons.
    case : ifP; rewrite mem_rcons ?last_rcons ?mem_head // in_cons =>_/IHs ->.
      by rewrite orbT.
  Qed.

  Definition measure (x:Q * T * seq T) :=
    let s := x.1.2 :: x.2 in
    let rs := rcons x.2 x.1.2 in
    match x.1.1 with
    | Qinit => ((size rs).+1 * 3 * (size rs).+1).+2
    | Qleft => (find (pred1 a) s + (size s).+1 * 2
                + (size rs).+1 * 3 * size (rmzero rs)).+1
    | Qright => (find (predU (pred1 a) (pred1 b)) (rev rs) + (size s).+1
                + (size rs).+1 * 3 * size (rmzero rs)).+1
    | Qleft2 => (find (pred1 b) s
                + (size rs).+1 * 3 * size (rmzero rs)).+1
    | Qacc => 0
    end.

  Theorem zclear_halt (t:T) (s:seq T) : TuringHalt Qacc zclear (Qinit, t, s).
  Proof.
    move /and3P: Huniq =>[]. rewrite !inE negb_or =>/andP[] Hab Haz Hbz _.
    have : zclear_valid (Qinit, t, s) =>//.
    move : {-1}(measure (Qinit, t, s)) (leqnn (measure (Qinit, t, s))) => n.
    elim : n (Qinit, t, s) =>[|n IHn] p Hp Hvalid.
    - apply : TuringHalt_acc. move : Hp. rewrite /measure. by case : p.1.1.
    - apply : TuringHalt_1step. apply : IHn (zclear_valid_1step _)=>//.
      move : Hvalid Hp. rewrite /measure /zclear_valid /Turing1step.
      case : p.1.1 =>[_|H|/andP[] Hl Hr|/andP[] Hl _|]//=;
        rewrite ltnS; apply : leq_trans.
      + rewrite size_rcons size_behead !size_rcons /=.
        rewrite [_ * (size _).+2]mulnS. apply : leq_add.
        * rewrite [_ * 3]mulnS leq_add2r leqW //. case : ifP =>//_.
          apply : leq_trans (find_size _ _) _.
            by rewrite size_behead size_rcons. 
        * rewrite leq_mul // size_filter. apply : leq_trans (count_size _ _) _.
            by rewrite size_rcons size_behead size_rcons.
      + case Ha : (p.1.2 == a);
          rewrite /= !size_rcons ?size_belast ?size_behead ?size_rcons /=.
        * move /eqP : Ha =>->. rewrite add0n -addSn. apply : leq_add.
          rewrite mulnS muln1 ltn_add2r ltnS.
          apply : leq_trans (find_size _ _) _.
            by rewrite size_rev /= -lastI.
            by rewrite -lastI !filter_rcons /= Haz Hbz size_rcons.
        * rewrite -addSn. apply : leq_add.
          rewrite ltn_add2r. case : p.2 H =>[|t' s']/=.
          rewrite /rhead /=. case : ifP =>_/=; rewrite ?Ha // eq_sym.
            by move /negbTE : Haz =>->.
          case : ifP =>//. rewrite -cats1 find_cat =>Ht' /(mem_rhead Haz).
          rewrite !in_cons eq_sym Ha eq_sym Ht' /=. case : ifP =>// /hasPn H.
          move /H =>/=. by rewrite eq_refl.
          rewrite !size_filter -cats1 count_cat addnC -count_cat cat1s -headI.
          rewrite leq_mul // -!cats1 !count_cat /= eq_refl /= !addn0.
          exact : leq_addr.
      + case Hb : (p.1.2 == b) =>//=. case Ha : (p.1.2 == a) =>/=;
        rewrite !size_rcons ?size_behead ?size_rcons /= -addSn; apply : leq_add.
        * rewrite addnS ltnS. case : ifP =>//_. rewrite addnS ltnS.
          apply : leq_trans (find_size _ _) _. rewrite size_behead size_rcons.
          exact : leq_addl.
        * rewrite leq_mul // !size_filter -cats1 count_cat addnC -count_cat.
          rewrite cat1s -headI. by move /eqP : Ha =>->.
        * rewrite size_belast ltn_add2r -lastI rev_rcons /= Ha Hb /= rev_cons.
          rewrite ltnS -cats1 find_cat has_rev. case : ifP =>// /hasPn H.
          move /(mem_lhead Hbz) : Hl. rewrite mem_rcons in_cons eq_sym Hb /=.
          move /H =>/=. by rewrite eq_refl orbT.
        * rewrite size_belast -lastI -cats1. apply : leq_mul =>//.
            by rewrite !size_filter count_cat /= eq_refl /= add0n leq_addr.
      + case Hb : (p.1.2 == b) =>/=; case : ifP => Hp2; rewrite ?add0n;
        rewrite !size_rcons size_behead size_rcons /=.
        * move /eqP : Hb =>->. rewrite -cats1 filter_rcons Hbz size_rcons.
          rewrite [_ * _ * _.+1]mulnS -addSn. apply : leq_add;
          rewrite ?ltn_pmul2l // leq_mul // !size_filter count_cat addnC.
          rewrite -count_cat cat1s -headI -cats1 count_cat /= eq_refl.
            by rewrite !addn0.
        * move /eqP : Hb =>->. rewrite [filter _ (rcons _ b)]filter_rcons Hbz.
          rewrite size_rcons [_ * _ * _.+1]mulnS -addSn. apply : leq_add.
          rewrite [_ * 3]mulnS ltn_add2r !ltnS.
          apply : leq_trans (find_size _ _) _.
            by rewrite size_behead size_rcons.
          apply : leq_mul =>//. rewrite !size_filter -cats1 count_cat addnC.
          rewrite -count_cat cat1s -headI -cats1 count_cat /= eq_refl.
            by rewrite !addn0.
        * rewrite addSn ltnS. apply : leq_trans _ (leq_addl _ _).
          rewrite leq_mul // !size_filter -cats1 count_cat addnC -count_cat.
          rewrite cat1s -headI -!cats1 !count_cat /= eq_refl !addn0.
          exact : leq_addr.
        * rewrite -addSn. apply : leq_add.
          move /(mem_lhead Hbz) : Hl. rewrite in_cons eq_sym Hb /= -cats1.
          case : p.2 Hp2 =>//= t' s'. rewrite in_cons [b == _]eq_sym =>->.
          move =>/=. rewrite !ltnS find_cat. case : ifP =>// /hasPn H /H /=.
            by rewrite eq_refl.
          rewrite leq_mul // !size_filter -cats1 count_cat addnC -count_cat.
          rewrite cat1s -headI -!cats1 !count_cat /= eq_refl !addn0.
          exact : leq_addr.
  Qed.

  Theorem zclear_sound (t:T) (s:seq T) n :
    let x := iter n (Turing1step zclear) (Qinit, t, s) in
    x.1.1 = Qacc -> all (fun t => t == zero) (x.1.2 :: x.2).
  Proof.
    have : zclear_valid (Qinit, t, s) =>//=.
    have : zclear_valid (iter n (Turing1step zclear) (Qinit, t, s)).
    elim : n =>[|n IHn]//=. exact : zclear_valid_1step.
    rewrite /zclear_valid.
    case : (iter n (Turing1step zclear) (Qinit, t, s)).1.1 =>//.
      by rewrite all_rcons.
  Qed.
End zclear.