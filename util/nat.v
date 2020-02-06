Require Import rt.util.tactics rt.util.divround rt.util.ssromega.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div.

(* Additional lemmas about natural numbers. *)
Section NatLemmas.
  
  Lemma addnb (b1 b2 : bool) : (b1 + b2) != 0 = b1 || b2.
  Proof.
    by destruct b1,b2;
    rewrite ?addn0 ?add0n ?addn1 ?orTb ?orbT ?orbF ?orFb.
  Qed.

  Lemma subh1 :
    forall m n p,
      m >= n ->
      m - n + p = m + p - n.
  Proof. by ins; ssromega. Qed.

  Lemma subh2 :
    forall m1 m2 n1 n2,
      m1 >= m2 ->
      n1 >= n2 ->
      (m1 + n1) - (m2 + n2) = m1 - m2 + (n1 - n2).
  Proof. by ins; ssromega. Qed.

  Lemma subh3 :
    forall m n p,
      m + p <= n ->
      n >= p ->
      m <= n - p.
  Proof.
    ins. rewrite <- leq_add2r with (p := p).
    by rewrite subh1 // -addnBA // subnn addn0.
  Qed.

  Lemma subh4:
    forall m n p,
      m <= n ->
      p <= n ->
      (m == n - p) = (p == n - m).
  Proof.
    intros; apply/eqP.
    destruct (p == n - m) eqn:EQ.
      by move: EQ => /eqP EQ; rewrite EQ subKn.
      by apply negbT in EQ; unfold not; intro BUG;
        rewrite BUG subKn ?eq_refl in EQ.
  Qed.

  Lemma addmovr:
    forall m n p,
      m >= n ->
      (m - n = p <-> m = p + n).
  Proof.
    by split; ins; ssromega.
  Qed.

  Lemma addmovl:
    forall m n p,
      m >= n ->
      (p = m - n <-> p + n = m).
  Proof.
    by split; ins; ssromega.
  Qed.

  Lemma ltn_div_trunc :
    forall m n d,
      d > 0 ->
      m %/ d < n %/ d ->
      m < n.
  Proof.
    intros m n d GT0 DIV; rewrite ltn_divLR in DIV; last by ins.
    by apply leq_trans with (n := n %/ d * d);
      [by ins| by apply leq_trunc_div].
  Qed.
  
  Lemma subndiv_eq_mod:
    forall n d, n - n %/ d * d = n %% d.
  Proof.
    by ins; rewrite {1}(divn_eq n d) addnC -addnBA // subnn addn0.
  Qed.

  Lemma ltSnm : forall n m, n.+1 < m -> n < m.
  Proof.
    by ins; apply ltn_trans with (n := n.+1); [by apply ltnSn |by ins].
  Qed.

  Lemma divSn_cases :
    forall n d,
      d > 1 ->
      (n %/ d = n.+1 %/d /\ n %% d + 1 = n.+1 %% d) \/
      (n %/ d + 1 = n.+1 %/ d).
  Proof.
    ins; set x := n %/ d; set y := n %% d.
    assert (GT0: d > 0); first by apply ltn_trans with (n := 1).
    destruct (ltngtP y (d - 1)) as [LTN | BUG | GE]; [left | | right];
      first 1 last.
    {
      exploit (@ltn_pmod n d); [by apply GT0 | intro LTd; fold y in LTd].
      rewrite -(ltn_add2r 1) [y+1]addn1 ltnS in BUG.
      rewrite subh1 in BUG; last by apply GT0.
      rewrite -addnBA // subnn addn0 in BUG.
      by apply (leq_ltn_trans BUG) in LTd; rewrite ltnn in LTd.
    }

    {
      (* Case 1: y = d - 1*)
      move: GE => /eqP GE; rewrite -(eqn_add2r 1) in GE.
      rewrite subh1 in GE; last by apply GT0.
      rewrite -addnBA // subnn addn0 in GE.
      move: GE => /eqP GE.
      apply f_equal with (f := fun x => x %/ d) in GE.
      rewrite divnn GT0 /= in GE.
      unfold x; rewrite -GE.
      rewrite -divnMDl; last by apply GT0.
      f_equal; rewrite addnA.
      by rewrite -divn_eq addn1.
    }
    {
      assert (EQDIV: n %/ d = n.+1 %/ d).
      {
        apply/eqP; rewrite eqn_leq; apply/andP; split;
          first by apply leq_div2r, leqnSn.
        rewrite leq_divRL; last by apply GT0.
        rewrite -ltnS {2}(divn_eq n.+1 d).
        rewrite -{1}[_ %/ d * d]addn0 ltn_add2l.
        unfold y in *.
        rewrite ltnNge; apply/negP; unfold not; intro BUG.
        rewrite leqn0 in BUG; move: BUG => /eqP BUG.
        rewrite -(modnn d) -addn1 in BUG.
        destruct d; first by rewrite sub0n in LTN.
        move: BUG; move/eqP; rewrite -[d.+1]addn1 eqn_modDr [d+1]addn1; move => /eqP BUG.
        rewrite BUG -[d.+1]addn1 -addnBA // subnn addn0 in LTN.
        by rewrite modn_small in LTN;
          [by rewrite ltnn in LTN | by rewrite addn1 ltnSn].
      }
      (* Case 2: y < d - 1 *)
      split; first by rewrite -EQDIV.
      {
        unfold x, y in *.
        rewrite -2!subndiv_eq_mod.
        rewrite subh1 ?addn1; last by apply leq_trunc_div.
        rewrite EQDIV; apply/eqP.
        rewrite -(eqn_add2r (n%/d*d)).
        by rewrite subh1; last by apply leq_trunc_div.
      }
    }
  Qed.

  Lemma ceil_neq0 :
    forall x y,
      x > 0 ->
      y > 0 ->
      div_ceil x y > 0.
  Proof.
    unfold div_ceil; intros x y GEx GEy.
    destruct (y %| x) eqn:DIV; last by done.
    by rewrite divn_gt0; first by apply dvdn_leq.
  Qed.

  Lemma leq_divceil2r :
    forall d m n,
      d > 0 ->
      m <= n ->
      div_ceil m d <= div_ceil n d.
  Proof.
    unfold div_ceil; intros d m n GT0 LE.
    destruct (d %| m) eqn:DIVm, (d %| n) eqn:DIVn;
      [by apply leq_div2r | | | by apply leq_div2r].
    by apply leq_trans with (n := n %/ d); first by apply leq_div2r.
    {
      rewrite leq_eqVlt in LE; move: LE => /orP [/eqP EQ | LT];
        first by subst; rewrite DIVn in DIVm.
      rewrite ltn_divLR //.
      apply leq_trans with (n := n); first by done.
      by apply eq_leq; symmetry; apply/eqP; rewrite -dvdn_eq.    
    }
  Qed.
  
  Lemma min_lt_same :
    forall x y z,
      minn x z < minn y z -> x < y.
  Proof.
    unfold minn; ins; desf.
    {
      apply negbT in Heq0; rewrite -ltnNge in Heq0.
      by apply leq_trans with (n := z).
    }
    {
      apply negbT in Heq; rewrite -ltnNge in Heq.
      by apply (ltn_trans H) in Heq0; rewrite ltnn in Heq0.
    }
    by rewrite ltnn in H.
  Qed.
  
End NatLemmas.