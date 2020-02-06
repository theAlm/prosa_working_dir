Require Import rt.util.tactics.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Lemmas about lists without duplicates. *)
Section UniqList.

  Lemma idx_lt_rcons :
    forall {T: eqType} (l: seq T) i x0,
      uniq l ->
      i < size l ->
      [seq x <- l | index x l < i.+1] =
        rcons [seq x <- l | index x l < i] (nth x0 l i).
  Proof.
    intros T l i x0 UNIQ LT.
    generalize dependent i.
    induction l as [| l' x] using last_ind; first by ins; rewrite ltn0 in LT.
    {
      intros i LT.
      rewrite size_rcons in LT.
      rewrite filter_rcons.
      rewrite -cats1 index_cat; desf; simpl in *;
        try (by rewrite rcons_uniq in UNIQ; move: UNIQ => /andP [NOTIN _]; rewrite Heq0 in NOTIN).
      {
        rewrite eq_refl addn0 in Heq.
        rewrite filter_cat /=.
        assert (EQ: i = size l'); first by apply/eqP; rewrite eqn_leq; apply/andP; split.
        rewrite index_cat Heq0 /= eq_refl addn0 EQ ltnn cats0.
        rewrite nth_cat ltnn subnn /=.
        f_equal; apply eq_in_filter; red; intros y INy.
        by rewrite index_cat INy ltnS index_size index_mem INy.
      }
      {
        rewrite rcons_uniq in UNIQ; move: UNIQ => /andP [NOTIN UNIQ].
        rewrite eq_refl addn0 in Heq.
        apply negbT in Heq; rewrite -leqNgt in Heq.
        rewrite nth_cat Heq.
        rewrite filter_cat /= index_cat Heq0 /= eq_refl addn0.
        rewrite ltnS in LT; rewrite ltnNge LT /= cats0 cats1.
        apply eq_trans with (y := [seq x1 <- l' | index x1 l' < i.+1]);
          first by apply eq_in_filter; red; intros y INy; rewrite -cats1 index_cat INy.
        rewrite IHl //; f_equal; apply eq_in_filter; intros y INy.
        by rewrite -cats1 index_cat INy.
      }
    }
  Qed.
  
  Lemma filter_idx_lt_take :
    forall {T: eqType} (l: seq T) i,
      uniq l ->
      i < size l ->
      [seq x <- l | index x l < i] = take i l.
  Proof.
    intros T l i UNIQ LT.
    generalize dependent l.
    induction i.
    {
      intros l UNIQ LT; destruct l as [| x0 l']; first by done.
      by apply eq_trans with (filter pred0 (x0 :: l'));
        [by apply eq_filter | by rewrite filter_pred0].
    }
    {
      intros l UNIQ LT.
      destruct (lastP l) as [| l' x]; first by rewrite ltn0 in LT.
      rewrite size_rcons ltnS in LT.
      rewrite (take_nth x); last by rewrite size_rcons; apply (leq_trans LT).
      rewrite -> idx_lt_rcons with (x0 := x); try (by done);
        last by rewrite size_rcons; apply (leq_trans LT).
      by f_equal; apply IHi; last by rewrite size_rcons; apply (leq_trans LT).
    }  
  Qed.

  Lemma filter_idx_le_takeS :
    forall {T: eqType} (l: seq T) i,
      uniq l ->
      i < size l ->
      [seq x <- l | index x l <= i] = take i.+1 l.
  Proof.
    intros T l i UNIQ LT.
    induction l as [| x0 l]; first by done.
    simpl; rewrite eq_refl leq0n; f_equal.
    apply eq_trans with (y := [seq x <- l | index x l < i]).
    {
      apply eq_in_filter; red; intros x IN.
      desf; subst; last by done.
      by simpl in *; rewrite IN andFb in UNIQ.
    }
    simpl in *; desf.
    rewrite /= ltnS in LT.
    rewrite leq_eqVlt in LT; desf.
    {
      rewrite take_size.
      apply eq_trans with (y := filter predT l); last by rewrite filter_predT.
      by apply eq_in_filter; red; ins; rewrite index_mem.
    }
    by apply filter_idx_lt_take.
  Qed.
  
End UniqList.

(* Additional lemmas about list zip. *)
Section Zip.
  
  Lemma zipP {T: eqType} (x0: T) (P: _ -> _ -> bool) (X Y: seq T):
    size X = size Y ->
    reflect (forall i, i < size (zip X Y) -> P (nth x0 X i) (nth x0 Y i))
            (all (fun p => P (fst p) (snd p)) (zip X Y)).
  Proof.
    intro SIZE; apply/introP.
    {
      move => /allP ALL i LT.
      apply (ALL (nth x0 X i,nth x0 Y i)).
      by rewrite -nth_zip; [by apply mem_nth | by done].
    }
    {
      rewrite -has_predC; unfold predC.
      move => /hasP HAS; simpl in *; destruct HAS as [x IN NOT].
      unfold not; intro BUG.
      exploit (BUG (index x (zip X Y))).
        by rewrite index_mem.
      have NTH := @nth_zip _ _ x0 x0 X Y (index x (zip X Y)) SIZE.
      destruct x as [x1 x2].
      rewrite {1}nth_index in NTH; last by done.
      clear BUG; intros BUG.
      inversion NTH as [[NTH0 NTH1]]; rewrite -NTH0 in NTH1.
      by rewrite -NTH0 -NTH1 in BUG; rewrite BUG in NOT.
    }
  Qed.

  Lemma mem_zip_exists :
    forall (T T': eqType) (x1: T) (x2: T') l1 l2 elem elem',
      size l1 = size l2 ->
      (x1, x2) \in zip l1 l2 ->
      exists idx,
        idx < size l1 /\
        idx < size l2 /\
        x1 = nth elem l1 idx /\
        x2 = nth elem' l2 idx.
  Proof.
    intros T T' x1 x2 l1 l2 elem elem' SIZE IN.
    assert (LT: index (x1, x2) (zip l1 l2) < size l1).
    {
      apply leq_trans with (n := size (zip l1 l2)); first by rewrite index_mem.
      by rewrite size_zip; apply geq_minl.
    }
    have NTH := @nth_index _ (elem,elem') (x1, x2) (zip l1 l2) IN.
    rewrite nth_zip in NTH; last by done.
    inversion NTH; rewrite H1 H0; rewrite H0 in H1.
    by exists (index (x1, x2) (zip l1 l2)); repeat split; try (by done); rewrite -?SIZE.
  Qed.

End Zip.

(* Restate nth_error function from Coq library. *)
Fixpoint nth_or_none {T: Type} (l: seq T) (n:nat) {struct n} : option T :=
  match n, l with
  | 0, x :: _ => Some x
  | n.+1, _ :: l => nth_or_none l n
  | _, _ => None
end.

(* Lemmas about nth_or_none. *)
Section NthOrNone.

  Context {T: eqType}.
  
  Lemma nth_or_none_mem :
    forall (l: seq T) n x, nth_or_none l n = Some x -> x \in l.
  Proof.
    induction l; first by unfold nth_or_none; ins; destruct n; ins.
    {
      ins; destruct n.
      {
        inversion H; subst.
        by rewrite in_cons eq_refl orTb.
      }
      simpl in H; rewrite in_cons; apply/orP; right.
      by apply IHl with (n := n).
    }
  Qed. 
    
  Lemma nth_or_none_mem_exists :
    forall (l: seq T) x, x \in l -> exists n, nth_or_none l n = Some x.
  Proof.
    induction l; first by intros x IN; rewrite in_nil in IN.
    {
      intros x IN; rewrite in_cons in IN.
      move: IN => /orP [/eqP EQ | IN]; first by subst; exists 0.
      specialize (IHl x IN); des.
      by exists n.+1.
    }
  Qed.
  
  Lemma nth_or_none_size_none :
    forall (l: seq T) n,
      nth_or_none l n = None <-> n >= size l.
  Proof.
    induction l; first by split; destruct n. 
    by destruct n; simpl; [by split; last by rewrite ltn0 | by rewrite ltnS].
  Qed.

  Lemma nth_or_none_size_some :
    forall (l: seq T) n x,
      nth_or_none l n = Some x -> n < size l.
  Proof.
    induction l; first by destruct n. 
    by intros n x; destruct n; simpl; last by rewrite ltnS; apply IHl.
  Qed.
  
  Lemma nth_or_none_uniq :
    forall (l: seq T) i j x,
      uniq l ->
      nth_or_none l i = Some x ->
      nth_or_none l j = Some x ->
      i = j.
  Proof.
    intros l i j x UNIQ SOMEi SOMEj.
    {
      generalize dependent j.
      generalize dependent i.
      induction l;
        first by ins; destruct i, j; simpl in *; inversion SOMEi.
      intros i SOMEi j SOMEj.
      simpl in UNIQ; move: UNIQ => /andP [NOTIN UNIQ].
      feed IHl; first by done.
      destruct i, j; simpl in *; first by done.
      - by inversion SOMEi; subst; apply nth_or_none_mem in SOMEj; rewrite SOMEj in NOTIN. 
      - by inversion SOMEj; subst; apply nth_or_none_mem in SOMEi; rewrite SOMEi in NOTIN.
      - by f_equal; apply IHl.
    }
  Qed.

Lemma nth_or_none_nth :
    forall (l: seq T) n x x0,
      nth_or_none l n = Some x ->
      nth x0 l n = x.
  Proof.
    induction l; first by destruct n.
    by intros n x x0 SOME; destruct n; simpl in *; [by inversion SOME | by apply IHl].
  Qed.

End NthOrNone.