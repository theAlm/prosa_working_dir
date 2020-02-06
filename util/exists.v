Require Import rt.util.tactics.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype.

(* Lemmas about the finite existential for Ordinals: [exists x, P x]. *)
Section OrdExists.

  Lemma exists_ord0:
    forall (T: eqType) P,
      [exists x in 'I_0, P x] = false.
  Proof.
    intros T P.
    apply negbTE; rewrite negb_exists; apply/forall_inP.
    intros x; destruct x as [x LT].
    by exfalso; rewrite ltn0 in LT.
  Qed.

  Lemma exists_recr:
    forall (T: eqType) n P,
      [exists x in 'I_n.+1, P x] =
      [exists x in 'I_n, P (widen_ord (leqnSn n) x)] || P (ord_max).
  Proof.
    intros t n P.
    apply/idP/idP.
    {
      move => /exists_inP EX; destruct EX as [x IN Px].
      destruct x as [x LT].
      remember LT as LT'; clear HeqLT'. 
      rewrite ltnS leq_eqVlt in LT; move: LT => /orP [/eqP EQ | LT].
      {
        apply/orP; right.
        unfold ord_max; subst x.
        apply eq_trans with (y := P (Ordinal LT')); last by done.
        by f_equal; apply ord_inj.
      }
      {
        apply/orP; left.
        apply/exists_inP; exists (Ordinal LT); first by done.
        apply eq_trans with (y := P (Ordinal LT')); last by done.
        by f_equal; apply ord_inj.
      }
    }
    {
      intro OR; apply/exists_inP.
      move: OR => /orP [/exists_inP EX | MAX].
      {
        by destruct EX as [x IN Px]; exists (widen_ord (leqnSn n) x).
      }
      by exists ord_max.
    }
  Qed.

End OrdExists.

