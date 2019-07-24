(** * Defines effective abstractions *)
Require Import Compression.srp.
Require Import Coq.Arith.Peano_dec.

Section Abstraction.
  Context (concrete : SRP)
          (abstract : SRP).

  Class Abstraction :=
  { f : (Vertex) -> (Vertex);
    h : (option (@A concrete)) -> (option (@A abstract));
    f_onto: forall uhat, (@V abstract) uhat -> exists u, (@V concrete u) /\ f u = uhat
  }.
End Abstraction.

Section EffectiveAbstraction.

  Context {concrete : SRP}
          {abstract : SRP}
          {wfC : Wellformed concrete}
          {wfA : Wellformed abstract}
          {abs : Abstraction concrete abstract}.

  Notation dC := (@d concrete).
  Notation dA := (@d abstract).
  Notation adA := (@ad abstract).
  Notation routeType := (option (@A concrete)).
  Notation "A < B" := ((@prec concrete) A B).
  Notation "A <^ B" := ((@prec abstract) A B) (at level 40).
  Notation "A ==^ B" := (@rankEq abstract A B) (at level 40).
  Notation transA := (@trans abstract).
  Notation transC := (@trans concrete).
  Notation f := (@f concrete abstract abs).
  Notation h := (@h concrete abstract abs).

  Class Effective :=
  { dest_equiv: f dC = dA /\ (forall d', dC <> d' -> f(d') <> dA);
    drop_equiv: h(None) = None;
    orig_equiv: h((@ad concrete)) = adA;
    rank_equiv: forall (a b: routeType), a < b <-> h(a) <^ h(b);
    trans_equiv: forall (u v: Vertex) (a : routeType),
                   h(transC (u,v) a) = transA (f(u), f(v)) (h a);
    forAll_Exists: forall (uhat vhat: Vertex),
                   (@E abstract) uhat vhat <-> (forall v, f(v) = vhat -> exists u, f(u) = uhat /\
                                                                      (@E concrete) u v)
  }.

  Context {solC: @Solution concrete}
          {solA: @Solution abstract}.

  Notation labC := (@lab _ solC).
  Notation labA := (@lab _ solA).
  Notation fwdC := (fwd _ labC).
  Notation fwdA := (fwd _ labA).

  (** To be used for protocols that support ECMP *)
  Definition labEquiv := forall u, h (labC u) ==^ labA (f u).
  (** To be used otherwise, requires a total ordering of routes. *)
  Definition labEqual := forall u, h (labC u) = labA (f u).
  Definition fwdEquiv :=
  forall (uhat vhat : Vertex),
               @V abstract uhat /\ @V abstract vhat ->
               (fwdA (uhat, vhat) <->
                 (forall u, f u = uhat -> exists v, f v = vhat /\ fwdC (u,v))).
End EffectiveAbstraction.

Section LabelEquivalence.
  Context {concrete : SRP}
          {abstract : SRP}
          {wfC : Wellformed concrete}
          {wfA : Wellformed abstract}
          {abs : Abstraction concrete abstract}
          {eff : Effective}
          {solC: @Solution concrete}
          {solA: @Solution abstract}.

  Notation dC := (@d concrete).
  Notation dA := (@d abstract).
  Notation adA := (@ad abstract).
  Notation routeType := (option (@A concrete)).
  Notation routeTypeA := (option (@A abstract)).
  Notation "A < B" := ((@prec concrete) A B).
  Notation "A <^ B" := ((@prec abstract) A B) (at level 40).
  Notation "A ==^ B" := (@rankEq abstract A B) (at level 40).
  Notation "A == B" := (@rankEq concrete A B) (at level 40).
  Notation transA := (@trans abstract).
  Notation transC := (@trans concrete).
  Notation f := (@f concrete abstract abs).
  Notation h := (@h concrete abstract abs).
  Notation labC := (@lab _ solC).
  Notation labA := (@lab _ solA).
  Notation fwdC := (fwd labC).
  Notation fwdA := (fwd labA).
  Notation labSpecC := (@labSpec concrete _).
  Notation labSpecA := (@labSpec abstract _).

  Definition choiceEquiv :=
  forall (u: Vertex) (e: edge) (routeA: routeTypeA),
               (exists routeC, (h routeC) ==^ routeA /\ choices _ labC u e routeC)
               <->
               choices _ labA (f u) (f (fst e), f (snd e)) routeA.

  Require Import Coq.Classes.RelationClasses.
  Require Import Classes.Morphisms.
  (* Add == as an equivalence relation*)
  Add Parametric Relation Srp (Wf : Wellformed Srp) : (option (@A Srp)) (@rankEq Srp)
      reflexivity proved by (@Equivalence_Reflexive _ _ (@rankEq_eq Srp Wf))
      symmetry proved by (@Equivalence_Symmetric _ _ (@rankEq_eq Srp Wf))
      transitivity proved by (@Equivalence_Transitive _ _ (@rankEq_eq Srp Wf))
        as eq_rank_rel.

  (* Allow generic rewriting of == over <*)
  Instance prec_Proper Srp (Wf : Wellformed Srp) : Proper (eq ==> (fun x y => @rankEq Srp x y) ==> iff) (@prec Srp).
  Proof.
    intros x1 x2 Hxeq y1 y2 Hpreceq.
    subst.
    split; intros.
    - destruct (prec_eq_total x2 y2) as [Hlt | [Hgt | Heq]].
      + eauto.
      + exfalso.
        pose proof (prec_trans y2 x2 y1 Hgt H).
        apply prec_not_eq in Hpreceq.
        destruct Hpreceq;
          now eauto.
      + rewrite <- Hpreceq in Heq.
        apply prec_not_eq in Heq.
        destruct Heq.
        now exfalso.
    - destruct (prec_eq_total x2 y1) as [Hlt | [Hgt | Heq]].
      + eauto.
      + exfalso.
        pose proof (prec_trans y1 x2 y2 Hgt H).
        apply prec_not_eq in Hpreceq.
        destruct Hpreceq;
          now eauto.
      + rewrite Hpreceq in Heq.
        apply prec_not_eq in Heq.
        destruct Heq.
        now exfalso.
  Defined.

  Lemma rank_equiv_eq :
    forall a b
      (Hrank_eq: forall a b,  a < b <-> (h a) <^ (h b)),
                 a == b <-> h a ==^ h b.
  Proof.
    intros.
    split; intros Heq.
    - destruct (prec_eq_total (h a) (h b)) as [Hlt | [Hgt | Heq']];
      auto.
      + pose proof (proj2 (Hrank_eq a b) Hlt).
        eapply prec_not_eq in Heq.
        exfalso; now auto.
      + pose proof (proj2 (Hrank_eq b a) Hgt).
        eapply prec_not_eq in Heq.
        exfalso; now auto.
    - destruct (prec_eq_total a b) as [Hlt | [Hgt | Heq']];
      auto.
      + pose proof (proj1 (Hrank_eq a b) Hlt).
        eapply prec_not_eq in Heq.
        exfalso; now auto.
      + pose proof (proj1 (Hrank_eq b a) Hgt).
        eapply prec_not_eq in Heq.
        exfalso; now auto.
  Qed.

  (** Choice equivalence implies label equivalence *)
  Theorem choiceEquiv_implies_labEquiv :
    choiceEquiv -> labEquiv.
  Proof.
    intros HchoiceEq.
    unfold labEquiv.
    intros u.
    pose proof (labSpecC u) as HlabSpec.
    pose proof (labSpecA (f u)) as HlabSpecA.
    inversion HlabSpec; subst.
    - (* case u is the destination *)
      destruct (dest_equiv) as [Heq Hneq].
      rewrite Heq.
      rewrite HisDest.
      rewrite Heq in HlabSpecA.
      inversion HlabSpecA as [HdA| |]; subst; [|exfalso; now eauto | exfalso; now eauto].
      (* abstract solution must be initial abstract route *)
      rewrite HdA.
      erewrite orig_equiv.
      reflexivity.
    - (* case u is a node without choices *)
      inversion HlabSpecA as [HdA Hfd | ? HdA HlabA  HnochoiceA | ? vhat]; subst.
      + exfalso.
        apply Hd.
        destruct (dest_equiv) as [Hfd' Hfneq].
        rewrite Hfd in Hfd'.
        specialize (Hfneq u ltac:(eauto)).
        exfalso; now congruence.
      + rewrite Hempty, HlabA.
        erewrite drop_equiv.
        reflexivity.
      + exfalso.
        assert (HedgeA: E vhat (f u)) by (inversion Hchoice; eauto).
        destruct (proj1 (forAll_Exists vhat (f u)) HedgeA u ltac:(auto)) as [v [Hfv HE]].
        (* NOTE: interesting case here, because of the flipped order on how
        choices work we need to flip the order on forall-exists too?
        Intuitively it makes sense. We wish to guarantee that if an attribute
        is sent over (uhat, vhat) then every v |-> vhat gets the message from
        some u |-> uhat. *)
        specialize (HchoiceEq u (v, u) (labA (f u))).
        simpl in HchoiceEq.
        subst vhat.
        destruct (proj2 HchoiceEq Hchoice) as [routeC [Hh Hchoices]].
        eapply Hnochoice;
          now eauto.
    - (* case u is a node with a choice *)
      unfold choiceEquiv in *.
      (* By choice equivalence the abstract network has a similar choice *)
      pose proof (proj1 (HchoiceEq u (v,u) (h (labC u)))
                        ltac:(exists (labC u); split; (eauto || reflexivity))) as HchoiceA.
      simpl in HchoiceA.
      (* show it's minimal *)
      assert(HminA: forall (what : Vertex) (bhat : option A),
                            choices abstract labA (f u) (what, f u) bhat ->
                            h (labC u) <^ bhat \/ h (labC u) ==^ bhat).
      { intros what bhat HchoicewHat.
        (* Suppose there is some better choice for the abstract network *)
        (* Then by choice-eq the concrete network has this choice too *)

        (* Since there is a choice of what, there is an abstract edge *)
        assert (Hwhat_u: E what (f u)) by (inversion HchoicewHat; eauto).
        (* By forall-exists there is a concrete node that maps to w and
           (u, w) \in E*)
        destruct (proj1 (forAll_Exists what (f u)) Hwhat_u u ltac:(auto)) as [w [Hfw HEwu]].
        (* By choice-equivalence the concrete network must have a similar ranked
        choice over this edge. *)
        specialize (proj2 (HchoiceEq u (w, u) bhat)).
        simpl.
        intros HchoiceEqw.
        rewrite Hfw in HchoiceEqw.
        destruct (HchoiceEqw HchoicewHat) as [b [Hb Hchoicew]].
        clear HchoiceEqw.
        (* by rank equivalence *)
        rewrite <- Hb.
        specialize (Hmin w b Hchoicew).
        destruct Hmin as [HlabC_best | Heq].
        - pose proof (rank_equiv (labC u) b) as Hrankeq.
          pose proof (proj1 Hrankeq HlabC_best);
            now auto.
        - eapply rank_equiv_eq in Heq; eauto.
          now eapply eff.
      }
      inversion HlabSpecA; subst.
      + exfalso.
        destruct (dest_equiv) as [Heq Hneq].
        rewrite H0 in Heq.
        specialize (Hneq u ltac:(eauto)).
        eauto.
      + exfalso.
        eapply Hnochoice;
          now eauto.
      + (* The abstract node f u has some minimal choice over some edge v0, to show:
           that it coincides with the choice of u *)
        specialize (Hmin0 _ _ HchoiceA).
        specialize (HminA _ _ Hchoice0).
        destruct HminA as [Hlt | ?]; [| now eauto].
        destruct Hmin0 as [Hgt | ?]; [| now eauto].
        eapply prec_asym in Hlt.
        exfalso;
          now auto.
  Qed.

  Theorem labEquiv_implies_fwdEquiv :
    choiceEquiv -> fwdEquiv.
  Proof.
    intros HchoiceEq.
    unfold choiceEquiv, fwdEquiv in *.
    intros uhat vhat [Hvu Hvv].
    split.
    - (* If abstract forwards towards vhat then concrete forwards towards v, f v = vhat*)
      intros HfwdA u Hfu.
      inversion HfwdA.
      inversion He; subst u0 v.
      clear He.
      (* by the fact that (uhat, vhat) \in E and forall-exists *)
      assert (Hfv: exists v, f v = vhat).
      { inversion HbestChoice; subst.
        eapply forAll_Exists in Hedge;
          eauto.
        destruct Hedge as [? [? ?]];
          now eauto.
      }
      destruct Hfv as [v Hfv].
      exists v.
      split; [assumption|].
      (* By choice equivalence, concrete network has a similar choice *)
      pose proof (proj2 (HchoiceEq u (v,u) a)) as HchoiceEquiv.
      simpl in HchoiceEquiv.
      rewrite Hfu, Hfv in HchoiceEquiv.
      destruct (HchoiceEquiv HbestChoice) as [routeC [HrouteC HchoiceC]].
      rewrite Hbest in HrouteC.
      (* by label equivalence we get that lab(uhat) == h(lab(u))*)
      pose proof (choiceEquiv_implies_labEquiv HchoiceEq) as HlabEquiv.
      specialize (HlabEquiv u).
      rewrite Hfu in HlabEquiv.
      rewrite <- HlabEquiv in HrouteC.
      (* and hence routeC == labC u *)
      eapply rank_equiv_eq in HrouteC;
        eauto using rank_equiv.
      econstructor;
        now eauto.
    - (*If concrete forwards towards v then the abstract forwards towards f v *)
      intros HfwdC.
      (* NOTE: I think here we need the assumption that f is onto. Every uhat is
        mapped to some u. *)
      destruct (f_onto _ _ uhat Hvu) as [u [Hu Hfu]].
      destruct (HfwdC u Hfu) as [v [Hv Hfwd]].
      inversion Hfwd; subst.
      inversion He; subst u0 v0.
      (* By choice equivalence, the abstract network has a similar choice *)
      pose proof (proj1 (HchoiceEq u (v,u) (h (labC u)))) as HchoiceEquiv.
      assert (Hpre: (exists routeC : routeType,
                    h routeC ==^ h (labC u) /\ choices concrete labC u (v, u) routeC)).
      { exists a.
        split; eauto.
        eapply rank_equiv_eq;
          now eauto using rank_equiv.
      }
      specialize (HchoiceEquiv Hpre).
      clear Hpre.
      simpl in HchoiceEquiv.
      (* And by label equivalence, h (labC u) == labA (f u)) *)
      pose proof (choiceEquiv_implies_labEquiv HchoiceEq) as HlabEquiv.
      specialize (HlabEquiv u).
      econstructor;
        now eauto.
  Qed.

End LabelEquivalence.
