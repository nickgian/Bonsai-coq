Require Import Coq.Sets.Ensembles.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Definition Vertex : Type := nat.
Notation edge := (prod Vertex Vertex).

Class SRP :=
  { V: Ensemble Vertex;
    E: relation Vertex;
    d: Vertex;
    A: Type;
    ad: option A;
    prec: relation (option A);
    rankEq: relation (option A);
    trans: edge -> option A -> option A
  }.

Class Wellformed (srp: SRP) :=
  { prec_bot: forall (a : A), prec (Some a) None;
    prec_trans: transitive _ prec;
    prec_asym: forall a b, prec a b -> ~ prec b a;
    prec_irrefl: forall a, ~ prec a a;
    prec_eq_total: forall a b, prec a b \/ prec b a \/ rankEq a b;
    prec_not_eq: forall a b, (rankEq a b <-> ~ prec a b /\ ~ prec b a);
    rankEq_eq:  Equivalence rankEq;
    self_loop_free: forall u, ~ E u u;
    non_spontaneous: forall (e : Vertex*Vertex), trans e None = None
  }.

Section Solution.
  Context (srp: SRP)
          {wf: Wellformed srp}.

  Notation routeType := (option A).
  Notation "A < B" := (prec A B).
  Notation "A == B" := (rankEq A B) (at level 40).
  Notation "A <= B" := ((A < B) \/ A == B).

  Inductive choices (lab: Vertex -> routeType) (u : Vertex) : edge -> routeType -> Prop :=
  | NotFailed :
      forall (v : Vertex) (a : A)
        (Hedge: E v u)
        (Htrans: trans (v,u) (lab v) = Some a),
    choices lab u (v,u) (Some a).

  Inductive labSpec' (lab: Vertex -> routeType): Vertex -> Prop :=
  | LabDest : forall
      (HisDest: lab d = ad),
      labSpec' lab d
  | LabEmpty : forall u
                 (Hd : u <> d)
                 (Hempty: lab u = None)
                 (Hnochoice: forall v a, ~ (choices lab u (v,u) a)),
    labSpec' lab u
  | LabMin : forall u v
        (Hd: u <> d)
        (Hchoice: choices lab u (v,u) (lab u))
        (Hmin: forall w b, choices lab u (w,u) b -> (lab u) <= b),
    labSpec' lab u.

  Inductive fwd (lab: Vertex -> routeType) (e: edge): Prop :=
  | Fwd : forall a u v
    (He: e = (u,v))
    (Hbest: a == lab(u))
    (HbestChoice: choices lab u (v,u) a),
    fwd lab e.

  Class Solution :=
    { lab: Vertex -> routeType;
      labSpec: forall u, labSpec' lab u
    }.

End Solution.
