Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
From SetsClass Require Import SetsClass.
Import SetsNotation.
Local Open Scope sets_scope.

(*********************************************************)
(**                                                      *)
(** Graph                                                *)
(**                                                      *)
(*********************************************************)

Module Graph.

Record PreGraph (Vertex Edge: Type) := {
  vvalid : Vertex -> Prop;
  evalid : Edge -> Prop;
  src : Edge -> Vertex;
  dst : Edge -> Vertex;
  weight: Edge -> Z;
}.

Notation "pg '.(vvalid)'" := (vvalid _ _ pg) (at level 1).
Notation "pg '.(evalid)'" := (evalid _ _ pg) (at level 1).
Notation "pg '.(src)'" := (src _ _ pg) (at level 1).
Notation "pg '.(dst)'" := (dst _ _ pg) (at level 1).

Record step_aux {V E: Type} (pg: PreGraph V E) (e: E) (x y: V): Prop :=
{
  step_evalid: pg.(evalid) e;
  step_src_valid: pg.(vvalid) x;
  step_dst_valid: pg.(vvalid) y;
  step_src: pg.(src) e = x;
  step_dst: pg.(dst) e = y;
}.

Definition step {V E: Type} (pg: PreGraph V E) (x y: V): Prop :=
  exists e, step_aux pg e x y \/ step_aux pg e y x.

Definition connected {V E: Type} (pg: PreGraph V E): V -> V -> Prop :=
  clos_refl_trans (step pg).

Record subgraph {V E: Type} (pg1 pg2: PreGraph V E): Prop :=
{
  subgraph_vvalid: pg1.(vvalid) == pg2.(vvalid);
  subgraph_evalid: pg1.(evalid) ⊆ pg2.(evalid);
  subgraph_src: forall e, e ∈ pg1.(evalid) -> pg1.(src) e = pg2.(src) e;
  subgraph_dst: forall e, e ∈ pg1.(evalid) -> pg1.(dst) e = pg2.(dst) e;
}.

End Graph.

Notation "'PreGraph'" := (Graph.PreGraph) (at level 0).
Notation "pg '.(vvalid)'" := (Graph.vvalid _ _ pg) (at level 1).
Notation "pg '.(evalid)'" := (Graph.evalid _ _ pg) (at level 1).
Notation "pg '.(src)'" := (Graph.src _ _ pg) (at level 1).
Notation "pg '.(dst)'" := (Graph.dst _ _ pg) (at level 1).



