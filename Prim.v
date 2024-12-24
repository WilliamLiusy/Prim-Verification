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
  vevalid: forall e, evalid e -> vvalid (src e) /\ vvalid (dst e);
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

Notation "'PreGraph'" := (Graph.PreGraph) (at level 0).
Notation "pg '.(vvalid)'" := (Graph.vvalid _ _ pg) (at level 1).
Notation "pg '.(evalid)'" := (Graph.evalid _ _ pg) (at level 1).
Notation "pg '.(src)'" := (Graph.src _ _ pg) (at level 1).
Notation "pg '.(dst)'" := (Graph.dst _ _ pg) (at level 1).

End Graph.


Module Tree.
Import Graph.

Inductive adjacent {A: Type} : A -> A -> list A -> Prop :=
  | adj_head : forall x y l, adjacent x y (x :: y :: l)
  | adj_tail : forall x y z l, adjacent x y l -> adjacent x y (z :: l).

Record Cycle {V E: Type} (pg: PreGraph V E) := {
  cycle_vertex: list V;
  cycle_edge: list E;
  cycle_evalid: forall e, In e cycle_edge -> pg.(evalid) e;
  
  cycle_v_continuous: forall e1 e2, adjacent e1 e2 cycle_edge -> pg.(src) e1 = pg.(dst) e2;
  cycle_no_dup: NoDup cycle_edge;
  cycle_connected: forall x y, In x cycle_edge -> In y cycle_edge -> connected pg (pg.(src) x) (pg.(dst) y);
}.


End Tree.


