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
Notation "pg '.(weight)'" := (weight _ _ pg) (at level 1).
Notation "pg '.(vevalid)'" := (vevalid _ _ pg) (at level 1).

Lemma valid {V E: Type} (pg: PreGraph V E) :
  forall e, pg.(evalid) e -> pg.(vvalid) (pg.(src) e) /\ pg.(vvalid) (pg.(dst) e).
Proof.
  intros. apply (pg.(vevalid) e). auto.
Qed.

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


Definition Cycle_ve_correspond_aux {V E: Type} (pg: PreGraph V E) (v: V) (l: list V): Prop := 
  match l with
  | nil => True
  | x :: xs => 
    step pg v x
  end.

Fixpoint Cycle_ve_correspond {V E: Type} (pg: PreGraph V E) (l: list V): Prop := 
  match l with
  | nil => True
  | x :: xs => Cycle_ve_correspond_aux pg x xs /\ Cycle_ve_correspond pg xs
  end.

Fixpoint Nodup {V: Type} (l: list V): Prop :=
  match l with
  | nil => True
  | x :: xs => ~ In x xs /\ Nodup xs
  end.

Print Coq.Lists.List.last.

Definition is_head {V: Type} (l: list V) (v: V): Prop := 
  match l with
  | nil => False
  | x :: xs => (v = x)
  end. 

Fixpoint is_last {V: Type} (l: list V) (v: V): Prop :=
  match l with
  | nil => False
  | x :: nil => (x = v)
  | x :: xs => (is_last xs v)
  end.

Record is_Cycle {V E: Type} (pg: PreGraph V E) (l: list V): Prop := {
  cycle_ve_correspond: Cycle_ve_correspond pg l /\ (forall last head: V, is_head l head -> is_last l last -> step pg last head);
  cycle_nodup: Nodup l;
  cycle_vvalid: forall v, In v l -> pg.(vvalid) v;
}.

Definition no_cycle {V E: Type} (pg: PreGraph V E): Prop := 
  forall l: list V, ~ is_Cycle pg l.

Definition graph_connected {V E: Type} (t: PreGraph V E): Prop := 
  forall x y, t.(vvalid) x -> t.(vvalid) y -> connected t x y.

(** True if t is a tree*)
Definition is_tree {V E: Type} (pg t: PreGraph V E): Prop := 
  subgraph t pg /\ no_cycle t /\ graph_connected t.


 (* 这里缺少一个语法， 新构建record实例时，如何验证他应该满足的性质 *)
(* Definition add_one_edge {V E: Type} (pg: PreGraph V E) (t: PreGraph V E) (e: E): PreGraph V E :=
  Build_PreGraph V E (t.(vvalid) ∪ (Sets.singleton (pg.(src) e)) ∪ (Sets.singleton (pg.(dst) e))) (pg.(evalid) ∪ (Sets.singleton e)) (pg.(src)) (pg.(dst)) (pg.(weight)). *)

(**一个树加一条边 有且仅有 一个环*)
(* Theorem tree_add_one_edge: forall {V E: Type} (pg: PreGraph V E) (t: PreGraph V E) (e: E),
  is_tree pg t -> pg.(evalid) e -> ~ t.(evalid) e -> 
  exists! l, is_Cycle  l.
Proof.
  
Qed. *)



