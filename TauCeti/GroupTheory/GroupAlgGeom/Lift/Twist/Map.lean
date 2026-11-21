/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Lift.Twist.Tower
public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Map

/-!
# Morphisms of stages of twist towers

A morphism `P → Q` of stages (`TauCeti.GroupAlgGeom.Lift.TowerStage.Hom`) is a `G`-homomorphism
of their groups carrying the point of `P` to the point of `Q`; it carries the value of a word at
the point of `P` to its value at the point of `Q`. A morphism lifts to the lifts of the stages
along a twist datum (`TowerStage.Hom.lift`): it is the homomorphism of extensions of centralizers
that it induces (`TauCeti.LimitGroup.CentralizerExt.map`). So it induces homomorphisms of the towers
along any list of twist data (`TowerStage.Hom.tower`), compatibly with identities and composition,
and these commute with the retractions of the towers onto their bases
(`TowerStage.Hom.towerRetraction_tower`).

The retraction `t ↦ u ^ k` of the lift along a twist datum `d` is a morphism from the lift to the
stage twisted `k` times along `d` (`TowerStage.liftRetraction`, [IFT], §7.2, (84)–(85)).

## Main definitions

* `TauCeti.GroupAlgGeom.Lift.TowerStage.Hom`: morphisms of stages.
* `TauCeti.GroupAlgGeom.Lift.TowerStage.Hom.lift`: the lift of a morphism along a twist datum.
* `TauCeti.GroupAlgGeom.Lift.TowerStage.Hom.tower`: the induced homomorphism of towers.
* `TauCeti.GroupAlgGeom.Lift.TowerStage.liftRetraction`: the retraction `t ↦ u ^ k` of one step,
  as a morphism to the twisted stage.

## Main results

* `TauCeti.GroupAlgGeom.Lift.TowerStage.Hom.tower_id`,
  `TauCeti.GroupAlgGeom.Lift.TowerStage.Hom.tower_comp`: the induced homomorphisms of towers
  respect identities and composition.
* `TauCeti.GroupAlgGeom.Lift.TowerStage.Hom.towerRetraction_tower`: they commute with the
  retractions of the towers onto their bases.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §7.2, (84)–(85) and Proposition 4.
-/

public section

universe u v w

open TauCeti.LimitGroup

namespace TauCeti.GroupAlgGeom.Lift

variable {G : Type u} [Group G] {X : Type v}

namespace TowerStage

/-- A morphism of stages: a `G`-homomorphism of the groups (`TauCeti.GroupAlgGeom.GHom`) carrying
the point of the first stage to the point of the second. -/
structure Hom (P Q : TowerStage.{u, v, w} G X) extends GHom P.coeff Q.coeff where
  /-- The homomorphism carries the point of the first stage to the point of the second. -/
  comp_point : toFun ∘ P.point = Q.point

/-- The `G`-homomorphism underlying a morphism of stages. -/
add_decl_doc Hom.toGHom

namespace Hom

variable {P Q R : TowerStage.{u, v, w} G X}

instance : FunLike (P.Hom Q) P.carrier Q.carrier where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ := g
    congr

instance : MonoidHomClass (P.Hom Q) P.carrier Q.carrier where
  map_mul f := f.map_mul'
  map_one f := f.map_one'

@[simp]
theorem coe_toGHom (f : P.Hom Q) : ⇑f.toGHom = f := (rfl)

theorem coe_toMonoidHom (f : P.Hom Q) : ⇑f.toMonoidHom = f := (rfl)

/-- Morphisms of stages agree when their homomorphisms agree. -/
@[ext]
theorem ext {f g : P.Hom Q} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[simp]
theorem map_coeff (f : P.Hom Q) (g : G) : f (P.coeff g) = Q.coeff g :=
  f.map_coeff' g

@[simp]
theorem map_point (f : P.Hom Q) (x : X) : f (P.point x) = Q.point x :=
  congrFun f.comp_point x

/-- A morphism of stages carries the value of a word at the first point to its value at the
second. -/
@[simp]
theorem map_eval (f : P.Hom Q) (w : GX G X) : f (eval P.coeff P.point w) = eval Q.coeff Q.point w :=
  (GroupAlgGeom.map_eval f.toGHom w).trans (by rw [← f.comp_point]; rfl)

variable (P) in
/-- The identity morphism of a stage. -/
protected def id : P.Hom P where
  toMonoidHom := .id P.carrier
  map_coeff' _ := rfl
  comp_point := rfl

@[simp]
theorem coe_id : ⇑(Hom.id P) = id := (rfl)

/-- The composite of two morphisms of stages. -/
def comp (g : Q.Hom R) (f : P.Hom Q) : P.Hom R where
  toMonoidHom := g.toMonoidHom.comp f.toMonoidHom
  map_coeff' x := by simp
  comp_point := funext fun x => by simp

@[simp]
theorem coe_comp (g : Q.Hom R) (f : P.Hom Q) : ⇑(g.comp f) = g ∘ f := (rfl)

@[simp]
theorem id_comp (f : P.Hom Q) : (Hom.id Q).comp f = f := (rfl)

@[simp]
theorem comp_id (f : P.Hom Q) : f.comp (Hom.id P) = f := (rfl)

/-- A morphism of stages lifts to their lifts along a twist datum: the homomorphism of extensions
of centralizers induced by it (`TauCeti.LimitGroup.CentralizerExt.map`), followed by the
identification of the extensions of the centralizers of the equal elements `f (A(v))` and
`A(f ∘ v)`. -/
noncomputable def lift (f : P.Hom Q) (d : TwistData G X) : (P.lift d).Hom (Q.lift d) where
  toMonoidHom :=
    (CentralizerExt.congr (n := 1) (u := f.toMonoidHom (eval P.coeff P.point d.A))
      (v := eval Q.coeff Q.point d.A)
      (congrArg (Subgroup.centralizer {·}) (f.map_eval d.A))).toMonoidHom.comp
      (CentralizerExt.map f.toMonoidHom _ 1)
  map_coeff' g := by
    -- `(P.lift d).coeff g` is `CentralizerExt.of (P.coeff g)` (`TowerStage.lift_coeff`), but its
    -- type `(P.lift d).carrier` is not reducibly the extension of the centralizer, so `simp` and
    -- `rw` cannot apply the equations of `CentralizerExt.map` to it; `change` restates the goal
    -- in the extensions of centralizers.
    change CentralizerExt.congr _ (CentralizerExt.map f.toMonoidHom _ 1
      (CentralizerExt.of (P.coeff g))) = CentralizerExt.of (Q.coeff g)
    simp only [CentralizerExt.map_of, CentralizerExt.congr_of, coe_toMonoidHom, map_coeff]
  comp_point := funext fun x => by
    -- As for `map_coeff'`: the point of the lift is `twistLift` (`TowerStage.lift_point`), with
    -- values in the extension of the centralizer only up to unfolding `(P.lift d).carrier`.
    change CentralizerExt.congr _ (CentralizerExt.map f.toMonoidHom _ 1
      (twistLift (eval P.coeff P.point d.A) P.point d.e x)) =
        twistLift (eval Q.coeff Q.point d.A) Q.point d.e x
    simp only [twistLift_apply, map_mul, map_zpow, CentralizerExt.map_t, CentralizerExt.map_of,
      CentralizerExt.congr_t, CentralizerExt.congr_of, coe_toMonoidHom, map_point]

theorem lift_apply (f : P.Hom Q) (d : TwistData G X) (x : (P.lift d).carrier) :
    f.lift d x = CentralizerExt.congr (congrArg (Subgroup.centralizer {·}) (f.map_eval d.A))
      (CentralizerExt.map f.toMonoidHom _ 1 x) := (rfl)

@[simp]
theorem lift_of (f : P.Hom Q) (d : TwistData G X) (x : P.carrier) :
    f.lift d (CentralizerExt.of x) = CentralizerExt.of (f x) :=
  (congrArg (CentralizerExt.congr _) (CentralizerExt.map_of _ _ 1 x)).trans
    (CentralizerExt.congr_of _ _)

@[simp]
theorem lift_t (f : P.Hom Q) (d : TwistData G X) (i : Fin 1) :
    f.lift d (CentralizerExt.t i) = CentralizerExt.t i :=
  (congrArg (CentralizerExt.congr _) (CentralizerExt.map_t _ _ 1 i)).trans
    (CentralizerExt.congr_t _ _)

/-- Lifts of morphisms of stages along a twist datum agree when they agree on the base and on the
new letter. -/
private theorem lift_ext {d : TwistData G X} {f g : (P.lift d).Hom Q}
    (hof : ∀ x, f (CentralizerExt.of x) = g (CentralizerExt.of x))
    (ht : f (CentralizerExt.t 0) = g (CentralizerExt.t 0)) : f = g :=
  ext fun x => DFunLike.congr_fun (CentralizerExt.hom_ext (MonoidHom.ext hof)
    (fun i => Fin.fin_one_eq_zero i ▸ ht) : f.toMonoidHom = g.toMonoidHom) x

@[simp]
theorem lift_id (d : TwistData G X) : (Hom.id P).lift d = Hom.id (P.lift d) :=
  lift_ext (lift_of _ d) (lift_t _ d 0)

theorem lift_comp (g : Q.Hom R) (f : P.Hom Q) (d : TwistData G X) :
    (g.comp f).lift d = (g.lift d).comp (f.lift d) :=
  lift_ext (fun x => (lift_of _ d x).trans
      ((congrArg (g.lift d) (lift_of f d x)).trans (lift_of g d (f x))).symm)
    ((lift_t _ d 0).trans ((congrArg (g.lift d) (lift_t f d 0)).trans (lift_t g d 0)).symm)

/-- The homomorphism of towers induced by a morphism of their bases. -/
@[expose] noncomputable def tower {P Q : TowerStage.{u, v, w} G X} :
    (l : List (TwistData G X)) → P.Hom Q → (twistTower l P).Hom (twistTower l Q)
  | [], f => f
  | d :: l, f => tower l (f.lift d)

@[simp]
theorem tower_nil (f : P.Hom Q) : f.tower [] = f := (rfl)

@[simp]
theorem tower_cons (f : P.Hom Q) (d : TwistData G X) (l : List (TwistData G X)) :
    f.tower (d :: l) = (f.lift d).tower l := (rfl)

@[simp]
theorem tower_id (l : List (TwistData G X)) : (Hom.id P).tower l = Hom.id (twistTower l P) := by
  induction l generalizing P with
  | nil => rfl
  | cons d l ih => exact (congrArg (tower l) (lift_id d)).trans ih

theorem tower_comp (g : Q.Hom R) (f : P.Hom Q) (l : List (TwistData G X)) :
    (g.comp f).tower l = (g.tower l).comp (f.tower l) := by
  induction l generalizing P Q R with
  | nil => rfl
  | cons d l ih => exact (congrArg (tower l) (lift_comp g f d)).trans (ih _ _)

/-- The lift of a morphism of stages commutes with the retractions `t ↦ u ^ k` of the lifts. -/
private theorem retraction_lift_apply (f : P.Hom Q) (d : TwistData G X) (k : ℤ)
    (x : (P.lift d).carrier) :
    CentralizerExt.retraction (fun _ => k) (f.lift d x) =
      f (CentralizerExt.retraction (fun _ => k) x) := by
  refine DFunLike.congr_fun (CentralizerExt.hom_ext (MonoidHom.ext fun g => ?_) fun i => ?_ :
    (CentralizerExt.retraction fun _ => k).comp (f.lift d).toMonoidHom =
      f.toMonoidHom.comp (CentralizerExt.retraction fun _ => k)) x
  -- Both sides are `f` on the base and send the new letter to `A(f ∘ v) ^ k = f (A(v) ^ k)`.
  · exact (congrArg _ (lift_of f d g)).trans <| (CentralizerExt.retraction_of _ _).trans
      (congrArg f (CentralizerExt.retraction_of _ g)).symm
  · exact (congrArg _ (lift_t f d i)).trans <| (CentralizerExt.retraction_t _ i).trans <|
      ((congrArg f (CentralizerExt.retraction_t _ i)).trans
        ((map_zpow f _ k).trans (congrArg (· ^ k) (f.map_eval d.A)))).symm

/-- The homomorphisms of towers induced by a morphism of stages commute with the retractions of
the towers onto their bases. -/
theorem towerRetraction_tower (f : P.Hom Q) (l : List (TwistData G X)) (p : List ℕ)
    (x : (twistTower l P).carrier) :
    towerRetraction l Q p (f.tower l x) = f (towerRetraction l P p x) := by
  induction l generalizing P Q p with
  | nil =>
    -- The tower along `[]` is the base only up to unfolding `twistTower`, which blocks
    -- `MonoidHom.id_apply`; the identities are applied definitionally.
    rw [towerRetraction_nil, towerRetraction_nil]
    rfl
  | cons d l ih =>
    rw [towerRetraction_cons_apply, towerRetraction_cons_apply]
    exact (congrArg _ (ih (f.lift d) p.tail x)).trans (retraction_lift_apply f d _ _)

end Hom

/-- The retraction `t ↦ u ^ k` of the lift along `d`, as a morphism to the stage twisted `k`
times along `d` ([IFT], §7.2: the transformation (84) is the specialisation `t ↦ u ^ q` of
(85)). -/
noncomputable def liftRetraction (P : TowerStage.{u, v, w} G X) (d : TwistData G X) (k : ℤ) :
    (P.lift d).Hom (P.twisted d k) where
  toMonoidHom := CentralizerExt.retraction fun _ => k
  -- `(P.lift d).coeff g` is `CentralizerExt.of (P.coeff g)` and `(P.twisted d k).coeff` is
  -- `P.coeff` (`TowerStage.lift_coeff`, `TowerStage.twisted_coeff`); the types of the stages are
  -- not reducibly those of the extension of the centralizer and of `P`, so the equation
  -- `CentralizerExt.retraction_of` is applied up to unfolding them.
  map_coeff' g := CentralizerExt.retraction_of _ (P.coeff g)
  comp_point := P.retraction_comp_lift_point d k

@[simp]
theorem liftRetraction_apply (P : TowerStage.{u, v, w} G X) (d : TwistData G X) (k : ℤ)
    (x : (P.lift d).carrier) :
    P.liftRetraction d k x = CentralizerExt.retraction (fun _ => k) x := (rfl)

end TowerStage

end TauCeti.GroupAlgGeom.Lift
