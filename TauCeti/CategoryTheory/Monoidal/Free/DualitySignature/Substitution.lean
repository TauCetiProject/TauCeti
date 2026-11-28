/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Diagram.RigidObject.Substitution
public import TauCeti.CategoryTheory.Monoidal.Free.DualitySignature.Basic
public import TauCeti.CategoryTheory.Monoidal.Free.DualitySignature.Interpretation
import TauCeti.CategoryTheory.EqToHom
import TauCeti.CategoryTheory.Monoidal.EqToHom

/-!
# Substitution of rigid expressions for coupons

A `DualitySignature.Substitution S T` replaces object generators of `S` by objects of
`T.FreeRigid` and coupons of `S` by raw morphisms `FreeRigid.Hom` in `T`:

* `FreeRigid.eval_eq_subst`, `FreeRigid.as_eval_eq_subst`,
  `Substitution.normalize_toFunctor_obj_as`: identify categorical object evaluation with
  `RigidObject.subst` and `WindingWord.subst`.
* `FreeRigid.Hom.subst` and `FreeRigid.HomEquiv.subst`: typed substitution on raw morphism
  expressions respecting the monoidal and zigzag axioms without coupon equations.
* `Substitution.toFunctor` and `Substitution.toFunctor_map_homMk`: induced strong monoidal functor
  `S.FreeRigid ⥤ T.FreeRigid` via `FreeRigid.lift`, agreeing with raw substitution.
* `Substitution.id` and `Substitution.comp`: identity and diagrammatic composition of
  substitutions, with two-sided unit laws (`id_comp`, `comp_id`), associativity (`comp_assoc`),
  coupon and raw substitution laws (`id_coupon`, `comp_coupon`, `Hom.subst_substitutionId`,
  `Hom.subst_subst`, and their `HEq` forms), and functoriality (`toFunctor_id`, `toFunctor_comp`).
* `Interpretation.reindex` and `Interpretation.extensionReindexIso`: reindexing of
  `DualitySignature.Interpretation` in an arbitrary rigid target along a substitution, with
  generator/coupon computation rules, identity and composition laws (`reindex_id`, `reindex_comp`,
  `reindex_reindex`), and a monoidal natural isomorphism comparing its extension with precomposition
  by `σ.toFunctor`.
* `DualitySignature.Renaming` and `Renaming.toSubstitution`: boundary-preserving renamings of
  generators and coupons, inducing substitutions with object and coupon computation rules.

Parallels `TauCeti.TensorSignature.Substitution`, extended to right and left duals.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §1.
* A. Joyal and R. Street, *Planar diagrams and tensor algebra*, unpublished manuscript (1988), §2.
-/

public section

universe u v u' v' u'' v'' u''' v''' w

open CategoryTheory MonoidalCategory ExactPairing

namespace TauCeti.DualitySignature

/-- A typed substitution between duality signatures. Object generators of `S` are replaced by
formal rigid object expressions in `T`, and coupons of `S` are replaced by raw morphism expressions
with the substituted source and target boundaries. The universes of the two signatures are
independent. -/
@[ext]
structure Substitution (S : DualitySignature.{u, v}) (T : DualitySignature.{u', v'}) where
  /-- The formal rigid object expression replacing each generating object of `S`. -/
  obj : S.Obj → T.FreeRigid
  /-- The raw formal morphism expression replacing each coupon of `S`. -/
  coupon : ∀ g : S.Coupon, FreeRigid.Hom
    (RigidObject.eval obj (S.src g)).as (RigidObject.eval obj (S.tgt g)).as

variable {S : DualitySignature.{u, v}} {T : DualitySignature.{u', v'}}
  {U : DualitySignature.{u'', v''}} {V : DualitySignature.{u''', v'''}}

namespace FreeRigid

/-- Interpreting a formal rigid object expression via `f : α → T.FreeRigid` wraps the syntactic
substitution `RigidObject.subst` of the underlying object expressions `(f a).as`. -/
theorem eval_eq_subst {α : Type w} (f : α → T.FreeRigid) (X : RigidObject α) :
    RigidObject.eval f X = ⟨RigidObject.subst (fun a ↦ (f a).as) X⟩ := by
  induction X with
  | of _ => rw [RigidObject.eval_of, RigidObject.subst_of]
  | unit => rw [RigidObject.eval_unit, RigidObject.subst_unit, mk_unit]
  | tensor _ _ ihX ihY =>
    rw [RigidObject.eval_tensor, RigidObject.subst_tensor, ihX, ihY, mk_tensor]
  | rightDual _ ih =>
    rw [RigidObject.eval_rightDual, RigidObject.subst_rightDual, ih, mk_rightDual]
  | leftDual _ ih =>
    rw [RigidObject.eval_leftDual, RigidObject.subst_leftDual, ih, mk_leftDual]

/-- Underlying `RigidObject` form of `eval_eq_subst`: categorical interpretation into
`T.FreeRigid` agrees with syntactic substitution `RigidObject.subst`. -/
@[simp]
theorem as_eval_eq_subst {α : Type w} (f : α → T.FreeRigid) (X : RigidObject α) :
    (RigidObject.eval f X).as = RigidObject.subst (fun a ↦ (f a).as) X :=
  congrArg FreeRigid.as (eval_eq_subst f X)

/-- Interpreting a formal rigid object by the generating objects of `S` recovers the object
itself. -/
@[simp]
theorem eval_of (X : RigidObject S.Obj) :
    RigidObject.eval (FreeRigid.of (S := S)) X = ⟨X⟩ :=
  (eval_eq_subst _ X).trans (congrArg FreeRigid.mk (RigidObject.subst_self X))

/-- Interpreting a formal rigid object after replacing generators by objects of `T.FreeRigid`
agrees with interpreting the outer assignment at the interpreted replacements. -/
theorem eval_eval {D : Type u''} [Category.{v''} D] [MonoidalCategory D] [RigidCategory D]
    (f : S.Obj → T.FreeRigid) (g : T.Obj → D) (X : RigidObject S.Obj) :
    RigidObject.eval g (RigidObject.eval f X).as =
      RigidObject.eval (fun a ↦ RigidObject.eval g (f a).as) X := by
  rw [as_eval_eq_subst, RigidObject.eval_subst]

/-- Substitute formal rigid object expressions for object generators and raw morphism expressions
for coupons. Endpoints are interpreted by `RigidObject.eval`. -/
def Hom.subst (σ : Substitution S T) : ∀ {X Y}, Hom X Y →
    Hom (RigidObject.eval σ.obj X).as (RigidObject.eval σ.obj Y).as
  | _, _, .id X => .id (RigidObject.eval σ.obj X).as
  | _, _, .α_hom X Y Z => .α_hom (RigidObject.eval σ.obj X).as
      (RigidObject.eval σ.obj Y).as (RigidObject.eval σ.obj Z).as
  | _, _, .α_inv X Y Z => .α_inv (RigidObject.eval σ.obj X).as
      (RigidObject.eval σ.obj Y).as (RigidObject.eval σ.obj Z).as
  | _, _, .l_hom X => .l_hom (RigidObject.eval σ.obj X).as
  | _, _, .l_inv X => .l_inv (RigidObject.eval σ.obj X).as
  | _, _, .ρ_hom X => .ρ_hom (RigidObject.eval σ.obj X).as
  | _, _, .ρ_inv X => .ρ_inv (RigidObject.eval σ.obj X).as
  | _, _, .ε_right X => .ε_right (RigidObject.eval σ.obj X).as
  | _, _, .η_right X => .η_right (RigidObject.eval σ.obj X).as
  | _, _, .ε_left X => .ε_left (RigidObject.eval σ.obj X).as
  | _, _, .η_left X => .η_left (RigidObject.eval σ.obj X).as
  | _, _, .coupon g => σ.coupon g
  | _, _, .comp f g => (f.subst σ).comp (g.subst σ)
  | _, _, .whiskerLeft X f => (f.subst σ).whiskerLeft (RigidObject.eval σ.obj X).as
  | _, _, .whiskerRight f X => (f.subst σ).whiskerRight (RigidObject.eval σ.obj X).as
  | _, _, .tensor f g => (f.subst σ).tensor (g.subst σ)

@[simp] theorem Hom.subst_id (σ : Substitution S T) (X) :
    (Hom.id X).subst σ = .id (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_coupon (σ : Substitution S T) (g : S.Coupon) :
    (Hom.coupon g).subst σ = σ.coupon g := by rfl
@[simp] theorem Hom.subst_comp (σ : Substitution S T) {X Y Z} (f : Hom X Y) (g : Hom Y Z) :
    (f.comp g).subst σ = (f.subst σ).comp (g.subst σ) := by rfl
@[simp] theorem Hom.subst_tensor (σ : Substitution S T) {W X Y Z} (f : Hom W X) (g : Hom Y Z) :
    (f.tensor g).subst σ = (f.subst σ).tensor (g.subst σ) := by rfl
@[simp] theorem Hom.subst_whiskerLeft (σ : Substitution S T) (X) {Y Z} (f : Hom Y Z) :
    (f.whiskerLeft X).subst σ = (f.subst σ).whiskerLeft (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_whiskerRight (σ : Substitution S T) {Y Z} (f : Hom Y Z) (X) :
    (f.whiskerRight X).subst σ = (f.subst σ).whiskerRight (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_α_hom (σ : Substitution S T) (X Y Z) : (Hom.α_hom X Y Z).subst σ =
    .α_hom (RigidObject.eval σ.obj X).as (RigidObject.eval σ.obj Y).as
      (RigidObject.eval σ.obj Z).as := by rfl
@[simp] theorem Hom.subst_α_inv (σ : Substitution S T) (X Y Z) : (Hom.α_inv X Y Z).subst σ =
    .α_inv (RigidObject.eval σ.obj X).as (RigidObject.eval σ.obj Y).as
      (RigidObject.eval σ.obj Z).as := by rfl
@[simp] theorem Hom.subst_l_hom (σ : Substitution S T) (X) :
    (Hom.l_hom X).subst σ = .l_hom (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_l_inv (σ : Substitution S T) (X) :
    (Hom.l_inv X).subst σ = .l_inv (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_ρ_hom (σ : Substitution S T) (X) :
    (Hom.ρ_hom X).subst σ = .ρ_hom (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_ρ_inv (σ : Substitution S T) (X) :
    (Hom.ρ_inv X).subst σ = .ρ_inv (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_ε_right (σ : Substitution S T) (X) :
    (Hom.ε_right X).subst σ = .ε_right (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_η_right (σ : Substitution S T) (X) :
    (Hom.η_right X).subst σ = .η_right (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_ε_left (σ : Substitution S T) (X) :
    (Hom.ε_left X).subst σ = .ε_left (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_η_left (σ : Substitution S T) (X) :
    (Hom.η_left X).subst σ = .η_left (RigidObject.eval σ.obj X).as := by rfl

end FreeRigid

namespace Substitution

open FreeRigid

variable (σ : Substitution S T)

/-- The strong monoidal functor `S.FreeRigid ⥤ T.FreeRigid` induced by a raw substitution, defined
as the universal lift of `σ.obj` and the quotient morphisms of `σ.coupon`. Exposed on objects so
that dependent morphism types over substituted endpoints reduce on constructors. -/
@[expose] def toFunctor : S.FreeRigid ⥤ T.FreeRigid :=
  FreeRigid.lift σ.obj (fun g ↦ FreeRigid.homMk (σ.coupon g))

instance : σ.toFunctor.Monoidal :=
  inferInstanceAs (FreeRigid.lift σ.obj (fun g ↦ FreeRigid.homMk (σ.coupon g))).Monoidal

@[simp] theorem toFunctor_ε : Functor.LaxMonoidal.ε σ.toFunctor = 𝟙 _ := FreeRigid.lift_ε _ _
@[simp] theorem toFunctor_η : Functor.OplaxMonoidal.η σ.toFunctor = 𝟙 _ := FreeRigid.lift_η _ _
@[simp] theorem toFunctor_μ (X Y : S.FreeRigid) :
    Functor.LaxMonoidal.μ σ.toFunctor X Y = 𝟙 _ := FreeRigid.lift_μ _ _ X Y
@[simp] theorem toFunctor_δ (X Y : S.FreeRigid) :
    Functor.OplaxMonoidal.δ σ.toFunctor X Y = 𝟙 _ := FreeRigid.lift_δ _ _ X Y
@[simp] theorem toFunctor_mapRightDualIso (X : S.FreeRigid) :
    σ.toFunctor.mapRightDualIso X = Iso.refl _ := FreeRigid.lift_mapRightDualIso _ _ X
@[simp] theorem toFunctor_mapLeftDualIso (X : S.FreeRigid) :
    σ.toFunctor.mapLeftDualIso X = Iso.refl _ := FreeRigid.lift_mapLeftDualIso _ _ X
@[simp] theorem toFunctor_obj (X : S.FreeRigid) :
    σ.toFunctor.obj X = RigidObject.eval σ.obj X.as := by rfl

theorem toFunctor_obj_as (X : S.FreeRigid) :
    (σ.toFunctor.obj X).as = RigidObject.subst (fun a ↦ (σ.obj a).as) X.as :=
  FreeRigid.as_eval_eq_subst σ.obj X.as

/-- Normalization of a substituted `FreeRigid` object agrees with winding-word substitution on the
normalized boundaries. -/
theorem normalize_toFunctor_obj_as (X : S.FreeRigid) :
    RigidObject.normalize (σ.toFunctor.obj X).as =
      WindingWord.subst (fun a ↦ RigidObject.normalize (σ.obj a).as)
        (RigidObject.normalize X.as) := by rw [σ.toFunctor_obj_as, RigidObject.normalize_subst]

@[simp] theorem toFunctor_map_coupon (g : S.Coupon) :
    σ.toFunctor.map (FreeRigid.coupon g) = FreeRigid.homMk (σ.coupon g) :=
  FreeRigid.lift_map_coupon _ _ g

/-- Interpreting a raw formal morphism expression via `σ.toFunctor` yields the equivalence class of
its raw substitution `f.subst σ`. -/
@[simp] theorem toFunctor_map_homMk {X Y : RigidObject S.Obj} (f : FreeRigid.Hom X Y) :
    σ.toFunctor.map (FreeRigid.homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f) = FreeRigid.homMk (f.subst σ) := by
  induction f with
  | id X => exact liftMap_id _ _ ⟨X⟩
  | α_hom X Y Z => exact lift_map_associator_hom _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | α_inv X Y Z => exact lift_map_associator_inv _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | l_hom X => exact lift_map_leftUnitor_hom _ _ ⟨X⟩
  | l_inv X => exact lift_map_leftUnitor_inv _ _ ⟨X⟩
  | ρ_hom X => exact lift_map_rightUnitor_hom _ _ ⟨X⟩
  | ρ_inv X => exact lift_map_rightUnitor_inv _ _ ⟨X⟩
  | ε_right X => exact lift_map_evaluation_rightDual _ _ ⟨X⟩
  | η_right X => exact lift_map_coevaluation_rightDual _ _ ⟨X⟩
  | ε_left X => exact lift_map_evaluation_leftDual _ _ ⟨X⟩
  | η_left X => exact lift_map_coevaluation_leftDual _ _ ⟨X⟩
  | coupon g => rw [homMk_coupon, σ.toFunctor_map_coupon, Hom.subst_coupon]
  | comp _ _ hf hg => exact (liftMap_comp _ _ _ _).trans (congrArg₂ (· ≫ ·) hf hg)
  | whiskerLeft X _ hf =>
    exact (lift_map_whiskerLeft _ _ ⟨X⟩ _).trans (congrArg (RigidObject.eval σ.obj X ◁ ·) hf)
  | whiskerRight _ X hf =>
    exact (lift_map_whiskerRight _ _ _ ⟨X⟩).trans (congrArg (· ▷ RigidObject.eval σ.obj X) hf)
  | tensor _ _ hf hg => exact (lift_map_tensorHom _ _ _ _).trans (congrArg₂ (· ⊗ₘ ·) hf hg)

end Substitution

namespace FreeRigid

/-- Raw substitution preserves the congruence generated by the monoidal and zigzag axioms. No
equation between the replacing coupons is required. -/
theorem HomEquiv.subst (σ : Substitution S T) {X Y} {f g : Hom X Y} (h : HomEquiv f g) :
    HomEquiv (f.subst σ) (g.subst σ) :=
  Quotient.exact (s := setoidHom _ _) <| (σ.toFunctor_map_homMk f).symm.trans
    ((congrArg (σ.toFunctor.map (X := ⟨X⟩) (Y := ⟨Y⟩)) (Quotient.sound h)).trans
      (σ.toFunctor_map_homMk g))

end FreeRigid

namespace Substitution

open FreeRigid

/-- Two substitutions are equal if they replace each generating object by the same rigid
expression and each coupon by the same raw expression, compared heterogeneously across equal
substituted boundaries. -/
theorem hext {σ σ' : Substitution S T} (hobj : σ.obj = σ'.obj)
    (hcoupon : ∀ g, σ.coupon g ≍ σ'.coupon g) : σ = σ' := by
  obtain ⟨obj, coupon⟩ := σ
  obtain ⟨obj', coupon'⟩ := σ'
  subst hobj
  congr
  funext g
  exact eq_of_heq (hcoupon g)

variable (S) in
/-- The identity substitution, replacing each generating object and each coupon of `S` by
itself. Exposed so that dependent morphism types over substituted endpoints reduce. -/
@[expose] def id : Substitution S S where
  obj := FreeRigid.of
  coupon g := cast (by rw [FreeRigid.eval_of, FreeRigid.eval_of]) (Hom.coupon g)

@[simp]
theorem id_obj (a : S.Obj) : (Substitution.id S).obj a = FreeRigid.of a := (rfl)

/-- The identity substitution replaces a coupon by the coupon itself, up to the identification of
each boundary object with its interpretation by `FreeRigid.of`. -/
theorem id_coupon_heq (g : S.Coupon) : (Substitution.id S).coupon g ≍ Hom.coupon g :=
  cast_heq _ _

/-- The identity substitution replaces each coupon `g` by `Hom.coupon g`, transported along the
boundary identifications `FreeRigid.eval_of`. -/
@[simp]
theorem id_coupon (g : S.Coupon) :
    (Substitution.id S).coupon g =
      cast (congrArg₂ Hom (congrArg FreeRigid.as (eval_of (S.src g))).symm
        (congrArg FreeRigid.as (eval_of (S.tgt g))).symm) (Hom.coupon g) :=
  (rfl)

/-- The diagrammatic composite of `σ` and `τ`: each generating object and coupon of `S` is
replaced by its replacement under `σ`, into which `τ` is substituted. Exposed so that dependent
morphism types over substituted endpoints reduce. -/
@[expose] def comp (σ : Substitution S T) (τ : Substitution T U) : Substitution S U where
  obj a := RigidObject.eval τ.obj (σ.obj a).as
  coupon g := cast (by rw [FreeRigid.eval_eval, FreeRigid.eval_eval]) ((σ.coupon g).subst τ)

@[simp]
theorem comp_obj (σ : Substitution S T) (τ : Substitution T U) (a : S.Obj) :
    (σ.comp τ).obj a = RigidObject.eval τ.obj (σ.obj a).as := (rfl)

/-- The composite substitution replaces a coupon by the substitution of `τ` into its replacement
under `σ`, up to the identification of boundary objects given by `FreeRigid.eval_eval`. -/
theorem comp_coupon_heq (σ : Substitution S T) (τ : Substitution T U) (g : S.Coupon) :
    (σ.comp τ).coupon g ≍ (σ.coupon g).subst τ :=
  cast_heq _ _

/-- The composite substitution replaces each coupon `g` by `(σ.coupon g).subst τ`, transported
along the boundary identifications `FreeRigid.eval_eval`. -/
@[simp]
theorem comp_coupon (σ : Substitution S T) (τ : Substitution T U) (g : S.Coupon) :
    (σ.comp τ).coupon g =
      cast (congrArg₂ Hom (congrArg FreeRigid.as (eval_eval σ.obj τ.obj (S.src g)))
        (congrArg FreeRigid.as (eval_eval σ.obj τ.obj (S.tgt g))))
        ((σ.coupon g).subst τ) :=
  (rfl)

end Substitution

namespace FreeRigid

/-- Substituting into heterogeneously equal raw expressions gives heterogeneously equal
results. -/
theorem Hom.subst_congr_heq (σ : Substitution S T) {X X' Y Y' : RigidObject S.Obj}
    {f : Hom X Y} {f' : Hom X' Y'} (hX : X = X') (hY : Y = Y') (h : f ≍ f') :
    f.subst σ ≍ f'.subst σ := by
  subst hX hY
  rw [eq_of_heq h]

private theorem α_hom_heq {X X' Y Y' Z Z' : RigidObject S.Obj} (hX : X = X')
    (hY : Y = Y') (hZ : Z = Z') : Hom.α_hom X Y Z ≍ Hom.α_hom X' Y' Z' := by
  subst hX hY hZ
  rfl

private theorem α_inv_heq {X X' Y Y' Z Z' : RigidObject S.Obj} (hX : X = X')
    (hY : Y = Y') (hZ : Z = Z') : Hom.α_inv X Y Z ≍ Hom.α_inv X' Y' Z' := by
  subst hX hY hZ
  rfl

private theorem comp_heq {X X' Y Y' Z Z' : RigidObject S.Obj} {f : Hom X Y}
    {f' : Hom X' Y'} {g : Hom Y Z} {g' : Hom Y' Z'} (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (hf : f ≍ f') (hg : g ≍ g') : f.comp g ≍ f'.comp g' := by
  subst hX hY hZ
  rw [eq_of_heq hf, eq_of_heq hg]

private theorem whiskerLeft_heq {X X' Y₁ Y₁' Y₂ Y₂' : RigidObject S.Obj}
    {f : Hom Y₁ Y₂} {f' : Hom Y₁' Y₂'} (hX : X = X') (h₁ : Y₁ = Y₁') (h₂ : Y₂ = Y₂')
    (hf : f ≍ f') : f.whiskerLeft X ≍ f'.whiskerLeft X' := by
  subst hX h₁ h₂
  rw [eq_of_heq hf]

private theorem whiskerRight_heq {X₁ X₁' X₂ X₂' Y Y' : RigidObject S.Obj}
    {f : Hom X₁ X₂} {f' : Hom X₁' X₂'} (h₁ : X₁ = X₁') (h₂ : X₂ = X₂') (hY : Y = Y')
    (hf : f ≍ f') : f.whiskerRight Y ≍ f'.whiskerRight Y' := by
  subst h₁ h₂ hY
  rw [eq_of_heq hf]

private theorem tensor_heq {W W' X X' Y Y' Z Z' : RigidObject S.Obj} {f : Hom W Y}
    {f' : Hom W' Y'} {g : Hom X Z} {g' : Hom X' Z'} (hW : W = W') (hX : X = X') (hY : Y = Y')
    (hZ : Z = Z') (hf : f ≍ f') (hg : g ≍ g') : f.tensor g ≍ f'.tensor g' := by
  subst hW hX hY hZ
  rw [eq_of_heq hf, eq_of_heq hg]

private theorem homMk_heq {X X' Y Y' : RigidObject S.Obj} {f : Hom X Y}
    {f' : Hom X' Y'} (hX : X = X') (hY : Y = Y') (hf : f ≍ f') :
    homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f ≍ homMk (X := ⟨X'⟩) (Y := ⟨Y'⟩) f' := by
  subst hX hY
  rw [eq_of_heq hf]

/-- Substituting the identity substitution into a raw expression gives the expression itself, up
to the identification of each object with its interpretation by `FreeRigid.of`. -/
theorem Hom.subst_substitutionId_heq {X Y : RigidObject S.Obj} (f : Hom X Y) :
    f.subst (Substitution.id S) ≍ f := by
  have h (Z : RigidObject S.Obj) : (RigidObject.eval (Substitution.id S).obj Z).as = Z :=
    congrArg FreeRigid.as (eval_of Z)
  induction f with
  | id X => exact congr_arg_heq Hom.id (h X)
  | α_hom X Y Z => exact α_hom_heq (h X) (h Y) (h Z)
  | α_inv X Y Z => exact α_inv_heq (h X) (h Y) (h Z)
  | l_hom X => exact congr_arg_heq Hom.l_hom (h X)
  | l_inv X => exact congr_arg_heq Hom.l_inv (h X)
  | ρ_hom X => exact congr_arg_heq Hom.ρ_hom (h X)
  | ρ_inv X => exact congr_arg_heq Hom.ρ_inv (h X)
  | ε_right X => exact congr_arg_heq Hom.ε_right (h X)
  | η_right X => exact congr_arg_heq Hom.η_right (h X)
  | ε_left X => exact congr_arg_heq Hom.ε_left (h X)
  | η_left X => exact congr_arg_heq Hom.η_left (h X)
  | coupon g => exact Substitution.id_coupon_heq g
  | comp _ _ hf hg => exact comp_heq (h _) (h _) (h _) hf hg
  | whiskerLeft X _ hf => exact whiskerLeft_heq (h X) (h _) (h _) hf
  | whiskerRight _ X hf => exact whiskerRight_heq (h _) (h _) (h X) hf
  | tensor _ _ hf hg => exact tensor_heq (h _) (h _) (h _) (h _) hf hg

/-- Substituting `σ` and then `τ` into a raw expression is substituting their composite, up to
the identification of boundary objects given by `FreeRigid.eval_eval`. -/
theorem Hom.subst_subst_heq (σ : Substitution S T) (τ : Substitution T U)
    {X Y : RigidObject S.Obj} (f : Hom X Y) :
    (f.subst σ).subst τ ≍ f.subst (σ.comp τ) := by
  have h (Z : RigidObject S.Obj) :
      (RigidObject.eval τ.obj (RigidObject.eval σ.obj Z).as).as =
        (RigidObject.eval (σ.comp τ).obj Z).as :=
    congrArg FreeRigid.as (eval_eval σ.obj τ.obj Z)
  induction f with
  | id X => exact congr_arg_heq Hom.id (h X)
  | α_hom X Y Z => exact α_hom_heq (h X) (h Y) (h Z)
  | α_inv X Y Z => exact α_inv_heq (h X) (h Y) (h Z)
  | l_hom X => exact congr_arg_heq Hom.l_hom (h X)
  | l_inv X => exact congr_arg_heq Hom.l_inv (h X)
  | ρ_hom X => exact congr_arg_heq Hom.ρ_hom (h X)
  | ρ_inv X => exact congr_arg_heq Hom.ρ_inv (h X)
  | ε_right X => exact congr_arg_heq Hom.ε_right (h X)
  | η_right X => exact congr_arg_heq Hom.η_right (h X)
  | ε_left X => exact congr_arg_heq Hom.ε_left (h X)
  | η_left X => exact congr_arg_heq Hom.η_left (h X)
  | coupon g => exact (Substitution.comp_coupon_heq σ τ g).symm
  | comp _ _ hf hg => exact comp_heq (h _) (h _) (h _) hf hg
  | whiskerLeft X _ hf => exact whiskerLeft_heq (h X) (h _) (h _) hf
  | whiskerRight _ X hf => exact whiskerRight_heq (h _) (h _) (h X) hf
  | tensor _ _ hf hg => exact tensor_heq (h _) (h _) (h _) (h _) hf hg

/-- Substituting the identity substitution into a raw expression returns the expression itself,
transported along the boundary identifications `FreeRigid.eval_of`. -/
@[simp]
theorem Hom.subst_substitutionId {X Y : RigidObject S.Obj} (f : Hom X Y) :
    f.subst (Substitution.id S) =
      cast (congrArg₂ Hom (congrArg FreeRigid.as (eval_of X)).symm
        (congrArg FreeRigid.as (eval_of Y)).symm) f :=
  eq_of_heq (f.subst_substitutionId_heq.trans (cast_heq _ f).symm)

/-- Substituting `σ` and then `τ` into a raw expression agrees with substituting their composite,
transported along the boundary identifications `FreeRigid.eval_eval`. -/
@[simp]
theorem Hom.subst_subst (σ : Substitution S T) (τ : Substitution T U)
    {X Y : RigidObject S.Obj} (f : Hom X Y) :
    (f.subst σ).subst τ =
      cast (congrArg₂ Hom (congrArg FreeRigid.as (eval_eval σ.obj τ.obj X)).symm
        (congrArg FreeRigid.as (eval_eval σ.obj τ.obj Y)).symm) (f.subst (σ.comp τ)) :=
  eq_of_heq ((f.subst_subst_heq σ τ).trans (cast_heq _ (f.subst (σ.comp τ))).symm)

end FreeRigid

namespace Substitution

open FreeRigid

/-- The identity substitution is a left unit for composition. -/
@[simp]
theorem id_comp (σ : Substitution S T) : (Substitution.id S).comp σ = σ :=
  hext (funext fun _ ↦ rfl) fun g ↦ (comp_coupon_heq _ σ g).trans
    (Hom.subst_congr_heq σ (congrArg FreeRigid.as (eval_of _))
      (congrArg FreeRigid.as (eval_of _)) (id_coupon_heq g))

/-- The identity substitution is a right unit for composition. -/
@[simp]
theorem comp_id (σ : Substitution S T) : σ.comp (Substitution.id T) = σ :=
  hext (funext fun _ ↦ eval_of _) fun g ↦
    (comp_coupon_heq σ _ g).trans (Hom.subst_substitutionId_heq _)

/-- Composition of substitutions is associative. -/
@[simp]
theorem comp_assoc (σ : Substitution S T) (τ : Substitution T U) (ρ : Substitution U V) :
    (σ.comp τ).comp ρ = σ.comp (τ.comp ρ) :=
  hext (funext fun a ↦ eval_eval τ.obj ρ.obj (σ.obj a).as) fun g ↦
    ((comp_coupon_heq _ ρ g).trans
      (Hom.subst_congr_heq ρ
        (congrArg FreeRigid.as (eval_eval _ _ _)).symm
        (congrArg FreeRigid.as (eval_eval _ _ _)).symm
        (comp_coupon_heq σ τ g))).trans
      ((Hom.subst_subst_heq τ ρ _).trans (comp_coupon_heq σ _ g).symm)

/-- The functor induced by the identity substitution is the identity functor. -/
@[simp]
theorem toFunctor_id : (Substitution.id S).toFunctor = 𝟭 S.FreeRigid := by
  refine Functor.hext (fun X ↦ eval_of X.as) fun ⟨X⟩ ⟨Y⟩ f ↦ ?_
  induction f using Quotient.inductionOn with | _ f
  exact ((Substitution.id S).toFunctor_map_homMk f).heq.trans
    (homMk_heq (congrArg FreeRigid.as (eval_of X))
      (congrArg FreeRigid.as (eval_of Y)) (Hom.subst_substitutionId_heq f))

/-- The functor induced by a composite substitution is the composite of the induced
functors. -/
@[simp]
theorem toFunctor_comp (σ : Substitution S T) (τ : Substitution T U) :
    (σ.comp τ).toFunctor = σ.toFunctor ⋙ τ.toFunctor := by
  refine Functor.hext (fun X ↦ (eval_eval σ.obj τ.obj X.as).symm)
    fun ⟨X⟩ ⟨Y⟩ f ↦ ?_
  induction f using Quotient.inductionOn with | _ f
  refine ((σ.comp τ).toFunctor_map_homMk f).heq.trans (HEq.trans ?_
    ((congrArg τ.toFunctor.map (σ.toFunctor_map_homMk f)).trans
      (τ.toFunctor_map_homMk _)).symm.heq)
  exact homMk_heq (congrArg FreeRigid.as (eval_eval σ.obj τ.obj X)).symm
    (congrArg FreeRigid.as (eval_eval σ.obj τ.obj Y)).symm
    (Hom.subst_subst_heq σ τ f).symm

end Substitution

/-- A boundary-preserving renaming between duality signatures. Generating objects and coupons of
`S` are sent to generating objects and coupons of `T`, preserving the formal source and target
boundaries up to generator renaming. -/
@[ext]
structure Renaming (S : DualitySignature.{u, v}) (T : DualitySignature.{u', v'}) where
  /-- The map on generating objects. -/
  obj : S.Obj → T.Obj
  /-- The map on coupons. -/
  coupon : S.Coupon → T.Coupon
  /-- Source boundaries are preserved under generator renaming. -/
  src_eq : ∀ g : S.Coupon, T.src (coupon g) = RigidObject.subst (fun a ↦ .of (obj a)) (S.src g)
  /-- Target boundaries are preserved under generator renaming. -/
  tgt_eq : ∀ g : S.Coupon, T.tgt (coupon g) = RigidObject.subst (fun a ↦ .of (obj a)) (S.tgt g)

namespace Renaming

/-- The identity renaming on a duality signature `S`. -/
def id (S : DualitySignature.{u, v}) : Renaming S S where
  obj := _root_.id
  coupon := _root_.id
  src_eq _ := (RigidObject.subst_self _).symm
  tgt_eq _ := (RigidObject.subst_self _).symm

@[simp] theorem id_obj (a : S.Obj) : (id S).obj a = a := (rfl)
@[simp] theorem id_coupon (g : S.Coupon) : (id S).coupon g = g := (rfl)

/-- Composition of boundary-preserving renamings in diagrammatic order. -/
def comp (r : Renaming S T) (s : Renaming T U) : Renaming S U where
  obj := s.obj ∘ r.obj
  coupon := s.coupon ∘ r.coupon
  src_eq g := by
    rw [Function.comp_apply, s.src_eq, r.src_eq, RigidObject.subst_subst]
    simp
  tgt_eq g := by
    rw [Function.comp_apply, s.tgt_eq, r.tgt_eq, RigidObject.subst_subst]
    simp

@[simp] theorem comp_obj (r : Renaming S T) (s : Renaming T U) (a : S.Obj) :
    (r.comp s).obj a = s.obj (r.obj a) := (rfl)
@[simp] theorem comp_coupon (r : Renaming S T) (s : Renaming T U) (g : S.Coupon) :
    (r.comp s).coupon g = s.coupon (r.coupon g) := (rfl)

@[simp] theorem id_comp (r : Renaming S T) : (id S).comp r = r := by ext <;> simp
@[simp] theorem comp_id (r : Renaming S T) : r.comp (id T) = r := by ext <;> simp
@[simp] theorem comp_assoc (r : Renaming S T) (s : Renaming T U) (t : Renaming U V) :
    (r.comp s).comp t = r.comp (s.comp t) := by ext <;> simp

/-- The typed substitution induced by a boundary-preserving renaming, sending each generating
object `a` to `FreeRigid.of (r.obj a)` and transporting each coupon
`FreeRigid.Hom.coupon (r.coupon g)` across the preserved boundaries. Exposed so that dependent
morphism types over substituted endpoints reduce. -/
@[expose] def toSubstitution (r : Renaming S T) : Substitution S T where
  obj a := FreeRigid.of (r.obj a)
  coupon g :=
    cast (congrArg₂ FreeRigid.Hom
      ((r.src_eq g).trans (FreeRigid.as_eval_eq_subst _ _).symm)
      ((r.tgt_eq g).trans (FreeRigid.as_eval_eq_subst _ _).symm))
      (FreeRigid.Hom.coupon (r.coupon g))

@[simp]
theorem toSubstitution_obj (r : Renaming S T) (a : S.Obj) :
    r.toSubstitution.obj a = FreeRigid.of (r.obj a) := (rfl)

/-- The substitution induced by a renaming replaces each coupon `g` by
`FreeRigid.Hom.coupon (r.coupon g)`, up to heterogeneous equality across the preserved source and
target boundaries. -/
theorem toSubstitution_coupon_heq (r : Renaming S T) (g : S.Coupon) :
    r.toSubstitution.coupon g ≍ FreeRigid.Hom.coupon (r.coupon g) :=
  cast_heq _ _

/-- The substitution induced by a renaming replaces each coupon `g` by
`FreeRigid.Hom.coupon (r.coupon g)`, transported across the preserved source and target
boundaries. -/
@[simp]
theorem toSubstitution_coupon (r : Renaming S T) (g : S.Coupon) :
    r.toSubstitution.coupon g =
      cast (congrArg₂ FreeRigid.Hom
        ((r.src_eq g).trans (FreeRigid.as_eval_eq_subst _ _).symm)
        ((r.tgt_eq g).trans (FreeRigid.as_eval_eq_subst _ _).symm))
        (FreeRigid.Hom.coupon (r.coupon g)) :=
  (rfl)

/-- The functor induced by `r.toSubstitution` acts on objects by syntactic renaming
`RigidObject.subst (fun a ↦ .of (r.obj a))`. -/
theorem toSubstitution_toFunctor_obj (r : Renaming S T) (X : S.FreeRigid) :
    r.toSubstitution.toFunctor.obj X = ⟨RigidObject.subst (fun a ↦ .of (r.obj a)) X.as⟩ :=
  FreeRigid.eval_eq_subst _ _

private theorem homMk_eq_eqToHom_of_heq {X₁ X₂ Y₁ Y₂ : T.FreeRigid}
    (hX : X₁ = X₂) (hY : Y₁ = Y₂) {f₁ : FreeRigid.Hom X₁.as Y₁.as}
    {f₂ : FreeRigid.Hom X₂.as Y₂.as} (hf : f₁ ≍ f₂) :
    FreeRigid.homMk f₁ = eqToHom hX ≫ FreeRigid.homMk f₂ ≫ eqToHom hY.symm := by
  subst hX hY
  cases eq_of_heq hf
  simp

/-- The functor induced by `r.toSubstitution` maps each coupon `g` to
`FreeRigid.coupon (r.coupon g)`, conjugated by `eqToHom` along the boundary preservation
proofs. -/
theorem toSubstitution_toFunctor_map_coupon (r : Renaming S T) (g : S.Coupon) :
    r.toSubstitution.toFunctor.map (FreeRigid.coupon g) =
      eqToHom ((r.toSubstitution_toFunctor_obj ⟨S.src g⟩).trans
        (congrArg FreeRigid.mk (r.src_eq g).symm)) ≫
        FreeRigid.coupon (r.coupon g) ≫
        eqToHom ((r.toSubstitution_toFunctor_obj ⟨S.tgt g⟩).trans
          (congrArg FreeRigid.mk (r.tgt_eq g).symm)).symm := by
  rw [Substitution.toFunctor_map_coupon, ← FreeRigid.homMk_coupon]
  exact homMk_eq_eqToHom_of_heq
    ((r.toSubstitution_toFunctor_obj ⟨S.src g⟩).trans (congrArg FreeRigid.mk (r.src_eq g).symm))
    ((r.toSubstitution_toFunctor_obj ⟨S.tgt g⟩).trans (congrArg FreeRigid.mk (r.tgt_eq g).symm))
    (r.toSubstitution_coupon_heq g)

@[simp]
theorem toSubstitution_id (S : DualitySignature.{u, v}) :
    (id S).toSubstitution = Substitution.id S :=
  Substitution.hext rfl fun g ↦
    (toSubstitution_coupon_heq _ g).trans (Substitution.id_coupon_heq g).symm

@[simp]
theorem toSubstitution_comp (r : Renaming S T) (s : Renaming T U) :
    (r.comp s).toSubstitution = r.toSubstitution.comp s.toSubstitution := by
  refine Substitution.hext (funext fun _ ↦ rfl) fun g ↦ ?_
  refine (toSubstitution_coupon_heq (r.comp s) g).trans ?_
  refine ((s.toSubstitution_coupon_heq (r.coupon g)).symm).trans ?_
  refine (FreeRigid.Hom.subst_congr_heq s.toSubstitution
    ((r.src_eq g).trans (FreeRigid.as_eval_eq_subst _ _).symm)
    ((r.tgt_eq g).trans (FreeRigid.as_eval_eq_subst _ _).symm)
    (r.toSubstitution_coupon_heq g).symm).trans ?_
  exact (Substitution.comp_coupon_heq r.toSubstitution s.toSubstitution g).symm

end Renaming

namespace Interpretation

open FreeRigid

variable {D : Type u''} [Category.{v''} D] [MonoidalCategory D] [RigidCategory D]

/-- Reindex an interpretation `I` of `T` in a rigid monoidal category `D` along a substitution
`σ : Substitution S T`. Each generating object `a` of `S` is interpreted by evaluating `I` at
`σ.obj a`, and each coupon `g` of `S` is interpreted by lifting `I` to `σ.coupon g`, conjugated by
`eqToHom` along `FreeRigid.eval_eval`. -/
@[expose]
def reindex (I : Interpretation T D) (σ : Substitution S T) : Interpretation S D where
  obj a := RigidObject.eval I.obj (σ.obj a).as
  coupon g :=
    eqToHom (FreeRigid.eval_eval σ.obj I.obj (S.src g)).symm ≫
      (FreeRigid.lift I.obj I.coupon).map (FreeRigid.homMk (σ.coupon g)) ≫
      eqToHom (FreeRigid.eval_eval σ.obj I.obj (S.tgt g))

/-- Reindexing `I` along `σ` evaluates `I` on each substituted object generator `σ.obj a`. -/
@[simp]
theorem reindex_obj (I : Interpretation T D) (σ : Substitution S T) (a : S.Obj) :
    (I.reindex σ).obj a = RigidObject.eval I.obj (σ.obj a).as := (rfl)

/-- Reindexing `I` along `σ` evaluates the lift of `I` on each substituted coupon `σ.coupon g`,
conjugated by `eqToHom` along `FreeRigid.eval_eval`. -/
@[simp]
theorem reindex_coupon (I : Interpretation T D) (σ : Substitution S T) (g : S.Coupon) :
    (I.reindex σ).coupon g =
      eqToHom (FreeRigid.eval_eval σ.obj I.obj (S.src g)).symm ≫
        (FreeRigid.lift I.obj I.coupon).map (FreeRigid.homMk (σ.coupon g)) ≫
        eqToHom (FreeRigid.eval_eval σ.obj I.obj (S.tgt g)) := (rfl)

private theorem comp_lift_mapRightDualIso (I : Interpretation T D) (σ : Substitution S T)
    (X : S.FreeRigid) :
    (σ.toFunctor ⋙ FreeRigid.lift I.obj I.coupon).mapRightDualIso X = Iso.refl _ := by
  ext
  refine (congrArg Iso.hom
    (Functor.mapRightDualIso_comp (FreeRigid.lift I.obj I.coupon) X)).trans ?_
  rw [Iso.trans_hom, FreeRigid.lift_mapRightDualIso, Iso.refl_hom, Functor.mapIso_hom]
  have hhom : (σ.toFunctor.mapRightDualIso X).hom = 𝟙 (σ.toFunctor.obj Xᘁ) := by
    rw [Substitution.toFunctor_mapRightDualIso, Iso.refl_hom]
  have hmap : (FreeRigid.lift I.obj I.coupon).map (σ.toFunctor.mapRightDualIso X).hom =
      𝟙 ((FreeRigid.lift I.obj I.coupon).obj (σ.toFunctor.obj Xᘁ)) :=
    (congrArg (FreeRigid.lift I.obj I.coupon).map hhom).trans (FreeRigid.liftMap_id _ _ _)
  exact (congrArg (· ≫ 𝟙 _) hmap).trans (Category.id_comp _)

private theorem comp_lift_mapLeftDualIso (I : Interpretation T D) (σ : Substitution S T)
    (X : S.FreeRigid) :
    (σ.toFunctor ⋙ FreeRigid.lift I.obj I.coupon).mapLeftDualIso X = Iso.refl _ := by
  ext
  refine ExactPairing.leftDualHom_ext
    (Y := (σ.toFunctor ⋙ FreeRigid.lift I.obj I.coupon).obj X) ?_
  have hμ : Functor.LaxMonoidal.μ (σ.toFunctor ⋙ FreeRigid.lift I.obj I.coupon) X (ᘁX) =
      𝟙 ((FreeRigid.lift I.obj I.coupon).obj (σ.toFunctor.obj X) ⊗
        (FreeRigid.lift I.obj I.coupon).obj (σ.toFunctor.obj (ᘁX))) :=
    ((Functor.LaxMonoidal.comp_μ σ.toFunctor (FreeRigid.lift I.obj I.coupon) X (ᘁX)).trans
      (congrArg₂ (· ≫ ·) (lift_μ _ _ _ _)
        ((congrArg (FreeRigid.lift I.obj I.coupon).map
          (Substitution.toFunctor_μ σ X (ᘁX))).trans (FreeRigid.liftMap_id _ _ _)))).trans
      (Category.id_comp _)
  have hη : Functor.OplaxMonoidal.η (σ.toFunctor ⋙ FreeRigid.lift I.obj I.coupon) = 𝟙 (𝟙_ D) :=
    ((Functor.OplaxMonoidal.comp_η σ.toFunctor (FreeRigid.lift I.obj I.coupon)).trans
      (congrArg₂ (· ≫ ·) (FreeRigid.liftMap_id _ _ _) (lift_η _ _))).trans
      (Category.id_comp _)
  have hε : (FreeRigid.lift I.obj I.coupon).map (σ.toFunctor.map (ε_ (ᘁX : S.FreeRigid) X)) =
      ε_ (ᘁ((FreeRigid.lift I.obj I.coupon).obj (σ.toFunctor.obj X)))
        ((FreeRigid.lift I.obj I.coupon).obj (σ.toFunctor.obj X)) :=
    (congrArg (FreeRigid.lift I.obj I.coupon).map (lift_map_evaluation_leftDual _ _ X)).trans
      (lift_map_evaluation_leftDual _ _ (σ.toFunctor.obj X))
  refine (Functor.whiskerLeft_mapLeftDualIso_hom_evaluation X).trans ?_
  refine (congrArg₂ (· ≫ ·) hμ (congrArg₂ (· ≫ ·) hε hη)).trans ?_
  exact ((Category.id_comp _).trans (Category.comp_id _)).trans
    ((congrArg (· ≫ _) (MonoidalCategory.whiskerLeft_id _ _)).trans (Category.id_comp _)).symm

private theorem comp_lift_obj_eq (I : Interpretation T D) (σ : Substitution S T)
    (X : RigidObject S.Obj) :
    (σ.toFunctor ⋙ FreeRigid.lift I.obj I.coupon).obj ⟨X⟩ =
      RigidObject.eval (fun a ↦ (σ.toFunctor ⋙ FreeRigid.lift I.obj I.coupon).obj (of a)) X :=
  FreeRigid.eval_eval σ.obj I.obj X

private theorem mapWordIso_comp_lift (I : Interpretation T D) (σ : Substitution S T)
    (X : RigidObject S.Obj) :
    mapWordIso (σ.toFunctor ⋙ FreeRigid.lift I.obj I.coupon) X =
      eqToIso (comp_lift_obj_eq I σ X) := by
  induction X with
  | of a =>
    ext
    rw [mapWordIso_of, Iso.refl_hom, eqToIso.hom]
    exact (eqToHom_refl _ _).symm
  | unit =>
    ext
    rw [mapWordIso_unit_hom, Functor.OplaxMonoidal.comp_η, lift_η, eqToIso.hom]
    -- `η σ.toFunctor` is `𝟙 (𝟙_ T.FreeRigid)`, whose endpoints agree definitionally with
    -- `σ.toFunctor.obj (𝟙_ S.FreeRigid)`.
    have hη : (FreeRigid.lift I.obj I.coupon).map (Functor.OplaxMonoidal.η σ.toFunctor) =
        𝟙 (𝟙_ D) :=
      FreeRigid.liftMap_id _ _ (𝟙_ T.FreeRigid)
    exact (congrArg (· ≫ 𝟙 (𝟙_ D)) hη).trans
      ((Category.id_comp _).trans (eqToHom_refl (𝟙_ D) _).symm)
  | tensor X Y ihX ihY =>
    ext
    rw [mapWordIso_tensor_hom, Functor.OplaxMonoidal.comp_δ, lift_δ, ihX, ihY, eqToIso.hom,
      eqToIso.hom, eqToIso.hom, eqToHom_tensorHom_eqToHom]
    -- `δ σ.toFunctor ⟨X⟩ ⟨Y⟩` is `𝟙 _`, whose endpoints agree definitionally after unfolding
    -- `lift`.
    have hδ : (FreeRigid.lift I.obj I.coupon).map
          (Functor.OplaxMonoidal.δ σ.toFunctor ⟨X⟩ ⟨Y⟩) =
        𝟙 (RigidObject.eval I.obj (RigidObject.eval σ.obj X).as ⊗
          RigidObject.eval I.obj (RigidObject.eval σ.obj Y).as) :=
      FreeRigid.liftMap_id _ _ _
    refine (congrArg (fun f ↦ (f ≫ 𝟙 _) ≫ _) hδ).trans ?_
    exact (congrArg (· ≫ _) (Category.id_comp _)).trans (Category.id_comp _)
  | rightDual X ih =>
    ext
    rw [mapWordIso_rightDual_hom, comp_lift_mapRightDualIso, ih, Iso.refl_hom, eqToIso.inv,
      rightAdjointMate_eqToHom, eqToIso.hom]
    exact Category.id_comp _
  | leftDual X ih =>
    ext
    rw [mapWordIso_leftDual_hom, comp_lift_mapLeftDualIso, ih, Iso.refl_hom, eqToIso.inv,
      leftAdjointMate_eqToHom, eqToIso.hom]
    exact Category.id_comp _

private def reindexGenIso (I : Interpretation T D) (σ : Substitution S T) (a : S.Obj) :
    (FreeRigid.lift (I.reindex σ).obj (I.reindex σ).coupon).obj (of a) ≅
      (σ.toFunctor ⋙ FreeRigid.lift I.obj I.coupon).obj (of a) :=
  Iso.refl _

private theorem wordIso_lift_comp_lift_hom (I : Interpretation T D) (σ : Substitution S T)
    (X : RigidObject S.Obj) :
    (wordIso (FreeRigid.lift (I.reindex σ).obj (I.reindex σ).coupon)
        (σ.toFunctor ⋙ FreeRigid.lift I.obj I.coupon) (reindexGenIso I σ) X).hom =
      eqToHom (FreeRigid.eval_eval σ.obj I.obj X).symm := by
  have hF :
      (mapWordIso (FreeRigid.lift (I.reindex σ).obj (I.reindex σ).coupon) X).hom =
        𝟙 (RigidObject.eval (I.reindex σ).obj X) := by
    rw [mapWordIso_lift, Iso.refl_hom]
  have hE :
      (RigidObject.evalIso (reindexGenIso I σ) X).hom =
        𝟙 (RigidObject.eval (I.reindex σ).obj X) :=
    congrArg Iso.hom (RigidObject.evalIso_refl X)
  have hG :
      (mapWordIso (σ.toFunctor ⋙ FreeRigid.lift I.obj I.coupon) X).inv =
        eqToHom (comp_lift_obj_eq I σ X).symm := by
    rw [mapWordIso_comp_lift, eqToIso.inv]
  refine (congrArg Iso.hom (wordIso_eq_mapWordIso _ _ (reindexGenIso I σ) X)).trans ?_
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, hG]
  exact (congrArg (fun f ↦ f ≫ (RigidObject.evalIso (reindexGenIso I σ) X).hom ≫
      eqToHom (comp_lift_obj_eq I σ X).symm) hF).trans
    ((Category.id_comp _).trans ((congrArg (· ≫ _) hE).trans (Category.id_comp _)))

private theorem extension_reindex_coupon_comm (I : Interpretation T D) (σ : Substitution S T)
    (g : S.Coupon) :
    (FreeRigid.lift (I.reindex σ).obj (I.reindex σ).coupon).map (FreeRigid.coupon g) ≫
        (wordIso (FreeRigid.lift (I.reindex σ).obj (I.reindex σ).coupon)
          (σ.toFunctor ⋙ FreeRigid.lift I.obj I.coupon) (reindexGenIso I σ) (S.tgt g)).hom =
      (wordIso (FreeRigid.lift (I.reindex σ).obj (I.reindex σ).coupon)
          (σ.toFunctor ⋙ FreeRigid.lift I.obj I.coupon) (reindexGenIso I σ) (S.src g)).hom ≫
        (σ.toFunctor ⋙ FreeRigid.lift I.obj I.coupon).map (FreeRigid.coupon g) := by
  have hleft :
      (FreeRigid.lift (I.reindex σ).obj (I.reindex σ).coupon).map (FreeRigid.coupon g) =
        eqToHom (FreeRigid.eval_eval σ.obj I.obj (S.src g)).symm ≫
          (FreeRigid.lift I.obj I.coupon).map (FreeRigid.homMk (σ.coupon g)) ≫
          eqToHom (FreeRigid.eval_eval σ.obj I.obj (S.tgt g)) :=
    (lift_map_coupon _ _ g).trans (reindex_coupon I σ g)
  have hright :
      (σ.toFunctor ⋙ FreeRigid.lift I.obj I.coupon).map (FreeRigid.coupon g) =
        (FreeRigid.lift I.obj I.coupon).map (FreeRigid.homMk (σ.coupon g)) :=
    congrArg (FreeRigid.lift I.obj I.coupon).map (Substitution.toFunctor_map_coupon σ g)
  have hmid :
      (eqToHom (FreeRigid.eval_eval σ.obj I.obj (S.src g)).symm ≫
            (FreeRigid.lift I.obj I.coupon).map (FreeRigid.homMk (σ.coupon g)) ≫
            eqToHom (FreeRigid.eval_eval σ.obj I.obj (S.tgt g))) ≫
          eqToHom (FreeRigid.eval_eval σ.obj I.obj (S.tgt g)).symm =
        eqToHom (FreeRigid.eval_eval σ.obj I.obj (S.src g)).symm ≫
          (FreeRigid.lift I.obj I.coupon).map (FreeRigid.homMk (σ.coupon g)) := by
    refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
    exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).trans
        (Category.comp_id _))
  exact (congrArg₂ (· ≫ ·) hleft (wordIso_lift_comp_lift_hom I σ (S.tgt g))).trans
    (hmid.trans (congrArg₂ (· ≫ ·) (wordIso_lift_comp_lift_hom I σ (S.src g)).symm hright.symm))

/-- The monoidal natural isomorphism comparing the extension of `I.reindex σ` with precomposition
of the extension of `I` by `σ.toFunctor`. -/
noncomputable def extensionReindexIso (I : Interpretation T D) (σ : Substitution S T) :
    ((extension S D).obj (I.reindex σ)).of ≅
      MonoidalFunctor.of (σ.toFunctor ⋙ ((extension T D).obj I).of.toFunctor) :=
  @MonoidalFunctor.isoMk _ _ _ _ _ _ (.of _) (MonoidalFunctor.of _)
    (monoidalNatIso (extension_reindex_coupon_comm I σ))
    (isMonoidal_monoidalNatIso_hom (extension_reindex_coupon_comm I σ))

/-- The forward component of `extensionReindexIso I σ` at any object `X` is the endpoint
identification `eqToHom (FreeRigid.eval_eval σ.obj I.obj X.as).symm`. -/
theorem extensionReindexIso_hom_hom_hom_app (I : Interpretation T D) (σ : Substitution S T)
    (X : S.FreeRigid) :
    (extensionReindexIso I σ).hom.hom.hom.app X =
      eqToHom (FreeRigid.eval_eval σ.obj I.obj X.as).symm := by
  -- As in `Interpretation.extension`, monoidality is supplied explicitly to
  -- `MonoidalFunctor.isoMk`, so `change` exposes the underlying component of `monoidalNatIso`.
  change (monoidalNatIso (extension_reindex_coupon_comm I σ)).hom.app X = _
  rw [monoidalNatIso_hom_app, wordIso_lift_comp_lift_hom]

/-- The inverse component of `extensionReindexIso I σ` at any object `X` is the endpoint
identification `eqToHom (FreeRigid.eval_eval σ.obj I.obj X.as)`. -/
theorem extensionReindexIso_inv_hom_hom_app (I : Interpretation T D) (σ : Substitution S T)
    (X : S.FreeRigid) :
    (extensionReindexIso I σ).inv.hom.hom.app X =
      eqToHom (FreeRigid.eval_eval σ.obj I.obj X.as) := by
  rw [← MonoidalFunctor.toFunctorIso_inv, ← Iso.app_inv,
    ← eqToIso.inv (FreeRigid.eval_eval σ.obj I.obj X.as).symm]
  exact congrArg Iso.inv (Iso.ext (extensionReindexIso_hom_hom_hom_app I σ X))

/-- At a generating object `of a`, the forward component of `extensionReindexIso I σ` is the
identity. -/
@[simp]
theorem extensionReindexIso_hom_hom_hom_app_of (I : Interpretation T D) (σ : Substitution S T)
    (a : S.Obj) :
    (extensionReindexIso I σ).hom.hom.hom.app (of a) =
      𝟙 (RigidObject.eval I.obj (σ.obj a).as) :=
  (extensionReindexIso_hom_hom_hom_app I σ (of a)).trans (eqToHom_refl _ _)

/-- At a generating object `of a`, the inverse component of `extensionReindexIso I σ` is the
identity. -/
@[simp]
theorem extensionReindexIso_inv_hom_hom_app_of (I : Interpretation T D) (σ : Substitution S T)
    (a : S.Obj) :
    (extensionReindexIso I σ).inv.hom.hom.app (of a) =
      𝟙 (RigidObject.eval I.obj (σ.obj a).as) :=
  (extensionReindexIso_inv_hom_hom_app I σ (of a)).trans (eqToHom_refl _ _)

/-- Reindexing an interpretation along the identity substitution leaves it unchanged. -/
@[simp]
theorem reindex_id (I : Interpretation T D) : I.reindex (Substitution.id T) = I := by
  obtain ⟨obj, coupon⟩ := I
  dsimp only [reindex]
  congr 1
  funext g
  refine eq_of_heq ((CategoryTheory.eqToHom_comp_heq _ _).trans
    ((CategoryTheory.comp_eqToHom_heq _ _).trans ?_))
  have hmk : FreeRigid.homMk ((Substitution.id T).coupon g) ≍ FreeRigid.coupon g := by
    rw [← FreeRigid.homMk_coupon]
    exact homMk_heq (congrArg FreeRigid.as (FreeRigid.eval_of (T.src g)))
      (congrArg FreeRigid.as (FreeRigid.eval_of (T.tgt g))) (Substitution.id_coupon_heq g)
  exact (Functor.map_heq (FreeRigid.lift obj coupon)
    (FreeRigid.eval_of (T.src g)) (FreeRigid.eval_of (T.tgt g)) hmk).trans
    (FreeRigid.lift_map_coupon obj coupon g).heq

/-- Reindexing along a composite substitution agrees with iterated reindexing in contravariant
order. -/
theorem reindex_comp (I : Interpretation U D) (σ : Substitution S T) (τ : Substitution T U) :
    I.reindex (σ.comp τ) = (I.reindex τ).reindex σ := by
  have hext : ∀ {x y : Interpretation S D}, x.obj = y.obj → x.coupon ≍ y.coupon → x = y := by
    rintro ⟨obj₁, c₁⟩ ⟨obj₂, c₂⟩ h1 h2
    dsimp at h1 h2
    subst h1
    exact congrArg _ (eq_of_heq h2)
  refine hext (funext fun a ↦ FreeRigid.eval_eval τ.obj I.obj (σ.obj a).as) ?_
  refine Function.hfunext rfl fun g _ hg ↦ ?_
  cases hg
  rw [reindex_coupon, reindex_coupon]
  refine (CategoryTheory.eqToHom_comp_heq _ _).trans
    ((CategoryTheory.comp_eqToHom_heq _ _).trans ?_)
  refine ((CategoryTheory.eqToHom_comp_heq _ _).trans
    ((CategoryTheory.comp_eqToHom_heq _ _).trans ?_)).symm
  have hmk : FreeRigid.homMk ((σ.comp τ).coupon g) ≍
      τ.toFunctor.map (FreeRigid.homMk (σ.coupon g)) := by
    rw [τ.toFunctor_map_homMk]
    exact homMk_heq (congrArg FreeRigid.as (FreeRigid.eval_eval σ.obj τ.obj (S.src g)).symm)
      (congrArg FreeRigid.as (FreeRigid.eval_eval σ.obj τ.obj (S.tgt g)).symm)
      (Substitution.comp_coupon_heq σ τ g)
  have hmap :
      (FreeRigid.lift I.obj I.coupon).map (FreeRigid.homMk ((σ.comp τ).coupon g)) ≍
        (τ.toFunctor ⋙ FreeRigid.lift I.obj I.coupon).map (FreeRigid.homMk (σ.coupon g)) :=
    Functor.map_heq (FreeRigid.lift I.obj I.coupon)
      (FreeRigid.eval_eval σ.obj τ.obj (S.src g)).symm
      (FreeRigid.eval_eval σ.obj τ.obj (S.tgt g)).symm hmk
  have hcomm := (extensionReindexIso I τ).hom.hom.hom.naturality (FreeRigid.homMk (σ.coupon g))
  rw [extensionReindexIso_hom_hom_hom_app, extensionReindexIso_hom_hom_hom_app] at hcomm
  have hnat :
      (FreeRigid.lift (I.reindex τ).obj (I.reindex τ).coupon).map (FreeRigid.homMk (σ.coupon g)) ≍
        (τ.toFunctor ⋙ FreeRigid.lift I.obj I.coupon).map (FreeRigid.homMk (σ.coupon g)) :=
    (CategoryTheory.comp_eqToHom_heq _ _).symm.trans
      (hcomm.heq.trans (CategoryTheory.eqToHom_comp_heq _ _))
  exact hnat.trans hmap.symm

/-- Iterated reindexing collapses to reindexing along the composite substitution. -/
@[simp]
theorem reindex_reindex (I : Interpretation U D) (σ : Substitution S T) (τ : Substitution T U) :
    (I.reindex τ).reindex σ = I.reindex (σ.comp τ) :=
  (reindex_comp I σ τ).symm

end Interpretation

end TauCeti.DualitySignature
