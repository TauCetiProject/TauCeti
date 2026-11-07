/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import TauCeti.LinearAlgebra.Complex.Conjugation

/-!
# Real descent for complex modules with conjugation

`TauCeti.ConjugateModuleCat` is the category of complex modules with a conjugate-linear
involution and complex-linear maps commuting with it. A native complex star module gives
an object of this category. No Hermitian pairing or finite-dimensionality is required.

Complexification and taking fixed points are quasi-inverse functors forming an equivalence
between this category and real modules. The counit is the canonical scalar multiplication map
`z ⊗ w ↦ z • w` supplied by `TauCeti.realPointsEquiv`; the unit is `w ↦ 1 ⊗ w`.
This makes descent natural in the module.

The fixed-point decomposition follows Serre, *Linear Representations of Finite Groups*,
§13.2. The linear equivalence and tensor conjugation are imported from
`TauCeti.LinearAlgebra.Complex.Conjugation`.

## Implementation notes

The functor abbreviations keep the subtype and tensor carriers available to dependent
constructions. The equivalence body is exposed so the dependent types of its unit and
counit compute to these functors.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace TauCeti

/-- Complex modules equipped with a conjugate-linear involution. -/
structure ConjugateModuleCat where
  /-- The underlying complex module. -/
  toModuleCat : ModuleCat.{u} ℂ
  /-- The conjugate-linear map defining the real structure. -/
  conj : toModuleCat →ₛₗ[starRingEnd ℂ] toModuleCat
  /-- Applying conjugation twice is the identity. -/
  involutive : Function.Involutive conj

namespace ConjugateModuleCat

instance : CoeSort ConjugateModuleCat.{u} (Type u) := ⟨fun V => V.toModuleCat⟩

instance (V : ConjugateModuleCat) : AddCommGroup V := V.toModuleCat.isAddCommGroup
instance (V : ConjugateModuleCat) : Module ℂ V := V.toModuleCat.isModule

/-- A native complex star module, regarded as a module with conjugation. -/
abbrev of (V : Type u) [AddCommGroup V] [Module ℂ V] [StarAddMonoid V]
    [StarModule ℂ V] : ConjugateModuleCat.{u} :=
  ⟨ModuleCat.of ℂ V, (starLinearEquiv ℂ (A := V)).toLinearMap, star_star⟩

/-- Complex-linear maps preserving the chosen conjugations. -/
@[ext]
structure Hom (V W : ConjugateModuleCat.{u}) where
  /-- The underlying complex-linear map. -/
  hom : V →ₗ[ℂ] W
  /-- Compatibility with conjugation. -/
  commutes : ∀ x, hom (V.conj x) = W.conj (hom x)

attribute [simp] Hom.commutes

instance : Category ConjugateModuleCat.{u} where
  Hom := Hom
  id V := ⟨LinearMap.id, fun _ => rfl⟩
  comp f g := ⟨g.hom.comp f.hom, fun x => by simp⟩

@[ext]
theorem hom_ext {V W : ConjugateModuleCat} {f g : V ⟶ W}
    (h : ∀ x, f.hom x = g.hom x) : f = g :=
  Hom.ext (LinearMap.ext h)

@[simp]
theorem hom_id (V : ConjugateModuleCat) : (𝟙 V : V ⟶ V).hom = LinearMap.id := (rfl)

@[simp]
theorem hom_comp {V W Z : ConjugateModuleCat} (f : V ⟶ W) (g : W ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := (rfl)

/-- A complex-linear equivalence preserving conjugation gives an isomorphism. -/
noncomputable def isoMk {V W : ConjugateModuleCat.{u}} (e : V ≃ₗ[ℂ] W)
    (he : ∀ x, e (V.conj x) = W.conj (e x)) : V ≅ W where
  hom := ⟨e.toLinearMap, he⟩
  inv := ⟨e.symm.toLinearMap,
    Function.Semiconj.inverse_left he e.symm_apply_apply e.apply_symm_apply⟩
  hom_inv_id := by ext x; exact e.symm_apply_apply x
  inv_hom_id := by ext x; exact e.apply_symm_apply x

@[simp]
theorem isoMk_hom_hom {V W : ConjugateModuleCat.{u}} (e : V ≃ₗ[ℂ] W)
    (he : ∀ x, e (V.conj x) = W.conj (e x)) :
    (isoMk e he).hom.hom = e.toLinearMap := (rfl)

@[simp]
theorem isoMk_inv_hom {V W : ConjugateModuleCat.{u}} (e : V ≃ₗ[ℂ] W)
    (he : ∀ x, e (V.conj x) = W.conj (e x)) :
    (isoMk e he).inv.hom = e.symm.toLinearMap := (rfl)

/-- The fixed-point functor, acting on morphisms by restriction. -/
noncomputable abbrev fixedPoints : ConjugateModuleCat.{u} ⥤ ModuleCat.{u} ℝ where
  obj V := ModuleCat.of ℝ (realPoints V.conj)
  map f := ModuleCat.ofHom ((f.hom.restrictScalars ℝ).restrict
    (p := realPoints _) (q := realPoints _) fun x hx => mem_realPoints.mpr (by
      rw [LinearMap.coe_restrictScalars, ← f.commutes, mem_realPoints.mp hx]))

/-- Complexification with tensor conjugation, lifting scalar extension on real modules. -/
noncomputable abbrev complexification : ModuleCat.{u} ℝ ⥤ ConjugateModuleCat.{u} where
  obj W := ⟨ModuleCat.of ℂ (ℂ ⊗[ℝ] W), tmulConj W, tmulConj_involutive W⟩
  map f := ⟨f.hom.baseChange ℂ, fun x => (tmulConj_baseChange f.hom x).symm⟩
  map_id W := by apply Hom.ext; exact LinearMap.baseChange_id
  map_comp f g := by apply Hom.ext; exact LinearMap.baseChange_comp f.hom g.hom

@[simp]
theorem complexification_conj (W : ModuleCat.{u} ℝ) :
    (complexification.obj W).conj = tmulConj W := (rfl)

@[simp]
theorem complexification_map_hom {V W : ModuleCat.{u} ℝ} (f : V ⟶ W) :
    (complexification.map f).hom = f.hom.baseChange ℂ := (rfl)

/-- The unit of real descent: a real vector is the fixed tensor `1 ⊗ w`.
Its inverse reads the real tensor coordinate. -/
noncomputable def descentUnit : 𝟭 (ModuleCat.{u} ℝ) ≅ complexification ⋙ fixedPoints :=
  NatIso.ofComponents (fun W => LinearEquiv.toModuleIso
    { toFun := fun w => ⟨1 ⊗ₜ[ℝ] w, by simp⟩
      map_add' v w := by ext; exact TensorProduct.tmul_add _ v w
      map_smul' r w := by ext; exact TensorProduct.tmul_smul r (1 : ℂ) w
      invFun := fun x => realPart W x.val
      left_inv := realPart_one_tmul W
      right_inv x := by
        apply Subtype.ext
        obtain ⟨w, hw⟩ := (tmulConj_eq_self_iff W x.val).mp (mem_realPoints.mp x.property)
        simp [hw] }) (by intros; ext w; apply Subtype.ext; simp [LinearMap.baseChange_tmul])

@[simp]
theorem descentUnit_hom_apply (W : ModuleCat.{u} ℝ) (w : W) :
    dsimp% (descentUnit.hom.app W w).val = 1 ⊗ₜ[ℝ] w := (rfl)

@[simp]
theorem descentUnit_inv_apply (W : ModuleCat.{u} ℝ)
    (x : fixedPoints.obj (complexification.obj W)) :
    dsimp% descentUnit.inv.app W x = realPart W x.val := (rfl)

/-- The counit of real descent is scalar multiplication, with inverse given by the
fixed-point real/imaginary decomposition. -/
noncomputable def descentCounit : fixedPoints ⋙ complexification ≅ 𝟭 ConjugateModuleCat.{u} :=
  NatIso.ofComponents (fun V => isoMk (realPointsEquiv V.involutive)
    (realPointsEquiv_tmulConj V.involutive)) (by
      intro V W f
      apply Hom.ext
      apply TensorProduct.AlgebraTensorModule.ext
      intro z w
      simp [LinearMap.baseChange_tmul])

@[simp]
theorem descentCounit_hom_tmul (V : ConjugateModuleCat)
    (z : ℂ) (w : fixedPoints.obj V) :
    dsimp% (descentCounit.hom.app V).hom (z ⊗ₜ[ℝ] w) = z • w.val :=
  realPointsEquiv_tmul V.involutive z w

/-- The inverse counit is the supplied inverse real-descent map. -/
@[simp]
theorem descentCounit_inv_hom (V : ConjugateModuleCat) :
    (descentCounit.inv.app V).hom = (realPointsEquiv V.involutive).symm.toLinearMap := (rfl)

/-- Real modules are equivalent to complex modules with conjugation. Both functors and the
unit and counit are the canonical tensor and fixed-point constructions. -/
@[expose] noncomputable def realDescentEquivalence : ModuleCat.{u} ℝ ≌ ConjugateModuleCat.{u} where
  functor := complexification
  inverse := fixedPoints
  unitIso := descentUnit
  counitIso := descentCounit
  functor_unitIso_comp W := by
    apply Hom.ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro z w
    -- Normalize the composition and base-change wrappers without unfolding the object carrier:
    -- unrestricted simp unfolds complexification, preventing the counit formula from matching.
    change (descentCounit.hom.app (complexification.obj W)).hom
      (z ⊗ₜ[ℝ] (descentUnit.hom.app W).hom w) = z ⊗ₜ[ℝ] w
    rw [descentCounit_hom_tmul, descentUnit_hom_apply W w]
    simp [TensorProduct.smul_tmul']

@[simp]
theorem realDescentEquivalence_functor : realDescentEquivalence.functor = complexification := (rfl)

@[simp]
theorem realDescentEquivalence_inverse : realDescentEquivalence.inverse = fixedPoints := (rfl)

@[simp]
theorem realDescentEquivalence_unitIso : realDescentEquivalence.unitIso = descentUnit := (rfl)

@[simp]
theorem realDescentEquivalence_counitIso : realDescentEquivalence.counitIso = descentCounit := (rfl)

end ConjugateModuleCat

end TauCeti
