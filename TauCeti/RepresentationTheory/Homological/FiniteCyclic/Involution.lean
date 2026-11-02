/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Cyclic.Automorphism
public import Mathlib.RepresentationTheory.Homological.FiniteCyclic

/-!
# The periodic short complexes of an involution

For an additive involution `A`, the norm of its cyclic representation is `1 + A`.
Mathlib's periodic short complexes use the other differential `A - 1`. We identify
their maps and give isomorphisms to the convention with differential `1 - A` by
negating one end of each short complex. Both composites of `1 + A` and `1 - A`
vanish. The difference differential is also identified for arbitrary finite order.

The shared complexes are `Rep.FiniteCyclicGroup.normHomCompSub` and
`Rep.FiniteCyclicGroup.subCompNormHom` from Mathlib's finite-cyclic resolution.
These comparisons require only an additive commutative group, so they also apply
in the presence of two-torsion; no division by two is involved.
-/

public section

open CategoryTheory Rep Rep.FiniteCyclicGroup

namespace AddEquiv

variable {T : Type*} [AddCommGroup T] (A : T ≃+ T)

section FiniteOrder

variable {m : ℕ} [NeZero m] (hA : (⇑A)^[m] = id)

/-- Mathlib's difference differential is the negative of the convention `1 - A`,
for an automorphism of any finite order. -/
theorem normHomCompSub_cyclicRep_g :
    (normHomCompSub (A.cyclicRep hA) (.ofAdd 1)).g =
      -(𝟙 (ModuleCat.of ℤ T) - ModuleCat.ofHom A.toIntLinearEquiv.toLinearMap) := by
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun x ↦ ?_
  dsimp only [normHomCompSub, ModuleCat.hom_ofHom]
  rw [A.cyclicRep_applyAsHom_sub_apply hA]
  simp

/-- The first map in the other periodic short complex is likewise `-(1 - A)`,
for an automorphism of any finite order. -/
theorem subCompNormHom_cyclicRep_f :
    (subCompNormHom (A.cyclicRep hA) (.ofAdd 1)).f =
      -(𝟙 (ModuleCat.of ℤ T) - ModuleCat.ofHom A.toIntLinearEquiv.toLinearMap) :=
  -- Both arrows are definitionally the underlying map of `ρ(g) - 𝟙`.
  A.normHomCompSub_cyclicRep_g hA

end FiniteOrder

variable (hA : (⇑A)^[2] = id)

/-- The norm differential for the cyclic representation of an involution is `1 + A`. -/
theorem normHomCompSub_cyclicRep_two_f :
    (normHomCompSub (A.cyclicRep hA) (.ofAdd 1)).f =
      𝟙 (ModuleCat.of ℤ T) + ModuleCat.ofHom A.toIntLinearEquiv.toLinearMap := by
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun x ↦ ?_
  dsimp only [normHomCompSub, ModuleCat.hom_ofHom]
  rw [cyclicRep_norm_apply]
  simp [Finset.sum_range_succ]

/-- The second map in the other periodic short complex is `1 + A`. -/
theorem subCompNormHom_cyclicRep_two_g :
    (subCompNormHom (A.cyclicRep hA) (.ofAdd 1)).g =
      𝟙 (ModuleCat.of ℤ T) + ModuleCat.ofHom A.toIntLinearEquiv.toLinearMap :=
  -- Both arrows are definitionally the underlying norm map.
  A.normHomCompSub_cyclicRep_two_f hA

include hA in
/-- For an involution, the composite of `1 + A` followed by `1 - A` vanishes. -/
theorem one_add_comp_one_sub_eq_zero :
    (𝟙 (ModuleCat.of ℤ T) + ModuleCat.ofHom A.toIntLinearEquiv.toLinearMap) ≫
      (𝟙 (ModuleCat.of ℤ T) - ModuleCat.ofHom A.toIntLinearEquiv.toLinearMap) = 0 := by
  have hz := (normHomCompSub (A.cyclicRep hA) (.ofAdd 1)).zero
  rwa [A.normHomCompSub_cyclicRep_two_f hA, A.normHomCompSub_cyclicRep_g hA,
    Preadditive.comp_neg, neg_eq_zero] at hz

include hA in
/-- For an involution, the composite of `1 - A` followed by `1 + A` vanishes. -/
theorem one_sub_comp_one_add_eq_zero :
    (𝟙 (ModuleCat.of ℤ T) - ModuleCat.ofHom A.toIntLinearEquiv.toLinearMap) ≫
      (𝟙 (ModuleCat.of ℤ T) + ModuleCat.ofHom A.toIntLinearEquiv.toLinearMap) = 0 := by
  have hz := (subCompNormHom (A.cyclicRep hA) (.ofAdd 1)).zero
  rwa [A.subCompNormHom_cyclicRep_f hA, A.subCompNormHom_cyclicRep_two_g hA,
    Preadditive.neg_comp, neg_eq_zero] at hz

/-- Negating the last object changes the periodic short complex `1 + A, A - 1`
to the convention `1 + A, 1 - A`. Its zero-composite law is inherited from
Mathlib's short complex. -/
noncomputable def normHomCompSubCyclicRepTwoIso :
    normHomCompSub (A.cyclicRep hA) (.ofAdd 1) ≅
      ShortComplex.mk
        (𝟙 (ModuleCat.of ℤ T) + ModuleCat.ofHom A.toIntLinearEquiv.toLinearMap)
        (𝟙 (ModuleCat.of ℤ T) - ModuleCat.ofHom A.toIntLinearEquiv.toLinearMap)
        (A.one_add_comp_one_sub_eq_zero hA) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (-(Iso.refl _))
    (by simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id] using
      (A.normHomCompSub_cyclicRep_two_f hA).symm)
    (by simpa only [Iso.refl_hom, Preadditive.neg_iso_hom, Category.id_comp,
        Preadditive.comp_neg, Category.comp_id, neg_neg] using
      congrArg Neg.neg (A.normHomCompSub_cyclicRep_g hA).symm)

/-- Negating the first object changes the periodic short complex `A - 1, 1 + A`
to the convention `1 - A, 1 + A`, retaining Mathlib's shared source complex. -/
noncomputable def subCompNormHomCyclicRepTwoIso :
    subCompNormHom (A.cyclicRep hA) (.ofAdd 1) ≅
      ShortComplex.mk
        (𝟙 (ModuleCat.of ℤ T) - ModuleCat.ofHom A.toIntLinearEquiv.toLinearMap)
        (𝟙 (ModuleCat.of ℤ T) + ModuleCat.ofHom A.toIntLinearEquiv.toLinearMap)
        (A.one_sub_comp_one_add_eq_zero hA) :=
  ShortComplex.isoMk (-(Iso.refl _)) (Iso.refl _) (Iso.refl _)
    (by simpa only [Preadditive.neg_iso_hom, Iso.refl_hom, Preadditive.neg_comp,
        Category.id_comp, Category.comp_id] using
      (A.subCompNormHom_cyclicRep_f hA).symm)
    (by simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id] using
      (A.subCompNormHom_cyclicRep_two_g hA).symm)

@[simp]
theorem normHomCompSubCyclicRepTwoIso_hom_τ₁ :
    (A.normHomCompSubCyclicRepTwoIso hA).hom.τ₁ = 𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem normHomCompSubCyclicRepTwoIso_hom_τ₂ :
    (A.normHomCompSubCyclicRepTwoIso hA).hom.τ₂ = 𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem normHomCompSubCyclicRepTwoIso_hom_τ₃ :
    (A.normHomCompSubCyclicRepTwoIso hA).hom.τ₃ = -𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem normHomCompSubCyclicRepTwoIso_inv_τ₁ :
    (A.normHomCompSubCyclicRepTwoIso hA).inv.τ₁ = 𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem normHomCompSubCyclicRepTwoIso_inv_τ₂ :
    (A.normHomCompSubCyclicRepTwoIso hA).inv.τ₂ = 𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem normHomCompSubCyclicRepTwoIso_inv_τ₃ :
    (A.normHomCompSubCyclicRepTwoIso hA).inv.τ₃ = -𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem subCompNormHomCyclicRepTwoIso_hom_τ₁ :
    (A.subCompNormHomCyclicRepTwoIso hA).hom.τ₁ = -𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem subCompNormHomCyclicRepTwoIso_hom_τ₂ :
    (A.subCompNormHomCyclicRepTwoIso hA).hom.τ₂ = 𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem subCompNormHomCyclicRepTwoIso_hom_τ₃ :
    (A.subCompNormHomCyclicRepTwoIso hA).hom.τ₃ = 𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem subCompNormHomCyclicRepTwoIso_inv_τ₁ :
    (A.subCompNormHomCyclicRepTwoIso hA).inv.τ₁ = -𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem subCompNormHomCyclicRepTwoIso_inv_τ₂ :
    (A.subCompNormHomCyclicRepTwoIso hA).inv.τ₂ = 𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem subCompNormHomCyclicRepTwoIso_inv_τ₃ :
    (A.subCompNormHomCyclicRepTwoIso hA).inv.τ₃ = 𝟙 (ModuleCat.of ℤ T) := (rfl)

end AddEquiv
