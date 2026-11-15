/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Int
public import TauCeti.RepresentationTheory.Cyclic.Affine
public import Mathlib.RepresentationTheory.Homological.FiniteCyclic

/-!
# The periodic short complexes of a finite-order automorphism

For an additive automorphism `A` of period dividing `m`, Mathlib's periodic short
complexes have differentials `cyclicNormHom m` and `-oneSubPow 1`. We identify
their maps and give isomorphisms to the convention with differential `1 - A` by
negating one end of each short complex. The target short complexes use the
zero-composite laws `AddEquiv.oneSubPow_comp_cyclicNormHom` and
`AddEquiv.cyclicNormHom_comp_oneSubPow` from
`TauCeti.RepresentationTheory.Cyclic.Affine`.

The shared complexes are `Rep.FiniteCyclicGroup.normHomCompSub` and
`Rep.FiniteCyclicGroup.subCompNormHom` from Mathlib's finite-cyclic resolution.
These comparisons require only an additive commutative group, so they also apply
in the presence of two-torsion; no division by two is involved.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter VI, §2, for the periodic cyclic resolution.
-/

public section

open CategoryTheory Rep Rep.FiniteCyclicGroup

namespace AddEquiv

variable {T : Type*} [AddCommGroup T] (A : T ≃+ T)

section FiniteOrder

variable {m : ℕ} [NeZero m] (hA : (⇑A)^[m] = id)

/-- The norm differential is the bundled partial norm for an automorphism of finite order. -/
theorem normHomCompSub_cyclicRep_f :
    (normHomCompSub (A.cyclicRep hA) (.ofAdd 1)).f =
      ModuleCat.ofHom (A.cyclicNormHom m).toIntLinearMap := by
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun x ↦ ?_
  dsimp only [normHomCompSub, ModuleCat.hom_ofHom, AddMonoidHom.coe_toIntLinearMap]
  rw [cyclicNormHom_apply, partialNorm_def]
  exact A.cyclicRep_norm_apply hA x

/-- Mathlib's difference differential is the negative of the convention `1 - A`,
for an automorphism of any finite order. -/
theorem normHomCompSub_cyclicRep_g :
    (normHomCompSub (A.cyclicRep hA) (.ofAdd 1)).g =
      -ModuleCat.ofHom (A.oneSubPow 1).toIntLinearMap := by
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun x ↦ ?_
  dsimp only [normHomCompSub, ModuleCat.hom_neg, ModuleCat.hom_ofHom,
    LinearMap.neg_apply, AddMonoidHom.coe_toIntLinearMap]
  rw [A.cyclicRep_applyAsHom_sub_apply hA]
  simp

/-- The first map in the other periodic short complex is likewise `-(1 - A)`,
for an automorphism of any finite order. -/
theorem subCompNormHom_cyclicRep_f :
    (subCompNormHom (A.cyclicRep hA) (.ofAdd 1)).f =
      -ModuleCat.ofHom (A.oneSubPow 1).toIntLinearMap :=
  -- Both arrows are definitionally the underlying map of ρ(g) - 𝟙.
  A.normHomCompSub_cyclicRep_g hA

/-- The second map in the other periodic short complex is the bundled partial norm. -/
theorem subCompNormHom_cyclicRep_g :
    (subCompNormHom (A.cyclicRep hA) (.ofAdd 1)).g =
      ModuleCat.ofHom (A.cyclicNormHom m).toIntLinearMap :=
  -- Both arrows are definitionally the underlying norm map.
  A.normHomCompSub_cyclicRep_f hA

end FiniteOrder

variable {m : ℕ} [NeZero m] (hA : (⇑A)^[m] = id)

/-- Negating the last object changes the periodic short complex `N_A, A - 1`
to the convention `N_A, 1 - A`, where `N_A = cyclicNormHom m`. -/
noncomputable def normHomCompSubCyclicRepIso :
    normHomCompSub (A.cyclicRep hA) (.ofAdd 1) ≅
      ShortComplex.mk
        (ModuleCat.ofHom (A.cyclicNormHom m).toIntLinearMap)
        (ModuleCat.ofHom (A.oneSubPow 1).toIntLinearMap)
        ((AddMonoidHom.ofHom_toIntLinearMap_comp_eq_zero_iff _ _).mpr
          (A.oneSubPow_comp_cyclicNormHom hA)) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (-(Iso.refl _))
    (by simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id] using
      (A.normHomCompSub_cyclicRep_f hA).symm)
    (by simpa only [Iso.refl_hom, Preadditive.neg_iso_hom, Category.id_comp,
        Preadditive.comp_neg, Category.comp_id, neg_neg] using
      congrArg Neg.neg (A.normHomCompSub_cyclicRep_g hA).symm)

/-- Negating the first object changes the periodic short complex `A - 1, N_A`
to the convention `1 - A, N_A`, where `N_A = cyclicNormHom m`. -/
noncomputable def subCompNormHomCyclicRepIso :
    subCompNormHom (A.cyclicRep hA) (.ofAdd 1) ≅
      ShortComplex.mk
        (ModuleCat.ofHom (A.oneSubPow 1).toIntLinearMap)
        (ModuleCat.ofHom (A.cyclicNormHom m).toIntLinearMap)
        ((AddMonoidHom.ofHom_toIntLinearMap_comp_eq_zero_iff _ _).mpr
          (A.cyclicNormHom_comp_oneSubPow hA)) :=
  ShortComplex.isoMk (-(Iso.refl _)) (Iso.refl _) (Iso.refl _)
    (by simpa only [Preadditive.neg_iso_hom, Iso.refl_hom, Preadditive.neg_comp,
        Category.id_comp, Category.comp_id] using
      (A.subCompNormHom_cyclicRep_f hA).symm)
    (by simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id] using
      (A.subCompNormHom_cyclicRep_g hA).symm)

@[simp]
theorem normHomCompSubCyclicRepIso_hom_τ₁ :
    (A.normHomCompSubCyclicRepIso hA).hom.τ₁ = 𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem normHomCompSubCyclicRepIso_hom_τ₂ :
    (A.normHomCompSubCyclicRepIso hA).hom.τ₂ = 𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem normHomCompSubCyclicRepIso_hom_τ₃ :
    (A.normHomCompSubCyclicRepIso hA).hom.τ₃ = -𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem normHomCompSubCyclicRepIso_inv_τ₁ :
    (A.normHomCompSubCyclicRepIso hA).inv.τ₁ = 𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem normHomCompSubCyclicRepIso_inv_τ₂ :
    (A.normHomCompSubCyclicRepIso hA).inv.τ₂ = 𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem normHomCompSubCyclicRepIso_inv_τ₃ :
    (A.normHomCompSubCyclicRepIso hA).inv.τ₃ = -𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem subCompNormHomCyclicRepIso_hom_τ₁ :
    (A.subCompNormHomCyclicRepIso hA).hom.τ₁ = -𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem subCompNormHomCyclicRepIso_hom_τ₂ :
    (A.subCompNormHomCyclicRepIso hA).hom.τ₂ = 𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem subCompNormHomCyclicRepIso_hom_τ₃ :
    (A.subCompNormHomCyclicRepIso hA).hom.τ₃ = 𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem subCompNormHomCyclicRepIso_inv_τ₁ :
    (A.subCompNormHomCyclicRepIso hA).inv.τ₁ = -𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem subCompNormHomCyclicRepIso_inv_τ₂ :
    (A.subCompNormHomCyclicRepIso hA).inv.τ₂ = 𝟙 (ModuleCat.of ℤ T) := (rfl)

@[simp]
theorem subCompNormHomCyclicRepIso_inv_τ₃ :
    (A.subCompNormHomCyclicRepIso hA).inv.τ₃ = 𝟙 (ModuleCat.of ℤ T) := (rfl)

end AddEquiv
