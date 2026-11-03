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
negating one end of each short complex. Both composites of the norm and `1 - A`
vanish. For period two, the norm is `1 + A`.

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

/-- For a periodic automorphism, `1 - A` annihilates the cyclic norm.
For nonzero period this is the zero-composite law of Mathlib's norm-then-difference complex. -/
theorem oneSubPow_comp_cyclicNormHom {m : ℕ} (hA : (⇑A)^[m] = id) :
    (A.oneSubPow 1).comp (A.cyclicNormHom m) = 0 := by
  by_cases hm : m = 0
  · subst m
    simp
  let : NeZero m := ⟨hm⟩
  have hz := (normHomCompSub (A.cyclicRep hA) (.ofAdd 1)).zero
  rw [A.normHomCompSub_cyclicRep_f hA, A.normHomCompSub_cyclicRep_g hA,
    Preadditive.comp_neg, neg_eq_zero] at hz
  exact (AddMonoidHom.ofHom_toIntLinearMap_comp_eq_zero_iff _ _).mp hz

/-- For a periodic automorphism, the cyclic norm annihilates `1 - A`.
For nonzero period this is the zero-composite law of Mathlib's difference-then-norm complex. -/
theorem cyclicNormHom_comp_oneSubPow {m : ℕ} (hA : (⇑A)^[m] = id) :
    (A.cyclicNormHom m).comp (A.oneSubPow 1) = 0 := by
  by_cases hm : m = 0
  · subst m
    simp
  let : NeZero m := ⟨hm⟩
  have hz := (subCompNormHom (A.cyclicRep hA) (.ofAdd 1)).zero
  rw [A.subCompNormHom_cyclicRep_f hA, A.subCompNormHom_cyclicRep_g hA,
    Preadditive.neg_comp, neg_eq_zero] at hz
  exact (AddMonoidHom.ofHom_toIntLinearMap_comp_eq_zero_iff _ _).mp hz

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
