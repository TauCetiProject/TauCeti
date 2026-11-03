/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Cyclic.Affine
public import Mathlib.RepresentationTheory.Homological.FiniteCyclic

/-!
# The periodic short complexes of an involution

For an additive involution `A`, the norm of its cyclic representation is `1 + A`.
Mathlib's periodic short complexes use the other differential `A - 1`. We identify
their maps and give isomorphisms to the convention with differential `1 - A` by
negating one end of each short complex. Both composites of `1 + A` and `1 - A`
vanish. For period dividing `m`, the differentials are `cyclicNormHom m` and
`-oneSubPow 1`; their comparisons and zero-composite laws are given for arbitrary finite order.

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
  A.normHomCompSub_cyclicRep_g hA

/-- The second map in the other periodic short complex is the bundled partial norm. -/
theorem subCompNormHom_cyclicRep_g :
    (subCompNormHom (A.cyclicRep hA) (.ofAdd 1)).g =
      ModuleCat.ofHom (A.cyclicNormHom m).toIntLinearMap :=
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
  exact congrArg (fun f : ModuleCat.of ℤ T ⟶ ModuleCat.of ℤ T ↦ f.hom.toAddMonoidHom) hz

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
  exact congrArg (fun f : ModuleCat.of ℤ T ⟶ ModuleCat.of ℤ T ↦ f.hom.toAddMonoidHom) hz

variable (hA : (⇑A)^[2] = id)

/-- Negating the last object changes the periodic short complex `1 + A, A - 1`
to the convention `1 + A, 1 - A`. Its zero-composite law is inherited from
Mathlib's short complex. -/
noncomputable def normHomCompSubCyclicRepTwoIso :
    normHomCompSub (A.cyclicRep hA) (.ofAdd 1) ≅
      ShortComplex.mk
        (ModuleCat.ofHom (A.cyclicNormHom 2).toIntLinearMap)
        (ModuleCat.ofHom (A.oneSubPow 1).toIntLinearMap)
        (congrArg (fun f : T →+ T ↦ ModuleCat.ofHom f.toIntLinearMap)
          (A.oneSubPow_comp_cyclicNormHom hA)) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (-(Iso.refl _))
    (by simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id] using
      (A.normHomCompSub_cyclicRep_f hA).symm)
    (by simpa only [Iso.refl_hom, Preadditive.neg_iso_hom, Category.id_comp,
        Preadditive.comp_neg, Category.comp_id, neg_neg] using
      congrArg Neg.neg (A.normHomCompSub_cyclicRep_g hA).symm)

/-- Negating the first object changes the periodic short complex `A - 1, 1 + A`
to the convention `1 - A, 1 + A`, retaining Mathlib's shared source complex. -/
noncomputable def subCompNormHomCyclicRepTwoIso :
    subCompNormHom (A.cyclicRep hA) (.ofAdd 1) ≅
      ShortComplex.mk
        (ModuleCat.ofHom (A.oneSubPow 1).toIntLinearMap)
        (ModuleCat.ofHom (A.cyclicNormHom 2).toIntLinearMap)
        (congrArg (fun f : T →+ T ↦ ModuleCat.ofHom f.toIntLinearMap)
          (A.cyclicNormHom_comp_oneSubPow hA)) :=
  ShortComplex.isoMk (-(Iso.refl _)) (Iso.refl _) (Iso.refl _)
    (by simpa only [Preadditive.neg_iso_hom, Iso.refl_hom, Preadditive.neg_comp,
        Category.id_comp, Category.comp_id] using
      (A.subCompNormHom_cyclicRep_f hA).symm)
    (by simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id] using
      (A.subCompNormHom_cyclicRep_g hA).symm)

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
