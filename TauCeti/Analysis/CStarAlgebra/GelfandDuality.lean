/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Analysis.Normed.Algebra.Character.Unitization
public import TauCeti.Analysis.Normed.Algebra.Character.ZeroAtInfty
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.OnePoint

import Mathlib.Algebra.Order.Star.Unitization
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Topology.ContinuousMap.StarOrdered
import TauCeti.Algebra.Algebra.Unitization
import TauCeti.Topology.Compactness.Compact

/-!
# Nonunital Gelfand Duality

Mathlib proves unital Gelfand duality (`gelfandStarTransform`): every commutative unital complex
C⋆-algebra `A` is isometrically `⋆`-isomorphic to `C(characterSpace ℂ A, ℂ)`, and
`TauCeti.Analysis.Normed.Algebra.Character.ZeroAtInfty` constructs the nonunital evaluation
homeomorphism `WeakDual.CharacterSpace.zeroAtInftyHomeoEval : Y ≃ₜ characterSpace 𝕜 C₀(Y, 𝕜)` for
every weakly locally compact Hausdorff space `Y` and `RCLike 𝕜`.

This file develops Gelfand duality for nonunital commutative C⋆-algebras by passing through the
minimal C⋆-unitization `A⁺¹ = Unitization ℂ A` and the augmentation character
`ε = Unitization.augmentation ℂ A`:

* `TauCeti.map_gelfandStarTransform_inrRange`: under `gelfandStarTransform A⁺¹`, the image of `A`
  inside `A⁺¹` (`ker ε`) equals the maximal ideal
  `ContinuousMap.evalKerSubalgebra ℂ ℂ ε = {F ∈ C(characterSpace ℂ A⁺¹, ℂ) : F ε = 0}`, which
  `ContinuousMap.restrictComplSingletonStarAlgEquiv` identifies isometrically with
  `C₀({φ : characterSpace ℂ A⁺¹ // φ ≠ ε}, ℂ)`;
* `TauCeti.puncturedGelfandStarTransform`: restricting `gelfandStarTransform A⁺¹ (a : A⁺¹)` to the
  locally compact Hausdorff complement `{φ : characterSpace ℂ A⁺¹ // φ ≠ ε}` gives a `⋆`-isomorphism
  `A ≃⋆ₐ[ℂ] C₀({φ : characterSpace ℂ A⁺¹ // φ ≠ ε}, ℂ)` whose inverse extends by zero at `ε`;
* `TauCeti.nonUnitalGelfandStarTransform`: reindexing along
  `WeakDual.CharacterSpace.unitizationComplAugmentationHomeomorph` yields the intrinsic Gelfand
  `⋆`-isomorphism `A ≃⋆ₐ[ℂ] C₀(characterSpace ℂ A, ℂ)`, `a ↦ (χ ↦ χ a)`. Both `⋆`-equivalences
  are automatically norm-preserving isometries via Mathlib's `StarAlgEquiv.norm_map` and
  `StarAlgEquiv.isometry`;
* `TauCeti.nonUnitalGelfandStarTransform_eq_of_unital`,
  `TauCeti.compactSpace_characterSpace_iff_isUnital`, and
  `TauCeti.isOpen_singleton_augmentation_iff_isUnital`: when `A` is unital, the nonunital Gelfand
  `⋆`-transform agrees with `gelfandStarTransform A` lifted to `C₀`, and conversely
  `characterSpace ℂ A` is compact (equivalently `{ε}` is open in `characterSpace ℂ A⁺¹`) if and
  only if `IsUnital A`;
* Comparing `TauCeti.nonUnitalGelfandStarTransform` on `C₀(Y, ℂ)` with
  `WeakDual.CharacterSpace.zeroAtInftyHomeoEval Y ℂ` recovers the identity `⋆`-automorphism on
  `C₀(Y, ℂ)`.
* `TauCeti.nonneg_iff_forall_characterSpace_nonneg`: an element of a commutative C⋆-algebra is
  positive exactly when every character is nonnegative on it, and
  `TauCeti.characterSpace_apply_gelfandStarTransform_symm`: a character evaluates the inverse
  Gelfand transform of `f` to `f` at that character.
* `WeakDual.CharacterSpace.instStarHomClassOfNonUnitalCommCStarAlgebra`: characters of a
  nonunital commutative C⋆-algebra commute with `star`.

## References

* J. B. Conway, *A Course in Functional Analysis*, §VIII.2.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Theorem 2.1.10.
-/

public section

open WeakDual
open scoped CStarAlgebra ZeroAtInfty

namespace Unitization

variable {A : Type*} [NonUnitalCommCStarAlgebra A]

/-- Evaluating `gelfandStarTransform A⁺¹ u` at the augmentation character recovers `u.fst`. -/
theorem gelfandStarTransform_apply_augmentation (u : A⁺¹) :
    gelfandStarTransform A⁺¹ u (Unitization.augmentation ℂ A) = u.fst := by
  simp

end Unitization

namespace TauCeti

section NonUnitalGelfand

variable {A : Type*} [NonUnitalCommCStarAlgebra A]

/-- For `a : A`, `gelfandStarTransform A⁺¹ (a : A⁺¹)` vanishes at the augmentation character. -/
theorem gelfandStarTransform_unitization_inr_apply_augmentation (a : A) :
    gelfandStarTransform A⁺¹ (a : A⁺¹) (Unitization.augmentation ℂ A) = 0 := by
  simp

/-- Under `gelfandStarTransform A⁺¹`, the nonunital star subalgebra `Set.range inr` of `A⁺¹` maps
onto `{F ∈ C(characterSpace ℂ A⁺¹, ℂ) : F (Unitization.augmentation ℂ A) = 0}`. -/
theorem map_gelfandStarTransform_inrRange :
    (Unitization.inrNonUnitalStarAlgHom ℂ A).range.map
        (gelfandStarTransform A⁺¹).toNonUnitalStarAlgHom =
      ContinuousMap.evalKerSubalgebra ℂ ℂ (Unitization.augmentation ℂ A) := by
  ext F
  simp only [NonUnitalStarSubalgebra.mem_map, NonUnitalStarAlgHom.mem_range,
    Unitization.inrNonUnitalStarAlgHom_apply, ContinuousMap.mem_evalKerSubalgebra]
  refine ⟨?_, fun hF ↦ ?_⟩
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact gelfandStarTransform_unitization_inr_apply_augmentation a
  · set u : A⁺¹ := (gelfandStarTransform A⁺¹).symm F
    have hu : u.fst = 0 := by
      rw [← u.gelfandStarTransform_apply_augmentation, StarAlgEquiv.apply_symm_apply, hF]
    exact ⟨u, ⟨u.snd, Unitization.inr_snd_of_fst_eq_zero hu⟩,
      (gelfandStarTransform A⁺¹).apply_symm_apply F⟩

private theorem bijective_codRestrict_gelfandStarTransform :
    Function.Bijective
      (((gelfandStarTransform A⁺¹).toNonUnitalStarAlgHom.comp
          (Unitization.inrNonUnitalStarAlgHom ℂ A)).codRestrict
        (ContinuousMap.evalKerSubalgebra ℂ ℂ (Unitization.augmentation ℂ A))
        fun a ↦ ContinuousMap.mem_evalKerSubalgebra.mpr
          (gelfandStarTransform_unitization_inr_apply_augmentation a)) :=
  ⟨(NonUnitalStarAlgHom.injective_codRestrict _ _ _).mpr <|
      (gelfandStarTransform A⁺¹).injective.comp Unitization.inr_injective,
    fun F ↦ by
      obtain ⟨_, ⟨a, rfl⟩, hu⟩ :=
        (SetLike.ext_iff.mp map_gelfandStarTransform_inrRange F.val).mpr F.property
      exact ⟨a, Subtype.ext hu⟩⟩

variable (A) in
/-- **Nonunital Gelfand transform via the punctured unitization character space.** Restricting
`gelfandStarTransform A⁺¹ (a : A⁺¹)` to `{φ : characterSpace ℂ A⁺¹ // φ ≠ ε}` identifies `A`
`⋆`-isomorphically (and isometrically via `StarAlgEquiv.isometry`) with
`C₀({φ : characterSpace ℂ A⁺¹ // φ ≠ Unitization.augmentation ℂ A}, ℂ)`, with inverse given by
extension by zero across the augmentation character. -/
noncomputable def puncturedGelfandStarTransform :
    A ≃⋆ₐ[ℂ] C₀({φ : characterSpace ℂ A⁺¹ // φ ≠ Unitization.augmentation ℂ A}, ℂ) :=
  (StarAlgEquiv.ofBijective _ bijective_codRestrict_gelfandStarTransform).trans
    (ContinuousMap.restrictComplSingletonStarAlgEquiv ℂ ℂ (Unitization.augmentation ℂ A))

/-- `puncturedGelfandStarTransform A a` evaluates `φ.1` on `(a : A⁺¹)`. -/
@[simp]
theorem puncturedGelfandStarTransform_apply (a : A)
    (φ : {φ : characterSpace ℂ A⁺¹ // φ ≠ Unitization.augmentation ℂ A}) :
    puncturedGelfandStarTransform A a φ = φ.val (a : A⁺¹) := by
  simp [puncturedGelfandStarTransform]

/-- Extending `puncturedGelfandStarTransform A a` by zero at the augmentation character recovers
`gelfandStarTransform A⁺¹ ↑a`. -/
@[simp]
theorem extendZero_puncturedGelfandStarTransform (a : A) :
    (puncturedGelfandStarTransform A a).extendZero = gelfandStarTransform A⁺¹ (a : A⁺¹) := by
  simp [puncturedGelfandStarTransform]

variable (A) in
/-- **Nonunital Gelfand duality.** Every nonunital commutative complex C⋆-algebra `A` is
`⋆`-isomorphic (and isometric by `StarAlgEquiv.isometry`) to `C₀(characterSpace ℂ A, ℂ)` via
evaluation `a ↦ (χ ↦ χ a)`. -/
noncomputable def nonUnitalGelfandStarTransform :
    A ≃⋆ₐ[ℂ] C₀(characterSpace ℂ A, ℂ) :=
  (puncturedGelfandStarTransform A).trans
    (ZeroAtInftyContinuousMap.congrLeftStarAlgEquiv ℂ ℂ
      (WeakDual.CharacterSpace.unitizationComplAugmentationHomeomorph ℂ A).symm)

/-- `nonUnitalGelfandStarTransform A a` evaluates a character `χ` at `a`. -/
@[simp]
theorem nonUnitalGelfandStarTransform_apply (a : A) (χ : characterSpace ℂ A) :
    nonUnitalGelfandStarTransform A a χ = χ a := by
  simp [nonUnitalGelfandStarTransform]

/-- Extending `nonUnitalGelfandStarTransform A a` by zero to `OnePoint (characterSpace ℂ A)` and
transporting along `(onePointHomeomorphUnitization ℂ A).symm` recovers
`gelfandStarTransform A⁺¹ (a : A⁺¹)`. -/
theorem toOnePoint_nonUnitalGelfandStarTransform_comp_symm (a : A) :
    (nonUnitalGelfandStarTransform A a).toOnePoint.comp
        (WeakDual.CharacterSpace.onePointHomeomorphUnitization ℂ A).symm =
      gelfandStarTransform A⁺¹ (a : A⁺¹) := by
  ext φ
  by_cases hφ : φ = Unitization.augmentation ℂ A
  · subst hφ
    simp
  · simp [WeakDual.CharacterSpace.onePointHomeomorphUnitization_symm_apply_of_ne hφ]

end NonUnitalGelfand

end TauCeti

namespace ZeroAtInftyContinuousMap

variable {A : Type*} [NonUnitalCommCStarAlgebra A]

/-- The inverse of `TauCeti.puncturedGelfandStarTransform A` extends `g` by zero at the augmentation
character and applies `(gelfandStarTransform A⁺¹).symm`. -/
@[simp]
theorem inr_puncturedGelfandStarTransform_symm
    (g : C₀({φ : characterSpace ℂ A⁺¹ // φ ≠ Unitization.augmentation ℂ A}, ℂ)) :
    (((TauCeti.puncturedGelfandStarTransform A).symm g : A) : A⁺¹) =
      (gelfandStarTransform A⁺¹).symm g.extendZero := by
  apply EquivLike.injective (gelfandStarTransform A⁺¹)
  rw [← TauCeti.extendZero_puncturedGelfandStarTransform, StarAlgEquiv.apply_symm_apply,
    StarAlgEquiv.apply_symm_apply]

/-- Embedding `(TauCeti.nonUnitalGelfandStarTransform A).symm f` into `A⁺¹` equals applying
`(gelfandStarTransform A⁺¹).symm` to `f.toOnePoint` transported along
`WeakDual.CharacterSpace.onePointHomeomorphUnitization ℂ A`. -/
@[simp]
theorem inr_nonUnitalGelfandStarTransform_symm (f : C₀(characterSpace ℂ A, ℂ)) :
    (((TauCeti.nonUnitalGelfandStarTransform A).symm f : A) : A⁺¹) =
      (gelfandStarTransform A⁺¹).symm
        (f.toOnePoint.comp
          (WeakDual.CharacterSpace.onePointHomeomorphUnitization ℂ A).symm) := by
  apply EquivLike.injective (gelfandStarTransform A⁺¹)
  rw [← TauCeti.toOnePoint_nonUnitalGelfandStarTransform_comp_symm, StarAlgEquiv.apply_symm_apply,
    StarAlgEquiv.apply_symm_apply]

end ZeroAtInftyContinuousMap

namespace WeakDual.CharacterSpace

section Separation

variable {A : Type*} [NonUnitalCommCStarAlgebra A]

/-- Continuous characters separate nonzero elements of any nonunital commutative complex
C⋆-algebra. -/
theorem exists_apply_ne_zero {a : A} (ha : a ≠ 0) :
    ∃ χ : characterSpace ℂ A, χ a ≠ 0 := by
  by_contra! h
  apply ha
  refine EquivLike.injective (TauCeti.nonUnitalGelfandStarTransform A) ?_
  ext χ
  simpa using h χ

/-- Two elements of a nonunital commutative complex C⋆-algebra are equal if every continuous
character takes the same value on them. -/
theorem eq_of_forall_apply_eq {a b : A} (h : ∀ χ : characterSpace ℂ A, χ a = χ b) :
    a = b := by
  by_contra hne
  obtain ⟨χ, hχ⟩ := exists_apply_ne_zero (sub_ne_zero.mpr hne)
  exact hχ (by simp [map_sub, h χ])

end Separation

section Star

variable {A : Type*} [NonUnitalCommCStarAlgebra A]

/-- Characters of a nonunital commutative C⋆-algebra commute with `star`, as restrictions of
characters of the unitization; Mathlib's `WeakDual.CharacterSpace.instStarHomClass` covers the
unital case. -/
instance instStarHomClassOfNonUnitalCommCStarAlgebra : StarHomClass (characterSpace ℂ A) A ℂ where
  map_star χ a := by
    simpa using map_star (unitizationExtend χ).val (a : A⁺¹)

end Star

end WeakDual.CharacterSpace

namespace TauCeti

section UnitalComparison

/-- For a unital commutative C⋆-algebra `A` viewed through its nonunital carrier,
`nonUnitalGelfandStarTransform A` agrees with the unital `gelfandStarTransform A` composed with
`ContinuousMap.liftZeroAtInftyStarAlgEquiv`. -/
theorem nonUnitalGelfandStarTransform_eq_of_unital (A : Type*) [CommCStarAlgebra A] :
    nonUnitalGelfandStarTransform A =
      (gelfandStarTransform A).trans
        (ContinuousMap.liftZeroAtInftyStarAlgEquiv ℂ (characterSpace ℂ A) ℂ) := by
  ext a χ
  simp

/-- In a nonunital commutative complex C⋆-algebra `A`, `characterSpace ℂ A` is compact if and only
if `A` has a multiplicative identity (`IsUnital A`). -/
theorem compactSpace_characterSpace_iff_isUnital (A : Type*) [NonUnitalCommCStarAlgebra A] :
    CompactSpace (characterSpace ℂ A) ↔ IsUnital A := by
  refine ⟨fun _ ↦ ⟨?_⟩, fun _ ↦ ?_⟩
  · let oneC₀ : C₀(characterSpace ℂ A, ℂ) :=
      ContinuousMap.liftZeroAtInftyStarAlgEquiv ℂ (characterSpace ℂ A) ℂ 1
    refine ⟨(nonUnitalGelfandStarTransform A).symm oneC₀, fun a ↦ ?_⟩
    have hleft : (nonUnitalGelfandStarTransform A).symm oneC₀ * a = a := by
      apply EquivLike.injective (nonUnitalGelfandStarTransform A)
      rw [map_mul, StarAlgEquiv.apply_symm_apply]
      ext χ
      simp [oneC₀]
    exact ⟨hleft, (mul_comm a _).trans hleft⟩
  · obtain ⟨e, he⟩ := IsUnital.isUnital (A := A)
    exact WeakDual.CharacterSpace.compactSpace_of_forall_mul_eq fun a ↦ (he a).2

/-- In a nonunital commutative complex C⋆-algebra `A`, the augmentation character is isolated in
`characterSpace ℂ A⁺¹` if and only if `A` has a multiplicative identity (`IsUnital A`). -/
theorem isOpen_singleton_augmentation_iff_isUnital (A : Type*) [NonUnitalCommCStarAlgebra A] :
    IsOpen ({Unitization.augmentation ℂ A} : Set (characterSpace ℂ A⁺¹)) ↔ IsUnital A := by
  rw [← compactSpace_complSingleton_iff_isOpen_singleton,
    ← compactSpace_characterSpace_iff_isUnital]
  exact
    ⟨fun _ ↦ (WeakDual.CharacterSpace.unitizationComplAugmentationHomeomorph ℂ A).symm.compactSpace,
     fun _ ↦ (WeakDual.CharacterSpace.unitizationComplAugmentationHomeomorph ℂ A).compactSpace⟩

end UnitalComparison

section Positivity

open WeakDual
open scoped ComplexOrder

/-- An element of a commutative unital C⋆-algebra is positive exactly when every character is
nonnegative on it: this is positivity of its Gelfand transform. -/
private theorem nonneg_iff_forall_characterSpace_nonneg_of_unital {C : Type*} [CommCStarAlgebra C]
    [PartialOrder C] [StarOrderedRing C] {x : C} : 0 ≤ x ↔ ∀ χ : characterSpace ℂ C, 0 ≤ χ x := by
  rw [← map_le_map_iff (gelfandStarTransform C), map_zero, ContinuousMap.le_def]
  simp

/-- An element of a commutative C⋆-algebra is positive exactly when every character is
nonnegative on it. -/
theorem nonneg_iff_forall_characterSpace_nonneg {C : Type*} [NonUnitalCommCStarAlgebra C]
    [PartialOrder C] [StarOrderedRing C] {x : C} : 0 ≤ x ↔ ∀ χ : characterSpace ℂ C, 0 ≤ χ x := by
  rw [← Unitization.inr_nonneg_iff ℂ, nonneg_iff_forall_characterSpace_nonneg_of_unital]
  refine ⟨fun h χ => by simpa using h (CharacterSpace.unitizationExtend χ), fun h χ => ?_⟩
  by_cases hχ : χ = Unitization.augmentation ℂ C
  · simp [hχ]
  · simpa using h (CharacterSpace.unitizationRestrict ⟨χ, hχ⟩)

/-- Evaluating the inverse Gelfand transform of `f` at a character `y` gives `f y`. It is not a
simp lemma: `simp` first rewrites `(gelfandStarTransform A).symm f` by Mathlib's
`gelfandStarTransform_symm_apply`. -/
theorem characterSpace_apply_gelfandStarTransform_symm {A : Type*} [CommCStarAlgebra A]
    (f : C(characterSpace ℂ A, ℂ)) (y : characterSpace ℂ A) :
    y ((gelfandStarTransform A).symm f) = f y := by
  simpa using congr($((gelfandStarTransform A).apply_symm_apply f) y)

end Positivity

end TauCeti

namespace WeakDual.CharacterSpace

/-- Applying `TauCeti.nonUnitalGelfandStarTransform` to `C₀(Y, ℂ)` and reindexing along
`WeakDual.CharacterSpace.zeroAtInftyHomeoEval Y ℂ` recovers the identity star-algebra equivalence
on `C₀(Y, ℂ)`. -/
@[simp]
theorem nonUnitalGelfandStarTransform_trans_congrLeftStarAlgEquiv_zeroAtInftyHomeoEval_symm
    (Y : Type*) [TopologicalSpace Y] [WeaklyLocallyCompactSpace Y] [T2Space Y] :
    (TauCeti.nonUnitalGelfandStarTransform C₀(Y, ℂ)).trans
        (ZeroAtInftyContinuousMap.congrLeftStarAlgEquiv ℂ ℂ (zeroAtInftyHomeoEval Y ℂ).symm) =
      StarAlgEquiv.refl ℂ C₀(Y, ℂ) := by
  ext f y
  simp

end WeakDual.CharacterSpace
