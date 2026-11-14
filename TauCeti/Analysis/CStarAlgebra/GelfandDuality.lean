/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.RCLike.Lemmas
public import TauCeti.Analysis.Normed.Algebra.Character.Pullback
public import TauCeti.Analysis.Normed.Algebra.Character.Unitization
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.OnePoint

import TauCeti.Topology.Compactness.Compact

/-!
# Nonunital Gelfand Duality

Mathlib proves unital Gelfand duality (`gelfandStarTransform`): every commutative unital complex
C⋆-algebra `A` is isometrically `⋆`-isomorphic to `C(characterSpace ℂ A, ℂ)`, and evaluation gives a
homeomorphism `WeakDual.CharacterSpace.homeoEval : X ≃ₜ characterSpace 𝕜 C(X, 𝕜)` for every compact
Hausdorff space `X`.

This file develops Gelfand duality for nonunital commutative C⋆-algebras by passing through the
minimal C⋆-unitization `A⁺¹ = Unitization ℂ A` and the augmentation character
`ε = Unitization.augmentation ℂ A`:

* `TauCeti.map_gelfandStarTransform_inrRange` and
  `TauCeti.image_gelfandStarTransform_range_inr`: under `gelfandStarTransform A⁺¹`, the image of
  `A` inside `A⁺¹` (`ker ε`) equals the maximal ideal
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
* `WeakDual.CharacterSpace.unitizationZeroAtInftyHomeoEval` and
  `WeakDual.CharacterSpace.zeroAtInftyHomeoEval`: for any weakly locally compact Hausdorff space
  `Y` and `RCLike` scalar field `𝕜`, point evaluation identifies `OnePoint Y` with
  `characterSpace 𝕜 (Unitization 𝕜 C₀(Y, 𝕜))` (sending `∞` to `ε`) and `Y` with
  `characterSpace 𝕜 C₀(Y, 𝕜)`, recovering the identity `⋆`-automorphism on `C₀(Y, ℂ)`.

## References

* J. B. Conway, *A Course in Functional Analysis*, §VIII.2.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Theorem 2.1.10.
-/

@[expose] public section

open Filter Function Set Topology OnePoint WeakDual
open scoped CStarAlgebra ZeroAtInfty

namespace TauCeti

section NonUnitalGelfand

variable {A : Type*} [NonUnitalCommCStarAlgebra A]

/-- Evaluating `gelfandStarTransform A⁺¹ u` at the augmentation character recovers `u.fst`. -/
theorem gelfandStarTransform_unitization_apply_augmentation (u : A⁺¹) :
    gelfandStarTransform A⁺¹ u (Unitization.augmentation ℂ A) = u.fst := by
  simp

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
    have hu : Unitization.augmentation ℂ A u = 0 := by
      rw [Unitization.augmentation_apply, ← gelfandStarTransform_unitization_apply_augmentation u,
        StarAlgEquiv.apply_symm_apply, hF]
    exact ⟨u, ⟨u.snd, Unitization.inr_snd_of_augmentation_eq_zero hu⟩,
      (gelfandStarTransform A⁺¹).apply_symm_apply F⟩

/-- Set-level form of `map_gelfandStarTransform_inrRange`: the Gelfand transform of `A⁺¹` carries
`Set.range (Unitization.inr : A → A⁺¹)` onto `{F ∈ C(characterSpace ℂ A⁺¹, ℂ) : F ε = 0}`. -/
theorem image_gelfandStarTransform_range_inr :
    gelfandStarTransform A⁺¹ '' Set.range (Unitization.inr : A → A⁺¹) =
      {F : C(characterSpace ℂ A⁺¹, ℂ) | F (Unitization.augmentation ℂ A) = 0} := by
  ext F
  simpa using SetLike.ext_iff.mp map_gelfandStarTransform_inrRange F

variable (A) in
/-- **Nonunital Gelfand transform via the punctured unitization character space.** Restricting
`gelfandStarTransform A⁺¹ (a : A⁺¹)` to `{φ : characterSpace ℂ A⁺¹ // φ ≠ ε}` identifies `A`
`⋆`-isomorphically (and isometrically via `StarAlgEquiv.isometry`) with
`C₀({φ : characterSpace ℂ A⁺¹ // φ ≠ Unitization.augmentation ℂ A}, ℂ)`, with inverse given by
extension by zero across the augmentation character. -/
noncomputable def puncturedGelfandStarTransform :
    A ≃⋆ₐ[ℂ] C₀({φ : characterSpace ℂ A⁺¹ // φ ≠ Unitization.augmentation ℂ A}, ℂ) :=
  let Φ : A →⋆ₙₐ[ℂ] C(characterSpace ℂ A⁺¹, ℂ) :=
    (gelfandStarTransform A⁺¹).toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  let hΦ : Function.Bijective
      (Φ.codRestrict (ContinuousMap.evalKerSubalgebra ℂ ℂ (Unitization.augmentation ℂ A))
        gelfandStarTransform_unitization_inr_apply_augmentation) :=
    ⟨(NonUnitalStarAlgHom.injective_codRestrict _ _ _).mpr <|
        (gelfandStarTransform A⁺¹).injective.comp Unitization.inr_injective,
      fun F ↦ by
        obtain ⟨_, ⟨a, rfl⟩, hu⟩ :=
          (SetLike.ext_iff.mp map_gelfandStarTransform_inrRange F.1).mpr F.2
        exact ⟨a, Subtype.ext hu⟩⟩
  (StarAlgEquiv.ofBijective _ hΦ).trans
    (ContinuousMap.restrictComplSingletonStarAlgEquiv ℂ ℂ (Unitization.augmentation ℂ A))

/-- `puncturedGelfandStarTransform A a` evaluates `φ.1` on `(a : A⁺¹)`. -/
@[simp]
theorem puncturedGelfandStarTransform_apply (a : A)
    (φ : {φ : characterSpace ℂ A⁺¹ // φ ≠ Unitization.augmentation ℂ A}) :
    puncturedGelfandStarTransform A a φ = φ.1 (a : A⁺¹) := (rfl)

/-- Extending `puncturedGelfandStarTransform A a` by zero at the augmentation character recovers
`gelfandStarTransform A⁺¹ ↑a`. -/
@[simp]
theorem extendZero_puncturedGelfandStarTransform (a : A) :
    (puncturedGelfandStarTransform A a).extendZero = gelfandStarTransform A⁺¹ (a : A⁺¹) :=
  ZeroAtInftyContinuousMap.extendZero_restrictComplSingleton
    (gelfandStarTransform_unitization_inr_apply_augmentation a)

/-- The inverse of `puncturedGelfandStarTransform A` extends `g` by zero at the augmentation
character and applies `(gelfandStarTransform A⁺¹).symm`. -/
@[simp]
theorem inr_puncturedGelfandStarTransform_symm
    (g : C₀({φ : characterSpace ℂ A⁺¹ // φ ≠ Unitization.augmentation ℂ A}, ℂ)) :
    (((puncturedGelfandStarTransform A).symm g : A) : A⁺¹) =
      (gelfandStarTransform A⁺¹).symm g.extendZero := by
  apply EquivLike.injective (gelfandStarTransform A⁺¹)
  rw [← extendZero_puncturedGelfandStarTransform, StarAlgEquiv.apply_symm_apply,
    StarAlgEquiv.apply_symm_apply]

variable (A) in
/-- **Nonunital Gelfand duality.** Every nonunital commutative complex C⋆-algebra `A` is
`⋆`-isomorphic (and isometric by `StarAlgEquiv.isometry`) to `C₀(characterSpace ℂ A, ℂ)` via
evaluation `a ↦ (χ ↦ χ a)`. -/
noncomputable def nonUnitalGelfandStarTransform :
    A ≃⋆ₐ[ℂ] C₀(characterSpace ℂ A, ℂ) :=
  (puncturedGelfandStarTransform A).trans
    (ZeroAtInftyContinuousMap.congrLeftStarAlgEquiv ℂ ℂ
      (WeakDual.CharacterSpace.unitizationComplAugmentationHomeomorph ℂ A).symm)

/-- Factorization of `nonUnitalGelfandStarTransform A` through `puncturedGelfandStarTransform A` and
`unitizationComplAugmentationHomeomorph ℂ A`. -/
theorem nonUnitalGelfandStarTransform_def (A : Type*) [NonUnitalCommCStarAlgebra A] :
    nonUnitalGelfandStarTransform A =
      (puncturedGelfandStarTransform A).trans
        (ZeroAtInftyContinuousMap.congrLeftStarAlgEquiv ℂ ℂ
          (WeakDual.CharacterSpace.unitizationComplAugmentationHomeomorph ℂ A).symm) := (rfl)

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

/-- Embedding `(nonUnitalGelfandStarTransform A).symm f` into `A⁺¹` equals applying
`(gelfandStarTransform A⁺¹).symm` to `f.toOnePoint` transported along
`onePointHomeomorphUnitization ℂ A`. -/
@[simp]
theorem inr_nonUnitalGelfandStarTransform_symm (f : C₀(characterSpace ℂ A, ℂ)) :
    (((nonUnitalGelfandStarTransform A).symm f : A) : A⁺¹) =
      (gelfandStarTransform A⁺¹).symm
        (f.toOnePoint.comp
          (WeakDual.CharacterSpace.onePointHomeomorphUnitization ℂ A).symm) := by
  apply EquivLike.injective (gelfandStarTransform A⁺¹)
  rw [← toOnePoint_nonUnitalGelfandStarTransform_comp_symm, StarAlgEquiv.apply_symm_apply,
    StarAlgEquiv.apply_symm_apply]

end NonUnitalGelfand

end TauCeti

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
  refine ⟨fun _ ↦ ⟨?_⟩, fun _ ↦ WeakDual.CharacterSpace.compactSpace_of_isUnital⟩
  let oneC₀ : C₀(characterSpace ℂ A, ℂ) :=
    ContinuousMap.liftZeroAtInftyStarAlgEquiv ℂ (characterSpace ℂ A) ℂ 1
  refine ⟨(nonUnitalGelfandStarTransform A).symm oneC₀, fun a ↦ ?_⟩
  have hleft : (nonUnitalGelfandStarTransform A).symm oneC₀ * a = a := by
    apply EquivLike.injective (nonUnitalGelfandStarTransform A)
    rw [map_mul, StarAlgEquiv.apply_symm_apply]
    ext χ
    simp [oneC₀]
  exact ⟨hleft, (mul_comm a _).trans hleft⟩

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

end TauCeti

namespace WeakDual.CharacterSpace

section ZeroAtInftyEval

variable (Y 𝕜 : Type*) [TopologicalSpace Y] [WeaklyLocallyCompactSpace Y] [T2Space Y] [RCLike 𝕜]

/-- Point evaluation identifies `OnePoint Y` with the character space of
`Unitization 𝕜 C₀(Y, 𝕜)`, sending `∞` to `Unitization.augmentation 𝕜 C₀(Y, 𝕜)` and `(y : Y)` to
`u ↦ u.fst + u.snd y`. -/
noncomputable def unitizationZeroAtInftyHomeoEval :
    OnePoint Y ≃ₜ characterSpace 𝕜 (Unitization 𝕜 C₀(Y, 𝕜)) :=
  (homeoEval (OnePoint Y) 𝕜).trans
    (AlgEquiv.characterSpaceHomeomorph (A := Unitization 𝕜 C₀(Y, 𝕜)) (B := C(OnePoint Y, 𝕜))
      (ZeroAtInftyContinuousMap.unitizationAlgEquiv Y 𝕜 𝕜))

/-- `unitizationZeroAtInftyHomeoEval Y 𝕜` sends `∞` to `Unitization.augmentation 𝕜 C₀(Y, 𝕜)`. -/
@[simp]
theorem unitizationZeroAtInftyHomeoEval_apply_infty :
    unitizationZeroAtInftyHomeoEval Y 𝕜 ∞ = Unitization.augmentation 𝕜 C₀(Y, 𝕜) := by
  ext u
  simp [unitizationZeroAtInftyHomeoEval]

/-- `(unitizationZeroAtInftyHomeoEval Y 𝕜).symm` sends `Unitization.augmentation 𝕜 C₀(Y, 𝕜)` to `∞`.
-/
@[simp]
theorem unitizationZeroAtInftyHomeoEval_symm_apply_augmentation :
    (unitizationZeroAtInftyHomeoEval Y 𝕜).symm (Unitization.augmentation 𝕜 C₀(Y, 𝕜)) = ∞ := by
  rw [Homeomorph.symm_apply_eq]
  exact (unitizationZeroAtInftyHomeoEval_apply_infty Y 𝕜).symm

/-- `unitizationZeroAtInftyHomeoEval Y 𝕜` evaluates `u` at a finite point `y : Y` as
`u.fst + u.snd y`. -/
@[simp]
theorem unitizationZeroAtInftyHomeoEval_apply_coe (y : Y) (u : Unitization 𝕜 C₀(Y, 𝕜)) :
    unitizationZeroAtInftyHomeoEval Y 𝕜 y u = u.fst + u.snd y := by
  simp [unitizationZeroAtInftyHomeoEval]

/-- Natural homeomorphism between a weakly locally compact Hausdorff space `Y` and
`characterSpace 𝕜 C₀(Y, 𝕜)` given by point evaluation `y ↦ (f ↦ f y)`. This is the nonunital
counterpart of `WeakDual.CharacterSpace.homeoEval`. -/
noncomputable def zeroAtInftyHomeoEval :
    Y ≃ₜ characterSpace 𝕜 C₀(Y, 𝕜) :=
  OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph.trans <|
    ((unitizationZeroAtInftyHomeoEval Y 𝕜).subtype fun p ↦ by
      rw [← OnePoint.compl_infty, Set.mem_compl_singleton_iff,
        ← unitizationZeroAtInftyHomeoEval_apply_infty Y 𝕜]
      exact (unitizationZeroAtInftyHomeoEval Y 𝕜).injective.ne_iff.symm).trans
      (unitizationComplAugmentationHomeomorph 𝕜 C₀(Y, 𝕜)).symm

/-- `zeroAtInftyHomeoEval Y 𝕜 y` evaluates `f : C₀(Y, 𝕜)` at `y`. -/
@[simp]
theorem zeroAtInftyHomeoEval_apply (y : Y) (f : C₀(Y, 𝕜)) :
    zeroAtInftyHomeoEval Y 𝕜 y f = f y := by
  simp [zeroAtInftyHomeoEval]

/-- On finite points `y : Y`, `unitizationZeroAtInftyHomeoEval Y 𝕜 y` is the unital extension of
`zeroAtInftyHomeoEval Y 𝕜 y`. -/
theorem unitizationZeroAtInftyHomeoEval_coe_eq_unitizationExtend (y : Y) :
    unitizationZeroAtInftyHomeoEval Y 𝕜 y =
      (unitizationExtend (zeroAtInftyHomeoEval Y 𝕜 y)).1 := by
  ext u
  simp

/-- On a punctured character `φ` of `Unitization 𝕜 C₀(Y, 𝕜)`,
`(unitizationZeroAtInftyHomeoEval Y 𝕜).symm φ.1` equals
`(zeroAtInftyHomeoEval Y 𝕜).symm (unitizationRestrict φ)`. -/
@[simp]
theorem unitizationZeroAtInftyHomeoEval_symm_apply_coe
    (φ : {φ : characterSpace 𝕜 (Unitization 𝕜 C₀(Y, 𝕜)) //
      φ ≠ Unitization.augmentation 𝕜 C₀(Y, 𝕜)}) :
    (unitizationZeroAtInftyHomeoEval Y 𝕜).symm φ.1 =
      ((zeroAtInftyHomeoEval Y 𝕜).symm (unitizationRestrict φ) : OnePoint Y) := by
  rw [Homeomorph.symm_apply_eq, unitizationZeroAtInftyHomeoEval_coe_eq_unitizationExtend,
    Homeomorph.apply_symm_apply, unitizationExtend_unitizationRestrict]

/-- Extending `zeroAtInftyHomeoEval Y 𝕜` to `OnePoint Y` and composing with
`onePointHomeomorphUnitization 𝕜 C₀(Y, 𝕜)` recovers `unitizationZeroAtInftyHomeoEval Y 𝕜`. -/
theorem onePointCongr_zeroAtInftyHomeoEval_trans_onePointHomeomorphUnitization :
    (zeroAtInftyHomeoEval Y 𝕜).onePointCongr.trans
        (onePointHomeomorphUnitization 𝕜 C₀(Y, 𝕜)) =
      unitizationZeroAtInftyHomeoEval Y 𝕜 := by
  ext p u
  induction p using OnePoint.rec with
  | infty => simp
  | coe y => simp

/-- Applying `TauCeti.nonUnitalGelfandStarTransform` to `C₀(Y, ℂ)` and reindexing along
`WeakDual.CharacterSpace.zeroAtInftyHomeoEval Y ℂ` recovers the identity star-algebra equivalence
on `C₀(Y, ℂ)`. -/
@[simp]
theorem nonUnitalGelfandStarTransform_zeroAtInfty_trans_congrLeft :
    (TauCeti.nonUnitalGelfandStarTransform C₀(Y, ℂ)).trans
        (ZeroAtInftyContinuousMap.congrLeftStarAlgEquiv ℂ ℂ (zeroAtInftyHomeoEval Y ℂ).symm) =
      StarAlgEquiv.refl ℂ C₀(Y, ℂ) := by
  ext f y
  simp

end ZeroAtInftyEval

end WeakDual.CharacterSpace
