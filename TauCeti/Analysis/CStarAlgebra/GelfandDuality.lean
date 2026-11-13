/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Analysis.Normed.Algebra.Character.Pullback
public import TauCeti.Analysis.Normed.Algebra.Character.Unitization

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
  `TauCeti.compactSpace_characterSpace_iff_exists_mul_id`, and
  `TauCeti.isOpen_singleton_augmentation_iff_exists_mul_id`: when `A` is unital, the nonunital
  Gelfand `⋆`-transform agrees with `gelfandStarTransform A` lifted to `C₀`, and conversely
  `characterSpace ℂ A` is compact (equivalently `{ε}` is open in `characterSpace ℂ A⁺¹`) if and
  only if `A` has a two-sided multiplicative identity;
* `WeakDual.CharacterSpace.onePointHomeoUnitizationZeroAtInfty` and
  `WeakDual.CharacterSpace.zeroAtInftyHomeoEval`: for any weakly locally compact Hausdorff space
  `Y` and `RCLike` scalar field `𝕜`, point evaluation identifies `OnePoint Y` with
  `characterSpace 𝕜 (Unitization 𝕜 C₀(Y, 𝕜))` (sending `∞` to `ε`) and `Y` with
  `characterSpace 𝕜 C₀(Y, 𝕜)`, recovering the identity `⋆`-automorphism on `C₀(Y, ℂ)`.

## References

* J. B. Conway, *A Course in Functional Analysis*, §VIII.2.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Theorem 2.1.10.
-/

public section

open Filter Function Set Topology OnePoint WeakDual
open scoped CStarAlgebra ZeroAtInfty

namespace WeakDual.CharacterSpace

/-- `WeakDual.CharacterSpace.homeoEval` evaluates a continuous function at the given point. -/
@[simp]
theorem homeoEval_apply {X 𝕜 : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [RCLike 𝕜] (x : X) (f : C(X, 𝕜)) :
    homeoEval X 𝕜 x f = f x := (rfl)

end WeakDual.CharacterSpace

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
  refine ⟨?_, fun hF => ?_⟩
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact gelfandStarTransform_unitization_inr_apply_augmentation a
  · set u : A⁺¹ := (gelfandStarTransform A⁺¹).symm F
    have hu : u.fst = 0 := by
      rw [← gelfandStarTransform_unitization_apply_augmentation u,
        StarAlgEquiv.apply_symm_apply, hF]
    refine ⟨u, ⟨u.snd, ?_⟩, (gelfandStarTransform A⁺¹).apply_symm_apply F⟩
    ext
    · exact (Unitization.fst_inr ℂ u.snd).trans hu.symm
    · simp

/-- Set-level form of `map_gelfandStarTransform_inrRange`: the Gelfand transform of `A⁺¹` carries
`Set.range (Unitization.inr : A → A⁺¹)` onto `{F ∈ C(characterSpace ℂ A⁺¹, ℂ) : F ε = 0}`. -/
theorem image_gelfandStarTransform_range_inr :
    gelfandStarTransform A⁺¹ '' Set.range (Unitization.inr : A → A⁺¹) =
      {F : C(characterSpace ℂ A⁺¹, ℂ) | F (Unitization.augmentation ℂ A) = 0} := by
  ext F
  have hF := SetLike.ext_iff.mp map_gelfandStarTransform_inrRange F
  rw [NonUnitalStarSubalgebra.mem_map, ContinuousMap.mem_evalKerSubalgebra] at hF
  refine ⟨?_, fun h0 => ?_⟩
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact gelfandStarTransform_unitization_inr_apply_augmentation a
  · obtain ⟨u, hu, rfl⟩ := hF.mpr h0
    rw [NonUnitalStarAlgHom.mem_range] at hu
    obtain ⟨a, rfl⟩ := hu
    exact ⟨a, ⟨a, rfl⟩, rfl⟩

variable (A) in
/-- **Nonunital Gelfand transform via the punctured unitization character space.** Restricting
`gelfandStarTransform A⁺¹ (a : A⁺¹)` to `{φ : characterSpace ℂ A⁺¹ // φ ≠ ε}` identifies `A`
`⋆`-isomorphically (and isometrically via `StarAlgEquiv.isometry`) with
`C₀({φ : characterSpace ℂ A⁺¹ // φ ≠ Unitization.augmentation ℂ A}, ℂ)`, with inverse given by
extension by zero across the augmentation character. -/
noncomputable def puncturedGelfandStarTransform :
    A ≃⋆ₐ[ℂ] C₀({φ : characterSpace ℂ A⁺¹ // φ ≠ Unitization.augmentation ℂ A}, ℂ) where
  toFun a :=
    (gelfandStarTransform A⁺¹ (a : A⁺¹)).restrictComplSingleton
      (gelfandStarTransform_unitization_inr_apply_augmentation a)
  invFun g := ((gelfandStarTransform A⁺¹).symm g.extendZero).snd
  left_inv a := by
    dsimp only
    rw [ZeroAtInftyContinuousMap.extendZero_restrictComplSingleton,
      StarAlgEquiv.symm_apply_apply, Unitization.snd_inr]
  right_inv g := by
    dsimp only
    set u : A⁺¹ := (gelfandStarTransform A⁺¹).symm g.extendZero
    have hfst : u.fst = 0 := by
      rw [← gelfandStarTransform_unitization_apply_augmentation u,
        StarAlgEquiv.apply_symm_apply]
      exact g.extendZero_apply_self
    have hu : (u.snd : A⁺¹) = u := by
      ext
      · exact (Unitization.fst_inr ℂ u.snd).trans hfst.symm
      · simp
    ext φ
    rw [ContinuousMap.restrictComplSingleton_apply, hu, StarAlgEquiv.apply_symm_apply,
      g.extendZero_apply_coe]
  map_smul' c a := by ext φ; simp
  map_add' a b := by ext φ; simp
  map_mul' a b := by ext φ; simp
  map_star' a := by
    ext φ
    rw [ContinuousMap.restrictComplSingleton_apply, Unitization.inr_star, map_star]
    simp

@[simp]
theorem puncturedGelfandStarTransform_apply (a : A)
    (φ : {φ : characterSpace ℂ A⁺¹ // φ ≠ Unitization.augmentation ℂ A}) :
    puncturedGelfandStarTransform A a φ = φ.1 (a : A⁺¹) := by
  simp [puncturedGelfandStarTransform]

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

@[simp]
theorem nonUnitalGelfandStarTransform_apply (a : A) (χ : characterSpace ℂ A) :
    nonUnitalGelfandStarTransform A a χ = χ a := by
  simp [nonUnitalGelfandStarTransform]

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
if `A` has a two-sided multiplicative identity. -/
theorem compactSpace_characterSpace_iff_exists_mul_id (A : Type*) [NonUnitalCommCStarAlgebra A] :
    CompactSpace (characterSpace ℂ A) ↔ ∃ e : A, ∀ a : A, e * a = a ∧ a * e = a := by
  refine ⟨fun _ => ?_, ?_⟩
  · let oneC₀ : C₀(characterSpace ℂ A, ℂ) :=
      ContinuousMap.liftZeroAtInftyStarAlgEquiv ℂ (characterSpace ℂ A) ℂ 1
    refine ⟨(nonUnitalGelfandStarTransform A).symm oneC₀, fun a => ?_⟩
    have hleft : (nonUnitalGelfandStarTransform A).symm oneC₀ * a = a := by
      apply EquivLike.injective (nonUnitalGelfandStarTransform A)
      rw [map_mul, StarAlgEquiv.apply_symm_apply]
      ext χ
      simp [oneC₀]
    exact ⟨hleft, (mul_comm a _).trans hleft⟩
  · rintro ⟨e, he⟩
    let f : C₀(characterSpace ℂ A, ℂ) := nonUnitalGelfandStarTransform A e
    have hf : ∀ χ : characterSpace ℂ A, f χ = 1 := fun χ => by
      have hex : ∃ a : A, χ a ≠ 0 := by
        by_contra! h0
        exact χ.prop.1 (ContinuousLinearMap.ext h0)
      obtain ⟨a, ha⟩ := hex
      refine mul_right_cancel₀ ha ?_
      calc
        f χ * χ a = χ (e * a) := by simp [f, ← map_mul]
        _ = 1 * χ a := by rw [(he a).1, one_mul]
    obtain ⟨K, hK, hsub⟩ :=
      Filter.mem_cocompact'.mp (zero_at_infty f (Metric.ball_mem_nhds 0 zero_lt_one))
    have hK_univ : K = Set.univ :=
      Set.eq_univ_of_forall fun χ =>
        hsub fun hball => by
          have hlt : dist (f χ) 0 < 1 := Metric.mem_ball.mp hball
          simp [hf χ] at hlt
    exact ⟨hK_univ ▸ hK⟩

/-- In a nonunital commutative complex C⋆-algebra `A`, the augmentation character is isolated in
`characterSpace ℂ A⁺¹` if and only if `A` has a two-sided multiplicative identity. -/
theorem isOpen_singleton_augmentation_iff_exists_mul_id (A : Type*)
    [NonUnitalCommCStarAlgebra A] :
    IsOpen ({Unitization.augmentation ℂ A} : Set (characterSpace ℂ A⁺¹)) ↔
      ∃ e : A, ∀ a : A, e * a = a ∧ a * e = a := by
  rw [← compactSpace_complSingleton_iff_isOpen_singleton,
    ← compactSpace_characterSpace_iff_exists_mul_id]
  exact
    ⟨fun _ =>
      (WeakDual.CharacterSpace.unitizationComplAugmentationHomeomorph ℂ A).symm.compactSpace,
     fun _ =>
      (WeakDual.CharacterSpace.unitizationComplAugmentationHomeomorph ℂ A).compactSpace⟩

end UnitalComparison

end TauCeti

namespace WeakDual.CharacterSpace

section ZeroAtInftyEval

variable (Y 𝕜 : Type*) [TopologicalSpace Y] [WeaklyLocallyCompactSpace Y] [T2Space Y] [RCLike 𝕜]

/-- Point evaluation identifies `OnePoint Y` with the character space of
`Unitization 𝕜 C₀(Y, 𝕜)`, sending `∞` to `Unitization.augmentation 𝕜 C₀(Y, 𝕜)` and `(y : Y)` to
`u ↦ u.fst + u.snd y`. -/
noncomputable def onePointHomeoUnitizationZeroAtInfty :
    OnePoint Y ≃ₜ characterSpace 𝕜 (Unitization 𝕜 C₀(Y, 𝕜)) :=
  (homeoEval (OnePoint Y) 𝕜).trans
    (AlgEquiv.characterSpaceHomeomorph (A := Unitization 𝕜 C₀(Y, 𝕜)) (B := C(OnePoint Y, 𝕜))
      (ZeroAtInftyContinuousMap.unitizationAlgEquiv Y 𝕜 𝕜))

@[simp]
theorem onePointHomeoUnitizationZeroAtInfty_apply_infty :
    onePointHomeoUnitizationZeroAtInfty Y 𝕜 ∞ = Unitization.augmentation 𝕜 C₀(Y, 𝕜) := by
  ext u
  simp [onePointHomeoUnitizationZeroAtInfty]

@[simp]
theorem onePointHomeoUnitizationZeroAtInfty_apply_coe (y : Y) (u : Unitization 𝕜 C₀(Y, 𝕜)) :
    onePointHomeoUnitizationZeroAtInfty Y 𝕜 y u = u.fst + u.snd y := by
  simp [onePointHomeoUnitizationZeroAtInfty]

private theorem onePointHomeoUnitizationZeroAtInfty_coe_ne_augmentation (y : Y) :
    onePointHomeoUnitizationZeroAtInfty Y 𝕜 y ≠ Unitization.augmentation 𝕜 C₀(Y, 𝕜) := by
  rw [← onePointHomeoUnitizationZeroAtInfty_apply_infty Y 𝕜]
  exact (onePointHomeoUnitizationZeroAtInfty Y 𝕜).injective.ne (OnePoint.coe_ne_infty y)

private theorem onePointHomeoUnitizationZeroAtInfty_symm_ne_infty (χ : characterSpace 𝕜 C₀(Y, 𝕜)) :
    (onePointHomeoUnitizationZeroAtInfty Y 𝕜).symm
      (unitizationComplAugmentationHomeomorph 𝕜 C₀(Y, 𝕜) χ).1 ≠ ∞ := by
  intro h
  apply (unitizationComplAugmentationHomeomorph 𝕜 C₀(Y, 𝕜) χ).2
  have h' := congrArg (onePointHomeoUnitizationZeroAtInfty Y 𝕜) h
  simpa using h'

/-- Natural homeomorphism between a weakly locally compact Hausdorff space `Y` and
`characterSpace 𝕜 C₀(Y, 𝕜)` given by point evaluation `y ↦ (f ↦ f y)`. This is the nonunital
counterpart of `WeakDual.CharacterSpace.homeoEval`. -/
noncomputable def zeroAtInftyHomeoEval :
    Y ≃ₜ characterSpace 𝕜 C₀(Y, 𝕜) where
  toFun y :=
    (unitizationComplAugmentationHomeomorph 𝕜 C₀(Y, 𝕜)).symm
      ⟨onePointHomeoUnitizationZeroAtInfty Y 𝕜 y,
        onePointHomeoUnitizationZeroAtInfty_coe_ne_augmentation Y 𝕜 y⟩
  invFun χ :=
    (OnePoint.ne_infty_iff_exists.mp
      (onePointHomeoUnitizationZeroAtInfty_symm_ne_infty Y 𝕜 χ)).choose
  left_inv y := by
    apply OnePoint.coe_injective
    have hchoose :=
      (OnePoint.ne_infty_iff_exists.mp
        (onePointHomeoUnitizationZeroAtInfty_symm_ne_infty Y 𝕜
          ((unitizationComplAugmentationHomeomorph 𝕜 C₀(Y, 𝕜)).symm
            ⟨onePointHomeoUnitizationZeroAtInfty Y 𝕜 y,
              onePointHomeoUnitizationZeroAtInfty_coe_ne_augmentation Y 𝕜 y⟩))).choose_spec
    rw [hchoose]
    simp
  right_inv χ := by
    apply (unitizationComplAugmentationHomeomorph 𝕜 C₀(Y, 𝕜)).injective
    apply Subtype.ext
    have hchoose :=
      (OnePoint.ne_infty_iff_exists.mp
        (onePointHomeoUnitizationZeroAtInfty_symm_ne_infty Y 𝕜 χ)).choose_spec
    dsimp only
    rw [Homeomorph.apply_symm_apply]
    dsimp only
    rw [hchoose, Homeomorph.apply_symm_apply]
  continuous_toFun :=
    (unitizationComplAugmentationHomeomorph 𝕜 C₀(Y, 𝕜)).symm.continuous.comp
      (((onePointHomeoUnitizationZeroAtInfty Y 𝕜).continuous.comp
        OnePoint.continuous_coe).subtype_mk _)
  continuous_invFun := by
    rw [OnePoint.isOpenEmbedding_coe.isInducing.continuous_iff]
    have hfun :
        (OnePoint.some ∘ fun χ : characterSpace 𝕜 C₀(Y, 𝕜) =>
          (OnePoint.ne_infty_iff_exists.mp
            (onePointHomeoUnitizationZeroAtInfty_symm_ne_infty Y 𝕜 χ)).choose) =
          fun χ => (onePointHomeoUnitizationZeroAtInfty Y 𝕜).symm
            (unitizationComplAugmentationHomeomorph 𝕜 C₀(Y, 𝕜) χ).1 := by
      ext χ
      exact (OnePoint.ne_infty_iff_exists.mp
        (onePointHomeoUnitizationZeroAtInfty_symm_ne_infty Y 𝕜 χ)).choose_spec
    rw [hfun]
    exact (onePointHomeoUnitizationZeroAtInfty Y 𝕜).symm.continuous.comp
      (continuous_subtype_val.comp (unitizationComplAugmentationHomeomorph 𝕜 C₀(Y, 𝕜)).continuous)

@[simp]
theorem zeroAtInftyHomeoEval_apply (y : Y) (f : C₀(Y, 𝕜)) :
    zeroAtInftyHomeoEval Y 𝕜 y f = f y := by
  simp [zeroAtInftyHomeoEval]

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
