/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Analysis.Normed.Algebra.Character.Unitization

/-!
# Nonunital Gelfand duality for commutative C⋆-algebras

For a nonunital commutative complex C⋆-algebra `A`, its minimal unitization `A⁺¹` is a unital
commutative C⋆-algebra (`Unitization.instCommCStarAlgebra`), so the unital Gelfand transform
`gelfandStarTransform A⁺¹ : A⁺¹ ≃⋆ₐ[ℂ] C(characterSpace ℂ A⁺¹, ℂ)` identifies `A⁺¹` with continuous
functions on the compact Hausdorff character space `characterSpace ℂ A⁺¹`. Under this equivalence:

* the image of `A` along `Unitization.inr` is precisely the closed maximal `⋆`-ideal of functions
  vanishing at the augmentation character `Unitization.fstCharacter ℂ A`
  (`TauCeti.coe_range_gelfandStarTransform_comp_inr`);
* restricting to the punctured character space `{Unitization.fstCharacter ℂ A}ᶜ` gives an isometric
  `⋆`-algebra equivalence
  `TauCeti.puncturedGelfandStarTransform A : A ≃⋆ₐ[ℂ] C₀({fstCharacter ℂ A}ᶜ, ℂ)`;
* transporting along `Unitization.characterSpaceComplFstHomeomorph ℂ A` yields the intrinsic
  nonunital Gelfand `⋆`-isomorphism
  `TauCeti.nonUnitalGelfandStarTransform A : A ≃⋆ₐ[ℂ] C₀(characterSpace ℂ A, ℂ)`
  evaluating to `(a, φ) ↦ φ a` (isometric by `StarAlgEquiv.isometry`).

When `A` already has an identity, `nonUnitalGelfandStarTransform A` agrees with
`gelfandStarTransform A` composed with `ContinuousMap.liftZeroAtInftyStarAlgEquiv ℂ ℂ`.
Conversely, for any locally compact Hausdorff space `X` and `RCLike` scalar field `𝕜`, point
evaluation gives a canonical homeomorphism
`WeakDual.CharacterSpace.homeoEvalZeroAtInfty X 𝕜 : X ≃ₜ characterSpace 𝕜 C₀(X, 𝕜)`, deduced from
`WeakDual.CharacterSpace.homeoEval (OnePoint X) 𝕜` via the unitization equivalence
`Unitization 𝕜 C₀(X, 𝕜) ≃⋆ₐ[𝕜] C(OnePoint X, 𝕜)`.

## Main declarations

* `WeakDual.CharacterSpace.compHomeomorph`: homeomorphism `characterSpace 𝕜 B ≃ₜ characterSpace 𝕜 A`
  induced by `A ≃⋆ₐ[𝕜] B`.
* `WeakDual.CharacterSpace.homeoEvalZeroAtInfty`: `X ≃ₜ characterSpace 𝕜 C₀(X, 𝕜)` for locally
  compact Hausdorff `X` and `[RCLike 𝕜]`.
* `TauCeti.coe_range_gelfandStarTransform_comp_inr`: the Gelfand image of `A` inside
  `C(characterSpace ℂ A⁺¹, ℂ)` is `{F | F (Unitization.fstCharacter ℂ A) = 0}`.
* `TauCeti.puncturedGelfandStarTransform`: `A ≃⋆ₐ[ℂ] C₀({Unitization.fstCharacter ℂ A}ᶜ, ℂ)`.
* `TauCeti.nonUnitalGelfandStarTransform`: `A ≃⋆ₐ[ℂ] C₀(characterSpace ℂ A, ℂ)`.
* `TauCeti.nonUnitalGelfandStarTransform_eq_gelfandStarTransform`: compatibility with
  `gelfandStarTransform` when `A` is unital.

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press (1990), Theorem 2.1.10.
* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), §VIII.2.
-/

public section

open WeakDual
open scoped CStarAlgebra OnePoint ZeroAtInfty

namespace WeakDual.CharacterSpace

section CompHomeomorph

variable {𝕜 A B : Type*} [NontriviallyNormedField 𝕜]
  [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] [StarRing A]
  [NormedRing B] [NormedAlgebra 𝕜 B] [CompleteSpace B] [StarRing B]

/-- A `⋆`-algebra equivalence between unital Banach `⋆`-algebras induces a homeomorphism of
character spaces by precomposition. -/
noncomputable def compHomeomorph (e : A ≃⋆ₐ[𝕜] B) :
    characterSpace 𝕜 B ≃ₜ characterSpace 𝕜 A where
  toFun := compContinuousMap e.toStarAlgHom
  invFun := compContinuousMap e.symm.toStarAlgHom
  left_inv φ := ext fun b ↦ by simp
  right_inv ψ := ext fun a ↦ by simp
  continuous_toFun := map_continuous _
  continuous_invFun := map_continuous _

/-- `compHomeomorph e` acts on a character `φ` by precomposing with `e`. -/
@[simp]
theorem compHomeomorph_apply_apply (e : A ≃⋆ₐ[𝕜] B) (φ : characterSpace 𝕜 B) (a : A) :
    compHomeomorph e φ a = φ (e a) := by
  simp [compHomeomorph]

/-- The inverse of `compHomeomorph e` is `compHomeomorph e.symm`. -/
@[simp]
theorem compHomeomorph_symm (e : A ≃⋆ₐ[𝕜] B) :
    (compHomeomorph e).symm = compHomeomorph e.symm := by
  rfl

end CompHomeomorph

section ZeroAtInfty

/-- `WeakDual.CharacterSpace.homeoEval X 𝕜` evaluates a continuous function `f : C(X, 𝕜)` at `x`. -/
@[simp]
theorem homeoEval_apply_apply {X 𝕜 : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [RCLike 𝕜] (x : X) (f : C(X, 𝕜)) :
    homeoEval X 𝕜 x f = f x := by
  rfl

/-- For any locally compact Hausdorff space `X` and `RCLike` scalar field `𝕜`, point evaluation
identifies `X` homeomorphically with `characterSpace 𝕜 C₀(X, 𝕜)`, extending
`WeakDual.CharacterSpace.homeoEval` from compact to locally compact Hausdorff spaces via
`Unitization 𝕜 C₀(X, 𝕜) ≃⋆ₐ[𝕜] C(OnePoint X, 𝕜)`. -/
noncomputable def homeoEvalZeroAtInfty (X 𝕜 : Type*) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] [RCLike 𝕜] :
    X ≃ₜ characterSpace 𝕜 C₀(X, 𝕜) :=
  let H : OnePoint X ≃ₜ characterSpace 𝕜 (Unitization 𝕜 C₀(X, 𝕜)) :=
    (homeoEval (OnePoint X) 𝕜).trans
      (compHomeomorph (A := Unitization 𝕜 C₀(X, 𝕜)) (B := C(OnePoint X, 𝕜))
        (ZeroAtInftyContinuousMap.unitizationStarAlgEquiv X 𝕜 𝕜))
  have hH : H ∞ = Unitization.fstCharacter 𝕜 C₀(X, 𝕜) := by
    ext u
    simp [H]
  let eX : X ≃ₜ ({∞}ᶜ : Set (OnePoint X)) :=
    OnePoint.isOpenEmbedding_coe.toIsEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr OnePoint.compl_infty.symm)
  (eX.trans (H.sets (t := {Unitization.fstCharacter 𝕜 C₀(X, 𝕜)}ᶜ)
    (by ext p; simp [← hH, H.injective.eq_iff]))).trans
    (Unitization.characterSpaceComplFstHomeomorph 𝕜 C₀(X, 𝕜)).symm

/-- `homeoEvalZeroAtInfty X 𝕜` sends `x : X` to point evaluation at `x` on `C₀(X, 𝕜)`. -/
@[simp]
theorem homeoEvalZeroAtInfty_apply_apply {X 𝕜 : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] [RCLike 𝕜] (x : X) (f : C₀(X, 𝕜)) :
    homeoEvalZeroAtInfty X 𝕜 x f = f x := by
  simp [homeoEvalZeroAtInfty, Homeomorph.setCongr]

end ZeroAtInfty

end WeakDual.CharacterSpace

namespace TauCeti

section NonUnitalCommCStarAlgebra

variable (A : Type*) [NonUnitalCommCStarAlgebra A]

/-- Under `gelfandStarTransform A⁺¹`, the image of `A` along `Unitization.inr` is precisely the set
of continuous functions on `characterSpace ℂ A⁺¹` vanishing at `Unitization.fstCharacter ℂ A`. -/
theorem coe_range_gelfandStarTransform_comp_inr :
    (((gelfandStarTransform A⁺¹).toNonUnitalStarAlgHom.comp
        (Unitization.inrNonUnitalStarAlgHom ℂ A)).range : Set C(characterSpace ℂ A⁺¹, ℂ)) =
      {F : C(characterSpace ℂ A⁺¹, ℂ) | F (Unitization.fstCharacter ℂ A) = 0} := by
  ext F
  simp only [SetLike.mem_coe, NonUnitalStarAlgHom.mem_range, NonUnitalStarAlgHom.coe_comp,
    Function.comp_apply, Unitization.inrNonUnitalStarAlgHom_apply, Set.mem_ofPred_eq]
  refine ⟨?_, fun hF ↦ ?_⟩
  · rintro ⟨a, rfl⟩
    exact (Unitization.fstCharacter_inr a)
  · have hfst : ((gelfandStarTransform A⁺¹).symm F).fst = 0 := by
      have h := congr($(gelfandStarTransform A⁺¹ |>.apply_symm_apply F)
        (Unitization.fstCharacter ℂ A))
      simpa [hF] using h
    obtain ⟨a, ha⟩ := Unitization.mem_range_inr_iff.mpr hfst
    refine ⟨a, ?_⟩
    exact ha.symm ▸ (gelfandStarTransform A⁺¹).apply_symm_apply F

/-- Auxiliary `⋆`-algebra equivalence identifying `A` with the maximal `⋆`-ideal of functions in
`C(characterSpace ℂ A⁺¹, ℂ)` vanishing at `Unitization.fstCharacter ℂ A`. -/
private noncomputable def gelfandStarTransformIdealEquiv :
    A ≃⋆ₐ[ℂ] ContinuousMap.idealOfSetStarSubalgebra ℂ ℂ
      ({Unitization.fstCharacter ℂ A}ᶜ : Set (characterSpace ℂ A⁺¹)) where
  toFun a := ⟨gelfandStarTransform A⁺¹ a, by simp⟩
  invFun F := ((gelfandStarTransform A⁺¹).symm F.1).snd
  left_inv a := by simp
  right_inv F := Subtype.ext <| by
    dsimp only
    have hF : F.1 (Unitization.fstCharacter ℂ A) = 0 :=
      (ContinuousMap.mem_idealOfSetStarSubalgebra_compl_singleton _ F.1).mp F.2
    have hfst : ((gelfandStarTransform A⁺¹).symm F.1).fst = 0 := by
      have h := congr($(gelfandStarTransform A⁺¹ |>.apply_symm_apply F.1)
        (Unitization.fstCharacter ℂ A))
      simpa [hF] using h
    have hx : (((gelfandStarTransform A⁺¹).symm F.1).snd : A⁺¹) =
        (gelfandStarTransform A⁺¹).symm F.1 :=
      Unitization.ext ((Unitization.fst_inr ℂ _).trans hfst.symm) (Unitization.snd_inr ℂ _)
    rw [hx, StarAlgEquiv.apply_symm_apply]
  map_mul' a b := Subtype.ext <| ContinuousMap.ext fun ψ ↦ by simp [Unitization.inr_mul]
  map_add' a b := Subtype.ext <| ContinuousMap.ext fun ψ ↦ by simp [Unitization.inr_add]
  map_star' a := Subtype.ext <| ContinuousMap.ext fun ψ ↦ by simp [Unitization.inr_star, map_star]
  map_smul' r a := Subtype.ext <| ContinuousMap.ext fun ψ ↦ by simp [Unitization.inr_smul]

/-- The **punctured-unitization Gelfand `⋆`-transform** of a nonunital commutative C⋆-algebra `A`,
identifying `A` with functions vanishing at infinity on the punctured unitization character space
`{Unitization.fstCharacter ℂ A}ᶜ`. By `StarAlgEquiv.isometry`, this equivalence is isometric. -/
noncomputable def puncturedGelfandStarTransform :
    A ≃⋆ₐ[ℂ] C₀(({Unitization.fstCharacter ℂ A}ᶜ : Set (characterSpace ℂ A⁺¹)), ℂ) :=
  (gelfandStarTransformIdealEquiv A).trans
    (ContinuousMap.restrictComplSingletonStarAlgEquiv ℂ ℂ (Unitization.fstCharacter ℂ A))

/-- `puncturedGelfandStarTransform A a` evaluates at `ψ ∈ {fstCharacter ℂ A}ᶜ` to `ψ.1 a`. -/
@[simp]
theorem puncturedGelfandStarTransform_apply {A : Type*} [NonUnitalCommCStarAlgebra A] (a : A)
    (ψ : ({Unitization.fstCharacter ℂ A}ᶜ : Set (characterSpace ℂ A⁺¹))) :
    puncturedGelfandStarTransform A a ψ = ψ.1 a := by
  simp [puncturedGelfandStarTransform, gelfandStarTransformIdealEquiv]

/-- Extending `puncturedGelfandStarTransform A a` by `0` at `fstCharacter ℂ A` recovers
`gelfandStarTransform A⁺¹ a`. -/
@[simp]
theorem extendComplSingleton_puncturedGelfandStarTransform {A : Type*}
    [NonUnitalCommCStarAlgebra A] (a : A) :
    (puncturedGelfandStarTransform A a).extendComplSingleton = gelfandStarTransform A⁺¹ a := by
  ext ψ
  rcases eq_or_ne ψ (Unitization.fstCharacter ℂ A) with rfl | hψ
  · simp
  · simp [ZeroAtInftyContinuousMap.extendComplSingleton_of_ne _ hψ]

/-- The **nonunital Gelfand `⋆`-transform** of a nonunital commutative complex C⋆-algebra `A`,
identifying `A` `⋆`-isomorphically (and isometrically, via `StarAlgEquiv.isometry`) with
`C₀(characterSpace ℂ A, ℂ)`. -/
noncomputable def nonUnitalGelfandStarTransform :
    A ≃⋆ₐ[ℂ] C₀(characterSpace ℂ A, ℂ) :=
  (puncturedGelfandStarTransform A).trans
    ((Unitization.characterSpaceComplFstHomeomorph ℂ A).compZeroAtInftyStarAlgEquiv' ℂ ℂ)

/-- `nonUnitalGelfandStarTransform A a` evaluates at `φ : characterSpace ℂ A` to `φ a`. -/
@[simp]
theorem nonUnitalGelfandStarTransform_apply {A : Type*} [NonUnitalCommCStarAlgebra A] (a : A)
    (φ : characterSpace ℂ A) :
    nonUnitalGelfandStarTransform A a φ = φ a := by
  simp [nonUnitalGelfandStarTransform]

/-- Forgetting the `⋆`-equivalence structure on `nonUnitalGelfandStarTransform A` recovers the
Banach-algebra `nonUnitalGelfandTransform ℂ A`. -/
@[simp]
theorem toNonUnitalAlgHom_nonUnitalGelfandStarTransform :
    (nonUnitalGelfandStarTransform A).toNonUnitalStarAlgHom.toNonUnitalAlgHom =
      nonUnitalGelfandTransform ℂ A := by
  ext a φ
  simp

end NonUnitalCommCStarAlgebra

section UnitalCompatibility

/-- When `A` is already a unital commutative C⋆-algebra, `characterSpace ℂ A` is compact and
`nonUnitalGelfandStarTransform A` agrees with `gelfandStarTransform A` followed by the canonical
identification `C(characterSpace ℂ A, ℂ) ≃⋆ₐ[ℂ] C₀(characterSpace ℂ A, ℂ)`. -/
theorem nonUnitalGelfandStarTransform_eq_gelfandStarTransform (A : Type*) [CommCStarAlgebra A] :
    nonUnitalGelfandStarTransform A =
      (gelfandStarTransform A).trans (ContinuousMap.liftZeroAtInftyStarAlgEquiv ℂ ℂ) := by
  ext a φ
  simp

end UnitalCompatibility

end TauCeti
