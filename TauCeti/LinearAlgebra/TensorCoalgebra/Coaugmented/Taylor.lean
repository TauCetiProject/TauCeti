/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Extension

/-!
# Taylor correspondence for coaugmentation-preserving coderivations

A signed coderivation of the coaugmented tensor coalgebra annihilating the empty word
is precisely the extension of a signed coderivation of the reduced tensor coalgebra.
Consequently it is determined by its positive-arity Taylor components. This identifies
the reduced and coaugmented descriptions of uncurved bar differentials.

The co-Leibniz rule itself forces the counit of every value to vanish; this is not an
extra hypothesis. Annihilation of the empty word, in contrast, is essential to the
uncurved correspondence. The twist parameter specifies the Koszul sign, independently
of homogeneity, as in the reduced correspondence.

## Main declarations

* `gradedCoderivEquivTaylor`: the linear equivalence with positive-arity Taylor maps.
* `IsGradedCoderivation.eq_extendReduced_gradedCoderiv`: reconstruction from those maps.
* `IsGradedCoderivation.isHomogeneous_iff`: homogeneity is detected on Taylor maps.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
-/

public section

open scoped TensorProduct

namespace TauCeti
namespace TensorWords

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {G : InternalGrading R M} {q : ℤ}
variable {b : TensorWords R M →ₗ[R] TensorWords R M}

/-- A signed coderivation annihilating the empty word restricts to a signed coderivation
of reduced tensor words. -/
theorem IsGradedCoderivation.restrictReduced (hb : IsGradedCoderivation G q b)
    (h₁ : b 1 = 0) :
    ReducedTensorWords.IsGradedCoderivation G q (TensorWords.restrictReduced b) := by
  let P := TensorProduct.map (reducedProjection R M) (reducedProjection R M)
  let I := TensorProduct.map (reducedInclusion R M) (reducedInclusion R M)
  let τ := map (G.koszulTwist q)
  let τr := ReducedTensorWords.map (R := R) (G.koszulTwist q)
  have ht (z : ReducedTensorWords R M) :
      τ (reducedInclusion R M z) = reducedInclusion R M (τr z) :=
    LinearMap.congr_fun (map_comp_reducedInclusion (G.koszulTwist q)) z
  have hl : P ∘ₗ LinearMap.rTensor (TensorWords R M) b ∘ₗ I =
      LinearMap.rTensor (ReducedTensorWords R M) (TensorWords.restrictReduced b) := by
    apply TensorProduct.ext'
    intro x y
    simp [P, I, restrictReduced_apply]
  have hr : P ∘ₗ LinearMap.lTensor (TensorWords R M) b ∘ₗ
      LinearMap.rTensor (TensorWords R M) τ ∘ₗ I =
      LinearMap.lTensor (ReducedTensorWords R M) (TensorWords.restrictReduced b) ∘ₗ
        LinearMap.rTensor (ReducedTensorWords R M) τr := by
    apply TensorProduct.ext'
    intro x y
    simp [P, I, ht, restrictReduced_apply]
  rw [ReducedTensorWords.isGradedCoderivation_iff]
  apply LinearMap.ext
  intro w
  have h := congrArg P (hb.deconcatenation_apply (reducedInclusion R M w))
  have hleft (z : TensorWords R M) :
      P (deconcatenation R M z) =
        ReducedTensorWords.deconcatenation R M (reducedProjection R M z) :=
    LinearMap.congr_fun (map_reducedProjection_comp_deconcatenation R M) z
  have hl' := LinearMap.congr_fun hl (ReducedTensorWords.deconcatenation R M w)
  have hr' := LinearMap.congr_fun hr (ReducedTensorWords.deconcatenation R M w)
  simp only [LinearMap.comp_apply, P, I, τ, τr] at hl' hr'
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, restrictReduced_apply,
    hleft, deconcatenation_comp_reducedInclusion_apply, map_add,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, map_one, h₁,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero,
    P, TensorProduct.map_tmul, reducedProjection_one, zero_add, add_zero,
    hl', hr'] using h

/-- Every signed coderivation annihilating the empty word is the extension of its
reduced restriction. -/
theorem IsGradedCoderivation.extendReduced_restrictReduced
    (hb : IsGradedCoderivation G q b) (h₁ : b 1 = 0) :
    extendReduced (TensorWords.restrictReduced b) = b :=
  TensorWords.extendReduced_restrictReduced b hb.counit_comp h₁

/-- Coaugmentation-preserving signed coderivations are determined by their
positive-arity letter components. -/
theorem IsGradedCoderivation.eq_of_letter_comp_restrictReduced_eq
    {b₁ b₂ : TensorWords R M →ₗ[R] TensorWords R M}
    (hb₁ : IsGradedCoderivation G q b₁) (hb₂ : IsGradedCoderivation G q b₂)
    (h₁ : b₁ 1 = 0) (h₂ : b₂ 1 = 0)
    (hF : ReducedTensorWords.letter R M ∘ₗ TensorWords.restrictReduced b₁ =
      ReducedTensorWords.letter R M ∘ₗ TensorWords.restrictReduced b₂) : b₁ = b₂ := by
  have h := (hb₁.restrictReduced h₁).eq_of_letter_comp_eq (hb₂.restrictReduced h₂) hF
  rw [← hb₁.extendReduced_restrictReduced h₁,
    ← hb₂.extendReduced_restrictReduced h₂, h]

/-- A coaugmentation-preserving signed coderivation is the extension of the graded
Taylor expansion of its positive-arity letter components. -/
theorem IsGradedCoderivation.eq_extendReduced_gradedCoderiv
    (hb : IsGradedCoderivation G q b) (h₁ : b 1 = 0) :
    b = extendReduced (ReducedTensorWords.gradedCoderiv G
      (ReducedTensorWords.letter R M ∘ₗ TensorWords.restrictReduced b) q) := by
  have h := (hb.restrictReduced h₁).eq_of_letter_comp_eq
    (ReducedTensorWords.isGradedCoderivation_gradedCoderiv G
      (ReducedTensorWords.letter R M ∘ₗ TensorWords.restrictReduced b) q)
    (ReducedTensorWords.letter_comp_gradedCoderiv G _ q).symm
  exact (hb.extendReduced_restrictReduced h₁).symm.trans (congrArg extendReduced h)

/-- For a coaugmentation-preserving signed coderivation, homogeneity is equivalent to
homogeneity of its positive-arity Taylor map. In particular this restricts the correspondence
to coderivations and Taylor maps of degree one. -/
theorem IsGradedCoderivation.isHomogeneous_iff
    (hb : IsGradedCoderivation G q b) (h₁ : b 1 = 0) (r : ℤ) :
    LinearMap.IsHomogeneous b (gradedPiece G) (gradedPiece G) r ↔
      LinearMap.IsHomogeneous
        (ReducedTensorWords.letter R M ∘ₗ TensorWords.restrictReduced b)
        (ReducedTensorWords.gradedPiece G) G.piece r := by
  constructor
  · intro h
    rw [LinearMap.isHomogeneous_def]
    intro D w hw
    have hi := mem_gradedPiece_of_reducedInclusion hw
    have hp := (isHomogeneous_reducedProjection G).map_mem (h.map_mem hi)
    have hl := (ReducedTensorWords.isHomogeneous_letter G).map_mem hp
    simpa only [LinearMap.comp_apply, restrictReduced_apply, add_zero] using hl
  · intro h
    have he := isHomogeneous_extendReduced
      (ReducedTensorWords.isHomogeneous_gradedCoderiv G _ q r h)
    -- Rewrite only the map argument: rewriting b globally would also rewrite its Taylor map.
    exact hb.eq_extendReduced_gradedCoderiv h₁ ▸ he

/-- The submodule of signed coderivations annihilating the coaugmentation.
Homogeneity is not included: the twist parameter determines the co-Leibniz sign. -/
noncomputable def coaugmentationPreservingGradedCoderivations
    (G : InternalGrading R M) (q : ℤ) :
    Submodule R (TensorWords R M →ₗ[R] TensorWords R M) where
  carrier := {b | IsGradedCoderivation G q b ∧ b 1 = 0}
  zero_mem' := by
    constructor
    · rw [isGradedCoderivation_iff]
      simp
    · simp
  add_mem' hb hc := by
    constructor
    · rw [isGradedCoderivation_iff]
      apply LinearMap.ext
      intro w
      simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add,
        hb.1.deconcatenation_apply, hc.1.deconcatenation_apply,
        LinearMap.rTensor_add, LinearMap.lTensor_add]
      abel
    · simp [hb.2, hc.2]
  smul_mem' r b hb := by
    constructor
    · rw [isGradedCoderivation_iff]
      apply LinearMap.ext
      intro w
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
        map_smul, hb.1.deconcatenation_apply, LinearMap.rTensor_smul,
        LinearMap.lTensor_smul, smul_add]
    · simp [hb.2]

/-- Membership means the signed co-Leibniz rule and annihilation of the empty word. -/
@[simp]
theorem mem_coaugmentationPreservingGradedCoderivations
    (G : InternalGrading R M) (q : ℤ) (b : TensorWords R M →ₗ[R] TensorWords R M) :
    b ∈ coaugmentationPreservingGradedCoderivations G q ↔
      IsGradedCoderivation G q b ∧ b 1 = 0 :=
  Iff.rfl

/-- The positive-arity Taylor correspondence for coaugmentation-preserving signed
coderivations. Its inverse is reduced Taylor expansion followed by extension by zero
on the empty word. -/
noncomputable def gradedCoderivEquivTaylor (G : InternalGrading R M) (q : ℤ) :
    coaugmentationPreservingGradedCoderivations G q ≃ₗ[R]
      (ReducedTensorWords R M →ₗ[R] M) where
  toFun b := ReducedTensorWords.letter R M ∘ₗ restrictReduced b.val
  invFun F := ⟨extendReduced (ReducedTensorWords.gradedCoderiv G F q),
    (mem_coaugmentationPreservingGradedCoderivations G q _).mpr
      ⟨isGradedCoderivation_extendReduced
        (ReducedTensorWords.isGradedCoderivation_gradedCoderiv G F q),
        extendReduced_one _⟩⟩
  left_inv b := by
    obtain ⟨hb, h₁⟩ := (mem_coaugmentationPreservingGradedCoderivations G q _).mp b.property
    exact Subtype.ext (hb.eq_extendReduced_gradedCoderiv h₁).symm
  right_inv F := by
    simp only [restrictReduced_extendReduced, ReducedTensorWords.letter_comp_gradedCoderiv]
  map_add' b c := by
    apply LinearMap.ext
    intro w
    simp
  map_smul' r b := by
    apply LinearMap.ext
    intro w
    simp

/-- The forward correspondence reads off the letter component of the reduced restriction. -/
@[simp]
theorem gradedCoderivEquivTaylor_apply (G : InternalGrading R M) (q : ℤ)
    (b : coaugmentationPreservingGradedCoderivations G q) :
    gradedCoderivEquivTaylor G q b =
      ReducedTensorWords.letter R M ∘ₗ restrictReduced b.val :=
  (rfl)

/-- The inverse correspondence is the extension of the reduced graded Taylor expansion. -/
@[simp]
theorem gradedCoderivEquivTaylor_symm_apply (G : InternalGrading R M) (q : ℤ)
    (F : ReducedTensorWords R M →ₗ[R] M) :
    ((gradedCoderivEquivTaylor G q).symm F).val =
      extendReduced (ReducedTensorWords.gradedCoderiv G F q) :=
  (rfl)

end TensorWords
end TauCeti
