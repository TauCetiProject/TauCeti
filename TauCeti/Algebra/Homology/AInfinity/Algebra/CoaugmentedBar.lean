/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Extension
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Grading

/-!
# The bar coderivation of the coaugmented tensor coalgebra

`TauCeti.AInfinityAlgebra.barDifferential` is the square-zero coderivation of the *reduced* tensor
coalgebra, and the Stasheff identities are read off from it.  The module and bimodule theories
need one step more: a right module is a coderivation over `b` on the cofree right bar comodule, and
a bimodule a bicomodule coderivation, so in both cases `b` has to be available as a coderivation
of the *coaugmented* tensor coalgebra, which also carries the empty word.

This file supplies that extension, for the bar differential of an `A∞` algebra.  The empty word is
annihilated, and on the coaugmented tensor coalgebra the extension is a
`TauCeti.TensorWords.IsGradedCoderivation` of twist parameter one whose square is zero and which
raises the total letter degree by one.

The extension itself is not specific to bar constructions: an endomorphism of the reduced words is
extended to all tensor words by
`TauCeti.TensorWords.extendReduced`, and the module
`TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Extension` proves there that the extension
preserves the square-zero law, the homogeneity in the total letter degree, and the `q`-twisted
co-Leibniz identity.  The results of this file are the applications of those three lemmas to
`TauCeti.AInfinityAlgebra.barDifferential`, together with the empty-word case; the coaugmented
co-Leibniz identity itself, the letterwise maps, and the total-letter-degree pieces are in
`TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.GradedCoderivation` and
`TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Basic`.

## Main definitions

* `TauCeti.AInfinityAlgebra.coaugmentedBarDifferential`: the bar coderivation extended to all
  tensor words by zero on the empty word.
* `TauCeti.AInfinityAlgebra.leftUnaryDifferential`: the differential `b_A ⊗ 1 + τ ⊗ d` of
  `Tᶜ(sA) ⊗ M`, for an endomorphism `d` of `M`.

## Main results

* `TauCeti.AInfinityAlgebra.coaugmentedBarDifferential_one`: the extension annihilates the empty
  word.
* `TauCeti.AInfinityAlgebra.coaugmentedBarDifferential_comp_reducedInclusion`: the extension
  restricts to the bar differential on the words of positive length.
* `TauCeti.AInfinityAlgebra.coaugmentedBarDifferential_subword`: on a block of a tuple it is the
  bar differential of the corresponding nonempty block.
* `TauCeti.AInfinityAlgebra.coaugmentedBarDifferential_sq`: its square is zero.
* `TauCeti.AInfinityAlgebra.isHomogeneous_coaugmentedBarDifferential`: it raises the total letter
  degree by one, for the internal grading `TensorWords.grading` of the suspended words.
* `TauCeti.AInfinityAlgebra.map_koszulTwist_coaugmentedBarDifferential`: the Koszul twist of the
  suspended words anticommutes with it.
* `TauCeti.AInfinityAlgebra.leftUnaryDifferential_comp_self`: the differential `b_A ⊗ 1 + τ ⊗ d`
  of `Tᶜ(sA) ⊗ M` squares to zero when `d` does.
* `TauCeti.AInfinityAlgebra.isGradedCoderivation_coaugmentedBarDifferential`: it is a
  twist-parameter-one graded coderivation of the coaugmented tensor coalgebra.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uA

namespace TauCeti

open TensorWords

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- The bar differential extended to the coaugmented tensor words: the square-zero coderivation
`TauCeti.AInfinityAlgebra.barDifferential` of the reduced tensor coalgebra, sent along
`TauCeti.TensorWords.extendReduced`, so that the empty word is annihilated. -/
noncomputable def coaugmentedBarDifferential (𝒜 : AInfinityAlgebra R A) :
    TensorWords R A →ₗ[R] TensorWords R A :=
  extendReduced 𝒜.barDifferential

/-- The bar coderivation of the coaugmented words is the extension of the bar differential of the
reduced words by zero on the empty word. -/
theorem coaugmentedBarDifferential_def (𝒜 : AInfinityAlgebra R A) :
    𝒜.coaugmentedBarDifferential = extendReduced 𝒜.barDifferential := by
  rw [coaugmentedBarDifferential]

/-- The extension annihilates the empty word. -/
@[simp]
theorem coaugmentedBarDifferential_one (𝒜 : AInfinityAlgebra R A) :
    𝒜.coaugmentedBarDifferential (1 : TensorWords R A) = 0 := by
  rw [coaugmentedBarDifferential_def, extendReduced_one]

/-- The extension agrees with the bar differential on the words of positive length. -/
theorem coaugmentedBarDifferential_comp_reducedInclusion (𝒜 : AInfinityAlgebra R A) :
    𝒜.coaugmentedBarDifferential ∘ₗ reducedInclusion R A
      = reducedInclusion R A ∘ₗ 𝒜.barDifferential :=
  extendReduced_comp_reducedInclusion 𝒜.barDifferential

/-- On a block of a tuple, the extension is the bar differential of the corresponding nonempty
block; an empty block is annihilated. -/
theorem coaugmentedBarDifferential_subword (𝒜 : AInfinityAlgebra R A) {n : ℕ} (x : Fin n → A)
    (a b : ℕ) :
    𝒜.coaugmentedBarDifferential (subword R x a b) =
      reducedInclusion R A (𝒜.barDifferential (ReducedTensorWords.subword R x a b)) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [ReducedTensorWords.subword_length_zero, map_zero, map_zero]
    by_cases ha : a ≤ n
    · rw [subword_length_zero R x ha, coaugmentedBarDifferential_one]
    · rw [subword_eq_zero_of_lt_add R x (by omega), map_zero]
  · rw [← reducedInclusion_subword R x hb, ← LinearMap.comp_apply 𝒜.coaugmentedBarDifferential,
      coaugmentedBarDifferential_comp_reducedInclusion, LinearMap.comp_apply]

/-- The extension squares to zero. -/
@[simp]
theorem coaugmentedBarDifferential_sq (𝒜 : AInfinityAlgebra R A) :
    𝒜.coaugmentedBarDifferential ∘ₗ 𝒜.coaugmentedBarDifferential = 0 :=
  extendReduced_sq 𝒜.barDifferential (barDifferential_sq 𝒜)

/-- The extension raises the total letter degree by one: it has degree one for the internal
grading of the suspended tensor words. -/
theorem isHomogeneous_coaugmentedBarDifferential (𝒜 : AInfinityAlgebra R A) :
    LinearMap.IsHomogeneous 𝒜.coaugmentedBarDifferential
      (TensorWords.grading (𝒜.grading.shift 1)).piece
      (TensorWords.grading (𝒜.grading.shift 1)).piece 1 := by
  rw [grading_piece]
  exact isHomogeneous_extendReduced 𝒜.isHomogeneous_barDifferential

/-- The Koszul twist of the suspended words anticommutes with the extension. -/
theorem map_koszulTwist_coaugmentedBarDifferential (𝒜 : AInfinityAlgebra R A)
    (w : TensorWords R A) :
    TensorWords.map ((𝒜.grading.shift 1).koszulTwist 1) (𝒜.coaugmentedBarDifferential w) =
      -𝒜.coaugmentedBarDifferential (TensorWords.map ((𝒜.grading.shift 1).koszulTwist 1) w) := by
  rw [← koszulTwist_grading]
  simpa using 𝒜.isHomogeneous_coaugmentedBarDifferential.koszulTwist_apply 1 w

/-- The extension satisfies the graded co-Leibniz identity of the coaugmented tensor coalgebra. -/
theorem isGradedCoderivation_coaugmentedBarDifferential (𝒜 : AInfinityAlgebra R A) :
    TensorWords.IsGradedCoderivation (𝒜.grading.shift 1) 1 𝒜.coaugmentedBarDifferential :=
  isGradedCoderivation_extendReduced 𝒜.isGradedCoderivation_barDifferential

/-! ### The bar differential tensored with a differential -/

section LeftUnary

variable {M : Type*} [AddCommGroup M] [Module R M] (𝒜 : AInfinityAlgebra R A) (d : Module.End R M)

/-- The differential `b_A ⊗ 1 + τ ⊗ d` of `Tᶜ(sA) ⊗ M`: the bar differential of `A` on the left
word plus the operator `d` on the module factor, with the Koszul sign `τ` of moving `d` past the
suspended left word. -/
noncomputable def leftUnaryDifferential : Module.End R (TensorWords R A ⊗[R] M) :=
  𝒜.coaugmentedBarDifferential.rTensor M +
    TensorProduct.map ((TensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1) d

/-- The left unary differential is `b_A ⊗ 1 + τ ⊗ d`. -/
theorem leftUnaryDifferential_def :
    𝒜.leftUnaryDifferential d = 𝒜.coaugmentedBarDifferential.rTensor M +
      TensorProduct.map ((TensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1) d := (rfl)

/-- The left unary differential on `w ⊗ x` is `b_A w ⊗ x + τ w ⊗ d x`. -/
@[simp]
theorem leftUnaryDifferential_tmul (w : TensorWords R A) (x : M) :
    𝒜.leftUnaryDifferential d (w ⊗ₜ x) = 𝒜.coaugmentedBarDifferential w ⊗ₜ x +
      TensorWords.map ((𝒜.grading.shift 1).koszulTwist 1) w ⊗ₜ d x := by
  simp [leftUnaryDifferential_def, koszulTwist_grading]

variable {d}

/-- The left unary differential has degree one for the total grading of `Tᶜ(sA) ⊗ M` when `d`
has degree one. -/
theorem isHomogeneous_leftUnaryDifferential {K : InternalGrading R M ℤ}
    (hd : LinearMap.IsHomogeneous d K.piece K.piece 1) :
    LinearMap.IsHomogeneous (𝒜.leftUnaryDifferential d)
      ((TensorWords.grading (𝒜.grading.shift 1)).tensorProduct K).piece
      ((TensorWords.grading (𝒜.grading.shift 1)).tensorProduct K).piece 1 := by
  rw [leftUnaryDifferential_def]
  simpa only [zero_add] using (𝒜.isHomogeneous_coaugmentedBarDifferential.rTensor K).add
    (((TensorWords.grading (𝒜.grading.shift 1)).isHomogeneous_koszulTwist 1).tensorProduct hd)

/-- The left unary differential squares to zero when `d` does, since the Koszul twist
anticommutes with the bar differential of `A`. -/
theorem leftUnaryDifferential_comp_self (hdd : d ∘ₗ d = 0) :
    𝒜.leftUnaryDifferential d ∘ₗ 𝒜.leftUnaryDifferential d = 0 := by
  have hodd : 𝒜.coaugmentedBarDifferential ∘ₗ
        (TensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 +
      (TensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 ∘ₗ 𝒜.coaugmentedBarDifferential =
        0 := by
    refine LinearMap.ext fun w ↦ ?_
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, koszulTwist_grading,
      map_koszulTwist_coaugmentedBarDifferential, add_neg_cancel, LinearMap.zero_apply]
  rw [leftUnaryDifferential_def, ← LinearMap.lTensor_comp_rTensor,
    LinearMap.rTensor_add_lTensor_comp_rTensor_comp_self _ _ d
      (InternalGrading.koszulTwist_comp_self _ _) hodd,
    coaugmentedBarDifferential_sq, hdd, LinearMap.rTensor_zero, LinearMap.lTensor_zero, add_zero]

end LeftUnary

end AInfinityAlgebra

end TauCeti
