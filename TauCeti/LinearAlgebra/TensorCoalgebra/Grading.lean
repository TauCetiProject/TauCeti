/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Grading

/-!
# The internal total-degree grading of reduced tensor words

The total-letter-degree pieces `TauCeti.ReducedTensorWords.gradedPiece G D` of the reduced tensor
coalgebra form an internal direct sum, `TauCeti.ReducedTensorWords.grading G`.  Independence is
inherited from the coaugmented tensor words along the injective inclusion
`TauCeti.TensorWords.reducedInclusion`, which preserves total degrees.

For this grading, the Koszul twist is the letterwise extension of the twist of the letters, so
the signs of the `q`-twisted co-Leibniz rule of `TauCeti.ReducedTensorWords.IsGradedCoderivation`
are the Koszul signs of the total grading.  Reduced deconcatenation preserves total degrees for
the tensor-product grading.  Together these make the reduced tensor coalgebra a graded
coalgebra in the sense used by differential graded coalgebras, such as the bar construction of an
`A∞` algebra.

## Main definitions

* `TauCeti.ReducedTensorWords.grading`: reduced tensor words graded by total letter degree.

## Main results

* `TauCeti.ReducedTensorWords.isInternal_gradedPiece`: the total-degree pieces form an internal
  direct sum.
* `TauCeti.ReducedTensorWords.koszulTwist_grading`: the Koszul twist of the total grading is the
  letterwise twist.
* `TauCeti.ReducedTensorWords.isHomogeneous_deconcatenation`: reduced deconcatenation preserves
  total degrees.
-/

public section

open TensorProduct

namespace TauCeti

namespace ReducedTensorWords

universe uR uM

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]
  (G : InternalGrading R M)

/-- Distinct total-degree pieces of the reduced tensor words are independent. -/
theorem iSupIndep_gradedPiece : iSupIndep (gradedPiece G) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s x hx hsum p hp
  have h := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1
    (TensorWords.iSupIndep_gradedPiece G) s
    (fun q ↦ TensorWords.reducedInclusion R M (x q))
    (fun q hq ↦ TensorWords.mem_gradedPiece_of_reducedInclusion (hx q hq))
    (by rw [← map_sum, hsum, map_zero]) p hp
  exact TensorWords.reducedInclusion_injective R M (h.trans (map_zero _).symm)

/-- The total-degree pieces of the reduced tensor words form an internal direct sum. -/
theorem isInternal_gradedPiece : DirectSum.IsInternal (gradedPiece G) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_gradedPiece G) (iSup_gradedPiece_eq_top G)

/-- Reduced tensor words graded by the sum of the cohomological degrees of their letters. -/
noncomputable def grading : InternalGrading R (ReducedTensorWords R M) where
  piece := gradedPiece G
  isInternal := isInternal_gradedPiece G

@[simp]
theorem grading_piece : (grading G).piece = gradedPiece G := (rfl)

/-- **The Koszul twist of the total grading is the letterwise Koszul twist.** -/
theorem koszulTwist_grading (q : ℤ) :
    (grading G).koszulTwist q = map (R := R) (G.koszulTwist q) :=
  (grading G).linearMap_ext fun _ _ hz ↦ by
    rw [(grading G).koszulTwist_apply_of_mem hz, map_koszulTwist_apply_of_mem G hz]

/-- **Reduced deconcatenation preserves total degrees**, for the tensor-product grading of the
two halves. -/
theorem isHomogeneous_deconcatenation :
    LinearMap.IsHomogeneous (deconcatenation R M) (grading G).piece
      ((grading G).tensorProduct (grading G)).piece 0 := by
  refine LinearMap.isHomogeneous_def.2 fun D z hz ↦ ?_
  rw [grading_piece] at hz
  rw [add_zero]
  refine gradedPiece_induction
    (motive := fun z ↦ deconcatenation R M z ∈ ((grading G).tensorProduct (grading G)).piece D)
    hz ?_ (fun _ _ _ _ hu hv ↦ by simpa using add_mem hu hv)
    (fun a _ _ hu ↦ by simpa using Submodule.smul_mem _ a hu)
  intro n hn 𝒟 x hx hD
  rw [of_tprod_eq_subword, deconcatenation_subword]
  refine Submodule.sum_mem _ fun c hc ↦ ?_
  rw [Finset.mem_Ioo] at hc
  let 𝒟' : ℕ → ℤ := fun i ↦ if h : i < n then 𝒟 ⟨i, h⟩ else 0
  have h𝒟' : ∀ i : Fin n, x i ∈ G.piece (𝒟' i) := fun i ↦ by simpa [𝒟'] using hx i
  have hsum : ∑ j ∈ Finset.range c, 𝒟' (0 + j) +
      ∑ j ∈ Finset.range (n - c), 𝒟' (0 + c + j) = D := by
    have h₁ : ∑ i, 𝒟 i = ∑ i ∈ Finset.range n, 𝒟' i := by
      rw [← Fin.sum_univ_eq_sum_range]
      simp [𝒟']
    have h₂ : ∑ i ∈ Finset.range n, 𝒟' i =
        ∑ i ∈ Finset.range c, 𝒟' i + ∑ j ∈ Finset.range (n - c), 𝒟' (c + j) := by
      rw [← Finset.sum_range_add, Nat.add_sub_cancel' hc.2.le]
    simp only [zero_add]
    rw [← hD, h₁, h₂]
  rw [← hsum]
  exact InternalGrading.tmul_mem_tensorProduct _ _
    (subword_mem_gradedPiece x 𝒟' h𝒟' 0 c)
    (subword_mem_gradedPiece x 𝒟' h𝒟' (0 + c) (n - c))

end ReducedTensorWords

end TauCeti
