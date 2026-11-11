/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Chebyshev

/-!
# Orthogonal families from orthogonal vectors

The squared norm of a finite sum of pairwise orthogonal vectors is the sum of their squared
norms, `‖∑ i ∈ s, v i‖² = ∑ i ∈ s, ‖v i‖²`, and passing to the limit gives the same identity for a
convergent series of pairwise orthogonal vectors. Both hold in a seminormed inner product space.

Vectors are pairwise orthogonal exactly when their spans form an `OrthogonalFamily`
(`orthogonalFamily_span_singleton_iff`). This allows orthogonal-series results for subspaces to
apply directly to a vector family, including one with zero terms: the span of a zero vector is the
zero subspace. Normalizing the nonzero vectors of a pairwise orthogonal family gives an orthonormal
family.

The residue classes modulo `L` give the almost-orthogonal version: if `⟪v i, v j⟫ = 0` whenever
`i + L ≤ j`, then `‖∑ i ∈ s, v i‖² ≤ L ∑ i ∈ s, ‖v i‖²`
(`TauCeti.norm_sum_sq_le_mul_sum_norm_sq_of_inner_eq_zero`). This is the form in which a
decomposition into pieces with almost disjoint frequency supports, such as Littlewood–Paley
blocks, is controlled in `L²`.

Orthogonality also gives linear independence: a nonzero vector followed by a linearly independent
family of vectors orthogonal to it is linearly independent
(`LinearIndependent.finCons_of_inner_eq_zero`), as for an outward normal followed by a basis of a
tangent space.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜]

section Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Pythagoras for pairwise orthogonal vectors.** The squared norm of a finite sum of pairwise
orthogonal vectors is the sum of their squared norms. Only the vectors indexed by the finite set
need to be pairwise orthogonal. -/
theorem norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero {v : ι → E} {s : Finset ι}
    (hv : (s : Set ι).Pairwise fun i j ↦ ⟪v i, v j⟫_𝕜 = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  have h : ((‖∑ i ∈ s, v i‖ : ℝ) : 𝕜) ^ 2 = ∑ i ∈ s, ((‖v i‖ : ℝ) : 𝕜) ^ 2 := by
    simp only [← inner_self_eq_norm_sq_to_K, sum_inner, inner_sum]
    exact Finset.sum_congr rfl fun i hi ↦
      Finset.sum_eq_single_of_mem i hi fun j hj hji ↦ hv hj hi hji
  exact mod_cast h

/-- **Pythagoras for an orthogonal series.** If pairwise orthogonal vectors sum to `y`, then
their squared norms sum to `‖y‖²`. -/
theorem hasSum_norm_sq_of_pairwise_inner_eq_zero {v : ι → E}
    (hv : Pairwise fun i j ↦ ⟪v i, v j⟫_𝕜 = 0) {y : E} (hy : HasSum v y) :
    HasSum (fun i ↦ ‖v i‖ ^ 2) (‖y‖ ^ 2) :=
  ((Filter.Tendsto.norm hy).pow 2).congr fun _ ↦
    norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero (hv.set_pairwise _)

end Seminormed

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Vectors are pairwise orthogonal exactly when their cyclic spans form an orthogonal family.
Zero vectors contribute the zero subspace, so no nonzero hypothesis is needed. -/
theorem orthogonalFamily_span_singleton_iff {v : ι → E} :
    OrthogonalFamily 𝕜 (fun i ↦ 𝕜 ∙ v i) (fun i ↦ (𝕜 ∙ v i).subtypeₗᵢ) ↔
      Pairwise fun i j ↦ ⟪v i, v j⟫_𝕜 = 0 :=
  orthogonalFamily_iff_pairwise.trans <| forall₃_congr fun _ _ _ ↦ by
    simp [Function.onFun, Submodule.isOrtho_span]

/-- **Almost orthogonal vectors.** If `⟪v i, v j⟫ = 0` whenever `i + L ≤ j`, then
`‖∑ i ∈ s, v i‖² ≤ L ∑ i ∈ s, ‖v i‖²`: the vectors whose indices have a fixed residue modulo `L`
are pairwise orthogonal, and there are `L` residues. -/
theorem norm_sum_sq_le_mul_sum_norm_sq_of_inner_eq_zero {v : ℕ → E} {L : ℕ}
    (hv : ∀ i j, i + L ≤ j → ⟪v i, v j⟫_𝕜 = 0) (s : Finset ℕ) :
    ‖∑ i ∈ s, v i‖ ^ 2 ≤ L * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · have h0 : ∀ i, v i = 0 := fun i ↦ inner_self_eq_zero.1 (hv i i (by simp))
    simp [h0]
  -- Distinct indices with the same residue modulo `L` are at least `L` apart.
  have hgap : ∀ i j, i % L = j % L → i < j → i + L ≤ j := fun i j hij h ↦ by
    have := Nat.le_of_dvd (Nat.sub_pos_of_lt h) ((Nat.modEq_iff_dvd' h.le).1 hij)
    omega
  -- Split the family by residues modulo `L`: each class is pairwise orthogonal.
  set w : ℕ → ℕ → E := fun r i ↦ if i % L = r then v i else 0
  have hw : ∀ r, Pairwise fun i j ↦ ⟪w r i, w r j⟫_𝕜 = 0 := by
    intro r i j hij
    simp only [w]
    split_ifs with hi hj
    · rcases lt_or_gt_of_ne hij with h | h
      · exact hv i j (hgap i j (hi.trans hj.symm) h)
      · rw [← inner_conj_symm, hv j i (hgap j i (hj.trans hi.symm) h), map_zero]
    all_goals simp
  have hsum : ∀ r, ∑ i ∈ s, w r i = ∑ i ∈ s with i % L = r, v i := fun r ↦
    (Finset.sum_filter _ _).symm
  have hsq : ∀ r, ∑ i ∈ s, ‖w r i‖ ^ 2 = ∑ i ∈ s with i % L = r, ‖v i‖ ^ 2 := fun r ↦ by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun i _ ↦ by simp only [w]; split_ifs <;> simp
  have hmaps : ∀ i ∈ s, i % L ∈ Finset.range L := fun i _ ↦
    Finset.mem_range.2 (Nat.mod_lt i hL)
  calc ‖∑ i ∈ s, v i‖ ^ 2
      = ‖∑ r ∈ Finset.range L, ∑ i ∈ s, w r i‖ ^ 2 := by
        simp_rw [hsum, Finset.sum_fiberwise_of_maps_to hmaps]
    _ ≤ (∑ r ∈ Finset.range L, ‖∑ i ∈ s, w r i‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ L * ∑ r ∈ Finset.range L, ‖∑ i ∈ s, w r i‖ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range L)
          (f := fun r ↦ ‖∑ i ∈ s, w r i‖)
    _ = L * ∑ i ∈ s, ‖v i‖ ^ 2 := by
        simp_rw [norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero ((hw _).set_pairwise _), hsq,
          Finset.sum_fiberwise_of_maps_to hmaps]

/-- **Normalizing an orthogonal family.** If the vectors `vᵢ` are pairwise orthogonal, then the
normalized nonzero vectors `‖vᵢ‖⁻¹ vᵢ` are orthonormal. -/
theorem orthonormal_inv_norm_smul_of_pairwise_inner_eq_zero {v : ι → E}
    (hv : Pairwise fun i j ↦ ⟪v i, v j⟫_𝕜 = 0) :
    Orthonormal 𝕜 fun i : {i // v i ≠ 0} ↦ ((‖v i‖⁻¹ : ℝ) : 𝕜) • v i := by
  refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
  · simp [norm_smul, i.2]
  · simp [inner_smul_left, inner_smul_right, hv (Subtype.coe_ne_coe.mpr hij)]

end TauCeti

namespace LinearIndependent

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A nonzero vector followed by a linearly independent family of vectors orthogonal to it is
linearly independent. -/
theorem finCons_of_inner_eq_zero {n : ℕ} {p : E} (hp : p ≠ 0) {v : Fin n → E}
    (hv : LinearIndependent 𝕜 v) (horth : ∀ i, inner 𝕜 p (v i) = 0) :
    LinearIndependent 𝕜 (Fin.cons p v : Fin (n + 1) → E) := by
  refine hv.finCons fun hmem ↦ hp ?_
  have hle : Submodule.span 𝕜 (Set.range v) ≤ (𝕜 ∙ p)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.2 (horth i)
  exact inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hmem))

end LinearIndependent
