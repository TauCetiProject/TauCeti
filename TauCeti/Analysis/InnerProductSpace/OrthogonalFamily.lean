/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Algebra.Order.Chebyshev

/-!
# Orthogonal families from orthogonal vectors

The squared norm of a finite sum of pairwise orthogonal vectors is the sum of their squared
norms, `‖∑ i ∈ s, v i‖² = ∑ i ∈ s, ‖v i‖²`, and passing to the limit gives the same identity for a
convergent series of pairwise orthogonal vectors. Both hold in a seminormed inner product space.

Vectors are pairwise orthogonal exactly when their spans form an `OrthogonalFamily`
(`orthogonalFamily_span_singleton_iff`); this equivalence also holds in a seminormed inner product
space. When the space is normed, it allows orthogonal-series results for subspaces to apply
directly to a vector family, including one with zero terms: the span of a zero vector is the zero
subspace. The normed hypothesis is needed there because Mathlib's `OrthogonalFamily` lemmas ask
each subspace to be a `NormedAddCommGroup`, which a cyclic span is only when the space is normed.

Normalizing the nonzero vectors of a pairwise orthogonal family gives an orthonormal family.

The residue classes modulo `L` give the almost-orthogonal version: if `⟪v i, v j⟫ = 0` whenever
`i + L ≤ j`, then `‖∑ i ∈ s, v i‖² ≤ L ∑ i ∈ s, ‖v i‖²`
(`TauCeti.norm_sum_sq_le_mul_sum_norm_sq_of_inner_eq_zero`). For a family with summable
squared norms the series `∑ v i` then converges in a complete space
(`TauCeti.summable_of_inner_eq_zero`), with `‖∑' i, v i‖² ≤ L ∑' i, ‖v i‖²`
(`TauCeti.norm_tsum_sq_le_mul_tsum_norm_sq_of_inner_eq_zero`). These are stated for families
indexed by `ℤ`; the `_nat` versions treat families indexed by `ℕ`. This is the form in which a
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

/-- **Almost orthogonal vectors.** If `⟪v i, v j⟫ = 0` for `i, j ∈ s` with `i + L ≤ j`, then
`‖∑ i ∈ s, v i‖² ≤ L ∑ i ∈ s, ‖v i‖²`: the vectors whose indices have a fixed residue modulo `L`
are pairwise orthogonal, and there are `L` residues. -/
theorem norm_sum_sq_le_mul_sum_norm_sq_of_inner_eq_zero {v : ℤ → E} {L : ℕ} {s : Finset ℤ}
    (hv : ∀ i ∈ s, ∀ j ∈ s, i + L ≤ j → ⟪v i, v j⟫_𝕜 = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 ≤ L * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · -- For `L = 0` every `v i` is orthogonal to itself, so has norm `0`.
    have h0 : ∀ i ∈ s, ‖v i‖ = 0 := fun i hi ↦ (pow_eq_zero_iff two_ne_zero).1 <| by
      rw [norm_sq_eq_re_inner (𝕜 := 𝕜), hv i hi i hi (by simp), map_zero]
    have : ‖∑ i ∈ s, v i‖ = 0 :=
      le_antisymm ((norm_sum_le _ _).trans_eq (Finset.sum_eq_zero h0)) (norm_nonneg _)
    simp [this]
  -- Distinct indices with the same residue modulo `L` are at least `L` apart.
  have hgap : ∀ i j : ℤ, i % L = j % L → i < j → i + L ≤ j := fun i j hij h ↦ by
    have := Int.le_of_dvd (sub_pos.2 h) (Int.ModEq.dvd hij)
    omega
  -- Split the family by residues modulo `L`: each class is pairwise orthogonal.
  set w : ℤ → ℤ → E := fun r i ↦ if i % L = r then v i else 0
  have hw : ∀ r, (s : Set ℤ).Pairwise fun i j ↦ ⟪w r i, w r j⟫_𝕜 = 0 := by
    intro r i hi j hj hij
    simp only [w]
    split_ifs with hir hjr
    · rcases lt_or_gt_of_ne hij with h | h
      · exact hv i hi j hj (hgap i j (hir.trans hjr.symm) h)
      · rw [← inner_conj_symm, hv j hj i hi (hgap j i (hjr.trans hir.symm) h), map_zero]
    all_goals simp
  have hsum : ∀ r, ∑ i ∈ s, w r i = ∑ i ∈ s with i % L = r, v i := fun r ↦
    (Finset.sum_filter _ _).symm
  have hsq : ∀ r, ∑ i ∈ s, ‖w r i‖ ^ 2 = ∑ i ∈ s with i % L = r, ‖v i‖ ^ 2 := fun r ↦ by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun i _ ↦ by simp only [w]; split_ifs <;> simp
  have hmaps : ∀ i ∈ s, i % L ∈ Finset.Ico (0 : ℤ) L := fun i _ ↦
    Finset.mem_Ico.2 ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  calc ‖∑ i ∈ s, v i‖ ^ 2
      = ‖∑ r ∈ Finset.Ico (0 : ℤ) L, ∑ i ∈ s, w r i‖ ^ 2 := by
        simp_rw [hsum, Finset.sum_fiberwise_of_maps_to hmaps]
    _ ≤ (∑ r ∈ Finset.Ico (0 : ℤ) L, ‖∑ i ∈ s, w r i‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ L * ∑ r ∈ Finset.Ico (0 : ℤ) L, ‖∑ i ∈ s, w r i‖ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.Ico (0 : ℤ) L)
          (f := fun r ↦ ‖∑ i ∈ s, w r i‖)
    _ = L * ∑ i ∈ s, ‖v i‖ ^ 2 := by
        simp_rw [norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero (hw _), hsq,
          Finset.sum_fiberwise_of_maps_to hmaps]

/-- The `ℕ`-indexed case of `norm_sum_sq_le_mul_sum_norm_sq_of_inner_eq_zero`: if
`⟪v i, v j⟫ = 0` for `i, j ∈ s` with `i + L ≤ j`, then `‖∑ i ∈ s, v i‖² ≤ L ∑ i ∈ s, ‖v i‖²`. -/
theorem norm_sum_sq_le_mul_sum_norm_sq_of_inner_eq_zero_nat {v : ℕ → E} {L : ℕ} {s : Finset ℕ}
    (hv : ∀ i ∈ s, ∀ j ∈ s, i + L ≤ j → ⟪v i, v j⟫_𝕜 = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 ≤ L * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  have h := norm_sum_sq_le_mul_sum_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) (L := L)
    (v := fun i : ℤ ↦ v i.toNat) (s := s.map Nat.castEmbedding) <| by
      simp only [Finset.mem_map, Nat.castEmbedding_apply]
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ hij
      exact hv i hi j hj (by omega)
  simpa using h

/-- **Almost orthogonal series converge.** In a complete space, if `⟪v i, v j⟫ = 0` whenever
`i + L ≤ j` and the squared norms `‖v i‖²` are summable, then so are the `v i`. -/
theorem summable_of_inner_eq_zero [CompleteSpace E] {v : ℤ → E} {L : ℕ}
    (hv : ∀ i j : ℤ, i + L ≤ j → ⟪v i, v j⟫_𝕜 = 0) (hsq : Summable fun i ↦ ‖v i‖ ^ 2) :
    Summable v := by
  refine summable_iff_vanishing_norm.2 fun ε hε ↦ ?_
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.1 hsq (ε ^ 2 / (L + 1)) (by positivity)
  refine ⟨s, fun t ht ↦ ?_⟩
  have h := hs t ht
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ ↦ by positivity)] at h
  refine (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).1
    ((norm_sum_sq_le_mul_sum_norm_sq_of_inner_eq_zero fun i _ j _ ↦ hv i j).trans_lt ?_)
  calc (L : ℝ) * ∑ i ∈ t, ‖v i‖ ^ 2 ≤ (L + 1) * ∑ i ∈ t, ‖v i‖ ^ 2 := by
        gcongr
        linarith
    _ < (L + 1) * (ε ^ 2 / (L + 1)) := by gcongr
    _ = ε ^ 2 := by field_simp

/-- **Almost orthogonal series.** If `⟪v i, v j⟫ = 0` whenever `i + L ≤ j` and the squared norms
`‖v i‖²` are summable, then `‖∑' i, v i‖² ≤ L ∑' i, ‖v i‖²`. -/
theorem norm_tsum_sq_le_mul_tsum_norm_sq_of_inner_eq_zero {v : ℤ → E} {L : ℕ}
    (hv : ∀ i j : ℤ, i + L ≤ j → ⟪v i, v j⟫_𝕜 = 0) (hsq : Summable fun i ↦ ‖v i‖ ^ 2) :
    ‖∑' i, v i‖ ^ 2 ≤ L * ∑' i, ‖v i‖ ^ 2 := by
  by_cases h : Summable v
  · refine le_of_tendsto' (h.hasSum.norm.pow 2) fun t ↦
      (norm_sum_sq_le_mul_sum_norm_sq_of_inner_eq_zero fun i _ j _ ↦ hv i j).trans ?_
    gcongr
    exact hsq.sum_le_tsum _ fun i _ ↦ by positivity
  · rw [tsum_eq_zero_of_not_summable h, norm_zero, zero_pow two_ne_zero]
    exact mul_nonneg (Nat.cast_nonneg L) (tsum_nonneg fun i ↦ by positivity)

/-- Extending an almost orthogonal `ℕ`-indexed family by zero to `ℤ` keeps it almost orthogonal. -/
private theorem inner_extend_natCast_eq_zero {v : ℕ → E} {L : ℕ}
    (hv : ∀ i j, i + L ≤ j → ⟪v i, v j⟫_𝕜 = 0) (i j : ℤ) (hij : i + L ≤ j) :
    ⟪Function.extend Nat.cast v 0 i, Function.extend Nat.cast v 0 j⟫_𝕜 = 0 := by
  by_cases hi : ∃ a : ℕ, (a : ℤ) = i
  · by_cases hj : ∃ b : ℕ, (b : ℤ) = j
    · obtain ⟨a, rfl⟩ := hi
      obtain ⟨b, rfl⟩ := hj
      rw [Nat.cast_injective.extend_apply, Nat.cast_injective.extend_apply]
      exact hv a b (by omega)
    · simp [Function.extend_apply' _ _ _ hj]
  · simp [Function.extend_apply' _ _ _ hi]

/-- Extending a family by zero to `ℤ` extends its squared norms by zero. -/
private theorem norm_sq_extend_natCast (v : ℕ → E) :
    (fun i ↦ ‖Function.extend ((↑) : ℕ → ℤ) v 0 i‖ ^ 2) =
      Function.extend ((↑) : ℕ → ℤ) (fun i ↦ ‖v i‖ ^ 2) 0 := by
  funext i
  by_cases hi : ∃ a : ℕ, (a : ℤ) = i
  · obtain ⟨a, rfl⟩ := hi
    rw [Nat.cast_injective.extend_apply, Nat.cast_injective.extend_apply]
  · simp [Function.extend_apply' _ _ _ hi]

/-- The `ℕ`-indexed case of `summable_of_inner_eq_zero`. -/
theorem summable_of_inner_eq_zero_nat [CompleteSpace E] {v : ℕ → E} {L : ℕ}
    (hv : ∀ i j, i + L ≤ j → ⟪v i, v j⟫_𝕜 = 0) (hsq : Summable fun i ↦ ‖v i‖ ^ 2) :
    Summable v :=
  (summable_extend_zero Nat.cast_injective).1 <|
    summable_of_inner_eq_zero (inner_extend_natCast_eq_zero hv) <| by
      rw [norm_sq_extend_natCast]
      exact (summable_extend_zero Nat.cast_injective).2 hsq

/-- The `ℕ`-indexed case of `norm_tsum_sq_le_mul_tsum_norm_sq_of_inner_eq_zero`. -/
theorem norm_tsum_sq_le_mul_tsum_norm_sq_of_inner_eq_zero_nat {v : ℕ → E} {L : ℕ}
    (hv : ∀ i j, i + L ≤ j → ⟪v i, v j⟫_𝕜 = 0) (hsq : Summable fun i ↦ ‖v i‖ ^ 2) :
    ‖∑' i, v i‖ ^ 2 ≤ L * ∑' i, ‖v i‖ ^ 2 := by
  have h := norm_tsum_sq_le_mul_tsum_norm_sq_of_inner_eq_zero
    (inner_extend_natCast_eq_zero hv) <| by
      rw [norm_sq_extend_natCast]
      exact (summable_extend_zero Nat.cast_injective).2 hsq
  rwa [norm_sq_extend_natCast, tsum_extend_zero Nat.cast_injective,
    tsum_extend_zero Nat.cast_injective] at h

/-- Vectors are pairwise orthogonal exactly when their cyclic spans form an orthogonal family.
Zero vectors contribute the zero subspace, so no nonzero hypothesis is needed. -/
@[simp]
theorem orthogonalFamily_span_singleton_iff {v : ι → E} :
    OrthogonalFamily 𝕜 (fun i ↦ 𝕜 ∙ v i) (fun i ↦ (𝕜 ∙ v i).subtypeₗᵢ) ↔
      Pairwise fun i j ↦ ⟪v i, v j⟫_𝕜 = 0 := by
  refine forall₃_congr fun i j _ ↦
    ⟨fun h ↦ h ⟨v i, Submodule.mem_span_singleton_self _⟩
      ⟨v j, Submodule.mem_span_singleton_self _⟩, ?_⟩
  -- Elements of the two spans are scalar multiples `a • v i` and `b • v j`.
  rintro h ⟨_, hx⟩ ⟨_, hy⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
  simp [inner_smul_left, inner_smul_right, h]

end Seminormed

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

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
