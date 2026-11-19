/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.MultiIndex.Coeff
import TauCeti.Algebra.Order.Antidiag.Pi

/-!
# Normally convergent multi-index series

A family of coefficients `c : (ι → ℕ) → F` with `∑ α, ‖c α‖ * r ^ (∑ i, α i)` finite defines the
function `z ↦ ∑' α, (∏ i, z i ^ α i) • c α` on the polydisc `‖z‖ < r` in `ι → 𝕜`. This file shows
that this function has a power series on that polydisc whose multi-index coefficients
(`FormalMultilinearSeries.mvCoeff`) are exactly the `c α`. This is the converse of
`HasFPowerSeriesOnBall.hasSum_mvCoeff`: power series in several variables can be handled entirely
through their multi-index coefficients, in either direction. With the identity theorem
`HasFPowerSeriesAt.mvCoeff_eq_zero_of_eventuallyEq_zero`, it follows that a normally convergent
multi-index series vanishing near the origin has all its coefficients zero.

The power series is built degree by degree. For each multi-index `α` of total degree `k` we fix one
tuple `a : Fin k → ι` in which each `i` occurs `α i` times, and use the multilinear map
`v ↦ c α • ∏ j, v j (a j)`. Its value on the diagonal is the monomial `(∏ i, z i ^ α i) • c α`, and
among the tuples of basis vectors it is nonzero only at the one given by `a`. No factorial or
multinomial coefficient is inverted, so the construction works in every characteristic.

## Main results

* `TauCeti.exists_hasFPowerSeriesOnBall_tsum`: a normally convergent multi-index series has a
  power series on the polydisc, with the given multi-index coefficients.
* `TauCeti.eq_zero_of_tsum_prod_pow_smul_eventuallyEq_zero`: the identity theorem for normally
  convergent multi-index series.
-/

public section

open Finset Topology
open scoped NNReal

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The continuous multilinear map `v ↦ ∏ j, v j (a j)` on `k` copies of `ι → 𝕜`, recording the
coordinate `a j` of the `j`-th argument. -/
private noncomputable def prodEval {k : ℕ} (a : Fin k → ι) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin k ↦ ι → 𝕜) 𝕜 :=
  (ContinuousMultilinearMap.mkPiAlgebra 𝕜 (Fin k) 𝕜).compContinuousLinearMap
    fun j ↦ ContinuousLinearMap.proj (a j)

private theorem prodEval_apply {k : ℕ} (a : Fin k → ι) (v : Fin k → ι → 𝕜) :
    prodEval a v = ∏ j, v j (a j) := by
  simp [prodEval]

variable [Fintype ι]

private theorem norm_prodEval_le {k : ℕ} (a : Fin k → ι) : ‖prodEval (𝕜 := 𝕜) a‖ ≤ 1 :=
  ContinuousMultilinearMap.opNorm_le_bound zero_le_one fun v ↦ by
    rw [prodEval_apply, norm_prod, one_mul]
    exact prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun j _ ↦ norm_le_pi_norm (v j) (a j)

/-- A tuple in which each `i` occurs `α i` times, for `α` of total degree `k`. -/
private noncomputable def countTuple [DecidableEq ι] {k : ℕ} {α : ι → ℕ}
    (hα : α ∈ univ.piAntidiag k) : Fin k → ι :=
  (exists_card_fiber_eq_of_mem_piAntidiag hα).choose

private theorem card_countTuple [DecidableEq ι] {k : ℕ} {α : ι → ℕ}
    (hα : α ∈ univ.piAntidiag k) (i : ι) : Fintype.card {j // countTuple hα j = i} = α i :=
  (exists_card_fiber_eq_of_mem_piAntidiag hα).choose_spec i

/-- The formal multilinear series with multi-index coefficients `c`: its degree-`k` term is
`v ↦ ∑ α, c α • ∏ j, v j (a_α j)` over the multi-indices `α` of total degree `k`, where `a_α` is a
tuple in which each `i` occurs `α i` times. -/
private noncomputable def ofMvCoeff [DecidableEq ι] (c : (ι → ℕ) → F) :
    FormalMultilinearSeries 𝕜 (ι → 𝕜) F :=
  fun k ↦ ∑ α ∈ (univ.piAntidiag k).attach, (prodEval (countTuple α.2)).smulRight (c α)

private theorem ofMvCoeff_apply [DecidableEq ι] (c : (ι → ℕ) → F) (k : ℕ)
    (v : Fin k → ι → 𝕜) :
    ofMvCoeff c k v = ∑ α ∈ (univ.piAntidiag k).attach, (∏ j, v j (countTuple α.2 j)) • c α := by
  simp [ofMvCoeff, prodEval_apply]

/-- The degree-`k` term of `ofMvCoeff c` on the diagonal is the sum of the monomials of total
degree `k` with coefficients `c`. -/
private theorem ofMvCoeff_apply_diag [DecidableEq ι] (c : (ι → ℕ) → F) (k : ℕ) (z : ι → 𝕜) :
    ofMvCoeff c k (fun _ ↦ z) = ∑ α ∈ univ.piAntidiag k, (∏ i, z i ^ α i) • c α := by
  rw [ofMvCoeff_apply, ← sum_attach (univ.piAntidiag k)]
  refine sum_congr rfl fun α _ ↦ ?_
  congr 1
  simpa [card_countTuple] using (Fintype.prod_fiberwise' (countTuple α.2) z).symm

/-- The multi-index coefficients of `ofMvCoeff c` are the `c α`. -/
private theorem mvCoeff_ofMvCoeff [DecidableEq ι] (c : (ι → ℕ) → F) (α : ι → ℕ) :
    (ofMvCoeff (𝕜 := 𝕜) c).mvCoeff α = c α := by
  have hα : α ∈ univ.piAntidiag (∑ i, α i) := mem_piAntidiag.2 ⟨rfl, by simp⟩
  -- At a tuple `b` of basis vectors, only the summand of the multi-index `β` with
  -- `countTuple β = b` survives.
  have hbasis (b : Fin (∑ i, α i) → ι) (β : univ.piAntidiag (∑ i, α i)) :
      (∏ j, (Pi.single (b j) 1 : ι → 𝕜) (countTuple β.2 j)) • c β =
        if countTuple β.2 = b then c β else 0 := by
    simp only [Pi.single_apply, prod_boole, mem_univ, true_implies, funext_iff]
    split_ifs <;> simp
  rw [FormalMultilinearSeries.mvCoeff_eq_sum _ rfl]
  simp_rw [ofMvCoeff_apply, hbasis]
  rw [sum_comm]
  -- The tuple `countTuple β` has coordinate counts `α` exactly when `β = α`.
  have hcount (β : univ.piAntidiag (∑ i, α i)) :
      (countTuple β.2 ∈ univ.filter fun b : Fin (∑ i, α i) → ι ↦
        ∀ i, Fintype.card {j // b j = i} = α i) ↔ (β : ι → ℕ) = α := by
    simp only [mem_filter, mem_univ, true_and, card_countTuple, funext_iff]
  simp_rw [sum_ite_eq, hcount]
  rw [sum_attach (univ.piAntidiag (∑ i, α i)) fun β ↦ if β = α then c β else 0]
  simp [hα]

/-- The degree-`k` term of `ofMvCoeff c` has norm at most the sum of the norms of the
coefficients of total degree `k`. -/
private theorem norm_ofMvCoeff_le [DecidableEq ι] (c : (ι → ℕ) → F) (k : ℕ) :
    ‖ofMvCoeff (𝕜 := 𝕜) c k‖ ≤ ∑ α ∈ univ.piAntidiag k, ‖c α‖ := by
  rw [ofMvCoeff, ← sum_attach (univ.piAntidiag k) fun α ↦ ‖c α‖]
  refine (norm_sum_le _ _).trans (sum_le_sum fun α _ ↦ ?_)
  rw [ContinuousMultilinearMap.norm_smulRight]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_prodEval_le _)

/-- **A normally convergent multi-index series has a power series on the polydisc.** If
`∑ α, ‖c α‖ * r ^ (∑ i, α i)` converges, then `z ↦ ∑' α, (∏ i, z i ^ α i) • c α` has a power series
on the ball of radius `r` about `0` in `ι → 𝕜`, whose multi-index coefficients are the `c α`. -/
theorem exists_hasFPowerSeriesOnBall_tsum [CompleteSpace F] (c : (ι → ℕ) → F) {r : ℝ≥0}
    (hr : 0 < r) (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i)) :
    ∃ p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F,
      HasFPowerSeriesOnBall (fun z : ι → 𝕜 ↦ ∑' α : ι → ℕ, (∏ i, z i ^ α i) • c α) p 0 r ∧
        ∀ α, p.mvCoeff α = c α := by
  classical
  -- A sum over all multi-indices can be taken degree by degree.
  have hfiber (k : ℕ) : (fun α : ι → ℕ ↦ ∑ i, α i) ⁻¹' {k} =
      ((univ.piAntidiag k : Finset (ι → ℕ)) : Set (ι → ℕ)) := by
    ext α
    simp [mem_piAntidiag]
  have hdeg_norm : Summable fun k ↦ ∑ α ∈ univ.piAntidiag k, ‖c α‖ * (r : ℝ) ^ (∑ i, α i) := by
    convert (hsum.hasSum.tsum_fiberwise fun α ↦ ∑ i, α i).summable with k
    rw [hfiber]
    exact (Finset.tsum_subtype' _ fun α ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i)).symm
  refine ⟨ofMvCoeff c, ⟨?_, ENNReal.coe_pos.2 hr, fun {y} hy ↦ ?_⟩, mvCoeff_ofMvCoeff c⟩
  · -- The degree-`k` terms are bounded by the coefficients of total degree `k`.
    refine FormalMultilinearSeries.le_radius_of_summable _ <|
      hdeg_norm.of_nonneg_of_le (fun _ ↦ by positivity) fun k ↦ ?_
    rw [sum_congr rfl fun α hα ↦ by rw [(mem_piAntidiag.1 hα).1], ← sum_mul]
    gcongr
    exact norm_ofMvCoeff_le c k
  · have hy : ‖y‖ < r := by simpa [eNorm_lt_coe] using hy
    -- On the ball the monomial series converges absolutely, by comparison with `hsum`.
    have hmono : Summable fun α : ι → ℕ ↦ (∏ i, y i ^ α i) • c α := by
      refine Summable.of_norm_bounded hsum fun α ↦ ?_
      rw [norm_smul, norm_prod, mul_comm, ← prod_pow_eq_pow_sum]
      gcongr with i
      rw [norm_pow]
      gcongr
      exact (norm_le_pi_norm y i).trans hy.le
    convert hmono.hasSum.tsum_fiberwise (fun α ↦ ∑ i, α i) using 1
    · ext k
      rw [ofMvCoeff_apply_diag, hfiber]
      exact (Finset.tsum_subtype' _ fun α ↦ (∏ i, y i ^ α i) • c α).symm
    · simp

/-- **The identity theorem for normally convergent multi-index series.** If
`∑ α, ‖c α‖ * r ^ (∑ i, α i)` converges for some `r > 0` and
`z ↦ ∑' α, (∏ i, z i ^ α i) • c α` vanishes near `0`, then every coefficient `c α` is zero. -/
theorem eq_zero_of_tsum_prod_pow_smul_eventuallyEq_zero [CompleteSpace F] {c : (ι → ℕ) → F}
    {r : ℝ≥0} (hr : 0 < r) (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i))
    (h : (fun z : ι → 𝕜 ↦ ∑' α : ι → ℕ, (∏ i, z i ^ α i) • c α) =ᶠ[𝓝 0] 0) : c = 0 := by
  obtain ⟨p, hp, hc⟩ := exists_hasFPowerSeriesOnBall_tsum (𝕜 := 𝕜) c hr hsum
  funext α
  rw [Pi.zero_apply, ← hc α]
  exact hp.hasFPowerSeriesAt.mvCoeff_eq_zero_of_eventuallyEq_zero h α

end TauCeti
