/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Trace.Domain
public import TauCeti.Analysis.CStarAlgebra.Trace.LowerSemicontinuous

/-!
# Projections have finite trace under a densely defined trace

Let `τ` be a densely defined trace on a C⋆-algebra `B` (`TauCeti.IsDenselyDefined`). Then every
projection `e ∈ B` has finite trace (`TauCeti.IsTrace.lt_top_of_isStarProjection`), so it lies in
the domain `𝔪_τ`. Choose `p ∈ 𝔪_τ⁺` with `‖p - e‖ < 1/2`. Conjugating by `e` gives
`e p e = e + e (p - e) e ≥ e - ‖p - e‖ e ≥ e/2`, and `e p e = (b e)⋆(b e)` has finite trace when
`p = b⋆b` with `b ∈ 𝔫_τ`. Hence `τ(e) ≤ 2 τ(e p e) < ∞`.

Applied to the matrix amplification `τ_n` of a densely defined trace, this places every projection
of `M_n(B)` in `M_n(𝔪_τ)` (Thomsen, Lemma 4.11, as specified by roadmap TracesOnCStarAlgebras
Tr1.3).

## Main results

* `TauCeti.IsTrace.lt_top_of_isStarProjection`: `τ(e) < ∞` for every projection `e`.
* `TauCeti.IsTrace.mem_finitePart_of_isStarProjection`,
  `TauCeti.IsTrace.mem_domain_of_isStarProjection`: so `e ∈ 𝔪_τ⁺ ⊆ 𝔪_τ`.
-/

public section

open scoped ENNReal NNReal

namespace TauCeti

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {τ : B → ℝ≥0∞}

namespace IsTrace

/-- Conjugating an element `p` with `‖p - e‖ ≤ 1/2` by a projection `e` gives at least `e/2`:
`(1/2) e ≤ e p e`. -/
private theorem half_smul_le_mul_mul {e p : B} (he : IsStarProjection e)
    (hp : IsSelfAdjoint p) (hpe : ‖p - e‖ ≤ 1 / 2) : (1 / 2 : ℝ) • e ≤ e * p * e := by
  have hh : IsSelfAdjoint (-(p - e)) := (hp.sub he.isSelfAdjoint).neg
  have h := CStarAlgebra.star_left_conjugate_le_norm_smul e (-(p - e)) hh
  have hstar : star e = e := he.isSelfAdjoint
  have hee : e * e = e := he.isIdempotentElem.eq
  rw [hstar, norm_neg, hee] at h
  -- `e p e = e + e (p - e) e` and `-e (p - e) e ≤ ‖p - e‖ e ≤ e / 2`.
  have hepe : e * p * e = e + e * (p - e) * e := by
    rw [mul_sub, sub_mul, hee, hee, add_sub_cancel]
  have h' : -(e * (p - e) * e) ≤ (1 / 2 : ℝ) • e := by
    calc -(e * (p - e) * e) = e * -(p - e) * e := by rw [mul_neg, neg_mul]
      _ ≤ ‖p - e‖ • e := h
      _ ≤ (1 / 2 : ℝ) • e := smul_le_smul_of_nonneg_right hpe he.nonneg
  rw [hepe]
  calc (1 / 2 : ℝ) • e = e - (1 / 2 : ℝ) • e := by
        rw [eq_sub_iff_add_eq, ← add_smul]
        norm_num
    _ ≤ e + e * (p - e) * e := by
        rw [sub_eq_add_neg]
        exact add_le_add le_rfl (neg_le.1 h')

/-- **Projections have finite trace.** For a densely defined trace `τ`, every projection `e`
satisfies `τ(e) < ∞`. -/
theorem lt_top_of_isStarProjection (hτ : IsTrace τ) (hd : IsDenselyDefined τ) {e : B}
    (he : IsStarProjection e) : τ e < ∞ := by
  obtain ⟨p, hp, hpe⟩ :=
    Metric.mem_closure_iff.1 (isDenselyDefined_iff.1 hd he.nonneg) (1 / 2) (by norm_num)
  obtain ⟨b, hb, rfl⟩ := exists_eq_star_mul_self_of_mem_finitePart hp
  have hstar : star e = e := he.isSelfAdjoint
  -- `e (b⋆b) e = (b e)⋆(b e)` has finite trace since `b e ∈ 𝔫_τ`.
  have hfin : τ (e * (star b * b) * e) < ∞ := by
    have h := hτ.mul_mem_sqIntegrable_right e hb
    rw [mem_sqIntegrable, star_mul, hstar] at h
    simpa [mul_assoc] using h
  have hle : (1 / 2 : ℝ) • e ≤ e * (star b * b) * e :=
    half_smul_le_mul_mul he (IsSelfAdjoint.star_mul_self b)
      (by rw [dist_comm, dist_eq_norm] at hpe; exact hpe.le)
  -- `τ(e) = 2 τ(e/2) ≤ 2 τ(e p e) < ∞`.
  have h2 : τ e = 2 * τ ((1 / 2 : ℝ≥0) • e) := by
    have := hτ.map_nnreal_smul_of_nonneg (1 / 2) he.nonneg
    rw [NNReal.smul_def, NNReal.coe_div, NNReal.coe_one, NNReal.coe_two] at *
    rw [this, ← mul_assoc]
    norm_num
    rw [ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  rw [h2]
  refine ENNReal.mul_lt_top (by norm_num) ((hτ.mono ?_ ?_).trans_lt hfin)
  · exact smul_nonneg (by norm_num) he.nonneg
  · simpa [NNReal.smul_def] using hle

/-- A projection lies in the finite part `𝔪_τ⁺` of a densely defined trace. -/
theorem mem_finitePart_of_isStarProjection (hτ : IsTrace τ) (hd : IsDenselyDefined τ) {e : B}
    (he : IsStarProjection e) : e ∈ finitePart τ :=
  mem_finitePart.2 ⟨he.nonneg, hτ.lt_top_of_isStarProjection hd he⟩

/-- A projection lies in the domain `𝔪_τ` of a densely defined trace. -/
theorem mem_domain_of_isStarProjection (hτ : IsTrace τ) (hd : IsDenselyDefined τ) {e : B}
    (he : IsStarProjection e) : e ∈ domain τ :=
  finitePart_subset_domain (τ := τ) (hτ.mem_finitePart_of_isStarProjection hd he)

end IsTrace

end TauCeti
