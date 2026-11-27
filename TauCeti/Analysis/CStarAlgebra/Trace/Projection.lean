/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Contraction
public import TauCeti.Analysis.CStarAlgebra.Trace.Domain
public import TauCeti.Analysis.CStarAlgebra.Trace.LowerSemicontinuous

/-!
# Projections have finite trace under a densely defined trace

Let `τ` be a densely defined trace on a C⋆-algebra `B` (`TauCeti.IsDenselyDefined`). Then every
projection `e ∈ B` lies in the finite part `𝔪_τ⁺`
(`TauCeti.IsTrace.mem_finitePart_of_isStarProjection`), so it has finite trace and lies in the
domain `𝔪_τ`. Choose `p ∈ 𝔪_τ⁺` with `‖p - e‖ < 1/2`.
Conjugating by `e` gives `e p e ≥ (1 - ‖p - e‖) e ≥ e/2`, and `e p e = (b e)⋆(b e)` lies in `𝔪_τ⁺`
when `p = b⋆b` with `b ∈ 𝔫_τ`. Since `𝔪_τ⁺` is hereditary, `e/2 ∈ 𝔪_τ⁺`, hence `e ∈ 𝔪_τ⁺`.

Applied to the matrix amplification `τ_n` of a densely defined trace, this places every projection
of `M_n(B)` in `M_n(𝔪_τ)` (Thomsen [WTK], Lemma 4.11).

## Main results

* `TauCeti.IsTrace.mem_finitePart_of_isStarProjection`: `e ∈ 𝔪_τ⁺` for every projection `e`.
* `TauCeti.IsTrace.lt_top_of_isStarProjection`, `TauCeti.IsTrace.mem_domain_of_isStarProjection`:
  so `τ(e) < ∞` and `e ∈ 𝔪_τ`.

## References

* Klaus Thomsen, *On weights, traces and K-theory*, arXiv:2211.03172, version of 15 March 2024:
  Lemma 4.11.
-/

public section

open scoped ENNReal NNReal

namespace TauCeti

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {τ : B → ℝ≥0∞}

namespace IsTrace

/-- **Projections lie in the finite part.** For a densely defined trace `τ`, every projection
lies in `𝔪_τ⁺` (Thomsen [WTK], Lemma 4.11). -/
theorem mem_finitePart_of_isStarProjection (hτ : IsTrace τ) (hd : IsDenselyDefined τ) {e : B}
    (he : IsStarProjection e) : e ∈ finitePart τ := by
  obtain ⟨p, hp, hpe⟩ :=
    Metric.mem_closure_iff.1 (isDenselyDefined_iff.1 hd he.nonneg) (1 / 2) (by norm_num)
  obtain ⟨b, hb, rfl⟩ := exists_eq_star_mul_self_of_mem_finitePart hp
  -- `e (b⋆b) e = (b e)⋆(b e)` lies in `𝔪_τ⁺` since `b e ∈ 𝔫_τ`.
  have hfin : e * (star b * b) * e ∈ finitePart τ := by
    have h := star_mul_self_mem_finitePart_iff.2 (hτ.mul_mem_sqIntegrable_right e hb)
    rwa [star_mul, he.isSelfAdjoint.star_eq, ← mul_assoc, mul_assoc e] at h
  -- `e/2 ≤ (1 - ‖b⋆b - e‖) e ≤ e (b⋆b) e`.
  have hle : (1 / 2 : ℝ) • e ≤ e * (star b * b) * e := by
    refine le_trans (smul_le_smul_of_nonneg_right ?_ he.nonneg)
      (he.one_sub_norm_sub_smul_le_mul_mul (IsSelfAdjoint.star_mul_self b))
    rw [dist_comm, dist_eq_norm] at hpe
    linarith
  have h := hτ.smul_mem_finitePart 2
    (hτ.mem_finitePart_of_le hfin (smul_nonneg (by norm_num) he.nonneg) hle)
  rwa [smul_smul, NNReal.coe_ofNat, mul_one_div_cancel two_ne_zero, one_smul] at h

/-- **Projections have finite trace.** For a densely defined trace `τ`, every projection `e`
satisfies `τ(e) < ∞` (Thomsen [WTK], Lemma 4.11). -/
theorem lt_top_of_isStarProjection (hτ : IsTrace τ) (hd : IsDenselyDefined τ) {e : B}
    (he : IsStarProjection e) : τ e < ∞ :=
  (mem_finitePart.1 (hτ.mem_finitePart_of_isStarProjection hd he)).2

/-- A projection lies in the domain `𝔪_τ` of a densely defined trace. -/
theorem mem_domain_of_isStarProjection (hτ : IsTrace τ) (hd : IsDenselyDefined τ) {e : B}
    (he : IsStarProjection e) : e ∈ domain τ :=
  finitePart_subset_domain (τ := τ) (hτ.mem_finitePart_of_isStarProjection hd he)

end IsTrace

end TauCeti
