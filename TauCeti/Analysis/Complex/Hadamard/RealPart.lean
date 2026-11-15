/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.OrderOne
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Summability
import TauCeti.Analysis.Meromorphic.Divisor

/-!
# Real parts of the Hadamard partial fractions

Let `f` be entire of order at most one with `f 0 ≠ 0`, zero multiplicities `m_ρ` read from its
divisor on `ℂ`, and `b = logDeriv f 0`, so that off the zeros
`logDeriv f s = b + ∑_ρ m_ρ (1 / (s - ρ) + 1 / ρ)`
(`TauCeti.OrderLE.logDeriv_eq_add_tsum`). If the real parts of the zeros are bounded, the real
parts `m_ρ Re (1 / ρ)` and `m_ρ Re (1 / (s - ρ))` are separately summable, so the real part of the
expansion splits into two sums.

Suppose moreover that the zeros satisfy `0 ≤ Re ρ`, and that the reflection `s ↦ 1 - conj s`
preserves the divisor and reflects the logarithmic derivative:
`logDeriv f (1 - conj s) = -conj (logDeriv f s)`. Both follow from a functional equation
`f (1 - s) = ε conj (f (conj s))` with `ε ≠ 0`, as for the entire completions of Dirichlet
L-functions, of the Riemann zeta function and of Dedekind zeta functions. For the entire
completion of an analytic L-function record with a functional equation, the divisor hypothesis
is `AnalyticLFunctionData.HasFunctionalEquation.divisor_entireCompletion_one_sub_conj`.
Comparing the real parts of the expansions at `0` and at `1 = 1 - conj 0`, and reindexing the
zeros by `ρ ↦ 1 - conj ρ`, gives

  `Re b = -∑_ρ m_ρ Re (1 / ρ)`,

so `Re (logDeriv f s) = ∑_ρ m_ρ Re (1 / (s - ρ))` off the zeros. No hypothesis of the form
`f (conj s) = conj (f s)` is needed. The identity fails without the reflection hypotheses, since
multiplying `f` by `exp (c s)` changes `b` and no zero.

Each summand `m_ρ Re (1 / (s - ρ))` is nonnegative when every zero has `Re ρ ≤ Re s`, and the
summand at a zero is positive when `Re ρ < Re s`.

## Main results

* `TauCeti.OrderLE.summable_divisor_mul_re_one_div` and
  `TauCeti.OrderLE.summable_divisor_mul_re_one_div_sub`: summability of the real parts.
* `TauCeti.OrderLE.re_logDeriv_zero_eq_neg_tsum`: `Re b = -∑_ρ m_ρ Re (1 / ρ)`.
* `TauCeti.OrderLE.re_logDeriv_eq_tsum`: `Re (logDeriv f s) = ∑_ρ m_ρ Re (1 / (s - ρ))`.
* `TauCeti.tsum_divisor_mul_re_one_div_sub_nonneg` and `TauCeti.OrderLE.re_logDeriv_nonneg`:
  positivity to the right of the zeros.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), Corollary 10.18,
  (10.37)–(10.38).
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 12.
-/

public section

open Complex ComplexConjugate

namespace TauCeti

variable {f : ℂ → ℂ}

/-- An entire function nonzero at the origin is nonzero wherever its divisor vanishes. -/
private theorem ne_zero_of_divisor_eq_zero (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) {z : ℂ}
    (hz : MeromorphicOn.divisor f Set.univ z = 0) : f z ≠ 0 := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun w _ ↦ hf.analyticAt w
  have htop : analyticOrderAt f z ≠ ⊤ :=
    hfa.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ 0)
      (Set.mem_univ z) (by simp [(hf.analyticAt 0).analyticOrderAt_eq_zero.mpr hf0])
  intro hfz
  have := (hfa.meromorphicOn.zero_lt_divisor_iff_of_analyticAt (hf.analyticAt z)
    (Set.mem_univ z) (by simp [(hf.analyticAt z).meromorphicOrderAt_eq, htop])).mpr hfz
  omega

/-- Reindexing the zeros by a reflection `ρ ↦ 1 - conj ρ` that preserves the divisor. -/
private theorem tsum_divisor_mul_comp_one_sub_conj
    (hdiv : ∀ s, MeromorphicOn.divisor f Set.univ (1 - conj s) =
      MeromorphicOn.divisor f Set.univ s) (g : ℂ → ℝ) :
    ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * g (1 - conj (ρ : ℂ)) =
      ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * g ρ := by
  have hinv : Function.Involutive fun s : ℂ ↦ 1 - conj s := fun s ↦ by simp
  let e : (MeromorphicOn.divisor f Set.univ).support ≃ (MeromorphicOn.divisor f Set.univ).support :=
    (hinv.toPerm _).subtypeEquiv fun s ↦ by
      simp only [Function.mem_support, Function.Involutive.coe_toPerm, hdiv]
  conv_rhs => rw [← e.tsum_eq]
  simp only [e, Equiv.subtypeEquiv_apply, Function.Involutive.coe_toPerm, hdiv]

/-- If the divisor is preserved by `s ↦ 1 - conj s` and every zero has `0 ≤ Re ρ`, then every
zero has `|Re ρ| ≤ 1`. -/
private theorem abs_re_le_one_of_divisor_pos
    (hdiv : ∀ s, MeromorphicOn.divisor f Set.univ (1 - conj s) =
      MeromorphicOn.divisor f Set.univ s)
    (hre : ∀ ρ, 0 < MeromorphicOn.divisor f Set.univ ρ → 0 ≤ ρ.re) (ρ : ℂ)
    (hρ : 0 < MeromorphicOn.divisor f Set.univ ρ) : |ρ.re| ≤ 1 := by
  have h1 := hre _ ((hdiv ρ).symm ▸ hρ)
  simp only [sub_re, one_re, conj_re] at h1
  exact abs_le.mpr ⟨by linarith [hre ρ hρ], by linarith⟩

/-- If the real parts of the zeros are bounded, the real parts `m_ρ Re (1 / ρ)` form a summable
family. -/
theorem OrderLE.summable_divisor_mul_re_one_div {A C : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hA : A < 2)
    (hre : ∀ ρ, 0 < MeromorphicOn.divisor f Set.univ ρ → |ρ.re| ≤ C) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re) := by
  refine ((h.summable_divisor_toNat_mul_norm_inv_sq hf hA).mul_left C).of_norm_bounded
    fun ρ ↦ ?_
  rcases le_or_gt (MeromorphicOn.divisor f Set.univ ρ) 0 with hd | hd
  · simp [Int.toNat_of_nonpos hd]
  have hC := hre ρ hd
  rw [norm_mul, Real.norm_natCast, Real.norm_eq_abs, mul_left_comm]
  gcongr
  rw [one_div, inv_re, abs_div, abs_of_nonneg (normSq_nonneg _), norm_inv, inv_pow,
    Complex.sq_norm, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hC (inv_nonneg.mpr (normSq_nonneg _))

/-- If the real parts of the zeros are bounded, the real parts `m_ρ Re (1 / (s - ρ))` form a
summable family off the zeros. The complex terms `m_ρ / (s - ρ)` need not be absolutely
summable. -/
theorem OrderLE.summable_divisor_mul_re_one_div_sub {A C : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) (hA : A < 2)
    (hre : ∀ ρ, 0 < MeromorphicOn.divisor f Set.univ ρ → |ρ.re| ≤ C) {s : ℂ} (hs : f s ≠ 0) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re) := by
  refine (((h.summable_norm_divisor_mul_one_div_sub_add_one_div hf hf0 hA hs).of_norm.mapL
    reCLM).sub (h.summable_divisor_mul_re_one_div hf hA hre)).congr fun ρ ↦ ?_
  simp only [reCLM_apply, mul_re, natCast_re, natCast_im, add_re, zero_mul, sub_zero]
  ring

/-- If the real parts of the zeros are bounded, the real part of the partial-fraction expansion
splits into two sums. -/
theorem OrderLE.re_logDeriv_eq_add_tsum_add_tsum {C : ℝ} (h : OrderLE f 1)
    (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hre : ∀ ρ, 0 < MeromorphicOn.divisor f Set.univ ρ → |ρ.re| ≤ C) {s : ℂ} (hs : f s ≠ 0) :
    (logDeriv f s).re = (logDeriv f 0).re +
      ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re +
      ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re := by
  rw [h.logDeriv_eq_add_tsum hf hf0 hs, add_re,
    re_tsum (h.summable_norm_divisor_mul_one_div_sub_add_one_div hf hf0 (by norm_num) hs).of_norm,
    add_assoc, ← (h.summable_divisor_mul_re_one_div_sub hf hf0 (by norm_num) hre hs).tsum_add
      (h.summable_divisor_mul_re_one_div hf (by norm_num) hre)]
  congr 2
  funext ρ
  simp only [mul_re, natCast_re, natCast_im, add_re, zero_mul, sub_zero]
  ring

/-- **The real part of `b`.** Let `f` be entire of order at most one with `f 0 ≠ 0`, whose zeros
satisfy `0 ≤ Re ρ`, whose divisor is preserved by `s ↦ 1 - conj s`, and whose logarithmic
derivative satisfies `logDeriv f (1 - conj s) = -conj (logDeriv f s)`. Then
`Re (logDeriv f 0) = -∑_ρ m_ρ Re (1 / ρ)`. -/
theorem OrderLE.re_logDeriv_zero_eq_neg_tsum (h : OrderLE f 1) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0)
    (hdiv : ∀ s, MeromorphicOn.divisor f Set.univ (1 - conj s) =
      MeromorphicOn.divisor f Set.univ s)
    (hlog : ∀ s, logDeriv f (1 - conj s) = -conj (logDeriv f s))
    (hre : ∀ ρ, 0 < MeromorphicOn.divisor f Set.univ ρ → 0 ≤ ρ.re) :
    (logDeriv f 0).re = -∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re := by
  have hre' := abs_re_le_one_of_divisor_pos hdiv hre
  have h1 : f 1 ≠ 0 := ne_zero_of_divisor_eq_zero hf hf0 <| by
    simpa using (hdiv 0).trans (Function.notMem_support.mp
      ((hf.analyticAt 0).notMem_divisor_support_of_ne_zero hf0))
  have hFE := congrArg re (hlog 0)
  simp only [map_zero, sub_zero, neg_re, conj_re] at hFE
  rw [h.re_logDeriv_eq_add_tsum_add_tsum hf hf0 hre' h1] at hFE
  have hreflect := tsum_divisor_mul_comp_one_sub_conj hdiv fun ρ ↦ (1 / (1 - ρ)).re
  simp only [sub_sub_cancel, one_div, ← map_inv₀, conj_re] at hreflect
  simp only [one_div] at hFE ⊢
  linarith

/-- **The real part of `logDeriv f` as a sum over zeros.** Under the hypotheses of
`TauCeti.OrderLE.re_logDeriv_zero_eq_neg_tsum`, off the zeros
`Re (logDeriv f s) = ∑_ρ m_ρ Re (1 / (s - ρ))`. -/
theorem OrderLE.re_logDeriv_eq_tsum (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hdiv : ∀ s, MeromorphicOn.divisor f Set.univ (1 - conj s) =
      MeromorphicOn.divisor f Set.univ s)
    (hlog : ∀ s, logDeriv f (1 - conj s) = -conj (logDeriv f s))
    (hre : ∀ ρ, 0 < MeromorphicOn.divisor f Set.univ ρ → 0 ≤ ρ.re) {s : ℂ} (hs : f s ≠ 0) :
    (logDeriv f s).re = ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re := by
  have hre' := abs_re_le_one_of_divisor_pos hdiv hre
  rw [h.re_logDeriv_eq_add_tsum_add_tsum hf hf0 hre' hs,
    h.re_logDeriv_zero_eq_neg_tsum hf hf0 hdiv hlog hre]
  ring

/-- A weighted summand `m_ρ Re (1 / (s - ρ))` is nonnegative if `Re ρ ≤ Re s` whenever `ρ` is a
zero. -/
theorem divisor_mul_re_one_div_sub_nonneg {s ρ : ℂ}
    (hre : 0 < MeromorphicOn.divisor f Set.univ ρ → ρ.re ≤ s.re) :
    0 ≤ ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re := by
  rcases le_or_gt (MeromorphicOn.divisor f Set.univ ρ) 0 with hd | hd
  · simp [Int.toNat_of_nonpos hd]
  refine mul_nonneg (Nat.cast_nonneg _) ?_
  rw [one_div, inv_re, sub_re]
  exact div_nonneg (sub_nonneg.mpr (hre hd)) (normSq_nonneg _)

/-- The weighted summand `m_ρ Re (1 / (s - ρ))` at a zero `ρ` with `Re ρ < Re s` is positive. -/
theorem divisor_mul_re_one_div_sub_pos {s ρ : ℂ} (hρ : 0 < MeromorphicOn.divisor f Set.univ ρ)
    (hre : ρ.re < s.re) :
    0 < ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re := by
  refine mul_pos (Nat.cast_pos.mpr (Int.pos_iff_toNat_pos.mp hρ)) ?_
  rwa [one_div, Complex.inv_re_pos, sub_re, sub_pos]

/-- **Positivity of the sum over zeros.** If every zero satisfies `Re ρ ≤ Re s`, then
`0 ≤ ∑_ρ m_ρ Re (1 / (s - ρ))`. -/
theorem tsum_divisor_mul_re_one_div_sub_nonneg {s : ℂ}
    (hre : ∀ ρ, 0 < MeromorphicOn.divisor f Set.univ ρ → ρ.re ≤ s.re) :
    0 ≤ ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re :=
  tsum_nonneg fun ρ ↦ divisor_mul_re_one_div_sub_nonneg (hre ρ)

/-- Under the hypotheses of `TauCeti.OrderLE.re_logDeriv_eq_tsum`, if every zero satisfies
`Re ρ ≤ Re s` and `f s ≠ 0`, then `0 ≤ Re (logDeriv f s)`. -/
theorem OrderLE.re_logDeriv_nonneg (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hdiv : ∀ s, MeromorphicOn.divisor f Set.univ (1 - conj s) =
      MeromorphicOn.divisor f Set.univ s)
    (hlog : ∀ s, logDeriv f (1 - conj s) = -conj (logDeriv f s))
    (hre : ∀ ρ, 0 < MeromorphicOn.divisor f Set.univ ρ → 0 ≤ ρ.re) {s : ℂ} (hs : f s ≠ 0)
    (hle : ∀ ρ, 0 < MeromorphicOn.divisor f Set.univ ρ → ρ.re ≤ s.re) :
    0 ≤ (logDeriv f s).re := by
  rw [h.re_logDeriv_eq_tsum hf hf0 hdiv hlog hre hs]
  exact tsum_divisor_mul_re_one_div_sub_nonneg hle

end TauCeti
