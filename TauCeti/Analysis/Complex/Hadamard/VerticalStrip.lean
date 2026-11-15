/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.OrderOne
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Summability

/-!
# Real-part partial fractions for order-one entire functions with zeros in a vertical strip

For a general entire function `f` of order at most one with `f 0 ≠ 0`, the partial-fraction
expansion `logDeriv f z = logDeriv f 0 + ∑' ρ, m_ρ (1 / (z - ρ) + 1 / ρ)` requires pairing
`1 / (z - ρ)` with `1 / ρ`: when the zeros grow along the real axis, as for `sin (π z)`, neither
`∑ m_ρ (1 / ρ)` nor its real part converges absolutely.

When the zeros of `f` have bounded real parts — that is, lie in a vertical strip — each real part
satisfies `|(1 / (z - ρ)).re| = |z.re - ρ.re| / ‖z - ρ‖ ^ 2 = O(‖ρ‖ ^ (-2))`. At any order strictly
below two, inverse-square summability of the zeros therefore makes the real-part series
`∑_ρ m_ρ (1 / (z - ρ)).re` and `∑_ρ m_ρ (1 / ρ).re` converge absolutely on their own, so at order
at most one the paired real-part expansion splits into two separate sums.

If in addition the analytic zero multiplicities are invariant under reflection `s ↦ a - conj s`
across a vertical line `Re s = a / 2` (`a : ℝ`), with `f a ≠ 0` and
`(logDeriv f a).re = -(logDeriv f 0).re`, reindexing at `z = a` equates the two zero sums and gives
`(logDeriv f 0).re = -∑' ρ, m_ρ (1 / ρ).re`. Cancelling the constant term yields the unpaired
identity `(logDeriv f z).re = ∑' ρ, m_ρ (1 / (z - ρ)).re` at every point `z` where `f z ≠ 0`,
together with positivity and finite-subset lower bounds to the right of all zeros. Multiply `f` by
`exp (c z)` for real `c ≠ 0` to see that the antisymmetry hypothesis on `logDeriv f` cannot be
dropped: the zeros are unchanged while `(logDeriv · 0).re` shifts by `c`.

## Main results

* `TauCeti.OrderLE.summable_norm_analyticOrderNatAt_mul_re_one_div_sub` and
  `TauCeti.OrderLE.summable_norm_analyticOrderNatAt_mul_re_one_div`: absolute convergence of the
  real-part reciprocal series over zeros in a vertical strip at every order below two.
* `TauCeti.OrderLE.re_logDeriv_eq_add_tsum`: the split real-part partial-fraction expansion at
  order at most one.
* `TauCeti.OrderLE.re_logDeriv_zero_eq_neg_tsum` and `TauCeti.OrderLE.re_logDeriv_eq_tsum`:
  cancellation of `(logDeriv f 0).re` under reflection symmetry across `Re s = a / 2`.
* `TauCeti.isBounded_re_divisor_support_of_le`, `TauCeti.OrderLE.re_logDeriv_nonneg`, and
  `TauCeti.OrderLE.sum_analyticOrderNatAt_mul_re_one_div_sub_le`: strip boundedness from a one-sided
  zero bound, nonnegativity, and finite-sum retention to the right of the zeros.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 12 and 14.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), Theorem 10.16 and
  Corollary 10.18, pp. 351–353.
-/

public section

open Complex ComplexConjugate Filter Metric Topology Bornology
open scoped BigOperators

namespace TauCeti

variable {f : ℂ → ℂ}

/-- For an entire function, any sequence weighted by `analyticOrderNatAt f` is supported inside the
whole-plane divisor support of `f`. -/
private theorem support_analyticOrderNatAt_mul_subset {M : Type*} [MulZeroClass M]
    (hf : Differentiable ℂ f) (c : ℕ → M) (hc : c 0 = 0) (g : ℂ → M) :
    Function.support (fun ρ : ℂ ↦ c (analyticOrderNatAt f ρ) * g ρ) ⊆
      (MeromorphicOn.divisor f Set.univ).support := by
  have ha : AnalyticOnNhd ℂ f Set.univ := fun w _ ↦ hf.analyticAt w
  intro ρ hρ
  by_contra hns
  rw [Function.notMem_support,
    ha.meromorphicOn.divisor_eq_analyticOrderNatAt (ha ρ (Set.mem_univ ρ)) (Set.mem_univ ρ),
    Int.natCast_eq_zero] at hns
  exact hρ (by simp [hns, hc])

/-! ### Absolute summability of real parts in a vertical strip -/

/-- When an entire function of order less than two has zeros of bounded real part, the real parts
`(analyticOrderNatAt f ρ : ℝ) * (1 / (z - ρ)).re` are absolutely summable over `ℂ` for every `z`
(under total division at `ρ = z`). -/
theorem OrderLE.summable_norm_analyticOrderNatAt_mul_re_one_div_sub {A : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hA : A < 2)
    (hre : IsBounded (Complex.re '' (MeromorphicOn.divisor f Set.univ).support)) (z : ℂ) :
    Summable (fun ρ : ℂ ↦ ‖(analyticOrderNatAt f ρ : ℝ) * (1 / (z - ρ)).re‖) := by
  set d := MeromorphicOn.divisor f Set.univ
  have ha : AnalyticOnNhd ℂ f Set.univ := fun w _ ↦ hf.analyticAt w
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp hre
  set K : ℝ := |z.re| + max B 0
  have : 0 ≤ K := by positivity
  -- On `d.support`, compare cofinitely against `4 K m_ρ ‖ρ⁻¹‖ ^ 2`.
  have hsub : Summable (fun ρ : d.support ↦
      ‖(analyticOrderNatAt f (ρ : ℂ) : ℝ) * (1 / (z - (ρ : ℂ))).re‖) := by
    refine ((h.summable_divisor_toNat_mul_norm_inv_sq hf hA).mul_left (4 * K))
      |>.of_norm_bounded_eventually ?_
    filter_upwards [(MeromorphicOn.divisor_norm_sublevel_finite f
      (2 * ‖z‖)).eventually_cofinite_notMem] with ρ hρ
    have : 2 * ‖z‖ < ‖(ρ : ℂ)‖ := lt_of_not_ge hρ
    have : 0 < ‖(ρ : ℂ)‖ := by linarith [norm_nonneg z]
    have hhalf : ‖(ρ : ℂ)‖ / 2 ≤ ‖z - (ρ : ℂ)‖ := by
      have htri := norm_sub_norm_le (ρ : ℂ) z
      rw [norm_sub_rev] at htri
      linarith
    have hreB : |(ρ : ℂ).re| ≤ max B 0 := by
      refine (le_trans ?_ (le_max_left B 0))
      simpa only [Real.norm_eq_abs] using hB (ρ : ℂ).re ⟨ρ, ρ.property, rfl⟩
    have hnum : |(z - (ρ : ℂ)).re| ≤ K := by
      rw [sub_re]
      exact (abs_sub _ _).trans (by linarith [hreB])
    have hord : (d ρ).toNat = analyticOrderNatAt f ρ := by
      rw [ha.meromorphicOn.divisor_eq_analyticOrderNatAt (ha ρ (Set.mem_univ ρ)) (Set.mem_univ ρ),
        Int.toNat_natCast]
    rw [Real.norm_eq_abs, abs_norm, norm_mul, RCLike.norm_natCast, Real.norm_eq_abs, one_div,
      Complex.inv_re, Complex.normSq_eq_norm_sq, abs_div,
      abs_of_nonneg (sq_nonneg ‖z - (ρ : ℂ)‖), ← hord]
    calc ((d ρ).toNat : ℝ) * (|(z - (ρ : ℂ)).re| / ‖z - (ρ : ℂ)‖ ^ 2)
        ≤ ((d ρ).toNat : ℝ) * (K / (‖(ρ : ℂ)‖ / 2) ^ 2) := by
          gcongr
      _ = 4 * K * (((d ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2) := by
          rw [norm_inv]
          field_simp
          ring
  have hsupp : Function.support
      (fun ρ : ℂ ↦ ‖(analyticOrderNatAt f ρ : ℝ) * (1 / (z - ρ)).re‖) ⊆ d.support := by
    simpa only [norm_mul, RCLike.norm_natCast] using
      support_analyticOrderNatAt_mul_subset hf Nat.cast Nat.cast_zero
        (fun ρ ↦ ‖(1 / (z - ρ)).re‖)
  exact ((hasSum_subtype_iff_of_support_subset hsupp).mp hsub.hasSum).summable

/-- Summability of the signed real-part partial-fraction series `(analyticOrderNatAt f ρ) *
Re (1 / (z - ρ))` over `ℂ` when the zeros have bounded real part and the order is below two. -/
theorem OrderLE.summable_analyticOrderNatAt_mul_re_one_div_sub {A : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hA : A < 2)
    (hre : IsBounded (Complex.re '' (MeromorphicOn.divisor f Set.univ).support)) (z : ℂ) :
    Summable (fun ρ : ℂ ↦ (analyticOrderNatAt f ρ : ℝ) * (1 / (z - ρ)).re) :=
  (h.summable_norm_analyticOrderNatAt_mul_re_one_div_sub hf hA hre z).of_norm

/-- When an entire function of order less than two has zeros of bounded real part, the reciprocal
real parts `(analyticOrderNatAt f ρ : ℝ) * (1 / ρ).re` are absolutely summable over `ℂ`. -/
theorem OrderLE.summable_norm_analyticOrderNatAt_mul_re_one_div {A : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hA : A < 2)
    (hre : IsBounded (Complex.re '' (MeromorphicOn.divisor f Set.univ).support)) :
    Summable (fun ρ : ℂ ↦ ‖(analyticOrderNatAt f ρ : ℝ) * (1 / ρ).re‖) := by
  simpa only [zero_sub, div_neg, neg_re, mul_neg, norm_neg] using
    h.summable_norm_analyticOrderNatAt_mul_re_one_div_sub hf hA hre 0

/-- Summability of `(analyticOrderNatAt f ρ : ℝ) * (1 / ρ).re` over `ℂ` when the zeros have bounded
real part and the order is below two. -/
theorem OrderLE.summable_analyticOrderNatAt_mul_re_one_div {A : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hA : A < 2)
    (hre : IsBounded (Complex.re '' (MeromorphicOn.divisor f Set.univ).support)) :
    Summable (fun ρ : ℂ ↦ (analyticOrderNatAt f ρ : ℝ) * (1 / ρ).re) :=
  (h.summable_norm_analyticOrderNatAt_mul_re_one_div hf hA hre).of_norm

/-! ### Unpaired real-part partial-fraction expansion and reflection cancellation -/

/-- **Split real-part partial fractions.** Off the zeros of an entire function `f` of order at most
one with `f 0 ≠ 0` whose zeros have bounded real part,
`(logDeriv f z).re = (logDeriv f 0).re + ∑_ρ m_ρ Re (1 / (z - ρ)) + ∑_ρ m_ρ Re (1 / ρ)`. -/
theorem OrderLE.re_logDeriv_eq_add_tsum (h : OrderLE f 1) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (hre : IsBounded (Complex.re '' (MeromorphicOn.divisor f Set.univ).support))
    {z : ℂ} (hz : f z ≠ 0) :
    (logDeriv f z).re = (logDeriv f 0).re +
      (∑' ρ : ℂ, (analyticOrderNatAt f ρ : ℝ) * (1 / (z - ρ)).re) +
      ∑' ρ : ℂ, (analyticOrderNatAt f ρ : ℝ) * (1 / ρ).re := by
  set d := MeromorphicOn.divisor f Set.univ
  have ha : AnalyticOnNhd ℂ f Set.univ := fun w _ ↦ hf.analyticAt w
  have hpair := (h.summable_norm_divisor_mul_one_div_sub_add_one_div hf hf0 (by norm_num)
    hz).of_norm
  have hs₁ : Summable (fun ρ : d.support ↦
      (analyticOrderNatAt f (ρ : ℂ) : ℝ) * (1 / (z - (ρ : ℂ))).re) :=
    (h.summable_analyticOrderNatAt_mul_re_one_div_sub hf (by norm_num) hre z).comp_injective
      Subtype.val_injective
  have hs₂ : Summable (fun ρ : d.support ↦
      (analyticOrderNatAt f (ρ : ℂ) : ℝ) * (1 / (ρ : ℂ)).re) :=
    (h.summable_analyticOrderNatAt_mul_re_one_div hf (by norm_num) hre).comp_injective
      Subtype.val_injective
  have hterm (ρ : d.support) :
      (((d ρ).toNat : ℂ) * (1 / (z - (ρ : ℂ)) + 1 / (ρ : ℂ))).re =
        (analyticOrderNatAt f (ρ : ℂ) : ℝ) * (1 / (z - (ρ : ℂ))).re +
          (analyticOrderNatAt f (ρ : ℂ) : ℝ) * (1 / (ρ : ℂ)).re := by
    have hord : (d ρ).toNat = analyticOrderNatAt f ρ := by
      rw [ha.meromorphicOn.divisor_eq_analyticOrderNatAt (ha ρ (Set.mem_univ ρ)) (Set.mem_univ ρ),
        Int.toNat_natCast]
    rw [hord, ← Complex.ofReal_natCast, Complex.re_ofReal_mul, add_re, mul_add]
  rw [h.logDeriv_eq_add_tsum hf hf0 hz, add_re, Complex.re_tsum hpair,
    tsum_congr hterm, hs₁.tsum_add hs₂,
    tsum_subtype_eq_of_support_subset
      (f := fun ρ : ℂ ↦ (analyticOrderNatAt f ρ : ℝ) * (1 / (z - ρ)).re)
      (support_analyticOrderNatAt_mul_subset hf Nat.cast Nat.cast_zero _),
    tsum_subtype_eq_of_support_subset
      (f := fun ρ : ℂ ↦ (analyticOrderNatAt f ρ : ℝ) * (1 / ρ).re)
      (support_analyticOrderNatAt_mul_subset hf Nat.cast Nat.cast_zero _),
    add_assoc]

/-- **Real-part cancellation of the Hadamard constant.** If an entire function `f` of order at most
one has zeros of bounded real part whose multiplicities are invariant under reflection
`s ↦ a - conj s` across the vertical line `Re s = a / 2` (`a : ℝ`), with `f 0 ≠ 0`, `f a ≠ 0`, and
`(logDeriv f a).re = -(logDeriv f 0).re`, then
`(logDeriv f 0).re = -∑' ρ, (analyticOrderNatAt f ρ : ℝ) * (1 / ρ).re`. -/
theorem OrderLE.re_logDeriv_zero_eq_neg_tsum (h : OrderLE f 1) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (hre : IsBounded (Complex.re '' (MeromorphicOn.divisor f Set.univ).support))
    {a : ℝ} (hfa : f a ≠ 0)
    (hord : ∀ s : ℂ, analyticOrderNatAt f (a - conj s) = analyticOrderNatAt f s)
    (hlog : (logDeriv f a).re = -(logDeriv f 0).re) :
    (logDeriv f 0).re = -∑' ρ : ℂ, (analyticOrderNatAt f ρ : ℝ) * (1 / ρ).re := by
  have hat := h.re_logDeriv_eq_add_tsum hf hf0 hre hfa
  let φ : ℂ ≃ ℂ :=
    ⟨fun ρ ↦ (a : ℂ) - conj ρ, fun ρ ↦ (a : ℂ) - conj ρ, fun ρ ↦ by simp, fun ρ ↦ by simp⟩
  have hsymm : (∑' ρ : ℂ, (analyticOrderNatAt f ρ : ℝ) * (1 / ((a : ℂ) - ρ)).re) =
      ∑' ρ : ℂ, (analyticOrderNatAt f ρ : ℝ) * (1 / ρ).re := by
    rw [← φ.tsum_eq]
    refine tsum_congr fun ρ ↦ ?_
    simp only [φ, Equiv.coe_fn_mk, hord ρ, sub_sub_cancel, one_div, ← map_inv₀, conj_re]
  linarith

/-- **Unpaired real-part partial fractions under reflection symmetry.** Under the hypotheses of
`OrderLE.re_logDeriv_zero_eq_neg_tsum`, at every `z` with `f z ≠ 0`,
`(logDeriv f z).re = ∑' ρ, (analyticOrderNatAt f ρ : ℝ) * (1 / (z - ρ)).re`. -/
theorem OrderLE.re_logDeriv_eq_tsum (h : OrderLE f 1) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (hre : IsBounded (Complex.re '' (MeromorphicOn.divisor f Set.univ).support))
    {a : ℝ} (hfa : f a ≠ 0)
    (hord : ∀ s : ℂ, analyticOrderNatAt f (a - conj s) = analyticOrderNatAt f s)
    (hlog : (logDeriv f a).re = -(logDeriv f 0).re) {z : ℂ} (hz : f z ≠ 0) :
    (logDeriv f z).re = ∑' ρ : ℂ, (analyticOrderNatAt f ρ : ℝ) * (1 / (z - ρ)).re := by
  rw [h.re_logDeriv_eq_add_tsum hf hf0 hre hz,
    h.re_logDeriv_zero_eq_neg_tsum hf hf0 hre hfa hord hlog]
  ring

/-! ### Positivity and finite-subset bounds to the right of all zeros -/

/-- If an entire function `f` with `f 0 ≠ 0` has zero multiplicities symmetric under
`s ↦ a - conj s` and all its zeros satisfy `ρ.re ≤ B`, then all its zeros lie in `[a - B, B]`, so
the real parts of its divisor support are bounded. -/
theorem isBounded_re_divisor_support_of_le (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) {a B : ℝ}
    (hord : ∀ s : ℂ, analyticOrderNatAt f (a - conj s) = analyticOrderNatAt f s)
    (hle : ∀ ρ, f ρ = 0 → ρ.re ≤ B) :
    IsBounded (Complex.re '' (MeromorphicOn.divisor f Set.univ).support) := by
  have ha : AnalyticOnNhd ℂ f Set.univ := fun w _ ↦ hf.analyticAt w
  refine (Metric.isBounded_Icc (a - B) B).subset ?_
  rintro _ ⟨ρ, hρ, rfl⟩
  have hfz : f ρ = 0 := by
    by_contra hne
    exact (hf.analyticAt ρ).notMem_divisor_support_of_ne_zero (U := Set.univ) hne hρ
  have htop : analyticOrderAt f ρ ≠ ⊤ := by
    refine ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (x := 0) trivial trivial ?_
    rw [(hf.analyticAt 0).analyticOrderAt_eq_zero.mpr hf0]
    simp
  have hne : analyticOrderNatAt f ρ ≠ 0 := by
    rw [← Nat.cast_ne_zero (R := ℕ∞), Nat.cast_analyticOrderNatAt htop]
    exact (hf.analyticAt ρ).analyticOrderAt_ne_zero.mpr hfz
  have hsymm : f (a - conj ρ) = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero (hord ρ ▸ hne)
  have hsymm_le := hle (a - conj ρ) hsymm
  simp only [sub_re, ofReal_re, conj_re] at hsymm_le
  exact ⟨by linarith, hle ρ hfz⟩

/-- At a point `z` whose real part is at least the real part of every zero of `f`, every summand
`(analyticOrderNatAt f ρ : ℝ) * (1 / (z - ρ)).re` is nonnegative. -/
private theorem analyticOrderNatAt_mul_re_one_div_sub_nonneg (hf : Differentiable ℂ f) {z : ℂ}
    (hle : ∀ ρ, f ρ = 0 → ρ.re ≤ z.re) (ρ : ℂ) :
    0 ≤ (analyticOrderNatAt f ρ : ℝ) * (1 / (z - ρ)).re := by
  by_cases hρ : f ρ = 0
  · have hsub : 0 ≤ (z - ρ).re := by
      rw [sub_re]
      linarith [hle ρ hρ]
    rw [one_div, Complex.inv_re]
    exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg hsub (Complex.normSq_nonneg _))
  · rw [analyticOrderNatAt, (hf.analyticAt ρ).analyticOrderAt_eq_zero.mpr hρ, ENat.toNat_zero,
      Nat.cast_zero, zero_mul]

/-- Under reflection symmetry across `Re s = a / 2`, `(logDeriv f z).re` is nonnegative at every
nonzero value `f z ≠ 0` lying to the right of all zeros of `f`. -/
theorem OrderLE.re_logDeriv_nonneg (h : OrderLE f 1) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) {a : ℝ} (hfa : f a ≠ 0)
    (hord : ∀ s : ℂ, analyticOrderNatAt f (a - conj s) = analyticOrderNatAt f s)
    (hlog : (logDeriv f a).re = -(logDeriv f 0).re) {z : ℂ} (hz : f z ≠ 0)
    (hle : ∀ ρ, f ρ = 0 → ρ.re ≤ z.re) :
    0 ≤ (logDeriv f z).re := by
  have hre := isBounded_re_divisor_support_of_le hf hf0 hord hle
  rw [h.re_logDeriv_eq_tsum hf hf0 hre hfa hord hlog hz]
  exact tsum_nonneg (analyticOrderNatAt_mul_re_one_div_sub_nonneg hf hle)

/-- **Finite-subset retention.** Under reflection symmetry across `Re s = a / 2`, at any point `z`
with `f z ≠ 0` lying to the right of all zeros of `f`, any finite sum of zero terms is bounded by
`(logDeriv f z).re`. -/
theorem OrderLE.sum_analyticOrderNatAt_mul_re_one_div_sub_le (h : OrderLE f 1)
    (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) {a : ℝ} (hfa : f a ≠ 0)
    (hord : ∀ s : ℂ, analyticOrderNatAt f (a - conj s) = analyticOrderNatAt f s)
    (hlog : (logDeriv f a).re = -(logDeriv f 0).re) {z : ℂ} (hz : f z ≠ 0)
    (hle : ∀ ρ, f ρ = 0 → ρ.re ≤ z.re) (S : Finset ℂ) :
    (∑ ρ ∈ S, (analyticOrderNatAt f ρ : ℝ) * (1 / (z - ρ)).re) ≤ (logDeriv f z).re := by
  have hre := isBounded_re_divisor_support_of_le hf hf0 hord hle
  rw [h.re_logDeriv_eq_tsum hf hf0 hre hfa hord hlog hz]
  exact Summable.sum_le_tsum S (fun ρ _ ↦ analyticOrderNatAt_mul_re_one_div_sub_nonneg hf hle ρ)
    (h.summable_analyticOrderNatAt_mul_re_one_div_sub hf (by norm_num) hre z)

/-! ### Examples -/

/-- Multiplying by `exp z` leaves the divisor empty (hence symmetric across every vertical line)
while giving `(logDeriv exp 0).re = 1 ≠ 0`, showing why the antisymmetry condition on `logDeriv`
in `OrderLE.re_logDeriv_zero_eq_neg_tsum` cannot be dropped. -/
example :
    (MeromorphicOn.divisor exp Set.univ).support = ∅ ∧
      (logDeriv exp 0).re = 1 ∧
      -(∑' ρ : ℂ, (analyticOrderNatAt exp ρ : ℝ) * (1 / ρ).re) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · ext z
    simp [(differentiable_exp.analyticAt z).notMem_divisor_support_of_ne_zero (exp_ne_zero z)]
  · rw [logDeriv_apply, Complex.deriv_exp, div_self (exp_ne_zero 0), one_re]
  · have hz (ρ : ℂ) : analyticOrderNatAt exp ρ = 0 := by
      rw [analyticOrderNatAt, (differentiable_exp.analyticAt ρ).analyticOrderAt_eq_zero.mpr
        (exp_ne_zero ρ), ENat.toNat_zero]
    simp [hz]

end TauCeti
