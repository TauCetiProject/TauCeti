/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.WienerIkehara.SharpCutoff
public import TauCeti.Order.Northcott.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Distribution.TestFunction.Approximation
import TauCeti.NumberTheory.LSeries.CoefficientGrowth
import TauCeti.NumberTheory.LSeries.Conjugate

/-!
# Smoothed and interval forms of the Wiener--Ikehara theorem for complex coefficients

For nonnegative real coefficients `f : ℕ → ℝ`, the Wiener--Ikehara theorem deduces the sharp
asymptotic `(∑_{1 ≤ n ≤ x} f n) / x → A` directly from continuous boundary data
`G s = LSeries f s - A / (s - 1)` on `Re s ≥ 1`: positivity supplies both the Chebyshev bound on
the partial sums and the Tauberian squeeze between smooth cutoffs.

For complex-valued coefficients `f : ℕ → ℂ`, these two roles separate:

* **Smoothed weights (`wienerIkehara_smoothed`).** Under the Chebyshev bound
  `∑_{1 ≤ n ≤ x} ‖f n‖ = O(x)` and continuous boundary data `(G, A)` on `Re s ≥ 1`, every
  continuous compactly supported test function `ψ : ℝ → ℂ` satisfies
  `((∑_{n ≥ 1} f n ψ (n / x)) / x) → A ∫_{(0, ∞)} ψ` as `x → ∞`. No sign or Tauberian hypothesis on
  `f` is assumed, `LSeriesSummable f s` on `Re s > 1` follows from the Chebyshev bound, and `ψ 0`
  need not vanish because `n = 0` is excluded from the sum and the Chebyshev bound controls the
  contribution of small positive ratios `0 < n / x ≤ δ` near `0`.
* **Interval and sharp cutoffs under a majorant (`wienerIkehara_interval`).** If `‖f n‖ ≤ g n` for
  all `n ≠ 0` and a sequence `g : ℕ → ℝ` whose Dirichlet series has its own summability on
  `Re s > 1` and continuous boundary data `(H, B)` on `Re s ≥ 1`, then
  `(S_f (b x) - S_f (a x)) / x → A (b - a)` for all `0 ≤ a ≤ b`, where `S_f` is
  `TauCeti.summatory (fun n : ℕ ↦ n)` on the zero-adjusted sequence
  `n ↦ if n = 0 then 0 else f n`. In particular, sequences bounded on positive indices
  (`‖f n‖ ≤ M` for `n ≠ 0`) satisfy the interval and sharp-cutoff asymptotics via the constant
  majorant `M` and `M ζ(s)`.
* **Necessity of the majorant
  (`exists_isBigO_sum_Icc_norm_id_and_continuousOn_eq_LSeries_and_not_tendsto_summatory_div`).**
  A Chebyshev bound on `f` alone does not imply the interval or sharp-cutoff form: the dyadic
  cancelling sequence with `f (2 ^ j) = 2 ^ j` and `f (2 ^ j + 1) = -2 ^ j` for `j ≥ 1` has
  `∑_{1 ≤ n ≤ x} ‖f n‖ ≤ 4 x` and continuous boundary data with `A = 0`, yet `S_f (x) / x`
  oscillates between `1` and `0`.

## Main results

* `TauCeti.LSeries.wienerIkehara_smoothed`: the smoothed Wiener--Ikehara asymptotic for complex
  coefficients under a Chebyshev bound and a continuous compactly supported test function `ψ`.
* `TauCeti.LSeries.wienerIkehara_interval`: the interval asymptotic
  `(S_f (b x) - S_f (a x)) / x → A (b - a)` for `0 ≤ a ≤ b` under a nonnegative majorant with
  continuous boundary data.
* `TauCeti.LSeries.wienerIkehara_of_norm_le`: the sharp-cutoff specialization
  `(∑_{1 ≤ n ≤ x} f n) / x → A` under a nonnegative majorant.
* `TauCeti.LSeries.wienerIkehara_interval_of_norm_le_const` and
  `TauCeti.LSeries.wienerIkehara_of_norm_le_const`: the interval and sharp-cutoff asymptotics for
  complex coefficients bounded on `n ≠ 0`.
* `exists_isBigO_sum_Icc_norm_id_and_continuousOn_eq_LSeries_and_not_tendsto_summatory_div`:
  counterexample showing that a Chebyshev bound and continuous boundary data without a majorant do
  not imply convergence of `S_f (x) / x`.

## Provenance

Compare `wiener_ikehara_smooth` and `WienerIkeharaInterval` in `PrimeNumberTheoremAnd/Wiener.lean`
of the Apache-2.0 `AxiomMath/PrimeNumberTheoremAnd` repository, revision
`2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`, which treat smooth test functions supported in
`(0, ∞)` with real residue and a separate summability hypothesis, and real nonnegative coefficients
on `[a, b)` with `0 < a ≤ b`. Derived here are complex residues, continuous test functions with
`ψ 0` unrestricted, summability from the Chebyshev bound, the majorant interval form including the
endpoint `a = 0`, and the dyadic counterexample.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.
-/

public section

open Asymptotics Complex Filter MeasureTheory Metric Real Set TopologicalSpace
open scoped ComplexOrder ContDiff Distributions Topology

namespace TauCeti.LSeries

/-! ### Continuous compactly supported weights -/

section Smoothed

/-- If `Δ` vanishes above `R`, then for `x > 0` the series
`∑' n, (if n = 0 then 0 else f n) * Δ (n / x)` reduces to the finite sum over `Icc 1 ⌊R * x⌋₊`. -/
private lemma tsum_if_ne_zero_mul_eq_sum_Icc (f : ℕ → ℂ) {Δ : ℝ → ℂ} {R x : ℝ}
    (hΔR : ∀ y, R < y → Δ y = 0) (hx : 0 < x) :
    (∑' n : ℕ, (if n = 0 then 0 else f n) * Δ (n / x)) =
      ∑ n ∈ Finset.Icc 1 ⌊R * x⌋₊, f n * Δ (n / x) := by
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊R * x⌋₊)]
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    simp [Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1]
  · intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    have hgt : ⌊R * x⌋₊ < n :=
      lt_of_not_ge fun hle ↦ hn (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn0, hle⟩)
    have hRx : R < (n : ℝ) / x := (lt_div_iff₀ hx).mpr (Nat.lt_of_floor_lt hgt)
    simp [hΔR _ hRx]

/-- Chebyshev bound on `(∑_{1 ≤ n ≤ ⌊R * x⌋₊} f n Δ (n / x)) / x` when `Δ` is bounded by `M₀`
on `(0, δ]` and by `ε` on `(δ, ∞)`. -/
private lemma norm_sum_Icc_mul_div_le {f : ℕ → ℂ} {Δ : ℝ → ℂ} {C M₀ ε δ R x : ℝ}
    (hC : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ‖f n‖ ≤ C * N)
    (hM₀ : 0 ≤ M₀) (hδ : 0 ≤ δ) (hR : 0 ≤ R) (hx : 0 < x)
    (hΔ₁ : ∀ y ∈ Ioc 0 δ, ‖Δ y‖ ≤ M₀) (hΔ₂ : ∀ y, δ < y → ‖Δ y‖ ≤ ε) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊R * x⌋₊, f n * Δ (n / x)) / x‖ ≤ C * (M₀ * δ + ε * R) := by
  have hC0 : 0 ≤ C := by
    simpa using (Finset.sum_nonneg fun n _ ↦ norm_nonneg (f n)).trans (hC 1)
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hΔ₂ (δ + 1) (by linarith))
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊R * x⌋₊) :
      ‖f n * Δ (n / x)‖ ≤
        (if n ≤ ⌊δ * x⌋₊ then ‖f n‖ * M₀ else 0) + ‖f n‖ * ε := by
    have hn1 : (0 : ℝ) < n := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
    rw [norm_mul]
    by_cases hnd : n ≤ ⌊δ * x⌋₊
    · have hy : (n : ℝ) / x ≤ δ :=
        (div_le_iff₀ hx).mpr ((Nat.le_floor_iff (mul_nonneg hδ hx.le)).mp hnd)
      simp only [hnd, ↓reduceIte]
      exact (mul_le_mul_of_nonneg_left (hΔ₁ _ ⟨div_pos hn1 hx, hy⟩) (norm_nonneg _)).trans
        (le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) hε))
    · have hy : δ < (n : ℝ) / x := (lt_div_iff₀ hx).mpr (Nat.lt_of_floor_lt (not_le.mp hnd))
      simp only [hnd, ↓reduceIte, zero_add]
      exact mul_le_mul_of_nonneg_left (hΔ₂ _ hy) (norm_nonneg _)
  have hsmall : ∑ n ∈ Finset.Icc 1 ⌊R * x⌋₊, (if n ≤ ⌊δ * x⌋₊ then ‖f n‖ * M₀ else 0) ≤
      C * (δ * x) * M₀ := by
    have hsub : ∑ n ∈ Finset.Icc 1 ⌊R * x⌋₊, (if n ≤ ⌊δ * x⌋₊ then ‖f n‖ * M₀ else 0) ≤
        ∑ n ∈ Finset.Icc 1 ⌊δ * x⌋₊, ‖f n‖ * M₀ := by
      rw [← Finset.sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn ↦ ?_)
        fun _ _ _ ↦ mul_nonneg (norm_nonneg _) hM₀
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1,
        (Finset.mem_filter.mp hn).2⟩
    refine hsub.trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right ((hC _).trans
      (mul_le_mul_of_nonneg_left (Nat.floor_le (mul_nonneg hδ hx.le)) hC0)) hM₀
  have hlarge : ∑ n ∈ Finset.Icc 1 ⌊R * x⌋₊, ‖f n‖ * ε ≤ C * (R * x) * ε := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right ((hC _).trans
      (mul_le_mul_of_nonneg_left (Nat.floor_le (mul_nonneg hR hx.le)) hC0)) hε
  rw [Complex.norm_div, Complex.norm_of_nonneg hx.le, div_le_iff₀ hx]
  calc ‖∑ n ∈ Finset.Icc 1 ⌊R * x⌋₊, f n * Δ (n / x)‖
      ≤ ∑ n ∈ Finset.Icc 1 ⌊R * x⌋₊, ‖f n * Δ (n / x)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊R * x⌋₊,
          ((if n ≤ ⌊δ * x⌋₊ then ‖f n‖ * M₀ else 0) + ‖f n‖ * ε) := Finset.sum_le_sum hpoint
    _ ≤ C * (δ * x) * M₀ + C * (R * x) * ε := by
          rw [Finset.sum_add_distrib]
          exact add_le_add hsmall hlarge
    _ = C * (M₀ * δ + ε * R) * x := by ring

/-- Integral bound on `∫_{(0, ∞)} Δ` under the same two-region estimate on `Δ`. -/
private lemma norm_setIntegral_Ioi_le {Δ : ℝ → ℂ} {M₀ ε δ R : ℝ}
    (hM₀ : 0 ≤ M₀) (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (hΔR : ∀ y, R < y → Δ y = 0)
    (hΔ₁ : ∀ y ∈ Ioc 0 δ, ‖Δ y‖ ≤ M₀) (hΔ₂ : ∀ y, δ < y → ‖Δ y‖ ≤ ε) :
    ‖∫ y in Ioi (0 : ℝ), Δ y‖ ≤ M₀ * δ + ε * R := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hΔ₂ (δ + 1) (by linarith))
  let b : ℝ → ℝ := fun y ↦ (Ioc 0 δ).indicator (fun _ ↦ M₀) y + (Ioc 0 R).indicator (fun _ ↦ ε) y
  have hb₁ : Integrable ((Ioc 0 δ).indicator (fun _ : ℝ ↦ M₀)) :=
    (integrableOn_const (hs := measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc
  have hb₂ : Integrable ((Ioc 0 R).indicator (fun _ : ℝ ↦ ε)) :=
    (integrableOn_const (hs := measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc
  have hle : ∀ y ∈ Ioi (0 : ℝ), ‖Δ y‖ ≤ b y := fun y (hy : 0 < y) ↦ by
    rcases le_or_gt y R with hyR | hyR
    · rcases le_or_gt y δ with hyδ | hyδ
      · have h1 : (Ioc 0 δ).indicator (fun _ ↦ M₀) y = M₀ :=
          indicator_of_mem (⟨hy, hyδ⟩ : y ∈ Ioc 0 δ) _
        have h2 : 0 ≤ (Ioc 0 R).indicator (fun _ ↦ ε) y := indicator_nonneg (fun _ _ ↦ hε) y
        simpa [b, h1] using (hΔ₁ y ⟨hy, hyδ⟩).trans (le_add_of_nonneg_right h2)
      · have h1 : 0 ≤ (Ioc 0 δ).indicator (fun _ ↦ M₀) y := indicator_nonneg (fun _ _ ↦ hM₀) y
        have h2 : (Ioc 0 R).indicator (fun _ ↦ ε) y = ε :=
          indicator_of_mem (⟨hy, hyR⟩ : y ∈ Ioc 0 R) _
        simpa [b, h2] using (hΔ₂ y hyδ).trans (le_add_of_nonneg_left h1)
    · rw [hΔR y hyR, norm_zero]
      exact add_nonneg (indicator_nonneg (fun _ _ ↦ hM₀) y) (indicator_nonneg (fun _ _ ↦ hε) y)
  calc ‖∫ y in Ioi (0 : ℝ), Δ y‖
      ≤ ∫ y in Ioi (0 : ℝ), b y :=
        norm_integral_le_of_norm_le (hb₁.add hb₂).integrableOn
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hle))
    _ = ∫ y, b y :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
          have hy0 : y ≤ 0 := not_lt.mp hy
          simp [b, indicator_of_notMem (fun h : y ∈ Ioc 0 δ ↦ h.1.not_ge hy0),
            indicator_of_notMem (fun h : y ∈ Ioc 0 R ↦ h.1.not_ge hy0)]
    _ = (∫ y, (Ioc 0 δ).indicator (fun _ ↦ M₀) y) + ∫ y, (Ioc 0 R).indicator (fun _ ↦ ε) y :=
        integral_add hb₁ hb₂
    _ = M₀ * δ + ε * R := by
        simp [integral_indicator_const _ measurableSet_Ioc, Real.volume_real_Ioc_of_le hδ,
          Real.volume_real_Ioc_of_le hR, mul_comm]

/-- A continuous function `ψ` supported in `[-R, R]` and bounded by `M` admits a smooth compactly
supported `φ` with `tsupport φ ⊆ (0, ∞)` vanishing on `(R + 1, ∞)` that is within `2 M + ε` of `ψ`
on `(0, δ]` and within `ε` of `ψ` on `(δ, ∞)`. -/
private lemma exists_contDiff_Ioi_approx {ψ : ℝ → ℂ} (hψ : Continuous ψ)
    {R M δ ε : ℝ} (hsupp : tsupport ψ ⊆ Icc (-R) R) (hM : ∀ y, ‖ψ y‖ ≤ M) (hδ : 0 < δ)
    (hε : 0 < ε) :
    ∃ φ : ℝ → ℂ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioi 0 ∧
      (∀ y, R + 1 < y → φ y = 0) ∧
      (∀ y ∈ Ioc 0 δ, ‖ψ y - φ y‖ ≤ 2 * M + ε) ∧
      (∀ y, δ < y → ‖ψ y - φ y‖ ≤ ε) := by
  set η : ℝ → ℝ := fun y ↦ max 0 (min 1 ((y - δ / 2) / (δ / 2)))
  set g : ℝ → ℂ := fun y ↦ (η y : ℂ) * ψ y
  have hη_cont : Continuous η := by fun_prop
  have hg_cont : Continuous g := by fun_prop
  have hgsupp : tsupport g ⊆ Icc (δ / 2) R := by
    refine closure_minimal (fun y hy ↦ ⟨?_, ?_⟩) isClosed_Icc
    · by_contra hlt
      have hle : (y - δ / 2) / (δ / 2) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      exact hy (by simp [g, η, min_eq_right (hle.trans zero_le_one), max_eq_left hle])
    · exact (hsupp (subset_tsupport ψ (right_ne_zero_of_mul hy))).2
  set r : ℝ := min (δ / 8) (1 / 2)
  have hr : 0 < r := by positivity
  have hcthick : cthickening r (Icc (δ / 2) R) ⊆ Icc (δ / 4) (R + 1) := by
    refine (cthickening_subset_thickening' (δ₂ := min (δ / 4) 1) (by positivity) ?_ _).trans
      fun y hy ↦ ?_
    · exact lt_min ((min_le_left _ _).trans_lt (by linarith))
        ((min_le_right _ _).trans_lt (by norm_num))
    · obtain ⟨z, hz, hdist⟩ := mem_thickening_iff.mp hy
      rw [Real.dist_eq, abs_lt] at hdist
      exact ⟨by linarith [hz.1, min_le_left (δ / 4) 1],
        by linarith [hz.2, min_le_right (δ / 4) 1]⟩
  have hΩ : cthickening r (Icc (δ / 2) R) ⊆ (⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) := by
    rw [Opens.coe_mk]
    exact hcthick.trans fun _ hy ↦ lt_of_lt_of_le (by positivity) hy.1
  obtain ⟨φ, hφsupp, hφdist⟩ := hg_cont.exists_testFunction_dist_le isCompact_Icc hgsupp hr hΩ hε
  have hφpos : tsupport (φ : ℝ → ℂ) ⊆ Ioi 0 := by
    simpa only [Opens.coe_mk] using TestFunctionClass.tsupport_map_subset φ
  refine ⟨φ, TestFunctionClass.map_contDiff φ, TestFunctionClass.map_hasCompactSupport φ,
    hφpos, fun y hy ↦ ?_, fun y _ ↦ ?_, fun y hy ↦ ?_⟩
  · exact image_eq_zero_of_notMem_tsupport fun hmem ↦ (not_le.mpr hy) (hcthick (hφsupp hmem)).2
  · have hη1 : |η y| ≤ 1 := by
      rw [abs_of_nonneg (le_max_left _ _)]
      exact max_le zero_le_one (min_le_left _ _)
    have hg_le : ‖g y‖ ≤ M := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul hη1 (hM y) (norm_nonneg _) zero_le_one).trans (one_mul M).le
    have hfg : ‖g y - φ y‖ ≤ ε := by simpa [dist_eq_norm, norm_sub_rev] using hφdist y
    calc ‖ψ y - φ y‖ = ‖(ψ y - g y) + (g y - φ y)‖ := by ring_nf
      _ ≤ ‖ψ y - g y‖ + ‖g y - φ y‖ := norm_add_le _ _
      _ ≤ (‖ψ y‖ + ‖g y‖) + ε := add_le_add (norm_sub_le _ _) hfg
      _ ≤ 2 * M + ε := by linarith [hM y]
  · have hη_eq : η y = 1 := by
      have hge : 1 ≤ (y - δ / 2) / (δ / 2) := (one_le_div (by positivity)).mpr (by linarith)
      simp [η, min_eq_left hge]
    have hgy : g y = ψ y := by simp [g, hη_eq]
    simpa [dist_eq_norm, norm_sub_rev, hgy] using hφdist y

/-- Combined discrepancy between `ψ` and its smooth cutoff `φ` in both the normalized Dirichlet
sum and the limit integral. -/
private lemma norm_smoothed_sub_approx_le {f : ℕ → ℂ} {A : ℂ} {C R M ε δ x : ℝ}
    (hC : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ‖f n‖ ≤ C * N)
    (hR1 : 1 ≤ R) (hδ : 0 < δ) (hx : 0 < x)
    {ψ φ : ℝ → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ Icc (-R) R) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφpos : tsupport φ ⊆ Ioi 0) (hφR : ∀ y, R + 1 < y → φ y = 0)
    (hφ₁ : ∀ y ∈ Ioc 0 δ, ‖ψ y - φ y‖ ≤ 2 * M + ε) (hφ₂ : ∀ y, δ < y → ‖ψ y - φ y‖ ≤ ε) :
    ‖(∑' n : ℕ, (if n = 0 then 0 else f n) * ψ (n / x)) / x -
        (x : ℂ)⁻¹ * ∑' n : ℕ, f n * φ (n / x)‖ +
      ‖A * (∫ y in Ioi (0 : ℝ), ψ y) - A * (∫ y in Ioi (0 : ℝ), φ y)‖ ≤
      (C + ‖A‖) * ((2 * M + ε) * δ + ε * (R + 1)) := by
  have hMε : 0 ≤ 2 * M + ε := (norm_nonneg _).trans (hφ₁ δ ⟨hδ, le_rfl⟩)
  have hφ0 : φ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ lt_irrefl (0 : ℝ) (hφpos h)
  have hψR : ∀ y, R + 1 < y → ψ y = 0 := fun y hy ↦
    image_eq_zero_of_notMem_tsupport fun hmem ↦ by linarith [(hsupp hmem).2]
  have hsum_diff : (∑' n : ℕ, (if n = 0 then 0 else f n) * ψ (n / x)) / x -
      (x : ℂ)⁻¹ * ∑' n : ℕ, f n * φ (n / x) =
      (∑ n ∈ Finset.Icc 1 ⌊(R + 1) * x⌋₊, f n * (ψ - φ) (n / x)) / x := by
    have hφ_eq : (∑' n : ℕ, f n * φ (n / x)) =
        ∑' n : ℕ, (if n = 0 then 0 else f n) * φ (n / x) :=
      tsum_congr fun n ↦ by
        rcases eq_or_ne n 0 with rfl | hn
        · simp [hφ0]
        · simp [hn]
    rw [hφ_eq, inv_mul_eq_div, tsum_if_ne_zero_mul_eq_sum_Icc f hψR hx,
      tsum_if_ne_zero_mul_eq_sum_Icc f hφR hx, ← sub_div, ← Finset.sum_sub_distrib]
    exact congrArg (· / (x : ℂ)) (Finset.sum_congr rfl fun n _ ↦ by simp [Pi.sub_apply, mul_sub])
  have herr_sum := norm_sum_Icc_mul_div_le (Δ := ψ - φ) (M₀ := 2 * M + ε) (R := R + 1)
    hC hMε hδ.le (by positivity) hx hφ₁ hφ₂
  have herr_int : ‖A * (∫ y in Ioi (0 : ℝ), ψ y) - A * (∫ y in Ioi (0 : ℝ), φ y)‖ ≤
      ‖A‖ * ((2 * M + ε) * δ + ε * (R + 1)) := by
    rw [← mul_sub, ← integral_sub (hψ.integrable_of_hasCompactSupport hψc).integrableOn
      (hφ.continuous.integrable_of_hasCompactSupport hφc).integrableOn, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_setIntegral_Ioi_le (Δ := ψ - φ) (M₀ := 2 * M + ε)
      (R := R + 1) hMε hδ.le (by positivity)
      (fun y hy ↦ by simp [hψR y hy, hφR y hy]) hφ₁ hφ₂) (norm_nonneg _)
  rw [hsum_diff]
  exact (add_le_add herr_sum herr_int).trans_eq (add_mul _ _ _).symm

/-- For any `η > 0`, `(∑_{n ≥ 1} f n ψ (n / x)) / x` is eventually within `η` of `A ∫_{(0, ∞)} ψ`
given explicit Chebyshev, support, and uniform bounds `(C, R, M)`. -/
private lemma eventually_dist_smoothed_lt {f : ℕ → ℂ} {G : ℂ → ℂ} {A : ℂ}
    (hcheby : (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖f n‖) =O[atTop] fun x ↦ x)
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hG' : ∀ s : ℂ, 1 < s.re → G s = LSeries f s - A / (s - 1))
    {C R M η : ℝ} (hC : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ‖f n‖ ≤ C * N)
    (hR1 : 1 ≤ R) (hη : 0 < η)
    {ψ : ℝ → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ Icc (-R) R) (hM : ∀ y, ‖ψ y‖ ≤ M) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀,
      dist ((∑' n : ℕ, (if n = 0 then 0 else f n) * ψ (n / x)) / x)
        (A * ∫ y in Ioi (0 : ℝ), ψ y) < η := by
  have hC0 : 0 ≤ C := by
    simpa using (Finset.sum_nonneg fun n _ ↦ norm_nonneg (f n)).trans (hC 1)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set K : ℝ := C + ‖A‖ + 1
  have hK : 0 < K := by positivity
  set ε : ℝ := min 1 (η / (8 * K * (R + 1)))
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := min_le_left _ _
  set δ : ℝ := min 1 (η / (8 * K * (2 * M + 1)))
  have hδ : 0 < δ := by positivity
  obtain ⟨φ, hφ, hφc, hφpos, hφR, hφ₁, hφ₂⟩ := exists_contDiff_Ioi_approx hψ hsupp hM hδ hε
  obtain ⟨x₀, hx₀⟩ := Metric.tendsto_atTop.mp
    (tendsto_inv_mul_tsum_mul_div_atTop hcheby hG hG' hφ hφc hφpos) (η / 2) (half_pos hη)
  have hsmall₁ : (2 * M + ε) * δ ≤ η / (8 * K) :=
    calc (2 * M + ε) * δ
        ≤ (2 * M + 1) * (η / (8 * K * (2 * M + 1))) :=
          mul_le_mul (by linarith) (min_le_right _ _) hδ.le (by positivity)
      _ = η / (8 * K) := by field_simp
  have hsmall₂ : ε * (R + 1) ≤ η / (8 * K) :=
    calc ε * (R + 1)
        ≤ (η / (8 * K * (R + 1))) * (R + 1) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = η / (8 * K) := by field_simp
  have hsmall : (2 * M + ε) * δ + ε * (R + 1) ≤ η / (4 * K) :=
    calc (2 * M + ε) * δ + ε * (R + 1)
        ≤ η / (8 * K) + η / (8 * K) := add_le_add hsmall₁ hsmall₂
      _ = η / (4 * K) := by field_simp; ring
  have hbudget : (C + ‖A‖) * ((2 * M + ε) * δ + ε * (R + 1)) < η / 2 :=
    calc (C + ‖A‖) * ((2 * M + ε) * δ + ε * (R + 1))
        ≤ (C + ‖A‖) * (η / (4 * K)) := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ < K * (η / (4 * K)) := mul_lt_mul_of_pos_right (by simp [K]) (by positivity)
      _ = η / 4 := by field_simp
      _ < η / 2 := by linarith
  refine ⟨max x₀ 1, fun x hx ↦ ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hx)
  have hmain := hx₀ x ((le_max_left _ _).trans hx)
  have herr := (norm_smoothed_sub_approx_le (A := A) hC hR1 hδ hxpos hψ hψc hsupp
    hφ hφc hφpos hφR hφ₁ hφ₂).trans_lt hbudget
  rw [← dist_eq_norm, ← dist_eq_norm] at herr
  exact (dist_triangle4_right _ _ ((x : ℂ)⁻¹ * ∑' n : ℕ, f n * φ (n / x))
    (A * ∫ y in Ioi (0 : ℝ), φ y)).trans_lt ((add_lt_add herr hmain).trans_eq (add_halves η))

/-- **Smoothed Wiener--Ikehara theorem for complex coefficients.** Under the Chebyshev bound
`∑_{1 ≤ n ≤ x} ‖f n‖ = O(x)` and continuous boundary data `G s = LSeries f s - A / (s - 1)` on
`Re s ≥ 1`, for every continuous compactly supported `ψ : ℝ → ℂ`,
`(∑_{n ≥ 1} f n ψ (n / x)) / x → A ∫_{(0, ∞)} ψ` as `x → ∞`. No sign of `f` and no separate
summability hypothesis is assumed, and `ψ 0` need not vanish. -/
theorem wienerIkehara_smoothed {f : ℕ → ℂ} {G : ℂ → ℂ} {A : ℂ}
    (hcheby : (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖f n‖) =O[atTop] (fun x : ℝ ↦ x))
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hG' : ∀ s : ℂ, 1 < s.re → G s = LSeries f s - A / (s - 1))
    {ψ : ℝ → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Tendsto (fun x : ℝ ↦ (∑' n : ℕ, (if n = 0 then 0 else f n) * ψ (n / x)) / x)
      atTop (𝓝 (A * ∫ y in Ioi (0 : ℝ), ψ y)) := by
  obtain ⟨C, hC⟩ := exists_sum_Icc_le_mul_of_isBigO hcheby
  obtain ⟨R₀, hR₀⟩ := hψc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  set R : ℝ := max R₀ 1
  have hsupp : tsupport ψ ⊆ Icc (-R) R := fun y hy ↦ by
    have hy' := hR₀ hy
    rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hy'
    exact ⟨by linarith [hy'.1, le_max_left R₀ 1], by linarith [hy'.2, le_max_left R₀ 1]⟩
  obtain ⟨M, hM⟩ := hψc.exists_bound_of_continuous hψ
  exact Metric.tendsto_atTop.mpr fun η hη ↦
    eventually_dist_smoothed_lt hcheby hG hG' hC (le_max_right _ _) hη hψ hψc hsupp hM

end Smoothed

/-! ### Interval and sharp-cutoff forms under a majorant -/

section Interval

/-- For complex coefficients `u : ℕ → ℂ` with nonnegative real parts on `n ≠ 0` and continuous
boundary data `U s = LSeries u s - C / (s - 1)` on `Re s ≥ 1`,
`x⁻¹ * ∑_{1 ≤ n ≤ x} (u n).re → C.re` as `x → ∞`. -/
private lemma tendsto_inv_mul_sum_Icc_re_of_nonneg {u : ℕ → ℂ} {U : ℂ → ℂ} {C : ℂ}
    (hu0 : ∀ n ≠ 0, 0 ≤ (u n).re)
    (husum : ∀ s : ℂ, 1 < s.re → LSeriesSummable u s)
    (hU : ContinuousOn U {s : ℂ | 1 ≤ s.re})
    (hU' : ∀ s : ℂ, 1 < s.re → U s = LSeries u s - C / (s - 1)) :
    Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (u n).re) atTop (𝓝 C.re) := by
  let a : ℕ → ℝ := fun n ↦ if n = 0 then 0 else (u n).re
  let F : ℂ → ℂ := fun s ↦ (2 : ℂ)⁻¹ * (LSeries u s + star (LSeries u (star s)))
  let G : ℂ → ℂ := fun s ↦ (2 : ℂ)⁻¹ * (U s + star (U (star s)))
  have ha : 0 ≤ a := fun n ↦ by
    dsimp only [a]
    split_ifs with hn
    · exact le_rfl
    · exact hu0 n hn
  have hF (s : ℂ) (hs : 1 < s.re) : LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s) := by
    have h1 : LSeriesHasSum u s (LSeries u s) := (husum s hs).LSeriesHasSum
    have h2 : LSeriesHasSum (star u) s (star (LSeries u (star s))) := by
      have hstar := (LSeriesHasSum_star_iff u (star s) (LSeries u (star s))).mpr
        (husum (star s) (by simpa using hs)).LSeriesHasSum
      simpa [Complex.star_def] using hstar
    refine (LSeriesHasSum_congr s (F s) fun {n} hn ↦ ?_).mpr ((h1.add h2).smul (2 : ℂ)⁻¹)
    simp only [a, hn, ↓reduceIte, Pi.smul_apply, Pi.add_apply, Pi.star_apply, smul_eq_mul]
    exact Complex.ext (by simp; ring) (by simp)
  have hG : ContinuousOn G {s : ℂ | 1 ≤ s.re} :=
    continuousOn_const.mul (hU.add (continuous_star.comp_continuousOn
      (hU.comp continuous_star.continuousOn fun s hs ↦ by simpa using hs)))
  have hGF (s : ℂ) (hs : 1 < s.re) : G s = F s - (C.re : ℂ) / (s - 1) := by
    have hUs := hU' s hs
    have hUstar := congrArg star (hU' (star s) (by simpa using hs))
    simp only [star_sub, star_div₀, star_star, star_one] at hUstar
    have hCre : (C.re : ℂ) = (2 : ℂ)⁻¹ * (C + star C) :=
      Complex.ext (by simp; ring) (by simp)
    dsimp only [G, F]
    rw [hUs, hUstar, hCre]
    ring
  refine (wienerIkehara ha hF hG hGF).congr fun x ↦ congrArg (x⁻¹ * ·)
    (Finset.sum_congr rfl fun n hn ↦ ?_)
  simp [a, Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1]

/-- If `(∑_{1 ≤ n ≤ x} f n) / x → A` as `x → ∞`, then
`(S_f (b * x) - S_f (a * x)) / x → A * (b - a)` for all `0 ≤ a ≤ b`. -/
private lemma tendsto_summatory_sub_div_of_tendsto_sum_Icc_div {f : ℕ → ℂ} {A : ℂ} {a b : ℝ}
    (h : Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n) / x) atTop (𝓝 A))
    (ha : 0 ≤ a) (hab : a ≤ b) :
    Tendsto (fun x : ℝ ↦
      (TauCeti.summatory (fun n : ℕ ↦ n) (fun n ↦ if n = 0 then 0 else f n) (b * x) -
        TauCeti.summatory (fun n : ℕ ↦ n) (fun n ↦ if n = 0 then 0 else f n) (a * x)) / x)
      atTop (𝓝 (A * ((b - a : ℝ) : ℂ))) := by
  have hscale {c : ℝ} (hc : 0 ≤ c) :
      Tendsto (fun x : ℝ ↦
        TauCeti.summatory (fun n : ℕ ↦ n) (fun n ↦ if n = 0 then 0 else f n) (c * x) / x)
        atTop (𝓝 (A * (c : ℂ))) := by
    have hsum {y : ℝ} :
        TauCeti.summatory (fun n : ℕ ↦ n) (fun n ↦ if n = 0 then 0 else f n) y =
          ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, f n := by
      rw [TauCeti.summatory_id_eq_sum_Icc (by simp)]
      exact Finset.sum_congr rfl fun n hn ↦ by
        simp [Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1]
    rcases eq_or_lt_of_le hc with rfl | hcpos
    · simp [hsum]
    · have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
      refine ((h.comp (tendsto_id.const_mul_atTop hcpos)).mul_const (c : ℂ)).congr fun x ↦ ?_
      dsimp only [Function.comp_def, id_eq]
      rw [hsum, Complex.ofReal_mul, mul_comm (c : ℂ) (x : ℂ), div_mul_eq_mul_div,
        mul_div_mul_right _ _ hc0]
  have hsub : A * ((b - a : ℝ) : ℂ) = A * (b : ℂ) - A * (a : ℂ) := by push_cast; ring
  rw [hsub]
  exact ((hscale (ha.trans hab)).sub (hscale ha)).congr fun x ↦ (sub_div _ _ _).symm

/-- **Sharp-cutoff Wiener--Ikehara theorem for complex coefficients under a majorant.** Let
`‖f n‖ ≤ g n` for all `n ≠ 0` and a majorant `g : ℕ → ℝ` whose Dirichlet series is summable on
`Re s > 1` and has continuous boundary data `H s = LSeries g s - B / (s - 1)` on `Re s ≥ 1`, and
let `f` have continuous boundary data `G s = LSeries f s - A / (s - 1)` on `Re s ≥ 1`. Then
`(∑_{1 ≤ n ≤ x} f n) / x → A` as `x → ∞`. -/
theorem wienerIkehara_of_norm_le {f : ℕ → ℂ} {g : ℕ → ℝ} {G H : ℂ → ℂ} {A B : ℂ}
    (hfg : ∀ n ≠ 0, ‖f n‖ ≤ g n)
    (hgsum : ∀ σ : ℝ, 1 < σ → LSeriesSummable (fun n ↦ (g n : ℂ)) σ)
    (hH : ContinuousOn H {s : ℂ | 1 ≤ s.re})
    (hH' : ∀ s : ℂ, 1 < s.re → H s = LSeries (fun n ↦ (g n : ℂ)) s - B / (s - 1))
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hG' : ∀ s : ℂ, 1 < s.re → G s = LSeries f s - A / (s - 1)) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n) / x) atTop (𝓝 A) := by
  let gC : ℕ → ℂ := fun n ↦ (g n : ℂ)
  have hgsum' (s : ℂ) (hs : 1 < s.re) : LSeriesSummable gC s :=
    (hgsum s.re hs).of_re_le_re (by simp)
  have hfsum (s : ℂ) (hs : 1 < s.re) : LSeriesSummable f s := by
    refine .of_norm <| (hgsum' s hs).norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · exact _root_.LSeries.norm_term_le s
        ((hfg n hn).trans_eq (Complex.norm_of_nonneg ((norm_nonneg _).trans (hfg n hn))).symm)
  have h₁ := tendsto_inv_mul_sum_Icc_re_of_nonneg (u := gC)
    (fun n hn ↦ by simpa [gC] using (norm_nonneg (f n)).trans (hfg n hn)) hgsum' hH hH'
  have h₂ := tendsto_inv_mul_sum_Icc_re_of_nonneg (u := gC + f) (U := H + G) (C := B + A)
    (fun n hn ↦ by
      simp only [gC, Pi.add_apply, add_re, ofReal_re]
      linarith [(abs_le.mp ((Complex.abs_re_le_norm (f n)).trans (hfg n hn))).1])
    (fun s hs ↦ (hgsum' s hs).add (hfsum s hs)) (hH.add hG)
    (fun s hs ↦ by
      simp only [Pi.add_apply, hH' s hs, hG' s hs, LSeries_add (hgsum' s hs) (hfsum s hs), add_div]
      ring)
  have h₃ := tendsto_inv_mul_sum_Icc_re_of_nonneg (u := gC + (-I) • f) (U := H + (-I) • G)
    (C := B + (-I) * A)
    (fun n hn ↦ by
      have hf_im := (abs_le.mp ((Complex.abs_im_le_norm (f n)).trans (hfg n hn))).1
      have hre_eq : ((gC + (-I) • f) n).re = g n + (f n).im := by simp [gC]
      linarith)
    (fun s hs ↦ (hgsum' s hs).add ((hfsum s hs).smul (-I)))
    (hH.add (continuousOn_const.mul hG))
    (fun s hs ↦ by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hH' s hs, hG' s hs,
        LSeries_add (hgsum' s hs) ((hfsum s hs).smul (-I)), LSeries_smul, add_div, mul_div_assoc]
      ring)
  have hre : Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (f n).re) atTop (𝓝 A.re) := by
    have hsub := h₂.sub h₁
    simp only [add_re, add_sub_cancel_left] at hsub
    refine hsub.congr fun x ↦ ?_
    simp [gC, Finset.sum_add_distrib, mul_add]
  have him : Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (f n).im) atTop (𝓝 A.im) := by
    have hsub := h₃.sub h₁
    have hCre : (B + -I * A).re - B.re = A.im := by simp
    rw [hCre] at hsub
    refine hsub.congr fun x ↦ ?_
    simp [gC, Finset.sum_add_distrib, mul_add]
  have hcomb := ((continuous_ofReal.tendsto A.re).comp hre).add
    (((continuous_ofReal.tendsto A.im).comp him).mul_const I)
  rw [Complex.re_add_im] at hcomb
  refine hcomb.congr fun x ↦ ?_
  dsimp only [Function.comp_def]
  push_cast
  rw [mul_assoc, Finset.sum_mul, ← mul_add, ← Finset.sum_add_distrib, div_eq_inv_mul]
  exact congrArg ((x : ℂ)⁻¹ * ·) (Finset.sum_congr rfl fun n _ ↦ Complex.re_add_im (f n))

/-- **Interval form of Wiener--Ikehara for complex coefficients.** Let `‖f n‖ ≤ g n` for all
`n ≠ 0` and a majorant `g : ℕ → ℝ` whose Dirichlet series is summable on `Re s > 1` and has
continuous boundary data `H s = LSeries g s - B / (s - 1)` on `Re s ≥ 1`, and let `f` have
continuous boundary data `G s = LSeries f s - A / (s - 1)` on `Re s ≥ 1`. Then for all
`0 ≤ a ≤ b`, `(S_f (b x) - S_f (a x)) / x → A (b - a)` as `x → ∞`. -/
theorem wienerIkehara_interval {f : ℕ → ℂ} {g : ℕ → ℝ} {G H : ℂ → ℂ} {A B : ℂ} {a b : ℝ}
    (hfg : ∀ n ≠ 0, ‖f n‖ ≤ g n)
    (hgsum : ∀ σ : ℝ, 1 < σ → LSeriesSummable (fun n ↦ (g n : ℂ)) σ)
    (hH : ContinuousOn H {s : ℂ | 1 ≤ s.re})
    (hH' : ∀ s : ℂ, 1 < s.re → H s = LSeries (fun n ↦ (g n : ℂ)) s - B / (s - 1))
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hG' : ∀ s : ℂ, 1 < s.re → G s = LSeries f s - A / (s - 1))
    (ha : 0 ≤ a) (hab : a ≤ b) :
    Tendsto (fun x : ℝ ↦
      (TauCeti.summatory (fun n : ℕ ↦ n) (fun n ↦ if n = 0 then 0 else f n) (b * x) -
        TauCeti.summatory (fun n : ℕ ↦ n) (fun n ↦ if n = 0 then 0 else f n) (a * x)) / x)
      atTop (𝓝 (A * ((b - a : ℝ) : ℂ))) :=
  tendsto_summatory_sub_div_of_tendsto_sum_Icc_div
    (wienerIkehara_of_norm_le hfg hgsum hH hH' hG hG') ha hab

/-- **Sharp-cutoff Wiener--Ikehara theorem for bounded complex coefficients.** If `‖f n‖ ≤ M` for
all `n ≠ 0` and `G s = LSeries f s - A / (s - 1)` is continuous on `Re s ≥ 1`, then
`(∑_{1 ≤ n ≤ x} f n) / x → A` as `x → ∞`. -/
theorem wienerIkehara_of_norm_le_const {f : ℕ → ℂ} {G : ℂ → ℂ} {A : ℂ} {M : ℝ}
    (hM : ∀ n ≠ 0, ‖f n‖ ≤ M)
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hG' : ∀ s : ℂ, 1 < s.re → G s = LSeries f s - A / (s - 1)) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n) / x) atTop (𝓝 A) := by
  have hcast : (fun _ : ℕ ↦ (M : ℂ)) = (M : ℂ) • (1 : ℕ → ℂ) := by ext; simp
  refine wienerIkehara_of_norm_le (g := fun _ ↦ M) (H := fun s ↦ (M : ℂ) * riemannZeta₀ s)
    (B := (M : ℂ)) hM
    (fun σ hσ ↦ hcast ▸ (LSeriesSummable_one_iff.mpr (by simpa using hσ)).smul (M : ℂ))
    (differentiable_riemannZeta₀.const_mul (M : ℂ)).continuous.continuousOn
    (fun s hs ↦ ?_) hG hG'
  have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs
  rw [hcast, LSeries_smul, LSeries_one_eq_riemannZeta hs, riemannZeta_eq_inv_sub_add hs1]
  ring

/-- **Interval Wiener--Ikehara theorem for bounded complex coefficients.** If `‖f n‖ ≤ M` for all
`n ≠ 0` and `G` is continuous on `Re s ≥ 1` with `G s = LSeries f s - A / (s - 1)` on `Re s > 1`,
then for all `0 ≤ a ≤ b`, `(S_f (b x) - S_f (a x)) / x → A (b - a)` as `x → ∞`. -/
theorem wienerIkehara_interval_of_norm_le_const {f : ℕ → ℂ} {G : ℂ → ℂ} {A : ℂ} {M a b : ℝ}
    (hM : ∀ n ≠ 0, ‖f n‖ ≤ M)
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hG' : ∀ s : ℂ, 1 < s.re → G s = LSeries f s - A / (s - 1))
    (ha : 0 ≤ a) (hab : a ≤ b) :
    Tendsto (fun x : ℝ ↦
      (TauCeti.summatory (fun n : ℕ ↦ n) (fun n ↦ if n = 0 then 0 else f n) (b * x) -
        TauCeti.summatory (fun n : ℕ ↦ n) (fun n ↦ if n = 0 then 0 else f n) (a * x)) / x)
      atTop (𝓝 (A * ((b - a : ℝ) : ℂ))) :=
  tendsto_summatory_sub_div_of_tendsto_sum_Icc_div
    (wienerIkehara_of_norm_le_const hM hG hG') ha hab

end Interval

/-! ### Necessity of the majorant hypothesis -/

section Counterexample

/-- The `j`-th cancelling dyadic dipole, equal to `2 ^ j` at `2 ^ j` and `-2 ^ j` at `2 ^ j + 1`. -/
private def dyadicPair (j n : ℕ) : ℂ :=
  (if n = 2 ^ j then (2 ^ j : ℂ) else 0) + (if n = 2 ^ j + 1 then -(2 ^ j : ℂ) else 0)

/-- The dyadic cancelling sequence `f(2 ^ j) = 2 ^ j`, `f(2 ^ j + 1) = -2 ^ j` for `j ≥ 1`. -/
private def dyadicCancel (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 n, dyadicPair j n

private lemma dyadicPair_eq_zero_of_gt {j n : ℕ} (h : n < j) : dyadicPair j n = 0 := by
  have hpow : n < 2 ^ j := h.trans Nat.lt_two_pow_self
  simp [dyadicPair, hpow.ne, (hpow.trans (Nat.lt_succ_self _)).ne]

private lemma dyadicCancel_eq_sum_Icc {n N : ℕ} (hn : n ≤ N) :
    dyadicCancel n = ∑ j ∈ Finset.Icc 1 N, dyadicPair j n :=
  Finset.sum_subset (Finset.Icc_subset_Icc_right hn) fun _ hj hnot ↦
    dyadicPair_eq_zero_of_gt (lt_of_not_ge fun hle ↦
      hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1, hle⟩))

/-- Exact evaluation of the partial sums of `dyadicCancel`: `2 ^ k` at `N = 2 ^ k` (`k ≥ 1`) and
`0` at `N = 2 ^ k + 1`. -/
private lemma sum_Icc_dyadicCancel (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, dyadicCancel n =
      ∑ j ∈ Finset.Icc 1 N, if N = 2 ^ j then (2 ^ j : ℂ) else 0 := by
  have hexpand : ∑ n ∈ Finset.Icc 1 N, dyadicCancel n =
      ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, dyadicPair j n :=
    Finset.sum_congr rfl fun n hn ↦ dyadicCancel_eq_sum_Icc (Finset.mem_Icc.mp hn).2
  rw [hexpand, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hpow1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  simp only [dyadicPair, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_Icc, hpow1,
    Nat.le_add_left 1 (2 ^ j), true_and]
  by_cases h1 : 2 ^ j ≤ N
  · by_cases h2 : 2 ^ j + 1 ≤ N
    · have hne : N ≠ 2 ^ j := by omega
      simp [h1, h2, hne]
    · have heq : N = 2 ^ j := by omega
      simp [heq]
  · have h2 : ¬ 2 ^ j + 1 ≤ N := by omega
    have hne : N ≠ 2 ^ j := by omega
    simp [h1, h2, hne]

/-- Chebyshev bound `∑_{1 ≤ n ≤ N} ‖dyadicCancel n‖ ≤ 4 N`. -/
private lemma sum_Icc_norm_dyadicCancel_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖dyadicCancel n‖ ≤ 4 * (N : ℝ) := by
  rcases eq_or_ne N 0 with rfl | hN0
  · simp
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      ‖dyadicCancel n‖ ≤ ∑ j ∈ Finset.Icc 1 N,
        ((if n = 2 ^ j then (2 : ℝ) ^ j else 0) + (if n = 2 ^ j + 1 then (2 : ℝ) ^ j else 0)) := by
    rw [dyadicCancel_eq_sum_Icc (Finset.mem_Icc.mp hn).2]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · split_ifs <;> simp
    · split_ifs <;> simp
  refine ((Finset.sum_le_sum hpoint).trans ?_)
  rw [Finset.sum_comm]
  have hinner (j : ℕ) :
      ∑ n ∈ Finset.Icc 1 N,
          ((if n = 2 ^ j then (2 : ℝ) ^ j else 0) + (if n = 2 ^ j + 1 then (2 : ℝ) ^ j else 0)) ≤
        if j ≤ Nat.log 2 N then 2 * (2 : ℝ) ^ j else 0 := by
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_Icc, Nat.one_le_two_pow,
      Nat.le_add_left 1 (2 ^ j), true_and]
    by_cases h1 : 2 ^ j ≤ N
    · have hjlog : j ≤ Nat.log 2 N := Nat.le_log_of_pow_le Nat.one_lt_two h1
      simp only [h1, hjlog, ↓reduceIte]
      split_ifs <;> linarith [pow_nonneg (zero_le_two : (0 : ℝ) ≤ 2) j]
    · have h2 : ¬ 2 ^ j + 1 ≤ N := by omega
      simp only [h1, h2, ↓reduceIte, add_zero]
      split_ifs <;> positivity
  refine (Finset.sum_le_sum fun j _ ↦ hinner j).trans ?_
  have hsub : ∑ j ∈ Finset.Icc 1 N, (if j ≤ Nat.log 2 N then 2 * (2 : ℝ) ^ j else 0) ≤
      ∑ j ∈ Finset.range (Nat.log 2 N + 1), 2 * (2 : ℝ) ^ j := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj ↦ ?_)
      fun j _ _ ↦ mul_nonneg zero_le_two (pow_nonneg zero_le_two j)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hj).2)
  have hgeom : ∑ j ∈ Finset.range (Nat.log 2 N + 1), (2 : ℝ) ^ j ≤
      2 * (2 : ℝ) ^ Nat.log 2 N := by
    have h := geom_sum_mul (2 : ℝ) (Nat.log 2 N + 1)
    rw [pow_succ] at h
    linarith [h]
  have hpowN : (2 : ℝ) ^ Nat.log 2 N ≤ N := by
    exact_mod_cast Nat.pow_log_le_self 2 hN0
  rw [← Finset.mul_sum] at hsub
  linarith

private lemma isBigO_sum_Icc_norm_dyadicCancel :
    (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖dyadicCancel n‖) =O[atTop] fun x ↦ x := by
  refine IsBigO.of_bound 4 ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _), Real.norm_of_nonneg hx]
  exact (sum_Icc_norm_dyadicCancel_le ⌊x⌋₊).trans
    (mul_le_mul_of_nonneg_left (Nat.floor_le hx) (by positivity))

/-- Paired Dirichlet term `2 ^ (j + 1) * ((2 ^ (j + 1)) ^ (-s) - (2 ^ (j + 1) + 1) ^ (-s))`. -/
private noncomputable def dyadicDirichletTerm (j : ℕ) (s : ℂ) : ℂ :=
  (2 ^ (j + 1) : ℂ) * (((2 ^ (j + 1) : ℕ) : ℂ) ^ (-s) - ((2 ^ (j + 1) + 1 : ℕ) : ℂ) ^ (-s))

/-- Mean-value bound on `dyadicDirichletTerm j s` on `{s | 1 ≤ s.re}`:
`‖dyadicDirichletTerm j s‖ ≤ ‖s‖ * (1 / 2) ^ (j + 1)`. -/
private lemma norm_dyadicDirichletTerm_le (j : ℕ) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖dyadicDirichletTerm j s‖ ≤ ‖s‖ * (1 / 2 : ℝ) ^ (j + 1) := by
  set m : ℕ := 2 ^ (j + 1)
  have hm_pos : (0 : ℝ) < m := by positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_two_pow
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr fun h ↦ by
    rw [h, zero_re] at hs
    norm_num at hs
  have hderiv : ∀ t ∈ Icc (m : ℝ) (m + 1),
      HasDerivWithinAt (fun t : ℝ ↦ (t : ℂ) ^ (-s)) (-s * (t : ℂ) ^ (-s - 1))
        (Icc (m : ℝ) (m + 1)) t := fun t ht ↦
    (hasDerivAt_ofReal_cpow_const (lt_of_lt_of_le hm_pos ht.1).ne' hs0).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico (m : ℝ) (m + 1),
      ‖-s * (t : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * ((m : ℝ) ^ 2)⁻¹ := fun t ht ↦ by
    have ht0 : 0 < t := lt_of_lt_of_le hm_pos ht.1
    have ht1 : 1 ≤ t := hm1.trans ht.1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hexp : (-s - 1).re ≤ -2 := by simp only [sub_re, neg_re, one_re]; linarith
    calc t ^ (-s - 1).re
        ≤ t ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 hexp
      _ ≤ (m : ℝ) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_nonpos hm_pos ht.1 (by norm_num)
      _ = ((m : ℝ) ^ 2)⁻¹ := by rw [Real.rpow_neg hm_pos.le, Real.rpow_two]
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound (m + 1)
    ⟨by linarith, le_rfl⟩
  rw [add_sub_cancel_left, mul_one, norm_sub_rev] at hmvt
  have hcast : ((m + 1 : ℝ) : ℂ) = ((m + 1 : ℕ) : ℂ) := by push_cast; rfl
  rw [hcast] at hmvt
  calc ‖dyadicDirichletTerm j s‖
      = (m : ℝ) * ‖((m : ℕ) : ℂ) ^ (-s) - ((m + 1 : ℕ) : ℂ) ^ (-s)‖ := by
        simp [dyadicDirichletTerm, m]
    _ ≤ (m : ℝ) * (‖s‖ * ((m : ℝ) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hmvt hm_pos.le
    _ = ‖s‖ * (m : ℝ)⁻¹ := by field_simp [hm_pos.ne']
    _ = ‖s‖ * (1 / 2 : ℝ) ^ (j + 1) := by simp [m, one_div, inv_pow]

/-- The paired series `∑' j, dyadicDirichletTerm j s` is continuous on `{s | 1 ≤ s.re}`. -/
private lemma continuousOn_tsum_dyadicDirichletTerm :
    ContinuousOn (fun s : ℂ ↦ ∑' j : ℕ, dyadicDirichletTerm j s) {s : ℂ | 1 ≤ s.re} := by
  refine continuousOn_of_locally_continuousOn fun s₀ _ ↦
    ⟨Metric.ball s₀ 1, Metric.isOpen_ball, Metric.mem_ball_self one_pos, ?_⟩
  refine continuousOn_tsum (fun j ↦ ?_)
    ((summable_geometric_two.mul_right (1 / 2 : ℝ)).mul_left (‖s₀‖ + 1)) fun j s hs ↦ ?_
  · refine continuousOn_const.mul (ContinuousOn.sub ?_ ?_)
    · exact (continuous_neg.const_cpow (Or.inl (by positivity))).continuousOn
    · exact (continuous_neg.const_cpow (Or.inl (by positivity))).continuousOn
  · have hs_ball : ‖s‖ ≤ ‖s₀‖ + 1 := by
      have hd : dist s s₀ < 1 := Metric.mem_ball.mp hs.2
      linarith [norm_sub_norm_le s s₀, dist_eq_norm s s₀]
    calc ‖dyadicDirichletTerm j s‖
        ≤ ‖s‖ * (1 / 2 : ℝ) ^ (j + 1) := norm_dyadicDirichletTerm_le j hs.1
      _ ≤ (‖s₀‖ + 1) * ((1 / 2 : ℝ) ^ j * (1 / 2 : ℝ)) := by
          rw [pow_succ]
          exact mul_le_mul_of_nonneg_right hs_ball (by positivity)

/-- On the dyadic block `[2 ^ (J + 1), 2 ^ (J + 2))`, only the `(J + 1)`-st dipole contributes to
`dyadicCancel`. -/
private lemma dyadicCancel_eq_dyadicPair_of_mem_Ico {J n : ℕ}
    (hn : n ∈ Finset.Ico (2 ^ (J + 1)) (2 ^ (J + 2))) :
    dyadicCancel n = dyadicPair (J + 1) n := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hn
  rw [dyadicCancel]
  have hmem : J + 1 ∈ Finset.Icc 1 n :=
    Finset.mem_Icc.mpr ⟨by omega, (Nat.lt_two_pow_self (n := J + 1)).le.trans hlo⟩
  rw [← Finset.add_sum_erase _ _ hmem]
  have hrest : ∑ j ∈ (Finset.Icc 1 n).erase (J + 1), dyadicPair j n = 0 := by
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hj_ne : j ≠ J + 1 := (Finset.mem_erase.mp hj).1
    rcases lt_trichotomy j (J + 1) with hlt | rfl | hgt
    · have hp : 2 * 2 ^ j ≤ 2 ^ (J + 1) := by
        simpa [pow_succ'] using Nat.pow_le_pow_right Nat.zero_lt_two (Nat.succ_le_of_lt hlt)
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp (Finset.mem_erase.mp hj).2).1
      have h2j : 2 ≤ 2 ^ j := by simpa using Nat.pow_le_pow_right Nat.zero_lt_two hj1
      have hne1 : n ≠ 2 ^ j := by omega
      have hne2 : n ≠ 2 ^ j + 1 := by omega
      simp [dyadicPair, hne1, hne2]
    · exact absurd rfl hj_ne
    · have hge : 2 ^ (J + 2) ≤ 2 ^ j :=
        Nat.pow_le_pow_right Nat.zero_lt_two (Nat.succ_le_of_lt hgt)
      have hne1 : n ≠ 2 ^ j := by omega
      have hne2 : n ≠ 2 ^ j + 1 := by omega
      simp [dyadicPair, hne1, hne2]
  rw [hrest, add_zero]

/-- Partial sums of `LSeries.term dyadicCancel s` up to `2 ^ (J + 1) - 1` match the first `J`
paired terms. -/
private lemma sum_range_term_dyadicCancel (s : ℂ) (J : ℕ) :
    ∑ n ∈ Finset.range (2 ^ (J + 1)), _root_.LSeries.term dyadicCancel s n =
      ∑ j ∈ Finset.range J, dyadicDirichletTerm j s := by
  induction J with
  | zero => simp [Finset.sum_range_succ, dyadicCancel, dyadicPair]
  | succ J ih =>
    have h2pos : 2 ≤ 2 ^ (J + 1) := by
      simpa using Nat.pow_le_pow_right Nat.zero_lt_two (Nat.succ_le_succ (Nat.zero_le J))
    have hpow_succ : 2 ^ (J + 2) = 2 ^ (J + 1) + 2 ^ (J + 1) := by ring
    have hle : 2 ^ (J + 1) ≤ 2 ^ (J + 2) := by omega
    rw [← Finset.sum_range_add_sum_Ico _ hle, ih, Finset.sum_range_succ]
    congr 1
    have hm1 : 2 ^ (J + 1) ∈ Finset.Ico (2 ^ (J + 1)) (2 ^ (J + 2)) :=
      Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
    have hm2 : 2 ^ (J + 1) + 1 ∈ (Finset.Ico (2 ^ (J + 1)) (2 ^ (J + 2))).erase (2 ^ (J + 1)) :=
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩
    rw [← Finset.add_sum_erase _ _ hm1, ← Finset.add_sum_erase _ _ hm2]
    have hzero : ∑ n ∈ ((Finset.Ico (2 ^ (J + 1)) (2 ^ (J + 2))).erase
        (2 ^ (J + 1))).erase (2 ^ (J + 1) + 1), _root_.LSeries.term dyadicCancel s n = 0 := by
      refine Finset.sum_eq_zero fun n hn ↦ ?_
      have hn2 : n ≠ 2 ^ (J + 1) + 1 := (Finset.mem_erase.mp hn).1
      have hn1 : n ≠ 2 ^ (J + 1) := (Finset.mem_erase.mp (Finset.mem_erase.mp hn).2).1
      have hnIco := (Finset.mem_erase.mp (Finset.mem_erase.mp hn).2).2
      have hdc : dyadicCancel n = 0 := by
        simp [dyadicCancel_eq_dyadicPair_of_mem_Ico hnIco, dyadicPair, hn1, hn2]
      simp [_root_.LSeries.term_def, hdc]
    have hv1 : dyadicCancel (2 ^ (J + 1)) = (2 ^ (J + 1) : ℂ) := by
      rw [dyadicCancel_eq_dyadicPair_of_mem_Ico hm1]
      simp [dyadicPair]
    have hv2 : dyadicCancel (2 ^ (J + 1) + 1) = -(2 ^ (J + 1) : ℂ) := by
      rw [dyadicCancel_eq_dyadicPair_of_mem_Ico (Finset.mem_erase.mp hm2).2]
      simp [dyadicPair]
    rw [_root_.LSeries.term_of_ne_zero (by positivity),
      _root_.LSeries.term_of_ne_zero (by positivity)]
    simp only [hzero, add_zero, hv1, hv2, dyadicDirichletTerm, cpow_neg, div_eq_mul_inv, neg_mul]
    ring

/-- On `Re s > 1`, the paired series agrees with `LSeries dyadicCancel s`. -/
private lemma tsum_dyadicDirichletTerm_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    (∑' j : ℕ, dyadicDirichletTerm j s) = LSeries dyadicCancel s := by
  have hLsum : LSeriesSummable dyadicCancel s :=
    LSeriesSummable_of_isBigO_sum_Icc_norm_id isBigO_sum_Icc_norm_dyadicCancel hs
  have hgsum : Summable fun j : ℕ ↦ dyadicDirichletTerm j s :=
    Summable.of_norm_bounded ((summable_geometric_two.mul_right (1 / 2 : ℝ)).mul_left ‖s‖)
      fun j ↦ by simpa only [pow_succ, mul_assoc] using norm_dyadicDirichletTerm_le j hs.le
  have hsubseq : StrictMono fun J : ℕ ↦ 2 ^ (J + 1) := fun i j hij ↦
    Nat.pow_lt_pow_right Nat.one_lt_two (Nat.add_lt_add_right hij 1)
  have hLlim : Tendsto (fun J : ℕ ↦ ∑ n ∈ Finset.range (2 ^ (J + 1)),
      _root_.LSeries.term dyadicCancel s n) atTop (𝓝 (LSeries dyadicCancel s)) :=
    hLsum.hasSum.tendsto_sum_nat.comp hsubseq.tendsto_atTop
  have hGlim : Tendsto (fun J : ℕ ↦ ∑ j ∈ Finset.range J, dyadicDirichletTerm j s)
      atTop (𝓝 (∑' j : ℕ, dyadicDirichletTerm j s)) :=
    hgsum.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique (hGlim.congr fun J ↦ (sum_range_term_dyadicCancel s J).symm) hLlim

private lemma not_tendsto_summatory_dyadicCancel_div :
    ¬ ∃ L : ℂ, Tendsto (fun x : ℝ ↦
      TauCeti.summatory (fun n : ℕ ↦ n) (fun n ↦ if n = 0 then 0 else dyadicCancel n) x / x)
      atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hsum_eq (N : ℕ) :
      TauCeti.summatory (fun n : ℕ ↦ n) (fun n ↦ if n = 0 then 0 else dyadicCancel n) N =
        ∑ n ∈ Finset.Icc 1 N, dyadicCancel n := by
    rw [TauCeti.summatory_id_eq_sum_Icc (by simp), Nat.floor_natCast]
    exact Finset.sum_congr rfl fun n hn ↦ by
      simp [Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1]
  have hseq1 : Tendsto (fun k : ℕ ↦ ((2 ^ (k + 1) : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (StrictMono.tendsto_atTop fun i j hij ↦
      Nat.pow_lt_pow_right Nat.one_lt_two (Nat.add_lt_add_right hij 1))
  have hseq0 : Tendsto (fun k : ℕ ↦ ((2 ^ (k + 1) + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (StrictMono.tendsto_atTop fun i j hij ↦
      Nat.add_lt_add_right (Nat.pow_lt_pow_right Nat.one_lt_two (Nat.add_lt_add_right hij 1)) 1)
  have hlim1 : Tendsto (fun k : ℕ ↦
      TauCeti.summatory (fun n : ℕ ↦ n) (fun n ↦ if n = 0 then 0 else dyadicCancel n)
        ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ)) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr fun k ↦ ?_
    rw [hsum_eq, sum_Icc_dyadicCancel]
    have hmem : k + 1 ∈ Finset.Icc 1 (2 ^ (k + 1)) :=
      Finset.mem_Icc.mpr ⟨by omega, Nat.lt_two_pow_self.le⟩
    rw [← Finset.add_sum_erase _ _ hmem]
    have hrest : ∑ j ∈ (Finset.Icc 1 (2 ^ (k + 1))).erase (k + 1),
        (if 2 ^ (k + 1) = 2 ^ j then (2 ^ j : ℂ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      have hne : 2 ^ (k + 1) ≠ 2 ^ j := fun heq ↦
        (Finset.mem_erase.mp hj).1 (Nat.pow_right_injective le_rfl heq.symm)
      simp [hne]
    simp only [hrest, add_zero, ↓reduceIte]
    push_cast
    exact (div_self (by positivity)).symm
  have hlim0 : Tendsto (fun k : ℕ ↦
      TauCeti.summatory (fun n : ℕ ↦ n) (fun n ↦ if n = 0 then 0 else dyadicCancel n)
        ((2 ^ (k + 1) + 1 : ℕ) : ℝ) / ((2 ^ (k + 1) + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr fun k ↦ ?_
    rw [hsum_eq, sum_Icc_dyadicCancel]
    have hzero : ∑ j ∈ Finset.Icc 1 (2 ^ (k + 1) + 1),
        (if 2 ^ (k + 1) + 1 = 2 ^ j then (2 ^ j : ℂ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hdvd1 : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (by omega)
      have hdvd2 : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
      have hne : 2 ^ (k + 1) + 1 ≠ 2 ^ j := by omega
      simp [hne]
    simp [hzero]
  exact one_ne_zero ((tendsto_nhds_unique (hL.comp hseq1) hlim1).symm.trans
    (tendsto_nhds_unique (hL.comp hseq0) hlim0))

/-- **A Chebyshev bound alone does not imply the sharp or interval Wiener--Ikehara theorem.**
There exist `f : ℕ → ℂ` and `G : ℂ → ℂ` such that `∑_{1 ≤ n ≤ x} ‖f n‖ = O(x)`, `G` is continuous
on `{s | 1 ≤ s.re}`, and `G s = LSeries f s` on `{s | 1 < s.re}` (so `wienerIkehara_smoothed`
applies with residue `A = 0`), yet the normalized summatory function `S_f (x) / x` does not
converge to any limit as `x → ∞`. -/
theorem exists_isBigO_sum_Icc_norm_id_and_continuousOn_eq_LSeries_and_not_tendsto_summatory_div :
    ∃ (f : ℕ → ℂ) (G : ℂ → ℂ),
      ((fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖f n‖) =O[atTop] fun x ↦ x) ∧
      ContinuousOn G {s : ℂ | 1 ≤ s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = LSeries f s) ∧
      ¬ ∃ L : ℂ, Tendsto (fun x : ℝ ↦
        TauCeti.summatory (fun n : ℕ ↦ n) (fun n ↦ if n = 0 then 0 else f n) x / x)
        atTop (𝓝 L) :=
  ⟨dyadicCancel, fun s ↦ ∑' j : ℕ, dyadicDirichletTerm j s, isBigO_sum_Icc_norm_dyadicCancel,
    continuousOn_tsum_dyadicDirichletTerm, fun _ hs ↦ tsum_dyadicDirichletTerm_eq_LSeries hs,
    not_tendsto_summatory_dyadicCancel_div⟩

end Counterexample

end TauCeti.LSeries
