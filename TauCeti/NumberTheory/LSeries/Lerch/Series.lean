/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.SlitPlane

/-!
# The Lerch transcendent: power series, compact convergence, and periodic zeta comparison

The Lerch transcendent is defined on the open unit disc `‖z‖ < 1` by the principal-logarithm power
series

`lerchSeries z s c = ∑' n : ℕ, z ^ n * Complex.exp (-s * Complex.log (n + c))`.

The additive-phase companion `lerchZeta s a c = lerchSeries (exp (2πia)) s c` specializes on the
upper half-plane `0 < a.im` to the same convergent series and on real `a` with `1 < s.re` to
Mathlib's exponential zeta function via `expZeta a s = exp (2πia) * lerchSeries (exp (2πia)) s 1`.

Writing the terms with `exp (-s * log (n + c))` matches `(n + c) ^ (-s)` whenever every `n + c` is
nonzero, while keeping every term entire in `s` and monomial in `z` without branch-cut case splits.
On compact subsets where `‖z‖ < 1` and `n + c ≠ 0`, the series is dominated by a single summable
sequence; when `c` lies in `Complex.slitPlane`, all shifts `n + c` stay in `Complex.slitPlane`,
giving uniform summable bounds for all mixed partial derivatives in `(z, s, c)`, joint analyticity
on `{p : ℂ × ℂ × ℂ | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane}`, and the parameter-raising
derivative `∂_c Φ(z, s, c) = -s * Φ(z, s + 1, c)`.

## Main definitions

* `TauCeti.lerchSeries`: the initial Lerch series `∑' n : ℕ, z ^ n * exp (-s * log (n + c))`.
* `TauCeti.lerchZeta`: the additive-phase Lerch series `lerchSeries (exp (2πia)) s c`.

## Main results

* `TauCeti.summable_norm_lerchSeries_term`, `TauCeti.hasSum_lerchSeries`: absolute convergence on
  `‖z‖ < 1` for all `s, c : ℂ`.
* `TauCeti.exists_summable_norm_lerchSeries_term_le` and
  `TauCeti.exists_summable_norm_iteratedDeriv_lerchSeries_term_le`: uniform summable bounds on
  compact parameter sets for the terms and all mixed partial derivatives in `(z, s, c)`.
* `TauCeti.tendstoUniformlyOn_iteratedDeriv_lerchSeries`: uniform convergence of partial sums of all
  mixed partial derivatives on compact subsets of
  `{p : ℂ × ℂ × ℂ | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane}`.
* `TauCeti.lerchSeries_zero_left`, `TauCeti.lerchSeries_zero_middle`,
  `TauCeti.lerchSeries_eq_cpow_add_mul_add_one`, `TauCeti.lerchSeries_natCast_add`: initial values
  at `z = 0` and `s = 0`, and the `c ↦ c + 1` and `c ↦ c + N` shift identities.
* `TauCeti.hasDerivAt_lerchSeries_left`, `TauCeti.hasDerivAt_lerchSeries_middle`,
  `TauCeti.hasDerivAt_lerchSeries_right`, `TauCeti.analyticOnNhd_lerchSeries`,
  `TauCeti.differentiableOn_lerchSeries`: termwise `z`-, `s`-, and `c`-derivatives (raising `s` to
  `s + 1`) and joint analyticity and holomorphy in `(s, z, c)`.
* `TauCeti.summable_norm_lerchSeries_term_of_norm_le_one`, `TauCeti.expZeta_eq_mul_lerchSeries`,
  `TauCeti.lerchSeries_one_left_eq_riemannZeta`,
  `TauCeti.lerchSeries_neg_one_left_eq_mul_riemannZeta`: boundary absolute convergence on
  `‖z‖ ≤ 1, 1 < s.re` and comparison with `HurwitzZeta.expZeta` and `riemannZeta`.

## References

* J. C. Lagarias and W. C. W. Li, *The Lerch zeta function I. Zeta integrals*, Forum Math. 24
  (2012), 1–48.
* J. C. Lagarias and W. C. W. Li, *The Lerch zeta function II. Analytic continuation*, Forum Math.
  24 (2012), 49–84.
* NIST Digital Library of Mathematical Functions, Chapter 25.14 (*Lerch's Transcendent*).
-/

public section

open Complex Filter Function MeasureTheory Metric Set
open scoped Topology Real

namespace TauCeti

/-- The Lerch transcendent on the open unit disc `‖z‖ < 1`, defined with Mathlib's principal
complex logarithm by `∑' n : ℕ, z ^ n * exp (-s * log (n + c))`. Outside the convergence domain the
value is totalized by `tsum` and carries no regularity assertion. -/
noncomputable def lerchSeries (z s c : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n * Complex.exp (-s * Complex.log (n + c))

/-- Defining series expansion of `lerchSeries`. -/
theorem lerchSeries_def (z s c : ℂ) :
    lerchSeries z s c = ∑' n : ℕ, z ^ n * Complex.exp (-s * Complex.log (n + c)) := by
  rfl

/-- Additive-phase Lerch series `L(s, a, c) = Φ(exp(2πia), s, c)`. -/
noncomputable def lerchZeta (s a c : ℂ) : ℂ :=
  lerchSeries (Complex.exp (2 * Real.pi * I * a)) s c

/-- Defining identity of `lerchZeta` in terms of `lerchSeries`. -/
theorem lerchZeta_def (s a c : ℂ) :
    lerchZeta s a c = lerchSeries (Complex.exp (2 * Real.pi * I * a)) s c := by
  rfl

/-- When no shift `n + c` vanishes, each `exp (-s * log (n + c))` coincides with the principal
complex power `(n + c) ^ (-s)`. -/
theorem lerchSeries_eq_tsum_cpow (z s : ℂ) {c : ℂ} (hc : ∀ n : ℕ, (n : ℂ) + c ≠ 0) :
    lerchSeries z s c = ∑' n : ℕ, z ^ n * ((n : ℂ) + c) ^ (-s) :=
  tsum_congr fun n => by
    rw [cpow_def_of_ne_zero (hc n), mul_comm (Complex.log _)]

/-! ### Uniform norm bounds and compact convergence -/

private theorem norm_log_pow_mul_exp_le {s w : ℂ} {S δ B : ℝ} (hS : ‖s‖ ≤ S) (hS0 : 0 ≤ S)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hw_lo : δ ≤ ‖w‖) (hB1 : 1 ≤ B) (hw_hi : ‖w‖ ≤ B) (k : ℕ) :
    ‖(-Complex.log w) ^ k * Complex.exp (-s * Complex.log w)‖ ≤
      (|Real.log δ| + Real.pi + B) ^ k * Real.exp (S * Real.pi) *
        (Real.exp (-S * Real.log δ) + B ^ S) := by
  have hw0 : 0 < ‖w‖ := hδ0.trans_le hw_lo
  have hlog_w : ‖Complex.log w‖ ≤ |Real.log ‖w‖| + Real.pi := by
    have h1 : ‖Complex.log w‖ ≤ |Real.log ‖w‖| + |w.arg| := by
      simpa [Complex.log_re, Complex.log_im] using norm_le_abs_re_add_abs_im (Complex.log w)
    linarith [abs_arg_le_pi w]
  have hlog_norm : ‖Complex.log w‖ ≤ |Real.log δ| + Real.pi + B := by
    have h1 : Real.log δ ≤ Real.log ‖w‖ := Real.log_le_log hδ0 hw_lo
    have h2 : Real.log ‖w‖ ≤ Real.log B := Real.log_le_log hw0 hw_hi
    have h3 : Real.log B ≤ B - 1 := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hB1)
    have hld : Real.log δ ≤ 0 := Real.log_nonpos hδ0.le hδ1
    rw [abs_of_nonpos hld]
    have habs : |Real.log ‖w‖| ≤ -Real.log δ + B := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hexp_re : (-s * Complex.log w).re ≤ S * (|Real.log ‖w‖| + Real.pi) := by
    calc (-s * Complex.log w).re ≤ ‖-s * Complex.log w‖ := re_le_norm _
      _ = ‖s‖ * ‖Complex.log w‖ := by rw [norm_mul, norm_neg]
      _ ≤ S * (|Real.log ‖w‖| + Real.pi) := mul_le_mul hS hlog_w (norm_nonneg _) hS0
  have hexp_abs : Real.exp (S * |Real.log ‖w‖|) ≤ Real.exp (-S * Real.log δ) + B ^ S := by
    rcases le_or_gt ‖w‖ 1 with hw1 | hw1
    · have hl : |Real.log ‖w‖| ≤ -Real.log δ := by
        rw [abs_of_nonpos (Real.log_nonpos hw0.le hw1)]; linarith [Real.log_le_log hδ0 hw_lo]
      have he : Real.exp (S * |Real.log ‖w‖|) ≤ Real.exp (-S * Real.log δ) := by
        rw [show -S * Real.log δ = S * (-Real.log δ) by ring]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hl hS0)
      linarith [Real.rpow_pos_of_pos (zero_lt_one.trans_le hB1) S]
    · have hl : |Real.log ‖w‖| ≤ Real.log B := by
        rw [abs_of_pos (Real.log_pos hw1)]; exact Real.log_le_log hw0 hw_hi
      have he : Real.exp (S * |Real.log ‖w‖|) ≤ B ^ S := by
        rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hB1), mul_comm (Real.log B)]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hl hS0)
      linarith [Real.exp_pos (-S * Real.log δ)]
  rw [norm_mul, norm_pow, norm_neg, Complex.norm_exp]
  calc ‖Complex.log w‖ ^ k * Real.exp (-s * Complex.log w).re
      ≤ (|Real.log δ| + Real.pi + B) ^ k * Real.exp (S * (|Real.log ‖w‖| + Real.pi)) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hlog_norm k)
          (Real.exp_le_exp.mpr hexp_re) (Real.exp_pos _).le (by positivity)
    _ = (|Real.log δ| + Real.pi + B) ^ k * Real.exp (S * Real.pi) *
          Real.exp (S * |Real.log ‖w‖|) := by rw [mul_add, Real.exp_add]; ring
    _ ≤ (|Real.log δ| + Real.pi + B) ^ k * Real.exp (S * Real.pi) *
          (Real.exp (-S * Real.log δ) + B ^ S) := by gcongr

private theorem summable_pow_add_one_mul_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (m : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ m * r ^ n) := by
  set q : ℝ := (r + 1) / 2 with hq_def
  have hq0 : 0 < q := by positivity
  have hq1 : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg hq0.le]
    linarith [hq_def]
  have hrq : r ≤ q := by linarith [hq_def]
  have hgeom : Summable (fun n : ℕ => (n : ℝ) ^ m * q ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one m hq1
  have hshift : Summable (fun n : ℕ => q⁻¹ * (((n + 1 : ℕ) : ℝ) ^ m * q ^ (n + 1))) :=
    ((summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ m * q ^ n) 1).mpr hgeom).mul_left q⁻¹
  have hle : ∀ n : ℕ, ((n : ℝ) + 1) ^ m * r ^ n ≤ q⁻¹ * (((n + 1 : ℕ) : ℝ) ^ m * q ^ (n + 1)) := by
    intro n
    have hqn : r ^ n ≤ q⁻¹ * q ^ (n + 1) := by
      rw [pow_succ', ← mul_assoc, inv_mul_cancel₀ hq0.ne', one_mul]
      exact pow_le_pow_left₀ hr0 hrq n
    rw [Nat.cast_add, Nat.cast_one, ← mul_assoc, mul_comm q⁻¹, mul_assoc]
    exact mul_le_mul_of_nonneg_left hqn (by positivity)
  exact Summable.of_nonneg_of_le (fun _ => by positivity) hle hshift

private theorem exists_pos_le_norm_natCast_add_on_compact {K : Set ℂ} (hK : IsCompact K)
    (hKc : ∀ c ∈ K, ∀ n : ℕ, (n : ℂ) + c ≠ 0) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ c ∈ K, ∀ n : ℕ, δ ≤ ‖(n : ℂ) + c‖ := by
  rcases K.eq_empty_or_nonempty with rfl | _
  · exact ⟨1, one_pos, le_rfl, by simp⟩
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  set C' : ℝ := max C 0
  set N : ℕ := Nat.ceil (C' + 1)
  have hlarge : ∀ c ∈ K, ∀ n : ℕ, N ≤ n → 1 ≤ ‖(n : ℂ) + c‖ := fun c hc n hn => by
    have hc' : ‖c‖ ≤ C' := (hC c hc).trans (le_max_left C 0)
    have hn' : C' + 1 ≤ (n : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
    have htri : ‖(n : ℂ)‖ ≤ ‖(n : ℂ) + c‖ + ‖-c‖ := by simpa using norm_add_le ((n : ℂ) + c) (-c)
    rw [Complex.norm_natCast, norm_neg] at htri; linarith
  have hcomp : IsCompact ((Finset.range N : Set ℕ) ×ˢ K) :=
    (Finset.finite_toSet _).isCompact.prod hK
  rcases (Finset.range N).eq_empty_or_nonempty with he | _
  · refine ⟨1, one_pos, le_rfl, fun c hc n => hlarge c hc n ?_⟩
    have := Finset.range_eq_empty_iff.mp he; omega
  · have hcont : Continuous (fun p : ℕ × ℂ => ‖(p.1 : ℂ) + p.2‖) :=
      continuous_norm.comp ((continuous_of_discreteTopology.comp continuous_fst).add continuous_snd)
    obtain ⟨δ₀, hδ₀, hmin⟩ := hcomp.exists_forall_le' hcont.continuousOn
      (fun p hp => norm_pos_iff.mpr (hKc p.2 hp.2 p.1))
    refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, min_le_right _ _, fun c hc n => ?_⟩
    rcases lt_or_ge n N with hn | hn
    · exact (min_le_left _ _).trans (hmin (n, c) ⟨Finset.mem_range.mpr hn, hc⟩)
    · exact (min_le_right _ _).trans (hlarge c hc n hn)

private theorem norm_log_pow_lerchTerm_le_aux {s z c : ℂ} {r S C δ : ℝ} (hz : ‖z‖ ≤ r)
    (hs : ‖s‖ ≤ S) (hS0 : 0 ≤ S) (hc : ‖c‖ ≤ C) (hC0 : 0 ≤ C) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hw_lo : ∀ n : ℕ, δ ≤ ‖(n : ℂ) + c‖) (k n : ℕ) :
    ‖z ^ n * ((-Complex.log (n + c)) ^ k * Complex.exp (-s * Complex.log (n + c)))‖ ≤
      (|Real.log δ| + Real.pi + C + 1) ^ k * Real.exp (S * Real.pi) *
        (Real.exp (-S * Real.log δ) * ((n : ℝ) + 1) ^ k * r ^ n +
          (C + 1) ^ Nat.ceil S * ((n : ℝ) + 1) ^ (k + Nat.ceil S) * r ^ n) := by
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hz
  have hw_hi : ‖(n : ℂ) + c‖ ≤ (n : ℝ) + C + 1 := by
    calc ‖(n : ℂ) + c‖ ≤ ‖(n : ℂ)‖ + ‖c‖ := norm_add_le _ _
      _ = (n : ℝ) + ‖c‖ := by rw [Complex.norm_natCast]
      _ ≤ (n : ℝ) + C + 1 := by linarith
  have hbase := norm_log_pow_mul_exp_le hs hS0 hδ0 hδ1 (hw_lo n)
    (by linarith [Nat.cast_nonneg (α := ℝ) n] : 1 ≤ (n : ℝ) + C + 1) hw_hi k
  set L : ℝ := |Real.log δ| + Real.pi + C + 1
  set M : ℕ := Nat.ceil S
  have hL_bound : |Real.log δ| + Real.pi + ((n : ℝ) + C + 1) ≤ L * ((n : ℝ) + 1) := by
    dsimp [L]; nlinarith [Nat.cast_nonneg (α := ℝ) n, abs_nonneg (Real.log δ), Real.pi_pos]
  have hB_bound : ((n : ℝ) + C + 1) ^ S ≤ (C + 1) ^ M * ((n : ℝ) + 1) ^ M := by
    have h1 : (n : ℝ) + C + 1 ≤ (C + 1) * ((n : ℝ) + 1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    calc ((n : ℝ) + C + 1) ^ S
        ≤ ((n : ℝ) + C + 1) ^ (M : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n])
            (Nat.le_ceil S)
      _ = ((n : ℝ) + C + 1) ^ M := Real.rpow_natCast _ M
      _ ≤ ((C + 1) * ((n : ℝ) + 1)) ^ M := pow_le_pow_left₀ (by positivity) h1 M
      _ = (C + 1) ^ M * ((n : ℝ) + 1) ^ M := mul_pow _ _ M
  rw [norm_mul, norm_pow]
  calc ‖z‖ ^ n * ‖(-Complex.log ((n : ℂ) + c)) ^ k * Complex.exp (-s * Complex.log ((n : ℂ) + c))‖
      ≤ r ^ n * ((L * ((n : ℝ) + 1)) ^ k * Real.exp (S * Real.pi) *
          (Real.exp (-S * Real.log δ) + (C + 1) ^ M * ((n : ℝ) + 1) ^ M)) := by
        refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz n) ?_ (norm_nonneg _)
          (pow_nonneg hr0 n)
        exact hbase.trans <| mul_le_mul
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) hL_bound k) (Real.exp_pos _).le)
          (by linarith) (by positivity) (by positivity)
    _ = L ^ k * Real.exp (S * Real.pi) *
          (Real.exp (-S * Real.log δ) * ((n : ℝ) + 1) ^ k * r ^ n +
            (C + 1) ^ M * ((n : ℝ) + 1) ^ (k + M) * r ^ n) := by
        rw [mul_pow, pow_add]; ring

private theorem exists_summable_norm_log_pow_lerchSeries_term_le {K : Set (ℂ × ℂ × ℂ)}
    (hK : IsCompact K) (hKz : ∀ p ∈ K, ‖p.2.1‖ < 1)
    (hKc : ∀ p ∈ K, ∀ n : ℕ, (n : ℂ) + p.2.2 ≠ 0) (k : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n : ℕ, ∀ p ∈ K,
      ‖p.2.1 ^ n * ((-Complex.log (n + p.2.2)) ^ k *
        Complex.exp (-p.1 * Complex.log (n + p.2.2)))‖ ≤ u n := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, summable_zero, by simp⟩
  obtain ⟨p₀, hp₀, hmax_z⟩ := hK.exists_isMaxOn hne
    (continuous_norm.comp (continuous_fst.comp continuous_snd)).continuousOn
  obtain ⟨S₀, hS₀⟩ := (hK.image continuous_fst).isBounded.exists_norm_le
  obtain ⟨C₀, hC₀⟩ := (hK.image (continuous_snd.comp continuous_snd)).isBounded.exists_norm_le
  obtain ⟨δ, hδ0, hδ1, hδK⟩ := exists_pos_le_norm_natCast_add_on_compact
    (hK.image (continuous_snd.comp continuous_snd))
    (by rintro _ ⟨p, hp, rfl⟩ n; exact hKc p hp n)
  set r : ℝ := ‖p₀.2.1‖
  set S : ℝ := max S₀ 0
  set C : ℝ := max C₀ 0
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r < 1 := hKz p₀ hp₀
  have hsum1 : Summable (fun n : ℕ => Real.exp (-S * Real.log δ) * ((n : ℝ) + 1) ^ k * r ^ n) :=
    ((summable_pow_add_one_mul_geometric hr0 hr1 k).mul_left
      (Real.exp (-S * Real.log δ))).congr fun _ => by ring
  have hsum2 : Summable (fun n : ℕ =>
      (C + 1) ^ Nat.ceil S * ((n : ℝ) + 1) ^ (k + Nat.ceil S) * r ^ n) :=
    ((summable_pow_add_one_mul_geometric hr0 hr1 (k + Nat.ceil S)).mul_left
      ((C + 1) ^ Nat.ceil S)).congr fun _ => by ring
  have hsum := (hsum1.add hsum2).mul_left
    ((|Real.log δ| + Real.pi + C + 1) ^ k * Real.exp (S * Real.pi))
  exact ⟨_, hsum, fun n p hp => norm_log_pow_lerchTerm_le_aux (hmax_z hp)
    ((hS₀ p.1 ⟨p, hp, rfl⟩).trans (le_max_left S₀ 0)) (le_max_right S₀ 0)
    ((hC₀ p.2.2 ⟨p, hp, rfl⟩).trans (le_max_left C₀ 0)) (le_max_right C₀ 0)
    hδ0 hδ1 (hδK p.2.2 ⟨p, hp, rfl⟩) k n⟩

/-- On any compact subset `K ⊆ ℂ × ℂ × ℂ` (in coordinates `(s, z, c)`) with `‖z‖ < 1` and
`n + c ≠ 0` for all `n : ℕ`, the Lerch series terms are dominated by a single summable sequence. -/
theorem exists_summable_norm_lerchSeries_term_le {K : Set (ℂ × ℂ × ℂ)} (hK : IsCompact K)
    (hKz : ∀ p ∈ K, ‖p.2.1‖ < 1) (hKc : ∀ p ∈ K, ∀ n : ℕ, (n : ℂ) + p.2.2 ≠ 0) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n : ℕ, ∀ p ∈ K,
      ‖p.2.1 ^ n * Complex.exp (-p.1 * Complex.log (n + p.2.2))‖ ≤ u n := by
  obtain ⟨u, hu, hle⟩ := exists_summable_norm_log_pow_lerchSeries_term_le hK hKz hKc 0
  exact ⟨u, hu, fun n p hp => by simpa using hle n p hp⟩

private theorem continuous_log_pow_lerchSeries_term_prod (c : ℂ) (k : ℕ) :
    Continuous (fun x : ℕ × (ℂ × ℂ) =>
      x.2.2 ^ x.1 * ((-Complex.log (x.1 + c)) ^ k *
        Complex.exp (-x.2.1 * Complex.log (x.1 + c)))) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have h1 : ContinuousAt (fun y : ℕ × (ℂ × ℂ) => y.2.2 ^ y.1) x := by
    have heq : (fun y : ℕ × (ℂ × ℂ) => y.2.2 ^ y.1) =ᶠ[𝓝 x] fun y => y.2.2 ^ x.1 := by
      filter_upwards [(isOpen_discrete ({x.1} : Set ℕ)).preimage continuous_fst |>.mem_nhds rfl]
        with y hy
      rw [mem_preimage, mem_singleton_iff] at hy
      rw [hy]
    exact ContinuousAt.congr ((continuous_snd.comp continuous_snd).pow x.1).continuousAt heq.symm
  have h2 : ContinuousAt (fun y : ℕ × (ℂ × ℂ) =>
      (-Complex.log (y.1 + c)) ^ k * Complex.exp (-y.2.1 * Complex.log (y.1 + c))) x := by
    have hcL : Continuous (fun y : ℕ × (ℂ × ℂ) => Complex.log ((y.1 : ℂ) + c)) :=
      (continuous_of_discreteTopology
        (f := fun m : ℕ => Complex.log ((m : ℂ) + c))).comp continuous_fst
    exact ((hcL.neg.pow k).mul
      (((continuous_fst.comp continuous_snd).neg.mul hcL).cexp)).continuousAt
  exact h1.mul h2

private theorem exists_summable_norm_log_pow_lerchSeries_term_le_fixed_right
    {K : Set (ℂ × ℂ)} (hK : IsCompact K) (hKz : ∀ q ∈ K, ‖q.2‖ < 1) (c : ℂ) (k : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n : ℕ, ∀ q ∈ K,
      ‖q.2 ^ n * ((-Complex.log (n + c)) ^ k * Complex.exp (-q.1 * Complex.log (n + c)))‖ ≤
        u n := by
  set N : ℕ := Nat.ceil (‖c‖ + 1)
  have hshift_ne : ∀ n : ℕ, (n : ℂ) + (c + N) ≠ 0 := fun n h => by
    have htri : ‖((n + N : ℕ) : ℂ)‖ ≤ ‖((n + N : ℕ) : ℂ) + c‖ + ‖-c‖ := by
      simpa using norm_add_le (((n + N : ℕ) : ℂ) + c) (-c)
    have hzero : ((n + N : ℕ) : ℂ) + c = 0 := by push_cast; linear_combination h
    rw [hzero, norm_zero, zero_add, Complex.norm_natCast, norm_neg] at htri
    linarith [Nat.le_ceil (‖c‖ + 1), (by exact_mod_cast Nat.le_add_left N n : (N : ℝ) ≤ ↑(n + N))]
  let emb : ℂ × ℂ → ℂ × ℂ × ℂ := fun q => (q.1, q.2, c + N)
  obtain ⟨u₁, hu₁, hle₁⟩ := exists_summable_norm_log_pow_lerchSeries_term_le
    (hK.image (by fun_prop : Continuous emb))
    (by rintro _ ⟨q, hq, rfl⟩; exact hKz q hq)
    (by rintro _ ⟨_, _, rfl⟩ n; exact hshift_ne n) k
  obtain ⟨M₀, hM₀⟩ := (((Finset.finite_toSet (Finset.range N)).isCompact.prod hK).image
    (continuous_log_pow_lerchSeries_term_prod c k)).isBounded.exists_norm_le
  let M : ℝ := max M₀ 0
  let u : ℕ → ℝ := fun n => if n < N then M else u₁ (n - N)
  have hu : Summable u := (summable_nat_add_iff N).mp (hu₁.congr fun n => by simp [u])
  refine ⟨u, hu, fun n q hq => ?_⟩
  by_cases hn : n < N
  · exact (hM₀ _ ⟨(n, q), ⟨Finset.mem_range.mpr hn, hq⟩, rfl⟩).trans
      (by simp [u, hn, M])
  · simp only [u, hn, ↓reduceIte]
    have hadd : (n : ℂ) + c = ((n - N : ℕ) : ℂ) + (c + N) := by
      have hsub : n - N + N = n := Nat.sub_add_cancel (Nat.le_of_not_lt hn)
      calc (n : ℂ) + c = ((n - N + N : ℕ) : ℂ) + c := by rw [hsub]
        _ = ((n - N : ℕ) : ℂ) + (c + N) := by push_cast; ring
    have hpow : ‖q.2 ^ n‖ ≤ ‖q.2 ^ (n - N)‖ := by
      rw [norm_pow, norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg _) (hKz q hq).le (Nat.sub_le n N)
    rw [norm_mul, hadd]
    calc ‖q.2 ^ n‖ * ‖(-Complex.log (((n - N : ℕ) : ℂ) + (c + N))) ^ k *
          Complex.exp (-q.1 * Complex.log (((n - N : ℕ) : ℂ) + (c + N)))‖
        ≤ ‖q.2 ^ (n - N)‖ * ‖(-Complex.log (((n - N : ℕ) : ℂ) + (c + N))) ^ k *
          Complex.exp (-q.1 * Complex.log (((n - N : ℕ) : ℂ) + (c + N)))‖ :=
            mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = ‖(emb q).2.1 ^ (n - N) * ((-Complex.log (((n - N : ℕ) : ℂ) + (emb q).2.2)) ^ k *
          Complex.exp (-(emb q).1 * Complex.log (((n - N : ℕ) : ℂ) + (emb q).2.2)))‖ := by
            dsimp [emb]; rw [← norm_mul]
      _ ≤ u₁ (n - N) := hle₁ (n - N) (emb q) ⟨q, hq, rfl⟩

/-- On the open unit disc `‖z‖ < 1`, the Lerch series converges absolutely for all `s, c : ℂ`. -/
theorem summable_norm_lerchSeries_term {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    Summable (fun n : ℕ => ‖z ^ n * Complex.exp (-s * Complex.log (n + c))‖) := by
  obtain ⟨u, hu, hle⟩ := exists_summable_norm_log_pow_lerchSeries_term_le_fixed_right
    (isCompact_singleton (x := (s, z))) (by simp [hz]) c 0
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => by simpa using hle n (s, z) rfl) hu

/-- On the open unit disc `‖z‖ < 1`, the Lerch series is summable for all `s, c : ℂ`. -/
theorem summable_lerchSeries_term {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    Summable (fun n : ℕ => z ^ n * Complex.exp (-s * Complex.log (n + c))) :=
  (summable_norm_lerchSeries_term hz s c).of_norm

/-- `HasSum` form of `lerchSeries` on `‖z‖ < 1`. -/
theorem hasSum_lerchSeries {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    HasSum (fun n : ℕ => z ^ n * Complex.exp (-s * Complex.log (n + c))) (lerchSeries z s c) :=
  (summable_lerchSeries_term hz s c).hasSum

/-! ### Initial evaluations and parameter shifts -/

/-- At `z = 0`, only the `n = 0` term survives: `Φ(0, s, c) = exp (-s * log c)`. -/
@[simp]
theorem lerchSeries_zero_left (s c : ℂ) :
    lerchSeries 0 s c = Complex.exp (-s * Complex.log c) := by
  rw [lerchSeries_def, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

/-- Normalization check `Φ(0, 2, 1) = 1`, distinguishing `Φ(z, s, c)` from `z * Φ(z, s, c)`. -/
theorem lerchSeries_zero_two_one : lerchSeries 0 2 1 = 1 := by
  simp

/-- At `s = 0` and `‖z‖ < 1`, the Lerch series reduces to the geometric sum `(1 - z)⁻¹`. -/
theorem lerchSeries_zero_middle {z : ℂ} (hz : ‖z‖ < 1) (c : ℂ) :
    lerchSeries z 0 c = (1 - z)⁻¹ := by
  simpa [lerchSeries_def] using tsum_geometric_of_norm_lt_one hz

/-- One-step shift identity in `c`: `Φ(z, s, c) = exp (-s * log c) + z * Φ(z, s, c + 1)` for
`‖z‖ < 1`. -/
theorem lerchSeries_eq_cpow_add_mul_add_one {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    lerchSeries z s c = Complex.exp (-s * Complex.log c) + z * lerchSeries z s (c + 1) := by
  rw [lerchSeries_def, (summable_lerchSeries_term hz s c).tsum_eq_zero_add]
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_add]
  congr 1
  rw [lerchSeries_def, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [pow_succ', mul_assoc]
  congr 5
  push_cast
  ring

/-- Rearranged shift identity `z * Φ(z, s, c + 1) = Φ(z, s, c) - exp (-s * log c)` on `‖z‖ < 1`. -/
theorem mul_lerchSeries_add_one {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    z * lerchSeries z s (c + 1) = lerchSeries z s c - Complex.exp (-s * Complex.log c) := by
  rw [lerchSeries_eq_cpow_add_mul_add_one hz s c, add_sub_cancel_left]

/-- `N`-step shift identity in `c` on `‖z‖ < 1`, peeling off the first `N` terms of the series. -/
theorem lerchSeries_natCast_add {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) (N : ℕ) :
    lerchSeries z s c =
      (∑ n ∈ Finset.range N, z ^ n * Complex.exp (-s * Complex.log (n + c))) +
        z ^ N * lerchSeries z s (c + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, Finset.sum_range_succ, lerchSeries_eq_cpow_add_mul_add_one hz s (c + N)]
    have hlog : Complex.log (c + (N : ℂ)) = Complex.log ((N : ℂ) + c) := by rw [add_comm]
    have hadd : c + (N : ℂ) + 1 = c + ((N + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hlog, hadd, pow_succ]
    ring

/-! ### Termwise derivatives, compact mixed-derivative bounds, and joint analyticity -/

private theorem natCast_add_mem_slitPlane_iff {c : ℂ} :
    (∀ n : ℕ, (n : ℂ) + c ∈ Complex.slitPlane) ↔ c ∈ Complex.slitPlane :=
  ⟨fun h => by simpa using h 0,
    fun hc n => by simpa using TauCeti.ofReal_add_mem_slitPlane hc (Nat.cast_nonneg n)⟩

private theorem iteratedDeriv_exp_neg_mul (L : ℂ) (k : ℕ) (s : ℂ) :
    iteratedDeriv k (fun w : ℂ => Complex.exp (-w * L)) s =
      (-L) ^ k * Complex.exp (-s * L) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, (funext ih : iteratedDeriv k _ = _)]
    have hd : HasDerivAt (fun w : ℂ => (-L) ^ k * Complex.exp (-w * L))
        ((-L) ^ k * (Complex.exp (-s * L) * (-1 * L))) s :=
      ((((hasDerivAt_neg s).mul_const L)).cexp).const_mul ((-L) ^ k)
    rw [hd.deriv, pow_succ]
    ring

/-- On `‖z‖ < 1`, `w ↦ lerchSeries w s c` has term-by-term complex derivative at `z` for all
`s, c : ℂ`. -/
theorem hasDerivAt_lerchSeries_left {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    HasDerivAt (fun w => lerchSeries w s c)
      (∑' n : ℕ, (n : ℂ) * z ^ (n - 1) * Complex.exp (-s * Complex.log (n + c))) z := by
  set r : ℝ := (‖z‖ + 1) / 2
  have hr_lt : r < 1 := by dsimp [r]; linarith
  have hzr : ‖z‖ < r := by dsimp [r]; linarith
  obtain ⟨u, hu, hle⟩ := exists_summable_norm_log_pow_lerchSeries_term_le_fixed_right
    (isCompact_singleton.prod (isCompact_closedBall (0 : ℂ) r))
    (fun q hq => (mem_closedBall_zero_iff.mp hq.2).trans_lt hr_lt) c 0
  let F : ℕ → ℂ → ℂ := fun n w => w ^ n * Complex.exp (-s * Complex.log (n + c))
  have hFo : ∀ n, DifferentiableOn ℂ (F n) (ball 0 r) := fun n => by fun_prop
  have hFb : ∀ n, ∀ w ∈ ball (0 : ℂ) r, ‖F n w‖ ≤ u n := fun n w hw => by
    simpa [F] using hle n (s, w) ⟨rfl, ball_subset_closedBall hw⟩
  have hdiff : DifferentiableAt ℂ (fun w => ∑' n, F n w) z :=
    (Complex.differentiableOn_tsum_of_summable_norm hu hFo isOpen_ball hFb).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hzr))
  have hsum := Complex.hasSum_deriv_of_summable_norm hu hFo isOpen_ball hFb
    (mem_ball_zero_iff.mpr hzr)
  have hterm : (fun n => deriv (F n) z) =
      fun n : ℕ => (n : ℂ) * z ^ (n - 1) * Complex.exp (-s * Complex.log (n + c)) := by
    ext n
    simp [F]
  have hd := hdiff.hasDerivAt
  rw [← hsum.tsum_eq, hterm] at hd
  exact hd.congr_of_eventuallyEq (Eventually.of_forall fun w => (lerchSeries_def w s c).symm)

/-- Term-by-term formula for `deriv (fun w => lerchSeries w s c) z` on `‖z‖ < 1`. -/
theorem deriv_lerchSeries_left {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    deriv (fun w => lerchSeries w s c) z =
      ∑' n : ℕ, (n : ℂ) * z ^ (n - 1) * Complex.exp (-s * Complex.log (n + c)) :=
  (hasDerivAt_lerchSeries_left hz s c).deriv

/-- For all `s, c : ℂ`, `w ↦ lerchSeries w s c` is holomorphic on the open unit disc. -/
theorem differentiableOn_lerchSeries_left (s c : ℂ) :
    DifferentiableOn ℂ (fun w => lerchSeries w s c) (ball 0 1) := fun _ hz =>
  (hasDerivAt_lerchSeries_left (mem_ball_zero_iff.mp hz) s c).differentiableAt
    |>.differentiableWithinAt

/-- On `‖z‖ < 1`, `w ↦ lerchSeries z w c` is entire and may be differentiated term-by-term in `s`
for all `c : ℂ`. -/
theorem hasDerivAt_lerchSeries_middle {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    HasDerivAt (fun w => lerchSeries z w c)
      (∑' n : ℕ, -Complex.log (n + c) * z ^ n * Complex.exp (-s * Complex.log (n + c))) s := by
  obtain ⟨u, hu, hle⟩ := exists_summable_norm_log_pow_lerchSeries_term_le_fixed_right
    ((isCompact_closedBall s 1).prod isCompact_singleton)
    (fun q hq => by rw [hq.2]; exact hz) c 0
  let F : ℕ → ℂ → ℂ := fun n w => z ^ n * Complex.exp (-w * Complex.log (n + c))
  have hFo : ∀ n, DifferentiableOn ℂ (F n) (ball s 1) := fun n => by fun_prop
  have hFb : ∀ n, ∀ w ∈ ball s 1, ‖F n w‖ ≤ u n := fun n w hw => by
    simpa [F] using hle n (w, z) ⟨ball_subset_closedBall hw, rfl⟩
  have hdiff : DifferentiableAt ℂ (fun w => ∑' n, F n w) s :=
    (Complex.differentiableOn_tsum_of_summable_norm hu hFo isOpen_ball hFb).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self one_pos))
  have hsum := Complex.hasSum_deriv_of_summable_norm hu hFo isOpen_ball hFb (mem_ball_self one_pos)
  have hterm : (fun n => deriv (F n) s) =
      fun n : ℕ => -Complex.log (n + c) * z ^ n * Complex.exp (-s * Complex.log (n + c)) := by
    ext n
    have hd : HasDerivAt (F n)
        (z ^ n * (Complex.exp (-s * Complex.log (n + c)) * (-1 * Complex.log (n + c)))) s :=
      (((hasDerivAt_neg s).mul_const (Complex.log (n + c))).cexp).const_mul (z ^ n)
    rw [hd.deriv]; ring
  have hd := hdiff.hasDerivAt
  rw [← hsum.tsum_eq, hterm] at hd
  exact hd.congr_of_eventuallyEq (Eventually.of_forall fun w => (lerchSeries_def z w c).symm)

/-- Termwise `s`-derivative of `lerchSeries` on `‖z‖ < 1`. -/
theorem deriv_lerchSeries_middle {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    deriv (fun w => lerchSeries z w c) s =
      ∑' n : ℕ, -Complex.log (n + c) * z ^ n * Complex.exp (-s * Complex.log (n + c)) :=
  (hasDerivAt_lerchSeries_middle hz s c).deriv

/-- For `‖z‖ < 1` and any `c : ℂ`, `s ↦ lerchSeries z s c` is entire on `ℂ`. -/
theorem differentiable_lerchSeries_middle {z : ℂ} (hz : ‖z‖ < 1) (c : ℂ) :
    Differentiable ℂ (fun s => lerchSeries z s c) := fun s =>
  (hasDerivAt_lerchSeries_middle hz s c).differentiableAt

/-- Raising relation in `c`: for `‖z‖ < 1` and `c ∈ Complex.slitPlane`,
`∂_c Φ(z, s, c) = -s * Φ(z, s + 1, c)`. -/
theorem hasDerivAt_lerchSeries_right {z : ℂ} (hz : ‖z‖ < 1) (s : ℂ) {c : ℂ}
    (hc : c ∈ Complex.slitPlane) :
    HasDerivAt (fun w => lerchSeries z s w) (-s * lerchSeries z (s + 1) c) c := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_singleton (x := c)).exists_cthickening_subset_open
    Complex.isOpen_slitPlane (singleton_subset_iff.mpr hc)
  have hcb : closedBall c δ ⊆ Complex.slitPlane := by
    simpa [cthickening_singleton _ hδ.le] using hsub
  obtain ⟨u, hu, hle⟩ := exists_summable_norm_lerchSeries_term_le
    (isCompact_singleton.prod (isCompact_singleton.prod (isCompact_closedBall c δ)))
    (fun p hp => by rw [hp.2.1]; exact hz)
    (fun p hp n => slitPlane_ne_zero (natCast_add_mem_slitPlane_iff.mpr (hcb hp.2.2) n))
  let F : ℕ → ℂ → ℂ := fun n w => z ^ n * Complex.exp (-s * Complex.log (n + w))
  have hFo : ∀ n, DifferentiableOn ℂ (F n) (ball c δ) := fun n w hw => by
    have hslit : (n : ℂ) + w ∈ Complex.slitPlane :=
      natCast_add_mem_slitPlane_iff.mpr (hcb (ball_subset_closedBall hw)) n
    exact (((((differentiableAt_id.const_add (n : ℂ)).clog hslit).const_mul (-s)).cexp).const_mul
      (z ^ n)).differentiableWithinAt
  have hFb : ∀ n, ∀ w ∈ ball c δ, ‖F n w‖ ≤ u n := fun n w hw =>
    hle n (s, z, w) ⟨rfl, rfl, ball_subset_closedBall hw⟩
  have hdiff : DifferentiableAt ℂ (fun w => ∑' n, F n w) c :=
    (Complex.differentiableOn_tsum_of_summable_norm hu hFo isOpen_ball hFb).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self hδ))
  have hsum := Complex.hasSum_deriv_of_summable_norm hu hFo isOpen_ball hFb (mem_ball_self hδ)
  have hterm : (fun n => deriv (F n) c) =
      fun n : ℕ => -s * (z ^ n * Complex.exp (-(s + 1) * Complex.log (n + c))) := by
    ext n
    have hslit : (n : ℂ) + c ∈ Complex.slitPlane := natCast_add_mem_slitPlane_iff.mpr hc n
    have hne : (n : ℂ) + c ≠ 0 := slitPlane_ne_zero hslit
    have hd : HasDerivAt (F n)
        (z ^ n * (Complex.exp (-s * Complex.log (n + c)) * (-s * (1 / ((n : ℂ) + c))))) c :=
      (((((hasDerivAt_id c).const_add (n : ℂ)).clog hslit).const_mul (-s)).cexp).const_mul (z ^ n)
    rw [hd.deriv]
    have hexp : Complex.exp (-(s + 1) * Complex.log (n + c)) =
        Complex.exp (-s * Complex.log (n + c)) * (1 / ((n : ℂ) + c)) := by
      rw [show -(s + 1) * Complex.log (n + c) = -s * Complex.log (n + c) - Complex.log (n + c)
        by ring, Complex.exp_sub, Complex.exp_log hne, div_eq_mul_inv, one_div]
    rw [hexp]; ring
  rw [hterm] at hsum
  have hd := hdiff.hasDerivAt
  rw [← hsum.tsum_eq, tsum_mul_left, ← lerchSeries_def] at hd
  exact hd.congr_of_eventuallyEq (Eventually.of_forall fun w => (lerchSeries_def z s w).symm)

/-- Derivative form of the raising relation `∂_c Φ(z, s, c) = -s * Φ(z, s + 1, c)`. -/
theorem deriv_lerchSeries_right {z : ℂ} (hz : ‖z‖ < 1) (s : ℂ) {c : ℂ}
    (hc : c ∈ Complex.slitPlane) :
    deriv (fun w => lerchSeries z s w) c = -s * lerchSeries z (s + 1) c :=
  (hasDerivAt_lerchSeries_right hz s hc).deriv

/-- For `‖z‖ < 1` and any `s : ℂ`, `c ↦ lerchSeries z s c` is holomorphic on `Complex.slitPlane`. -/
theorem differentiableOn_lerchSeries_right {z : ℂ} (hz : ‖z‖ < 1) (s : ℂ) :
    DifferentiableOn ℂ (fun w => lerchSeries z s w) Complex.slitPlane := fun _ hc =>
  (hasDerivAt_lerchSeries_right hz s hc).differentiableAt.differentiableWithinAt

private theorem continuousOn_lerchSeries :
    ContinuousOn (fun p : ℂ × ℂ × ℂ => lerchSeries p.2.1 p.1 p.2.2)
      {p | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane} := by
  set U : Set (ℂ × ℂ × ℂ) := {p | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane}
  have hUo : IsOpen U :=
    (isOpen_lt (continuous_norm.comp (continuous_fst.comp continuous_snd)) continuous_const).inter
      (Complex.isOpen_slitPlane.preimage (continuous_snd.comp continuous_snd))
  intro p₀ hp₀
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_singleton (x := p₀)).exists_cthickening_subset_open
    hUo (singleton_subset_iff.mpr hp₀)
  have hcb : closedBall p₀ δ ⊆ U := by simpa [cthickening_singleton _ hδ.le] using hsub
  obtain ⟨u, hu, hle⟩ := exists_summable_norm_lerchSeries_term_le (isCompact_closedBall p₀ δ)
    (fun q hq => (hcb hq).1)
    (fun q hq n => slitPlane_ne_zero (natCast_add_mem_slitPlane_iff.mpr (hcb hq).2 n))
  have hcball : ContinuousOn (fun p : ℂ × ℂ × ℂ => lerchSeries p.2.1 p.1 p.2.2) (ball p₀ δ) := by
    simp_rw [lerchSeries_def]
    refine continuousOn_tsum (fun n q hq => ?_) hu fun n q hq => hle n q (ball_subset_closedBall hq)
    have hslit : (n : ℂ) + q.2.2 ∈ Complex.slitPlane :=
      natCast_add_mem_slitPlane_iff.mpr (hcb (ball_subset_closedBall hq)).2 n
    exact (((continuous_fst.comp continuous_snd).pow n).continuousAt.mul
      ((continuous_fst.neg.continuousAt.mul
        ((continuous_const.add (continuous_snd.comp continuous_snd)).continuousAt.clog
          hslit)).cexp)).continuousWithinAt
  exact (hcball.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hδ))).continuousWithinAt

/-- `lerchSeries` is jointly analytic in `(s, z, c)` on
`{p : ℂ × ℂ × ℂ | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_lerchSeries :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => lerchSeries p.2.1 p.1 p.2.2)
      {p | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane} := by
  set U : Set (ℂ × ℂ × ℂ) := {p | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane}
  have hUo : IsOpen U :=
    (isOpen_lt (continuous_norm.comp (continuous_fst.comp continuous_snd)) continuous_const).inter
      (Complex.isOpen_slitPlane.preimage (continuous_snd.comp continuous_snd))
  let e : (Fin 3 → ℂ) ≃L[ℂ] ℂ × ℂ × ℂ :=
    { toLinearEquiv :=
        { toFun := fun v => (v 0, v 1, v 2)
          invFun := fun p => ![p.1, p.2.1, p.2.2]
          left_inv := fun v => by ext i; fin_cases i <;> rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := continuous_pi fun i => by fin_cases i <;> fun_prop }
  have han : AnalyticOnNhd ℂ
      ((fun p : ℂ × ℂ × ℂ => lerchSeries p.2.1 p.1 p.2.2) ∘ e) (e ⁻¹' U) := by
    refine ContinuousOn.analyticOnNhd_of_differentiableAt_update
      (continuousOn_lerchSeries.comp e.continuous.continuousOn (mapsTo_preimage _ _))
      (hUo.preimage e.continuous) fun v hv i => ?_
    have hv1 : ‖v 1‖ < 1 := hv.1
    have hv2 : v 2 ∈ Complex.slitPlane := hv.2
    fin_cases i
    · change DifferentiableAt ℂ (fun x => lerchSeries (update v 0 x 1) (update v 0 x 0)
        (update v 0 x 2)) (v 0)
      simpa using (hasDerivAt_lerchSeries_middle hv1 (v 0) (v 2)).differentiableAt
    · change DifferentiableAt ℂ (fun x => lerchSeries (update v 1 x 1) (update v 1 x 0)
        (update v 1 x 2)) (v 1)
      simpa using (hasDerivAt_lerchSeries_left hv1 (v 0) (v 2)).differentiableAt
    · change DifferentiableAt ℂ (fun x => lerchSeries (update v 2 x 1) (update v 2 x 0)
        (update v 2 x 2)) (v 2)
      simpa using (hasDerivAt_lerchSeries_right hv1 (v 0) hv2).differentiableAt
  intro p hp
  have hp' : e.symm p ∈ e ⁻¹' U := by
    rw [mem_preimage, e.apply_symm_apply]
    exact hp
  have hcomp : ((fun q : ℂ × ℂ × ℂ => lerchSeries q.2.1 q.1 q.2.2) ∘ e) ∘ e.symm =
      fun q : ℂ × ℂ × ℂ => lerchSeries q.2.1 q.1 q.2.2 :=
    funext fun q => congrArg (fun r : ℂ × ℂ × ℂ => lerchSeries r.2.1 r.1 r.2.2)
      (e.apply_symm_apply q)
  exact hcomp ▸ (han (e.symm p) hp').comp (e.symm.analyticAt p)

/-- `lerchSeries` is jointly complex differentiable in `(s, z, c)` on
`{p : ℂ × ℂ × ℂ | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane}`. -/
theorem differentiableOn_lerchSeries :
    DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => lerchSeries p.2.1 p.1 p.2.2)
      {p | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane} :=
  analyticOnNhd_lerchSeries.differentiableOn

/-- `lerchZeta` is jointly analytic in `(s, a, c)` on the upper half-plane in `a` and slit plane in
`c`: `{p : ℂ × ℂ × ℂ | 0 < p.2.1.im ∧ p.2.2 ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_lerchZeta :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => lerchZeta p.1 p.2.1 p.2.2)
      {p | 0 < p.2.1.im ∧ p.2.2 ∈ Complex.slitPlane} := by
  intro p hp
  let φ : ℂ × ℂ × ℂ → ℂ × ℂ × ℂ := fun q =>
    (q.1, Complex.exp (2 * Real.pi * I * q.2.1), q.2.2)
  have hφ : AnalyticAt ℂ φ p :=
    analyticAt_fst.prod (((analyticAt_const.mul (analyticAt_fst.comp analyticAt_snd)).cexp).prod
      (analyticAt_snd.comp analyticAt_snd))
  have hmem : φ p ∈ {q : ℂ × ℂ × ℂ | ‖q.2.1‖ < 1 ∧ q.2.2 ∈ Complex.slitPlane} := by
    refine ⟨?_, hp.2⟩
    dsimp [φ]
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    have hre : (2 * (Real.pi : ℂ) * I * p.2.1).re = -2 * Real.pi * p.2.1.im := by
      simp [mul_assoc]
    rw [hre]; nlinarith [Real.pi_pos, hp.1]
  have hcomp := (analyticOnNhd_lerchSeries (φ p) hmem).comp hφ
  exact hcomp.congr (Eventually.of_forall fun q => (lerchZeta_def q.1 q.2.1 q.2.2).symm)

private theorem differentiableOn_iteratedDeriv {f : ℂ → ℂ} {V : Set ℂ} (hf : DifferentiableOn ℂ f V)
    (hVo : IsOpen V) (k : ℕ) : DifferentiableOn ℂ (iteratedDeriv k f) V := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv hVo

private theorem tendstoLocallyUniformlyOn_iteratedDeriv {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {V : Set ℂ}
    (hf : TendstoLocallyUniformlyOn F f atTop V) (hF : ∀ N, DifferentiableOn ℂ (F N) V)
    (hVo : IsOpen V) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun N => iteratedDeriv k (F N)) (iteratedDeriv k f) atTop V := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    simp_rw [iteratedDeriv_succ]
    exact ih.deriv (Eventually.of_forall fun N => differentiableOn_iteratedDeriv (hF N) hVo k) hVo

private theorem hasSum_iteratedDeriv_of_summable_norm {F : ℕ → ℂ → ℂ} {V : Set ℂ} (hVo : IsOpen V)
    (hF : ∀ n, DifferentiableOn ℂ (F n) V) {u : ℕ → ℝ} (hu : Summable u)
    (hle : ∀ n, ∀ w ∈ V, ‖F n w‖ ≤ u n) (k : ℕ) {w₀ : ℂ} (hw₀ : w₀ ∈ V) :
    HasSum (fun n => iteratedDeriv k (F n) w₀) (iteratedDeriv k (fun w => ∑' n, F n w) w₀) := by
  rw [Summable.hasSum_iff_tendsto_nat]
  · have hloc := (tendstoUniformlyOn_tsum_nat hu hle).tendstoLocallyUniformlyOn
    have hsum_diff : ∀ N, DifferentiableOn ℂ (fun w => ∑ n ∈ Finset.range N, F n w) V :=
      fun N => DifferentiableOn.fun_sum fun n _ => hF n
    have hiter := (tendstoLocallyUniformlyOn_iteratedDeriv hloc hsum_diff hVo k).tendsto_at hw₀
    refine hiter.congr fun N => ?_
    induction N with
    | zero => simp
    | succ M ih =>
      simp_rw [Finset.sum_range_succ]
      have hc1 : ContDiffAt ℂ k (fun w => ∑ n ∈ Finset.range M, F n w) w₀ :=
        ((DifferentiableOn.fun_sum fun n _ => hF n).analyticOnNhd hVo w₀ hw₀).contDiffAt
      have hc2 : ContDiffAt ℂ k (F M) w₀ := ((hF M).analyticOnNhd hVo w₀ hw₀).contDiffAt
      rw [← ih]
      exact iteratedDeriv_add hc1 hc2
  · obtain ⟨δ, hδ, hcb⟩ := (isCompact_singleton (x := w₀)).exists_cthickening_subset_open
      hVo (singleton_subset_iff.mpr hw₀)
    have hsub : closedBall w₀ δ ⊆ V := by simpa [cthickening_singleton _ hδ.le] using hcb
    refine Summable.of_norm_bounded (hu.mul_left (k.factorial / δ ^ k)) fun n => ?_
    have hdc : DiffContOnCl ℂ (F n) (ball w₀ δ) :=
      ⟨(hF n).mono (ball_subset_closedBall.trans hsub),
        (hF n).continuousOn.mono (closure_ball_subset_closedBall.trans hsub)⟩
    have hb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hδ hdc
      fun w hw => hle n w (hsub (sphere_subset_closedBall hw))
    calc ‖iteratedDeriv k (F n) w₀‖ ≤ k.factorial * u n / δ ^ k := hb
      _ = k.factorial / δ ^ k * u n := by ring

private theorem iteratedDeriv_lerchSeries_term_eq (n dz ds dc : ℕ) (p : ℂ × ℂ × ℂ) :
    iteratedDeriv dc (fun c =>
      iteratedDeriv dz (fun z =>
        iteratedDeriv ds (fun s => z ^ n * Complex.exp (-s * Complex.log (n + c))) p.1)
        p.2.1) p.2.2 =
      iteratedDeriv dz (fun z : ℂ =>
        z ^ n * iteratedDeriv dc (fun c : ℂ => (-Complex.log (n + c)) ^ ds *
          Complex.exp (-p.1 * Complex.log (n + c))) p.2.2) p.2.1 := by
  let g : ℂ → ℂ := fun c => (-Complex.log (n + c)) ^ ds * Complex.exp (-p.1 * Complex.log (n + c))
  have hs_eval (z c : ℂ) :
      iteratedDeriv ds (fun s => z ^ n * Complex.exp (-s * Complex.log (n + c))) p.1 =
        z ^ n * g c := by
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_exp_neg_mul]
  have hz_pull (a : ℂ) : iteratedDeriv dz (fun z : ℂ => z ^ n * a) p.2.1 =
      iteratedDeriv dz (fun z : ℂ => z ^ n) p.2.1 * a := by
    simp_rw [mul_comm _ a, iteratedDeriv_const_mul_field]
  simp_rw [hs_eval, hz_pull (g _), iteratedDeriv_const_mul_field]
  exact (hz_pull (iteratedDeriv dc g p.2.2)).symm

private theorem norm_mul_iteratedDeriv_right_lerchSeries_term_le (n ds dc : ℕ) {s z' c₀ : ℂ}
    {R B : ℝ} (hR : 0 < R) (hcs : ∀ c' ∈ closedBall c₀ R, c' ∈ Complex.slitPlane)
    (hB : ∀ c' ∈ sphere c₀ R,
      ‖z' ^ n * ((-Complex.log (n + c')) ^ ds * Complex.exp (-s * Complex.log (n + c')))‖ ≤ B) :
    ‖z' ^ n * iteratedDeriv dc (fun c => (-Complex.log (n + c)) ^ ds *
      Complex.exp (-s * Complex.log (n + c))) c₀‖ ≤ dc.factorial * B / R ^ dc := by
  let g : ℂ → ℂ := fun c => (-Complex.log (n + c)) ^ ds * Complex.exp (-s * Complex.log (n + c))
  have hg_diff : DifferentiableOn ℂ (fun c' => z' ^ n * g c') (closedBall c₀ R) := fun c' hc' => by
    have hslit : (n : ℂ) + c' ∈ Complex.slitPlane :=
      natCast_add_mem_slitPlane_iff.mpr (hcs c' hc') n
    have hlog : DifferentiableAt ℂ (fun w : ℂ => Complex.log ((n : ℂ) + w)) c' :=
      (differentiableAt_id.const_add (n : ℂ)).clog hslit
    exact (((hlog.neg.pow ds).mul ((hlog.const_mul (-s)).cexp)).const_mul
      (z' ^ n)).differentiableWithinAt
  rw [← iteratedDeriv_const_mul_field (z' ^ n) g]
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le dc hR
    ⟨hg_diff.mono ball_subset_closedBall, hg_diff.continuousOn.mono closure_ball_subset_closedBall⟩
    hB

/-- On any compact subset `K` of `{p : ℂ × ℂ × ℂ | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane}`
(in coordinates `(s, z, c)`), every fixed mixed iterated partial derivative of order `(dz, ds, dc)`
of the Lerch series terms has a single summable norm bound uniformly on `K`. -/
theorem exists_summable_norm_iteratedDeriv_lerchSeries_term_le {K : Set (ℂ × ℂ × ℂ)}
    (hK : IsCompact K) (hKU : K ⊆ {p : ℂ × ℂ × ℂ | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane})
    (dz ds dc : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n : ℕ, ∀ p ∈ K,
      ‖iteratedDeriv dc (fun c =>
          iteratedDeriv dz (fun z =>
            iteratedDeriv ds (fun s => z ^ n * Complex.exp (-s * Complex.log (n + c))) p.1)
            p.2.1) p.2.2‖ ≤ u n := by
  set U : Set (ℂ × ℂ × ℂ) := {p | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane}
  have hUo : IsOpen U :=
    (isOpen_lt (continuous_norm.comp (continuous_fst.comp continuous_snd)) continuous_const).inter
      (Complex.isOpen_slitPlane.preimage (continuous_snd.comp continuous_snd))
  obtain ⟨δ, hδ, hK'U⟩ := hK.exists_cthickening_subset_open hUo hKU
  set R : ℝ := δ / 2 with hR_def
  have hR : 0 < R := half_pos hδ
  have hmem_K' : ∀ p ∈ K, ∀ z' ∈ closedBall p.2.1 R, ∀ c' ∈ closedBall p.2.2 R,
      (p.1, z', c') ∈ cthickening δ K := fun p hp z' hz' c' hc' => by
    refine mem_cthickening_of_dist_le (p.1, z', c') p δ K hp ?_
    have hRδ : R ≤ δ := by linarith [hR_def, hδ]
    simp only [Prod.dist_eq, dist_self, max_le_iff]
    exact ⟨hδ.le, (mem_closedBall.mp hz').trans hRδ, (mem_closedBall.mp hc').trans hRδ⟩
  obtain ⟨v, hv, hv_le⟩ := exists_summable_norm_log_pow_lerchSeries_term_le hK.cthickening
    (fun q hq => (hK'U hq).1)
    (fun q hq n => slitPlane_ne_zero (natCast_add_mem_slitPlane_iff.mpr (hK'U hq).2 n)) ds
  refine ⟨fun n => (dz.factorial / R ^ dz) * (dc.factorial / R ^ dc) * v n,
    hv.mul_left _, fun n p hp => ?_⟩
  rw [iteratedDeriv_lerchSeries_term_eq]
  let W : ℂ := iteratedDeriv dc (fun c => (-Complex.log (n + c)) ^ ds *
    Complex.exp (-p.1 * Complex.log (n + c))) p.2.2
  have hc_bound : ∀ z' ∈ sphere p.2.1 R, ‖z' ^ n * W‖ ≤ dc.factorial * v n / R ^ dc :=
    fun z' hz' => norm_mul_iteratedDeriv_right_lerchSeries_term_le n ds dc hR
      (fun c' hc' => (hK'U (hmem_K' p hp z' (sphere_subset_closedBall hz') c' hc')).2)
      (fun c' hc' => hv_le n (p.1, z', c')
        (hmem_K' p hp z' (sphere_subset_closedBall hz') c' (sphere_subset_closedBall hc')))
  have hz_diff : DiffContOnCl ℂ (fun z' : ℂ => z' ^ n * W) (ball p.2.1 R) :=
    (by fun_prop : Differentiable ℂ (fun z' : ℂ => z' ^ n * W)).diffContOnCl
  calc ‖iteratedDeriv dz (fun z' : ℂ => z' ^ n * W) p.2.1‖
      ≤ dz.factorial * (dc.factorial * v n / R ^ dc) / R ^ dz :=
        Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le dz hR hz_diff hc_bound
    _ = (dz.factorial / R ^ dz) * (dc.factorial / R ^ dc) * v n := by ring

private theorem iteratedDeriv_lerchSeries_middle_left_eq_tsum {s₀ z₀ : ℂ} (hz : ‖z₀‖ < 1)
    (c : ℂ) (dz ds : ℕ) :
    iteratedDeriv dz (fun z => iteratedDeriv ds (fun s => lerchSeries z s c) s₀) z₀ =
      ∑' n : ℕ, iteratedDeriv dz (fun z =>
        iteratedDeriv ds (fun s => z ^ n * Complex.exp (-s * Complex.log (n + c))) s₀) z₀ := by
  have hs_step : ∀ {z : ℂ}, ‖z‖ < 1 →
      iteratedDeriv ds (fun s => lerchSeries z s c) s₀ =
        ∑' n : ℕ,
          iteratedDeriv ds (fun s => z ^ n * Complex.exp (-s * Complex.log (n + c))) s₀ := by
    intro z hz'
    obtain ⟨u, hu, hle⟩ := exists_summable_norm_log_pow_lerchSeries_term_le_fixed_right
      ((isCompact_closedBall s₀ 1).prod isCompact_singleton)
      (fun q hq => by rw [hq.2]; exact hz') c 0
    simp_rw [lerchSeries_def]
    exact (hasSum_iteratedDeriv_of_summable_norm isOpen_ball (fun n => by fun_prop) hu
      (fun n w hw => by simpa using hle n (w, z) ⟨ball_subset_closedBall hw, rfl⟩)
      ds (mem_ball_self one_pos)).tsum_eq.symm
  set r : ℝ := (‖z₀‖ + 1) / 2
  have hzr : ‖z₀‖ < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have heq : EqOn (fun z => iteratedDeriv ds (fun s => lerchSeries z s c) s₀)
      (fun z => ∑' n : ℕ,
        iteratedDeriv ds (fun s => z ^ n * Complex.exp (-s * Complex.log (n + c))) s₀)
      (ball 0 r) := fun z hz' => hs_step ((mem_ball_zero_iff.mp hz').trans hr1)
  rw [(heq.eventuallyEq_of_mem
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hzr))).iteratedDeriv_eq dz]
  obtain ⟨u, hu, hle⟩ := exists_summable_norm_log_pow_lerchSeries_term_le_fixed_right
    (isCompact_singleton.prod (isCompact_closedBall (0 : ℂ) r))
    (fun q hq => (mem_closedBall_zero_iff.mp hq.2).trans_lt hr1) c ds
  refine (hasSum_iteratedDeriv_of_summable_norm isOpen_ball (fun n => ?_) hu (fun n z' hz' => ?_)
    dz (mem_ball_zero_iff.mpr hzr)).tsum_eq.symm
  · simp_rw [iteratedDeriv_const_mul_field, iteratedDeriv_exp_neg_mul]
    fun_prop
  · rw [iteratedDeriv_const_mul_field, iteratedDeriv_exp_neg_mul]
    exact hle n (s₀, z') ⟨rfl, ball_subset_closedBall hz'⟩

/-- At every `p` with `‖p.2.1‖ < 1` and `p.2.2 ∈ Complex.slitPlane`, the mixed `(dz, ds, dc)`
iterated derivative of `lerchSeries` equals the term-by-term sum of the mixed derivatives. -/
theorem iteratedDeriv_lerchSeries_eq_tsum {p : ℂ × ℂ × ℂ} (hz : ‖p.2.1‖ < 1)
    (hc : p.2.2 ∈ Complex.slitPlane) (dz ds dc : ℕ) :
    iteratedDeriv dc (fun c =>
      iteratedDeriv dz (fun z =>
        iteratedDeriv ds (fun s => lerchSeries z s c) p.1) p.2.1) p.2.2 =
      ∑' n : ℕ, iteratedDeriv dc (fun c =>
        iteratedDeriv dz (fun z =>
          iteratedDeriv ds (fun s => z ^ n * Complex.exp (-s * Complex.log (n + c))) p.1)
          p.2.1) p.2.2 := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_singleton (x := p.2.2)).exists_cthickening_subset_open
    Complex.isOpen_slitPlane (singleton_subset_iff.mpr hc)
  have hcb : closedBall p.2.2 δ ⊆ Complex.slitPlane := by
    simpa [cthickening_singleton _ hδ.le] using hsub
  simp_rw [iteratedDeriv_lerchSeries_middle_left_eq_tsum hz _ dz ds]
  obtain ⟨u, hu, hle⟩ := exists_summable_norm_iteratedDeriv_lerchSeries_term_le
    (isCompact_singleton.prod (isCompact_singleton.prod (isCompact_closedBall p.2.2 δ)))
    (fun q hq => ⟨by rw [hq.2.1]; exact hz, hcb hq.2.2⟩) dz ds 0
  refine (hasSum_iteratedDeriv_of_summable_norm isOpen_ball (fun n c' hc' => ?_) hu
    (fun n c' hc' => ?_) dc (mem_ball_self hδ)).tsum_eq.symm
  · simp_rw [iteratedDeriv_const_mul_field, iteratedDeriv_exp_neg_mul]
    have hpull (w : ℂ) : iteratedDeriv dz (fun z : ℂ =>
        z ^ n * ((-Complex.log (n + w)) ^ ds * Complex.exp (-p.1 * Complex.log (n + w)))) p.2.1 =
        iteratedDeriv dz (fun z : ℂ => z ^ n) p.2.1 *
          ((-Complex.log (n + w)) ^ ds * Complex.exp (-p.1 * Complex.log (n + w))) := by
      simp [mul_comm]
    simp_rw [hpull]
    have hslit : (n : ℂ) + c' ∈ Complex.slitPlane :=
      natCast_add_mem_slitPlane_iff.mpr (hcb (ball_subset_closedBall hc')) n
    have hlog : DifferentiableAt ℂ (fun w : ℂ => Complex.log ((n : ℂ) + w)) c' :=
      (differentiableAt_id.const_add (n : ℂ)).clog hslit
    exact (((hlog.neg.pow ds).mul ((hlog.const_mul (-p.1)).cexp)).const_mul _
      |>.differentiableWithinAt)
  · simpa using hle n (p.1, p.2.1, c') ⟨rfl, rfl, ball_subset_closedBall hc'⟩

/-- Partial sums of every mixed `(dz, ds, dc)` partial derivative of `lerchSeries` converge
uniformly on every compact subset of `{p : ℂ × ℂ × ℂ | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane}`. -/
theorem tendstoUniformlyOn_iteratedDeriv_lerchSeries {K : Set (ℂ × ℂ × ℂ)} (hK : IsCompact K)
    (hKU : K ⊆ {p : ℂ × ℂ × ℂ | ‖p.2.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane}) (dz ds dc : ℕ) :
    TendstoUniformlyOn
      (fun N p => ∑ n ∈ Finset.range N,
        iteratedDeriv dc (fun c =>
          iteratedDeriv dz (fun z =>
            iteratedDeriv ds (fun s => z ^ n * Complex.exp (-s * Complex.log (n + c))) p.1)
            p.2.1) p.2.2)
      (fun p => iteratedDeriv dc (fun c =>
        iteratedDeriv dz (fun z =>
          iteratedDeriv ds (fun s => lerchSeries z s c) p.1) p.2.1) p.2.2)
      atTop K := by
  obtain ⟨u, hu, hle⟩ := exists_summable_norm_iteratedDeriv_lerchSeries_term_le hK hKU dz ds dc
  exact (tendstoUniformlyOn_tsum_nat hu hle).congr_right fun p hp =>
    (iteratedDeriv_lerchSeries_eq_tsum (hKU hp).1 (hKU hp).2 dz ds dc).symm

/-! ### Boundary convergence on `‖z‖ ≤ 1, 1 < s.re` and comparison with `expZeta` -/

/-- On the closed unit disc `‖z‖ ≤ 1` with `1 < s.re`, the Lerch series converges absolutely for
every `c : ℂ`. -/
theorem summable_norm_lerchSeries_term_of_norm_le_one {z s : ℂ} (hz : ‖z‖ ≤ 1) (hs : 1 < s.re)
    (c : ℂ) :
    Summable (fun n : ℕ => ‖z ^ n * Complex.exp (-s * Complex.log (n + c))‖) := by
  set N : ℕ := Nat.ceil (2 * ‖c‖ + 1)
  rw [← summable_nat_add_iff N]
  have hp : Summable (fun n : ℕ =>
      Real.exp (|s.im| * Real.pi) * (2 : ℝ) ^ s.re * ((n + N : ℕ) : ℝ) ^ (-s.re)) :=
    ((summable_nat_add_iff N).mpr (Real.summable_nat_rpow.mpr (by linarith))).mul_left _
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hp
  set m : ℕ := n + N
  have hmN : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.le_add_left N n
  have hNc : 2 * ‖c‖ + 1 ≤ (N : ℝ) := Nat.le_ceil _
  have hm_pos : 0 < (m : ℝ) := by linarith [norm_nonneg c]
  have hw_lo : (m : ℝ) / 2 ≤ ‖(m : ℂ) + c‖ := by
    have htri : ‖(m : ℂ)‖ ≤ ‖(m : ℂ) + c‖ + ‖-c‖ := by simpa using norm_add_le ((m : ℂ) + c) (-c)
    rw [Complex.norm_natCast, norm_neg] at htri; linarith
  have hre : (-s * Complex.log ((m : ℂ) + c)).re ≤
      |s.im| * Real.pi - s.re * Real.log ((m : ℝ) / 2) := by
    have hlog : Real.log ((m : ℝ) / 2) ≤ Real.log ‖(m : ℂ) + c‖ :=
      Real.log_le_log (half_pos hm_pos) hw_lo
    have him : s.im * ((m : ℂ) + c).arg ≤ |s.im| * Real.pi :=
      (le_abs_self _).trans <| by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_arg_le_pi _) (abs_nonneg _)
    simp only [mul_re, neg_re, neg_im, Complex.log_re, Complex.log_im]
    nlinarith [hs]
  have hexp_eq : Real.exp (|s.im| * Real.pi - s.re * Real.log ((m : ℝ) / 2)) =
      Real.exp (|s.im| * Real.pi) * (2 : ℝ) ^ s.re * (m : ℝ) ^ (-s.re) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.log_div hm_pos.ne' two_ne_zero]
    have hlin : -(s.re * (Real.log m - Real.log 2)) =
        Real.log 2 * s.re + Real.log m * (-s.re) := by ring
    rw [hlin, Real.exp_add, ← Real.rpow_def_of_pos two_pos, ← Real.rpow_def_of_pos hm_pos]
    ring
  rw [norm_mul, norm_pow, Complex.norm_exp]
  calc ‖z‖ ^ m * Real.exp (-s * Complex.log ((m : ℂ) + c)).re
      ≤ 1 * Real.exp (|s.im| * Real.pi - s.re * Real.log ((m : ℝ) / 2)) :=
        mul_le_mul (pow_le_one₀ (norm_nonneg _) hz) (Real.exp_le_exp.mpr hre)
          (Real.exp_pos _).le zero_le_one
    _ = Real.exp (|s.im| * Real.pi) * (2 : ℝ) ^ s.re * (m : ℝ) ^ (-s.re) := by
        rw [one_mul, hexp_eq]

/-- Summability of the Lerch series on `‖z‖ ≤ 1` when `1 < s.re`. -/
theorem summable_lerchSeries_term_of_norm_le_one {z s : ℂ} (hz : ‖z‖ ≤ 1) (hs : 1 < s.re)
    (c : ℂ) :
    Summable (fun n : ℕ => z ^ n * Complex.exp (-s * Complex.log (n + c))) :=
  (summable_norm_lerchSeries_term_of_norm_le_one hz hs c).of_norm

/-- `HasSum` form of `lerchSeries` on the closed unit disc `‖z‖ ≤ 1` when `1 < s.re`. -/
theorem hasSum_lerchSeries_of_norm_le_one {z s : ℂ} (hz : ‖z‖ ≤ 1) (hs : 1 < s.re) (c : ℂ) :
    HasSum (fun n : ℕ => z ^ n * Complex.exp (-s * Complex.log (n + c))) (lerchSeries z s c) :=
  (summable_lerchSeries_term_of_norm_le_one hz hs c).hasSum

/-- On `1 < s.re`, Mathlib's periodic zeta `HurwitzZeta.expZeta a s` differs from the `c = 1`
boundary Lerch series at `z = exp (2πia)` by the prefactor `exp (2πia)`. -/
theorem expZeta_eq_mul_lerchSeries (a : ℝ) {s : ℂ} (hs : 1 < s.re) :
    HurwitzZeta.expZeta a s =
      Complex.exp (2 * Real.pi * I * a) * lerchSeries (Complex.exp (2 * Real.pi * I * a)) s 1 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp only [zero_re] at hs
    linarith
  have hsum := HurwitzZeta.hasSum_expZeta_of_one_lt_re a hs
  rw [← hsum.tsum_eq, hsum.summable.tsum_eq_zero_add]
  simp only [Nat.cast_zero, mul_zero, Complex.zero_cpow hs0, div_zero, zero_add]
  rw [lerchSeries_def, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hn1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hexp_n : Complex.exp (2 * Real.pi * I * a * ((n + 1 : ℕ) : ℂ)) =
      Complex.exp (2 * Real.pi * I * a) * Complex.exp (2 * Real.pi * I * a) ^ n := by
    rw [Nat.cast_add_one, mul_add, mul_one, Complex.exp_add, mul_comm _ (n : ℂ),
      Complex.exp_nat_mul, mul_comm]
  have hcpow : (((n + 1 : ℕ) : ℂ) ^ s)⁻¹ = Complex.exp (-s * Complex.log ((n : ℂ) + 1)) := by
    rw [cpow_def_of_ne_zero hn1, ← Complex.exp_neg, Nat.cast_add_one]
    congr 1; ring
  rw [div_eq_mul_inv, hexp_n, hcpow, mul_assoc]

/-- Equivalent form in terms of `lerchZeta`: `expZeta a s = exp (2πia) * lerchZeta s a 1` for
`a : ℝ` and `1 < s.re`. -/
theorem expZeta_eq_mul_lerchZeta (a : ℝ) {s : ℂ} (hs : 1 < s.re) :
    HurwitzZeta.expZeta a s = Complex.exp (2 * Real.pi * I * a) * lerchZeta s a 1 :=
  expZeta_eq_mul_lerchSeries a hs

/-- At `z = 1` and `c = 1`, `lerchSeries 1 s 1 = riemannZeta s` for `1 < s.re`. -/
theorem lerchSeries_one_left_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    lerchSeries 1 s 1 = riemannZeta s := by
  have h := expZeta_eq_mul_lerchSeries 0 hs
  simpa [HurwitzZeta.expZeta_zero] using h.symm

/-- At `z = -1` and `c = 1`, `lerchSeries (-1) s 1 = (1 - 2 ^ (1 - s)) * riemannZeta s` for
`1 < s.re`. -/
theorem lerchSeries_neg_one_left_eq_mul_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    lerchSeries (-1) s 1 = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have hc1 : ∀ n : ℕ, (n : ℂ) + 1 ≠ 0 := fun n => by exact_mod_cast Nat.succ_ne_zero n
  have hs1 : Summable (fun n : ℕ => ((n : ℂ) + 1) ^ (-s)) := by
    simpa [cpow_def_of_ne_zero (hc1 _), mul_comm (Complex.log _)] using
      summable_lerchSeries_term_of_norm_le_one (z := 1) (by simp) hs 1
  have hs2 : Summable (fun n : ℕ => (-1 : ℂ) ^ n * ((n : ℂ) + 1) ^ (-s)) := by
    simpa [cpow_def_of_ne_zero (hc1 _), mul_comm (Complex.log _)] using
      summable_lerchSeries_term_of_norm_le_one (z := -1) (by simp) hs 1
  have hdiff :
      lerchSeries 1 s 1 - lerchSeries (-1) s 1 = (2 : ℂ) ^ (1 - s) * lerchSeries 1 s 1 := by
    rw [lerchSeries_eq_tsum_cpow 1 s hc1, lerchSeries_eq_tsum_cpow (-1) s hc1]
    simp only [one_pow, one_mul]
    rw [← hs1.tsum_sub hs2]
    have hse : Summable (fun m : ℕ => ((2 * m : ℕ) + 1 : ℂ) ^ (-s) -
        (-1 : ℂ) ^ (2 * m) * ((2 * m : ℕ) + 1 : ℂ) ^ (-s)) := by
      simp
    have hodd_term (m : ℕ) : (((2 * m + 1 : ℕ) : ℂ) + 1) ^ (-s) -
        (-1 : ℂ) ^ (2 * m + 1) * (((2 * m + 1 : ℕ) : ℂ) + 1) ^ (-s) =
        (2 : ℂ) ^ (1 - s) * ((m : ℂ) + 1) ^ (-s) := by
      have hpow : (-1 : ℂ) ^ (2 * m + 1) = -1 := by simp [pow_add, pow_mul]
      have hmul : (((2 * m + 1 : ℕ) : ℂ) + 1) ^ (-s) = (2 : ℂ) ^ (-s) * ((m : ℂ) + 1) ^ (-s) := by
        have h1 : ((2 * m + 1 : ℕ) : ℂ) + 1 = ((2 : ℝ) : ℂ) * (((m + 1 : ℕ) : ℝ) : ℂ) := by
          push_cast; ring
        rw [h1, mul_cpow_ofReal_nonneg zero_le_two (Nat.cast_nonneg _)]
        push_cast; rfl
      have htwo : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
        rw [sub_eq_add_neg, cpow_add _ _ two_ne_zero, cpow_one]
      rw [hpow, hmul, htwo]; ring
    have hso : Summable (fun m : ℕ => (((2 * m + 1 : ℕ) : ℂ) + 1) ^ (-s) -
        (-1 : ℂ) ^ (2 * m + 1) * (((2 * m + 1 : ℕ) : ℂ) + 1) ^ (-s)) :=
      (hs1.mul_left ((2 : ℂ) ^ (1 - s))).congr fun m => (hodd_term m).symm
    rw [← tsum_even_add_odd hse hso]
    have heven : (∑' m : ℕ, (((2 * m : ℕ) + 1 : ℂ) ^ (-s) -
        (-1 : ℂ) ^ (2 * m) * ((2 * m : ℕ) + 1 : ℂ) ^ (-s))) = 0 := by simp [pow_mul]
    rw [heven, zero_add, ← tsum_mul_left]
    exact tsum_congr hodd_term
  rw [lerchSeries_one_left_eq_riemannZeta hs] at hdiff
  linear_combination -hdiff

/-- Alternating Basel check `lerchSeries (-1) 2 1 = π ^ 2 / 12`. -/
theorem lerchSeries_neg_one_two_one :
    lerchSeries (-1) 2 1 = (Real.pi : ℂ) ^ 2 / 12 := by
  rw [lerchSeries_neg_one_left_eq_mul_riemannZeta (by norm_num : 1 < (2 : ℂ).re), riemannZeta_two]
  have htwo : (2 : ℂ) ^ ((1 : ℂ) - 2) = (2 : ℂ)⁻¹ := by
    rw [show (1 : ℂ) - 2 = (-1 : ℤ) by norm_num, cpow_intCast, zpow_neg_one]
  rw [htwo]
  ring

/-- Sign-distinguishing check against `HurwitzZeta.expZeta`: at `a = 1 / 2` and `s = 2`,
`expZeta (1 / 2) 2 = -π ^ 2 / 12`, opposite in sign to `lerchSeries (-1) 2 1 = π ^ 2 / 12` due to
the prefactor `exp (2πi · (1 / 2)) = -1`. -/
theorem expZeta_half_two :
    HurwitzZeta.expZeta ((1 / 2 : ℝ) : UnitAddCircle) 2 = -(Real.pi : ℂ) ^ 2 / 12 := by
  rw [expZeta_eq_mul_lerchSeries (1 / 2 : ℝ) (by norm_num : 1 < (2 : ℂ).re)]
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * I * ((1 / 2 : ℝ) : ℂ)) = -1 := by
    push_cast
    rw [show 2 * (Real.pi : ℂ) * I * (1 / 2) = Real.pi * I by ring, Complex.exp_pi_mul_I]
  rw [hexp, lerchSeries_neg_one_two_one]
  ring

end TauCeti
