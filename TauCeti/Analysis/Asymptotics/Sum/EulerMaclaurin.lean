/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The Euler–Maclaurin summation formula

For integers `a ≤ n`, the Euler–Maclaurin formula expresses `∑_{j=a}^n f(j)` through the
integral `∫_a^n f`, the endpoint values of `f` and of its odd-order derivatives weighted by
Bernoulli numbers, and an exact remainder integral against the periodic Bernoulli function
`Bₖ({x})`, where `{x} = x - ⌊x⌋` is the fractional part, written
`bernoulliFun k (Int.fract x)`. The function `f` takes values in a real Banach space `E`, so
complex-valued `f` is included.

It is the basic tool for the asymptotics of sums `∑_{j<n} f(j)` as `n → ∞`, such as those of
`∑ j^α`, `∑ 1/j` and `∑ j log j`: the remainder integral is controlled by `f^{(k)}` alone.

## Main results

* `IntervalIntegrable.bernoulliFun_fract_smul`: the remainder integrands
  `Bₖ({x}) g(x)` are interval integrable whenever `g` is.
* `TauCeti.sum_Icc_eq_eulerMaclaurin_of_hasDerivAt`: the formula of any order `k ≥ 1`, for a
  family `g` with `g 0 = f` continuous on `[a, n]` up to order `k - 1`, each `g i` having
  derivative `g (i + 1)` on `(a, n)`, and `g k` interval integrable:
  `∑_{j=a}^n g₀(j) = ∫_a^n g₀ + (g₀(a) + g₀(n))/2 + ∑_{s=2}^k Bₛ/s! (g_{s-1}(n) - g_{s-1}(a))
    - (-1)^k/k! ∫_a^n Bₖ({x}) g_k(x) dx`.
* `TauCeti.sum_Icc_eq_eulerMaclaurin`: the even-order form of DLMF 2.10.1 for `f` of class
  `C^{2m}` on `[a, n]`, with derivatives taken within `[a, n]`, and remainder
  `∫_a^n (B_{2m} - B_{2m}({x}))/(2m)! f^{(2m)}(x) dx`.

The proof integrates by parts on each unit interval `[j, j + 1]`, on whose interior `(j, j + 1)`
`Bₖ({x}) = Bₖ(x - j)` (the endpoints do not affect the integral), using `Bₖ' = k Bₖ₋₁`
(`hasDerivAt_bernoulliFun`), `Bₖ(1) = Bₖ(0) = Bₖ` for `k ≠ 1`
(`bernoulliFun_endpoints_eq_of_ne_one`) and the vanishing of the odd Bernoulli numbers beyond
`B₁` (`bernoulli_eq_zero_of_odd`).

## References

* NIST *Digital Library of Mathematical Functions*, §2.10(i), formula 2.10.1.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §1.
-/

public section

open Finset intervalIntegral MeasureTheory
open scoped Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The product of an interval integrable function with the periodic Bernoulli function
`Bₖ({x})`, where `{x} = x - ⌊x⌋`, is interval integrable, so the remainder integrals of the
Euler–Maclaurin formula exist. -/
theorem IntervalIntegrable.bernoulliFun_fract_smul {u : ℝ → E} {a b : ℝ}
    (hu : IntervalIntegrable u volume a b) (k : ℕ) :
    IntervalIntegrable (fun x => bernoulliFun k (Int.fract x) • u x) volume a b := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_bernoulliFun k).continuousOn
  rw [intervalIntegrable_iff] at hu ⊢
  exact hu.bdd_smul C
    ((continuous_bernoulliFun k).measurable.comp measurable_fract).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x =>
      hC _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩)

namespace TauCeti

/-- One integration by parts against a shifted Bernoulli polynomial on `[t, t + 1]`. -/
private theorem integral_bernoulliFun_sub_smul {u u' : ℝ → E} {t : ℝ} (k : ℕ)
    (hu : ContinuousOn u (Set.Icc t (t + 1)))
    (hderiv : ∀ x ∈ Set.Ioo t (t + 1), HasDerivAt u (u' x) x)
    (hint : IntervalIntegrable u' volume t (t + 1)) :
    ∫ x in t..t + 1, bernoulliFun k (x - t) • u x =
      ((k + 1 : ℝ)⁻¹ * bernoulliFun (k + 1) 1) • u (t + 1) -
        ((k + 1 : ℝ)⁻¹ * bernoulliFun (k + 1) 0) • u t -
        (k + 1 : ℝ)⁻¹ • ∫ x in t..t + 1, bernoulliFun (k + 1) (x - t) • u' x := by
  have ht : t ≤ t + 1 := by linarith
  have hB : ∀ x, HasDerivAt (fun x => (k + 1 : ℝ)⁻¹ * bernoulliFun (k + 1) (x - t))
      (bernoulliFun k (x - t)) x := fun x => by
    simpa [div_eq_inv_mul] using (antideriv_bernoulliFun k (x - t)).comp_sub_const x t
  have h := integral_smul_deriv_eq_deriv_smul_of_hasDerivAt (by fun_prop)
    (by rwa [Set.uIcc_of_le ht]) (fun x _ => hB x)
    (fun x hx => hderiv x (by rwa [min_eq_left ht, max_eq_right ht] at hx))
    ((by fun_prop : Continuous _).intervalIntegrable _ _) hint
  simp only [add_sub_cancel_left, sub_self, mul_smul, intervalIntegral.integral_smul] at h
  rw [mul_smul, mul_smul, h]
  abel

/-- The Euler–Maclaurin formula of order `k ≥ 1` on one unit interval `[t, t + 1]`, with the
remainder written against the shifted Bernoulli polynomial `Bₖ(x - t)`. -/
private theorem inv_two_smul_add_eq_eulerMaclaurin {g : ℕ → ℝ → E} {t : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hcont : ∀ i < k, ContinuousOn (g i) (Set.Icc t (t + 1)))
    (hderiv : ∀ i < k, ∀ x ∈ Set.Ioo t (t + 1), HasDerivAt (g i) (g (i + 1) x) x)
    (hint : IntervalIntegrable (g k) volume t (t + 1)) :
    (2 : ℝ)⁻¹ • (g 0 t + g 0 (t + 1)) = (∫ x in t..t + 1, g 0 x) +
      ∑ s ∈ Icc 2 k, (bernoulli s / s ! : ℝ) • (g (s - 1) (t + 1) - g (s - 1) t) -
      ((-1) ^ k / k ! : ℝ) • ∫ x in t..t + 1, bernoulliFun k (x - t) • g k x := by
  induction k, hk using Nat.le_induction with
  | base =>
    have h := integral_bernoulliFun_sub_smul 0 (hcont 0 one_pos) (hderiv 0 one_pos) hint
    simp only [bernoulliFun_zero, one_smul, zero_add, Nat.cast_zero, inv_one, one_mul,
      bernoulliFun_eval_one, bernoulliFun_eval_zero, bernoulli_one] at h
    rw [Icc_eq_empty (by norm_num), sum_empty, h]
    norm_num
    module
  | succ k hk ih =>
    have hgk : IntervalIntegrable (g k) volume t (t + 1) :=
      ((hcont k (by omega)).mono (Set.uIcc_of_le (by linarith)).subset).intervalIntegrable
    have h := integral_bernoulliFun_sub_smul k (hcont k (by omega)) (hderiv k (by omega)) hint
    rw [bernoulliFun_endpoints_eq_of_ne_one (by omega), bernoulliFun_eval_zero] at h
    -- `(-1)^k Bₖ₊₁ = -Bₖ₊₁`: either `k` is odd, or `k + 1 ≥ 3` is odd and `Bₖ₊₁ = 0`.
    have hB : (-1 : ℝ) ^ k * bernoulli (k + 1) = -bernoulli (k + 1) := by
      rcases Nat.even_or_odd k with he | ho
      · simp [bernoulli_eq_zero_of_odd he.add_one (by omega)]
      · rw [ho.neg_one_pow, neg_one_mul]
    rw [ih (fun i hi => hcont i (by omega)) (fun i hi => hderiv i (by omega)) hgk, h,
      sum_Icc_succ_top (by omega), Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
    simp only [div_eq_mul_inv, mul_inv]
    push_cast
    linear_combination (norm := module)
      (-(k ! : ℝ)⁻¹ * (k + 1 : ℝ)⁻¹ * hB) • (g k (t + 1) - g k t)

/-- On `(n, n + 1)` the periodic Bernoulli function is the shifted Bernoulli polynomial. -/
private theorem eqOn_bernoulliFun_fract (k : ℕ) (n : ℤ) :
    Set.EqOn (fun x => bernoulliFun k (Int.fract x)) (fun x => bernoulliFun k (x - n))
      (Set.uIoo (n : ℝ) (n + 1)) := by
  intro x hx
  rw [Set.uIoo_of_le (by linarith)] at hx
  simp only [Int.fract, Int.floor_eq_iff.2 ⟨hx.1.le, hx.2⟩]

/-- **Euler–Maclaurin formula** of order `k ≥ 1`. Let `g 0 = f` and suppose that, on `[a, n]`
for integers `a ≤ n`, each `g i` with `i < k` is continuous and has derivative `g (i + 1)` at
every interior point, and that `g k` is interval integrable. Then
`∑_{j=a}^n f(j) = ∫_a^n f + (f(a) + f(n))/2 + ∑_{s=2}^k Bₛ/s! (g_{s-1}(n) - g_{s-1}(a))
  - (-1)^k/k! ∫_a^n Bₖ({x}) g_k(x) dx`,
where `Bₖ({x})`, with `{x} = x - ⌊x⌋` the fractional part, is the periodic Bernoulli
function. -/
theorem sum_Icc_eq_eulerMaclaurin_of_hasDerivAt {g : ℕ → ℝ → E} {a n : ℤ} (han : a ≤ n)
    {k : ℕ} (hk : 1 ≤ k) (hcont : ∀ i < k, ContinuousOn (g i) (Set.Icc (a : ℝ) n))
    (hderiv : ∀ i < k, ∀ x ∈ Set.Ioo (a : ℝ) n, HasDerivAt (g i) (g (i + 1) x) x)
    (hint : IntervalIntegrable (g k) volume a n) :
    ∑ j ∈ Icc a n, g 0 j = (∫ x in a..n, g 0 x) + (2 : ℝ)⁻¹ • (g 0 a + g 0 n) +
      ∑ s ∈ Icc 2 k, (bernoulli s / s ! : ℝ) • (g (s - 1) n - g (s - 1) a) -
      ((-1) ^ k / k ! : ℝ) • ∫ x in a..n, bernoulliFun k (Int.fract x) • g k x := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = a + m := ⟨(n - a).toNat, by omega⟩
  clear han
  induction m with
  | zero => simp [← two_smul ℝ (g 0 a), smul_smul]
  | succ m ih =>
    -- Split `[a, a + m + 1]` as `[a, a + m] ∪ [a + m, a + m + 1]`.
    set t : ℝ := a + m with ht
    have hcast : (((a + (m + 1 : ℕ) : ℤ)) : ℝ) = t + 1 := by push_cast; ring
    have hcast' : (((a + m : ℤ)) : ℝ) = t := by push_cast; ring
    rw [hcast] at hcont hderiv hint ⊢
    rw [hcast'] at ih
    have ha : (a : ℝ) ≤ t := by rw [ht]; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have h₁ : Set.uIcc (a : ℝ) t ⊆ Set.Icc (a : ℝ) (t + 1) := by
      rw [Set.uIcc_of_le ha]; exact Set.Icc_subset_Icc_right (by linarith)
    have h₂ : Set.uIcc t (t + 1) ⊆ Set.Icc (a : ℝ) (t + 1) := by
      rw [Set.uIcc_of_le (by linarith)]; exact Set.Icc_subset_Icc_left ha
    have hab : Set.uIcc (a : ℝ) (t + 1) = Set.Icc (a : ℝ) (t + 1) := Set.uIcc_of_le (by linarith)
    have hint₁ : IntervalIntegrable (g k) volume a t := hint.mono_set (hab ▸ h₁)
    have hint₂ : IntervalIntegrable (g k) volume t (t + 1) := hint.mono_set (hab ▸ h₂)
    have hg₁ : IntervalIntegrable (g 0) volume a t :=
      ((hcont 0 hk).mono h₁).intervalIntegrable
    have hg₂ : IntervalIntegrable (g 0) volume t (t + 1) :=
      ((hcont 0 hk).mono h₂).intervalIntegrable
    have hunit := inv_two_smul_add_eq_eulerMaclaurin (t := t) hk
      (fun i hi => (hcont i hi).mono (Set.uIcc_of_le (by linarith : t ≤ t + 1) ▸ h₂))
      (fun i hi x hx => hderiv i hi x ⟨ha.trans_lt hx.1, hx.2⟩) hint₂
    rw [← integral_congr_uIoo fun x hx => congrArg (· • g k x) (by
      simpa [ht] using eqOn_bernoulliFun_fract k (a + m) (by simpa [ht] using hx))] at hunit
    have hsum : Icc a (a + (m + 1 : ℕ)) = insert (a + m + 1) (Icc a (a + m)) := by
      ext j; simp only [mem_Icc, mem_insert]; omega
    rw [hsum, sum_insert (by simp), ih (fun i hi => (hcont i hi).mono (Set.uIcc_of_le ha ▸ h₁))
      (fun i hi x hx => hderiv i hi x ⟨hx.1, hx.2.trans (by linarith)⟩) hint₁,
      ← integral_add_adjacent_intervals hg₁ hg₂,
      ← integral_add_adjacent_intervals (hint₁.bernoulliFun_fract_smul k)
        (hint₂.bernoulliFun_fract_smul k)]
    have hlast : ((a + m + 1 : ℤ) : ℝ) = t + 1 := by push_cast; ring
    have hΔ : ∑ s ∈ Icc 2 k, (bernoulli s / s ! : ℝ) • (g (s - 1) (t + 1) - g (s - 1) a) =
        ∑ s ∈ Icc 2 k, (bernoulli s / s ! : ℝ) • (g (s - 1) t - g (s - 1) a) +
          ∑ s ∈ Icc 2 k, (bernoulli s / s ! : ℝ) • (g (s - 1) (t + 1) - g (s - 1) t) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun s _ => by module
    rw [hlast, hΔ]
    linear_combination (norm := module) hunit

/-- **Euler–Maclaurin formula** (DLMF 2.10.1). For integers `a ≤ n`, `m ≥ 1` and `f` of class
`C^{2m}` on `[a, n]`, with derivatives `f^{(i)}` taken within `[a, n]`,
`∑_{j=a}^n f(j) = ∫_a^n f + f(a)/2 + f(n)/2
  + ∑_{s=1}^{m-1} B_{2s}/(2s)! (f^{(2s-1)}(n) - f^{(2s-1)}(a))
  + ∫_a^n (B_{2m} - B_{2m}({x}))/(2m)! f^{(2m)}(x) dx`,
where `B_{2m}({x})`, with `{x} = x - ⌊x⌋` the fractional part, is the periodic Bernoulli
function. -/
theorem sum_Icc_eq_eulerMaclaurin {f : ℝ → E} {a n : ℤ} (han : a ≤ n) {m : ℕ} (hm : 1 ≤ m)
    (hf : ContDiffOn ℝ (2 * m : ℕ) f (Set.Icc (a : ℝ) n)) :
    ∑ j ∈ Icc a n, f j = (∫ x in a..n, f x) + (2 : ℝ)⁻¹ • f a + (2 : ℝ)⁻¹ • f n +
      ∑ s ∈ Ico 1 m, (bernoulli (2 * s) / (2 * s)! : ℝ) •
        (iteratedDerivWithin (2 * s - 1) f (Set.Icc a n) n -
          iteratedDerivWithin (2 * s - 1) f (Set.Icc a n) a) +
      ∫ x in a..n, ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)!) •
        iteratedDerivWithin (2 * m) f (Set.Icc a n) x := by
  rcases han.lt_or_eq with han | rfl
  swap
  · simp [← add_smul]
    norm_num
  set g : ℕ → ℝ → E := fun i => iteratedDerivWithin i f (Set.Icc a n) with hg
  have han' : (a : ℝ) ≤ n := by exact_mod_cast han.le
  have hU : UniqueDiffOn ℝ (Set.Icc (a : ℝ) n) := uniqueDiffOn_Icc (by exact_mod_cast han)
  have hcont : ∀ i ≤ 2 * m, ContinuousOn (g i) (Set.Icc (a : ℝ) n) := fun i hi =>
    hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hi) hU
  have hderiv : ∀ i < 2 * m, ∀ x ∈ Set.Ioo (a : ℝ) n, HasDerivAt (g i) (g (i + 1) x) x := by
    intro i hi x hx
    have hx' : Set.Icc (a : ℝ) n ∈ nhds x := Icc_mem_nhds hx.1 hx.2
    have hd := hf.differentiableOn_iteratedDerivWithin (m := i) (by exact_mod_cast hi) hU x
      (Set.Ioo_subset_Icc_self hx)
    simp only [hg, iteratedDerivWithin_succ, derivWithin_of_mem_nhds hx']
    exact (hd.differentiableAt hx').hasDerivAt
  have hint : ∀ i ≤ 2 * m, IntervalIntegrable (g i) volume a n := fun i hi =>
    (hcont i hi).intervalIntegrable_of_Icc han'
  have hEM := sum_Icc_eq_eulerMaclaurin_of_hasDerivAt (g := g) han.le (k := 2 * m) (by omega)
    (fun i hi => hcont i hi.le) hderiv (hint _ le_rfl)
  -- The odd-index terms `s = 2r + 3` vanish, since `B_{2r+3} = 0`.
  have heven : ∀ m' ≥ 1, ∑ s ∈ Icc 2 (2 * m'), (bernoulli s / s ! : ℝ) • (g (s - 1) n - g (s - 1) a)
      = ∑ s ∈ Icc 1 m', (bernoulli (2 * s) / (2 * s)! : ℝ) •
        (g (2 * s - 1) n - g (2 * s - 1) a) := by
    intro m' hm'
    induction m', hm' using Nat.le_induction with
    | base => simp
    | succ m' hm' ih =>
      have h3 : bernoulli (2 * m' + 1) = 0 := bernoulli_eq_zero_of_odd ⟨m', rfl⟩ (by omega)
      rw [show 2 * (m' + 1) = 2 * m' + 1 + 1 by ring, sum_Icc_succ_top (by omega),
        sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), ih, h3]
      simp [mul_add]
  -- The `s = m` term is absorbed into the remainder by
  -- `∫_a^n f^{(2m)} = f^{(2m-1)}(n) - f^{(2m-1)}(a)`.
  have hFTC : ∫ x in a..n, g (2 * m) x = g (2 * m - 1) n - g (2 * m - 1) a := by
    have h := integral_eq_sub_of_hasDerivAt_of_le han' (hcont (2 * m - 1) (by omega))
      (fun x hx => hderiv (2 * m - 1) (by omega) x hx) (hint (2 * m - 1 + 1) (by omega))
    rwa [Nat.sub_add_cancel (by omega)] at h
  rw [heven m hm, ← Finset.Ico_add_one_right_eq_Icc 1 m, sum_Ico_succ_top hm] at hEM
  have hR : ∫ x in a..n, ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)!) •
        g (2 * m) x =
      (bernoulli (2 * m) / (2 * m)! : ℝ) • (∫ x in a..n, g (2 * m) x) -
        (1 / (2 * m)! : ℝ) • ∫ x in a..n, bernoulliFun (2 * m) (Int.fract x) • g (2 * m) x := by
    have h₁ : IntervalIntegrable (fun x => (bernoulli (2 * m) / (2 * m)! : ℝ) • g (2 * m) x)
        volume a n := (hint _ le_rfl).smul _
    have h₂ : IntervalIntegrable (fun x => (1 / (2 * m)! : ℝ) •
        bernoulliFun (2 * m) (Int.fract x) • g (2 * m) x) volume a n :=
      ((hint _ le_rfl).bernoulliFun_fract_smul _).smul _
    rw [← intervalIntegral.integral_smul, ← intervalIntegral.integral_smul,
      ← intervalIntegral.integral_sub h₁ h₂]
    exact integral_congr fun x _ => by module
  simp only [hg, iteratedDerivWithin_zero] at hEM hR hFTC ⊢
  rw [hEM, hR, hFTC, pow_mul, neg_one_sq, one_pow]
  module

end TauCeti
