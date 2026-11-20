/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.ExpDecay
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.LaplaceTransform.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The recurrence of Legendre's continued fraction for the upper incomplete Gamma function

Legendre's continued fraction (DLMF 8.9.2) expands `z^{-a} e^z Γ(a, z)` as
`a₁ / (1 + a₂ / (1 + a₃ / (1 + ⋯)))` with partial denominators `1` and partial numerators
`a₁ = z⁻¹`, `a_{2k} = (k - a) z⁻¹` and `a_{2k + 1} = k z⁻¹` (`k ≥ 1`). Its three-term recurrence
`y(n + 1) = y(n) + aₙ y(n - 1)` (`n ≥ 1`) has an explicit solution built from the Laplace
transforms `K(c, d)(z) = ∫₀^∞ e^{-zt} t^c (1 + t)^d dt` (`c ∈ ℕ`, `d ∈ ℂ`, `Re z > 0`), which
are Kummer's functions `c! U(c + 1, c + d + 2, z)`:
`f(0) = 1`, `f(2k) = (1 - a)_k z^{-k} K(k - 1, a - 1 - k)` (`k ≥ 1`) and
`f(2k + 1) = -(1 - a)_k z^{-k} K(k, a - 1 - k)` (`k ≥ 0`), so that
`-f(1) / f(0) = K(0, a - 1)(z) = ∫₀^∞ e^{-zt} (1 + t)^{a - 1} dt`.

The recurrence rests on two relations between the transforms `K(c, d)`: the pointwise identity
`K(c, d) - K(c, d - 1) = K(c + 1, d - 1)`, and the integration by parts
`z K(c + 1, d) = (c + 1) K(c, d) + d K(c + 1, d - 1)`, whose boundary term at `c = 0` gives
`z K(0, d) = 1 + d K(0, d - 1)`. In Gautschi's approach to continued fractions through minimal
solutions, `f` is the solution whose minimality gives convergence of Legendre's fraction to
`-f(1) / f(0)`: the reduction-of-order criterion
`TauCeti.tendsto_convs_contFrac_of_tendsto_norm_sum` applies to `f` once it is eventually nonzero
with norm-divergent reduction-of-order sums.

## Main definitions

* `Complex.legendreContFractIntegral c d z` — the Laplace transform
  `K(c, d)(z) = ∫₀^∞ e^{-zt} t^c (1 + t)^d dt`.
* `Complex.legendreContFractNum a z` — the 1-indexed partial numerators of DLMF 8.9.2.
* `Complex.legendreContFractSol a z` — the explicit solution of the three-term recurrence, with
  `f(0) = 1`.

## Main results

* `Complex.integrableOn_legendreContFractIntegrand` — the integrand of `K(c, d)(z)` is integrable
  on `(0, ∞)` when `Re z > 0`.
* `Complex.legendreContFractIntegral_sub` — `K(c, d) - K(c, d - 1) = K(c + 1, d - 1)`.
* `Complex.mul_legendreContFractIntegral_zero` — `z K(0, d) = 1 + d K(0, d - 1)`.
* `Complex.mul_legendreContFractIntegral_succ` —
  `z K(c + 1, d) = (c + 1) K(c, d) + d K(c + 1, d - 1)`.
* `Complex.legendreContFractNum_ne_zero` — the partial numerators `aₙ` (`n ≥ 1`) are nonzero
  when `z ≠ 0` and `a ∉ {1, 2, …}`.
* `Complex.legendreContFractSol_recurrence` — `f(n + 1) = f(n) + aₙ f(n - 1)` for `n ≥ 1` and
  `Re z > 0`, for every complex `a`.
* `Complex.legendreContFractSol_one` — `f(1) = -K(0, a - 1)(z)`, while `f(0) = 1`.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.9](https://dlmf.nist.gov/8.9).
* W. Gautschi, *Computational aspects of three-term recurrence relations*, SIAM Rev. 9 (1967),
  24–82, §1 and §5.
-/

public section

noncomputable section

open MeasureTheory Set Polynomial

namespace Complex

/-! ### The Laplace transforms `K(c, d)` -/

/-- The Laplace transform `K(c, d)(z) = ∫₀^∞ e^{-zt} t^c (1 + t)^d dt` (with `c ∈ ℕ`), which
builds the explicit solution of the recurrence of Legendre's continued fraction DLMF 8.9.2. The
integral converges absolutely for `Re z > 0`; elsewhere this is the Bochner integral, which may
take the junk value `0`. -/
def legendreContFractIntegral (c : ℕ) (d z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), cexp (-(z * t)) * (t : ℂ) ^ c * (1 + (t : ℂ)) ^ d

/-- Unfolding `legendreContFractIntegral` to its defining integral. -/
theorem legendreContFractIntegral_def (c : ℕ) (d z : ℂ) :
    legendreContFractIntegral c d z =
      ∫ t in Ioi (0 : ℝ), cexp (-(z * t)) * (t : ℂ) ^ c * (1 + (t : ℂ)) ^ d := (rfl)

private theorem norm_legendreContFractIntegrand (c : ℕ) (d z : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖cexp (-(z * t)) * (t : ℂ) ^ c * (1 + (t : ℂ)) ^ d‖ =
      t ^ c * (1 + t) ^ d.re * Real.exp (-(z.re * t)) := by
  have h1 : (1 + (t : ℂ)) = ((1 + t : ℝ) : ℂ) := by push_cast; ring
  rw [norm_mul, norm_mul, norm_exp, norm_pow, norm_real, Real.norm_of_nonneg ht, h1,
    norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  ring

private theorem continuousOn_legendreContFractIntegrand (c : ℕ) (d z : ℂ) :
    ContinuousOn (fun t : ℝ => cexp (-(z * t)) * (t : ℂ) ^ c * (1 + (t : ℂ)) ^ d) (Ici 0) := by
  refine ((by fun_prop : Continuous fun t : ℝ => cexp (-(z * t)) * (t : ℂ) ^ c).continuousOn).mul
    ((by fun_prop : Continuous fun t : ℝ => 1 + (t : ℂ)).continuousOn.cpow_const fun t ht => ?_)
  exact TauCeti.one_add_ofReal_mem_slitPlane ht

/-- For `Re z > 0`, the integrand `e^{-zt} t^c (1 + t)^d` of `K(c, d)(z)` is integrable on
`(0, ∞)`. -/
theorem integrableOn_legendreContFractIntegrand (c : ℕ) (d : ℂ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => cexp (-(z * t)) * (t : ℂ) ^ c * (1 + (t : ℂ)) ^ d) (Ioi 0) := by
  have hg : IntegrableOn (fun t : ℝ => t ^ c * (1 + t) ^ d.re * Real.exp (-(z.re * t)))
      (Ioi 0) := by
    refine integrable_of_isBigO_exp_neg (half_pos hz) ?_
      (TauCeti.isBigO_pow_mul_one_add_rpow_mul_exp c d.re hz)
    refine ((continuous_pow c).continuousOn.mul ?_).mul (by fun_prop)
    exact (by fun_prop : Continuous fun t : ℝ => 1 + t).continuousOn.rpow_const
      fun t ht => Or.inl (by have : (0 : ℝ) ≤ t := ht; positivity)
  refine hg.mono' ((continuousOn_legendreContFractIntegrand c d z).mono Ioi_subset_Ici_self
    |>.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (norm_legendreContFractIntegrand c d z (le_of_lt ht)).le

/-- **Pointwise relation** between the transforms: for `Re z > 0`,
`K(c, d) - K(c, d - 1) = K(c + 1, d - 1)`. -/
theorem legendreContFractIntegral_sub (c : ℕ) (d : ℂ) {z : ℂ} (hz : 0 < z.re) :
    legendreContFractIntegral c d z - legendreContFractIntegral c (d - 1) z =
      legendreContFractIntegral (c + 1) (d - 1) z := by
  rw [legendreContFractIntegral, legendreContFractIntegral, legendreContFractIntegral,
    ← integral_sub (integrableOn_legendreContFractIntegrand c d hz)
      (integrableOn_legendreContFractIntegrand c (d - 1) hz)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have hne : 1 + (t : ℂ) ≠ 0 := slitPlane_ne_zero (TauCeti.one_add_ofReal_mem_slitPlane ht.le)
  have hd : (1 + (t : ℂ)) ^ d = (1 + (t : ℂ)) ^ (d - 1) * (1 + (t : ℂ)) := by
    conv_lhs => rw [← sub_add_cancel d 1]
    rw [cpow_add _ _ hne, cpow_one]
  rw [hd]
  ring

/-- Integration by parts for the transforms, with the boundary value `0 ^ c` at `t = 0`: for
`Re z > 0`, `z K(c, d) = 0 ^ c + c K(c - 1, d) + d K(c, d - 1)`. This is the Laplace transform of
the derivative of `t ^ c (1 + t) ^ d`. -/
private theorem mul_legendreContFractIntegral (c : ℕ) (d : ℂ) {z : ℂ} (hz : 0 < z.re) :
    z * legendreContFractIntegral c d z =
      0 ^ c + c * legendreContFractIntegral (c - 1) d z +
        d * legendreContFractIntegral c (d - 1) z := by
  set v : ℝ → ℂ := fun t => (t : ℂ) ^ c * (1 + (t : ℂ)) ^ d
  set v' : ℝ → ℂ := fun t =>
    c * (t : ℂ) ^ (c - 1) * (1 + (t : ℂ)) ^ d + (t : ℂ) ^ c * (d * (1 + (t : ℂ)) ^ (d - 1))
  have hI (c' : ℕ) (d' : ℂ) := integrableOn_legendreContFractIntegrand c' d' hz
  have hv0 : ContinuousWithinAt v (Ici 0) 0 :=
    ((by fun_prop : Continuous fun t : ℝ => (t : ℂ) ^ c).continuousOn.mul
      ((by fun_prop : Continuous fun t : ℝ => 1 + (t : ℂ)).continuousOn.cpow_const
        fun t ht => TauCeti.one_add_ofReal_mem_slitPlane ht)) 0 (mem_Ici.2 le_rfl)
  have hv (t : ℝ) (ht : t ∈ Ioi 0) : HasDerivAt v (v' t) t := by
    have h := ((hasDerivAt_pow c (t : ℂ)).mul
      (((hasDerivAt_id (t : ℂ)).const_add 1).cpow_const (c := d)
        (TauCeti.one_add_ofReal_mem_slitPlane ht.le))).comp_ofReal
    simp only [id, mul_one] at h
    exact h
  -- The Laplace integrands of `v` and `v'` are combinations of integrands of `K`.
  have hsplit (t : ℝ) : cexp (-z * t) • v' t =
      c * (cexp (-(z * t)) * (t : ℂ) ^ (c - 1) * (1 + (t : ℂ)) ^ d) +
        d * (cexp (-(z * t)) * (t : ℂ) ^ c * (1 + (t : ℂ)) ^ (d - 1)) := by
    simp only [v', smul_eq_mul, neg_mul]
    ring
  have hL : TauCeti.HasLaplace v z (legendreContFractIntegral c d z) := by
    have heq : (fun t : ℝ => cexp (-z * t) • v t) =
        fun t : ℝ => cexp (-(z * t)) * (t : ℂ) ^ c * (1 + (t : ℂ)) ^ d := funext fun t => by
      simp only [v, smul_eq_mul, neg_mul, mul_assoc]
    exact TauCeti.HasLaplace.intro (heq ▸ hI c d) (heq ▸ rfl)
  have hB : IntegrableOn (fun t : ℝ =>
      c * (cexp (-(z * t)) * (t : ℂ) ^ (c - 1) * (1 + (t : ℂ)) ^ d) +
        d * (cexp (-(z * t)) * (t : ℂ) ^ c * (1 + (t : ℂ)) ^ (d - 1))) (Ioi 0) :=
    ((hI (c - 1) d).const_mul (c : ℂ)).add ((hI c (d - 1)).const_mul d)
  have hL' := (TauCeti.hasLaplace_deriv hv0 hv hL (funext hsplit ▸ hB)).integral_eq
  simp only [hsplit, smul_eq_mul, v] at hL'
  rw [integral_add ((hI (c - 1) d).const_mul _) ((hI c (d - 1)).const_mul _),
    integral_const_mul, integral_const_mul] at hL'
  simp only [legendreContFractIntegral, ofReal_zero, add_zero, one_cpow, mul_one] at hL' ⊢
  linear_combination -hL'

/-- **Integration by parts** for `K(0, d)`, with boundary term `1`: for `Re z > 0`,
`z K(0, d) = 1 + d K(0, d - 1)`. -/
theorem mul_legendreContFractIntegral_zero (d : ℂ) {z : ℂ} (hz : 0 < z.re) :
    z * legendreContFractIntegral 0 d z = 1 + d * legendreContFractIntegral 0 (d - 1) z := by
  simpa using mul_legendreContFractIntegral 0 d hz

/-- **Integration by parts** for `K(c + 1, d)`: for `Re z > 0`,
`z K(c + 1, d) = (c + 1) K(c, d) + d K(c + 1, d - 1)`. -/
theorem mul_legendreContFractIntegral_succ (c : ℕ) (d : ℂ) {z : ℂ} (hz : 0 < z.re) :
    z * legendreContFractIntegral (c + 1) d z =
      (c + 1) * legendreContFractIntegral c d z +
        d * legendreContFractIntegral (c + 1) (d - 1) z := by
  simpa using mul_legendreContFractIntegral (c + 1) d hz

/-! ### Partial numerators -/

/-- The 1-indexed partial numerators `aₙ` of Legendre's continued fraction DLMF 8.9.2 for
`z^{-a} e^z Γ(a, z)`: `a₁ = z⁻¹`, `a_{2k} = (k - a) z⁻¹` and `a_{2k + 1} = k z⁻¹` for `k ≥ 1`.
The value at the unused index `0` is `-a z⁻¹`. -/
def legendreContFractNum (a z : ℂ) (n : ℕ) : ℂ :=
  if n = 1 then z⁻¹ else if Even n then (((n / 2 : ℕ) : ℂ) - a) * z⁻¹ else ((n / 2 : ℕ) : ℂ) * z⁻¹

/-- The first partial numerator `a₁` of DLMF 8.9.2 is `z⁻¹`. -/
@[simp]
theorem legendreContFractNum_one (a z : ℂ) : legendreContFractNum a z 1 = z⁻¹ := by
  simp [legendreContFractNum]

/-- The even partial numerator `a_{2k}` of DLMF 8.9.2 is `(k - a) z⁻¹`. -/
@[simp]
theorem legendreContFractNum_two_mul (a z : ℂ) (k : ℕ) :
    legendreContFractNum a z (2 * k) = (k - a) * z⁻¹ := by
  simp [legendreContFractNum, show 2 * k ≠ 1 by omega]

/-- For `k ≥ 1`, the odd partial numerator `a_{2k + 1}` of DLMF 8.9.2 is `k z⁻¹`. -/
theorem legendreContFractNum_two_mul_add_one (a z : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    legendreContFractNum a z (2 * k + 1) = k * z⁻¹ := by
  have hdiv : (2 * k + 1) / 2 = k := by omega
  simp [legendreContFractNum, hdiv, show k ≠ 0 by omega]

/-- The partial numerators `aₙ` (`n ≥ 1`) of DLMF 8.9.2 are nonzero when `z ≠ 0` and `a` is not a
positive integer. -/
theorem legendreContFractNum_ne_zero {a z : ℂ} (ha : ∀ k : ℕ, a ≠ k + 1) (hz : z ≠ 0) {n : ℕ}
    (hn : 1 ≤ n) : legendreContFractNum a z n ≠ 0 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [legendreContFractNum_two_mul]
    refine mul_ne_zero (sub_ne_zero.2 fun h => ha m ?_) (inv_ne_zero hz)
    rw [← h]
    push_cast
    ring
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using hz
    · rw [legendreContFractNum_two_mul_add_one a z hk]
      exact mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (inv_ne_zero hz)

/-! ### The explicit solution and its three-term recurrence -/

/-- The explicit solution of the three-term recurrence `y(n + 1) = y(n) + aₙ y(n - 1)` of
Legendre's continued fraction DLMF 8.9.2: `f(0) = 1`, `f(2k) = (1 - a)_k z^{-k} K(k - 1, a - 1 - k)`
for `k ≥ 1`, and `f(2k + 1) = -(1 - a)_k z^{-k} K(k, a - 1 - k)` for `k ≥ 0`, where
`K = legendreContFractIntegral`. -/
def legendreContFractSol (a z : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 1 else
    (-1) ^ n * (ascPochhammer ℂ (n / 2)).eval (1 - a) * z⁻¹ ^ (n / 2) *
      legendreContFractIntegral ((n - 1) / 2) (a - 1 - (n / 2 : ℕ)) z

/-- Normalization of `legendreContFractSol` at `0`: `f(0) = 1`. -/
@[simp]
theorem legendreContFractSol_zero (a z : ℂ) : legendreContFractSol a z 0 = 1 := by
  simp [legendreContFractSol]

/-- Explicit form of `legendreContFractSol` at positive even indices:
`f(2k) = (1 - a)_k z^{-k} K(k - 1, a - 1 - k)` for `k ≥ 1`. -/
theorem legendreContFractSol_two_mul (a z : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    legendreContFractSol a z (2 * k) =
      (ascPochhammer ℂ k).eval (1 - a) * z⁻¹ ^ k *
        legendreContFractIntegral (k - 1) (a - 1 - k) z := by
  have h1 : (2 * k - 1) / 2 = k - 1 := by omega
  simp [legendreContFractSol, show 2 * k ≠ 0 by omega, h1, pow_mul]

/-- Explicit form of `legendreContFractSol` at odd indices:
`f(2k + 1) = -(1 - a)_k z^{-k} K(k, a - 1 - k)`. -/
theorem legendreContFractSol_two_mul_add_one (a z : ℂ) (k : ℕ) :
    legendreContFractSol a z (2 * k + 1) =
      -((ascPochhammer ℂ k).eval (1 - a) * z⁻¹ ^ k *
        legendreContFractIntegral k (a - 1 - k) z) := by
  have h1 : (2 * k + 1) / 2 = k := by omega
  simp [legendreContFractSol, h1, pow_succ, pow_mul]

/-- Value of `legendreContFractSol` at `1`: `f(1) = -K(0, a - 1)(z)`, so that the value
`-f(1) / f(0)` the solution assigns to Legendre's continued fraction is
`K(0, a - 1)(z) = ∫₀^∞ e^{-zt} (1 + t)^{a - 1} dt`. -/
@[simp]
theorem legendreContFractSol_one (a z : ℂ) :
    legendreContFractSol a z 1 = -legendreContFractIntegral 0 (a - 1) z := by
  simpa using legendreContFractSol_two_mul_add_one a z 0

/-- For `Re z > 0` and every complex `a`, `legendreContFractSol a z` solves the three-term
recurrence `f(n + 1) = f(n) + aₙ f(n - 1)` (`n ≥ 1`) of Legendre's continued fraction, whose
partial denominators are all `1`. -/
theorem legendreContFractSol_recurrence (a : ℂ) {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : 1 ≤ n) :
    legendreContFractSol a z (n + 1) =
      legendreContFractSol a z n +
        legendreContFractNum a z n * legendreContFractSol a z (n - 1) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hzz : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · -- `n = 2k` with `k ≥ 1`: the pointwise relation for `K(k - 1, ·)`.
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hrel := legendreContFractIntegral_sub m (a - 1 - (m + 1 : ℕ) + 1) hz
    rw [legendreContFractSol_two_mul_add_one,
      legendreContFractSol_two_mul a z (by omega), legendreContFractNum_two_mul,
      show 2 * (m + 1) - 1 = 2 * m + 1 by omega, legendreContFractSol_two_mul_add_one,
      ascPochhammer_succ_eval]
    simp only [Nat.add_sub_cancel, add_sub_cancel_right] at hrel ⊢
    push_cast at hrel ⊢
    rw [show a - 1 - ((m : ℂ) + 1) + 1 = a - 1 - m by ring] at hrel
    linear_combination (ascPochhammer ℂ m).eval (1 - a) * (1 - a + m) * z⁻¹ ^ (m + 1) * hrel
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · -- `n = 1`: integration by parts for `K(0, a - 1)`, with boundary term `1`.
      have hibp := mul_legendreContFractIntegral_zero (a - 1) hz
      rw [show 2 * 0 + 1 + 1 = 2 * 1 by rfl, legendreContFractSol_two_mul a z le_rfl]
      simp only [Nat.mul_zero, Nat.zero_add, legendreContFractSol_one, legendreContFractNum_one,
        Nat.sub_self, legendreContFractSol_zero, ascPochhammer_one, eval_X, pow_one,
        Nat.cast_one]
      linear_combination z⁻¹ * hibp - legendreContFractIntegral 0 (a - 1) z * hzz
    · -- `n = 2k + 1` with `k ≥ 1`: integration by parts for `K(k, ·)`.
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have hibp := mul_legendreContFractIntegral_succ m (a - 1 - (m + 1 : ℕ)) hz
      rw [show 2 * (m + 1) + 1 + 1 = 2 * (m + 2) by ring,
        legendreContFractSol_two_mul a z (by omega), legendreContFractSol_two_mul_add_one,
        legendreContFractNum_two_mul_add_one a z (by omega), Nat.add_sub_cancel,
        legendreContFractSol_two_mul a z (by omega), ascPochhammer_succ_eval]
      simp only [Nat.add_sub_cancel] at hibp ⊢
      push_cast at hibp ⊢
      rw [show a - 1 - ((m : ℂ) + 1) - 1 = a - 1 - ((m : ℂ) + 2) by ring] at hibp
      linear_combination (ascPochhammer ℂ (m + 1)).eval (1 - a) * z⁻¹ ^ (m + 2) * hibp -
        (ascPochhammer ℂ (m + 1)).eval (1 - a) * z⁻¹ ^ (m + 1) *
          legendreContFractIntegral (m + 1) (a - 1 - ((m : ℂ) + 1)) z * hzz

end Complex
