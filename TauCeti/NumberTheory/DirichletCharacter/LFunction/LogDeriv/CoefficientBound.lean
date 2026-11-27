/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Taylor
import TauCeti.Analysis.Calculus.IteratedDeriv.ReciprocalPower
import TauCeti.Analysis.Calculus.LogDeriv
import TauCeti.Analysis.Complex.JensenFormula
import TauCeti.Analysis.Complex.Taylor.LogDeriv
import TauCeti.Analysis.Meromorphic.Divisor
import TauCeti.NumberTheory.DirichletCharacter.LFunction.PoleClearedGrowth

/-!
# Taylor coefficient bounds for Dirichlet logarithmic derivatives

At a centre right of the line `Re s = 1`, the coefficients of `−L′/L` consist of the
principal-character pole, the divisor-weighted reciprocal powers of nearby zeros, and an
geometrically decaying error when the divisor disc has radius greater than one. The divisor
is that of the entire function
`DirichletCharacter.entireLFunction`, so it has no spurious zero at `1` even for the principal
character. This is the local expansion used in the Deuring–Heilbronn argument.

The coefficient convention is that of `DirichletCharacter.negLogDerivTaylorCoeff`, and the
estimate uses Landau's local lemma in the form of
`AnalyticOnNhd.norm_neg_one_pow_mul_iteratedDeriv_logDeriv_div_factorial_sub_finsum_divisor_le`
and the local count uses Jensen's formula.
-/

public section

open Complex Filter MeromorphicOn Metric
open scoped Topology

namespace DirichletCharacter

open Classical in
/-- For `Re z > 1`, the Taylor coefficient of `−L′/L` in `z - s` is the coefficient of the
principal pole minus that of `logDeriv` of the pole-cleared L-function. -/
theorem negLogDerivTaylorCoeff_eq_pole_sub_entire {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {z : ℂ} (hz : 1 < z.re) (k : ℕ) :
    χ.negLogDerivTaylorCoeff k z =
      (if χ = 1 then (1 : ℂ) else 0) / (z - 1) ^ (k + 1) -
        (-1 : ℂ) ^ k * iteratedDeriv k (logDeriv χ.entireLFunction) z / k.factorial := by
  classical
  let δ : ℂ := if χ = 1 then 1 else 0
  let p (s : ℂ) : ℂ := δ / (s - 1)
  have heq : -logDeriv χ.LFunction =ᶠ[𝓝 z] p - logDeriv χ.entireLFunction := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hz] with s hs
    have hL := χ.LSeriesHasSum_twist_vonMangoldt hs
    have h := (LSeriesHasSum_iff.mp hL).2
    simpa only [Pi.neg_apply, Pi.sub_apply, Pi.mul_def, neg_neg, p, δ,
      χ.logDeriv_LFunction_eq_neg_LSeries hs] using h
  have hp : AnalyticAt ℂ p z :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr (ne_of_apply_ne re (by simpa using hz.ne')))
  have hlog := (χ.analyticAt_entireLFunction z).logDeriv
    (χ.entireLFunction_ne_zero_of_one_le_re hz.le)
  have h := heq.iteratedDeriv_eq k
  rw [iteratedDeriv_sub hp.contDiffAt hlog.contDiffAt] at h
  simp only [negLogDerivTaylorCoeff_def, h, mul_sub, sub_div]
  congr 1
  simpa only [p, δ, mul_div_assoc, Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, one_mul,
    Nat.zero_add, pow_one] using
    TauCeti.neg_one_pow_mul_iteratedDeriv_div_factorial_const_div_sub_pow 0 k δ z 1

/-- Every point counted by the divisor of the pole-cleared L-function lies strictly
left of the line `Re s = 1`. In particular the pole at `1` contributes no zero. -/
theorem re_lt_one_of_divisor_entireLFunction_ne_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {U : Set ℂ} {ρ : ℂ}
    (hρ : divisor χ.entireLFunction U ρ ≠ 0) : ρ.re < 1 := by
  by_contra! h
  exact hρ ((χ.analyticAt_entireLFunction ρ).divisor_apply_eq_zero
    (χ.entireLFunction_ne_zero_of_one_le_re h))

/-- On a closed disc of fixed radius centred on any fixed vertical line, the number of
zeros, counted with multiplicity, of the pole-cleared L-function is at most
`C log(q (|Im z| + 2))`, uniformly in the ambient level and character. -/
theorem exists_sum_divisor_entireLFunction_le (σ b : ℝ) :
    ∃ C : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {z : ℂ}, z.re = σ →
      ((∑ᶠ ρ, divisor χ.entireLFunction (closedBall z b) ρ : ℤ) : ℝ) ≤
        C * Real.log (q * (|z.im| + 2)) := by
  let r := max 1 b + |σ - 2|
  obtain ⟨D, hD⟩ := TauCeti.exists_norm_entireLFunction_le_rpow_mul one_lt_two (r + 1)
  refine ⟨D / Real.log ((r + 1) / r), fun {q} _ χ {z} hz ↦ ?_⟩
  let c : ℂ := 2 + z.im * I
  have hc : c.re = 2 := by simp [c]
  have hcim : c.im = z.im := by simp [c]
  have hr : 0 < r := by dsimp [r]; linarith [le_max_left (1 : ℝ) b, abs_nonneg (σ - 2)]
  have hsub : closedBall z b ⊆ closedBall c r := closedBall_subset_closedBall' (by
    rw [Complex.dist_of_im_eq hcim.symm, hz, hc, Real.dist_eq]
    exact add_le_add (le_max_right 1 b) le_rfl)
  have h := AnalyticOnNhd.sum_divisor_le_log_div_log_of_closedBall_subset
    (fun w _ ↦ χ.analyticAt_entireLFunction w) hr (lt_add_one r)
    (χ.entireLFunction_ne_zero_of_one_le_re (by simp [hc]))
    (fun w hw ↦ hD χ hc (mem_sphere_iff_norm.mp hw).le) hsub
  have hpos : 0 < (q : ℝ) * (|c.im| + 2) := by have := NeZero.pos q; positivity
  rw [Real.log_rpow hpos, hcim] at h
  exact h.trans_eq (by ring)

open Classical in
/-- The Taylor expansion at any centre on a fixed line `Re z = σ > 1`, with a
conductor-uniform error bounded by `C log(q (|Im z| + 2)) / a^k`. The zero terms are taken
from the divisor of the
pole-cleared L-function on `closedBall z b`, which counts the deleted Euler-factor zeros
as well. Taking `σ = a = 2` and `b = 3` gives an error `C log(q (|Im z| + 2)) 2⁻ᵏ`. -/
theorem exists_norm_negLogDerivTaylorCoeff_sub_pole_add_divisor_le_log
    {σ a b : ℝ} (hσ : 1 < σ) (ha : 0 < a) (hab : a < b) :
    ∃ C : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {z : ℂ}, z.re = σ →
      ∀ k : ℕ,
      ‖χ.negLogDerivTaylorCoeff k z - (if χ = 1 then (1 : ℂ) else 0) / (z - 1) ^ (k + 1) +
        ∑ᶠ ρ, (divisor χ.entireLFunction (closedBall z b) ρ : ℂ) / (z - ρ) ^ (k + 1)‖ ≤
          C * Real.log (q * (|z.im| + 2)) / a ^ k := by
  obtain ⟨D, hD⟩ := TauCeti.exists_norm_entireLFunction_le_rpow_mul hσ (b + 1)
  let A := 4 * (b + a) / (b - a) ^ 2 + b / (((b + 1) ^ 2 - b * a) * Real.log ((b + 1) / b))
  refine ⟨A * D, fun {q} _ χ {z} hz k ↦ ?_⟩
  have hpos : 0 < (q : ℝ) * (|z.im| + 2) := by have := NeZero.pos q; positivity
  have hz' : 1 < z.re := hz ▸ hσ
  have hlocal :=
    @AnalyticOnNhd.norm_neg_one_pow_mul_iteratedDeriv_logDeriv_div_factorial_sub_finsum_divisor_le
  have h := hlocal (f := χ.entireLFunction) (c := z) (fun w _ ↦ χ.analyticAt_entireLFunction w)
    (χ.entireLFunction_ne_zero_of_one_le_re hz'.le) ha hab (lt_add_one b)
    (fun w hw ↦ hD χ hz (mem_sphere_iff_norm.mp hw).le) k
  rw [Real.log_rpow hpos, ← mul_assoc] at h
  rw [χ.negLogDerivTaylorCoeff_eq_pole_sub_entire hz', ← norm_neg]
  convert h using 2
  ring

end DirichletCharacter
