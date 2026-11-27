/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Analysis.Complex.VerticalStrip.Growth
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.Basic
import TauCeti.NumberTheory.LFunctions.Dirichlet.Basic
import TauCeti.NumberTheory.LFunctions.GammaFactor.Vertical

/-!
# Conductor-uniform growth of Dirichlet `L`-functions on vertical strips

Let `χ` be a primitive nonprincipal Dirichlet character of conductor `N`. On every closed vertical
strip `a ≤ Re s ≤ b` its `L`-function grows at most polynomially in the analytic conductor:
`‖L(s, χ)‖ ≤ C (N (|Im s| + 2)) ^ B`, with `C` and `B` depending only on `a` and `b`, and not on
`N`, `χ` or the height. This is the growth input for counting zeros of `L(s, χ)` in discs and for
the local expansion of `L′/L(s, χ)` with constants uniform in the conductor.

## Main results

* `TauCeti.exists_norm_LFunction_le_rpow`: the strip bound, at every height.
* `TauCeti.exists_norm_LFunction_le_rpow_of_norm_sub_le`: the same bound on closed discs of a fixed
  radius centred on a vertical line, in terms of the height of the centre.

## Implementation notes

Right of `Re s = 1/2` the partial-summation bound `‖L(s, χ)‖ ≤ N ‖s‖ / Re s`
(`DirichletCharacter.norm_LFunction_le_level_mul_norm_div_re`) suffices. Left of it, the
functional equation `DirichletCharacter.IsPrimitive.LFunction_eq_rootNumber_mul_cpow_mul` of the
uncompleted `L`-function reflects that bound, and the archimedean factor
`N ^ (1/2 - s) γ_{χ⁻¹}(1 - s) / γ_χ(s)` is at most a constant times a power of the analytic
conductor, uniformly in `N`: this is
`exists_norm_conductor_cpow_mul_dual_gammaFactor_div_strip_le_of_shift_re_nonneg` in the namespace
`TauCeti.LFunctions.AnalyticLFunctionData`, applied to the record
`TauCeti.LFunctions.dirichletData χ hχ`. No Phragmén–Lindelöf
interpolation is used, so the exponent is not the convexity exponent.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 9 (the functional equation) and
  Chapter 16.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, §5.1 and Theorem 5.6.
* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Lemma 11.2, p.113.
-/

public section

open Complex DirichletCharacter TauCeti.LFunctions

namespace TauCeti

/-- Right of `Re s = 1/2`, `‖L(s, χ)‖ ≤ 2 (M + 1) N (|Im s| + 2)` once `|Re s| ≤ M`. -/
private theorem norm_LFunction_le_of_half_le_re {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {M : ℝ} {s : ℂ} (hre : 1 / 2 ≤ s.re) (hM : |s.re| ≤ M) :
    ‖χ.LFunction s‖ ≤ 2 * (M + 1) * (N * (|s.im| + 2)) := by
  have hL := χ.norm_LFunction_le_level_mul_norm_div_re hne (s := s) (by linarith)
  have hs : ‖s‖ ≤ (M + 1) * (|s.im| + 2) := by
    nlinarith [norm_le_abs_re_add_abs_im s, abs_nonneg s.re, abs_nonneg s.im]
  calc ‖χ.LFunction s‖ ≤ N * ‖s‖ / s.re := hL
    _ ≤ N * ‖s‖ / (1 / 2) := by gcongr
    _ = 2 * (N * ‖s‖) := by ring
    _ ≤ 2 * (N * ((M + 1) * (|s.im| + 2))) := by gcongr
    _ = _ := by ring

open AnalyticLFunctionData in
/-- Left of `Re s = 1/2`, on `a ≤ Re s`, the archimedean factor
`N ^ (1/2 - s) γ_{χ⁻¹}(1 - s) / γ_χ(s)` of the functional equation is at most
`C₁ (2 (M + 3) N (|Im s| + 2)) ^ max (1/2 - a) 0` once `|Re s| ≤ M`, with `C₁` depending on `a`
alone. -/
private theorem exists_norm_cpow_mul_gammaFactor_div_le (a : ℝ) :
    ∃ C₁ > 0, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ (M : ℝ) (s : ℂ), 0 ≤ M → a ≤ s.re → s.re < 1 / 2 → |s.re| ≤ M →
        ‖(N : ℂ) ^ ((1 : ℂ) / 2 - s) * (χ⁻¹.gammaFactor (1 - s) / χ.gammaFactor s)‖ ≤
          C₁ * (2 * (M + 3) * (N * (|s.im| + 2))) ^ max (1 / 2 - a) 0 := by
  classical
  obtain ⟨C₁, hC₁, hstrip⟩ :=
    exists_norm_conductor_cpow_mul_dual_gammaFactor_div_strip_le_of_shift_re_nonneg
      a (b := 1 / 2) (by norm_num) 1 1
  refine ⟨C₁, hC₁, fun N _ χ hχ M s hM ha hre hsM ↦ ?_⟩
  set d := dirichletData χ hχ
  have hR : ∀ μ ∈ d.gammaR, ‖μ‖ ≤ 1 ∧ 0 ≤ μ.re := fun μ hμ ↦ by
    simp only [d, dirichletData_gammaR, Multiset.mem_singleton] at hμ
    split_ifs at hμ <;> simp [hμ]
  have hC : ∀ ν ∈ d.gammaC, ‖ν‖ ≤ 1 ∧ 0 ≤ ν.re := fun ν hν ↦ by simp [d] at hν
  have hfac := hstrip d (by simp [d]) hR hC s ⟨ha, hre.le⟩
  simp only [d, dirichletData_conductor, PNat.mk_coe, dirichletData_dual,
    dirichletData_gammaFactor] at hfac
  have hQ : d.analyticConductorAt s ≤ 2 * (M + 3) * (N * (|s.im| + 2)) := by
    have h := d.analyticConductorAt_le hM zero_le_one (fun μ hμ ↦ (hR μ hμ).1)
      (fun ν hν ↦ (hC ν hν).1) hsM
    simp only [d, dirichletData_degree, dirichletData_conductor, PNat.mk_coe, pow_one] at h
    refine h.trans ?_
    nlinarith [mul_nonneg (mul_nonneg (by linarith : 0 ≤ M + 3) (N.cast_nonneg : (0 : ℝ) ≤ N))
      (by linarith [abs_nonneg s.im] : 0 ≤ |s.im| + 1)]
  have hexp : 1 / 2 - s.re ≤ max (1 / 2 - a) 0 := le_max_of_le_left (by linarith)
  refine hfac.trans (mul_le_mul_of_nonneg_left ?_ hC₁.le)
  exact (Real.rpow_le_rpow_of_exponent_le (d.one_le_analyticConductorAt s) hexp).trans
    (Real.rpow_le_rpow (d.analyticConductorAt_pos s).le hQ (le_max_right _ _))

/-- **Conductor-uniform polynomial growth on vertical strips.** For real `a` and `b` there are
`C > 0` and `B ≥ 0` such that every primitive nonprincipal Dirichlet character `χ` of conductor
`N` satisfies `‖L(s, χ)‖ ≤ C (N (|Im s| + 2)) ^ B` for all `s` with `a ≤ Re s ≤ b`. The constants
depend on `a` and `b` alone. -/
theorem exists_norm_LFunction_le_rpow (a b : ℝ) :
    ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖χ.LFunction s‖ ≤ C * (N * (|s.im| + 2)) ^ B := by
  obtain ⟨C₁, hC₁, hfac⟩ := exists_norm_cpow_mul_gammaFactor_div_le a
  set M := max |a| |b|
  have hM : 0 ≤ M := (abs_nonneg a).trans (le_max_left _ _)
  set E := max (1 / 2 - a) 0
  have hE : 0 ≤ E := le_max_right _ _
  set K := 2 * (M + 3)
  set C := 2 * (M + 2) * max 1 (C₁ * K ^ E)
  have hC : 0 < C := mul_pos (by linarith) (lt_max_of_lt_left one_pos)
  refine ⟨C, E + 1, hC, by linarith, fun N _ χ hχ hne s ha hb ↦ ?_⟩
  set X : ℝ := N * (|s.im| + 2)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hX1 : 1 ≤ X := by
    simp only [X]
    nlinarith [abs_nonneg s.im]
  have hsM : |s.re| ≤ M := abs_le_max_abs_abs ha hb
  rcases le_or_gt (1 / 2) s.re with hre | hre
  · have hXB : X ≤ X ^ (E + 1) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hX1 (by linarith : (1 : ℝ) ≤ E + 1)
    calc ‖χ.LFunction s‖ ≤ 2 * (M + 1) * X := norm_LFunction_le_of_half_le_re hne hre hsM
      _ ≤ C * X := by
        have h1 : 2 * (M + 2) * X * 1 ≤ 2 * (M + 2) * X * max 1 (C₁ * K ^ E) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
        have h2 : 2 * (M + 1) * X ≤ 2 * (M + 2) * X := by nlinarith
        exact h2.trans (by simp only [C]; linarith)
      _ ≤ C * X ^ (E + 1) := by gcongr
  -- Left of `Re s = 1/2`: reflect through the functional equation.
  have hdual : ‖χ⁻¹.LFunction (1 - s)‖ ≤ 2 * (M + 2) * X := by
    have h := norm_LFunction_le_of_half_le_re (inv_ne_one.mpr hne) (M := M + 1) (s := 1 - s)
      (by simp only [sub_re, one_re]; linarith) (by
        simp only [sub_re, one_re]
        exact (abs_sub _ _).trans (by rw [abs_one]; linarith))
    simpa [X, show M + 1 + 1 = M + 2 by ring] using h
  rw [hχ.LFunction_eq_rootNumber_mul_cpow_mul hne (by linarith), mul_assoc χ.rootNumber,
    norm_mul, norm_mul, norm_rootNumber hχ, one_mul]
  calc _ ≤ C₁ * (K * X) ^ E * (2 * (M + 2) * X) :=
        mul_le_mul (hfac N χ hχ M s hM ha hre hsM) hdual (norm_nonneg _) (by positivity)
    _ = 2 * (M + 2) * (C₁ * K ^ E) * (X ^ E * X) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]; ring
    _ ≤ C * X ^ (E + 1) := by
        rw [Real.rpow_add_one (by positivity : X ≠ 0)]
        have h1 : C₁ * K ^ E ≤ max 1 (C₁ * K ^ E) := le_max_right _ _
        have h2 : 0 ≤ 2 * (M + 2) := by linarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) (by positivity)

/-- **Conductor-uniform growth on discs.** On the closed discs of a fixed radius `R` centred on a
vertical line `Re s₀ = σ₀`, every primitive nonprincipal Dirichlet character `χ` of conductor `N`
satisfies `‖L(w, χ)‖ ≤ K (N (|Im s₀| + 2)) ^ B`, with `K > 0` and `B ≥ 0` depending only on `σ₀`
and `R`. -/
theorem exists_norm_LFunction_le_rpow_of_norm_sub_le (σ₀ R : ℝ) :
    ∃ K B : ℝ, 0 < K ∧ 0 ≤ B ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → ∀ s₀ w : ℂ, s₀.re = σ₀ → ‖w - s₀‖ ≤ R →
        ‖χ.LFunction w‖ ≤ K * (N * (|s₀.im| + 2)) ^ B := by
  obtain ⟨C, B, hC, hB, h⟩ := exists_norm_LFunction_le_rpow (σ₀ - R) (σ₀ + R)
  refine ⟨C * (|R| + 1) ^ B, B, by positivity, hB, fun N _ χ hχ hne s₀ w hs₀ hw ↦ ?_⟩
  exact le_mul_rpow_mul_rpow_of_norm_sub_le (g := fun s ↦ ‖χ.LFunction s‖) hC.le N.cast_nonneg hB
    (h N χ hχ hne) hs₀ hw

end TauCeti
