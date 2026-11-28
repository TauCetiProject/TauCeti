/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import TauCeti.NumberTheory.LFunctions.Continued.Convexity
import TauCeti.NumberTheory.LFunctions.Continued.Dirichlet
import TauCeti.NumberTheory.LFunctions.Continued.Growth

/-!
# The convexity bound for Dirichlet `L`-functions

For every `ε > 0` there is `C` such that every primitive Dirichlet character `χ` modulo `q`
satisfies
$$\|L(1/2 + it, \chi)\| \le C\, (q (|t| + 3))^{1/4 + \varepsilon}$$
for all real `t` (`TauCeti.exists_norm_LFunction_one_half_add_mul_I_le_rpow`). The constant does
not depend on `q`, `χ` or `t`. At `q = 1` this is `ζ(1/2 + it) ≪ (|t| + 3) ^ (1/4 + ε)`.

This is the general convexity bound
`AnalyticLFunctionData.exists_norm_poleClearedContinuedL_le_analyticConductorAt_rpow` of
`TauCeti/NumberTheory/LFunctions/Continued/Convexity.lean` applied to the records
`TauCeti.LFunctions.dirichletData χ hχ`: their degree is one, their gamma shift is `0` or `1`,
and the coefficient sum `∑ ‖χ(k)‖ k ^ (-(1 + δ))` is at most `ζ(1 + δ)`. For nonprincipal `χ`
the `L`-function is entire, so no pole is cleared. For `q = 1` the pole of `ζ`
at `1` is cleared by `X - 1`, and `|1/2 + it - 1| ≥ (1 + |t|) / 4` removes the factor
`1 + |t|` this costs on the critical line.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (2004), §5.2.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed. (1986), §5.1.
-/

public section

open Complex Polynomial TauCeti.LFunctions

namespace TauCeti

section Record

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)

/-- The gamma shift of a primitive Dirichlet record is `0` or `1`. -/
private theorem dirichletData_gammaR_bound {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ μ ∈ (dirichletData χ hχ).gammaR, ‖μ‖ ≤ 1 ∧ 1 ≤ 1 + δ + μ.re := by
  classical
  intro μ hμ
  rw [dirichletData_gammaR, Multiset.mem_singleton] at hμ
  subst hμ
  split_ifs <;> norm_num <;> linarith

/-- The coefficient sum of a Dirichlet record at `σ > 1` is at most that of `ζ`. -/
private theorem tsum_norm_term_dirichletData_le {σ : ℝ} (hσ : 1 < σ) :
    ∑' k, ‖LSeries.term (dirichletData χ hχ).coeff σ k‖ ≤ ∑' k, ‖LSeries.term 1 σ k‖ := by
  have hle : ∀ k, ‖LSeries.term (dirichletData χ hχ).coeff σ k‖ ≤ ‖LSeries.term 1 σ k‖ :=
    fun k ↦ LSeries.norm_term_le _ <| by
      rcases eq_or_ne k 0 with rfl | hk
      · simp
      · rw [dirichletData_coeff_of_ne_zero χ hχ hk, Pi.one_apply, norm_one]
        exact χ.norm_le_one _
  have hsum : Summable fun k ↦ ‖LSeries.term 1 σ k‖ :=
    (LSeriesSummable_one_iff.mpr (by simpa using hσ)).norm
  exact (hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle).tsum_le_tsum hle hsum

/-- On the critical line the analytic conductor of a primitive Dirichlet record is at most
`2 q (|t| + 3)`. -/
private theorem analyticConductorAt_dirichletData_le (t : ℝ) :
    (dirichletData χ hχ).analyticConductorAt (1 / 2 + t * I) ≤ 2 * ((q : ℝ) * (|t| + 3)) := by
  classical
  have ha : ∀ a : ℂ, ‖a‖ ≤ 1 → ‖1 / 2 + t * I + a‖ + 3 ≤ 2 * (|t| + 3) := fun a ha ↦ by
    have h : ‖1 / 2 + t * I + a‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖(t : ℂ) * I‖ + ‖a‖ := norm_add₃_le
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    have ht : ‖(t : ℂ) * I‖ = |t| := by simp
    linarith [abs_nonneg t]
  simp only [AnalyticLFunctionData.analyticConductorAt_def, dirichletData_conductor,
    dirichletData_gammaR, dirichletData_gammaC, Multiset.map_singleton, Multiset.prod_singleton,
    Multiset.map_zero, Multiset.prod_zero, mul_one, PNat.mk_coe]
  split_ifs
  · nlinarith [ha 0 (by simp)]
  · nlinarith [ha 1 (by simp)]

end Record

/-- The last step: a bound `C' S 𝔮 ^ e` with `C' ≤ C`, `S ≤ Z` and `𝔮 ≤ 2 Q` is at most
`C Z 2 ^ e Q ^ e`. -/
private theorem le_of_le_mul_mul_rpow {x C' C S Z 𝔮 Q e : ℝ} (hC' : 0 ≤ C') (hC : C' ≤ C)
    (hS₀ : 0 ≤ S) (hS : S ≤ Z) (h𝔮₀ : 0 ≤ 𝔮) (h𝔮 : 𝔮 ≤ 2 * Q) (he : 0 ≤ e)
    (hx : x ≤ C' * S * 𝔮 ^ e) : x ≤ C * Z * 2 ^ e * Q ^ e := by
  have hQ : 0 ≤ Q := by linarith
  have hC₀ : 0 ≤ C := hC'.trans hC
  have hZ : 0 ≤ Z := hS₀.trans hS
  refine hx.trans ?_
  calc C' * S * 𝔮 ^ e ≤ C * Z * (2 * Q) ^ e := by
        gcongr
    _ = C * Z * 2 ^ e * Q ^ e := by rw [Real.mul_rpow zero_le_two hQ]; ring

/-- The critical-line exponent `(1/2 + δ) (1 + δ - 1/2) / (1 + 2 δ)` is `1/4 + δ/2`. -/
private theorem convexity_exponent_one_half (δ : ℝ) :
    (1 / 2 + δ) * (1 + δ - 1 / 2) / (1 + 2 * δ) = 1 / 4 + δ / 2 := by
  rcases eq_or_ne (1 + 2 * δ) 0 with h | h
  · obtain rfl : δ = -1 / 2 := by linarith
    norm_num
  · field_simp
    ring

/-- On the critical line `|1/2 + it - 1| ≥ (1 + |t|) / 4`, so a bound
`|s - 1| x ≤ A (1 + |Im s|) B` gives `x ≤ 4 A B`. -/
private theorem le_mul_of_norm_sub_one_mul_le {s : ℂ} (hs : s.re = 1 / 2) {x A B : ℝ}
    (hx₀ : 0 ≤ x) (hx : ‖s - 1‖ * x ≤ A * (1 + |s.im|) * B) :
    x ≤ 4 * A * B := by
  have h1 : |s.im| ≤ ‖s - 1‖ := by simpa using abs_im_le_norm (s - 1)
  have h2 : 1 / 2 ≤ ‖s - 1‖ := by
    have h := abs_re_le_norm (s - 1)
    norm_num [hs] at h
    linarith
  refine le_of_mul_le_mul_left ?_ (by positivity : 0 < 1 + |s.im|)
  calc (1 + |s.im|) * x ≤ 4 * (‖s - 1‖ * x) := by nlinarith
    _ ≤ 4 * (A * (1 + |s.im|) * B) := by gcongr
    _ = (1 + |s.im|) * (4 * A * B) := by ring

/-- **The convexity bound for Dirichlet `L`-functions, uniformly in the modulus.** For every
`ε > 0` there is `C` such that every primitive Dirichlet character `χ` modulo `q` satisfies
`‖L(1/2 + it, χ)‖ ≤ C (q (|t| + 3)) ^ (1/4 + ε)` for all real `t`. At `q = 1` this is
`ζ(1/2 + it) ≪ (|t| + 3) ^ (1/4 + ε)`. -/
theorem exists_norm_LFunction_one_half_add_mul_I_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ t : ℝ,
      ‖χ.LFunction (1 / 2 + t * I)‖ ≤ C * ((q : ℝ) * (|t| + 3)) ^ (1 / 4 + ε) := by
  have hδ : 0 < 2 * ε := by positivity
  obtain ⟨C₀, hC₀, h₀⟩ :=
    AnalyticLFunctionData.exists_norm_poleClearedContinuedL_le_analyticConductorAt_rpow
      hδ one_pos 1 1 (X - C 1)
  obtain ⟨C₁, hC₁, h₁⟩ :=
    AnalyticLFunctionData.exists_norm_continuedL_one_half_add_mul_I_le_analyticConductorAt_rpow
      hδ one_pos 1 1
  refine ⟨max (4 * C₀) C₁ * (∑' k, ‖LSeries.term 1 (1 + 2 * ε : ℝ) k‖) * 2 ^ (1 / 4 + ε),
    fun q _ χ hχ t ↦ ?_⟩
  have hR := dirichletData_gammaR_bound hχ hδ.le
  have hC : ∀ ν ∈ (dirichletData χ hχ).gammaC, ‖ν‖ ≤ 1 ∧ 1 ≤ 1 + 2 * ε + ν.re := by simp
  have hS := tsum_norm_term_dirichletData_le hχ (σ := 1 + 2 * ε) (by linarith)
  have hS₀ : 0 ≤ ∑' k, ‖LSeries.term (dirichletData χ hχ).coeff (1 + 2 * ε : ℝ) k‖ :=
    tsum_nonneg fun _ ↦ norm_nonneg _
  have h𝔮 := analyticConductorAt_dirichletData_le hχ t
  have h𝔮₀ := ((dirichletData χ hχ).analyticConductorAt_pos (1 / 2 + t * I)).le
  have he : (1 / 4 + 2 * ε / 2) = 1 / 4 + ε := by ring
  have hD := dirichletData_hasDirichletAgreement χ hχ
  have hfe := dirichletData_hasFunctionalEquation χ hχ
  have hfin := dirichletData_isFiniteOrder χ hχ
  by_cases hq : q = 1
  · subst hq
    set s : ℂ := 1 / 2 + t * I
    have hs : s.re = 1 / 2 := by simp [s]
    have hP : (X - C 1 : ℂ[X]).eval s ≠ 0 := fun h ↦ by
      have := congrArg re h
      norm_num [s] at this
    have hbound := h₀ (dirichletData χ hχ) (dirichletData_degree χ hχ) hR hC hD hfe hfin
      (fun z _ ↦ by
        rw [dirichletData_modOne]
        exact riemannZetaData_continuedL_cleared_by_X_sub_one z)
      s (by rw [hs]; constructor <;> linarith)
    rw [AnalyticLFunctionData.poleClearedContinuedL_eq_of_eval_ne_zero hP,
      dirichletData_continuedL, norm_mul, hs, convexity_exponent_one_half, he, eval_sub,
      eval_X, eval_C, natDegree_X_sub_C, pow_one] at hbound
    have hx := le_mul_of_norm_sub_one_mul_le hs (norm_nonneg _) hbound
    exact le_of_le_mul_mul_rpow (by positivity) (le_max_left _ _) hS₀ hS h𝔮₀ h𝔮 (by positivity)
      (by simpa only [mul_assoc] using hx)
  · have hne : χ ≠ 1 := mt hχ.eq_one_iff.mp hq
    have ha : ∀ z : ℂ, z.re ∈ Set.Icc (-(2 * ε)) (1 + 2 * ε) →
        AnalyticAt ℂ (dirichletData χ hχ).continuedL z := fun z _ ↦ by
      rw [dirichletData_continuedL]
      exact (DirichletCharacter.differentiable_LFunction hne).analyticAt z
    have hbound := h₁ (dirichletData χ hχ) (dirichletData_degree χ hχ) hR hC hD hfe hfin ha t
    rw [dirichletData_continuedL, he] at hbound
    exact le_of_le_mul_mul_rpow hC₁.le (le_max_right _ _) hS₀ hS h𝔮₀ h𝔮 (by positivity) hbound

end TauCeti
