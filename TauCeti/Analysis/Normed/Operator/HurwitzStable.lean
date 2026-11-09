/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Normed.Algebra.Exponential
public import TauCeti.Analysis.Normed.Module.Complexification
public import TauCeti.Analysis.Normed.Operator.Exponential
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-!
# Exponential decay of Hurwitz-stable operators

An operator on a finite-dimensional space is *Hurwitz stable* when all its complex eigenvalues lie
in the open left half-plane. The flow `t ↦ exp (t • T)` of such an operator then decays
exponentially: `‖exp (t • T)‖ ≤ K * Real.exp (-α * t)` for `t ≥ 0`, with `α > 0`. This is the
linear estimate behind exponential dichotomies of hyperbolic equilibria.

Over `ℂ` the eigenvalue condition is stated on the spectrum
(`ContinuousLinearMap.exists_norm_exp_smul_le_of_forall_mem_spectrum_re_neg`). Every point of the
spectrum of `exp T` is `exp z` for an eigenvalue `z` of `T`
(`ContinuousLinearMap.exists_mem_spectrum_eq_exp_of_mem_spectrum_exp`). Hence the spectral radius
of `exp T` is less than one, Gelfand's formula gives some power `exp T ^ n` of norm less than one,
and the semigroup law spreads this contraction over all times
(`TauCeti.exists_norm_exp_smul_le_of_norm_exp_smul_lt_one`).

Over `ℝ` the complex eigenvalues are among the complex roots of any polynomial annihilating the
operator, and the condition is stated that way
(`ContinuousLinearMap.exists_norm_exp_smul_le_of_aeval_eq_zero`): if `p(B) = 0` for a real
polynomial `p` whose complex roots all have negative real part, the flow of `B` decays
exponentially. The proof passes to the complexification `B.complexify`, which is annihilated by
`p` and has the same operator norms, and applies the complex result.

If `p(A) q(A) = 0` with `u * p + v * q = 1`, then `(v * q)(A)` is the projection onto
`ker p(A)` along `ker q(A)`, and the flow of `A` decays exponentially on its range as soon as the
complex roots of `p` have negative real part, whatever the roots of `q`
(`ContinuousLinearMap.exists_norm_exp_smul_mul_aeval_le`). This is the forward half of the
exponential dichotomy of a hyperbolic operator.

## References

* M. W. Hirsch, S. Smale and R. L. Devaney, *Differential Equations, Dynamical Systems, and an
  Introduction to Chaos*, third edition, Academic Press, 2013, Chapter 7.
-/

public section

open NormedSpace Polynomial

namespace ContinuousLinearMap

section Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- **Exponential decay for a Hurwitz-stable complex operator.** If every point of the spectrum of
an operator `T` on a finite-dimensional complex space has negative real part, then
`‖exp (t • T)‖ ≤ K * Real.exp (-α * t)` for all `t ≥ 0`, with constants `K` and `α > 0`. -/
theorem exists_norm_exp_smul_le_of_forall_mem_spectrum_re_neg (T : F →L[ℂ] F)
    (h : ∀ z ∈ spectrum ℂ T, z.re < 0) :
    ∃ K α : ℝ, 0 < α ∧ ∀ t : ℝ, 0 ≤ t → ‖exp (t • T)‖ ≤ K * Real.exp (-α * t) := by
  rcases subsingleton_or_nontrivial F with hF | hF
  · refine ⟨0, 1, one_pos, fun t _ ↦ ?_⟩
    rw [Subsingleton.elim (exp (t • T)) 0, norm_zero, zero_mul]
  have hρ : spectralRadius ℂ (exp T) < 1 := by
    have := spectrum.spectralRadius_lt_of_forall_lt (exp T) (r := 1) fun μ hμ ↦ by
      obtain ⟨z, hz, rfl⟩ := T.exists_mem_spectrum_eq_exp_of_mem_spectrum_exp hμ
      rw [← Complex.exp_eq_exp_ℂ, ← NNReal.coe_lt_coe]
      simpa [Complex.norm_exp] using h z hz
    simpa using this
  -- By Gelfand's formula some power `exp T ^ n = exp (n • T)` has norm less than one.
  obtain ⟨n, hn, hn0⟩ := ((spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius
    (exp T)).eventually (gt_mem_nhds hρ)).and (Filter.eventually_gt_atTop 0) |>.exists
  have hlt : ‖exp ((n : ℝ) • T)‖ < 1 := by
    let +nondep : NormedAlgebra ℚ (F →L[ℂ] F) := .restrictScalars ℚ ℂ _
    have h1 : (‖exp T ^ n‖₊ : ENNReal) < 1 := by
      by_contra hge
      exact (ENNReal.one_le_rpow (le_of_not_gt hge)
        (one_div_pos.mpr (Nat.cast_pos.mpr hn0))).not_gt hn
    rw [Nat.cast_smul_eq_nsmul, exp_nsmul]
    exact_mod_cast h1
  exact TauCeti.exists_norm_exp_smul_le_of_norm_exp_smul_lt_one T (Nat.cast_pos.mpr hn0) hlt

end Complex

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Exponential decay for a Hurwitz-stable real operator.** If an operator `B` on a
finite-dimensional real space is annihilated by a real polynomial `p` whose complex roots all have
negative real part, then `‖exp (t • B)‖ ≤ K * Real.exp (-α * t)` for all `t ≥ 0`, with constants
`K` and `α > 0`. -/
theorem exists_norm_exp_smul_le_of_aeval_eq_zero (B : E →L[ℝ] E) {p : ℝ[X]}
    (hp : aeval B p = 0) (hroots : ∀ z : ℂ, aeval z p = 0 → z.re < 0) :
    ∃ K α : ℝ, 0 < α ∧ ∀ t : ℝ, 0 ≤ t → ‖exp (t • B)‖ ≤ K * Real.exp (-α * t) := by
  have : FiniteDimensional ℝ (TauCeti.Complexification E) :=
    (TauCeti.Complexification.equivProd E).toLinearEquiv.symm.finiteDimensional
  have : FiniteDimensional ℂ (TauCeti.Complexification E) :=
    .of_restrictScalars_finite ℝ ℂ _
  -- The complexification of `B` is annihilated by `p`, so its spectrum consists of roots of `p`.
  have hpC : aeval B.complexify (p.map (algebraMap ℝ ℂ)) = 0 := by
    rw [aeval_map_algebraMap, ← complexifyAlgHom_apply, aeval_algHom_apply, hp, map_zero]
  obtain ⟨K, α, hα, hK⟩ := exists_norm_exp_smul_le_of_forall_mem_spectrum_re_neg B.complexify
    fun z hz ↦ hroots z <| by
      rcases subsingleton_or_nontrivial (TauCeti.Complexification E →L[ℂ]
        TauCeti.Complexification E) with _ | _
      · rw [spectrum.of_subsingleton] at hz
        exact hz.elim
      have h := spectrum.subset_polynomial_aeval B.complexify (p.map (algebraMap ℝ ℂ))
        ⟨z, hz, rfl⟩
      rw [hpC, spectrum.zero_eq, Set.mem_singleton_iff] at h
      simpa only [eval_map_algebraMap] using h
  -- Complexification preserves operator norms and commutes with the exponential.
  refine ⟨K, α, hα, fun t ht ↦ ?_⟩
  have hmap : (exp (t • B)).complexify = exp (t • B.complexify) := by
    let +nondep : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ _
    let +nondep : NormedAlgebra ℚ (TauCeti.Complexification E →L[ℂ]
      TauCeti.Complexification E) := .restrictScalars ℚ ℂ _
    have hc : Continuous (complexifyAlgHom E) := (complexifyₗᵢ E E).continuous.congr fun _ ↦ by simp
    rw [← complexifyAlgHom_apply, map_exp _ hc, map_smul, complexifyAlgHom_apply]
  rw [← norm_complexify, hmap]
  exact hK t ht

/-- **Exponential decay on a stable polynomial summand.** If `p(A) q(A) = 0` with
`u * p + v * q = 1` and the complex roots of `p` have negative real part, then the flow of `A`
decays exponentially on the range of `(v * q)(A)`, the projection onto `ker p(A)` along
`ker q(A)`. -/
theorem exists_norm_exp_smul_mul_aeval_le {A : E →L[ℝ] E} {p q u v : ℝ[X]}
    (hpq : aeval A (p * q) = 0) (huv : u * p + v * q = 1)
    (hp : ∀ z : ℂ, aeval z p = 0 → z.re < 0) :
    ∃ K α : ℝ, 0 < α ∧ ∀ t : ℝ, 0 ≤ t →
      ‖exp (t • A) * aeval A (v * q)‖ ≤ K * Real.exp (-α * t) := by
  -- `B = s(A)` acts as `A` on `ker p(A)` and as `-1` on `ker q(A)`.
  set s : ℝ[X] := X * (v * q) - u * p
  have hsX : s - X = -((X + 1) * u * p) := by linear_combination X * huv
  have hs1 : s + 1 = (X + 1) * (v * q) := by linear_combination -huv
  have hps : p ∣ p.comp s := by
    have h := sub_dvd_eval_sub s X (p.map C)
    rw [eval_map, eval_map, eval₂_C_X, ← algebraMap_eq, ← aeval_def, ← comp_eq_aeval] at h
    have hp' : p ∣ s - X := ⟨-((X + 1) * u), by rw [hsX]; ring⟩
    simpa using (hp'.trans h).add (dvd_refl p)
  have hB : aeval (aeval A s) (p * (X + 1)) = 0 := by
    rw [← aeval_comp, Polynomial.mul_comp, Polynomial.add_comp, Polynomial.X_comp,
      Polynomial.one_comp, hs1]
    refine aeval_eq_zero_of_dvd_aeval_eq_zero ?_ hpq
    exact mul_dvd_mul hps ⟨(X + 1) * v, by ring⟩
  obtain ⟨K, α, hα, hK⟩ := exists_norm_exp_smul_le_of_aeval_eq_zero (aeval A s) hB
    fun z hz ↦ by
      rw [map_mul, mul_eq_zero] at hz
      rcases hz with hz | hz
      · exact hp z hz
      · simp only [map_add, aeval_X, map_one, add_eq_zero_iff_eq_neg] at hz
        simp [hz]
  refine ⟨K * ‖aeval A (v * q)‖, α, hα, fun t ht ↦ ?_⟩
  -- `s(A) = A + D` with `D` commuting with `A` and killing the range of `(v * q)(A)`.
  set D := aeval A (s - X)
  have hDP : t • D * aeval A (v * q) = 0 := by
    rw [smul_mul_assoc, ← map_mul, aeval_eq_zero_of_dvd_aeval_eq_zero _ hpq, smul_zero]
    exact ⟨-((X + 1) * u * v), by rw [hsX]; ring⟩
  have hsD : aeval A s = A + D := by
    simp only [D, map_sub, aeval_X]
    abel
  have hAD : Commute A D := by simpa using (Commute.all (X : ℝ[X]) (s - X)).map (aeval A)
  have hsplit : exp (t • aeval A s) = exp (t • A) * exp (t • D) := by
    let +nondep : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ _
    rw [hsD, smul_add, exp_add_of_commute ((hAD.smul_left t).smul_right t)]
  have hexp : exp (t • A) * aeval A (v * q) = exp (t • aeval A s) * aeval A (v * q) := by
    rw [hsplit, mul_assoc]
    congr 1
    ext z
    rw [mul_apply_eq_comp, (t • D).exp_apply_of_apply_eq_smul (μ := 0), exp_zero, one_smul]
    rw [zero_smul, ← mul_apply_eq_comp, hDP, zero_apply]
  rw [hexp]
  calc ‖exp (t • aeval A s) * aeval A (v * q)‖
      ≤ ‖exp (t • aeval A s)‖ * ‖aeval A (v * q)‖ := norm_mul_le _ _
    _ ≤ K * Real.exp (-α * t) * ‖aeval A (v * q)‖ := by gcongr; exact hK t ht
    _ = K * ‖aeval A (v * q)‖ * Real.exp (-α * t) := by ring

end Real

end ContinuousLinearMap
