/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.NumberTheory.LFunctions.Dirichlet.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Basic

/-!
# Entire completions of primitive Dirichlet records

For a nonprincipal primitive character, the analytic record has no poles, so its
entire completion equals its canonical completion at every point. The conductor
factor is everywhere analytic and nonzero and changes no zero multiplicities.
On the positive half-plane the archimedean factor is also analytic and nonzero,
so the entire completion and the ordinary continued L-function have the same
zeros with the same analytic orders.

All functions are the native continued Dirichlet functions. In particular these
comparisons do not evaluate a Dirichlet series outside its convergence domain.
The nonprincipality and half-plane hypotheses exclude the pole-clearing and
trivial-zero corrections needed in other cases.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), §10.2.
-/

public section

open Complex Filter Topology Polynomial

namespace TauCeti.LFunctions

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

/-- A nonprincipal primitive Dirichlet record has no poles. -/
theorem dirichletData_polarOrder_eq_zero (hne : χ ≠ 1) :
    (dirichletData χ hχ).polarOrder = 0 := by
  have hN : N ≠ 1 := fun h ↦ hne (hχ.eq_one_iff.mpr h)
  simp [dirichletData_polarOrder, hN]

/-- No pole-clearing polynomial is needed for a nonprincipal primitive character. -/
theorem dirichletData_polarPolynomial_of_ne_one (hne : χ ≠ 1) :
    (dirichletData χ hχ).polarPolynomial = 1 := by
  rw [AnalyticLFunctionData.polarPolynomial_def, dirichletData_polarOrder_eq_zero χ hχ hne]
  simp

/-- For a nonprincipal primitive character the removable extension retains every completed value. -/
theorem dirichletData_entireCompletion_of_ne_one (hne : χ ≠ 1) :
    (dirichletData χ hχ).entireCompletion = (dirichletData χ hχ).completed := by
  ext s
  rw [(dirichletData_hasMeromorphicContinuation χ hχ).entireCompletion_eq
    (by rw [dirichletData_polarOrder_eq_zero χ hχ hne]; rfl),
    dirichletData_polarPolynomial_of_ne_one χ hχ hne, Polynomial.eval_one, one_mul]

/-- The conductor factor changes no zero multiplicities of the completed Dirichlet function. -/
theorem analyticOrderAt_dirichletData_entireCompletion (hne : χ ≠ 1) (s : ℂ) :
    analyticOrderAt (dirichletData χ hχ).entireCompletion s =
      analyticOrderAt χ.completedLFunction s := by
  rw [dirichletData_entireCompletion_of_ne_one χ hχ hne]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hNpos : 0 < (N : ℂ).re := by exact_mod_cast NeZero.pos N
  have hc : AnalyticAt ℂ (fun z : ℂ ↦ (N : ℂ) ^ (z / 2)) s := by
    fun_prop (disch := exact Or.inl hNpos)
  have hc0 : (N : ℂ) ^ (s / 2) ≠ 0 := by simp [hN]
  rw [funext (dirichletData_completed χ hχ)]
  change analyticOrderAt ((fun z : ℂ ↦ (N : ℂ) ^ (z / 2)) * χ.completedLFunction) s = _
  have hL := (DirichletCharacter.differentiable_completedLFunction hne).analyticAt s
  rw [analyticOrderAt_mul hc hL,
    hc.analyticOrderAt_eq_zero.mpr hc0, zero_add]

/-- The entire completion and ordinary L-function have equal analytic orders
on the positive half-plane. -/
theorem analyticOrderAt_dirichletData_entireCompletion_eq_LFunction (hne : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt (dirichletData χ hχ).entireCompletion s = analyticOrderAt χ.LFunction s := by
  rw [analyticOrderAt_dirichletData_entireCompletion χ hχ hne]
  have hΓ := χ.analyticAt_gammaFactor_of_re_pos hs
  have hΓ0 := χ.gammaFactor_ne_zero_of_re_pos hs
  have he : χ.completedLFunction =ᶠ[𝓝 s] χ.gammaFactor * χ.LFunction := by
    have hpos : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re :=
      (isOpen_lt continuous_const continuous_re).mem_nhds hs
    filter_upwards [hpos] with z hz
    have hγ := χ.gammaFactor_ne_zero_of_re_pos hz
    dsimp only [Pi.mul_apply]
    rw [χ.LFunction_eq_completed_div_gammaFactor z (.inl (by rintro rfl; simp at hz))]
    exact (mul_div_cancel₀ _ hγ).symm
  rw [analyticOrderAt_congr he,
    analyticOrderAt_mul hΓ ((DirichletCharacter.differentiable_LFunction hne).analyticAt s),
    hΓ.analyticOrderAt_eq_zero.mpr hΓ0, zero_add]

/-- The entire completion and ordinary L-function have the same zeros
on the positive half-plane. -/
theorem dirichletData_entireCompletion_eq_zero_iff (hne : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    (dirichletData χ hχ).entireCompletion s = 0 ↔ χ.LFunction s = 0 := by
  have ha := (dirichletData_hasMeromorphicContinuation χ hχ).analyticAt_entireCompletion s
  rw [← ha.analyticOrderAt_ne_zero,
    analyticOrderAt_dirichletData_entireCompletion_eq_LFunction χ hχ hne hs,
    ((DirichletCharacter.differentiable_LFunction hne).analyticAt s).analyticOrderAt_ne_zero]

/-- A nonprincipal primitive Dirichlet entire completion is nonzero at the origin,
as required by Hadamard factorization. -/
theorem dirichletData_entireCompletion_zero_ne_zero (hne : χ ≠ 1) :
    (dirichletData χ hχ).entireCompletion 0 ≠ 0 := by
  have h1 : (dirichletData χ hχ).entireCompletion 1 ≠ 0 := by
    intro hz
    exact DirichletCharacter.LFunction_apply_one_ne_zero hne
      ((dirichletData_entireCompletion_eq_zero_iff χ hχ hne (s := 1) (by norm_num)).mp hz)
  intro hz
  rw [dirichletData_entireCompletion_of_ne_one χ hχ hne] at hz h1
  have hp := dirichletData_polarOrder_eq_zero χ hχ hne
  have heq := (dirichletData_hasFunctionalEquation χ hχ).completed_eq 1
    (by rw [hp]; rfl) (by rw [hp]; rfl)
  apply h1
  rw [sub_self, AnalyticLFunctionData.dual_completed_apply, map_zero, hz, map_zero,
    mul_zero] at heq
  exact heq

/-- All analytic orders of a nonprincipal primitive Dirichlet entire completion are finite. -/
theorem analyticOrderAt_dirichletData_entireCompletion_ne_top (hne : χ ≠ 1) (s : ℂ) :
    analyticOrderAt (dirichletData χ hχ).entireCompletion s ≠ ⊤ := by
  have ha : AnalyticOnNhd ℂ (dirichletData χ hχ).entireCompletion Set.univ :=
    fun z _ ↦ (dirichletData_hasMeromorphicContinuation χ hχ).analyticAt_entireCompletion z
  refine ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (x := 0) (by trivial) (by trivial) ?_
  rw [(ha 0 (by trivial)).analyticOrderAt_eq_zero.mpr
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne)]
  simp

end TauCeti.LFunctions
