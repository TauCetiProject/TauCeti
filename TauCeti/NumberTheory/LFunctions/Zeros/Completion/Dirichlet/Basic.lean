/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.NumberTheory.LFunctions.Dirichlet.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Basic

import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic

/-!
# Entire completions of primitive Dirichlet records

For a nonprincipal primitive character, the analytic record has no poles, so its
entire completion equals its canonical completion at every point. The conductor
factor is everywhere analytic and nonzero and changes no zero multiplicities.
On the positive half-plane the archimedean factor is also analytic and nonzero,
so the entire completion and the ordinary continued L-function have the same
zeros with the same analytic orders.

At conductor `N = 1`, `dirichletData χ hχ` recovers `riemannZetaData`, whose
entire completion is `zetaEntireCompletion`. Every primitive Dirichlet entire
completion therefore is nonzero at the origin, has finite analytic orders
everywhere, and satisfies the functional equation
`Λ₀(χ)(1 - s) = ε(χ) Λ₀(χ⁻¹)(s)`, the reflection `Λ₀(χ⁻¹)(s) = conj (Λ₀(χ)(conj s))`,
and their composite `Λ₀(χ)(1 - s) = ε(χ) conj (Λ₀(χ)(conj s))`.
A real character has the same analytic record as its inverse.

All functions are the native continued Dirichlet functions. In particular these
comparisons do not evaluate a Dirichlet series outside its convergence domain.
The nonprincipality and half-plane hypotheses on the direct `completedLFunction`
and `LFunction` comparisons exclude the pole-clearing and trivial-zero
corrections needed in other cases.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), §10.2.
-/

public section

open Complex ComplexConjugate Filter Topology Polynomial

namespace TauCeti.LFunctions

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

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
    (by simp only [dirichletData_polarOrder_eq_zero χ hχ hne, Finsupp.zero_apply]),
    dirichletData_polarPolynomial_of_ne_one χ hχ hne, Polynomial.eval_one, one_mul]

/-- The functional equation of a primitive Dirichlet entire completion, against the inverse
character. -/
theorem dirichletData_entireCompletion_one_sub (s : ℂ) :
    (dirichletData χ hχ).entireCompletion (1 - s) =
      χ.rootNumber * (dirichletData χ⁻¹ hχ.inv).entireCompletion s := by
  have hdeg : (-1 : ℂ) ^ (dirichletData χ hχ).polarPolynomial.natDegree = 1 := by
    by_cases hN : N = 1
    · subst N
      rw [dirichletData_modOne, riemannZetaData_polarPolynomial, ← C_1,
        natDegree_mul X_ne_zero (X_sub_C_ne_zero (1 : ℂ)), natDegree_X, natDegree_X_sub_C]
      norm_num
    · rw [dirichletData_polarPolynomial_of_ne_one χ hχ (mt hχ.eq_one_iff.mp hN),
        natDegree_one, pow_zero]
  have h := (dirichletData_hasFunctionalEquation χ hχ).entireCompletion_one_sub
    (dirichletData_hasMeromorphicContinuation χ hχ) s
  simpa only [hdeg, one_mul, dirichletData_rootNumber, dirichletData_dual] using h

/-- Conjugation exchanges the entire completions of a primitive character and its inverse. -/
theorem dirichletData_entireCompletion_inv_conj (s : ℂ) :
    (dirichletData χ⁻¹ hχ.inv).entireCompletion s =
      conj ((dirichletData χ hχ).entireCompletion (conj s)) := by
  simpa only [dirichletData_dual] using
    (dirichletData_hasMeromorphicContinuation χ hχ).dual_entireCompletion s

/-- Combined functional and conjugation symmetry of a primitive Dirichlet entire completion. -/
theorem dirichletData_entireCompletion_one_sub_eq_rootNumber_mul_conj_conj (s : ℂ) :
    (dirichletData χ hχ).entireCompletion (1 - s) =
      χ.rootNumber * conj ((dirichletData χ hχ).entireCompletion (conj s)) := by
  rw [dirichletData_entireCompletion_one_sub χ hχ, dirichletData_entireCompletion_inv_conj χ hχ]

/-- For a real character, the inverse character has the same analytic record. Mathlib's
`MulChar.IsQuadratic.inv` supplies the hypothesis for quadratic characters. -/
theorem dirichletData_inv_of_inv_eq (hreal : χ⁻¹ = χ) :
    dirichletData χ⁻¹ hχ.inv = dirichletData χ hχ := by
  -- `hχ.inv` mentions `χ⁻¹`, so generalize it before rewriting `χ⁻¹` to `χ`.
  generalize hχ.inv = hχ'
  revert hχ'
  rw [hreal]
  exact fun _ ↦ rfl

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
  rw [← Pi.mul_def]
  have hL := (DirichletCharacter.differentiable_completedLFunction hne).analyticAt s
  rw [analyticOrderAt_mul hc hL,
    hc.analyticOrderAt_eq_zero.mpr hc0, zero_add]

/-- The entire completion and ordinary L-function have equal analytic orders
on the positive half-plane. -/
theorem analyticOrderAt_dirichletData_entireCompletion_eq_LFunction (hne : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt (dirichletData χ hχ).entireCompletion s = analyticOrderAt χ.LFunction s := by
  rw [analyticOrderAt_dirichletData_entireCompletion χ hχ hne,
    χ.analyticOrderAt_completedLFunction hs (.inr hne)]

/-- The conductor factor changes no natural zero multiplicities of the completed Dirichlet
function. -/
theorem analyticOrderNatAt_dirichletData_entireCompletion (hne : χ ≠ 1) (s : ℂ) :
    analyticOrderNatAt (dirichletData χ hχ).entireCompletion s =
      analyticOrderNatAt χ.completedLFunction s :=
  congrArg ENat.toNat (analyticOrderAt_dirichletData_entireCompletion χ hχ hne s)

/-- The entire completion and ordinary L-function have equal natural zero multiplicities on the
positive half-plane. -/
theorem analyticOrderNatAt_dirichletData_entireCompletion_eq_LFunction (hne : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    analyticOrderNatAt (dirichletData χ hχ).entireCompletion s =
      analyticOrderNatAt χ.LFunction s :=
  congrArg ENat.toNat (analyticOrderAt_dirichletData_entireCompletion_eq_LFunction χ hχ hne hs)

/-- The entire completion and ordinary L-function have the same zeros
on the positive half-plane. -/
theorem dirichletData_entireCompletion_eq_zero_iff (hne : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    (dirichletData χ hχ).entireCompletion s = 0 ↔ χ.LFunction s = 0 := by
  have ha := (dirichletData_hasMeromorphicContinuation χ hχ).analyticAt_entireCompletion s
  rw [← ha.analyticOrderAt_ne_zero,
    analyticOrderAt_dirichletData_entireCompletion_eq_LFunction χ hχ hne hs,
    ((DirichletCharacter.differentiable_LFunction hne).analyticAt s).analyticOrderAt_ne_zero]

/-- Every primitive Dirichlet entire completion is nonzero at the origin,
as required by Hadamard factorization. -/
theorem dirichletData_entireCompletion_zero_ne_zero :
    (dirichletData χ hχ).entireCompletion 0 ≠ 0 := by
  by_cases hN : N = 1
  · subst N
    simp [dirichletData_modOne]
  · have hne : χ ≠ 1 := mt hχ.eq_one_iff.mp hN
    have h1 : (dirichletData χ hχ).entireCompletion 1 ≠ 0 := fun hz ↦
      DirichletCharacter.LFunction_apply_one_ne_zero hne
        ((dirichletData_entireCompletion_eq_zero_iff χ hχ hne (s := 1) (by norm_num)).mp hz)
    have h01 := (dirichletData_hasFunctionalEquation χ hχ).entireCompletion_eq_zero_iff_one_sub_conj
      (dirichletData_hasMeromorphicContinuation χ hχ) 0
    exact h01.not.mp (by simpa using h1)

/-- All analytic orders of a primitive Dirichlet entire completion are finite. -/
theorem analyticOrderAt_dirichletData_entireCompletion_ne_top (s : ℂ) :
    analyticOrderAt (dirichletData χ hχ).entireCompletion s ≠ ⊤ := by
  have ha : AnalyticOnNhd ℂ (dirichletData χ hχ).entireCompletion Set.univ :=
    fun z _ ↦ (dirichletData_hasMeromorphicContinuation χ hχ).analyticAt_entireCompletion z
  refine ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (x := 0) (by trivial) (by trivial) ?_
  rw [(ha 0 (by trivial)).analyticOrderAt_eq_zero.mpr
    (dirichletData_entireCompletion_zero_ne_zero χ hχ)]
  simp

/-- For a nonprincipal primitive character the entire completion is the conductor factor times
Mathlib's completed function. -/
theorem dirichletData_entireCompletion_eq (hne : χ ≠ 1) :
    (dirichletData χ hχ).entireCompletion =
      fun s ↦ (N : ℂ) ^ (s / 2) * χ.completedLFunction s := by
  rw [dirichletData_entireCompletion_of_ne_one χ hχ hne]
  exact funext (dirichletData_completed χ hχ)

end TauCeti.LFunctions

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- All analytic orders of a nonprincipal continued Dirichlet L-function are finite. -/
theorem analyticOrderAt_LFunction_ne_top (hne : χ ≠ 1) (s : ℂ) :
    analyticOrderAt χ.LFunction s ≠ ⊤ := by
  have ha : AnalyticOnNhd ℂ χ.LFunction Set.univ :=
    fun z _ ↦ (differentiable_LFunction hne).analyticAt z
  refine ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (x := 1) (by trivial) (by trivial) ?_
  rw [(ha 1 (by trivial)).analyticOrderAt_eq_zero.mpr (LFunction_apply_one_ne_zero hne)]
  simp

/-- At any point, the meromorphic order of a nonprincipal continued Dirichlet L-function is the
cast of its natural analytic order. -/
theorem meromorphicOrderAt_LFunction_eq_analyticOrderNatAt (hne : χ ≠ 1) (s : ℂ) :
    meromorphicOrderAt χ.LFunction s = (analyticOrderNatAt χ.LFunction s : ℤ) := by
  have haL := (differentiable_LFunction hne).analyticAt s
  rw [haL.meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (χ.analyticOrderAt_LFunction_ne_top hne s)]
  rfl

/-- A nonprincipal continued Dirichlet L-function vanishes at `s` if and only if its natural
analytic order at `s` is at least `1`. -/
theorem LFunction_eq_zero_iff_one_le_analyticOrderNatAt (hne : χ ≠ 1) (s : ℂ) :
    χ.LFunction s = 0 ↔ 1 ≤ analyticOrderNatAt χ.LFunction s := by
  have haL := (differentiable_LFunction hne).analyticAt s
  rw [← haL.analyticOrderAt_ne_zero,
    ← Nat.cast_analyticOrderNatAt (χ.analyticOrderAt_LFunction_ne_top hne s)]
  exact_mod_cast Nat.one_le_iff_ne_zero.symm

/-- A nonprincipal continued Dirichlet L-function has positive meromorphic order at `s` if and only
if it vanishes at `s`. -/
theorem pos_meromorphicOrderAt_LFunction_iff (hne : χ ≠ 1) (s : ℂ) :
    0 < meromorphicOrderAt χ.LFunction s ↔ χ.LFunction s = 0 := by
  rw [χ.meromorphicOrderAt_LFunction_eq_analyticOrderNatAt hne s,
    χ.LFunction_eq_zero_iff_one_le_analyticOrderNatAt hne s]
  exact_mod_cast Nat.pos_iff_ne_zero.trans Nat.one_le_iff_ne_zero.symm

/-- A nonprincipal continued Dirichlet L-function has meromorphic order `1` at `s` if and only if
its natural analytic order at `s` is `1`. -/
theorem meromorphicOrderAt_LFunction_eq_one_iff (hne : χ ≠ 1) (s : ℂ) :
    meromorphicOrderAt χ.LFunction s = 1 ↔ analyticOrderNatAt χ.LFunction s = 1 := by
  rw [χ.meromorphicOrderAt_LFunction_eq_analyticOrderNatAt hne s]
  exact_mod_cast Iff.rfl

end DirichletCharacter
