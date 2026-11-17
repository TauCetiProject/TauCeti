/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.DirichletCharacter.Conductor
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.NumberTheory.DirichletCharacter.Primitive
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta

/-!
# Meromorphicity, analyticity, and level changes for Dirichlet L-functions

This file packages basic analytic regularity and germ-level comparison lemmas for Mathlib's
continued Dirichlet L-function `DirichletCharacter.LFunction`:

* every Dirichlet L-function is meromorphic on `ℂ` (entire when `χ ≠ 1`, and agreeing away from
  `s = 1` with the product of `∏ p ∈ N.primeFactors, (1 - p ^ (-s))` and `riemannZeta` when
  `χ = 1`);
* `χ.LFunction` is analytic at `s` whenever `χ ≠ 1 ∨ s ≠ 1`, and hence `AnalyticOnNhd` on
  `{1}ᶜ` and on the half-plane `{s | 1 < s.re}`;
* raising the level via `changeLevel hMN χ` yields the punctured germ identity
  `(changeLevel hMN χ).LFunction =ᶠ[𝓝[≠] s] fun z ↦ χ.LFunction z * ...`
  (with the Euler-factor deletion over `N.primeFactors`) at every `s : ℂ`, including `s = 1`;
* any primitive character inducing `χ` has the same L-function as `χ.primitiveCharacter`.

## Main results

* `DirichletCharacter.IsPrimitive.LFunction_eq_primitiveCharacter`: uniqueness of the L-function
  of the primitive character inducing `χ`.
* `DirichletCharacter.LFunction_primitiveCharacter_one`: the primitive character inducing the
  principal character modulo `N` has `LFunction = riemannZeta`.
* `DirichletCharacter.analyticAt_LFunction`: `AnalyticAt ℂ χ.LFunction s` for
  `χ ≠ 1 ∨ s ≠ 1` (everywhere if nonprincipal, away from `1` if principal).
* `DirichletCharacter.analyticOnNhd_LFunction_compl_one`: `AnalyticOnNhd ℂ χ.LFunction {1}ᶜ`.
* `DirichletCharacter.analyticOnNhd_LFunction_halfPlane`:
  `AnalyticOnNhd ℂ χ.LFunction {s | 1 < s.re}`.
* `DirichletCharacter.differentiable_prod_one_sub_mul_prime_cpow` and
  `DirichletCharacter.analyticAt_prod_one_sub_mul_prime_cpow`: entirety and analyticity of the
  Euler-factor deletion `∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-z))`.
* `DirichletCharacter.meromorphic_LFunction`: `Meromorphic χ.LFunction`.
* `DirichletCharacter.LFunction_changeLevel_eventuallyEq`: punctured-germ level-change identity at
  every point `s : ℂ`.

## References

Built on Mathlib's `DirichletCharacter.LFunction` and `DirichletCharacter.LFunction_changeLevel`,
by David Loeffler and Michael Stoll.
-/

public section

open Filter
open scoped Topology

namespace DirichletCharacter

variable {M N : ℕ}

/-- Any primitive character inducing `χ` has the same continued L-function as
`χ.primitiveCharacter`. -/
theorem IsPrimitive.LFunction_eq_primitiveCharacter [NeZero M] [NeZero N]
    {χ : DirichletCharacter ℂ N} {χ' : DirichletCharacter ℂ M}
    (hχ' : χ'.IsPrimitive) (hdvd : M ∣ N) (hind : changeLevel hdvd χ' = χ) :
    χ'.LFunction = χ.primitiveCharacter.LFunction := by
  have h := (hχ'.changeLevel_eq_changeLevel_iff χ.primitiveCharacter_isPrimitive
    hdvd χ.conductor_dvd_level).mp (hind.trans χ.changeLevel_primitiveCharacter.symm)
  suffices ∀ {c : ℕ} [NeZero c] (ψ : DirichletCharacter ℂ c) (he : M = c),
      he ▸ χ' = ψ → χ'.LFunction = ψ.LFunction from
    this χ.primitiveCharacter h.1 h.2
  rintro c hc ψ rfl hchar
  dsimp only at hchar
  rw [hchar]

/-- The primitive character inducing the trivial character modulo `N` has
`LFunction = riemannZeta`. -/
@[simp]
theorem LFunction_primitiveCharacter_one [NeZero N] :
    (1 : DirichletCharacter ℂ N).primitiveCharacter.LFunction = riemannZeta :=
  ((IsPrimitive.LFunction_eq_primitiveCharacter
    (by simp [isPrimitive_def, conductor_one]) (one_dvd N)
    (changeLevel_one (one_dvd N))).symm).trans LFunction_modOne_eq

/-- **Analyticity of a Dirichlet L-function.** `χ.LFunction` is analytic at `s` whenever `χ ≠ 1`
or `s ≠ 1`. -/
theorem analyticAt_LFunction [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (h : χ ≠ 1 ∨ s ≠ 1) : AnalyticAt ℂ χ.LFunction s := by
  rcases h with hχ | hs
  · exact (differentiable_LFunction hχ).analyticAt s
  · have hdiff : DifferentiableOn ℂ χ.LFunction {1}ᶜ := fun z hz ↦
      (differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
    exact hdiff.analyticAt (isOpen_compl_singleton.mem_nhds hs)

/-- Every Dirichlet L-function is analytic on `ℂ \ {1}`. -/
theorem analyticOnNhd_LFunction_compl_one [NeZero N] (χ : DirichletCharacter ℂ N) :
    AnalyticOnNhd ℂ χ.LFunction {1}ᶜ := fun _ hs ↦
  analyticAt_LFunction χ (Or.inr hs)

/-- Every Dirichlet L-function is analytic on the half-plane `Re s > 1`. -/
theorem analyticOnNhd_LFunction_halfPlane [NeZero N] (χ : DirichletCharacter ℂ N) :
    AnalyticOnNhd ℂ χ.LFunction {s | 1 < s.re} := fun _ hs ↦
  analyticAt_LFunction χ (Or.inr fun h ↦ by simp [h] at hs)

/-- The Euler-factor deletion `∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-z))` is entire. -/
theorem differentiable_prod_one_sub_mul_prime_cpow (χ : DirichletCharacter ℂ M) (N : ℕ) :
    Differentiable ℂ (fun z : ℂ ↦
      ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-z))) := fun _ ↦
  DifferentiableAt.fun_finsetProd fun p hp ↦ by
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    fun_prop

/-- The Euler-factor deletion `∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-z))` is analytic on
`ℂ`. -/
theorem analyticAt_prod_one_sub_mul_prime_cpow (χ : DirichletCharacter ℂ M) (N : ℕ) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ ↦ ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-z))) s :=
  (differentiable_prod_one_sub_mul_prime_cpow χ N).analyticAt s

/-- Every Dirichlet L-function is meromorphic on `ℂ`. -/
theorem meromorphic_LFunction [NeZero N] (χ : DirichletCharacter ℂ N) :
    Meromorphic χ.LFunction := by
  by_cases hχ : χ = 1
  · subst hχ
    intro s
    have hdiff : Differentiable ℂ (fun z : ℂ ↦
        ∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-z))) := by
      simpa using differentiable_prod_one_sub_mul_prime_cpow (1 : DirichletCharacter ℂ 1) N
    have hmero : MeromorphicAt
        (fun z : ℂ ↦ (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z) s :=
      (hdiff.analyticAt s).meromorphicAt.mul (TauCeti.meromorphic_riemannZeta s)
    refine hmero.congr (Filter.eventually_of_mem
      (nhdsWithin_compl_singleton_le s 1 self_mem_nhdsWithin) fun z hz ↦ ?_)
    exact (LFunctionTrivChar_eq_mul_riemannZeta hz).symm
  · exact fun s ↦ ((differentiable_LFunction hχ).analyticAt s).meromorphicAt

/-- **Level change of a Dirichlet L-function, as punctured germs.** At every `s : ℂ`, including
`s = 1` when `χ = 1`, `(changeLevel hMN χ).LFunction` has the same punctured germ as
`χ.LFunction z * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-z))`. -/
theorem LFunction_changeLevel_eventuallyEq [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) (s : ℂ) :
    (changeLevel hMN χ).LFunction =ᶠ[𝓝[≠] s]
      fun z ↦ χ.LFunction z * ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-z)) :=
  Filter.eventually_of_mem (nhdsWithin_compl_singleton_le s 1 self_mem_nhdsWithin) fun _ hz ↦
    LFunction_changeLevel hMN χ (Or.inr hz)

end DirichletCharacter
