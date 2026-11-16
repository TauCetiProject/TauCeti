/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.NumberField.Cyclotomic.DedekindZeta
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel

/-!
# The cyclotomic factorization of the continued Dedekind zeta function

Let `K` be an `n`-th cyclotomic field over `ℚ` (`n ≠ 0`). On the half-plane `Re s > 1` of
absolute convergence, the Dedekind zeta function factors as the product of the Dirichlet
`L`-functions of the primitive characters inducing the characters modulo `n`:
`ζ_K(s) = ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s`
(`TauCeti.NumberField.dedekindZeta_eq_prod_LFunction_primitiveCharacter`).

Each factor `χ.primitiveCharacter.LFunction` is meromorphic on `ℂ` and analytic away from `s = 1`
(the principal character contributes `riemannZeta`, and every nonprincipal factor is entire).
Hence their product is a meromorphic continuation of `ζ_K`, and the factorization extends to the
continued Dedekind zeta function `TauCeti.LFunctions.dedekindZetaC K`.

Both sides have a simple pole at `s = 1`, where the values of the total functions carry no meaning,
so both the primitive and imprimitive (level-`n`) factorizations are stated as equalities of
punctured germs at every point of `ℂ` and as pointwise equalities away from `s = 1`.

## Main results

* `TauCeti.LFunctions.dedekindZetaC_eventuallyEq_prod_LFunction_primitiveCharacter`: at every
  `s : ℂ`, `dedekindZetaC K` has the punctured germ of
  `∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction z`.
* `TauCeti.LFunctions.dedekindZetaC_eq_prod_LFunction_primitiveCharacter`:
  `dedekindZetaC K s = ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s` for `s ≠ 1`.
* `TauCeti.LFunctions.dedekindZetaC_eq_riemannZeta_mul_prod_LFunction_primitiveCharacter`:
  the same with the principal factor `riemannZeta s` separated.
* `TauCeti.LFunctions.dedekindZetaC_mul_prod_eulerFactor_eventuallyEq_prod_LFunction`: the
  imprimitive level-`n` factorization as an equality of punctured germs at every `s : ℂ`.
* `TauCeti.LFunctions.dedekindZetaC_mul_prod_eulerFactor_eq_prod_LFunction`: the imprimitive
  level-`n` factorization pointwise for `s ≠ 1`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Theorem 4.3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, Corollary 5.11.
-/

public section

open Filter NumberField
open scoped Topology

namespace TauCeti.LFunctions

section

variable (n : ℕ) [NeZero n]

/-- The product `∏ χ, χ.primitiveCharacter.LFunction z` is analytic away from `s = 1`. -/
private theorem analyticAt_prod_LFunction_primitiveCharacter {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ
      (fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction z) s :=
  Finset.analyticAt_fun_prod Finset.univ fun χ _ ↦
    DirichletCharacter.analyticAt_LFunction_primitiveCharacter χ (.inr hs)

/-- The product `∏ χ, χ.primitiveCharacter.LFunction z` is meromorphic on the plane. -/
private theorem meromorphic_prod_LFunction_primitiveCharacter :
    Meromorphic fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction z := fun z ↦
  MeromorphicAt.fun_prod fun χ _ ↦
    DirichletCharacter.meromorphic_LFunction_primitiveCharacter χ z

/-- The product `∏ χ, χ.primitiveCharacter.LFunction z` is analytic on `Re s > 1`. -/
private theorem analyticOnNhd_prod_LFunction_primitiveCharacter :
    AnalyticOnNhd ℂ
      (fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction z)
      {s | 1 < s.re} := fun _ hs ↦
  analyticAt_prod_LFunction_primitiveCharacter n fun h ↦ by simp [h] at hs

end

variable (K : Type*) [Field K] [NumberField K] (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ K]

/-- The product `∏ χ, χ.primitiveCharacter.LFunction z` agrees with `ζ_K` on `Re s > 1`. -/
private theorem eqOn_prod_LFunction_primitiveCharacter :
    Set.EqOn (fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction z)
      (dedekindZeta K) {s | 1 < s.re} := fun _ hs ↦
  (NumberField.dedekindZeta_eq_prod_LFunction_primitiveCharacter K n hs).symm

/-- **The cyclotomic factorization of the continued Dedekind zeta function, as germs.** If `K` is
an `n`-th cyclotomic field over `ℚ` (`n ≠ 0`), then at every point `s : ℂ`, including the pole
`s = 1`, `dedekindZetaC K` has the punctured germ of
`∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction z`. -/
theorem dedekindZetaC_eventuallyEq_prod_LFunction_primitiveCharacter (s : ℂ) :
    dedekindZetaC K =ᶠ[𝓝[≠] s]
      fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction z := by
  rw [dedekindZetaC_def]
  exact meromorphicContinuation_eventuallyEq
    (meromorphic_prod_LFunction_primitiveCharacter n)
    (analyticOnNhd_prod_LFunction_primitiveCharacter n)
    (eqOn_prod_LFunction_primitiveCharacter K n) s

/-- **The cyclotomic factorization of the continued Dedekind zeta function (primitive form).**
If `K` is an `n`-th cyclotomic field over `ℚ` (`n ≠ 0`), then
`dedekindZetaC K s = ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s` at every
`s ≠ 1`. At `s = 1` both sides have a simple pole, and
`dedekindZetaC_eventuallyEq_prod_LFunction_primitiveCharacter` compares their germs there. -/
theorem dedekindZetaC_eq_prod_LFunction_primitiveCharacter {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC K s =
      ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s := by
  rw [dedekindZetaC_def]
  exact meromorphicContinuation_apply
    (meromorphic_prod_LFunction_primitiveCharacter n)
    (analyticOnNhd_prod_LFunction_primitiveCharacter n)
    (eqOn_prod_LFunction_primitiveCharacter K n)
    (analyticAt_prod_LFunction_primitiveCharacter n hs)

/-- **The cyclotomic factorization of `dedekindZetaC` with `riemannZeta` separated.** For every
`s ≠ 1`, `dedekindZetaC K s = riemannZeta s * ∏ χ ≠ 1, χ.primitiveCharacter.LFunction s`. -/
theorem dedekindZetaC_eq_riemannZeta_mul_prod_LFunction_primitiveCharacter
    [DecidableEq (DirichletCharacter ℂ n)] {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC K s =
      riemannZeta s *
        ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ n),
          χ.primitiveCharacter.LFunction s := by
  rw [dedekindZetaC_eq_prod_LFunction_primitiveCharacter K n hs,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (1 : DirichletCharacter ℂ n)),
    DirichletCharacter.LFunction_primitiveCharacter_one]

/-- **The imprimitive cyclotomic factorization of `dedekindZetaC`, as germs.** In terms of the
level-`n` characters `χ : DirichletCharacter ℂ n`, the missing Euler factors at primes dividing `n`
multiply `dedekindZetaC K` on the left as an equality of punctured germs at every `s : ℂ`. -/
theorem dedekindZetaC_mul_prod_eulerFactor_eventuallyEq_prod_LFunction (s : ℂ) :
    (fun z ↦ dedekindZetaC K z *
        ∏ χ : DirichletCharacter ℂ n, ∏ p ∈ n.primeFactors,
          (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-z))) =ᶠ[𝓝[≠] s]
      fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.LFunction z := by
  have hne : ∀ᶠ z in 𝓝[≠] s, z ≠ 1 := by
    rcases eq_or_ne s 1 with rfl | hs1
    · exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds hs1)
  filter_upwards [dedekindZetaC_eventuallyEq_prod_LFunction_primitiveCharacter K n s, hne]
    with z hz hz1
  rw [hz, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun χ _ ↦ ?_
  rw [← DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (.inr hz1), χ.changeLevel_primitiveCharacter]

/-- **The imprimitive cyclotomic factorization of `dedekindZetaC`.** For every `s ≠ 1`,
`dedekindZetaC K s * ∏ χ, ∏ p ∈ n.primeFactors, (1 - χ.primitiveCharacter p * p ^ (-s))` equals
`∏ χ : DirichletCharacter ℂ n, χ.LFunction s`. -/
theorem dedekindZetaC_mul_prod_eulerFactor_eq_prod_LFunction {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC K s *
        ∏ χ : DirichletCharacter ℂ n, ∏ p ∈ n.primeFactors,
          (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)) =
      ∏ χ : DirichletCharacter ℂ n, χ.LFunction s := by
  rw [dedekindZetaC_eq_prod_LFunction_primitiveCharacter K n hs, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun χ _ ↦ ?_
  rw [← DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (.inr hs), χ.changeLevel_primitiveCharacter]

end TauCeti.LFunctions
