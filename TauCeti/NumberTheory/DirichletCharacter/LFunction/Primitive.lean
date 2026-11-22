/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.DirichletCharacter.Conductor
public import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta
import TauCeti.NumberTheory.DirichletCharacter.Primitive

/-!
# Continued Dirichlet `L`-functions of primitive characters

For a nonzero modulus `n`, associating to each `χ : DirichletCharacter ℂ n` its primitive character
`χ.primitiveCharacter` produces a finite family of continued Dirichlet `L`-functions:

* At `χ = 1`, `χ.primitiveCharacter` has level `1` and its continued `L`-function is `riemannZeta`
  (`DirichletCharacter.LFunction_primitiveCharacter_one`), so splitting off `χ = 1` separates
  `riemannZeta` from the product over `χ ≠ 1`
  (`DirichletCharacter.prod_LFunction_primitiveCharacter_eq_riemannZeta_mul`).
* Any primitive character `ψ` modulo `m ∣ n` lifting to `χ` has the same continued `L`-function as
  `χ.primitiveCharacter`
  (`DirichletCharacter.IsPrimitive.LFunction_eq_primitiveCharacter_of_changeLevel_eq`).
* Away from `s = 1`, multiplying `∏ χ, χ.primitiveCharacter.LFunction s` by the Euler factors
  `∏ χ, ∏ p ∈ n.primeFactors, (1 - χ.primitiveCharacter p * p ^ (-s))` deleted when raising level
  from `χ.conductor` to `n` recovers `∏ χ : DirichletCharacter ℂ n, χ.LFunction s`
  (`DirichletCharacter.prod_LFunction_primitiveCharacter_mul_prod_eq_prod_LFunction`).
* Raising the level of `χ` does not change `χ.primitiveCharacter.LFunction`
  (`DirichletCharacter.LFunction_primitiveCharacter_changeLevel`); in particular, if `χ.mul ψ` is
  principal then `χ` and `ψ⁻¹` have the same primitive `L`-function
  (`DirichletCharacter.LFunction_primitiveCharacter_eq_of_mul_eq_one`).
* Each nonprincipal factor `χ.primitiveCharacter.LFunction` is entire, so the product over `χ ≠ 1`
  is entire (`DirichletCharacter.differentiable_prod_LFunction_primitiveCharacter_ne_one`), while
  the full product is analytic away from `s = 1`
  (`DirichletCharacter.analyticAt_prod_LFunction_primitiveCharacter`) and meromorphic on `ℂ`
  (`DirichletCharacter.meromorphic_prod_LFunction_primitiveCharacter`).

## Main results

* `DirichletCharacter.LFunction_eq_riemannZeta_of_eq_one`,
  `DirichletCharacter.LFunction_primitiveCharacter_one`: the continued `L`-function at level `1`
  (and of `(1 : DirichletCharacter ℂ n).primitiveCharacter`) equals `riemannZeta`.
* `DirichletCharacter.IsPrimitive.LFunction_eq_primitiveCharacter_of_changeLevel_eq`: any primitive
  lift of `χ` has the same continued `L`-function as `χ.primitiveCharacter`.
* `DirichletCharacter.LFunction_primitiveCharacter_changeLevel`,
  `DirichletCharacter.LFunction_primitiveCharacter_eq_of_mul_eq_one`: raising the level does not
  change the primitive `L`-function, and characters `χ`, `ψ` with principal common-level product
  `χ.mul ψ` have the primitive `L`-functions of `χ` and `ψ⁻¹` equal.
* `DirichletCharacter.prod_LFunction_primitiveCharacter_eq_riemannZeta_mul`: separates `riemannZeta`
  from the `χ ≠ 1` factors of `∏ χ, χ.primitiveCharacter.LFunction s`.
* `DirichletCharacter.prod_LFunction_primitiveCharacter_mul_prod_eq_prod_LFunction`: Euler-factor
  comparison between `∏ χ, χ.primitiveCharacter.LFunction s` and `∏ χ, χ.LFunction s` for `s ≠ 1`.
* `DirichletCharacter.differentiable_prod_LFunction_primitiveCharacter_ne_one`,
  `DirichletCharacter.analyticAt_prod_LFunction_primitiveCharacter`,
  `DirichletCharacter.meromorphic_prod_LFunction_primitiveCharacter`: regularity and meromorphy of
  the primitive-character `L`-function products.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 9.
* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 4.
-/

public section

namespace DirichletCharacter

/-- A Dirichlet character whose level equals `1` has continued `L`-function equal to
`riemannZeta`. -/
theorem LFunction_eq_riemannZeta_of_eq_one {m : ℕ} [NeZero m] (hm : m = 1)
    (ψ : DirichletCharacter ℂ m) : ψ.LFunction = riemannZeta := by
  subst hm
  exact LFunction_modOne_eq

/-- The continued `L`-function of the primitive character of the principal character modulo `n`
(`n ≠ 0`) is the Riemann zeta function. -/
@[simp]
theorem LFunction_primitiveCharacter_one (n : ℕ) [NeZero n] :
    (1 : DirichletCharacter ℂ n).primitiveCharacter.LFunction = riemannZeta :=
  LFunction_eq_riemannZeta_of_eq_one conductor_one _

/-- A primitive character `ψ` of level `m ∣ n` (`n ≠ 0`) whose lift to level `n` is `χ` has the
same continued `L`-function as `χ.primitiveCharacter`. -/
theorem IsPrimitive.LFunction_eq_primitiveCharacter_of_changeLevel_eq {m n : ℕ} [NeZero m]
    [NeZero n] {ψ : DirichletCharacter ℂ m} {χ : DirichletCharacter ℂ n}
    (hψ : ψ.IsPrimitive) (hm : m ∣ n) (hind : changeLevel hm ψ = χ) :
    ψ.LFunction = χ.primitiveCharacter.LFunction := by
  obtain ⟨rfl, rfl⟩ := hψ.eq_primitiveCharacter_of_changeLevel_eq hm hind
  rfl

/-- Lifting a character `χ` of nonzero level `m` to a nonzero multiple `n` of `m` does not change
the continued `L`-function of its primitive character. -/
@[simp]
theorem LFunction_primitiveCharacter_changeLevel {m n : ℕ} [NeZero m] [NeZero n]
    (χ : DirichletCharacter ℂ m) (hm : m ∣ n) :
    (changeLevel hm χ).primitiveCharacter.LFunction = χ.primitiveCharacter.LFunction :=
  (χ.primitiveCharacter_isPrimitive.LFunction_eq_primitiveCharacter_of_changeLevel_eq
    (χ.conductor_dvd_level.trans hm)
    (by rw [changeLevel_trans _ χ.conductor_dvd_level, changeLevel_primitiveCharacter])).symm

/-- If the common-level product `χ.mul ψ` of characters of nonzero levels is principal, then `χ`
and `ψ⁻¹` induce the same primitive character, so their primitive characters have the same
continued `L`-function. -/
theorem LFunction_primitiveCharacter_eq_of_mul_eq_one {m n : ℕ} [NeZero m] [NeZero n]
    {χ : DirichletCharacter ℂ m} {ψ : DirichletCharacter ℂ n} (h : χ.mul ψ = 1) :
    χ.primitiveCharacter.LFunction = ψ⁻¹.primitiveCharacter.LFunction := by
  have : NeZero (m.lcm n) := ⟨Nat.lcm_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  rw [DirichletCharacter.mul] at h
  rw [← LFunction_primitiveCharacter_changeLevel χ (Nat.dvd_lcm_left m n),
    ← LFunction_primitiveCharacter_changeLevel ψ⁻¹ (Nat.dvd_lcm_right m n), map_inv,
    eq_inv_of_mul_eq_one_left h]

open scoped Classical in
/-- Splitting off the principal character `χ = 1` separates `riemannZeta s` from the product of
`χ.primitiveCharacter.LFunction s` over all `χ : DirichletCharacter ℂ n`. -/
theorem prod_LFunction_primitiveCharacter_eq_riemannZeta_mul (n : ℕ) [NeZero n] (s : ℂ) :
    (∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s) =
      riemannZeta s *
        ∏ χ : DirichletCharacter ℂ n with χ ≠ 1, χ.primitiveCharacter.LFunction s := by
  rw [Finset.filter_ne', ← Finset.mul_prod_erase Finset.univ
    (fun χ : DirichletCharacter ℂ n ↦ χ.primitiveCharacter.LFunction s) (Finset.mem_univ 1),
    LFunction_primitiveCharacter_one]

/-- Away from `s = 1`, multiplying the product of `χ.primitiveCharacter.LFunction s` over
`χ : DirichletCharacter ℂ n` by the Euler factors deleted at primes dividing `n` recovers the
product of the level-`n` continued `L`-functions `χ.LFunction s`. -/
theorem prod_LFunction_primitiveCharacter_mul_prod_eq_prod_LFunction (n : ℕ) [NeZero n] {s : ℂ}
    (hs : s ≠ 1) :
    (∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s) *
        (∏ χ : DirichletCharacter ℂ n,
          ∏ p ∈ n.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s))) =
      ∏ χ : DirichletCharacter ℂ n, χ.LFunction s := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun χ _ ↦ ?_
  rw [← LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter (.inr hs),
    χ.changeLevel_primitiveCharacter]

open scoped Classical in
/-- The product of `χ.primitiveCharacter.LFunction` over all nonprincipal characters `χ` modulo `n`
(`n ≠ 0`) is entire. -/
theorem differentiable_prod_LFunction_primitiveCharacter_ne_one (n : ℕ) [NeZero n] :
    Differentiable ℂ fun z ↦
      ∏ χ : DirichletCharacter ℂ n with χ ≠ 1, χ.primitiveCharacter.LFunction z :=
  Differentiable.fun_finsetProd fun χ hχ ↦
    differentiable_LFunction (mt χ.primitiveCharacter_eq_one_iff.mp (Finset.mem_filter.mp hχ).2)

/-- Away from `s = 1`, the product of `χ.primitiveCharacter.LFunction` over all characters `χ`
modulo `n` (`n ≠ 0`) is analytic at `s`. -/
theorem analyticAt_prod_LFunction_primitiveCharacter (n : ℕ) [NeZero n] {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ
      (fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction z) s := by
  classical
  rw [funext (prod_LFunction_primitiveCharacter_eq_riemannZeta_mul n)]
  exact (analyticOn_riemannZeta s hs).mul
    ((differentiable_prod_LFunction_primitiveCharacter_ne_one n).analyticAt s)

/-- The product of `χ.primitiveCharacter.LFunction` over all characters `χ` modulo `n` (`n ≠ 0`) is
meromorphic on `ℂ`. -/
theorem meromorphic_prod_LFunction_primitiveCharacter (n : ℕ) [NeZero n] :
    Meromorphic fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction z := by
  classical
  rw [funext (prod_LFunction_primitiveCharacter_eq_riemannZeta_mul n)]
  exact fun z ↦ (TauCeti.meromorphic_riemannZeta z).mul
    ((differentiable_prod_LFunction_primitiveCharacter_ne_one n).analyticAt z).meromorphicAt

end DirichletCharacter
