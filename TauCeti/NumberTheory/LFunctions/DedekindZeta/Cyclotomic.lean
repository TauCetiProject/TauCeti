/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.NumberField.Cyclotomic.DedekindZeta
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Meromorphic
import TauCeti.NumberTheory.DirichletCharacter.PolynomialProduct
import TauCeti.NumberTheory.DirichletCharacter.Primitive
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta

/-!
# The cyclotomic factorization of the continued Dedekind zeta function

Let `F` be an `n`-th cyclotomic field over `ℚ` (`[IsCyclotomicExtension {n} ℚ F]` with
`[NeZero n]`). On the half-plane `Re s > 1` of absolute convergence, the Dedekind zeta function
factors as `ζ_F(s) = ∏ χ : DirichletCharacter ℂ n, L(s, χ.primitiveCharacter)`
(`TauCeti.NumberField.dedekindZeta_eq_prod_LFunction_primitiveCharacter`). Each factor
`L(s, χ.primitiveCharacter)` is meromorphic on `ℂ` (`DirichletCharacter.meromorphic_LFunction`)
and analytic off `s = 1` (`DirichletCharacter.analyticAt_LFunction`), so the finite product is a
meromorphic continuation of `ζ_F` that is analytic on `ℂ \ {1}`. By uniqueness of the canonical
meromorphic continuation `dedekindZetaC F`, the factorization lifts to the whole complex plane.

Both sides have a simple pole at `s = 1` — contributed by the trivial character, whose primitive
L-function is `riemannZeta` — where Mathlib's total functions carry junk values. Thus every
continued-function factorization is stated in two forms (with the convergent half-plane form
immediately following from `s ≠ 1`):

* as an equality of punctured germs `=ᶠ[𝓝[≠] s]` at every point `s : ℂ`, including `s = 1`;
* as a pointwise equality for every `s ≠ 1`.

In addition to the canonical primitive form (`χ.primitiveCharacter`), this file records:

* the factorization with `riemannZeta` separated (`dedekindZetaC_eventuallyEq_riemannZeta_mul_prod`
  and `dedekindZetaC_eq_riemannZeta_mul_prod`);
* the arbitrary-primitive-representative forms
  (`dedekindZetaC_eventuallyEq_prod_LFunction_of_isPrimitive` and
  `dedekindZetaC_eq_prod_LFunction_of_isPrimitive`);
* the imprimitive level-`n` factorizations (`dedekindZetaC_mul_prod_eventuallyEq_prod_LFunction`,
  `dedekindZetaC_mul_prod_eq_prod_LFunction`,
  `dedekindZetaC_mul_prod_primesOver_eventuallyEq_prod_LFunction`,
  `dedekindZetaC_mul_prod_primesOver_eq_prod_LFunction`,
  `dedekindZetaC_mul_prod_ite_eventuallyEq_prod_LFunction`, and
  `dedekindZetaC_mul_prod_ite_eq_prod_LFunction`), where the missing Euler factors forced by
  `L(χ, s) = L(χ*, s) ∏_{p ∣ n} (1 - χ*(p) p ^ (-s))` multiply `dedekindZetaC F`;
* the closed-form prime-power specialization (`n = p ^ (k + 1)`), where the entire correction
  product collapses to the single factor `1 - (p : ℂ) ^ (-s)`;
* concrete worked checks at `n = 1` (`ℚ`), `n = 2` (`ℚ` via `2 % 4 = 2`, both primitive and
  imprimitive), `n = 4` (`ℚ(i)` with explicit level-4 correction `1 - 2 ^ (-s)`), `n = 5`
  (`ℚ(ζ₅)` with explicit level-5 correction `1 - 5 ^ (-s)`), and `n = 6` (`6 % 4 = 2`, explicit
  correction `(1 - 4 ^ (-s)) * (1 - 3 ^ (-s))`).

## Main results

* `TauCeti.LFunctions.dedekindZetaC_eventuallyEq_prod_LFunction_primitiveCharacter`: punctured-germ
  factorization at every `s : ℂ`.
* `TauCeti.LFunctions.dedekindZetaC_eq_prod_LFunction_primitiveCharacter`: pointwise factorization
  for every `s ≠ 1`.
* `TauCeti.LFunctions.dedekindZetaC_eventuallyEq_riemannZeta_mul_prod` and
  `TauCeti.LFunctions.dedekindZetaC_eq_riemannZeta_mul_prod`: factorization with `riemannZeta`
  separated.
* `TauCeti.LFunctions.dedekindZetaC_eventuallyEq_prod_LFunction_of_isPrimitive` and
  `TauCeti.LFunctions.dedekindZetaC_eq_prod_LFunction_of_isPrimitive`: primitive cyclotomic
  factorization for arbitrary inducing primitive characters `(m, hdvd, χ', hprim, hind)`.
* `TauCeti.LFunctions.dedekindZetaC_mul_prod_eventuallyEq_prod_LFunction` and
  `TauCeti.LFunctions.dedekindZetaC_mul_prod_eq_prod_LFunction`: imprimitive level-`n`
  factorization.
* `TauCeti.LFunctions.dedekindZetaC_mul_prod_primesOver_eventuallyEq_prod_LFunction` and
  `TauCeti.LFunctions.dedekindZetaC_mul_prod_primesOver_eq_prod_LFunction`: imprimitive
  factorization expressed via primes above `p ∣ n`.
* `TauCeti.LFunctions.dedekindZetaC_mul_prod_ite_eventuallyEq_prod_LFunction` and
  `TauCeti.LFunctions.dedekindZetaC_mul_prod_ite_eq_prod_LFunction`: imprimitive level-`n`
  factorization for arbitrary inducing primitive characters in `if p ∣ m χ then 1 else ...` form.
* `TauCeti.LFunctions.dedekindZetaC_mul_one_sub_prime_cpow_eventuallyEq_prod_LFunction` and
  `TauCeti.LFunctions.dedekindZetaC_mul_one_sub_prime_cpow_eq_prod_LFunction`: prime-power level
  collapse `n = p ^ (k + 1)`.
* Worked specializations for `n = 1` (`ℚ`), `n = 2`, `n = 4`, `n = 5`, and `n = 6`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, Corollary 5.11.
* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 4, Theorem 4.3.
* H. Davenport, *Multiplicative Number Theory*, Chapter 6.
* Built on Mathlib's `DirichletCharacter.LFunction` and `DirichletCharacter.LFunction_changeLevel`
  (by David Loeffler and Michael Stoll).
-/

public section

open Filter Ideal IsDedekindDomain NumberField
open scoped NumberField Topology

namespace TauCeti.LFunctions

section General

variable {n : ℕ} [NeZero n] {F : Type*} [Field F] [NumberField F]
  [IsCyclotomicExtension {n} ℚ F]

/-- **Cyclotomic factorization of `dedekindZetaC`, as punctured germs.** At every point `s : ℂ`,
including the pole `s = 1`, `dedekindZetaC F` has the punctured germ of the product of the
primitive Dirichlet L-functions modulo `n`. -/
theorem dedekindZetaC_eventuallyEq_prod_LFunction_primitiveCharacter (s : ℂ) :
    dedekindZetaC F =ᶠ[𝓝[≠] s]
      fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction z := by
  rw [dedekindZetaC_def]
  exact meromorphicContinuation_eventuallyEq
    (fun z ↦ MeromorphicAt.fun_prod fun (χ : DirichletCharacter ℂ n) _ ↦
      DirichletCharacter.meromorphic_LFunction χ.primitiveCharacter z)
    (fun z hz ↦ Finset.analyticAt_fun_prod _ fun (χ : DirichletCharacter ℂ n) _ ↦
      DirichletCharacter.analyticAt_LFunction χ.primitiveCharacter
        (Or.inr fun h ↦ by simp [h] at hz))
    (fun _ hz ↦
      (NumberField.dedekindZeta_eq_prod_LFunction_primitiveCharacter (n := n) (F := F) hz).symm)
    s

/-- **Cyclotomic factorization of `dedekindZetaC` away from `s = 1`.** For every `s ≠ 1`,
`dedekindZetaC F s = ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s`.
At `s = 1` both sides have a pole; use
`dedekindZetaC_eventuallyEq_prod_LFunction_primitiveCharacter` there. -/
theorem dedekindZetaC_eq_prod_LFunction_primitiveCharacter {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC F s = ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s := by
  rw [dedekindZetaC_def]
  exact meromorphicContinuation_apply
    (fun z ↦ MeromorphicAt.fun_prod fun (χ : DirichletCharacter ℂ n) _ ↦
      DirichletCharacter.meromorphic_LFunction χ.primitiveCharacter z)
    (fun z hz ↦ Finset.analyticAt_fun_prod _ fun (χ : DirichletCharacter ℂ n) _ ↦
      DirichletCharacter.analyticAt_LFunction χ.primitiveCharacter
        (Or.inr fun h ↦ by simp [h] at hz))
    (fun _ hz ↦
      (NumberField.dedekindZeta_eq_prod_LFunction_primitiveCharacter (n := n) (F := F) hz).symm)
    (Finset.analyticAt_fun_prod _ fun (χ : DirichletCharacter ℂ n) _ ↦
      DirichletCharacter.analyticAt_LFunction χ.primitiveCharacter (Or.inr hs))

/-- **Cyclotomic factorization of `dedekindZetaC` with `riemannZeta` separated, as germs.** -/
theorem dedekindZetaC_eventuallyEq_riemannZeta_mul_prod
    [DecidableEq (DirichletCharacter ℂ n)] (s : ℂ) :
    dedekindZetaC F =ᶠ[𝓝[≠] s] fun z ↦ riemannZeta z *
      ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ n),
        χ.primitiveCharacter.LFunction z := by
  filter_upwards [dedekindZetaC_eventuallyEq_prod_LFunction_primitiveCharacter (n := n) (F := F) s]
    with z hz
  rw [hz, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (1 : DirichletCharacter ℂ n)),
    DirichletCharacter.LFunction_primitiveCharacter_one]

/-- **Cyclotomic factorization of `dedekindZetaC` with `riemannZeta` separated, away from `1`.** -/
theorem dedekindZetaC_eq_riemannZeta_mul_prod
    [DecidableEq (DirichletCharacter ℂ n)] {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC F s = riemannZeta s *
      ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ n),
        χ.primitiveCharacter.LFunction s := by
  rw [dedekindZetaC_eq_prod_LFunction_primitiveCharacter (n := n) (F := F) hs,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (1 : DirichletCharacter ℂ n)),
    DirichletCharacter.LFunction_primitiveCharacter_one]

/-! ### Arbitrary primitive representatives -/

section PrimitiveRepresentatives

variable (m : DirichletCharacter ℂ n → ℕ) (hdvd : ∀ χ, m χ ∣ n)
  (χ' : ∀ χ : DirichletCharacter ℂ n, DirichletCharacter ℂ (m χ))
  (hprim : ∀ χ, (χ' χ).IsPrimitive)
  (hind : ∀ χ, DirichletCharacter.changeLevel (hdvd χ) (χ' χ) = χ)

include hprim hind

/-- **Cyclotomic factorization as punctured germs for arbitrary primitive representatives.** -/
theorem dedekindZetaC_eventuallyEq_prod_LFunction_of_isPrimitive (s : ℂ) :
    dedekindZetaC F =ᶠ[𝓝[≠] s] fun z ↦
      ∏ χ : DirichletCharacter ℂ n,
        haveI : NeZero (m χ) := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne n) (hdvd χ)⟩
        (χ' χ).LFunction z := by
  filter_upwards [dedekindZetaC_eventuallyEq_prod_LFunction_primitiveCharacter (n := n) (F := F) s]
    with z hz
  rw [hz]
  refine Finset.prod_congr rfl fun χ _ ↦ ?_
  have : NeZero (m χ) := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne n) (hdvd χ)⟩
  exact (congrFun ((hprim χ).LFunction_eq_primitiveCharacter (hdvd χ) (hind χ)) z).symm

/-- **Cyclotomic factorization away from `s = 1` for arbitrary primitive representatives.** This
covers the convergent half-plane `1 < s.re` as well as every other `s ≠ 1`. -/
theorem dedekindZetaC_eq_prod_LFunction_of_isPrimitive {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC F s =
      ∏ χ : DirichletCharacter ℂ n,
        haveI : NeZero (m χ) := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne n) (hdvd χ)⟩
        (χ' χ).LFunction s := by
  rw [dedekindZetaC_eq_prod_LFunction_primitiveCharacter (n := n) (F := F) hs]
  refine Finset.prod_congr rfl fun χ _ ↦ ?_
  have : NeZero (m χ) := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne n) (hdvd χ)⟩
  exact (congrFun ((hprim χ).LFunction_eq_primitiveCharacter (hdvd χ) (hind χ)) s).symm

end PrimitiveRepresentatives

/-! ### Imprimitive level-`n` factorizations -/

/-- **Imprimitive cyclotomic factorization as punctured germs.** At every `s : ℂ`, including `1`,
multiplying `dedekindZetaC F` by the missing Euler factors
`∏ χ, ∏ p ∈ n.primeFactors, (1 - χ.primitiveCharacter p * p ^ (-z))` gives the germ of
`∏ χ : DirichletCharacter ℂ n, χ.LFunction z`. -/
theorem dedekindZetaC_mul_prod_eventuallyEq_prod_LFunction (s : ℂ) :
    (fun z ↦ dedekindZetaC F z *
        ∏ χ : DirichletCharacter ℂ n, ∏ p ∈ n.primeFactors,
          (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-z))) =ᶠ[𝓝[≠] s]
      fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.LFunction z := by
  have h1 := dedekindZetaC_eventuallyEq_prod_LFunction_primitiveCharacter (n := n) (F := F) s
  have h2 : ∀ χ : DirichletCharacter ℂ n,
      (fun z ↦ χ.primitiveCharacter.LFunction z *
          ∏ p ∈ n.primeFactors,
            (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-z)))
        =ᶠ[𝓝[≠] s] χ.LFunction := fun χ ↦ by
    have he := DirichletCharacter.LFunction_changeLevel_eventuallyEq χ.conductor_dvd_level
      χ.primitiveCharacter s
    rw [χ.changeLevel_primitiveCharacter] at he
    exact he.symm
  have hprod : (fun z ↦ ∏ χ : DirichletCharacter ℂ n,
        (χ.primitiveCharacter.LFunction z *
          ∏ p ∈ n.primeFactors,
            (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-z))))
      =ᶠ[𝓝[≠] s] fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.LFunction z := by
    filter_upwards [Filter.eventually_all.mpr h2] with z hz
    exact Finset.prod_congr rfl fun χ _ ↦ hz χ
  filter_upwards [h1, hprod] with z hz1 hzp
  rw [hz1, ← Finset.prod_mul_distrib]
  exact hzp

/-- **Imprimitive cyclotomic factorization away from `s = 1`.** For every `s ≠ 1`, multiplying
`dedekindZetaC F s` by `∏ χ, ∏ p ∈ n.primeFactors, (1 - χ.primitiveCharacter p * p ^ (-s))`
gives `∏ χ, χ.LFunction s`. -/
theorem dedekindZetaC_mul_prod_eq_prod_LFunction {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC F s *
        ∏ χ : DirichletCharacter ℂ n, ∏ p ∈ n.primeFactors,
          (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)) =
      ∏ χ : DirichletCharacter ℂ n, χ.LFunction s := by
  rw [dedekindZetaC_eq_prod_LFunction_primitiveCharacter (n := n) (F := F) hs,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun χ _ ↦ ?_
  rw [← DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (Or.inr hs), χ.changeLevel_primitiveCharacter]

/-- **Imprimitive cyclotomic factorization via primes above `p ∣ n`, as punctured germs.** -/
theorem dedekindZetaC_mul_prod_primesOver_eventuallyEq_prod_LFunction (s : ℂ) :
    (fun z ↦ dedekindZetaC F z *
        ∏ p ∈ n.primeFactors, ∏ P ∈ primesOverFinset (span {(p : ℤ)}) (𝓞 F),
          (1 - (Ideal.absNorm P : ℂ) ^ (-z))) =ᶠ[𝓝[≠] s]
      fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.LFunction z := by
  filter_upwards [dedekindZetaC_mul_prod_eventuallyEq_prod_LFunction (n := n) (F := F) s] with z hz
  rw [← hz]
  congr 1
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun p hp ↦
    NumberField.prod_primesOverFinset_one_sub_absNorm_cpow (n := n) (F := F)
      (Nat.prime_of_mem_primeFactors hp) z

/-- **Imprimitive cyclotomic factorization via primes above `p ∣ n`, away from `s = 1`.** -/
theorem dedekindZetaC_mul_prod_primesOver_eq_prod_LFunction {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC F s *
        ∏ p ∈ n.primeFactors, ∏ P ∈ primesOverFinset (span {(p : ℤ)}) (𝓞 F),
          (1 - (Ideal.absNorm P : ℂ) ^ (-s)) =
      ∏ χ : DirichletCharacter ℂ n, χ.LFunction s := by
  rw [← dedekindZetaC_mul_prod_eq_prod_LFunction (n := n) (F := F) hs]
  congr 1
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun p hp ↦
    NumberField.prod_primesOverFinset_one_sub_absNorm_cpow (n := n) (F := F)
      (Nat.prime_of_mem_primeFactors hp) s

section ImprimitiveRepresentatives

variable (m : DirichletCharacter ℂ n → ℕ) (hdvd : ∀ χ, m χ ∣ n)
  (χ' : ∀ χ : DirichletCharacter ℂ n, DirichletCharacter ℂ (m χ))
  (hprim : ∀ χ, (χ' χ).IsPrimitive)
  (hind : ∀ χ, DirichletCharacter.changeLevel (hdvd χ) (χ' χ) = χ)

include hprim hind

/-- **Imprimitive cyclotomic factorization as punctured germs for arbitrary primitive
representatives**, written with explicit `if p ∣ m χ then 1 else ...` correction factors. -/
theorem dedekindZetaC_mul_prod_ite_eventuallyEq_prod_LFunction (s : ℂ) :
    (fun z ↦ dedekindZetaC F z * ∏ χ : DirichletCharacter ℂ n, ∏ p ∈ n.primeFactors,
        (if p ∣ m χ then (1 : ℂ) else 1 - χ' χ (p : ZMod (m χ)) * (p : ℂ) ^ (-z)))
      =ᶠ[𝓝[≠] s] fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.LFunction z := by
  filter_upwards [dedekindZetaC_mul_prod_eventuallyEq_prod_LFunction (n := n) (F := F) s] with z hz
  rw [← hz]
  congr 1
  refine Finset.prod_congr rfl fun χ _ ↦ Finset.prod_congr rfl fun p hp ↦ ?_
  rw [DirichletCharacter.ite_dvd_one_sub_mul (χ' χ) (Nat.prime_of_mem_primeFactors hp),
    (hprim χ).apply_natCast_eq_primitiveCharacter (hdvd χ) (hind χ) p]

/-- **Imprimitive cyclotomic factorization away from `s = 1` for arbitrary primitive
representatives**, written with explicit `if p ∣ m χ then 1 else ...` correction factors. This
covers the convergent half-plane `1 < s.re` as well as every other `s ≠ 1`. -/
theorem dedekindZetaC_mul_prod_ite_eq_prod_LFunction {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC F s * ∏ χ : DirichletCharacter ℂ n, ∏ p ∈ n.primeFactors,
        (if p ∣ m χ then (1 : ℂ) else 1 - χ' χ (p : ZMod (m χ)) * (p : ℂ) ^ (-s)) =
      ∏ χ : DirichletCharacter ℂ n, χ.LFunction s := by
  rw [← dedekindZetaC_mul_prod_eq_prod_LFunction (n := n) (F := F) hs]
  congr 1
  refine Finset.prod_congr rfl fun χ _ ↦ Finset.prod_congr rfl fun p hp ↦ ?_
  rw [DirichletCharacter.ite_dvd_one_sub_mul (χ' χ) (Nat.prime_of_mem_primeFactors hp),
    (hprim χ).apply_natCast_eq_primitiveCharacter (hdvd χ) (hind χ) p]

end ImprimitiveRepresentatives

end General

/-! ### Prime-power level collapse -/

section PrimePower

variable {p k : ℕ} (hp : p.Prime) {F : Type*} [Field F] [NumberField F]
  [IsCyclotomicExtension {p ^ (k + 1)} ℚ F]

/-- **Prime-power imprimitive factorization, as punctured germs.** At any prime-power level
`p ^ (k + 1)`, the entire imprimitive correction product collapses to the single factor
`1 - p ^ (-z)`. -/
theorem dedekindZetaC_mul_one_sub_prime_cpow_eventuallyEq_prod_LFunction (s : ℂ) :
    haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    (fun z ↦ dedekindZetaC F z * (1 - (p : ℂ) ^ (-z))) =ᶠ[𝓝[≠] s]
      fun z ↦ ∏ χ : DirichletCharacter ℂ (p ^ (k + 1)), χ.LFunction z := by
  have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : NeZero ((Monoid.exponent (ZMod (p ^ (k + 1)))ˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  filter_upwards
    [dedekindZetaC_mul_prod_eventuallyEq_prod_LFunction (n := p ^ (k + 1)) (F := F) s] with z hz
  rw [← DirichletCharacter.prod_one_sub_primitiveCharacter_mul_prime_pow (R := ℂ) hp k
    (fun q ↦ (q : ℂ) ^ (-z)), hz]

/-- **Prime-power imprimitive factorization, away from `s = 1`.** At any prime-power level
`p ^ (k + 1)`, `dedekindZetaC F s * (1 - p ^ (-s))` equals
`∏ χ : DirichletCharacter ℂ (p ^ (k + 1)), χ.LFunction s` for every `s ≠ 1`. -/
theorem dedekindZetaC_mul_one_sub_prime_cpow_eq_prod_LFunction {s : ℂ} (hs : s ≠ 1) :
    haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    dedekindZetaC F s * (1 - (p : ℂ) ^ (-s)) =
      ∏ χ : DirichletCharacter ℂ (p ^ (k + 1)), χ.LFunction s := by
  have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : NeZero ((Monoid.exponent (ZMod (p ^ (k + 1)))ˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  rw [← DirichletCharacter.prod_one_sub_primitiveCharacter_mul_prime_pow (R := ℂ) hp k
    (fun q ↦ (q : ℂ) ^ (-s))]
  exact dedekindZetaC_mul_prod_eq_prod_LFunction (n := p ^ (k + 1)) (F := F) hs

end PrimePower

/-! ### Worked concrete checks (`n = 1, 2, 4, 5, 6`) -/

section WorkedExamples

/-- **Check `n = 1` (`ℚ`), as germs.** `dedekindZetaC ℚ` has the punctured germ of `riemannZeta`
at every point `s : ℂ`. -/
theorem dedekindZetaC_rat_eventuallyEq_riemannZeta (s : ℂ) :
    dedekindZetaC ℚ =ᶠ[𝓝[≠] s] riemannZeta := by
  classical
  have : IsCyclotomicExtension {1} ℚ ℚ :=
    IsCyclotomicExtension.singleton_one_of_algebraMap_bijective Function.surjective_id
  filter_upwards [dedekindZetaC_eventuallyEq_riemannZeta_mul_prod (n := 1) (F := ℚ) s] with z hz
  have h : (Finset.univ.erase (1 : DirichletCharacter ℂ 1)) = ∅ := by
    ext χ
    simp [DirichletCharacter.level_one' χ]
  rw [hz, h, Finset.prod_empty, mul_one]

/-- **Check `n = 1` (`ℚ`), away from `s = 1`.** `dedekindZetaC ℚ s = riemannZeta s`
for `s ≠ 1`. -/
theorem dedekindZetaC_rat_eq_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC ℚ s = riemannZeta s := by
  classical
  have : IsCyclotomicExtension {1} ℚ ℚ :=
    IsCyclotomicExtension.singleton_one_of_algebraMap_bijective Function.surjective_id
  rw [dedekindZetaC_eq_riemannZeta_mul_prod (n := 1) (F := ℚ) hs]
  have h : (Finset.univ.erase (1 : DirichletCharacter ℂ 1)) = ∅ := by
    ext χ
    simp [DirichletCharacter.level_one' χ]
  rw [h, Finset.prod_empty, mul_one]

/-- **Check `n = 2` (`2 % 4 = 2`, primitive germs).** Every `2`-nd cyclotomic field over `ℚ` has
the punctured germ of `riemannZeta` at every point `s : ℂ`. -/
theorem dedekindZetaC_two_eventuallyEq_riemannZeta
    {F : Type*} [Field F] [NumberField F] [IsCyclotomicExtension {2} ℚ F] (s : ℂ) :
    dedekindZetaC F =ᶠ[𝓝[≠] s] riemannZeta := by
  classical
  have huniq : ∀ χ : DirichletCharacter ℂ 2, χ = 1 := fun χ ↦ by
    ext a
    have ha : (a : ZMod 2) = 1 := by fin_cases a; rfl
    rw [ha, map_one, map_one]
  filter_upwards [dedekindZetaC_eventuallyEq_riemannZeta_mul_prod (n := 2) (F := F) s] with z hz
  have h : (Finset.univ.erase (1 : DirichletCharacter ℂ 2)) = ∅ := by
    ext χ
    simp [huniq χ]
  rw [hz, h, Finset.prod_empty, mul_one]

/-- **Check `n = 2` (`2 % 4 = 2`, primitive pointwise off `1`).** Every `2`-nd cyclotomic field
over `ℚ` satisfies `dedekindZetaC F s = riemannZeta s` for `s ≠ 1`. -/
theorem dedekindZetaC_two_eq_riemannZeta
    {F : Type*} [Field F] [NumberField F] [IsCyclotomicExtension {2} ℚ F]
    {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC F s = riemannZeta s := by
  classical
  have huniq : ∀ χ : DirichletCharacter ℂ 2, χ = 1 := fun χ ↦ by
    ext a
    have ha : (a : ZMod 2) = 1 := by fin_cases a; rfl
    rw [ha, map_one, map_one]
  rw [dedekindZetaC_eq_riemannZeta_mul_prod (n := 2) (F := F) hs]
  have h : (Finset.univ.erase (1 : DirichletCharacter ℂ 2)) = ∅ := by
    ext χ
    simp [huniq χ]
  rw [h, Finset.prod_empty, mul_one]

/-- **Check `n = 2` (`2 % 4 = 2`, imprimitive level-2 pointwise off `1`).** At level `2`, the
imprimitive product adds the deleted Euler factor `1 - 2 ^ (-s)` on the left. -/
theorem dedekindZetaC_two_mul_one_sub_eq_prod_LFunction
    {F : Type*} [Field F] [NumberField F] [IsCyclotomicExtension {2} ℚ F]
    {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC F s * (1 - (2 : ℂ) ^ (-s)) =
      ∏ χ : DirichletCharacter ℂ 2, χ.LFunction s := by
  simpa using dedekindZetaC_mul_one_sub_prime_cpow_eq_prod_LFunction (p := 2) (k := 0) (F := F)
    Nat.prime_two hs

/-- **Check `n = 4` (`ℚ(i)`), imprimitive level-4 germs.** At level `4`, the trivial character
contributes `1 - 2 ^ (-z)` and the odd character of conductor `4` contributes `1`, so the
imprimitive factorization multiplies `dedekindZetaC F` by `1 - 2 ^ (-z)`. -/
theorem dedekindZetaC_four_mul_one_sub_eventuallyEq_prod_LFunction
    {F : Type*} [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F] (s : ℂ) :
    (fun z ↦ dedekindZetaC F z * (1 - (2 : ℂ) ^ (-z))) =ᶠ[𝓝[≠] s]
      fun z ↦ ∏ χ : DirichletCharacter ℂ 4, χ.LFunction z := by
  simpa using dedekindZetaC_mul_one_sub_prime_cpow_eventuallyEq_prod_LFunction
    (p := 2) (k := 1) (F := F) Nat.prime_two s

/-- **Check `n = 4` (`ℚ(i)`), imprimitive level-4 pointwise off `1`.** -/
theorem dedekindZetaC_four_mul_one_sub_eq_prod_LFunction
    {F : Type*} [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F]
    {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC F s * (1 - (2 : ℂ) ^ (-s)) =
      ∏ χ : DirichletCharacter ℂ 4, χ.LFunction s := by
  simpa using dedekindZetaC_mul_one_sub_prime_cpow_eq_prod_LFunction
    (p := 2) (k := 1) (F := F) Nat.prime_two hs

/-- **Check `n = 5` (`ℚ(ζ₅)`), imprimitive level-5 germs.** By
`DirichletCharacter.isPrimitive_of_prime_of_ne_one`, the three nontrivial characters modulo `5`
have conductor `5` and only the trivial character has conductor `1`, so at the totally ramified
prime `5` the correction product collapses to `1 - 5 ^ (-z)`. -/
theorem dedekindZetaC_five_mul_one_sub_eventuallyEq_prod_LFunction
    {F : Type*} [Field F] [NumberField F] [IsCyclotomicExtension {5} ℚ F] (s : ℂ) :
    (fun z ↦ dedekindZetaC F z * (1 - (5 : ℂ) ^ (-z))) =ᶠ[𝓝[≠] s]
      fun z ↦ ∏ χ : DirichletCharacter ℂ 5, χ.LFunction z := by
  simpa using dedekindZetaC_mul_one_sub_prime_cpow_eventuallyEq_prod_LFunction
    (p := 5) (k := 0) (F := F) (by decide) s

/-- **Check `n = 5` (`ℚ(ζ₅)`), imprimitive level-5 pointwise off `1`.** -/
theorem dedekindZetaC_five_mul_one_sub_eq_prod_LFunction
    {F : Type*} [Field F] [NumberField F] [IsCyclotomicExtension {5} ℚ F]
    {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC F s * (1 - (5 : ℂ) ^ (-s)) =
      ∏ χ : DirichletCharacter ℂ 5, χ.LFunction s := by
  simpa using dedekindZetaC_mul_one_sub_prime_cpow_eq_prod_LFunction
    (p := 5) (k := 0) (F := F) (by decide) hs

/-- **Check `n = 6` (`6 % 4 = 2`, composite level with unramified prime factor `2`).** In
`ℚ(ζ₆) = ℚ(ζ₃)`, the prime `2` is inert of residue degree `2` (`ord_3(2) = 2`), so the
imprimitive level-6 correction at `2` is `1 - 4 ^ (-s)` and at `3` is `1 - 3 ^ (-s)`. -/
theorem dedekindZetaC_six_mul_eq_prod_LFunction
    {F : Type*} [Field F] [NumberField F] [IsCyclotomicExtension {6} ℚ F]
    {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC F s * ((1 - (4 : ℂ) ^ (-s)) * (1 - (3 : ℂ) ^ (-s))) =
      ∏ χ : DirichletCharacter ℂ 6, χ.LFunction s := by
  have : NeZero ((Monoid.exponent (ZMod 6)ˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  have h6eq : (6 : ℕ) = 2 * 3 := by norm_num
  have hpf : (6 : ℕ).primeFactors = {2, 3} := by
    rw [h6eq, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.prime_two.primeFactors, Nat.prime_three.primeFactors]
    rfl
  have h2ord : orderOf ((2 : ℕ) : ZMod 3) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by decide) (by decide)
  have h3one : ((3 : ℕ) : ZMod 2) = 1 := by decide
  have h3ord : orderOf ((3 : ℕ) : ZMod 2) = 1 := by rw [h3one, orderOf_one]
  have h4eq : (4 : ℂ) = ((2 ^ 2 : ℕ) : ℂ) := by norm_num
  have h4 : (4 : ℂ) ^ (-s) = ((2 : ℂ) ^ (-s)) ^ 2 := by
    rw [h4eq, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
    simp
  rw [← dedekindZetaC_mul_prod_eq_prod_LFunction (n := 6) (F := F) hs]
  congr 1
  rw [Finset.prod_comm, hpf, Finset.prod_pair (by decide)]
  simp only [Nat.cast_ofNat]
  have h2 := DirichletCharacter.prod_one_sub_primitiveCharacter_mul
    (R := ℂ) (n := 6) (p := 2) (k := 1) (m := 3) Nat.prime_two (by norm_num) (by decide)
    ((2 : ℂ) ^ (-s))
  have h3 := DirichletCharacter.prod_one_sub_primitiveCharacter_mul
    (R := ℂ) (n := 6) (p := 3) (k := 1) (m := 2) Nat.prime_three (by norm_num) (by decide)
    ((3 : ℂ) ^ (-s))
  simp only [Nat.cast_ofNat] at h2 h3 h2ord h3ord
  rw [h2, h3, h2ord, h3ord]
  have ht3 : (3 : ℕ).totient = 2 := by decide
  have ht2 : (2 : ℕ).totient = 1 := by decide
  rw [ht3, ht2, h4]
  norm_num

end WorkedExamples

end TauCeti.LFunctions
