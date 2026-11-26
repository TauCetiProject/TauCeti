/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.NumberField.Cyclotomic.DedekindZeta
import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Primitive
import TauCeti.NumberTheory.DirichletCharacter.Primitive

/-!
# Cyclotomic factorizations of the continued Dedekind zeta function

Let `K` be an `n`-th cyclotomic field over `ℚ` (`n ≠ 0`). On the half-plane `Re s > 1`, the Dedekind
zeta function factors into the Dirichlet `L`-functions of the primitive characters attached to the
characters modulo `n` (`TauCeti.NumberField.dedekindZeta_eq_prod_LFunction_primitiveCharacter`):

`ζ_K(s) = ∏ χ : DirichletCharacter ℂ n, L(s, χ.primitiveCharacter)
        = ζ(s) ∏_{χ ≠ 1} L(s, χ.primitiveCharacter)`.

Each nonprincipal factor `L(s, χ.primitiveCharacter)` is entire, while `ζ(s)` is meromorphic on `ℂ`
and holomorphic off `s = 1`. Consequently, the product furnishes the meromorphic continuation of
`ζ_K` to the whole complex plane, and the factorization lifts to
`TauCeti.LFunctions.dedekindZetaC K` both as an equality of punctured germs at every `s : ℂ`
(including the pole `s = 1`) and as a pointwise identity for every `s ≠ 1`.

When one instead works with the ambient level-`n` characters `χ : DirichletCharacter ℂ n`, each
imprimitive character deletes the Euler factors at primes dividing `n` via
`L(s, χ) = L(s, χ.primitiveCharacter) ∏_{p ∣ n} (1 - χ.primitiveCharacter p * p ^ (-s))`
(`DirichletCharacter.LFunction_changeLevel`). Multiplying `dedekindZetaC K s` by those missing Euler
factors therefore recovers `∏ χ : DirichletCharacter ℂ n, L(s, χ)`. Both the canonical
`χ.primitiveCharacter` formulation and the indexed primitive-lift formulation `(m χ, χ' χ)` are
provided, together with the specializations to prime and prime-power levels:

* At prime level `p`, every nonprincipal character modulo `p` is already primitive, so
  `dedekindZetaC K s = ζ(s) ∏_{χ ≠ 1} L(s, χ)` with no level adjustment.
* At prime-power level `p ^ k` (`k ≠ 0`), every nonprincipal character has conductor divisible by
  `p`, so only the principal character misses an Euler factor at `p`, yielding
  `dedekindZetaC K s * (1 - p ^ (-s)) = ∏ χ : DirichletCharacter ℂ (p ^ k), L(s, χ)`.

## Main results

* `TauCeti.LFunctions.dedekindZetaC_eventuallyEq_prod_LFunction_primitiveCharacter`,
  `TauCeti.LFunctions.dedekindZetaC_eq_prod_LFunction_primitiveCharacter`: primitive-character
  factorization of `dedekindZetaC K` as punctured germs on `ℂ` and pointwise for `s ≠ 1`.
* `TauCeti.LFunctions.dedekindZetaC_eventuallyEq_riemannZeta_mul_prod_LFunction_primitiveCharacter`,
  `TauCeti.LFunctions.dedekindZetaC_eq_riemannZeta_mul_prod_LFunction_primitiveCharacter`:
  factorization with `riemannZeta` separated from `χ ≠ 1`.
* `TauCeti.LFunctions.dedekindZetaC_eventuallyEq_prod_LFunction_of_isPrimitive`,
  `TauCeti.LFunctions.dedekindZetaC_eq_prod_LFunction_of_isPrimitive`: factorization for any
  indexed family `(m χ, χ' χ)` of primitive lifts inducing the characters modulo `n`.
* `TauCeti.LFunctions.dedekindZetaC_mul_prod_eq_prod_LFunction`,
  `TauCeti.LFunctions.dedekindZetaC_mul_prod_eventuallyEq_prod_LFunction`,
  `TauCeti.LFunctions.dedekindZetaC_mul_prod_ite_eq_prod_LFunction_of_isPrimitive`,
  `TauCeti.LFunctions.dedekindZetaC_mul_prod_ite_eventuallyEq_prod_LFunction_of_isPrimitive`:
  level-`n` imprimitive factorizations with the explicit Euler-factor correction.
* `TauCeti.LFunctions.dedekindZetaC_eq_riemannZeta_mul_prod_LFunction_of_prime`,
  `TauCeti.LFunctions.dedekindZetaC_eventuallyEq_riemannZeta_mul_prod_LFunction_of_prime`,
  `TauCeti.LFunctions.dedekindZetaC_mul_one_sub_cpow_eq_prod_LFunction_of_prime_pow`,
  `TauCeti.LFunctions.dedekindZetaC_mul_one_sub_cpow_eventuallyEq_prod_LFunction_of_prime_pow`:
  prime and prime-power cyclotomic specializations.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Theorem 4.3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, Corollary 5.11.
-/

public section

open Filter
open scoped Topology

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Canonical primitive-character factorizations -/

section Primitive

variable {n : ℕ} [NeZero n] [IsCyclotomicExtension {n} ℚ K]

/-- **Cyclotomic factorization of `dedekindZetaC`, as punctured germs.** In an `n`-th cyclotomic
field `K` over `ℚ` (`n ≠ 0`), at every `s : ℂ` (including `s = 1`), `dedekindZetaC K` has the
punctured germ of `∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction`. -/
theorem dedekindZetaC_eventuallyEq_prod_LFunction_primitiveCharacter (s : ℂ) :
    dedekindZetaC K =ᶠ[𝓝[≠] s]
      fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction z := by
  rw [dedekindZetaC_def]
  exact meromorphicContinuation_eventuallyEq
    (DirichletCharacter.meromorphic_prod_LFunction_primitiveCharacter n)
    (fun _ hs ↦ DirichletCharacter.analyticAt_prod_LFunction_primitiveCharacter n
      fun h ↦ by simp [h] at hs)
    (fun _ hs ↦ (NumberField.dedekindZeta_eq_prod_LFunction_primitiveCharacter (n := n) hs).symm) s

/-- **Cyclotomic factorization of `dedekindZetaC` away from `s = 1`.** In an `n`-th cyclotomic
field `K` over `ℚ` (`n ≠ 0`), `dedekindZetaC K s` equals the product of
`χ.primitiveCharacter.LFunction s` over all `χ : DirichletCharacter ℂ n` for every `s ≠ 1`. -/
theorem dedekindZetaC_eq_prod_LFunction_primitiveCharacter {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC K s =
      ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s := by
  rw [dedekindZetaC_def]
  exact meromorphicContinuation_apply
    (DirichletCharacter.meromorphic_prod_LFunction_primitiveCharacter n)
    (fun _ ht ↦ DirichletCharacter.analyticAt_prod_LFunction_primitiveCharacter n
      fun h ↦ by simp [h] at ht)
    (fun _ ht ↦ (NumberField.dedekindZeta_eq_prod_LFunction_primitiveCharacter (n := n) ht).symm)
    (DirichletCharacter.analyticAt_prod_LFunction_primitiveCharacter n hs)

open scoped Classical in
/-- **Cyclotomic factorization of `dedekindZetaC` with `riemannZeta` separated, as germs.** -/
theorem dedekindZetaC_eventuallyEq_riemannZeta_mul_prod_LFunction_primitiveCharacter (s : ℂ) :
    dedekindZetaC K =ᶠ[𝓝[≠] s] fun z ↦
      riemannZeta z *
        ∏ χ : DirichletCharacter ℂ n with χ ≠ 1, χ.primitiveCharacter.LFunction z := by
  simpa only [← funext (DirichletCharacter.prod_LFunction_primitiveCharacter_eq_riemannZeta_mul n)]
    using dedekindZetaC_eventuallyEq_prod_LFunction_primitiveCharacter (K := K) (n := n) s

open scoped Classical in
/-- **Cyclotomic factorization of `dedekindZetaC` with `riemannZeta` separated.** For `s ≠ 1`,
`dedekindZetaC K s = riemannZeta s * ∏_{χ ≠ 1} χ.primitiveCharacter.LFunction s`. -/
theorem dedekindZetaC_eq_riemannZeta_mul_prod_LFunction_primitiveCharacter {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC K s =
      riemannZeta s *
        ∏ χ : DirichletCharacter ℂ n with χ ≠ 1, χ.primitiveCharacter.LFunction s := by
  rw [dedekindZetaC_eq_prod_LFunction_primitiveCharacter (n := n) hs,
    DirichletCharacter.prod_LFunction_primitiveCharacter_eq_riemannZeta_mul]

/-- **Cyclotomic factorization for an indexed family of primitive lifts, as germs.** If for each
`χ : DirichletCharacter ℂ n`, `χ' χ` is a primitive character modulo `m χ ∣ n` whose lift to level
`n` is `χ`, then `dedekindZetaC K` has the punctured germ of `∏ χ, (χ' χ).LFunction` at every
`s : ℂ`. -/
theorem dedekindZetaC_eventuallyEq_prod_LFunction_of_isPrimitive
    (m : DirichletCharacter ℂ n → ℕ) [∀ χ, NeZero (m χ)] (hdvd : ∀ χ, m χ ∣ n)
    (χ' : ∀ χ : DirichletCharacter ℂ n, DirichletCharacter ℂ (m χ))
    (hprim : ∀ χ, (χ' χ).IsPrimitive)
    (hind : ∀ χ, DirichletCharacter.changeLevel (hdvd χ) (χ' χ) = χ) (s : ℂ) :
    dedekindZetaC K =ᶠ[𝓝[≠] s]
      fun z ↦ ∏ χ : DirichletCharacter ℂ n, (χ' χ).LFunction z := by
  refine (dedekindZetaC_eventuallyEq_prod_LFunction_primitiveCharacter (K := K) (n := n) s).trans
    (Eventually.of_forall fun z ↦ Finset.prod_congr rfl fun χ _ ↦ ?_)
  rw [(hprim χ).LFunction_eq_primitiveCharacter_of_changeLevel_eq (hdvd χ) (hind χ)]

/-- **Cyclotomic factorization for an indexed family of primitive lifts.** Pointwise form of
`dedekindZetaC_eventuallyEq_prod_LFunction_of_isPrimitive` away from `s = 1`. -/
theorem dedekindZetaC_eq_prod_LFunction_of_isPrimitive
    (m : DirichletCharacter ℂ n → ℕ) [∀ χ, NeZero (m χ)] (hdvd : ∀ χ, m χ ∣ n)
    (χ' : ∀ χ : DirichletCharacter ℂ n, DirichletCharacter ℂ (m χ))
    (hprim : ∀ χ, (χ' χ).IsPrimitive)
    (hind : ∀ χ, DirichletCharacter.changeLevel (hdvd χ) (χ' χ) = χ) {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC K s = ∏ χ : DirichletCharacter ℂ n, (χ' χ).LFunction s := by
  rw [dedekindZetaC_eq_prod_LFunction_primitiveCharacter (n := n) hs]
  refine Finset.prod_congr rfl fun χ _ ↦ ?_
  rw [(hprim χ).LFunction_eq_primitiveCharacter_of_changeLevel_eq (hdvd χ) (hind χ)]

end Primitive

/-! ### Imprimitive level-`n` factorizations with Euler-factor correction -/

section Imprimitive

variable {n : ℕ} [NeZero n] [IsCyclotomicExtension {n} ℚ K]

/-- **Imprimitive level-`n` factorization of `dedekindZetaC` away from `s = 1`.** Multiplying
`dedekindZetaC K s` by the Euler factors `1 - χ.primitiveCharacter p * p ^ (-s)` at primes dividing
`n` yields the product of the ambient level-`n` Dirichlet `L`-functions `χ.LFunction s`. -/
theorem dedekindZetaC_mul_prod_eq_prod_LFunction {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC K s *
        (∏ χ : DirichletCharacter ℂ n,
          ∏ p ∈ n.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s))) =
      ∏ χ : DirichletCharacter ℂ n, χ.LFunction s := by
  rw [dedekindZetaC_eq_prod_LFunction_primitiveCharacter (n := n) hs,
    DirichletCharacter.prod_LFunction_primitiveCharacter_mul_prod_eq_prod_LFunction n hs]

/-- **Imprimitive level-`n` factorization of `dedekindZetaC`, as punctured germs.** Holds at every
`s : ℂ`, including the pole `s = 1`. -/
theorem dedekindZetaC_mul_prod_eventuallyEq_prod_LFunction (s : ℂ) :
    (fun z ↦ dedekindZetaC K z *
        ∏ χ : DirichletCharacter ℂ n,
          ∏ p ∈ n.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-z))) =ᶠ[𝓝[≠] s]
      fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.LFunction z :=
  ((eventually_cofinite_ne 1).filter_mono (nhdsNE_le_cofinite s)).mono fun _ hz ↦
    dedekindZetaC_mul_prod_eq_prod_LFunction (n := n) hz

/-- **Imprimitive level-`n` factorization for an indexed family of primitive lifts.** Away from
`s = 1`, multiplying `dedekindZetaC K s` by `∏ χ, ∏ p ∈ n.primeFactors, (if p ∣ m χ then 1 else
1 - χ' χ p * p ^ (-s))` recovers `∏ χ : DirichletCharacter ℂ n, χ.LFunction s`. -/
theorem dedekindZetaC_mul_prod_ite_eq_prod_LFunction_of_isPrimitive
    (m : DirichletCharacter ℂ n → ℕ) (hdvd : ∀ χ, m χ ∣ n)
    (χ' : ∀ χ : DirichletCharacter ℂ n, DirichletCharacter ℂ (m χ))
    (hprim : ∀ χ, (χ' χ).IsPrimitive)
    (hind : ∀ χ, DirichletCharacter.changeLevel (hdvd χ) (χ' χ) = χ) {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC K s *
        (∏ χ : DirichletCharacter ℂ n, ∏ p ∈ n.primeFactors,
          (if p ∣ m χ then (1 : ℂ) else 1 - χ' χ p * (p : ℂ) ^ (-s))) =
      ∏ χ : DirichletCharacter ℂ n, χ.LFunction s := by
  have hcorr : (∏ χ : DirichletCharacter ℂ n, ∏ p ∈ n.primeFactors,
        (if p ∣ m χ then (1 : ℂ) else 1 - χ' χ p * (p : ℂ) ^ (-s))) =
      ∏ χ : DirichletCharacter ℂ n,
        ∏ p ∈ n.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) := by
    refine Finset.prod_congr rfl fun χ _ ↦ Finset.prod_congr rfl fun p hp ↦ ?_
    split_ifs with hpc
    · rw [(hprim χ).level_eq_conductor_of_changeLevel_eq (hdvd χ) (hind χ)] at hpc
      simp [χ.primitiveCharacter_apply_prime_eq_zero (Nat.prime_of_mem_primeFactors hp) hpc]
    · have hp_eq : (χ' χ) p = χ.primitiveCharacter p := by
        simpa only [Int.cast_natCast] using
          (hprim χ).apply_intCast_eq_primitiveCharacter_of_changeLevel_eq (hdvd χ) (hind χ) p
      rw [hp_eq]
  rw [hcorr]
  exact dedekindZetaC_mul_prod_eq_prod_LFunction (n := n) hs

/-- **Imprimitive level-`n` factorization for an indexed family of primitive lifts, as germs.** -/
theorem dedekindZetaC_mul_prod_ite_eventuallyEq_prod_LFunction_of_isPrimitive
    (m : DirichletCharacter ℂ n → ℕ) (hdvd : ∀ χ, m χ ∣ n)
    (χ' : ∀ χ : DirichletCharacter ℂ n, DirichletCharacter ℂ (m χ))
    (hprim : ∀ χ, (χ' χ).IsPrimitive)
    (hind : ∀ χ, DirichletCharacter.changeLevel (hdvd χ) (χ' χ) = χ) (s : ℂ) :
    (fun z ↦ dedekindZetaC K z *
        ∏ χ : DirichletCharacter ℂ n, ∏ p ∈ n.primeFactors,
          (if p ∣ m χ then (1 : ℂ) else 1 - χ' χ p * (p : ℂ) ^ (-z))) =ᶠ[𝓝[≠] s]
      fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.LFunction z :=
  ((eventually_cofinite_ne 1).filter_mono (nhdsNE_le_cofinite s)).mono fun _ hz ↦
    dedekindZetaC_mul_prod_ite_eq_prod_LFunction_of_isPrimitive m hdvd χ' hprim hind hz

end Imprimitive

/-! ### Specializations to prime and prime-power cyclotomic fields -/

section PrimeAndPrimePow

open scoped Classical in
/-- **Factorization of `dedekindZetaC` for a prime cyclotomic field.** At prime level `p`, every
nonprincipal character modulo `p` is primitive, so `dedekindZetaC K s` equals
`riemannZeta s * ∏_{χ ≠ 1} χ.LFunction s` directly for every `s ≠ 1`. -/
theorem dedekindZetaC_eq_riemannZeta_mul_prod_LFunction_of_prime {p : ℕ} [hp : Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ K] {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC K s =
      riemannZeta s * ∏ χ : DirichletCharacter ℂ p with χ ≠ 1, χ.LFunction s := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  rw [dedekindZetaC_eq_riemannZeta_mul_prod_LFunction_primitiveCharacter (n := p) hs]
  congr 1
  refine Finset.prod_congr rfl fun χ hχ ↦ ?_
  rw [← (DirichletCharacter.isPrimitive_of_ne_one_of_prime hp.out
    (Finset.mem_filter.mp hχ).2).LFunction_eq_primitiveCharacter_of_changeLevel_eq (dvd_refl p)
    (DirichletCharacter.changeLevel_self χ)]

open scoped Classical in
/-- **Factorization of `dedekindZetaC` for a prime cyclotomic field, as punctured germs.** -/
theorem dedekindZetaC_eventuallyEq_riemannZeta_mul_prod_LFunction_of_prime {p : ℕ}
    [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] (s : ℂ) :
    dedekindZetaC K =ᶠ[𝓝[≠] s] fun z ↦
      riemannZeta z * ∏ χ : DirichletCharacter ℂ p with χ ≠ 1, χ.LFunction z :=
  ((eventually_cofinite_ne 1).filter_mono (nhdsNE_le_cofinite s)).mono fun _ hz ↦
    dedekindZetaC_eq_riemannZeta_mul_prod_LFunction_of_prime hz

/-- **Level-`p ^ k` factorization of `dedekindZetaC` for a prime-power cyclotomic field.** For
`k ≠ 0`, every nonprincipal character modulo `p ^ k` has conductor divisible by `p`, so only the
principal character misses an Euler factor at `p`, giving
`dedekindZetaC K s * (1 - p ^ (-s)) = ∏ χ : DirichletCharacter ℂ (p ^ k), χ.LFunction s` for
`s ≠ 1`. -/
theorem dedekindZetaC_mul_one_sub_cpow_eq_prod_LFunction_of_prime_pow {p k : ℕ}
    [hp : Fact p.Prime] (hk : k ≠ 0) [IsCyclotomicExtension {p ^ k} ℚ K] {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC K s * (1 - (p : ℂ) ^ (-s)) =
      ∏ χ : DirichletCharacter ℂ (p ^ k), χ.LFunction s := by
  classical
  have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.out.ne_zero⟩
  rw [← dedekindZetaC_mul_prod_eq_prod_LFunction (K := K) (n := p ^ k) hs]
  congr 1
  simp_rw [Nat.primeFactors_prime_pow hk hp.out, Finset.prod_singleton]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun χ : DirichletCharacter ℂ (p ^ k) ↦ 1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s))
    (Finset.mem_univ 1)]
  have hc1 : (1 : DirichletCharacter ℂ (p ^ k)).conductor = 1 := DirichletCharacter.conductor_one
  have : Subsingleton (ZMod (1 : DirichletCharacter ℂ (p ^ k)).conductor) := hc1 ▸ inferInstance
  have h1 : (1 : DirichletCharacter ℂ (p ^ k)).primitiveCharacter p = 1 := by
    rw [DirichletCharacter.primitiveCharacter_one, MulChar.one_apply (isUnit_of_subsingleton _)]
  have hne : (∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ (p ^ k)),
      (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s))) = 1 :=
    Finset.prod_eq_one fun χ hχ ↦ by
      simp [χ.primitiveCharacter_apply_prime_eq_zero hp.out
        ((DirichletCharacter.dvd_conductor_iff_ne_one_of_prime_pow hp.out χ).mpr
          (Finset.ne_of_mem_erase hχ))]
  rw [hne, mul_one, h1, one_mul]

/-- **Level-`p ^ k` factorization of `dedekindZetaC` for a prime-power cyclotomic field, as
germs.** -/
theorem dedekindZetaC_mul_one_sub_cpow_eventuallyEq_prod_LFunction_of_prime_pow {p k : ℕ}
    [Fact p.Prime] (hk : k ≠ 0) [IsCyclotomicExtension {p ^ k} ℚ K] (s : ℂ) :
    (fun z ↦ dedekindZetaC K z * (1 - (p : ℂ) ^ (-z))) =ᶠ[𝓝[≠] s]
      fun z ↦ ∏ χ : DirichletCharacter ℂ (p ^ k), χ.LFunction z :=
  ((eventually_cofinite_ne 1).filter_mono (nhdsNE_le_cofinite s)).mono fun _ hz ↦
    dedekindZetaC_mul_one_sub_cpow_eq_prod_LFunction_of_prime_pow hk hz

end PrimeAndPrimePow

end TauCeti.LFunctions
