/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.NumberField.Cyclotomic.DedekindZeta
import TauCeti.NumberTheory.DirichletCharacter.Primitive
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta

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
* `TauCeti.LFunctions.dedekindZetaC_eq_dedekindZeta_of_isCyclotomicExtension`: `dedekindZetaC K s`
  agrees with `NumberField.dedekindZeta K s` on `1 < s.re`.
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

/-! ### Analytic and meromorphic helpers for the primitive-character product -/

section Helpers

variable {n : ℕ} [NeZero n]

open scoped Classical in
/-- The product of `χ.primitiveCharacter.LFunction` over nonprincipal `χ` modulo `n` is entire. -/
private theorem differentiable_prod_LFunction_primitiveCharacter_ne_one :
    Differentiable ℂ fun z ↦
      ∏ χ : DirichletCharacter ℂ n with χ ≠ 1, χ.primitiveCharacter.LFunction z :=
  Differentiable.fun_finsetProd fun χ hχ ↦
    DirichletCharacter.differentiable_LFunction
      (mt χ.primitiveCharacter_eq_one_iff.mp (Finset.mem_filter.mp hχ).2)

/-- Away from `s = 1`, the full product `∏ χ, χ.primitiveCharacter.LFunction` is analytic. -/
private theorem analyticAt_prod_LFunction_primitiveCharacter {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ
      (fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction z) s := by
  classical
  rw [funext (DirichletCharacter.prod_LFunction_primitiveCharacter_eq_riemannZeta_mul n)]
  exact (analyticOn_riemannZeta s hs).mul
    (differentiable_prod_LFunction_primitiveCharacter_ne_one.analyticAt s)

/-- The full product `∏ χ, χ.primitiveCharacter.LFunction` is meromorphic on `ℂ`. -/
private theorem meromorphic_prod_LFunction_primitiveCharacter :
    Meromorphic fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction z := by
  classical
  rw [funext (DirichletCharacter.prod_LFunction_primitiveCharacter_eq_riemannZeta_mul n)]
  exact fun z ↦ (meromorphic_riemannZeta z).mul
    (differentiable_prod_LFunction_primitiveCharacter_ne_one.analyticAt z).meromorphicAt

/-- The full product `∏ χ, χ.primitiveCharacter.LFunction` is holomorphic on `Re s > 1`. -/
private theorem analyticOnNhd_prod_LFunction_primitiveCharacter :
    AnalyticOnNhd ℂ
      (fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction z)
      {s | 1 < s.re} := fun _ hs ↦
  analyticAt_prod_LFunction_primitiveCharacter fun h ↦ by simp [h] at hs

/-- On `Re s > 1`, the primitive-character product agrees with `NumberField.dedekindZeta K`. -/
private theorem eqOn_prod_LFunction_primitiveCharacter [IsCyclotomicExtension {n} ℚ K] :
    Set.EqOn (fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction z)
      (NumberField.dedekindZeta K) {s | 1 < s.re} := fun _ hs ↦
  (NumberField.dedekindZeta_eq_prod_LFunction_primitiveCharacter (n := n) hs).symm

/-- Every punctured neighborhood `𝓝[≠] s` in `ℂ` avoids `1`. -/
private theorem compl_singleton_one_mem_nhdsWithin_ne (s : ℂ) :
    ({1}ᶜ : Set ℂ) ∈ 𝓝[≠] s := by
  rcases eq_or_ne s 1 with rfl | hs
  · exact self_mem_nhdsWithin
  · exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hs)

/-- Any primitive character `ψ` of level `M ∣ n` lifting to `χ` modulo `n` has the same level,
character values on `ℕ`, and continued `L`-function as `χ.primitiveCharacter`. -/
private theorem isPrimitive_lift_eq_primitiveCharacter {M : ℕ} (hdvd : M ∣ n)
    (ψ : DirichletCharacter ℂ M) (hprim : ψ.IsPrimitive)
    (hind : DirichletCharacter.changeLevel hdvd ψ = χ) :
    M = χ.conductor ∧ (∀ a : ℕ, ψ a = χ.primitiveCharacter a) ∧
      (∀ [NeZero M], ψ.LFunction = χ.primitiveCharacter.LFunction) := by
  obtain ⟨hM, hψ⟩ := (hprim.changeLevel_eq_changeLevel_iff χ.primitiveCharacter_isPrimitive
    hdvd χ.conductor_dvd_level).mp (hind.trans χ.changeLevel_primitiveCharacter.symm)
  subst hM
  subst hψ
  exact ⟨rfl, fun _ ↦ rfl, fun {_} ↦ rfl⟩

end Helpers

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
  exact meromorphicContinuation_eventuallyEq meromorphic_prod_LFunction_primitiveCharacter
    analyticOnNhd_prod_LFunction_primitiveCharacter eqOn_prod_LFunction_primitiveCharacter s

/-- **Cyclotomic factorization of `dedekindZetaC` away from `s = 1`.** In an `n`-th cyclotomic
field `K` over `ℚ` (`n ≠ 0`), `dedekindZetaC K s` equals the product of
`χ.primitiveCharacter.LFunction s` over all `χ : DirichletCharacter ℂ n` for every `s ≠ 1`. -/
theorem dedekindZetaC_eq_prod_LFunction_primitiveCharacter {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC K s =
      ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s := by
  rw [dedekindZetaC_def]
  exact meromorphicContinuation_apply meromorphic_prod_LFunction_primitiveCharacter
    analyticOnNhd_prod_LFunction_primitiveCharacter eqOn_prod_LFunction_primitiveCharacter
    (analyticAt_prod_LFunction_primitiveCharacter hs)

/-- On `Re s > 1`, the continued Dedekind zeta function of a cyclotomic field agrees with
`NumberField.dedekindZeta K`. -/
theorem dedekindZetaC_eq_dedekindZeta_of_isCyclotomicExtension (n : ℕ) [NeZero n]
    [IsCyclotomicExtension {n} ℚ K] {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaC K s = NumberField.dedekindZeta K s := by
  rw [dedekindZetaC_eq_prod_LFunction_primitiveCharacter (n := n) (fun h ↦ by simp [h] at hs),
    NumberField.dedekindZeta_eq_prod_LFunction_primitiveCharacter (n := n) hs]

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
  exact ((isPrimitive_lift_eq_primitiveCharacter (hdvd χ) (χ' χ) (hprim χ) (hind χ)).2.2 ▸ rfl)

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
  rw [(isPrimitive_lift_eq_primitiveCharacter (hdvd χ) (χ' χ) (hprim χ) (hind χ)).2.2]

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
  rw [dedekindZetaC_eq_prod_LFunction_primitiveCharacter (n := n) hs, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun χ _ ↦ ?_
  rw [← DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (.inr hs), χ.changeLevel_primitiveCharacter]

/-- **Imprimitive level-`n` factorization of `dedekindZetaC`, as punctured germs.** Holds at every
`s : ℂ`, including the pole `s = 1`. -/
theorem dedekindZetaC_mul_prod_eventuallyEq_prod_LFunction (s : ℂ) :
    (fun z ↦ dedekindZetaC K z *
        ∏ χ : DirichletCharacter ℂ n,
          ∏ p ∈ n.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-z))) =ᶠ[𝓝[≠] s]
      fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.LFunction z := by
  filter_upwards [compl_singleton_one_mem_nhdsWithin_ne s] with z hz
  exact dedekindZetaC_mul_prod_eq_prod_LFunction (n := n) hz

/-- For a primitive lift `χ' χ` of level `m χ ∣ n` and a prime `p`, the explicit conditional Euler
factor `if p ∣ m χ then 1 else 1 - χ' χ p * p ^ (-s)` coincides with
`1 - χ.primitiveCharacter p * p ^ (-s)`. -/
private theorem ite_dvd_eq_one_sub_primitiveCharacter {m : ℕ} (hdvd : m ∣ n)
    (ψ : DirichletCharacter ℂ m) (hprim : ψ.IsPrimitive)
    (hind : DirichletCharacter.changeLevel hdvd ψ = χ) {p : ℕ} (hp : p.Prime) (s : ℂ) :
    (if p ∣ m then (1 : ℂ) else 1 - ψ p * (p : ℂ) ^ (-s)) =
      1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s) := by
  obtain ⟨hm, hval, -⟩ := isPrimitive_lift_eq_primitiveCharacter hdvd ψ hprim hind
  rw [hval p]
  split_ifs with hpc
  · rw [hm] at hpc
    have hnu : ¬ IsUnit (p : ZMod χ.conductor) :=
      fun hu ↦ (ZMod.isUnit_prime_iff_not_dvd hp).mp hu hpc
    simp [χ.primitiveCharacter.map_nonunit hnu]
  · rfl

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
        ∏ p ∈ n.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) :=
    Finset.prod_congr rfl fun χ _ ↦ Finset.prod_congr rfl fun p hp ↦
      ite_dvd_eq_one_sub_primitiveCharacter (hdvd χ) (χ' χ) (hprim χ) (hind χ)
        (Nat.prime_of_mem_primeFactors hp) s
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
      fun z ↦ ∏ χ : DirichletCharacter ℂ n, χ.LFunction z := by
  filter_upwards [compl_singleton_one_mem_nhdsWithin_ne s] with z hz
  exact dedekindZetaC_mul_prod_ite_eq_prod_LFunction_of_isPrimitive m hdvd χ' hprim hind hz

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
  have hprim := DirichletCharacter.isPrimitive_of_ne_one_of_prime hp.out (Finset.mem_filter.mp hχ).2
  have hEq := isPrimitive_lift_eq_primitiveCharacter (dvd_refl p) χ hprim
    (DirichletCharacter.changeLevel_self χ)
  rw [← hEq.2.2]

open scoped Classical in
/-- **Factorization of `dedekindZetaC` for a prime cyclotomic field, as punctured germs.** -/
theorem dedekindZetaC_eventuallyEq_riemannZeta_mul_prod_LFunction_of_prime {p : ℕ}
    [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] (s : ℂ) :
    dedekindZetaC K =ᶠ[𝓝[≠] s] fun z ↦
      riemannZeta z * ∏ χ : DirichletCharacter ℂ p with χ ≠ 1, χ.LFunction z := by
  filter_upwards [compl_singleton_one_mem_nhdsWithin_ne s] with z hz
  exact dedekindZetaC_eq_riemannZeta_mul_prod_LFunction_of_prime hz

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
      (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s))) = 1 := by
    refine Finset.prod_eq_one fun χ hχ ↦ ?_
    have hdiv : p ∣ χ.conductor :=
      (DirichletCharacter.dvd_conductor_iff_ne_one_of_prime_pow hp.out χ).mpr
        (Finset.ne_of_mem_erase hχ)
    have hnu : ¬ IsUnit (p : ZMod χ.conductor) :=
      fun hu ↦ (ZMod.isUnit_prime_iff_not_dvd hp.out).mp hu hdiv
    simp [χ.primitiveCharacter.map_nonunit hnu]
  rw [hne, mul_one, h1, one_mul]

/-- **Level-`p ^ k` factorization of `dedekindZetaC` for a prime-power cyclotomic field, as
germs.** -/
theorem dedekindZetaC_mul_one_sub_cpow_eventuallyEq_prod_LFunction_of_prime_pow {p k : ℕ}
    [hp : Fact p.Prime] (hk : k ≠ 0) [IsCyclotomicExtension {p ^ k} ℚ K] (s : ℂ) :
    (fun z ↦ dedekindZetaC K z * (1 - (p : ℂ) ^ (-z))) =ᶠ[𝓝[≠] s]
      fun z ↦ ∏ χ : DirichletCharacter ℂ (p ^ k), χ.LFunction z := by
  filter_upwards [compl_singleton_one_mem_nhdsWithin_ne s] with z hz
  exact dedekindZetaC_mul_one_sub_cpow_eq_prod_LFunction_of_prime_pow hk hz

end PrimeAndPrimePow

end TauCeti.LFunctions
