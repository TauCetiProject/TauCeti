/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.VonMangoldt

/-!
# The Frobenius `ψ` fibres partition Chebyshev's `ψ`

Let `L / K` be a finite Galois extension of number fields with group `G`. A prime power `𝔭 ^ j`
with `𝔭` unramified in `L` lies in the powered Frobenius fibre of exactly one conjugacy class of
`G`, namely `(artinSymbol 𝔭) ^ j`, and a prime power based at a ramified prime lies in none. So the
Frobenius `ψ` functions of all conjugacy classes add up to Chebyshev's `ψ` of `K` with the ramified
primes removed:

```text
∑_C ψ_C(x) + ψ_{ramifiedPrimes K L}(x) = ψ_K(x),
```

and the correction is `O(log x)` because the ramified set is finite.

These identities supply the partition input for the weighted crossing. The later squeeze also
requires the cyclotomic weighted theorem and its consequence `ψ_K(x) / x → 1`.

## Main results

* `NumberField.Chebotarev.sum_frobeniusPrimePowerWeight`: at a single prime power, the Frobenius
  weights of all classes add up to the von Mangoldt weight if the base is unramified, and to `0`
  otherwise.
* `NumberField.Chebotarev.sum_frobeniusPsi_add_primePsi_ramifiedPrimes`: the Frobenius `ψ`
  functions and `ψ` of the ramified primes add up to `ψ_K`.
* `NumberField.Chebotarev.primePsi_univ_sub_sum_frobeniusPsi_isBigO_log`: the Frobenius `ψ`
  functions account for `ψ_K` up to `O(log x)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* S. Lang, *Algebraic Number Theory*, Chapter XV.
-/

public section

namespace NumberField.Chebotarev

open Filter TauCeti
open scoped Asymptotics NumberField
open IsDedekindDomain (HeightOneSpectrum)

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

open scoped Classical in
variable (K L) in
/-- **The Frobenius weights partition the von Mangoldt weight.** At a prime power `𝔭 ^ j`, the
powered Frobenius weights of all conjugacy classes add up to `log N𝔭` when `𝔭` is unramified in
`L`, the only nonzero term being that of `(artinSymbol 𝔭) ^ j`, and to `0` when `𝔭` ramifies. -/
theorem sum_frobeniusPrimePowerWeight (A : IdealPrimePower K) :
    ∑ C : ConjClasses (L ≃ₐ[K] L), frobeniusPrimePowerWeight K L C A =
      {B : IdealPrimePower K | primePowerBase B ∉ ramifiedPrimes K L}.indicator
        primePowerWeight A := by
  by_cases hA : primePowerBase A ∈ ramifiedPrimes K L
  · rw [Set.indicator_of_notMem (by simpa using hA)]
    refine Finset.sum_eq_zero fun C _ ↦ frobeniusPrimePowerWeight_of_notMem ?_
    intro h
    obtain ⟨hur, -⟩ := mem_frobeniusPrimePowerSet_iff.mp h
    exact (mem_ramifiedPrimes_iff _).mp hA hur
  · rw [Set.indicator_of_mem (by simpa using hA)]
    have hur := not_not.mp ((mem_ramifiedPrimes_iff _).not.mp hA)
    rw [Finset.sum_eq_single (artinSymbol (primePowerBase A).asIdeal hur ^ primePowerExponent A)
      (fun C _ hC ↦ frobeniusPrimePowerWeight_of_notMem
        fun h ↦ hC ((mem_frobeniusPrimePowerSet_iff_artinSymbol_pow_eq hur C).mp h).symm)
      (fun h ↦ absurd (Finset.mem_univ _) h)]
    exact frobeniusPrimePowerWeight_of_artinSymbol_pow_eq hur rfl

open scoped Classical in
variable (K L) in
/-- **The Frobenius `ψ` fibres partition Chebyshev's `ψ`.** Summed over all conjugacy classes of
`Gal(L/K)`, the Frobenius `ψ` functions count every prime power based at a prime unramified in `L`
exactly once; adding `ψ` of the finite set `ramifiedPrimes K L` gives `ψ_K`. -/
theorem sum_frobeniusPsi_add_primePsi_ramifiedPrimes (x : ℝ) :
    ∑ C : ConjClasses (L ≃ₐ[K] L), frobeniusPsi K L C x +
        primePsi K (ramifiedPrimes K L : Set (HeightOneSpectrum (𝓞 K))) x =
      primePsi K Set.univ x := by
  simp only [frobeniusPsi_apply, primePsi_apply]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  rw [sum_frobeniusPrimePowerWeight]
  by_cases hA : primePowerBase A ∈ ramifiedPrimes K L <;>
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Finset.mem_coe, Set.mem_univ, hA,
      not_true_eq_false, not_false_eq_true, ite_true, ite_false, zero_add, add_zero]

open scoped Classical in
variable (K L) in
/-- **The Frobenius `ψ` fibres account for `ψ_K` up to `O(log x)`.** The only prime powers missed by
all Frobenius fibres are those based at the finitely many primes of `ramifiedPrimes K L`. -/
theorem primePsi_univ_sub_sum_frobeniusPsi_isBigO_log :
    (fun x : ℝ ↦ primePsi K Set.univ x - ∑ C : ConjClasses (L ≃ₐ[K] L), frobeniusPsi K L C x)
      =O[atTop] Real.log := by
  refine (primePsi_isBigO_log_of_finite (ramifiedPrimes K L).finite_toSet).congr_left fun x ↦ ?_
  rw [← sum_frobeniusPsi_add_primePsi_ramifiedPrimes K L x, add_sub_cancel_left]

end NumberField.Chebotarev
