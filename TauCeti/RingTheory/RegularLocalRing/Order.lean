/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Ideal.Order
public import Mathlib.RingTheory.RegularLocalRing.Defs
import TauCeti.RingTheory.RegularLocalRing.AssociatedGraded

/-!
# Multiplicativity of ideal order in regular local rings

In a regular local ring `(R, 𝔪)`, the associated graded ring `gr_𝔪 R` is a domain, so initial
forms multiply (`TauCeti.IsRegularLocalRing.mul_notMem_maximalIdeal_pow_succ`). Combining this with
Krull's intersection theorem yields multiplicativity of local ideal order:

`ord(I * J) = ord(I) + ord(J)` and `ord(I ^ n) = n • ord(I)`

for all ideals `I, J` and all `n : ℕ`, including zero ideals (order `∞`) and `n = 0` (unit ideal,
order `0`). No equicharacteristic hypothesis is needed; in particular these formulas apply to
mixed-characteristic regular local rings such as `ℤ_(p)`.

Localizing at a prime `p` whose localization is regular local gives the same formulas for
`Ideal.orderAt`: `ord_p(I * J) = ord_p(I) + ord_p(J)` and `ord_p(I ^ n) = n • ord_p(I)`.

## Main results

* `Ideal.localOrder_mul`: over a regular local ring,
  `(I * J).localOrder = I.localOrder + J.localOrder`.
* `Ideal.localOrder_pow`: over a regular local ring, `(I ^ n).localOrder = n • I.localOrder`.
* `Ideal.localOrder_prod`: over a regular local ring, the local order of a finite product of ideals
  is the sum of their local orders.
* `Ideal.orderAt_mul`: at a prime with regular localization,
  `(I * J).orderAt p = I.orderAt p + J.orderAt p`.
* `Ideal.orderAt_pow`: at a prime with regular localization, `(I ^ n).orderAt p = n • I.orderAt p`.
* `Ideal.orderAt_prod`: at a prime with regular localization, the order of a finite product of
  ideals is the sum of their orders.

## References

* [The Stacks Project, Lemma 10.106.1](https://stacks.math.columbia.edu/tag/00NO).
* E. Bierstone and P. D. Milman, *Canonical desingularization in characteristic zero by blowing
  up the maximum strata of a local invariant*, Invent. Math. 128 (1997), §4.1–4.2, p. 241.
-/

public section

namespace Ideal

open IsLocalRing

section RegularLocal

variable {R : Type*} [CommRing R] [IsRegularLocalRing R]

/-- **Multiplicativity of local ideal order.** In a regular local ring, the local order of a
product of ideals is the sum of their local orders, including zero ideals with order `∞`. -/
theorem localOrder_mul (I J : Ideal R) :
    (I * J).localOrder = I.localOrder + J.localOrder := by
  refine le_antisymm ?_ (le_localOrder_mul I J)
  cases hI : I.localOrder with
  | top => simp
  | coe a =>
    cases hJ : J.localOrder with
    | top => simp
    | coe b =>
      obtain ⟨x, hxI, hxa, hxa'⟩ := exists_mem_notMem_maximalIdeal_pow_succ hI
      obtain ⟨y, hyJ, hyb, hyb'⟩ := exists_mem_notMem_maximalIdeal_pow_succ hJ
      have hxy_mem : x * y ∈ I * J := mul_mem_mul hxI hyJ
      have hxy_not : x * y ∉ maximalIdeal R ^ (a + b + 1) :=
        TauCeti.IsRegularLocalRing.mul_notMem_maximalIdeal_pow_succ hxa hxa' hyb hyb'
      by_contra hlt
      have hsucc : ((a + b + 1 : ℕ) : ℕ∞) ≤ (I * J).localOrder := by
        rw [Nat.cast_add, Nat.cast_one, ENat.natCast_add_one_le_iff]
        simpa only [Nat.cast_add] using lt_of_not_ge hlt
      exact hxy_not ((natCast_le_localOrder_iff (I * J) (a + b + 1)).mp hsucc hxy_mem)

/-- **Power formula for local ideal order.** In a regular local ring, the local order of `I ^ n`
is `n • I.localOrder`, for every `n : ℕ` and every ideal `I` (including `I = ⊥` and `n = 0`). -/
theorem localOrder_pow (I : Ideal R) (n : ℕ) :
    (I ^ n).localOrder = n • I.localOrder := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, localOrder_mul, ih, succ_nsmul]

/-- In a regular local ring, the local order of a finite product of ideals is the sum of their
local orders. -/
theorem localOrder_prod {ι : Type*} (s : Finset ι) (I : ι → Ideal R) :
    (∏ i ∈ s, I i).localOrder = ∑ i ∈ s, (I i).localOrder := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, localOrder_mul, ih]

end RegularLocal

section AtPrime

variable {R : Type*} [CommRing R]

/-- **Multiplicativity of ideal order at a regular prime.** At a prime whose localization is a
regular local ring, the order of a product of ideals is the sum of their orders. -/
theorem orderAt_mul (I J : Ideal R) (p : PrimeSpectrum R)
    [IsRegularLocalRing (Localization.AtPrime p.asIdeal)] :
    (I * J).orderAt p = I.orderAt p + J.orderAt p := by
  simpa only [orderAt_def, Ideal.map_mul] using localOrder_mul
    (I.map (algebraMap R (Localization.AtPrime p.asIdeal)))
    (J.map (algebraMap R (Localization.AtPrime p.asIdeal)))

/-- **Power formula for ideal order at a regular prime.** At a prime whose localization is a
regular local ring, the order of `I ^ n` is `n • I.orderAt p`. -/
theorem orderAt_pow (I : Ideal R) (p : PrimeSpectrum R)
    [IsRegularLocalRing (Localization.AtPrime p.asIdeal)] (n : ℕ) :
    (I ^ n).orderAt p = n • I.orderAt p := by
  simpa only [orderAt_def, Ideal.map_pow] using localOrder_pow
    (I.map (algebraMap R (Localization.AtPrime p.asIdeal))) n

/-- At a prime whose localization is a regular local ring, the order of a finite product of ideals
is the sum of their orders. -/
theorem orderAt_prod {ι : Type*} (s : Finset ι) (I : ι → Ideal R) (p : PrimeSpectrum R)
    [IsRegularLocalRing (Localization.AtPrime p.asIdeal)] :
    (∏ i ∈ s, I i).orderAt p = ∑ i ∈ s, (I i).orderAt p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, orderAt_mul, ih]

end AtPrime

end Ideal
