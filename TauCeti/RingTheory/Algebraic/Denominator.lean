/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Algebraic.Denominator
public import Mathlib.RingTheory.Localization.Integral

/-!
# Denominators of integral elements

The *denominator* `Algebra.natDenominator x` of an element `x` of a commutative ring is the
absolute value of a generator of the ideal of integers `n` with `n • x` integral over `ℤ`
(`Algebra.natDenominator_dvd_iff`); it is `0` when `x` is transcendental over `ℤ`. The denominator
of `x` is `1` exactly when `x` is itself integral over `ℤ`
(`Algebra.natDenominator_eq_one_iff`), that is, when every integer multiple of `x` is integral over
`ℤ`. In a `ℚ`-algebra, an element algebraic over `ℚ` is algebraic over `ℤ`, so it has a nonzero
denominator (`Algebra.natDenominator_ne_zero_of_isAlgebraic_rat`), and the denominator of a
transcendental element is `0`: over any commutative ring the denominator is nonzero exactly for
elements algebraic over `ℤ` (`Algebra.natDenominator_ne_zero_iff_isAlgebraic`), and in a
`ℚ`-algebra exactly for elements algebraic over `ℚ`
(`Algebra.natDenominator_ne_zero_iff_isAlgebraic_rat`).

## Main results

* `Algebra.natDenominator_eq_one_iff`: `natDenominator x = 1` iff `x` is integral over `ℤ`.
* `Algebra.natDenominator_ne_zero_of_isAlgebraic_rat`: the denominator of an element of a
  `ℚ`-algebra that is algebraic over `ℚ` is nonzero.
* `Algebra.natDenominator_ne_zero_iff_isAlgebraic`: the denominator of `x` is nonzero exactly when
  `x` is algebraic over `ℤ`.
* `Algebra.natDenominator_ne_zero_iff_isAlgebraic_rat`: in a `ℚ`-algebra, the denominator of `x`
  is nonzero exactly when `x` is algebraic over `ℚ`.
* `Algebra.exists_ne_zero_nsmul_isIntegral`,
  `Algebra.exists_ne_zero_nsmul_isIntegral_of_isAlgebraic_rat`: a finite family of algebraic
  elements admits a common nonzero natural scalar making every entry integral over `ℤ`.
-/

public section

namespace Algebra

/-- The denominator of `x` is one exactly when `x` is integral over `ℤ`: then every integer
multiple of `x` is integral over `ℤ`. -/
@[simp]
theorem natDenominator_eq_one_iff {S : Type*} [CommRing S] {x : S} :
    natDenominator x = 1 ↔ IsIntegral ℤ x := by
  rw [← Nat.dvd_one, natDenominator_dvd_iff, one_smul]

/-- The denominator of `x` is nonzero when `x` is algebraic over `ℚ`: in a `ℚ`-algebra, being
algebraic over `ℚ` and being algebraic over `ℤ` are equivalent. -/
theorem natDenominator_ne_zero_of_isAlgebraic_rat {S : Type*} [CommRing S] [Algebra ℚ S] {x : S}
    (hx : IsAlgebraic ℚ x) : natDenominator x ≠ 0 :=
  IsAlgebraic.natDenominator_ne_zero ((IsFractionRing.isAlgebraic_iff ℤ ℚ S).2 hx)

/-- The denominator of `x` is nonzero exactly when `x` is algebraic over `ℤ`; a transcendental
element has denominator `0`. -/
theorem natDenominator_ne_zero_iff_isAlgebraic {S : Type*} [CommRing S] {x : S} :
    natDenominator x ≠ 0 ↔ IsAlgebraic ℤ x := by
  refine ⟨fun h ↦ ?_, IsAlgebraic.natDenominator_ne_zero⟩
  have hint : IsIntegral ℤ ((natDenominator x : ℤ) • x) := by
    simpa only [natCast_zsmul] using isIntegral_natDenominator_smul x
  exact hint.isAlgebraic.of_smul (mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast h))

/-- In a `ℚ`-algebra, the denominator of `x` is nonzero exactly when `x` is algebraic over `ℚ`. -/
theorem natDenominator_ne_zero_iff_isAlgebraic_rat {S : Type*} [CommRing S] [Algebra ℚ S] {x : S} :
    natDenominator x ≠ 0 ↔ IsAlgebraic ℚ x :=
  natDenominator_ne_zero_iff_isAlgebraic.trans (IsFractionRing.isAlgebraic_iff ℤ ℚ S)

/-- Given a finite family `x` over `s` of elements algebraic over `ℤ`, there is a nonzero natural
number `n` (namely `∏ i ∈ s, natDenominator (x i)`) such that `n • x i` is integral over `ℤ` for
every `i ∈ s`. -/
theorem exists_ne_zero_nsmul_isIntegral {S ι : Type*} [CommRing S] (s : Finset ι) (x : ι → S)
    (hx : ∀ i ∈ s, IsAlgebraic ℤ (x i)) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ i ∈ s, IsIntegral ℤ (n • x i) :=
  ⟨∏ i ∈ s, natDenominator (x i),
    Finset.prod_ne_zero_iff.mpr fun i hi ↦ (hx i hi).natDenominator_ne_zero,
    fun _ hi ↦ natDenominator_dvd_iff.mp (Finset.dvd_prod_of_mem _ hi)⟩

/-- Given a finite family `x` over `s` of elements of a `ℚ`-algebra that are algebraic over `ℚ`,
there is a nonzero natural number `n` such that `n • x i` is integral over `ℤ` for every
`i ∈ s`. -/
theorem exists_ne_zero_nsmul_isIntegral_of_isAlgebraic_rat {S ι : Type*} [CommRing S]
    [Algebra ℚ S] (s : Finset ι) (x : ι → S) (hx : ∀ i ∈ s, IsAlgebraic ℚ (x i)) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ i ∈ s, IsIntegral ℤ (n • x i) :=
  exists_ne_zero_nsmul_isIntegral s x fun i hi ↦ (IsFractionRing.isAlgebraic_iff ℤ ℚ S).2 (hx i hi)

end Algebra
