/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bigraded.PowerSeries
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Poincare.PowerSeries

/-!
# Euler formal power series of unbounded bigraded Ext

For an internally finite pair `(X, Y)` in a `k`-linear abelian category equipped with a shift
autoequivalence `e`, `TauCeti.bigradedExtPoincarePowerSeries` packages all dimensions
`dim_k Extⁿ(X, Y{j})` into a formal power series over `ℤ[q,q⁻¹]`, with no uniform cohomological
vanishing bound.

This file identifies the two specializations from `TauCeti.Algebra.Bigraded.PowerSeries` on that
series:

* When negative internal shifts have no Ext and each nonnegative internal shift `(X, Y{a})` is
  Ext-bounded (with a bound allowed to grow with `a`), the bigraded Poincaré power series satisfies
  `TauCeti.Bigraded.HasEulerPowerSeries`, and the `a`-th coefficient of its Alexander-graded Euler
  power series is the ordinary Ext-Euler characteristic `χ(X, Y{a})`.
* Its Maslov-graded Euler power series has `n`-th coefficient
  `(-1)ⁿ dim_k (⨁ j, Extⁿ(X, Y{j}))`, specializing on diagonally supported Ext to the signed
  diagonal Ext formal power series `∑ n, (-1)ⁿ dim_k Extⁿ(X, Y{n}) tⁿ`.
* When Ext vanishes strictly below the diagonal (`j < n`), equality of the two Euler power series
  is equivalent to off-diagonal Ext vanishing `Extⁿ(X, Y{j}) = 0` for all `n ≠ j`.

## Main results

* `TauCeti.hasEulerPowerSeries_bigradedExtPoincarePowerSeries`: slicewise Ext-boundedness in
  nonnegative internal degrees and vanishing in negative internal degrees supply
  `Bigraded.HasEulerPowerSeries`.
* `TauCeti.coeff_eulerPowerSeries_bigradedExtPoincarePowerSeries`: the `a`-th coefficient of the
  Alexander-graded Euler power series is `extEuler k ha` for `Y{a}`.
* `TauCeti.maslovEulerPowerSeries_bigradedExtPoincarePowerSeries` and
  `TauCeti.maslovEulerPowerSeries_bigradedExtPoincarePowerSeries_of_diagonal`: explicit
  formulas for the Maslov-graded Euler power series in general and on diagonal Ext.
* `TauCeti.eulerPowerSeries_eq_maslovEulerPowerSeries_bigradedExtPoincarePowerSeries_iff`:
  agreement of the two Euler formal power series detects off-diagonal Ext vanishing without a
  cohomological bound.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11.
-/

public section

open scoped DirectSum

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C]
  {k : Type t} [Field k] [Linear k C] [HasExt.{w} C]
  {e : C ≌ C} {X Y : C}

/-- If `Extⁿ(X, Y{j})` vanishes for `j < 0` and each nonnegative internal slice `(X, Y{a})` is
Ext-bounded (with no uniformity required across `a`), then `bigradedExtPoincarePowerSeries`
satisfies `Bigraded.HasEulerPowerSeries`. -/
theorem hasEulerPowerSeries_bigradedExtPoincarePowerSeries
    (h : IsGradedExtInternallyFinite.{w} k e X Y)
    (hneg : ∀ (n : ℕ) {j : ℤ}, j < 0 → Subsingleton (GradedExt.{w} e X Y n j))
    (hbound : ∀ a : ℕ, IsExtBounded.{w} X ((e ^ (a : ℤ)).functor.obj Y)) :
    Bigraded.HasEulerPowerSeries (bigradedExtPoincarePowerSeries k e h) where
  coeff_eq_zero_of_neg n a ha := by
    let _ := hneg n ha
    rw [coeff_coeff_bigradedExtPoincarePowerSeries, Module.finrank_zero_of_subsingleton,
      Nat.cast_zero]
  finite_support a := by
    obtain ⟨N, hN⟩ := (hbound a).exists_bound
    refine (Finset.range N).finite_toSet.subset fun n hn ↦ ?_
    simp only [Set.mem_ofPred_eq, coeff_coeff_bigradedExtPoincarePowerSeries] at hn
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hge
    let _ := hN.subsingleton (Nat.le_of_not_lt hge)
    exact hn (by simp [Module.finrank_zero_of_subsingleton])

/-- Each coefficient of the Alexander-graded Euler formal power series of
`bigradedExtPoincarePowerSeries` is the ordinary Ext-Euler characteristic `χ(X, Y{a})` of the
corresponding internal target shift. -/
theorem coeff_eulerPowerSeries_bigradedExtPoincarePowerSeries
    (h : IsGradedExtInternallyFinite.{w} k e X Y)
    (hP : Bigraded.HasEulerPowerSeries (bigradedExtPoincarePowerSeries k e h)) (a : ℕ)
    (ha : IsEulerAdmissible.{w} k X ((e ^ (a : ℤ)).functor.obj Y)) :
    PowerSeries.coeff a (Bigraded.eulerPowerSeries hP) = extEuler.{w} k ha := by
  obtain ⟨N, hN⟩ := ha.isExtBounded.exists_bound
  rw [Bigraded.coeff_eulerPowerSeries_eq_sum hP a N (fun n hn ↦ by
      let _ := hN.subsingleton hn
      rw [coeff_coeff_bigradedExtPoincarePowerSeries, Module.finrank_zero_of_subsingleton,
        Nat.cast_zero]),
    extEuler_eq k ha hN, truncatedExtEuler_def]
  simp only [coeff_coeff_bigradedExtPoincarePowerSeries]

/-- The Maslov-graded Euler formal power series of `bigradedExtPoincarePowerSeries` has `n`-th
coefficient `(-1)ⁿ dim_k (⨁ j, Extⁿ(X, Y{j}))`. -/
theorem maslovEulerPowerSeries_bigradedExtPoincarePowerSeries
    (h : IsGradedExtInternallyFinite.{w} k e X Y) :
    Bigraded.maslovEulerPowerSeries (bigradedExtPoincarePowerSeries k e h) =
      PowerSeries.mk fun n ↦ (-1 : ℤ) ^ n * Module.finrank k (⨁ j, GradedExt.{w} e X Y n j) := by
  rw [Bigraded.maslovEulerPowerSeries_apply,
    rescale_neg_one_map_laurentEval_one_bigradedExtPoincarePowerSeries]

/-- On a diagonally supported Ext Poincaré series, `Bigraded.maslovEulerPowerSeries` specializes to
the signed formal power series of diagonal Ext dimensions `(-1)ⁿ dim_k Extⁿ(X, Y{n})`. -/
theorem maslovEulerPowerSeries_bigradedExtPoincarePowerSeries_of_diagonal
    (h : IsGradedExtInternallyFinite.{w} k e X Y)
    (hdiag : ∀ (n : ℕ) (j : ℤ), (n : ℤ) ≠ j →
      (PowerSeries.coeff n (bigradedExtPoincarePowerSeries k e h)).coeff j = 0) :
    Bigraded.maslovEulerPowerSeries (bigradedExtPoincarePowerSeries k e h) =
      PowerSeries.rescale (-1 : ℤ)
        (PowerSeries.mk fun n ↦ (Module.finrank k (GradedExt.{w} e X Y n n) : ℤ)) := by
  rw [Bigraded.maslovEulerPowerSeries_apply,
    map_laurentEval_one_bigradedExtPoincarePowerSeries_of_diagonal h hdiag]

/-- When `Extⁿ(X, Y{j})` vanishes strictly below the diagonal (`j < n`), the Alexander-graded and
Maslov-graded Euler formal power series of `bigradedExtPoincarePowerSeries` coincide if and only if
all off-diagonal Ext groups vanish. -/
theorem eulerPowerSeries_eq_maslovEulerPowerSeries_bigradedExtPoincarePowerSeries_iff
    (h : IsGradedExtInternallyFinite.{w} k e X Y)
    (hP : Bigraded.HasEulerPowerSeries (bigradedExtPoincarePowerSeries k e h))
    (hl : ∀ (n : ℕ) (j : ℤ), j < n →
      (PowerSeries.coeff n (bigradedExtPoincarePowerSeries k e h)).coeff j = 0) :
    Bigraded.eulerPowerSeries hP =
        Bigraded.maslovEulerPowerSeries (bigradedExtPoincarePowerSeries k e h) ↔
      ∀ (n : ℕ) (j : ℤ), (n : ℤ) ≠ j → Subsingleton (GradedExt.{w} e X Y n j) := by
  rw [Bigraded.eulerPowerSeries_eq_maslovEulerPowerSeries_iff hP
      (fun n j ↦ by
        rw [coeff_coeff_bigradedExtPoincarePowerSeries]
        exact Int.natCast_nonneg _)
      hl,
    diagonal_bigradedExtPoincarePowerSeries_iff]

end TauCeti
