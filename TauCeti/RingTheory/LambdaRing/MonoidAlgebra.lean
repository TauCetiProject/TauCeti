/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import TauCeti.Algebra.MonoidAlgebra.Basic
public import TauCeti.RingTheory.LambdaRing.Basic
import TauCeti.RingTheory.Binomial

/-!
# The line-monomial pre-λ structure on a monoid algebra

For a commutative monoid `M`, the integral monoid algebra `ℤ[M]` carries a unique pre-λ
structure in which every basis monomial `[m]` is a line element, `λ_t [m] = 1 + [m] t`. Since
the total operation turns sums into products, it is

```text
λ_t (∑ cₘ [m]) = ∏ (1 + [m] t) ^ cₘ,
```

and on an integral multiple of a monomial `λⁿ (c [m]) = (c choose n) [mⁿ]`. This is the
λ-structure of a representation ring of a diagonalizable group, whose characters are lines; for
the trivial monoid it is the binomial structure on `ℤ`. Laurent polynomials `ℤ[u, u⁻¹]` and
polynomials `ℤ[u]` are the cases `M = Multiplicative ℤ` and `M = Multiplicative ℕ`.

## Main definitions

* `TauCeti.PreLambdaStructure.lineMonomial M`: the line-monomial structure on `ℤ[M]`.
* `TauCeti.PreLambdaStructure.lineMonomialMapDomain`: the map `ℤ[M] → ℤ[N]` induced by a
  monoid homomorphism `M →* N`, as a morphism of line-monomial structures.

## Main results

* `TauCeti.PreLambdaStructure.lineMonomial_lambda_single`: `λⁿ (c [m]) = (c choose n) [mⁿ]`.
* `TauCeti.PreLambdaStructure.isLine_lineMonomial_of`: basis monomials are line elements.
* `TauCeti.PreLambdaStructure.eq_lineMonomial`: uniqueness, among pre-λ structures on `ℤ[M]` in
  which every basis monomial is a line element.

## References

* C. A. Weibel, *The K-book*, §II.4 and its exercises.
-/

public noncomputable section

open PowerSeries MonoidAlgebra

namespace TauCeti

namespace PreLambdaStructure

variable (M : Type*) [CommMonoid M] {N : Type*} [CommMonoid N]

/-- The total operation of the line-monomial structure: `∑ cₘ [m] ↦ ∏ (1 + [m] t) ^ cₘ`, where
`(1 + [m] t) ^ c` is the binomial series `(1 + t) ^ c` rescaled by `[m]`. -/
private def lineMonomialTotal : Multiplicative (MonoidAlgebra ℤ M) →* (MonoidAlgebra ℤ M)⟦X⟧ where
  toFun x := x.toAdd.coeff.prod fun m c => rescale (of ℤ M m) (binomialSeries _ c)
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, coeff_add]
    exact Finsupp.prod_add_index' (by simp) (by simp [binomialSeries_add])

private theorem lineMonomialTotal_single (m : M) (c : ℤ) :
    lineMonomialTotal M (Multiplicative.ofAdd (single m c)) =
      rescale (of ℤ M m) (binomialSeries _ c) := by
  simp [lineMonomialTotal, Finsupp.prod_single_index]

private theorem coeff_lineMonomialTotal_single (n : ℕ) (m : M) (c : ℤ) :
    coeff n (lineMonomialTotal M (Multiplicative.ofAdd (single m c))) =
      single (m ^ n) (Ring.choose c n) := by
  rw [lineMonomialTotal_single]
  simp [coeff_rescale, binomialSeries_coeff, of_apply, single_pow, intCast_def]

private theorem constantCoeff_lineMonomialTotal (x : Multiplicative (MonoidAlgebra ℤ M)) :
    constantCoeff (lineMonomialTotal M x) = 1 := by
  induction x using Multiplicative.rec with | ofAdd x => ?_
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [ofAdd_add, map_mul, map_mul, hx, hy, mul_one]
  | single m c =>
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_lineMonomialTotal_single]
    simp [one_def]

private theorem coeff_one_lineMonomialTotal (x : Multiplicative (MonoidAlgebra ℤ M)) :
    coeff 1 (lineMonomialTotal M x) = x.toAdd := by
  induction x using Multiplicative.rec with | ofAdd x => ?_
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [ofAdd_add, map_mul, coeff_one_mul, constantCoeff_lineMonomialTotal,
      constantCoeff_lineMonomialTotal, hx, hy]
    simp
  | single m c => simp [coeff_lineMonomialTotal_single]

/-- The line-monomial pre-λ structure on the integral monoid algebra `ℤ[M]` of a commutative
monoid: the unique pre-λ structure in which every basis monomial `[m]` is a line element. -/
def lineMonomial : PreLambdaStructure (MonoidAlgebra ℤ M) :=
  ofTotalHom (lineMonomialTotal M) (constantCoeff_lineMonomialTotal M)
    (coeff_one_lineMonomialTotal M)

variable {M}

/-- The operations of the line-monomial structure on an integral multiple of a monomial:
`λⁿ (c [m]) = (c choose n) [mⁿ]`. -/
@[simp]
theorem lineMonomial_lambda_single (n : ℕ) (m : M) (c : ℤ) :
    (lineMonomial M).lambda n (single m c) = single (m ^ n) (Ring.choose c n) := by
  simp [lineMonomial, coeff_lineMonomialTotal_single]

/-- The total operation of the line-monomial structure on an integral multiple of a monomial is
the binomial series `(1 + [m] t) ^ c`. -/
theorem totalSeries_lineMonomial_single (m : M) (c : ℤ) :
    (lineMonomial M).totalSeries (single m c) = rescale (of ℤ M m) (binomialSeries _ c) := by
  ext n
  rw [coeff_totalSeries, lineMonomial_lambda_single, ← coeff_lineMonomialTotal_single,
    lineMonomialTotal_single]

/-- Every basis monomial is a line element of the line-monomial structure. -/
theorem isLine_lineMonomial_of (m : M) : (lineMonomial M).IsLine (of ℤ M m) := by
  refine (isLine_iff _).2 fun n hn => ?_
  rw [of_apply, lineMonomial_lambda_single, Ring.choose_one_of_two_le ℤ hn, single_zero]

theorem totalSeries_lineMonomial_of (m : M) :
    (lineMonomial M).totalSeries (of ℤ M m) = 1 + C (of ℤ M m) * X :=
  (isLine_lineMonomial_of m).totalSeries_eq

/-- Uniqueness of the line-monomial structure: a pre-λ structure on `ℤ[M]` in which every basis
monomial is a line element is the line-monomial structure. -/
theorem eq_lineMonomial {Λ : PreLambdaStructure (MonoidAlgebra ℤ M)}
    (h : ∀ m, Λ.IsLine (of ℤ M m)) : Λ = lineMonomial M := by
  refine ext_of_closure addSubgroupClosure_range_of ?_
  rintro _ ⟨m, rfl⟩
  rw [(h m).totalSeries_eq, totalSeries_lineMonomial_of]

/-- The map of monoid algebras induced by a monoid homomorphism, as a morphism of line-monomial
structures. -/
def lineMonomialMapDomain (f : M →* N) : PreLambdaHom (lineMonomial M) (lineMonomial N) :=
  PreLambdaHom.ofClosure (mapDomainRingHom ℤ f) addSubgroupClosure_range_of <| by
    rintro _ ⟨m, rfl⟩
    have hf : mapDomainRingHom ℤ f (of ℤ M m) = of ℤ N (f m) := by simp [of_apply]
    simp [-of_apply, totalSeries_lineMonomial_of, hf]

@[simp]
theorem coe_lineMonomialMapDomain (f : M →* N) :
    ⇑(lineMonomialMapDomain f) = mapDomainRingHom ℤ f :=
  PreLambdaHom.coe_ofClosure _ _ _

end PreLambdaStructure

end TauCeti
