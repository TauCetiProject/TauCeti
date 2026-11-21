/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Bundled
public import TauCeti.FieldTheory.FunctionField.Belyi.Polynomial.Basic
public import TauCeti.FieldTheory.RatFunc.Substitution

/-!
# Bundled polynomial Belyi pairs

A polynomial `q ∈ k[X]` of positive degree whose critical values lie in `{0, 1}` defines an
algebraic Belyi pair: the rational function field `k(x)` over `k(t)`, with `t = q(x)`
(`TauCeti.IsAlgebraicBelyiPair.of_criticalValues_subset`). As a map of the projective line its
only pole is at `∞`. This file bundles that pair as
`TauCeti.AlgebraicBelyiPair.ofPolynomial q`, with its coordinate `x`, and compares the
isomorphism classes of such pairs: isomorphisms of polynomial pairs are affine changes of variable
(`TauCeti.nonempty_algEquiv_iff_exists_comp_eq`).

## Main definitions

* `TauCeti.AlgebraicBelyiPair.ofPolynomial`: the polynomial Belyi pair `x ↦ q(x)`.
* `TauCeti.AlgebraicBelyiPair.ofPolynomialGen`: its coordinate `x`.
* `TauCeti.AlgebraicBelyiPair.ofPolynomialEquiv`: its function field is `k(x)`.

## Main results

* `TauCeti.AlgebraicBelyiPair.adjoin_ofPolynomialGen` and
  `TauCeti.AlgebraicBelyiPair.algebraMap_ofPolynomial_X`: `x` generates the function field of
  `ofPolynomial q`, and `t = q(x)` on it.
* `TauCeti.AlgebraicBelyiPair.IsoClass.mk_ofPolynomial_eq_mk_ofPolynomial_iff`: two polynomial
  pairs are isomorphic exactly when their polynomials differ by an affine change of variable.

## References

* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer, 2004, §2.2, for Shabat polynomials.
-/

public section

open Polynomial

open scoped IntermediateField

universe u

namespace TauCeti

namespace AlgebraicBelyiPair

variable {k : Type u} [Field k] [CharZero k]

section OfPolynomial

variable (q : k[X]) (hq : 0 < q.natDegree)
  (hcrit : ∀ (L : Type u) [Field L] [Algebra k L], q.criticalValues L ⊆ {0, 1})

/-- **The polynomial Belyi pair** of a polynomial `q ∈ k[X]` of positive degree whose critical
values, in every field extension of `k`, lie in `{0, 1}`: the rational function field `k(x)` over
`k(t)`, with `t = q(x)`. Its Belyi map is `x ↦ q(x)`, whose only pole is at `∞`. -/
noncomputable def ofPolynomial : AlgebraicBelyiPair k :=
  -- `q(x)` is transcendental over `k`, so `t ↦ q(x)` embeds `k(t)` into `k(x)`.
  have ht : Transcendental k (aeval (RatFunc.X : RatFunc k) q) :=
    RatFunc.transcendental_X.aeval q hq.ne' <| mem_nonZeroDivisors_of_ne_zero <|
      leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hq)
  letI := ratFuncAlgebraOfTranscendental ht
  haveI := isScalarTower_ratFuncAlgebraOfTranscendental ht
  have hX : algebraMap (RatFunc k) (RatFunc k) RatFunc.X = aeval RatFunc.X q :=
    algebraMap_ratFuncAlgebraOfTranscendental_X _
  haveI := finiteDimensional_of_aeval_eq RatFunc.adjoin_X hX
  { carrier := RatFunc k
    isAlgebraicBelyiPair := .of_criticalValues_subset RatFunc.adjoin_X hX hcrit }

/-- The coordinate `x` of the polynomial Belyi pair `ofPolynomial q`, on which the Belyi map is
`t = q(x)`. -/
noncomputable def ofPolynomialGen : ofPolynomial q hq hcrit :=
  (RatFunc.X : RatFunc k)

/-- The coordinate `x` generates the function field of `ofPolynomial q` over `k`. -/
theorem adjoin_ofPolynomialGen : k⟮ofPolynomialGen q hq hcrit⟯ = ⊤ :=
  -- The function field of `ofPolynomial q` is `k(X)`, with its usual `k`-algebra structure.
  RatFunc.adjoin_X

/-- On the polynomial Belyi pair `ofPolynomial q`, the function `t` is `q(x)`. -/
@[simp]
theorem algebraMap_ofPolynomial_X :
    algebraMap (RatFunc k) (ofPolynomial q hq hcrit) RatFunc.X =
      aeval (ofPolynomialGen q hq hcrit) q :=
  -- The `k(t)`-algebra structure of `ofPolynomial q` is the one sending `t` to `q(X)`.
  algebraMap_ratFuncAlgebraOfTranscendental_X _

/-- The function field of the polynomial Belyi pair `ofPolynomial q` is the rational function
field `k(x)` in its coordinate `x`: as a `k`-algebra it is `k(X)`, with `x` corresponding to the
variable `X` (`TauCeti.AlgebraicBelyiPair.ofPolynomialEquiv_ofPolynomialGen`). This forgets the
`k(t)`-algebra structure. -/
noncomputable def ofPolynomialEquiv : ofPolynomial q hq hcrit ≃ₐ[k] RatFunc k :=
  -- The function field of `ofPolynomial q` is `k(X)`, with its usual `k`-algebra structure.
  AlgEquiv.refl

@[simp]
theorem ofPolynomialEquiv_ofPolynomialGen :
    ofPolynomialEquiv q hq hcrit (ofPolynomialGen q hq hcrit) = RatFunc.X :=
  (rfl)

@[simp]
theorem ofPolynomialEquiv_symm_X :
    (ofPolynomialEquiv q hq hcrit).symm RatFunc.X = ofPolynomialGen q hq hcrit :=
  (rfl)

namespace IsoClass

variable {q}

/-- **Isomorphic polynomial pairs**: two polynomial Belyi pairs are isomorphic exactly when their
polynomials differ by an affine change of variable, `q' = q(a X + b)` with `a ≠ 0`. -/
theorem mk_ofPolynomial_eq_mk_ofPolynomial_iff {q' : k[X]} (hq' : 0 < q'.natDegree)
    (hcrit' : ∀ (L : Type u) [Field L] [Algebra k L], q'.criticalValues L ⊆ {0, 1}) :
    mk (ofPolynomial q hq hcrit) = mk (ofPolynomial q' hq' hcrit') ↔
      ∃ a b : k, a ≠ 0 ∧ q.comp (C a * X + C b) = q' := by
  rw [mk_eq_mk_iff]
  exact nonempty_algEquiv_iff_exists_comp_eq (adjoin_ofPolynomialGen q hq hcrit)
    (adjoin_ofPolynomialGen q' hq' hcrit') (algebraMap_ofPolynomial_X q hq hcrit)
    (algebraMap_ofPolynomial_X q' hq' hcrit')

end IsoClass

end OfPolynomial

end AlgebraicBelyiPair

end TauCeti
