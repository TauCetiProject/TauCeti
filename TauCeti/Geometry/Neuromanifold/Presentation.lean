/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Basic
public import TauCeti.Geometry.Neuromanifold.Polynomial
public import TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree
public import TauCeti.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Faithful coefficient presentations of polynomial models

A presentation of a realization map `f : W → X → Y` is a coefficient map `c : W → V` together
with an evaluation `E : V → X → Y` satisfying `E (c w) = f w`; the comparisons for a faithful
(injective) presentation are in `TauCeti.Geometry.Neuromanifold.Basic`. This file specialises
them to jointly polynomial models.

For a jointly polynomial tuple `P`, the coefficient space is the product, over output
coordinates, of the polynomials in the inputs of total degree at most `d`. Evaluating these
polynomials is the linear map `polynomialEvaluation d`, which is injective over an infinite
integral domain, and `polynomialCoefficientMap P` is a coefficient map for
`polynomialRealization P` against it. With finitely many input variables, the monomial
coefficients give the linear equivalence `coefficientCoordinates J d` with the finite coordinate
space indexed by pairs of an output coordinate and an exponent vector of degree at most `d`. In
these coordinates the coefficient map of `P` has polynomial coordinates in the parameters.

Over an infinite integral domain, evaluation is faithful for every degree bound. Over a finite
field it can fail to be faithful, since distinct polynomials of large degree can define the same
function. A presentation by sampled outputs is not automatically faithful.

The jointly polynomial setting and its finite ambient coefficient space follow
Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3.1.
Faithfulness of evaluation is Mathlib's `MvPolynomial.funext`, and the coordinates come from the
monomial basis `MvPolynomial.basisRestrictTotalDegree` and Mathlib's `Pi.basis`.
-/

public section

noncomputable section

namespace TauCeti.Neuromanifold

open MvPolynomial

section Evaluation

variable {K X J : Type*} [CommSemiring K]

variable (J) in
/-- Evaluation of a tuple, indexed by output coordinates `J`, of polynomials of total degree at
most `d` in the input variables `X`. -/
def polynomialEvaluation (d : ℕ) : (J → restrictTotalDegree X K d) →ₗ[K] (X → K) → J → K where
  toFun q x j := eval x (q j : MvPolynomial X K)
  map_add' q r := by
    funext x j
    simp
  map_smul' a q := by
    funext x j
    simp

/-- Coordinate evaluation of a tuple of bounded-degree polynomials. -/
@[simp] theorem polynomialEvaluation_apply (d : ℕ) (q : J → restrictTotalDegree X K d)
    (x : X → K) (j : J) :
    polynomialEvaluation J d q x j = eval x (q j : MvPolynomial X K) := (rfl)

/-- Over an infinite integral domain, evaluation of bounded-degree polynomial tuples is
faithful. -/
theorem polynomialEvaluation_injective {K : Type*} [CommRing K] [IsDomain K] [Infinite K]
    (d : ℕ) : Function.Injective (polynomialEvaluation (K := K) (X := X) J d) := by
  intro q r h
  funext j
  exact Subtype.ext <| MvPolynomial.funext fun x => congrFun (congrFun h x) j

variable {W : Type*} [Fintype J]

/-- Evaluating the polynomial coefficient map of `P` recovers the realization map of `P`, with
no infinitude assumption on the scalars. -/
@[simp] theorem polynomialEvaluation_polynomialCoefficientMap
    (P : J → MvPolynomial (W ⊕ X) K) (w : W → K) :
    polynomialEvaluation J _ (polynomialCoefficientMap P w) = polynomialRealization P w := by
  funext x j
  rw [polynomialEvaluation_apply, polynomialCoefficientMap_coe, eval_map, eval₂_inputPolynomial]

/-- The functions realized by a jointly polynomial tuple are the evaluations of its coefficient
image. -/
theorem realizedFunctions_polynomialRealization (P : J → MvPolynomial (W ⊕ X) K) :
    realizedFunctions (polynomialRealization P) =
      polynomialEvaluation J _ '' Set.range (polynomialCoefficientMap P) :=
  realizedFunctions_eq_image_range (polynomialEvaluation_polynomialCoefficientMap P)

section Faithful

variable {K : Type*} [CommRing K] [IsDomain K] [Infinite K]

/-- Over an infinite integral domain, parameters of a jointly polynomial tuple realize the same
function exactly when they have the same input coefficients. -/
theorem polynomialCoefficientMap_eq_iff (P : J → MvPolynomial (W ⊕ X) K) {w v : W → K} :
    polynomialCoefficientMap P w = polynomialCoefficientMap P v ↔
      polynomialRealization P w = polynomialRealization P v :=
  apply_eq_apply_iff_of_injective (polynomialEvaluation_injective _)
    (polynomialEvaluation_polynomialCoefficientMap P)

/-- Over an infinite integral domain, the realization fibre of a jointly polynomial tuple over
the evaluation of `q` is the coefficient fibre over `q`. -/
theorem fiber_polynomialRealization_polynomialEvaluation (P : J → MvPolynomial (W ⊕ X) K)
    (q : J → restrictTotalDegree X K (polynomialInputDegree P)) :
    fiber (polynomialRealization P) (polynomialEvaluation J _ q) =
      polynomialCoefficientMap P ⁻¹' {q} :=
  fiber_apply_eq_preimage (polynomialEvaluation_injective _)
    (polynomialEvaluation_polynomialCoefficientMap P) q

end Faithful

end Evaluation

section Coordinates

variable {K X J : Type*} [CommSemiring K] [Finite X] [Fintype J]

variable (K X J) in
/-- The monomial coefficient coordinates of a tuple, indexed by output coordinates `J`, of
polynomials of total degree at most `d` in finitely many input variables `X`. The coordinate
space is indexed by pairs of an output coordinate and an exponent vector of degree at most `d`. -/
def coefficientCoordinates (d : ℕ) :
    (J → restrictTotalDegree X K d) ≃ₗ[K] (J × {s : X →₀ ℕ // s.degree ≤ d} → K) :=
  ((Pi.basis fun _ : J => basisRestrictTotalDegree X K d).reindex
    (Equiv.sigmaEquivProd _ _)).equivFun

/-- The coordinate of a polynomial tuple at `(j, s)` is the coefficient of `X ^ s` in its
`j`-th polynomial. -/
@[simp] theorem coefficientCoordinates_apply (d : ℕ) (q : J → restrictTotalDegree X K d)
    (i : J × {s : X →₀ ℕ // s.degree ≤ d}) :
    coefficientCoordinates K X J d q i = (q i.1 : MvPolynomial X K).coeff i.2 := by
  simp [coefficientCoordinates]

/-- The polynomial tuple with prescribed coordinates has the prescribed coefficients. -/
@[simp] theorem coeff_coefficientCoordinates_symm_apply (d : ℕ)
    (a : J × {s : X →₀ ℕ // s.degree ≤ d} → K) (j : J) (s : {s : X →₀ ℕ // s.degree ≤ d}) :
    ((coefficientCoordinates K X J d).symm a j : MvPolynomial X K).coeff s = a (j, s) := by
  rw [← coefficientCoordinates_apply d ((coefficientCoordinates K X J d).symm a) (j, s),
    LinearEquiv.apply_symm_apply]

/-- In monomial coordinates, the coefficient map of a jointly polynomial tuple is polynomial in
the parameters: each coordinate is the evaluation of an input coefficient. -/
theorem coefficientCoordinates_polynomialCoefficientMap {W : Type*}
    (P : J → MvPolynomial (W ⊕ X) K) (w : W → K) (i : J × {s : X →₀ ℕ // s.degree ≤ _}) :
    coefficientCoordinates K X J _ (polynomialCoefficientMap P w) i =
      eval w ((inputPolynomial P i.1).coeff i.2) := by
  rw [coefficientCoordinates_apply, coeff_polynomialCoefficientMap]

end Coordinates

end TauCeti.Neuromanifold
