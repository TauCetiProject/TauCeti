/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Neurovariety
public import TauCeti.Geometry.Neuromanifold.Polynomial.Homogeneous

/-!
# Neurovarieties of polynomial models do not depend on the presentation

A jointly polynomial model `P` has finite coefficient coordinates
`polynomialCoefficientCoordinates P`, indexed by an output and an input exponent of degree at most
the uniform input-degree bound. Its neurovariety and the algebraicity of its coefficient image are
defined in these coordinates. This file shows that they do not depend on that choice.

* Raising the degree bound zero-pads the coordinates. For any parametrization in bounded-degree
  coordinates, the padding transports the neurovariety and preserves and reflects algebraicity
  (`neurovariety_boundedCoefficientPadding_comp`,
  `isAlgebraicImage_boundedCoefficientPadding_comp_iff`).
* When every input polynomial is homogeneous of degree `d`, the homogeneous coordinates
  `polynomialHomogeneousCoefficientCoordinates P hP` give the same neurovariety up to extension by
  zero, and the same algebraicity of the image.
* Over an infinite field, any faithful linear presentation of the realization map in finitely many
  coordinates, for instance one obtained by a change of basis, is a linear function of the monomial
  coordinates which restricts to a bijection between the two neurovarieties
  (`exists_linearMap_comp_eq_bijOn_neurovariety_polynomialCoefficientCoordinates`), and has
  algebraic coefficient image exactly when the monomial coordinates do
  (`isAlgebraicImage_polynomialCoefficientCoordinates_iff_of_injective`).

The first two items hold over every field. The last needs the realization map to determine its
coefficients, which is why the field is infinite there; over a finite field evaluation need not be
faithful.

The neurovariety is the Zariski closure of the coefficient image, following
Finkel–Rodriguez–Wu–Yahl, *Activation degree thresholds and expressiveness of polynomial neural
networks*, [arXiv:2408.04569v4](https://arxiv.org/abs/2408.04569v4), §1.1, equations (3)–(4);
the finite coefficient space of a jointly polynomial model is that of
Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3.1.
-/

public section

namespace TauCeti.Neuromanifold

open MvPolynomial

variable {K W X J : Type*} [Field K] [Finite X]

section Padding

variable {V : Type*} {d e : ℕ}

/-- Raising the degree bound of a parametrization in bounded-degree coefficient coordinates
transports its neurovariety along the zero-padding. -/
theorem neurovariety_boundedCoefficientPadding_comp (h : d ≤ e)
    (c : V → J × {s : X →₀ ℕ // s.degree ≤ d} → K) :
    neurovariety (boundedCoefficientPadding h ∘ c) =
      boundedCoefficientPadding h '' neurovariety c := by
  rw [boundedCoefficientPadding_eq_extendByZero_linearMap]
  exact neurovariety_extendByZero_comp
    (Function.injective_id.prodMap (Subtype.impEmbedding _ _ _).injective) c

/-- Raising the degree bound of a parametrization in bounded-degree coefficient coordinates
preserves and reflects algebraicity of its coefficient image. -/
theorem isAlgebraicImage_boundedCoefficientPadding_comp_iff (h : d ≤ e)
    {c : V → J × {s : X →₀ ℕ // s.degree ≤ d} → K} :
    IsAlgebraicImage (boundedCoefficientPadding h ∘ c) ↔ IsAlgebraicImage c := by
  rw [boundedCoefficientPadding_eq_extendByZero_linearMap]
  exact isAlgebraicImage_extendByZero_comp_iff
    (Function.injective_id.prodMap (Subtype.impEmbedding _ _ _).injective)

end Padding

variable [Fintype J]

section Homogeneous

variable {d : ℕ}

/-- For a model whose input polynomials are homogeneous of degree `d`, padding the neurovariety
in bounded-degree coordinates up to the bound `d` gives the neurovariety in homogeneous
coordinates, extended by zero. -/
theorem
  image_boundedCoefficientPadding_neurovariety_polynomialCoefficientCoordinates_of_isHomogeneous
    (P : J → MvPolynomial (W ⊕ X) K) (hP : ∀ j, (inputPolynomial P j).IsHomogeneous d) :
    boundedCoefficientPadding (polynomialInputDegree_le_of_isHomogeneous hP) ''
        neurovariety (polynomialCoefficientCoordinates P) =
      Function.ExtendByZero.linearMap K K (Prod.map (id : J → J)
          (Subtype.impEmbedding (fun s : X →₀ ℕ => s.degree = d) (fun s => s.degree ≤ d)
            fun _ hs => hs.le)) ''
        neurovariety (polynomialHomogeneousCoefficientCoordinates P hP) := by
  rw [← neurovariety_boundedCoefficientPadding_comp, ← neurovariety_extendByZero_comp
    (Function.injective_id.prodMap (Subtype.impEmbedding _ _ _).injective)]
  exact congrArg neurovariety <| _root_.funext
    (boundedCoefficientPadding_polynomialCoefficientCoordinates_of_isHomogeneous P hP)

/-- For a model whose input polynomials are homogeneous of degree `d`, the coefficient image is
algebraic in bounded-degree coordinates exactly when it is algebraic in homogeneous
coordinates. -/
theorem isAlgebraicImage_polynomialCoefficientCoordinates_iff_of_isHomogeneous
    (P : J → MvPolynomial (W ⊕ X) K) (hP : ∀ j, (inputPolynomial P j).IsHomogeneous d) :
    IsAlgebraicImage (polynomialCoefficientCoordinates P) ↔
      IsAlgebraicImage (polynomialHomogeneousCoefficientCoordinates P hP) := by
  have hc : boundedCoefficientPadding (polynomialInputDegree_le_of_isHomogeneous hP) ∘
        polynomialCoefficientCoordinates P =
      Function.ExtendByZero.linearMap K K (Prod.map (id : J → J)
          (Subtype.impEmbedding (fun s : X →₀ ℕ => s.degree = d) (fun s => s.degree ≤ d)
            fun _ hs => hs.le)) ∘
        polynomialHomogeneousCoefficientCoordinates P hP := _root_.funext
    (boundedCoefficientPadding_polynomialCoefficientCoordinates_of_isHomogeneous P hP)
  rw [← isAlgebraicImage_boundedCoefficientPadding_comp_iff
      (polynomialInputDegree_le_of_isHomogeneous hP), hc,
    isAlgebraicImage_extendByZero_comp_iff
      (Function.injective_id.prodMap (Subtype.impEmbedding _ _ _).injective)]

end Homogeneous

section Faithful

variable [Infinite K] {τ : Type*} [Finite τ] {E : (τ → K) →ₗ[K] (X → K) → J → K}
  {c : (W → K) → τ → K}

/-- Over an infinite field, every faithful linear presentation
`E (c w) = polynomialRealization P w` of a polynomial model in finitely many coordinates is the
image of the monomial coefficient coordinates under a linear map, which restricts to a bijection
between the two neurovarieties. -/
theorem exists_linearMap_comp_eq_bijOn_neurovariety_polynomialCoefficientCoordinates
    (P : J → MvPolynomial (W ⊕ X) K) (hE : Function.Injective E)
    (h : ∀ w, E (c w) = polynomialRealization P w) :
    ∃ φ : (J × {s : X →₀ ℕ // s.degree ≤ polynomialInputDegree P} → K) →ₗ[K] (τ → K),
      φ ∘ polynomialCoefficientCoordinates P = c ∧
        Set.BijOn φ (neurovariety (polynomialCoefficientCoordinates P)) (neurovariety c) :=
  exists_linearMap_comp_eq_bijOn_neurovariety
    (E₁ := tupleEvaluation J _ ∘ₗ (boundedCoefficientEquiv X K J _).symm.toLinearMap)
    ((tupleEvaluation_injective _).comp (LinearEquiv.injective _)) hE
    (tupleEvaluation_boundedCoefficientEquiv_symm_polynomialCoefficientCoordinates P) h

/-- Over an infinite field, a faithful linear presentation `E (c w) = polynomialRealization P w`
of a polynomial model in finitely many coordinates has algebraic coefficient image exactly when
the monomial coefficient coordinates do. -/
theorem isAlgebraicImage_polynomialCoefficientCoordinates_iff_of_injective
    (P : J → MvPolynomial (W ⊕ X) K) (hE : Function.Injective E)
    (h : ∀ w, E (c w) = polynomialRealization P w) :
    IsAlgebraicImage (polynomialCoefficientCoordinates P) ↔ IsAlgebraicImage c :=
  isAlgebraicImage_iff_isAlgebraicImage_of_injective
    (E₁ := tupleEvaluation J _ ∘ₗ (boundedCoefficientEquiv X K J _).symm.toLinearMap)
    ((tupleEvaluation_injective _).comp (LinearEquiv.injective _)) hE
    (tupleEvaluation_boundedCoefficientEquiv_symm_polynomialCoefficientCoordinates P) h

end Faithful

end TauCeti.Neuromanifold
