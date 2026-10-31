/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Polynomial.Basic
public import TauCeti.Geometry.RealAlgebraic.CAD.Existence
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image

/-!
# Semialgebraic coefficient images of real polynomial models

The finite monomial coefficient image of a real jointly polynomial model is semialgebraic.
More generally, restricting parameters to any semialgebraic set still gives a semialgebraic
coefficient image. Each coefficient coordinate is a polynomial in the parameters, so the
Tarski–Seidenberg theorem applies through `TauCeti.IsSemialgebraic.image_eval`. The real
projection theorem is supplied by `TauCeti.Geometry.RealAlgebraic.CAD.Existence`; no projection
closure hypothesis is imposed on callers.

These statements concern the faithful finite coefficient coordinates, not a semialgebraic
structure on the ambient space of all functions. They do not assert that the coefficient image
is Zariski closed or equal to its neurovariety.

The jointly polynomial setting and the coefficient/function viewpoint follow
Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3.1.
-/

public section

namespace TauCeti.Neuromanifold

open MvPolynomial

variable {W X J : Type*} [Finite W] [Finite X] [Fintype J]

/-- The finite coefficient image of a real jointly polynomial model restricted to a
semialgebraic parameter set is semialgebraic. -/
theorem isSemialgebraic_image_polynomialCoefficientCoordinates
    (P : J → MvPolynomial (W ⊕ X) ℝ) {s : Set (W → ℝ)} (hs : IsSemialgebraic s) :
    IsSemialgebraic (polynomialCoefficientCoordinates P '' s) := by
  have hcoords : polynomialCoefficientCoordinates P =
      fun w i => eval w ((inputPolynomial P i.1).coeff i.2) := by
    funext w i
    exact polynomialCoefficientCoordinates_apply P w i
  rw [hcoords]
  exact hs.image_eval _

/-- The full finite coefficient image of every real jointly polynomial model is semialgebraic,
without a closed-image assumption. -/
theorem isSemialgebraic_range_polynomialCoefficientCoordinates
    (P : J → MvPolynomial (W ⊕ X) ℝ) :
    IsSemialgebraic (Set.range (polynomialCoefficientCoordinates P)) := by
  simpa only [Set.image_univ] using
    isSemialgebraic_image_polynomialCoefficientCoordinates P isSemialgebraic_univ

end TauCeti.Neuromanifold
