/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.PolynomialPresentation
public import TauCeti.CategoryTheory.Monad.SimplicialResolution

/-!
# The standard simplicial polynomial algebra

Iterating the free-polynomial comonad gives a simplicial commutative algebra,
functorial in the algebra being resolved. Its terms are polynomial rings on
specified sets: degree zero is `R[B]`, and each subsequent degree is the
polynomial ring on the preceding term. Faces evaluate a layer of variables;
degeneracies insert a layer of variables.

This file constructs the simplicial algebra, not its augmentation or the
acyclicity and comparison theorems for polynomial resolutions.

## References

* The Stacks Project, Definition 92.3.1 (Tag 08PM).

The construction uses `CommAlgCat.polynomialComonad` and
`CategoryTheory.Comonad.simplicialResolution`.
-/

public noncomputable section

open CategoryTheory Opposite

universe u v

namespace CommAlgCat

variable (R : Type u) [CommRing R]

/-- The simplicial algebra of the standard polynomial resolution, functorial in the
commutative algebra. Exposed so its polynomial term types compute. -/
@[expose] def polynomialSimplicialResolution :
    CommAlgCat.{max u v} R ⥤ SimplicialObject (CommAlgCat.{max u v} R) :=
  (polynomialComonad R).simplicialResolution

/-- Every term is a polynomial algebra on the underlying set of the preceding iterate,
with the original algebra serving as the zeroth iterate. -/
@[simp] lemma polynomialSimplicialResolution_obj_obj (B : CommAlgCat.{max u v} R) (n : ℕ) :
    ((polynomialSimplicialResolution R).obj B).obj (op (SimplexCategory.mk n)) =
      of R (MvPolynomial (((polynomialComonad R).resolutionStage n).obj B) R) := (rfl)

/-- The zeroth face from degree one to degree zero evaluates the outer variables. -/
@[simp] lemma polynomialSimplicialResolution_δ_zero (B : CommAlgCat.{max u v} R) :
    (((polynomialSimplicialResolution R).obj B).δ (0 : Fin 2)).hom =
      MvPolynomial.aeval (id : MvPolynomial B R → MvPolynomial B R) := by
  dsimp only [polynomialSimplicialResolution]
  rw [Comonad.simplicialResolution_δ, Comonad.resolutionFace_zero]
  exact polynomialComonad_ε_app_hom R ((polynomialComonad R).obj B)

/-- The other face from degree one to degree zero renames variables by evaluation. -/
@[simp] lemma polynomialSimplicialResolution_δ_one (B : CommAlgCat.{max u v} R) :
    (((polynomialSimplicialResolution R).obj B).δ (1 : Fin 2)).hom =
      MvPolynomial.rename (R := R) (MvPolynomial.aeval (id : B → B)) := by
  dsimp only [polynomialSimplicialResolution]
  rw [← Fin.succ_zero_eq_one, Comonad.simplicialResolution_δ,
    Comonad.resolutionFace_succ, Comonad.resolutionFace_zero]
  exact congrArg Hom.hom (polynomialComonad_map_ε_app R B)

/-- The first degeneracy inserts a variable layer, sending `X b` to `X (X b)`. -/
@[simp] lemma polynomialSimplicialResolution_σ_zero (B : CommAlgCat.{max u v} R) :
    (((polynomialSimplicialResolution R).obj B).σ (0 : Fin 1)).hom =
      MvPolynomial.rename (MvPolynomial.X : B → MvPolynomial B R) := by
  dsimp only [polynomialSimplicialResolution]
  rw [Comonad.simplicialResolution_σ, Comonad.resolutionDegeneracy_zero]
  exact polynomialComonad_δ_app_hom R B

end CommAlgCat
