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

/-- The polynomial resolution is the resolution of the free-polynomial comonad. -/
lemma polynomialSimplicialResolution_def :
    polynomialSimplicialResolution.{u, v} R = (polynomialComonad R).simplicialResolution := (rfl)

-- Keep these all-degree formulas as rewrite lemmas: making them simp rules would shadow
-- the polynomial term and low-degree formulas below, which are the chosen simp normal forms.

/-- Faces in every degree are the iterated counits of the polynomial comonad. -/
lemma polynomialSimplicialResolution_δ (B : CommAlgCat.{max u v} R) {n : ℕ}
    (i : Fin (n + 2)) :
    ((polynomialSimplicialResolution R).obj B).δ i =
      ((polynomialComonad R).resolutionFace (n + 1) i).app B :=
  Comonad.simplicialResolution_δ _ B i

/-- Degeneracies in every degree are the iterated polynomial comultiplications. -/
lemma polynomialSimplicialResolution_σ (B : CommAlgCat.{max u v} R) {n : ℕ}
    (i : Fin (n + 1)) :
    ((polynomialSimplicialResolution R).obj B).σ i =
      ((polynomialComonad R).resolutionDegeneracy n i).app B :=
  Comonad.simplicialResolution_σ _ B i

/-- A morphism acts termwise by the corresponding iterate of the polynomial comonad. -/
lemma polynomialSimplicialResolution_map_app {B B' : CommAlgCat.{max u v} R}
    (f : B ⟶ B') (n : ℕ) :
    ((polynomialSimplicialResolution R).map f).app (op (SimplexCategory.mk n)) =
      ((polynomialComonad R).resolutionStage (n + 1)).map f := (rfl)

/-- Every term is a polynomial algebra on the underlying set of the preceding iterate,
with the original algebra serving as the zeroth iterate. -/
@[simp] lemma polynomialSimplicialResolution_obj_obj (B : CommAlgCat.{max u v} R) (n : ℕ) :
    ((polynomialSimplicialResolution R).obj B).obj (op (SimplexCategory.mk n)) =
      of R (MvPolynomial (((polynomialComonad R).resolutionStage n).obj B) R) := (rfl)

/-- The zeroth face from degree one to degree zero evaluates the outer variables. -/
@[simp] lemma polynomialSimplicialResolution_δ_zero_hom (B : CommAlgCat.{max u v} R) :
    (((polynomialSimplicialResolution R).obj B).δ (0 : Fin 2)).hom =
      MvPolynomial.aeval (id : MvPolynomial B R → MvPolynomial B R) := by
  rw [polynomialSimplicialResolution_δ, Comonad.resolutionFace_zero_app]
  -- Reduce the stage in the dependent source and target types before applying the hom formula.
  dsimp only [Comonad.resolutionStage, Functor.comp_obj, Functor.id_obj]
  exact polynomialComonad_ε_app_hom R ((polynomialComonad R).obj B)

/-- The other face from degree one to degree zero renames variables by evaluation. -/
@[simp] lemma polynomialSimplicialResolution_δ_one_hom (B : CommAlgCat.{max u v} R) :
    (((polynomialSimplicialResolution R).obj B).δ (1 : Fin 2)).hom =
      MvPolynomial.rename (R := R) (MvPolynomial.aeval (id : B → B)) := by
  rw [← Fin.succ_zero_eq_one, polynomialSimplicialResolution_δ,
    Comonad.resolutionFace_succ_app, Comonad.resolutionFace_zero_app]
  dsimp only [Comonad.resolutionStage, Functor.id_obj]
  exact congrArg Hom.hom (polynomialComonad_map_ε_app R B)

/-- The first degeneracy inserts a variable layer, sending `X b` to `X (X b)`. -/
@[simp] lemma polynomialSimplicialResolution_σ_zero_hom (B : CommAlgCat.{max u v} R) :
    (((polynomialSimplicialResolution R).obj B).σ (0 : Fin 1)).hom =
      MvPolynomial.rename (MvPolynomial.X : B → MvPolynomial B R) := by
  rw [polynomialSimplicialResolution_σ, Comonad.resolutionDegeneracy_zero_app]
  dsimp only [Comonad.resolutionStage, Functor.id_obj]
  exact polynomialComonad_δ_app_hom R B

end CommAlgCat
