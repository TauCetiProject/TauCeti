/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Category.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor
public import TauCeti.Combinatorics.PlanarMatching.Rigid

/-!
# The rigid structure of the linear Temperley–Lieb category

Every object of the linear Temperley–Lieb category `TauCeti.TLCat R δ` is its own dual, so
`TLCat R δ` is a rigid monoidal `R`-linear category, for every commutative ring `R` and every loop
value `δ : R`.

The self-duality of `TLCat.of n` is the image, under the strict monoidal linearization functor
`TauCeti.TLCat.linearize R δ : TLDiagCat ⥤ TLCat R δ`, of the self-duality of `TLDiagCat.of n` in
the Temperley–Lieb diagram category. Its coevaluation is the basis morphism of `n` nested cups and
its evaluation the basis morphism of `n` nested caps (`TauCeti.TLCat.coevaluation_eq_diagBasis`,
`TauCeti.TLCat.evaluation_eq_diagBasis`). On the generating object `TLCat.of 1` they are the cup
and the cap, and closing the strand gives the loop value: `η ≫ ε = δ • 𝟙 (𝟙_ (TLCat R δ))`
(`TauCeti.TLCat.coevaluation_comp_evaluation_one`). So the generating object of `TLCat R δ` is a
self-duality with circle value `δ`, the input of the `R`-linear universal property of `TLCat R δ`.

Linearization is compatible with the rigid structures: it sends coevaluations, evaluations and
right adjoint mates in `TLDiagCat` to those in `TLCat R δ`, and it sends the self-duality of each
object of `TLDiagCat` to that of its image along the identity
(`TauCeti.TLCat.linearize_sendsSelfDuality`).

## Main definitions

* `TauCeti.TLCat.instExactPairing`: every object of `TLCat R δ` is self-dual.
* `TauCeti.TLCat.instRigidCategory`: `TLCat R δ` is rigid, with every object its own left and
  right dual.

## Main results

* `TauCeti.TLCat.coevaluation_eq_diagBasis`, `TauCeti.TLCat.evaluation_eq_diagBasis`: the
  coevaluation and evaluation of `X` are the basis morphisms of `X.as` nested cups and caps.
* `TauCeti.TLCat.coevaluation_one`, `TauCeti.TLCat.evaluation_one`: on `of 1` they are `cup` and
  `cap`.
* `TauCeti.TLCat.coevaluation_comp_evaluation_one`: the closed circle on the generating object is
  `δ` times the identity of the unit.
* `TauCeti.TLCat.linearize_map_coevaluation`, `TauCeti.TLCat.linearize_map_evaluation`,
  `TauCeti.TLCat.linearize_map_rightAdjointMate`: linearization preserves the rigid structure.
* `TauCeti.TLCat.linearize_sendsSelfDuality`: linearization sends each self-duality of
  `TLDiagCat` to the corresponding one of `TLCat R δ`.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

open CategoryTheory MonoidalCategory

universe u

namespace TauCeti

namespace TLCat

variable {R : Type u} [CommRing R] {δ : R}

/-- **Every object of `TLCat R δ` is self-dual**: the self-duality of `of n` is the image under
`linearize R δ` of that of `TLDiagCat.of n`, with coevaluation `n` nested cups and evaluation `n`
nested caps. The zigzag identities are the images of those in `TLDiagCat`. -/
noncomputable instance instExactPairing (X : TLCat R δ) : ExactPairing X X where
  coevaluation' := (linearize R δ).map (η_ (TLDiagCat.of X.as) (TLDiagCat.of X.as))
  evaluation' := (linearize R δ).map (ε_ (TLDiagCat.of X.as) (TLDiagCat.of X.as))
  coevaluation_evaluation' := by
    -- `linearize R δ` is strict monoidal, so it sends the zigzag identities of `TLDiagCat.of X.as`
    -- to those of its image `of X.as = X`.
    have h := congrArg (linearize R δ).map
      (ExactPairing.coevaluation_evaluation (TLDiagCat.of X.as) (TLDiagCat.of X.as))
    simp only [Functor.map_comp, linearize_map_whiskerLeft, linearize_map_whiskerRight,
      linearize_map_associator_inv, linearize_map_rightUnitor_hom,
      linearize_map_leftUnitor_inv] at h
    exact h
  evaluation_coevaluation' := by
    have h := congrArg (linearize R δ).map
      (ExactPairing.evaluation_coevaluation (TLDiagCat.of X.as) (TLDiagCat.of X.as))
    simp only [Functor.map_comp, linearize_map_whiskerLeft, linearize_map_whiskerRight,
      linearize_map_associator_hom, linearize_map_leftUnitor_hom,
      linearize_map_rightUnitor_inv] at h
    exact h

/-- Linearization sends the coevaluation of an object of `TLDiagCat` to the coevaluation of its
image. -/
@[simp]
theorem linearize_map_coevaluation (X : TLDiagCat) :
    (linearize R δ).map (η_ X X) = η_ ((linearize R δ).obj X) ((linearize R δ).obj X) :=
  -- The coevaluation of `(linearize R δ).obj X = of X.as` is by definition the image of the one of
  -- `TLDiagCat.of X.as`, which is `X` up to structure eta.
  (rfl)

/-- Linearization sends the evaluation of an object of `TLDiagCat` to the evaluation of its
image. -/
@[simp]
theorem linearize_map_evaluation (X : TLDiagCat) :
    (linearize R δ).map (ε_ X X) = ε_ ((linearize R δ).obj X) ((linearize R δ).obj X) :=
  -- The evaluation of `(linearize R δ).obj X = of X.as` is by definition the image of the one of
  -- `TLDiagCat.of X.as`, which is `X` up to structure eta.
  (rfl)

/-- **The coevaluation of `X` is `X.as` nested cups**: the basis morphism of the matching joining
the top points `i` and `2 * X.as - 1 - i`. -/
theorem coevaluation_eq_diagBasis (X : TLCat R δ) :
    η_ X X = diagBasis (of 0) (X ⊗ X)
      (PlanarMatching.cast (Nat.zero_add _).symm (PlanarMatching.nested X.as)) := by
  rw [← of_as X, ← linearize_obj_of, ← linearize_map_coevaluation, linearize_map,
    TLDiagCat.diagram_coevaluation, pow_zero, one_smul]
  -- What remains is the projection of the matching from the anonymous diagram, with the objects
  -- `of (𝟙_ TLDiagCat).as = of 0` and `(linearize R δ).obj (TLDiagCat.of X.as) = of X.as`.
  rfl

/-- **The evaluation of `X` is `X.as` nested caps**: the basis morphism of the matching joining
the bottom points `i` and `2 * X.as - 1 - i`. -/
theorem evaluation_eq_diagBasis (X : TLCat R δ) :
    ε_ X X = diagBasis (X ⊗ X) (of 0)
      (PlanarMatching.cast (Nat.add_zero _).symm (PlanarMatching.nested X.as)) := by
  rw [← of_as X, ← linearize_obj_of, ← linearize_map_evaluation, linearize_map,
    TLDiagCat.diagram_evaluation, pow_zero, one_smul]
  -- What remains is the projection of the matching from the anonymous diagram, with the objects
  -- `of (𝟙_ TLDiagCat).as = of 0` and `(linearize R δ).obj (TLDiagCat.of X.as) = of X.as`.
  rfl

/-- The coevaluation of the generating object `of 1` is the cup. -/
@[simp]
theorem coevaluation_one : η_ (of 1 : TLCat R δ) (of 1) = cup := by
  refine (linearize_map_coevaluation (TLDiagCat.of 1)).symm.trans ?_
  rw [TLDiagCat.coevaluation_one, linearize_map_cup]

/-- The evaluation of the generating object `of 1` is the cap. -/
@[simp]
theorem evaluation_one : ε_ (of 1 : TLCat R δ) (of 1) = cap := by
  refine (linearize_map_evaluation (TLDiagCat.of 1)).symm.trans ?_
  rw [TLDiagCat.evaluation_one, linearize_map_cap]

/-- **The circle value of the generating self-duality**: closing the strand of `of 1` is `δ` times
the identity of the monoidal unit. -/
@[reassoc]
theorem coevaluation_comp_evaluation_one :
    η_ (of 1 : TLCat R δ) (of 1) ≫ ε_ (of 1) (of 1) = δ • 𝟙 (𝟙_ (TLCat R δ)) := by
  rw [coevaluation_one, evaluation_one, cup_comp_cap]
  -- The monoidal unit of `TLCat R δ` is `of 0` by definition.
  rfl

/-- **The linear Temperley–Lieb category is rigid**: every object is its own left and right
dual. -/
noncomputable instance instRigidCategory : RigidCategory (TLCat R δ) where
  rightDual X := ⟨X⟩
  leftDual X := ⟨X⟩

/-- Every object is its own right dual. -/
@[simp]
theorem rightDual_eq (X : TLCat R δ) : Xᘁ = X := (rfl)

/-- Every object is its own left dual. -/
@[simp]
theorem leftDual_eq (X : TLCat R δ) : (ᘁX : TLCat R δ) = X := (rfl)

/-- Linearization sends the right adjoint mate of a morphism of `TLDiagCat` to the right adjoint
mate of its image. -/
@[simp]
theorem linearize_map_rightAdjointMate {X Y : TLDiagCat} (f : X ⟶ Y) :
    (linearize R δ).map (fᘁ) = ((linearize R δ).map f)ᘁ := by
  -- Both right duals of `(linearize R δ).obj X` are given by the same exact pairing, so the
  -- comparison between them is the identity.
  have h (Z : TLDiagCat) : (linearize R δ).mapRightDualIso Z = Iso.refl _ := by
    refine Iso.ext (ExactPairing.rightHom_ext (X := (linearize R δ).obj Z)
      (Y := ((linearize R δ).obj Z)ᘁ)
      ((Functor.mapRightDualIso_hom_whiskerRight_evaluation Z).trans ?_))
    simp only [linearize_μ, linearize_η, Iso.refl_hom, id_whiskerRight, Category.id_comp]
    exact (Category.comp_id _).trans (linearize_map_evaluation Z)
  simpa only [h, Iso.refl_hom, Category.comp_id, Category.id_comp] using
    Functor.mapRightDualIso_hom_naturality (F := linearize R δ) f

/-- **Linearization sends self-dualities to self-dualities**: it sends the self-duality of an
object `X` of `TLDiagCat` to the self-duality of its image, along the identity. -/
theorem linearize_sendsSelfDuality (X : TLDiagCat) :
    SendsSelfDuality (linearize R δ) ((linearize R δ).obj X) (Iso.refl _) where
  coevaluation := by
    simp only [linearize_ε, linearize_μ, linearize_map_coevaluation, Iso.refl_inv,
      id_tensorHom_id, Category.id_comp, Category.comp_id]
  evaluation := by
    simp only [linearize_η, linearize_μ, linearize_map_evaluation, Iso.refl_inv,
      id_tensorHom_id, Category.id_comp]
    exact Category.comp_id _

end TLCat

end TauCeti
