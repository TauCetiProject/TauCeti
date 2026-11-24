/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import TauCeti.CategoryTheory.Preadditive.Projective.Basic

/-!
# Projective objects of functor categories

For an object `X` of `C`, Mathlib's `evaluationLeftAdjoint A X` sends `V : A` to the free
corepresentable functor `c ↦ ∐_{X ⟶ c} V`, left adjoint to evaluation at `X`. When evaluation at
`X` preserves epimorphisms, for instance when `A` has pushouts, it preserves projective objects
(`CategoryTheory.preservesProjectiveObjects_evaluationLeftAdjoint`).

Every functor `M : C ⥤ A` is a quotient of the coproduct, over the objects `X` of `C`, of these
functors at projective presentations of `M.obj X`
(`CategoryTheory.epi_sigmaDescEvaluationLeftAdjointProjectivePresentation`). So if `A` has enough
projectives and pushouts, so does `C ⥤ A` (`CategoryTheory.functorCategoryEnoughProjectives`); for
abelian `A` this gives projective resolutions of functors by coproducts of free corepresentable
functors, for instance of coefficient systems for the homology of a small category.

## References

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341 (1973), §1, p. 91.
-/

public section

noncomputable section

open CategoryTheory Limits

universe v u v' u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [∀ a b : C, HasCoproductsOfShape (a ⟶ b) A]

/-- The free corepresentable functor `c ↦ ∐_{X ⟶ c} V` on a projective object `V` is projective,
when evaluation at `X` preserves epimorphisms. -/
instance preservesProjectiveObjects_evaluationLeftAdjoint (X : C)
    [((evaluation C A).obj X).PreservesEpimorphisms] :
    (evaluationLeftAdjoint A X).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (evaluationAdjunctionRight A X)

variable [HasColimitsOfShape (Discrete C) A]

/-- The morphism from the coproduct over the objects `X` of `C` of the free corepresentable
functors on projective presentations of `M.obj X` to `M`; on the summand of `X` it is adjoint to
the presentation `Projective.π (M.obj X)`. -/
def sigmaDescEvaluationLeftAdjointProjectivePresentation [EnoughProjectives A] (M : C ⥤ A) :
    (∐ fun X : C ↦ (evaluationLeftAdjoint A X).obj (Projective.over (M.obj X))) ⟶ M :=
  Sigma.desc fun X ↦ ((evaluationAdjunctionRight A X).homEquiv _ _).symm (Projective.π (M.obj X))

@[reassoc (attr := simp)]
lemma ι_sigmaDescEvaluationLeftAdjointProjectivePresentation [EnoughProjectives A] (M : C ⥤ A)
    (X : C) :
    Sigma.ι (fun X : C ↦ (evaluationLeftAdjoint A X).obj (Projective.over (M.obj X))) X ≫
        sigmaDescEvaluationLeftAdjointProjectivePresentation M =
      ((evaluationAdjunctionRight A X).homEquiv _ _).symm (Projective.π (M.obj X)) :=
  Sigma.ι_comp_desc _ _

instance epi_sigmaDescEvaluationLeftAdjointProjectivePresentation [EnoughProjectives A]
    (M : C ⥤ A) : Epi (sigmaDescEvaluationLeftAdjointProjectivePresentation M) := by
  suffices ∀ c, Epi ((sigmaDescEvaluationLeftAdjointProjectivePresentation M).app c) from
    NatTrans.epi_of_epi_app _
  intro c
  -- The presentation of `M.obj c` factors through the component at `c`, through the summand of
  -- `c` and its coefficient at the identity of `c`.
  refine epi_of_epi_fac (f := (evaluationAdjunctionRight A c).unit.app _ ≫
    (Sigma.ι (fun X : C ↦ (evaluationLeftAdjoint A X).obj (Projective.over (M.obj X))) c).app c)
    (h := Projective.π (M.obj c)) ?_
  rw [Category.assoc, ← NatTrans.comp_app, ι_sigmaDescEvaluationLeftAdjointProjectivePresentation]
  -- The component at `c` is evaluation at `c`, the right adjoint, applied to the transpose.
  exact ((evaluationAdjunctionRight A c).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- If `A` has enough projectives and pushouts, then so has the functor category `C ⥤ A`: every
functor is a quotient of a coproduct of free corepresentable functors on projective objects. -/
instance functorCategoryEnoughProjectives [EnoughProjectives A] [HasPushouts A] :
    EnoughProjectives (C ⥤ A) where
  presentation M := ⟨{
    p := _
    projective := Projective.of_isColimit_cofan (coproductIsCoproduct _)
    f := sigmaDescEvaluationLeftAdjointProjectivePresentation M }⟩

end CategoryTheory
