/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Internal Hom comparison for monoidal functors

A lax monoidal functor `F : C ⥤ D` has a canonical comparison morphism whenever
`A` and `F.obj A` are closed:

`F.obj (A ⟶[C] B) ⟶ (F.obj A ⟶[D] F.obj B)`.

It is the mate, under the two tensor--Hom adjunctions, of the tensorator
`F.obj A ⊗ F.obj B ⟶ F.obj (A ⊗ B)`. This file packages the comparison as a natural
transformation in `B`, characterizes it by evaluation and coevaluation, and proves its
contravariant naturality in `A`. These formulas allow closed-structure comparisons to be used
without unfolding the mates construction.

The construction generalizes Mathlib's Cartesian-closed `CategoryTheory.expComparison`; its
definition and characteristic formulas follow the mate-based development in
`Mathlib.CategoryTheory.Monoidal.Closed.Functor`.

## Main declarations

* `CategoryTheory.Functor.ihomComparison`: the internal Hom comparison of a lax monoidal
  functor;
* `CategoryTheory.Functor.ihomComparison_ev`: its characteristic equation against evaluation;
* `CategoryTheory.Functor.coev_ihomComparison`: its characteristic equation against
  coevaluation;
* `CategoryTheory.Functor.ihomComparison_whiskerLeft`: its naturality in the source of the
  internal Hom.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor MonoidalCategory MonoidalClosed

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable (F : C ⥤ D) [F.LaxMonoidal]

private def laxCommTensorLeft (A : C) :
    TwoSquare F (tensorLeft A) (tensorLeft (F.obj A)) F :=
  .mk _ _ _ _ { app := fun B => Functor.LaxMonoidal.μ F A B
                naturality := fun _ _ f => Functor.LaxMonoidal.μ_natural_right F A f }

/-- The canonical comparison from the image of an internal Hom to the internal Hom of the
images under a lax monoidal functor. It is natural in the target of the internal Hom. -/
def ihomComparison (A : C) [Closed A] [Closed (F.obj A)] :
    TwoSquare (ihom A) F F (ihom (F.obj A)) :=
  mateEquiv (ihom.adjunction A) (ihom.adjunction (F.obj A))
    (laxCommTensorLeft F A)

/-- Evaluation after the internal Hom comparison is the image of evaluation, preceded by the
tensorator. This equation characterizes `ihomComparison`. -/
@[reassoc (attr := simp)]
theorem ihomComparison_ev (A B : C) [Closed A] [Closed (F.obj A)] :
    F.obj A ◁ (ihomComparison F A).natTrans.app B ≫
        (ihom.ev (F.obj A)).app (F.obj B) =
      Functor.LaxMonoidal.μ F A ((ihom A).obj B) ≫ F.map ((ihom.ev A).app B) := by
  -- `ihom.ev` is the counit of `ihom.adjunction`; `TwoSquare.app` is its
  -- underlying natural transformation, and tensor whiskering is `tensorLeft.map`.
  change (tensorLeft (F.obj A)).map ((ihomComparison F A).app B) ≫
      (ihom.adjunction (F.obj A)).counit.app (F.obj B) =
    (laxCommTensorLeft F A).app ((ihom A).obj B) ≫
      F.map ((ihom.adjunction A).counit.app B)
  exact mateEquiv_counit (ihom.adjunction A) (ihom.adjunction (F.obj A))
    (laxCommTensorLeft F A) B

/-- The image of coevaluation followed by the internal Hom comparison is coevaluation followed
by the internal Hom of the tensorator. -/
@[reassoc (attr := simp)]
theorem coev_ihomComparison (A B : C) [Closed A] [Closed (F.obj A)] :
    F.map ((ihom.coev A).app B) ≫
        (ihomComparison F A).natTrans.app (A ⊗ B) =
      (ihom.coev (F.obj A)).app (F.obj B) ≫
        (ihom (F.obj A)).map (Functor.LaxMonoidal.μ F A B) := by
  -- `ihom.coev` is the unit of `ihom.adjunction`; the functor compositions
  -- and `TwoSquare.app` elaborate to the corresponding displayed components.
  change F.map ((ihom.adjunction A).unit.app B) ≫
      (ihomComparison F A).app ((tensorLeft A).obj B) =
    (ihom.adjunction (F.obj A)).unit.app (F.obj ((𝟭 C).obj B)) ≫
      (ihom (F.obj A)).map ((laxCommTensorLeft F A).app ((𝟭 C).obj B))
  exact unit_mateEquiv (ihom.adjunction A) (ihom.adjunction (F.obj A))
    (laxCommTensorLeft F A) B

/-- Uncurrying the internal Hom comparison gives the tensorator followed by the image of
evaluation. -/
@[simp]
theorem uncurry_ihomComparison (A B : C) [Closed A] [Closed (F.obj A)] :
    uncurry ((ihomComparison F A).natTrans.app B) =
      Functor.LaxMonoidal.μ F A ((ihom A).obj B) ≫ F.map ((ihom.ev A).app B) := by
  rw [uncurry_eq, ihomComparison_ev]

/-- The internal Hom comparison is contravariantly natural in the source of the internal Hom. -/
theorem ihomComparison_whiskerLeft {A A' : C} [Closed A] [Closed A']
    [Closed (F.obj A)] [Closed (F.obj A')] (f : A' ⟶ A) :
    (ihomComparison F A).whiskerBottom (pre (F.map f)) =
      (ihomComparison F A').whiskerTop (pre f) := by
  unfold ihomComparison pre
  have vcomp₁ := mateEquiv_conjugateEquiv_vcomp
    (ihom.adjunction A) (ihom.adjunction (F.obj A)) (ihom.adjunction (F.obj A'))
    (laxCommTensorLeft F A) ((curriedTensor D).map (F.map f))
  have vcomp₂ := conjugateEquiv_mateEquiv_vcomp
    (ihom.adjunction A) (ihom.adjunction A') (ihom.adjunction (F.obj A'))
    ((curriedTensor C).map f) (laxCommTensorLeft F A')
  rw [← vcomp₁, ← vcomp₂]
  unfold TwoSquare.whiskerLeft TwoSquare.whiskerRight
  congr 1
  apply congr_arg
  ext B
  simp only [Functor.comp_obj, curriedTensor_obj_obj, NatTrans.comp_app,
    Functor.whiskerLeft_app, curriedTensor_map_app, Functor.whiskerRight_app,
    laxCommTensorLeft]
  rw [Functor.LaxMonoidal.μ_natural_left]

end CategoryTheory.Functor
