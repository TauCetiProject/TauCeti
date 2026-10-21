/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# Structure maps of duals pulled back along a monoidal equivalence

Mathlib's `CategoryTheory.hasRightDualOfEquivalence` gives an object `X` of `C` a right dual by
pulling back the right dual of `F.obj X` along a monoidal equivalence `F : C ⥤ D`. Its evaluation
and coevaluation are defined as preimages under `F`. This file records their images under `F`:
the evaluation and coevaluation of `(F.obj X, (F.obj X)ᘁ)`, transported across the counit of the
equivalence and conjugated by the comparison maps of `F`.

These identities are how the structure maps of such a dual are computed. For instance, Mathlib
makes `Action V H` right rigid this way, and its evaluation and coevaluation are computed from
them on underlying objects.

## Main results

* `CategoryTheory.map_evaluation_hasRightDualOfEquivalence`: the image under `F` of the evaluation
  of the pulled-back right dual;
* `CategoryTheory.map_coevaluation_hasRightDualOfEquivalence`: the image under `F` of the
  coevaluation of the pulled-back right dual.
-/

public section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} [F.Monoidal] {G : D ⥤ C} (adj : F ⊣ G) [F.IsEquivalence]

/-- The evaluation of a right dual pulled back along a monoidal equivalence `F` is, by definition,
the preimage under `F` of the evaluation of the right dual of `F.obj X` transported across the
counit. -/
theorem map_evaluation_hasRightDualOfEquivalence (X : C) [HasRightDual (F.obj X)] :
    F.map (@ExactPairing.evaluation _ _ _ X _ (hasRightDualOfEquivalence adj X).exact) =
      δ F _ _ ≫ ((adj.toEquivalence.counitIso.app (F.obj X)ᘁ).hom ▷ F.obj X ≫
        ε_ (F.obj X) (F.obj X)ᘁ) ≫ ε F :=
  F.map_preimage _

/-- The coevaluation of a right dual pulled back along a monoidal equivalence `F` is, by
definition, the preimage under `F` of the coevaluation of the right dual of `F.obj X` transported
across the counit. -/
theorem map_coevaluation_hasRightDualOfEquivalence (X : C) [HasRightDual (F.obj X)] :
    F.map (@ExactPairing.coevaluation _ _ _ X _ (hasRightDualOfEquivalence adj X).exact) =
      η F ≫ (η_ (F.obj X) (F.obj X)ᘁ ≫
        F.obj X ◁ (adj.toEquivalence.counitIso.app (F.obj X)ᘁ).inv) ≫ μ F _ _ :=
  F.map_preimage _

end CategoryTheory
