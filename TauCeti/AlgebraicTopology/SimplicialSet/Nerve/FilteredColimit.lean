/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.EssImage

/-!
# The nerve commutes with filtered colimits of categories

The nerve functor `nerveFunctor : Cat ⥤ SSet` creates filtered colimits
(`CategoryTheory.nerveFunctor.createsColimitsOfShape`), and hence preserves them
(`CategoryTheory.nerveFunctor.preservesFilteredColimitsOfSize`). So for a small filtered diagram
`F` of small categories (Mathlib provides colimits in `Cat`), Mathlib's
`preservesColimitIso nerveFunctor F : nerveFunctor.obj (colimit F) ≅ colimit (F ⋙ nerveFunctor)`
identifies the nerve of the colimit with the colimit of the nerves, compatibly with every stage
inclusion. Since colimits of simplicial sets are computed degreewise, in each degree `n` the
strings of `n` composable arrows of the colimit category are the filtered colimit of the strings
of `n` composable arrows of the stages.

The proof does not describe filtered colimits of categories directly. A colimit of the nerves
in `SSet` is strict Segal, since a finite string of arrows and the equations it satisfies occur at
a common stage of the filtered diagram (`SSet.IsStrictSegal.of_isColimit`). A strict Segal
simplicial set is the nerve of a category (`SSet.mem_essImage_nerveFunctor_iff`), and since the
nerve is fully faithful it then creates the colimit.

## Main results

* `CategoryTheory.nerveFunctor.createsColimitsOfShape`: the nerve creates colimits of filtered
  diagrams of categories, of any size. In particular it preserves the colimit of a filtered
  diagram `F` whenever `F ⋙ nerveFunctor` has a colimit.
* `CategoryTheory.nerveFunctor.preservesFilteredColimitsOfSize`: the nerve preserves filtered
  colimits indexed by categories whose objects live in a universe at most that of the categories.

## References

* D. Quillen, *Higher algebraic K-theory: I*, in *Algebraic K-theory I*, Lecture Notes in Math.
  341, Springer, 1973, §1, p. 92.
-/

public section

open CategoryTheory Limits

universe w w' u

namespace CategoryTheory.nerveFunctor

/-- The nerve functor creates colimits of filtered (or empty) diagrams of categories. -/
noncomputable instance createsColimitsOfShape {J : Type w} [Category.{w'} J]
    [IsFilteredOrEmpty J] : CreatesColimitsOfShape J nerveFunctor.{u, u} where
  CreatesColimit {F} :=
    { lifts c t :=
        have : ∀ j, ((F ⋙ nerveFunctor).obj j).IsStrictSegal :=
          fun j ↦ Nerve.isStrictSegal (F.obj j)
        have h := SSet.mem_essImage_nerveFunctor_iff.2 (SSet.IsStrictSegal.of_isColimit t)
        (createsColimitOfFullyFaithfulOfIso' t h.witness h.getIso).lifts c t }

/-- The nerve functor preserves filtered colimits indexed by categories whose objects live in a
universe at most that of the categories. -/
instance preservesFilteredColimitsOfSize [UnivLE.{w, u}] :
    PreservesFilteredColimitsOfSize.{w', w} nerveFunctor.{u, u} where
  preserves_filtered_colimits _ _ _ := inferInstance

end CategoryTheory.nerveFunctor
