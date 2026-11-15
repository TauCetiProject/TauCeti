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

The nerve functor `nerveFunctor : Cat ⥤ SSet` preserves filtered colimits
(`CategoryTheory.nerveFunctor.preservesFilteredColimits`). So for a filtered diagram `F` of
small categories (Mathlib provides colimits in `Cat`), the comparison map
`colimit (F ⋙ nerveFunctor) ⟶ nerve (colimit F)` induced by the nerves of the stage inclusions
is an isomorphism (Mathlib's `preservesColimitIso`), compatibly with every stage inclusion.
Since colimits of simplicial sets are computed degreewise, in each degree `n` the strings of `n`
composable arrows of the colimit category are the filtered colimit of the strings of `n`
composable arrows of the stages.

The proof does not describe filtered colimits of categories directly. The colimit of the nerves
in `SSet` is strict Segal, since a finite string of arrows and the equations it satisfies occur at
a common stage of the filtered diagram (`SSet.IsStrictSegal.of_isColimit`). A strict Segal
simplicial set is the nerve of a category (`SSet.mem_essImage_nerveFunctor_iff`), and since the
nerve is fully faithful it then creates the colimit.

## Main results

* `CategoryTheory.nerveFunctor.preservesColimit_of_isFiltered`: the nerve preserves the colimit of
  any filtered diagram of categories, of any size for which colimits of types exist.
* `CategoryTheory.nerveFunctor.preservesFilteredColimits`: the nerve preserves filtered colimits.

## References

* D. Quillen, *Higher algebraic K-theory: I*, in *Algebraic K-theory I*, Lecture Notes in Math.
  341, Springer, 1973, §1, p. 92.
-/

public section

open CategoryTheory Limits

universe w w' u

namespace CategoryTheory.nerveFunctor

/-- The nerve preserves the colimit of a filtered diagram of categories: the colimit of the
nerves is strict Segal, hence the nerve of a category, and the fully faithful nerve functor creates
colimits whose image lies in its essential image. -/
theorem preservesColimit_of_isFiltered {J : Type w} [Category.{w'} J] [IsFiltered J]
    [HasColimitsOfShape J (Type u)] (F : J ⥤ Cat.{u, u}) :
    PreservesColimit F nerveFunctor.{u, u} := by
  have : ∀ j, ((F ⋙ nerveFunctor).obj j).IsStrictSegal := fun j ↦ Nerve.isStrictSegal (F.obj j)
  obtain ⟨C, ⟨e⟩⟩ := SSet.mem_essImage_nerveFunctor_iff.2
    (SSet.IsStrictSegal.of_isColimit (colimit.isColimit (F ⋙ nerveFunctor)))
  have := createsColimitOfFullyFaithfulOfIso C e
  infer_instance

/-- The nerve functor preserves filtered colimits. -/
instance preservesFilteredColimits : PreservesFilteredColimits nerveFunctor.{u, u} where
  preserves_filtered_colimits _ _ _ := ⟨preservesColimit_of_isFiltered _⟩

end CategoryTheory.nerveFunctor
