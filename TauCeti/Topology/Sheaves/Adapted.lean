/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import TauCeti.CategoryTheory.Sites.TopologicalBasis

/-!
# Presheaves adapted to a basis

A presheaf `F` on a topological space `X` is *adapted* to a set `B` of opens if, for every open
`V`, the restriction maps `F(V) ⟶ F(U)` to the members `U ∈ B` with `U ≤ V` exhibit `F(V)` as the
limit of the `F(U)`. In the language of Kan extensions, `F` is the pointwise right Kan extension
of its restriction to `B` along the inclusion of `B` into the opens of `X`. This is the sense in
which the structure presheaf of an adic spectrum, defined on rational opens and extended to all
opens by limits, is determined by its values on the rational opens.

When `B` is a basis of the topology, an adapted presheaf is a sheaf exactly when its restriction
to `B` is a sheaf for the topology restricted to `B`; this is what makes sheaf conditions checkable
on a basis for presheaves defined by such limits. Only the direction from `B` to `X` uses
adaptedness; the other direction holds for every sheaf.

## Main definitions

* `TopCat.Presheaf.IsAdapted`: `F` is adapted to `B`.

## Main results

* `TopCat.Presheaf.isSheaf_of_isAdapted_of_isSheaf_restrictedTopology`: an adapted presheaf whose
  restriction to `B` is a sheaf for the restricted topology is a sheaf.
* `TopCat.Presheaf.IsSheaf.isSheaf_restrictedTopology`: the restriction of a sheaf to a basis is a
  sheaf for the restricted topology.
* `TopCat.Presheaf.isSheaf_iff_of_isAdapted`: for a presheaf adapted to a basis, the two sheaf
  conditions are equivalent.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Remark and Definition 8.9.
* M. Artin, A. Grothendieck, J.-L. Verdier, *Théorie des topos et cohomologie étale des schémas*
  (SGA 4), Tome 1, Exposé III, 2.2, for the passage from a sheaf on the basis to a sheaf on the
  space, which is Mathlib's `CategoryTheory.RanIsSheafOfIsCocontinuous.isLimitMultifork`.
-/

public section

universe w v u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}} (F : X.Presheaf C) (B : Set (Opens X))

/-- A presheaf `F` on `X` is adapted to a set `B` of opens if, at every open `V`, the restriction
maps to the members of `B` contained in `V` make `F.obj (op V)` the limit of `F` over them: `F`
is the pointwise right Kan extension of its restriction to `B`. -/
@[expose] def IsAdapted : Prop :=
  Nonempty (Functor.RightExtension.mk F
    (𝟙 ((inducedFunctor (Subtype.val : B → Opens X)).op ⋙ F))).IsPointwiseRightKanExtension

/-- **The sheaf condition on a basis `B` suffices for an adapted presheaf.** If `F` is adapted to
the basis `B` and its restriction to `B` is a sheaf for the topology restricted to `B`, then `F` is
a sheaf. A sieve on a member of `B` covers for the restricted topology exactly when its image
covers in `X` (`Functor.mem_restrictedTopology_iff`), so the hypothesis involves only covers of
members of `B` by members of `B`. The inclusion of a basis is cocontinuous for the restricted
topology, and a pointwise right Kan extension of a sheaf along a cocontinuous functor is a sheaf
(SGA 4 III 2.2). -/
theorem isSheaf_of_isAdapted_of_isSheaf_restrictedTopology (hB : Opens.IsBasis B)
    (hF : F.IsAdapted B)
    (h : CategoryTheory.Presheaf.IsSheaf
      ((inducedFunctor (Subtype.val : B → Opens X)).restrictedTopology
        (Opens.grothendieckTopology X))
      ((inducedFunctor (Subtype.val : B → Opens X)).op ⋙ F)) :
    F.IsSheaf :=
  -- a basis is cover-dense, so its inclusion is cocontinuous for the restricted topology
  have := TauCeti.TopologicalSpace.Opens.coverDense_inducedFunctor_subtypeVal hB
  (Presheaf.isSheaf_iff_multifork _ _).mpr fun _ S ↦
    ⟨RanIsSheafOfIsCocontinuous.isLimitMultifork h hF.some S⟩

/-- The restriction of a sheaf to a basis `B` is a sheaf for the restricted topology on `B`. -/
theorem IsSheaf.isSheaf_restrictedTopology {B : Set (Opens X)} (hB : Opens.IsBasis B)
    {F : X.Presheaf C} (hF : F.IsSheaf) :
    CategoryTheory.Presheaf.IsSheaf
      ((inducedFunctor (Subtype.val : B → Opens X)).restrictedTopology
        (Opens.grothendieckTopology X))
      ((inducedFunctor (Subtype.val : B → Opens X)).op ⋙ F) :=
  -- a basis is cover-dense, hence a dense subsite for the restricted topology, hence continuous
  have := TauCeti.TopologicalSpace.Opens.coverDense_inducedFunctor_subtypeVal hB
  Functor.op_comp_isSheaf_of_isSheaf _ _ _ F hF

/-- **A presheaf adapted to a basis is a sheaf exactly when it is a sheaf on the basis**, for the
topology restricted to the basis. -/
theorem isSheaf_iff_of_isAdapted (hB : Opens.IsBasis B) (hF : F.IsAdapted B) :
    F.IsSheaf ↔ CategoryTheory.Presheaf.IsSheaf
      ((inducedFunctor (Subtype.val : B → Opens X)).restrictedTopology
        (Opens.grothendieckTopology X))
      ((inducedFunctor (Subtype.val : B → Opens X)).op ⋙ F) :=
  ⟨fun h ↦ h.isSheaf_restrictedTopology hB,
    isSheaf_of_isAdapted_of_isSheaf_restrictedTopology F B hB hF⟩

end TopCat.Presheaf

end
