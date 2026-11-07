/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import TauCeti.Algebra.Homology.Ext.Basic
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# The image sequence of the embedding of a sheaf into an injective sheaf

Let `F` be a sheaf of abelian groups on a topological space `X`, embedded into the chosen
injective sheaf `I` with cokernel sheaf `Q`. The cokernel sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` is exact as
a sequence of sheaves, but not on sections: `I(V) ⟶ Q(V)` need not be onto. Replacing `Q` by the
image presheaf `G` of `I ⟶ Q` gives a sequence `0 ⟶ F ⟶ I ⟶ G ⟶ 0` of presheaves which is exact on
the sections over every open. Dimension-shifting arguments comparing Čech cohomology with sheaf
cohomology apply the long exact Čech sequence to it.

## Main definitions

* `TauCeti.Topology.injectiveImageSequence F`: the sequence `0 ⟶ F ⟶ I ⟶ G ⟶ 0` of presheaves.

## Main results

* `TauCeti.Topology.injectiveImageSequence_map_shortExact`: this sequence is exact on the sections
  over every open.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TauCeti.Topology

variable {X : TopCat.{u}} (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- The sequence of presheaves `0 ⟶ F ⟶ I ⟶ G ⟶ 0`, where `F ⟶ I` is the chosen embedding into an
injective sheaf and `G` is the image presheaf of `I ⟶ Q`, for `Q` its cokernel sheaf. Unlike the
cokernel sequence of sheaves, it is exact on the sections over every open
(`TauCeti.Topology.injectiveImageSequence_map_shortExact`). -/
abbrev injectiveImageSequence : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  ShortComplex.mk (Injective.ι F).hom (factorThruImage (cokernel.π (Injective.ι F)).hom) (by
    rw [← cancel_mono (image.ι _), Category.assoc, image.fac, zero_comp]
    exact ((injectiveCokernelSequence F).map (sheafToPresheaf _ AddCommGrpCat.{u})).zero)

/-- The sequence `0 ⟶ F ⟶ I ⟶ G ⟶ 0` is exact on every open: the kernel of `I(V) ⟶ Q(V)` is
`F(V)`, and `G(V)` is the image of `I(V)` in `Q(V)`. -/
theorem injectiveImageSequence_map_shortExact (V : (Opens X)ᵒᵖ) :
    ((injectiveImageSequence F).map ((evaluation _ AddCommGrpCat.{u}).obj V)).ShortExact := by
  have hE := (injectiveCokernelSequence_shortExact F).exact.map_of_mono_of_preservesKernel
    (sheafToPresheaf _ AddCommGrpCat.{u} ⋙ (evaluation _ AddCommGrpCat.{u}).obj V)
    inferInstance inferInstance
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ab_exact_iff] at hE ⊢
    intro x hx
    apply hE x
    dsimp at hx ⊢
    have h := congrArg ((image.ι (cokernel.π (Injective.ι F)).hom).app V) hx
    rwa [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, image.fac, map_zero] at h
  · exact Functor.map_mono (sheafToPresheaf _ AddCommGrpCat.{u} ⋙
      (evaluation _ AddCommGrpCat.{u}).obj V) (Injective.ι F)
  · dsimp
    infer_instance

end TauCeti.Topology
