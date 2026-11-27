/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.HomGroupoid

/-!
# Checks for band preservation along modifications

For pseudofunctors `F`, `G` with `A`-bandings, `G` with groupoid fibres:

* a modification `m : η ⟶ θ` with no invertibility hypothesis carries band preservation of `η`
  to `θ`, and of `θ` back to `η`.
-/

public section

namespace TauCeti.Examples.BandedMorphismHomGroupoid

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Bicategory
open scoped Pseudofunctor.StrongTrans
open BandedMorphism

variable {C : Type*} [Category* C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat}
  [∀ U : C, IsGroupoid (G.obj (.mk (op U)))]
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat}
  {bF : F.AbelianBanding J A} {bG : G.AbelianBanding J A}

/-- A modification carries band preservation of its source to its target. -/
example {η θ : F ⟶ G} (m : η ⟶ θ) [BandPreserving bF bG η] : BandPreserving bF bG θ :=
  (modification_iff m).1 inferInstance

/-- A modification carries band preservation of its target back to its source. -/
example {η θ : F ⟶ G} (m : η ⟶ θ) [BandPreserving bF bG θ] : BandPreserving bF bG η :=
  (modification_iff m).2 inferInstance

end TauCeti.Examples.BandedMorphismHomGroupoid
