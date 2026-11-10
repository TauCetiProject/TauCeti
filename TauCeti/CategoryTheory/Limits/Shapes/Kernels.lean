/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import TauCeti.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Colimits commute with cokernels

Let `α : F ⟶ G` and `π : G ⟶ H` be natural transformations of diagrams `J ⥤ D` such that each
component `π j` is a cokernel of `α j`.  If `F` and `G` have colimit cocones, then a cocone on `H`
whose apex is the cokernel of the map induced by `α` on the colimits is itself a colimit cocone
(`TauCeti.isColimitOfIsColimitCokernelCofork`).  No existence of colimits or cokernels in `D` is
assumed: all the relevant cocones and coforks are given.  This is the special case of
`TauCeti.isColimitOfIsColimitCofork` for coequalizers with the zero morphism.

This is how a quotient construction, such as relative chains as the quotient of the chains of a
space by those of a subspace, inherits a colimit description from the two objects it is formed
from.
-/

public section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace TauCeti

variable {J : Type u₁} [Category.{v₁} J] {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]
  {F G H : J ⥤ D} {α : F ⟶ G} {π : G ⟶ H} {w : ∀ j, α.app j ≫ π.app j = 0}
  {cF : Cocone F} {cG : Cocone G} {cH : Cocone H} {f : cF.pt ⟶ cG.pt} {p : cG.pt ⟶ cH.pt}
  {wp : f ≫ p = 0}

/-- **Colimits commute with cokernels.**  Let `π j` be a cokernel of `α j` for every `j`, let `cF`
and `cG` be colimit cocones, and let `f` and `p` be maps of apexes compatible with `α` and `π`.
If `p` is a cokernel of `f`, then `cH` is a colimit cocone. -/
def isColimitOfIsColimitCokernelCofork (hπ : ∀ j, IsColimit (CokernelCofork.ofπ _ (w j)))
    (hF : IsColimit cF) (hG : IsColimit cG)
    (hf : ∀ j, cF.ι.app j ≫ f = α.app j ≫ cG.ι.app j)
    (hp : ∀ j, cG.ι.app j ≫ p = π.app j ≫ cH.ι.app j)
    (hcok : IsColimit (CokernelCofork.ofπ p wp)) : IsColimit cH :=
  isColimitOfIsColimitCofork (β := 0) (g := 0) hπ hF hG hf (fun _ ↦ by simp) hp hcok

end TauCeti
