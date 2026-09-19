/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Refining quasi-coherent data

Quasi-coherent data for a sheaf of modules `M` consists of a covering family `X i` together with
a presentation of each restriction `M.over (X i)`. Given a second covering family `Y j` refining
the first one, meaning that each `Y j` comes with an arrow to some `X i`, restricting the
presentations along these arrows gives quasi-coherent data for `M` on the family `Y j`.

Restriction along an arrow `f : Y ⟶ X` is Mathlib's `SheafOfModules.overMap`. On a site with
pullbacks it is a left adjoint, so it maps presentations to presentations
(`SheafOfModules.Presentation.map`); `SheafOfModules.overFunctorMap` identifies the restriction of
`M.over X` with `M.over Y`.

This lets two quasi-coherent sheaves be presented on a common refinement of their covers, which is
how the tensor product of quasi-coherent sheaves is shown to be quasi-coherent.

## Main declaration

* `SheafOfModules.QuasicoherentData.ofRefinement`.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe w u v₁ u₁

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Quasi-coherent data for `M` transported to a refining covering family `Y`: each `Y i` maps to
the member `q.X (index i)` of the original cover by `map i`, and the presentation of
`M.over (Y i)` is the restriction of the presentation of `M.over (q.X (index i))` along
`map i`. -/
@[expose, simps I X presentation]
def _root_.SheafOfModules.QuasicoherentData.ofRefinement {M : SheafOfModules.{u} R}
    (q : M.QuasicoherentData) {I : Type w} (Y : I → C) (coversTop : J.CoversTop Y)
    (index : I → q.I) (map : ∀ i, Y i ⟶ q.X (index i)) : M.QuasicoherentData where
  I := I
  X := Y
  coversTop := coversTop
  presentation i :=
    ((q.presentation (index i)).map (overMap R (map i)) (overMapUnitIso (map i)).symm).ofIsIso
      ((overFunctorMap R (map i)).hom.app M)

end SheafOfModules

end

end TauCeti
