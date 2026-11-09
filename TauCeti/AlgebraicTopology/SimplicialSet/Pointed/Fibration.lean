/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.PullbackHom

import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Kan fibrations of based mapping simplicial sets

The based mapping simplicial set preserves Kan fibrations in its target. In particular,
based maps into a Kan complex form a Kan complex, and simplicial loops preserve Kan complexes.
These are point-set lifting statements, independent of a stable model structure.

The target-only assertion is the based pullback–hom corner theorem applied to the
initial based map. The Kan-complex assertion uses the unpointed restriction map at
the basepoint; its fibre retains the prescribed basepoint.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Chapter I.
-/

public section

open CategoryTheory CategoryTheory.ConcreteCategory MonoidalCategory MonoidalClosed Limits
  HomotopicalAlgebra
open scoped Simplicial

universe u

namespace TauCeti.PointedSSet

open SSet.modelCategoryQuillen

variable {X E B : PointedSSet.{u}}

/-- The based mapping simplicial set preserves Kan fibrations in the target. -/
instance fibration_ihom_map (X : PointedSSet.{u}) (p : E ⟶ B) [Fibration p.right] :
    Fibration ((PointedSSet.ihom X).map p).right := by
  let i : Under.mk (𝟙 (Δ[0] : SSet.{u})) ⟶ X := Under.homMk X.hom
  have : Mono i.right := SSet.stdSimplex.isTerminalObj₀.mono_from X.hom
  exact fibration_pullbackObjObjπ i p
    (Functor.PullbackObjObj.ofIsInitial MonoidalClosed.internalHom i p Under.mkIdInitial)

/-- Based maps into a Kan complex form a Kan complex, with no hypothesis on the source. -/
instance kanComplex_ihom (X E : PointedSSet.{u}) [SSet.KanComplex E.right] :
    SSet.KanComplex ((PointedSSet.ihom X).obj E).right := by
  have : Mono X.hom := SSet.stdSimplex.isTerminalObj₀.mono_from X.hom
  have hf : Fibration (SSet.stdSimplex.isTerminalObj₀.from (basedMaps X E).toSSet) := by
    rw [SSet.modelCategoryQuillen.fibration_iff]
    exact MorphismProperty.of_isPullback (basedMaps_isPullback X E)
      ((SSet.modelCategoryQuillen.fibration_iff _).1 inferInstance)
  exact (isFibrant_iff_of_isTerminal _ SSet.stdSimplex.isTerminalObj₀).2 hf

end TauCeti.PointedSSet
