/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import TauCeti.Topology.Covering.IsFiniteCover
public import TauCeti.Topology.Covering.Pullback

/-!
# Pullbacks of finite covers

The pullback of a finite covering map along a continuous map remains a finite cover. This
supplies the finite cover of a hypersurface obtained by pulling back an ambient finite cover.

Adapted from Riccardo Brasca's `ForTauCeti` formalization in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/e965b7833fd9d435ce18a25c7624dc8866c7acf2/ForTauCeti/Topology/Covering/FinitePullback.lean).
-/

public section

open Function

namespace TauCeti

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {f : X → Y} {p : Z → Y}

/-- A finite cover stays finite after pullback along a continuous map. -/
theorem IsFiniteCover.pullback_fst (hp : IsFiniteCover p) (hf : Continuous f) :
    IsFiniteCover (Pullback.fst : f.Pullback p → X) where
  isCoveringMap := hp.isCoveringMap.pullback_fst hf
  surjective := Pullback.fst_surjective_iff.mpr (by simp [hp.surjective.range_eq])
  finite_fiber := fun x ↦ (Pullback.finite_preimage_fst_singleton_iff x).mpr
    (hp.finite_fiber (f x))

end TauCeti
