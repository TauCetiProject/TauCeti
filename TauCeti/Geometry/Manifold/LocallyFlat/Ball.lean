/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.BallSphere
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic

/-!
# Locally flat maps into a closed ball

The open ball is an open subset of both the closed ball and the ambient space. A map into a
closed ball that avoids its boundary sphere is therefore locally flat in the closed ball as soon
as it is locally flat as a map into the ambient space
(`TauCeti.IsLocallyFlat.of_coe_closedBall`).
-/

public section

open Metric Set Topology

namespace TauCeti

/-- A map into a closed ball centred at zero that avoids the boundary sphere is locally flat as
soon as it is locally flat as a map into the ambient space. -/
theorem IsLocallyFlat.of_coe_closedBall {E X G G' : Type*} [SeminormedAddCommGroup E]
    [TopologicalSpace X] [TopologicalSpace G] [TopologicalSpace G'] [Zero G'] {r : ℝ}
    {g : X → closedBall (0 : E) r} (hg : ∀ x, ‖(g x : E)‖ < r)
    (h : IsLocallyFlat G G' fun x => (g x : E)) : IsLocallyFlat G G' g := by
  set O := {y : closedBall (0 : E) r | ‖(y : E)‖ < r}
  have hO : IsOpen O := isOpen_lt (by fun_prop) continuous_const
  exact (IsLocallyFlat.of_isOpenEmbedding_comp (g := fun y : O => ((y : closedBall (0 : E) r) : E))
    (f := fun x => (⟨g x, hg x⟩ : O)) (hO.isOpenEmbedding_coe_openSubset_closedBall fun y hy => hy)
    h).isOpenEmbedding_comp hO.isOpenEmbedding_subtypeVal

end TauCeti
