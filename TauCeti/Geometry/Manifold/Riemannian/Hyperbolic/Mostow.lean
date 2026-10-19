/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.Isometry

/-!
# Mostow rigidity for hyperbolic metrics

This file records the metric-level statement of Mostow rigidity for closed hyperbolic manifolds.
The resulting relation supports comparing the total volumes carried by different hyperbolic
metrics.

The formulation follows Ratcliffe, *Foundations of Hyperbolic Manifolds*, 3rd ed., Theorem
11.8.5.
-/

public section

open Manifold Bundle
open scoped ContDiff Manifold

noncomputable section

universe uE uH uM

namespace TauCeti

variable {E : Type uE} {H : Type uH} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [T3Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The metric-level conclusion of Mostow rigidity for one fixed manifold and dimension.

The predicate asserts that every pair of bundled hyperbolic metrics on a closed, connected,
boundaryless manifold of real dimension at least three is related by a bundled isometry. -/
def IsMostowRigid : Prop :=
  ∀ [BoundarylessManifold I M] [CompactSpace M] [ConnectedSpace M],
    3 ≤ Module.finrank ℝ E →
      ∀ (g g' : HyperbolicMetric (I := I) (M := M)),
        Nonempty (HyperbolicMetric.Isometry g g')

/-- A fixed-manifold Mostow-rigidity predicate is equivalent to its characteristic statement. -/
theorem isMostowRigid_iff :
    IsMostowRigid (I := I) (M := M) ↔
      ∀ [BoundarylessManifold I M] [CompactSpace M] [ConnectedSpace M],
        3 ≤ Module.finrank ℝ E →
          ∀ (g g' : HyperbolicMetric (I := I) (M := M)),
            Nonempty (HyperbolicMetric.Isometry g g') := by
  rfl

/-- Introduce fixed-manifold Mostow rigidity from its characteristic statement. -/
theorem isMostowRigid_of
    (h : ∀ [BoundarylessManifold I M] [CompactSpace M] [ConnectedSpace M],
      3 ≤ Module.finrank ℝ E →
        ∀ (g g' : HyperbolicMetric (I := I) (M := M)),
          Nonempty (HyperbolicMetric.Isometry g g')) :
    IsMostowRigid (I := I) (M := M) := by
  exact h

/-- Extract the isometry conclusion from a fixed-manifold Mostow-rigidity hypothesis. -/
theorem IsMostowRigid.isometry [BoundarylessManifold I M] [CompactSpace M] [ConnectedSpace M]
    (h : IsMostowRigid (I := I) (M := M)) {hdim : 3 ≤ Module.finrank ℝ E}
    (g g' : HyperbolicMetric (I := I) (M := M)) :
    Nonempty (HyperbolicMetric.Isometry g g') := by
  exact h hdim g g'

/-- The Mostow rigidity statement, universally over closed connected manifolds. -/
def MostowRigidity : Prop :=
  ∀ {E : Type uE} {H : Type uH} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [T3Space M] [ChartedSpace H M] [IsManifold I ∞ M],
    IsMostowRigid (I := I) (M := M)

/-- Specialize the universal Mostow-rigidity statement to one manifold. -/
theorem MostowRigidity.isMostowRigid (h : MostowRigidity.{uE, uH, uM}) :
    IsMostowRigid (I := I) (M := M) := by
  exact h (E := E) (H := H) (M := M) (I := I)

end TauCeti
