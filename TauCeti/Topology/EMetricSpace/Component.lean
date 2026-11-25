/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Sets.Opens

/-!
# Metrics on finite-distance components

The finite-distance component of `x` in an extended pseudometric space is the existing subtype
`Metric.eball x ∞`. Its extended distances are finite, so Mathlib's
`PseudoEMetricSpace.toPseudoMetricSpace` gives it a pseudometric with the inherited extended
distance and uniformity. For a separated ambient space, Mathlib's `metricSpaceEMetricBall`
supplies the corresponding metric. If the ambient space is complete, so is the component, since
it is closed.

These instances allow the usual metric-valued theory of absolutely continuous curves and gradient
flows to be applied on a finite-distance component of an extended metric space. The metric
instances have low priority so that an ambient (pseudo)metric space retains its usual subtype
instance. In either case, `dist_edist` identifies the distance with the real value of the inherited
extended distance. Anchors at finite distance define the same component.

The component is open, and `TauCeti.eballTopOpens x` is the same component as an element of
`TopologicalSpace.Opens`, the form used for open submanifolds. The canonical instances above are
also registered on this open-set view.
-/

public section

open scoped ENNReal

namespace TauCeti

variable {X : Type*}

/-- The finite-distance component of an extended pseudometric space has the inherited uniformity
and the distance obtained by taking the real value of its extended distance. The usual subtype
pseudometric takes precedence when the ambient space already has a pseudometric. -/
noncomputable instance (priority := low) instPseudoMetricSpaceEBallTop [PseudoEMetricSpace X]
    (x : X) : PseudoMetricSpace (Metric.eball x ∞) :=
  PseudoEMetricSpace.toPseudoMetricSpace fun y z ↦
    ((edist_triangle (y : X) x z).trans_lt (ENNReal.add_lt_top.2
      ⟨y.property, by simpa only [Metric.mem_eball, edist_comm] using z.property⟩)).ne

/-- A finite-distance component of an extended metric space is a metric space. The usual subtype
metric takes precedence when the ambient space already has a metric. -/
noncomputable instance (priority := low) instMetricSpaceEBallTop [EMetricSpace X] (x : X) :
    MetricSpace (Metric.eball x ∞) :=
  metricSpaceEMetricBall x ∞

/-- A finite-distance component of a complete extended pseudometric space is complete. -/
instance instCompleteSpaceEBallTop [PseudoEMetricSpace X] [CompleteSpace X] (x : X) :
    CompleteSpace (Metric.eball x ∞) :=
  Metric.isClosed_eball_top.isComplete.completeSpace_coe

/-- Moving the anchor by a finite distance leaves its finite-distance component unchanged. -/
theorem eball_top_eq_of_edist_ne_top [TopologicalSpace X] [WeakPseudoEMetricSpace X]
    {x y : X} (hxy : edist x y ≠ ∞) :
    Metric.eball x ∞ = Metric.eball y ∞ :=
  Set.Subset.antisymm (Metric.eball_subset le_top hxy)
    (Metric.eball_subset le_top (by simpa only [edist_comm] using hxy))

/-- The finite-distance component of `x`, as an open set. It is reducible so that the metric
instances below, transferred from `Metric.eball x ∞`, unfold at instance transparency to the
subtype topology used by the charts of open submanifolds. -/
abbrev eballTopOpens [PseudoEMetricSpace X] (x : X) : TopologicalSpace.Opens X :=
  ⟨Metric.eball x ∞, Metric.isOpen_eball⟩

/-- The open-set view of the finite-distance component has the points of `Metric.eball x ∞`. -/
@[simp]
theorem coe_eballTopOpens [PseudoEMetricSpace X] (x : X) :
    (eballTopOpens x : Set X) = Metric.eball x ∞ :=
  rfl

/-- A point lies in the finite-distance component of `x` if and only if it is at finite distance
from `x`. -/
theorem mem_eballTopOpens [PseudoEMetricSpace X] {x y : X} :
    y ∈ eballTopOpens x ↔ edist y x < ∞ :=
  Iff.rfl

/-- The pseudometric `TauCeti.instPseudoMetricSpaceEBallTop`, on the open-set view of the
finite-distance component. -/
noncomputable instance (priority := low) instPseudoMetricSpaceEBallTopOpens
    [PseudoEMetricSpace X] (x : X) : PseudoMetricSpace (eballTopOpens x) :=
  instPseudoMetricSpaceEBallTop x

/-- The metric `TauCeti.instMetricSpaceEBallTop`, on the open-set view of the finite-distance
component. Its topology is the subtype topology up to unfolding instances, so it is compatible
with the charts of open submanifolds. -/
noncomputable instance (priority := low) instMetricSpaceEBallTopOpens [EMetricSpace X] (x : X) :
    MetricSpace (eballTopOpens x) :=
  instMetricSpaceEBallTop x

/-- The open-set view of a finite-distance component of a complete space is complete. -/
instance instCompleteSpaceEBallTopOpens [PseudoEMetricSpace X] [CompleteSpace X] (x : X) :
    CompleteSpace (eballTopOpens x) :=
  instCompleteSpaceEBallTop x

end TauCeti
