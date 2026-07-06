/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic

/-!
# Continuity consequences of `J`-holomorphicity

This file records the basic regularity consequences of the local `J`-holomorphic predicates
used by the analytic Heegaard Floer roadmap. In the current normed-vector-space model, a
`J`-holomorphic map is defined by the existence of a Frechet derivative satisfying the
Cauchy--Riemann equation. The derivative witness already implies the usual differentiability
and continuity facts; this module packages those consequences so later local curve arguments can
consume them without unfolding `IsJHolomorphicAt` or `IsJHolomorphicWithinAt`.

The statements are deliberately no stronger than the existing definitions justify. They are
chart-level bookkeeping for the later almost-complex-manifold and holomorphic-curve local theory
in `TauCetiRoadmap/HeegaardFloer/README.md`, Lane F2.1.

## Main declarations

* `TauCeti.IsJHolomorphicAt.continuousAt`: pointwise `J`-holomorphicity implies continuity at
  the point.
* `TauCeti.IsJHolomorphicWithinAt.continuousWithinAt`: within-set `J`-holomorphicity implies
  continuity within the source set.
* `TauCeti.IsJHolomorphicOn.differentiableOn` and
  `TauCeti.IsJHolomorphicOn.continuousOn`: setwise regularity consequences.
* `TauCeti.IsJHolomorphic.differentiable` and `TauCeti.IsJHolomorphic.continuous`: global
  regularity consequences.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: the analytic condition is the Frechet-derivative equation
`df ∘ J = J' ∘ df`.
-/

public section

namespace TauCeti

variable {V W : Type*}

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

variable {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
variable {f : V → W} {s : Set V} {x : V}

namespace IsJHolomorphicAt

/-- A pointwise `J`-holomorphic map is continuous at the point. -/
lemma continuousAt (hf : IsJHolomorphicAt J J' f x) : ContinuousAt f x :=
  hf.hasFDerivAt.continuousAt

/-- A pointwise `J`-holomorphic map is continuous within any source set at the point. -/
lemma continuousWithinAt (hf : IsJHolomorphicAt J J' f x) :
    ContinuousWithinAt f s x :=
  hf.continuousAt.continuousWithinAt

end IsJHolomorphicAt

namespace IsJHolomorphicWithinAt

/-- A map that is `J`-holomorphic within a set is continuous within that set at the point. -/
lemma continuousWithinAt (hf : IsJHolomorphicWithinAt J J' f s x) :
    ContinuousWithinAt f s x :=
  hf.hasFDerivWithinAt.continuousWithinAt

/-- A map that is `J`-holomorphic within a neighborhood of the point is continuous at the
point. -/
lemma continuousAt_of_mem_nhds (hf : IsJHolomorphicWithinAt J J' f s x) (hs : s ∈ nhds x) :
    ContinuousAt f x :=
  hf.continuousWithinAt.continuousAt hs

/-- A map that is `J`-holomorphic within a neighborhood of the point is differentiable at the
point. -/
lemma differentiableAt_of_mem_nhds (hf : IsJHolomorphicWithinAt J J' f s x) (hs : s ∈ nhds x) :
    DifferentiableAt ℝ f x :=
  (hf.isJHolomorphicAt_of_mem_nhds hs).differentiableAt

/-- A map that is `J`-holomorphic within a set is continuous within every smaller source set at
the point. -/
lemma continuousWithinAt_mono (hf : IsJHolomorphicWithinAt J J' f s x) {t : Set V}
    (hts : t ⊆ s) : ContinuousWithinAt f t x :=
  hf.continuousWithinAt.mono hts

end IsJHolomorphicWithinAt

namespace IsJHolomorphicOn

/-- A map that is `J`-holomorphic on a set is differentiable on that set. -/
lemma differentiableOn (hf : IsJHolomorphicOn J J' f s) :
    DifferentiableOn ℝ f s :=
  fun x hx => (hf x hx).differentiableWithinAt

/-- A map that is `J`-holomorphic on a set is differentiable within that set at each of its
points. -/
lemma differentiableWithinAt (hf : IsJHolomorphicOn J J' f s) (hx : x ∈ s) :
    DifferentiableWithinAt ℝ f s x :=
  (hf x hx).differentiableWithinAt

/-- A map that is `J`-holomorphic on a set is continuous on that set. -/
lemma continuousOn (hf : IsJHolomorphicOn J J' f s) :
    ContinuousOn f s :=
  fun x hx => (hf x hx).continuousWithinAt

/-- A map that is `J`-holomorphic on a set is continuous within that set at each of its points. -/
lemma continuousWithinAt (hf : IsJHolomorphicOn J J' f s) (hx : x ∈ s) :
    ContinuousWithinAt f s x :=
  (hf x hx).continuousWithinAt

/-- A map that is `J`-holomorphic on an open set is pointwise differentiable at each point of
that set. -/
lemma differentiableAt_of_isOpen (hf : IsJHolomorphicOn J J' f s) (hs : IsOpen s)
    (hx : x ∈ s) : DifferentiableAt ℝ f x :=
  (hf x hx).differentiableAt_of_mem_nhds (hs.mem_nhds hx)

/-- A map that is `J`-holomorphic on an open set is continuous at each point of that set. -/
lemma continuousAt_of_isOpen (hf : IsJHolomorphicOn J J' f s) (hs : IsOpen s)
    (hx : x ∈ s) : ContinuousAt f x :=
  (hf x hx).continuousAt_of_mem_nhds (hs.mem_nhds hx)

end IsJHolomorphicOn

namespace IsJHolomorphic

/-- A globally `J`-holomorphic map is differentiable. -/
lemma differentiable (hf : IsJHolomorphic J J' f) : Differentiable ℝ f :=
  fun x => (hf x).differentiableAt

/-- A globally `J`-holomorphic map is differentiable at every point. -/
lemma differentiableAt (hf : IsJHolomorphic J J' f) (x : V) : DifferentiableAt ℝ f x :=
  (hf x).differentiableAt

/-- A globally `J`-holomorphic map is continuous. -/
lemma continuous (hf : IsJHolomorphic J J' f) : Continuous f :=
  continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt

/-- A globally `J`-holomorphic map is continuous at every point. -/
lemma continuousAt (hf : IsJHolomorphic J J' f) (x : V) : ContinuousAt f x :=
  (hf x).continuousAt

/-- A globally `J`-holomorphic map is differentiable on every source set. -/
lemma differentiableOn (hf : IsJHolomorphic J J' f) (s : Set V) : DifferentiableOn ℝ f s :=
  (hf.isJHolomorphicOn s).differentiableOn

/-- A globally `J`-holomorphic map is continuous on every source set. -/
lemma continuousOn (hf : IsJHolomorphic J J' f) (s : Set V) : ContinuousOn f s :=
  (hf.isJHolomorphicOn s).continuousOn

end IsJHolomorphic

end TauCeti
