/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeology.Coinduced

/-!
# Quotient diffeologies on quotient types

This file equips the quotient `Quotient s` of a diffeological space by a setoid with the quotient
diffeology, the diffeology coinduced by `Quotient.mk s`. It is the diffeological counterpart of
Mathlib's quotient topology `instTopologicalSpaceQuotient`. A map from a Cartesian space to the
quotient is a plot exactly when it locally lifts to plots of the space, the projection is a
subduction, and a function out of the quotient is smooth exactly when its composite with the
projection is.

Since `MulAction.orbitRel.Quotient G X` is by definition the quotient by the orbit relation, this
is in particular the diffeology on the orbit space of a group action, for instance the coarse
smooth structure on the quotient of a chart by a finite group acting smoothly. No finiteness or
smoothness of the action is needed for the statements here.

The D-topology of the quotient diffeology is the quotient of the D-topology of the space. Hence,
whenever the topology of the space is its D-topology, the D-topology of the quotient is the
ordinary quotient topology, so the quotient diffeology is compatible with Mathlib's topology on
the quotient type (`TauCeti.Diffeology.instIsDTopologyCompatibleQuotient`).

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), Article 1.50 for quotient diffeologies and Chapter 2 for the
  D-topology.
-/

public noncomputable section

open Function Set
open scoped ContDiff

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

variable {X Y : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] (s : Setoid X)

/-- The quotient diffeology on a quotient type: the diffeology coinduced by the projection. -/
instance instDiffeologicalSpaceQuotient : DiffeologicalSpace (Quotient s) :=
  coinducedDiffeology (Quotient.mk s)

/-- A map is a plot of the quotient exactly when it locally lifts through the projection. -/
theorem isPlot_quotient_iff {n : ℕ} {p : 𝔼ⁿ → Quotient s} :
    _root_.Diffeology.IsPlot p ↔ LocallyLifts (Quotient.mk s) univ p :=
  isPlot_coinducedDiffeology_iff_locallyLifts Quotient.mk_surjective

/-- The projection onto a quotient is a subduction. -/
theorem isSubduction_quotient_mk : IsSubduction (Quotient.mk s) :=
  isSubduction_coinducedDiffeology Quotient.mk_surjective

/-- The projection onto a quotient is smooth. -/
@[fun_prop]
theorem dSmooth_quotient_mk : _root_.Diffeology.DSmooth (Quotient.mk s) :=
  (isSubduction_quotient_mk s).dSmooth

variable {s}

/-- Descent to a quotient: a function out of a quotient is smooth exactly when the function on
the space it descends from is smooth. -/
@[simp]
theorem dSmooth_quotient_lift_iff {f : X → Y} (hs : ∀ a b, a ≈ b → f a = f b) :
    _root_.Diffeology.DSmooth (Quotient.lift f hs : Quotient s → Y) ↔
      _root_.Diffeology.DSmooth f := by
  rw [(isSubduction_quotient_mk s).dSmooth_iff, Quotient.lift_comp_mk]

/-- A smooth function that is constant on equivalence classes descends to a smooth function on
the quotient. -/
@[fun_prop]
theorem _root_.Diffeology.DSmooth.quotient_lift {f : X → Y} (hf : _root_.Diffeology.DSmooth f)
    (hs : ∀ a b, a ≈ b → f a = f b) :
    _root_.Diffeology.DSmooth (Quotient.lift f hs : Quotient s → Y) :=
  (dSmooth_quotient_lift_iff hs).mpr hf

/-- A smooth map respecting two equivalence relations induces a smooth map of quotients. -/
@[fun_prop]
theorem _root_.Diffeology.DSmooth.quotient_map {t : Setoid Y} {f : X → Y}
    (hf : _root_.Diffeology.DSmooth f) (h : ∀ ⦃a b⦄, a ≈ b → f a ≈ f b) :
    _root_.Diffeology.DSmooth (Quotient.map f h : Quotient s → Quotient t) :=
  ((dSmooth_quotient_mk t).comp hf).quotient_lift _

/-- The D-topology of a quotient diffeology is the quotient of the D-topology of the space. -/
theorem isQuotientMap_dTopology_quotient_mk :
    @Topology.IsQuotientMap X (Quotient s) _root_.Diffeology.dTopology _root_.Diffeology.dTopology
      (Quotient.mk s) :=
  (isSubduction_quotient_mk s).isQuotientMap_dTopology

/-- If the topology of a space is its D-topology, then the D-topology of a quotient is the
quotient topology. -/
instance instIsDTopologyCompatibleQuotient [TopologicalSpace X]
    [_root_.Diffeology.IsDTopologyCompatible X] :
    _root_.Diffeology.IsDTopologyCompatible (Quotient s) :=
  (isSubduction_quotient_mk s).isDTopologyCompatible isQuotientMap_quotient_mk'

end TauCeti.Diffeology
