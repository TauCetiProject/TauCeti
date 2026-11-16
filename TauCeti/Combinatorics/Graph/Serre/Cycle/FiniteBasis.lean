/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Cycle.Basis
public import TauCeti.Combinatorics.Graph.Serre.Cycle.Coordinates
public import TauCeti.Combinatorics.Graph.Serre.Cycle.SpanningTree

/-!
# Fundamental bases in finite binary cycle coordinates

The fundamental cycles of a spanning forest form a basis of the binary incidence kernel
`SerreGraph.cycleSpace`, expressed as functions on the chosen darts. The coefficient of each
fundamental cycle is the value of the original cycle at its chord. Thus restriction to chords
specifies a cycle uniquely, and every chord assignment has a unique cycle completion.

The construction transports the Finsupp forest basis through `cycleSpaceFinsuppEquiv`; it does
not choose another family of forest return paths. No connectedness or orientation is needed
for the forest results. For a spanning tree and an orientation, the basis is indexed by the
positive non-tree darts and the dimension is `#O + 1 - #V`.

## References

* R. Diestel, *Graph Theory*, §1.9, Theorem 1.9.6 (fundamental cycle bases).
* A. Hatcher, *Algebraic Topology*, §1.A and §2.2 (tree loops and incidence boundaries).
-/

public section

namespace TauCeti.SerreGraph

variable {Γ : SerreGraph} {O F : Set Γ.E} [Finite Γ.V] [Finite O]

/-- The fundamental binary cycles in finite-function coordinates, indexed by the chords of
any spanning forest. -/
noncomputable def IsSpanningForest.cycleSpaceBasis (hF : Γ.IsSpanningForest O F) :
    Module.Basis ↥(O \ F) (ZMod 2) (Γ.cycleSpace O) :=
  (hF.cycleBasis (ZMod 2)).map
    ((LinearEquiv.ofEq _ _ (modTwoCycleSpace_def (Γ := Γ) (O := O)).symm).trans
      (Γ.cycleSpaceFinsuppEquiv O))

/-- The finite-coordinate fundamental cycle has the same values on all darts as its
Finsupp counterpart. -/
theorem IsSpanningForest.cycleSpaceBasis_val (hF : Γ.IsSpanningForest O F)
    (e : ↥(O \ F)) :
    (hF.cycleSpaceBasis e).val = ⇑(hF.cycleBasis (ZMod 2) e).val := by
  ext d
  simp [IsSpanningForest.cycleSpaceBasis, LinearEquiv.coe_ofEq_apply,
    Finsupp.linearEquivFunOnFinite_apply]

/-- Fundamental-cycle coefficients are precisely the chord values of a binary cycle. -/
@[simp] theorem IsSpanningForest.cycleSpaceBasis_repr (hF : Γ.IsSpanningForest O F)
    (c : Γ.cycleSpace O) (e : ↥(O \ F)) :
    hF.cycleSpaceBasis.repr c e = c.val ⟨e.val, e.property.1⟩ := by
  simp [IsSpanningForest.cycleSpaceBasis, LinearEquiv.coe_ofEq_apply]

/-- The fundamental binary cycle through a chord has value one at that chord and zero at
every other chord. -/
@[simp] theorem IsSpanningForest.cycleSpaceBasis_apply_chord (hF : Γ.IsSpanningForest O F)
    (e f : ↥(O \ F)) :
    (hF.cycleSpaceBasis e).val ⟨f.val, f.property.1⟩ = Finsupp.single e (1 : ZMod 2) f := by
  rw [← hF.cycleSpaceBasis_repr]
  simp

/-- Every assignment on the chords extends uniquely to a binary cycle, with no connectedness
assumption on the graph. -/
theorem IsSpanningForest.existsUnique_cycleSpace_val_eq (hF : Γ.IsSpanningForest O F)
    (a : ↥(O \ F) → ZMod 2) :
    ∃! c : Γ.cycleSpace O, ∀ e : ↥(O \ F), c.val ⟨e.val, e.property.1⟩ = a e := by
  simpa [funext_iff] using hF.cycleSpaceBasis.equivFun.bijective.existsUnique a

/-- The dimension of the finite-function binary cycle space is the number of chords of any
spanning forest. -/
theorem IsSpanningForest.finrank_cycleSpace (hF : Γ.IsSpanningForest O F) :
    Module.finrank (ZMod 2) (Γ.cycleSpace O) = Nat.card ↥(O \ F) :=
  Module.finrank_eq_nat_card_basis hF.cycleSpaceBasis

/-- Binary cycle dimension, plus vertices, equals edges plus components, also for disconnected
and empty graphs. -/
theorem finrank_cycleSpace_add_card :
    Module.finrank (ZMod 2) (Γ.cycleSpace O) + Nat.card Γ.V =
      Nat.card O + Nat.card (Γ.supportGraph O).ConnectedComponent := by
  rw [← (Γ.cycleSpaceFinsuppEquiv O).finrank_eq, modTwoCycleSpace_def]
  exact finrank_ker_incidenceBoundary_add_card (Γ := Γ) (O := O) (R := ZMod 2)

namespace SpanningTree

variable (T : Γ.SpanningTree) (hO : Γ.IsOrientation O)

/-- The fundamental binary cycle basis of a spanning tree, indexed by the positive non-tree
darts. -/
noncomputable def cycleSpaceBasis : Module.Basis ↥(O \ T.darts) (ZMod 2) (Γ.cycleSpace O) :=
  ((T.isSpanningForest hO).cycleSpaceBasis).reindex
    (Set.equivOfEq Set.sdiff_inter_self_eq_sdiff)

/-- A tree fundamental cycle is the corresponding cycle of its positive spanning forest. -/
theorem cycleSpaceBasis_apply (e : ↥(O \ T.darts)) :
    T.cycleSpaceBasis hO e = (T.isSpanningForest hO).cycleSpaceBasis
      ⟨e.val, e.property.1, fun h => e.property.2 h.1⟩ := by
  simp [cycleSpaceBasis]

/-- In tree coordinates too, the coefficient of a fundamental cycle is its non-tree dart
coordinate. -/
@[simp] theorem cycleSpaceBasis_repr (c : Γ.cycleSpace O) (e : ↥(O \ T.darts)) :
    (T.cycleSpaceBasis hO).repr c e = c.val ⟨e.val, e.property.1⟩ := by
  simp [cycleSpaceBasis]

/-- The fundamental cycles through positive non-tree darts have unit non-tree coordinates. -/
@[simp] theorem cycleSpaceBasis_apply_chord (e f : ↥(O \ T.darts)) :
    (T.cycleSpaceBasis hO e).val ⟨f.val, f.property.1⟩ = Finsupp.single e (1 : ZMod 2) f := by
  rw [← T.cycleSpaceBasis_repr hO]
  simp

end SpanningTree

/-- The Euler dimension formula for the binary cycle space of a connected graph, stated
additively to avoid truncated subtraction. -/
theorem IsOrientation.finrank_cycleSpace_add_card (hO : Γ.IsOrientation O) (h : Γ.Connected) :
    Module.finrank (ZMod 2) (Γ.cycleSpace O) + Nat.card Γ.V = Nat.card O + 1 := by
  rw [SerreGraph.finrank_cycleSpace_add_card, SimpleGraph.card_connectedComponent_eq_one_iff.mpr
    (hO.connected_supportGraph_iff.mpr h)]

/-- The binary cycle space of a connected finite graph has dimension `#O + 1 - #V`. -/
theorem IsOrientation.finrank_cycleSpace (hO : Γ.IsOrientation O) (h : Γ.Connected) :
    Module.finrank (ZMod 2) (Γ.cycleSpace O) = Nat.card O + 1 - Nat.card Γ.V := by
  have := hO.finrank_cycleSpace_add_card h
  omega

end TauCeti.SerreGraph
