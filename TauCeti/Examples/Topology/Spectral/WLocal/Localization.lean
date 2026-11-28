/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Spectral.WLocal.Localization
public import TauCeti.Topology.Spectral.SpectralMap
import TauCeti.Topology.Order.Sierpinski

/-!
# Examples of w-localization

The Sierpiński space has three specialization pairs and two connected components in
its w-localization. The extra pair distinguishes the counit from the component label,
and shows why w-localization need not fix an already w-local space. Discrete spaces
test the functor's action on both coordinates, and the empty space tests the absence
of any nonemptiness hypothesis.
-/

public section

open Function Set Topology
open TauCeti.WLocalization

namespace TauCeti.Examples.WLocalization

local instance : SpectralSpace Prop := spectralSpace_prop

/-- The nondiagonal pair in the w-localization of the Sierpiński space. -/
private def mixed : WLocalization Prop :=
  ofSpecializes (WithTopology.toTopology _ False) True
    (specializes_iff_nhds.2 (nhds_false ▸ le_top))

/-- The Sierpiński model consists of exactly the two diagonal pairs and the mixed pair. -/
example (q : WLocalization Prop) :
    q = diagonal (WithTopology.toTopology _ False) ∨
      q = diagonal (WithTopology.toTopology _ True) ∨ q = mixed := by
  by_cases hy : toBase q
  · by_cases hx : WithTopology.ofTopology (componentLabel q)
    · right; left
      apply WLocalization.ext
      · simpa using (WithTopology.ofTopology_injective _).eq_iff.1 (eq_true hx)
      · simpa using eq_true hy
    · right; right
      apply WLocalization.ext
      · simpa [mixed] using (WithTopology.ofTopology_injective _).eq_iff.1 (eq_false hx)
      · simpa [mixed] using eq_true hy
  · have hx := q.toBase_specializes_componentLabel.mem_closed isClosed_singleton_false (eq_false hy)
    left
    apply WLocalization.ext
    · simpa using (WithTopology.ofTopology_injective _).eq_iff.1 hx
    · simpa using eq_false hy

/-- The counit identifies the generic diagonal point and the mixed pair. -/
example : ¬ Injective (toBase : WLocalization Prop → Prop) := by
  intro h
  have heq : mixed = diagonal (WithTopology.toTopology _ True) := h (by simp [mixed])
  have hlabel := congrArg (WithTopology.ofTopology ∘ componentLabel) heq
  simp [mixed] at hlabel

/-- The mixed pair has the closed component label and the generic counit image. -/
example : WithTopology.ofTopology (componentLabel mixed) = False ∧ toBase mixed = True := by
  simp [mixed]

/-- The mixed pair lies in the closed-labelled component, but not the generic-labelled one. -/
example : mixed ∈ connectedComponent (diagonal (WithTopology.toTopology _ False)) ∧
    mixed ∉ connectedComponent (diagonal (WithTopology.toTopology _ True)) := by
  simp [mem_connectedComponent_iff, mixed]

/-- The mixed pair is not closed, so the three-point model is not Hausdorff. -/
example : ¬ IsClosed ({mixed} : Set (WLocalization Prop)) ∧ ¬ T2Space (WLocalization Prop) := by
  have h : ¬ IsClosed ({mixed} : Set (WLocalization Prop)) := by
    simp [isClosed_singleton_iff, mixed]
  exact ⟨h, fun _ ↦ h isClosed_singleton⟩

/-- The component homeomorphism fixes the closed label, without permuting the two components. -/
example : pi0 (ConnectedComponents.mk mixed) = WithTopology.toTopology _ False := by
  simp [mixed]

/-- The component fibre map retains the generalizing coordinate of the mixed pair. -/
example :
    (componentFiber (WithTopology.toTopology _ False) ⟨mixed, by simp [mixed]⟩).val = True := by
  simp [mixed]

/-- Swapping discrete Boolean points swaps both endpoints and hence the counit image. -/
example : toBase (map Bool.not (continuous_of_discreteTopology) (diagonal
      (WithTopology.toTopology _ false))) = true ∧
    WithTopology.ofTopology (componentLabel (map Bool.not (continuous_of_discreteTopology)
      (diagonal (WithTopology.toTopology _ false)))) = true := by simp

/-- The map to a point collapses the distinct specialization pairs. -/
example : map (fun _ : Prop ↦ ()) continuous_const mixed =
    map (fun _ : Prop ↦ ()) continuous_const (diagonal (WithTopology.toTopology _ True)) := by
  apply WLocalization.ext <;> simp [mixed]

/-- W-localization of an empty space is empty. -/
example : IsEmpty (WLocalization Empty) := ⟨fun q ↦ (toBase q).elim⟩

/-- The universal property applies to a nonempty profinite source. -/
example : ∃! g : Bool → WLocalization Bool, IsWLocalMap g ∧ toBase ∘ g = id :=
  have : SpectralSpace Bool := spectralSpace_of_zeroDimensionalSpace Bool
  universal (IsWLocalSpace.of_zeroDimensionalSpace Bool) isSpectralMap_id

end TauCeti.Examples.WLocalization
