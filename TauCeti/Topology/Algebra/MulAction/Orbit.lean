/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Topology.Constructible
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.NoetherianSpace

/-!
# Constructible orbits are locally closed

For an action by homeomorphisms, local closedness of an orbit at one of its points implies
local closedness everywhere on that orbit. If the orbit is constructible inside its closure,
its relative interior is dense and hence nonempty, supplying such a point. In particular,
constructible orbits in a Noetherian space are locally closed.

This is the topological step in realizing homogeneous spaces as locally closed orbits: once
constructibility of an orbit has been established, the orbit is open in its closure. Only
continuity of each translation is required; the acting group need not carry a topology.

The constructible-set argument reuses `Topology.IsConstructible.dense_interior`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.65(b) and §7.c.
-/

public section

open Set Topology TopologicalSpace
open scoped Set.Notation
open scoped Pointwise

namespace TauCeti

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X]

/-- An orbit which is locally closed at one of its points is locally closed. -/
theorem isLocallyClosed_orbit_of_isLocallyClosedAt (x : X) {y : X}
    (hy : y ∈ MulAction.orbit G x) (h : IsLocallyClosedAt (MulAction.orbit G x) y) :
    IsLocallyClosed (MulAction.orbit G x) := by
  rw [isLocallyClosed_iff_isLocallyClosedAt]
  intro z hz
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
  obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp hz
  have heq : (fun t : X ↦ (g * k⁻¹) • t) ⁻¹' MulAction.orbit G x =
      MulAction.orbit G x := by
    ext t
    simp only [mem_preimage, ← MulAction.orbit_eq_iff, MulAction.orbit_smul]
  have h' := (by simpa only [mul_smul, inv_smul_smul] using h :
    IsLocallyClosedAt (MulAction.orbit G x) ((g * k⁻¹) • (k • x))).preimage
    (f := fun t : X ↦ (g * k⁻¹) • t)
    (x := k • x) (continuous_const_smul _)
  rw [heq] at h'
  exact h'

/-- An orbit constructible in its closure is locally closed, without a Noetherian or
separation hypothesis on the ambient space. -/
theorem isLocallyClosed_orbit_of_isConstructible_preimage_val_closure (x : X)
    (h : IsConstructible (closure (MulAction.orbit G x) ↓∩ MulAction.orbit G x)) :
    IsLocallyClosed (MulAction.orbit G x) := by
  let s := MulAction.orbit G x
  have hd : Dense (closure s ↓∩ s) := by
    rw [Subtype.dense_iff, Subtype.image_preimage_coe,
      inter_eq_right.mpr (subset_closure (s := s))]
  have : Nonempty (closure s) := ⟨⟨x, subset_closure (MulAction.mem_orbit_self x)⟩⟩
  obtain ⟨y, hy⟩ := (h.dense_interior hd).nonempty
  have hys : y.val ∈ s := interior_subset (s := closure s ↓∩ s) hy
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp
    (isOpen_interior : IsOpen (interior (closure s ↓∩ s)))
  apply isLocallyClosed_orbit_of_isLocallyClosedAt x hys
  apply isLocallyClosedAt_iff_exists_inter_closure_subset.mpr
  have hyU : y ∈ Subtype.val ⁻¹' U := by rw [hUeq]; exact hy
  refine ⟨U, hU.mem_nhds hyU, ?_⟩
  intro z hz
  exact interior_subset (s := closure s ↓∩ s)
    (hUeq ▸ hz.1 : (⟨z, hz.2⟩ : closure s) ∈
    interior (closure s ↓∩ s))

/-- A constructible orbit in a Noetherian space is locally closed. This applies to actions
by homeomorphisms on spaces with the Zariski topology. -/
theorem isLocallyClosed_orbit_of_isConstructible [NoetherianSpace X] (x : X)
    (h : IsConstructible (MulAction.orbit G x)) : IsLocallyClosed (MulAction.orbit G x) := by
  apply isLocallyClosed_orbit_of_isConstructible_preimage_val_closure x
  exact h.preimage_of_isClosedEmbedding isClosed_closure.isClosedEmbedding_subtypeVal
    (NoetherianSpace.isCompact _)

end TauCeti
