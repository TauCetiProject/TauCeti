/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.PNat.Basic
public import TauCeti.Topology.Grassmannian.Tautological
public import TauCeti.Topology.VectorBundle.Orientation.Proper
public import TauCeti.Topology.VectorBundle.Orientation.Tautological

/-!
# Finite oriented real Grassmannians

For positive rank, the finite oriented Grassmannian is the orientation double cover of the
existing real tautological bundle. Its tautological bundle is pulled back along the
orientation-forgetting projection and has the orientation recorded by each point, supplied by
`TauCeti.VectorBundleOrientationCover.tautologicalOrientation`. The construction uses the
original finite Grassmannian and its original tautological bundle.

The forgetting map is a proper two-sheeted covering, so this carrier is compact. When the
rank equals the ambient dimension it still has two points, corresponding to the two
orientations of the whole space. Rank zero is excluded: its orientation cover has two points
over the one-point Grassmannian, whereas the canonically oriented rank-zero Grassmannian is
conventionally a point. This carrier is therefore defined only for positive rank.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, §§5, 9.
-/

public section

noncomputable section

open Bundle Set
open scoped Topology

namespace TauCeti

/-- The finite oriented real Grassmannian in positive rank, as the orientation double cover
of the tautological bundle on the finite real Grassmannian. -/
abbrev finiteOrientedGrassmannian (r : ℕ+) (N : ℕ) : Type :=
  VectorBundleOrientationCover (Fin r → ℝ) (finiteGrassmannian.Tautological ℝ r N) (Fin r)

namespace finiteOrientedGrassmannian

variable {r : ℕ+} {N : ℕ}

/-- Forget the orientation of an oriented plane. This is a continuous map to the existing
finite real Grassmannian. -/
abbrev forget : C(finiteOrientedGrassmannian r N, finiteGrassmannian ℝ r N) :=
  VectorBundleOrientationCover.projection

@[simp]
theorem forget_apply (p : finiteOrientedGrassmannian r N) : forget p = p.proj :=
  (rfl)

/-- Finite oriented Grassmannians are compact. -/
instance : CompactSpace (finiteOrientedGrassmannian r N) :=
  VectorBundleOrientationCover.compactSpace (by simp)

/-- The oriented tautological bundle is the pullback of the original tautological bundle along
orientation forgetting. Its fibre over an oriented plane is that same plane. -/
abbrev Tautological (r : ℕ+) (N : ℕ) : finiteOrientedGrassmannian r N → Type :=
  (forget : finiteOrientedGrassmannian r N → finiteGrassmannian ℝ r N) *ᵖ
    (finiteGrassmannian.Tautological ℝ r N)

/-- In full ambient rank the oriented Grassmannian has two points, rather than one. -/
theorem encard_univ_fullRank :
    (univ : Set (finiteOrientedGrassmannian r r)).encard = 2 := by
  obtain ⟨V⟩ := (finiteGrassmannian.nonempty_iff_le (𝕜 := ℝ) (r := r) (N := r)).2 le_rfl
  have h : (forget : finiteOrientedGrassmannian r r → finiteGrassmannian ℝ r r) ⁻¹' {V} = univ := by
    ext p
    simp [Subsingleton.elim p.proj V]
  rw [← h]
  exact VectorBundleOrientationCover.encard_preimage_proj_singleton (by simp) V

end finiteOrientedGrassmannian

end TauCeti
