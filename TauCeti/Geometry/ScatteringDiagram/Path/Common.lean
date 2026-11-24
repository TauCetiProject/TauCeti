/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Geometry.ScatteringDiagram.Path.Basic

/-!
# Common admissible paths for countably many wall families

Between endpoints off every wall, the free vertices giving a common admissible
two-segment path for countably many finite wall families are dense. Thus a single
polygonal path can be tested at every order of a wall diagram. Each family retains
its own singular support: intersections between walls from different families need
not be singular for either one.

The construction chooses a vertex avoiding the stronger exceptional arrangement
for the union of all walls. Only the free vertex is constrained to a prescribed
open set; the two segments need not stay there. This does not assert preservation
of the crossings of an already prescribed path.
-/

public section

open Set

namespace TauCeti

variable {V J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Countable J]
  {ι : J → Type*} [∀ j, Countable (ι j)]

/-- With endpoints off all walls, the free vertices making both segments admissible
for every family form a dense set. The families may themselves be countable;
for finite families each resulting path has finitely many crossings at each level. -/
theorem dense_common_admissibleSegments
    (W : ∀ j, ι j → Set V) (hpoly : ∀ j i, IsConvexPolyhedron (W j i))
    (hdim : ∀ j i,
      Module.finrank ℝ (affineSpan ℝ (W j i)).direction + 1 = Module.finrank ℝ V)
    {x y : V} (hx : ∀ j i, x ∉ W j i) (hy : ∀ j i, y ∉ W j i) :
    Dense {z : V | ∃ hz : ∀ j i, z ∉ W j i, ∀ j,
      WallComplement.AdmissibleSegment (⟨x, hx j⟩ : WallComplement (W j)) ⟨z, hz j⟩ ∧
      WallComplement.AdmissibleSegment (⟨z, hz j⟩ : WallComplement (W j)) ⟨y, hy j⟩} := by
  rw [dense_iff_inter_open]
  intro U hU hne
  let allWalls : (Σ j, ι j) → Set V := fun p => W p.1 p.2
  obtain ⟨z, hzU, hz, ht, hr⟩ := exists_mem_open_two_transverse_lineMaps
    allWalls (fun p => hpoly p.1 p.2) (fun p => hdim p.1 p.2)
    (fun p => hx p.1 p.2) (fun p => hy p.1 p.2) hU hne
  refine ⟨z, hzU, ?_⟩
  refine ⟨fun j i => hz ⟨j, i⟩, fun j => ?_⟩
  have hsing : singularSupport (W j) ⊆ singularSupport allWalls :=
    singularSupport_comp_subset allWalls (fun i => Sigma.mk j i)
  have hxz : WallComplement.AdmissibleSegment
      (⟨x, hx j⟩ : WallComplement (W j)) ⟨z, fun i => hz ⟨j, i⟩⟩ :=
    ⟨fun i _ => (ht ⟨j, i⟩).1, fun t _ h => (hr t).1 (hsing h)⟩
  have hyz : WallComplement.AdmissibleSegment
      (⟨y, hy j⟩ : WallComplement (W j)) ⟨z, fun i => hz ⟨j, i⟩⟩ :=
    ⟨fun i _ => (ht ⟨j, i⟩).2, fun t _ h => (hr t).2 (hsing h)⟩
  exact ⟨hxz, hyz.symm⟩

end TauCeti
