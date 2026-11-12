/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober

/-!
# Sets of closed points in Noetherian spaces

In a Noetherian quasi-sober space, a closed set consisting of closed points is finite: it is a
finite union of irreducible closed sets, and each of them is the closure of its generic point,
which is a closed point.

A locally closed set `s = U ∩ Z` consisting of closed points is closed. Write the closed set `Z`
as a finite union of irreducible closed sets. If one of them, `T`, meets the open set `U`, then
its generic point lies in `U`, hence in `s`, so it is a closed point and `T` is that single
point. Thus `s` is a finite union of closed points.

On a Noetherian integral scheme of dimension at most one every point other than the generic point
is closed, so this applies to the zero locus of a nonzero function on an open subset: that zero
locus is closed in the whole scheme, not only in the open subset. Likewise a closed subset not
containing the generic point is finite.

## Main results

* `IsClosed.finite_of_subset_closedPoints`: a closed set of closed points of a Noetherian
  quasi-sober space is finite.
* `IsLocallyClosed.isClosed_of_subset_closedPoints`: a locally closed set of closed points of a
  Noetherian quasi-sober space is closed.

## References

* The Stacks Project, Tag 0052, *Noetherian topological spaces*.
-/

public section

open Set TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- **Closed sets of closed points are finite** in a Noetherian quasi-sober space. -/
theorem IsClosed.finite_of_subset_closedPoints [NoetherianSpace X] [QuasiSober X]
    {s : Set X} (hs : IsClosed s) (hcl : s ⊆ closedPoints X) : s.Finite := by
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hs
  refine hSf.sUnion fun T hT ↦ ?_
  -- The generic point of the irreducible closed set `T` lies in `s`, so it is a closed point and
  -- `T` is that single point.
  obtain ⟨g, hg⟩ : ∃ g, IsGenericPoint g T :=
    ⟨_, (hSc T hT).closure_eq ▸ (hSi T hT).isGenericPoint_genericPoint_closure⟩
  rw [← hg.def, (hcl (subset_sUnion_of_mem hT hg.mem)).closure_eq]
  exact finite_singleton g

/-- **Locally closed sets of closed points are closed** in a Noetherian quasi-sober space. -/
theorem IsLocallyClosed.isClosed_of_subset_closedPoints [NoetherianSpace X] [QuasiSober X]
    {s : Set X} (hs : IsLocallyClosed s) (hcl : s ⊆ closedPoints X) : IsClosed s := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hs
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [sUnion_eq_biUnion, inter_iUnion₂]
  refine hSf.isClosed_biUnion fun T hT ↦ ?_
  rcases (U ∩ T).eq_empty_or_nonempty with h | ⟨y, hyU, hyT⟩
  · rw [h]
    exact isClosed_empty
  -- The generic point `g` of `T` generizes `y ∈ U`, so it lies in `U` and hence in `s`; being a
  -- closed point, it is all of `T`.
  obtain ⟨g, hg⟩ : ∃ g, IsGenericPoint g T :=
    ⟨_, (hSc T hT).closure_eq ▸ (hSi T hT).isGenericPoint_genericPoint_closure⟩
  have hgU : g ∈ U := (hg.specializes hyT).mem_open hU hyU
  have hgs : g ∈ U ∩ ⋃₀ S := ⟨hgU, subset_sUnion_of_mem hT hg.mem⟩
  rw [← hg.def, (hcl hgs).closure_eq, inter_eq_right.mpr (singleton_subset_iff.mpr hgU)]
  exact hcl hgs
