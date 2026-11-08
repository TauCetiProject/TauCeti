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
# Locally closed sets of closed points in Noetherian spaces

In a Noetherian quasi-sober space, a locally closed set `s = U ∩ Z` consisting of closed points is
closed. Write the closed set `Z` as a finite union of irreducible closed sets. If one of them, `T`,
meets the open set `U`, then its generic point lies in `U`, hence in `s`, so it is a closed point
and `T` is that single point. Thus `s` is a finite union of closed points.

On a Noetherian integral scheme of dimension at most one every point other than the generic point
is closed, so this applies to the zero locus of a nonzero function on an open subset: that zero
locus is closed in the whole scheme, not only in the open subset.

In particular a Noetherian quasi-sober `T₁` space is finite: it is the closure of its finitely
many generic points, and a finite set is closed in a `T₁` space.

## Main results

* `IsLocallyClosed.isClosed_of_subset_closedPoints`: a locally closed set of closed points of a
  Noetherian quasi-sober space is closed.
* `TauCeti.finite_of_noetherianSpace_of_t1Space`: a Noetherian quasi-sober `T₁` space is finite.

## References

* The Stacks Project, Tag 0052, *Noetherian topological spaces*.
-/

public section

open Set TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

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

namespace TauCeti

/-- **Noetherian `T₁` spaces are finite.** A Noetherian quasi-sober space in which every point is
closed is finite: it has finitely many irreducible components, hence finitely many generic points,
and their closure is the whole space. -/
theorem finite_of_noetherianSpace_of_t1Space [NoetherianSpace X] [QuasiSober X] [T1Space X] :
    Finite X := by
  have hfin : (genericPoints X).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  have h := genericPoints.closure (α := X)
  rw [hfin.isClosed.closure_eq] at h
  exact Set.finite_univ_iff.mp (h ▸ hfin)

end TauCeti
