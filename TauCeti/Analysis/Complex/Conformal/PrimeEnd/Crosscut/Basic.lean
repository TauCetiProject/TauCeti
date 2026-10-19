/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# Crosscuts of planar domains

A **crosscut** of a plane domain `U` is a simple path whose two endpoints lie on the frontier of
`U` and whose open interior lies in `U`. Crosscuts are the basic geometric objects used to define
prime ends: a prime end is represented by a nested null chain of crosscuts, with two chains
identified when they eventually select the same side of each other.

This file introduces the crosscut predicate at the level of paths, proves the elementary API that
later prime-end constructions need, and supplies its fundamental nondegenerate examples: chords
between distinct points of the boundary circle are crosscuts of an open disc.

The definition uses the open unit interval in the path parameter. This excludes the endpoints
from the part required to lie in `U`, while injectivity prevents a boundary endpoint from being
visited again in the interior. For an open `U`, it follows that the path meets `frontier U`
exactly at its two endpoints.

Crosscuts are unoriented objects geometrically. Accordingly, reversing a path preserves the
predicate. The oriented path is nevertheless retained: a prime-end chain will use the order only
to choose and compare the components of `U` cut off by its crosscuts.

## Main declarations

* `Path.IsCrosscut` — a simple path with endpoints on `frontier U` and interior in `U`.
* `Path.IsCrosscut.range_subset_closure` — a crosscut lies in the domain's closure.
* `Path.IsCrosscut.range_inter_frontier` — it meets the frontier exactly at its endpoints.
* `Path.isCrosscut_symm` — crosscuts are invariant under reversing orientation.
* `Path.IsCrosscut.map_homeomorph` — ambient homeomorphisms carry crosscuts to crosscuts.
* `Path.isCrosscut_segment_ball` — every nondegenerate chord of a disc is a crosscut.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Chapter 2.
* C. Carathéodory, *Über die Begrenzung einfach zusammenhängender Gebiete*, Math. Ann. 73
  (1913).
-/

public section

open Metric Set Topology
open scoped unitInterval

namespace Path

variable {x y : ℂ} {γ : Path x y} {U : Set ℂ}

/-- A path is a **crosscut** of `U` when it is injective, both endpoints lie on `frontier U`, and
every non-endpoint parameter is mapped into `U`.

No openness or connectedness hypothesis is built into the predicate. Those are properties of the
ambient domain in applications, while retaining the bare predicate makes it usable for relative
domains and lets the elementary orientation API avoid irrelevant assumptions. -/
def IsCrosscut (γ : Path x y) (U : Set ℂ) : Prop :=
  Function.Injective γ ∧ x ∈ frontier U ∧ y ∈ frontier U ∧ MapsTo γ (Ioo (0 : I) 1) U

/-- The defining characterization of a crosscut. -/
theorem isCrosscut_def :
    IsCrosscut γ U ↔
      Function.Injective γ ∧ x ∈ frontier U ∧ y ∈ frontier U ∧
        MapsTo γ (Ioo (0 : I) 1) U :=
  Iff.rfl

/-- A crosscut has an injective parametrization. -/
theorem IsCrosscut.injective (hγ : IsCrosscut γ U) : Function.Injective γ :=
  hγ.1

/-- The source of a crosscut lies on the frontier of its domain. -/
theorem IsCrosscut.source_mem_frontier (hγ : IsCrosscut γ U) : x ∈ frontier U :=
  hγ.2.1

/-- The target of a crosscut lies on the frontier of its domain. -/
theorem IsCrosscut.target_mem_frontier (hγ : IsCrosscut γ U) : y ∈ frontier U :=
  hγ.2.2.1

/-- The open interior of a crosscut lies in its domain. -/
theorem IsCrosscut.mapsTo_interior (hγ : IsCrosscut γ U) : MapsTo γ (Ioo (0 : I) 1) U :=
  hγ.2.2.2

/-- The two endpoints of a crosscut are distinct. -/
theorem IsCrosscut.source_ne_target (hγ : IsCrosscut γ U) : x ≠ y := by
  intro hxy
  have h01 : (0 : I) ≠ 1 := zero_ne_one
  exact h01 (hγ.injective (by simp [hxy]))

/-- Every value of a crosscut lies in the closure of its domain. -/
theorem IsCrosscut.range_subset_closure (hγ : IsCrosscut γ U) :
    range γ ⊆ closure U := by
  rintro z ⟨t, rfl⟩
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc t.2 with ht | ht | ht
  · have : t = 0 := Subtype.ext ht
    subst t
    simpa using frontier_subset_closure hγ.source_mem_frontier
  · have : t = 1 := Subtype.ext ht
    subst t
    simpa using frontier_subset_closure hγ.target_mem_frontier
  · exact subset_closure (hγ.mapsTo_interior ht)

/-- A crosscut of an open set meets its frontier exactly at its two endpoints. -/
theorem IsCrosscut.range_inter_frontier (hγ : IsCrosscut γ U) (hU : IsOpen U) :
    range γ ∩ frontier U = {x, y} := by
  ext z
  constructor
  · rintro ⟨⟨t, rfl⟩, htfr⟩
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc t.2 with ht | ht | ht
    · left
      have : t = 0 := Subtype.ext ht
      subst t
      simp
    · right
      have : t = 1 := Subtype.ext ht
      subst t
      simp
    · exact (hU.frontier_eq.subset htfr).2 (hγ.mapsTo_interior ht) |>.elim
  · intro hz
    rcases hz with rfl | rfl
    · exact ⟨⟨0, by simp⟩, hγ.source_mem_frontier⟩
    · exact ⟨⟨1, by simp⟩, hγ.target_mem_frontier⟩

/-- Reversing an oriented crosscut gives a crosscut with the opposite orientation. -/
theorem IsCrosscut.symm (hγ : IsCrosscut γ U) : IsCrosscut γ.symm U := by
  rw [isCrosscut_def]
  refine ⟨?_, hγ.target_mem_frontier, hγ.source_mem_frontier, ?_⟩
  · intro s t hst
    apply unitInterval.symm_bijective.1
    apply hγ.injective
    exact hst
  · intro t ht
    rw [Path.symm_apply]
    refine hγ.mapsTo_interior ⟨?_, ?_⟩
    · rw [← unitInterval.symm_one]
      exact unitInterval.strictAnti_symm ht.2
    · rw [← unitInterval.symm_zero]
      exact unitInterval.strictAnti_symm ht.1

/-- A path is a crosscut exactly when its reversal is a crosscut. -/
@[simp]
theorem isCrosscut_symm : IsCrosscut γ.symm U ↔ IsCrosscut γ U := by
  constructor
  · intro h
    simpa using h.symm
  · exact IsCrosscut.symm

/-- An ambient homeomorphism carries a crosscut to a crosscut of the image domain. -/
theorem IsCrosscut.map_homeomorph (hγ : IsCrosscut γ U) (e : ℂ ≃ₜ ℂ) :
    IsCrosscut (γ.map e.continuous) (e '' U) := by
  rw [isCrosscut_def]
  refine ⟨e.injective.comp hγ.injective, ?_, ?_, ?_⟩
  · rw [← e.image_frontier]
    exact ⟨x, hγ.source_mem_frontier, rfl⟩
  · rw [← e.image_frontier]
    exact ⟨y, hγ.target_mem_frontier, rfl⟩
  · intro t ht
    exact ⟨γ t, hγ.mapsTo_interior ht, rfl⟩

/-- **A nondegenerate chord of a disc is a crosscut.** If `x` and `y` are distinct points of
`sphere c r`, then the straight path from `x` to `y` is injective, its endpoints lie on the
frontier of `ball c r`, and strict convexity puts every interior point of the chord in the open
disc. No positivity hypothesis on `r` is needed: the sphere of radius `0` is a single point,
so two distinct points on it force `r ≠ 0`. -/
theorem isCrosscut_segment_ball {c x y : ℂ} {r : ℝ}
    (hx : x ∈ sphere c r) (hy : y ∈ sphere c r) (hxy : x ≠ y) :
    IsCrosscut (Path.segment x y) (ball c r) := by
  have hr : r ≠ 0 := by
    rintro rfl
    rw [sphere_zero, Set.mem_singleton_iff] at hx hy
    exact hxy (hx.trans hy.symm)
  rw [isCrosscut_def]
  refine ⟨Path.segment_injective_of_ne hxy, ?_, ?_, ?_⟩
  · rwa [frontier_ball c hr]
  · rwa [frontier_ball c hr]
  · intro t ht
    apply openSegment_subset_ball_of_ne (sphere_subset_closedBall hx)
      (sphere_subset_closedBall hy) hxy
    exact lineMap_mem_openSegment ℝ x y ht

end Path
