/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.Normed.Module.Ball.Action
public import TauCeti.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Topology.PathComponent

/-!
# The zero-sphere

Every sphere in a one-dimensional real normed space is finite and discrete. If a sphere centered
at zero contains `p`, it consists of `p` and its antipode `-p`. On the unit sphere, these two
points are distinct, so the component of `-p` is the only path component other than that of `p`.

These are the inputs for the degree-zero computation of the reduced homology of spheres, which is
the base case of the induction on dimension through the suspension isomorphism.

## Main results

* `TauCeti.sphere_eq_pair_of_finrank_eq_one`: a sphere centered at zero containing `p` is `{p, -p}`.
* `TauCeti.finite_sphere_of_finrank_eq_one`: every sphere is finite.
* `TauCeti.discreteTopology_sphere_of_finrank_eq_one`: every sphere is discrete.
* `TauCeti.zerothHomotopySphereUnique`: the path component of `-p` is the unique path component
  other than that of `p`.
-/

public section

open Metric Module

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A sphere centered at zero in a one-dimensional real normed space consists of a point on it
and its antipode. For radius zero, the two points coincide. -/
theorem sphere_eq_pair_of_finrank_eq_one (h : finrank ℝ E = 1) {r : ℝ} {p : E}
    (hp : p ∈ sphere (0 : E) r) : sphere (0 : E) r = {p, -p} := by
  have hp' : ‖p‖ = r := by simpa using hp
  ext x
  simp only [mem_sphere_zero_iff_norm, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    exact eq_or_eq_neg_of_norm_eq_of_finrank_eq_one h (hx.trans hp'.symm)
  · rintro (rfl | rfl) <;> simpa using hp'

/-- Every sphere in a one-dimensional real normed space is finite. -/
theorem finite_sphere_of_finrank_eq_one (h : finrank ℝ E = 1) (x : E) (r : ℝ) :
    Finite (sphere x r) := by
  apply Set.finite_coe_iff.mpr
  have hs : (sphere (0 : E) r).Finite := by
    rcases (sphere (0 : E) r).eq_empty_or_nonempty with hs | ⟨p, hp⟩
    · rw [hs]
      exact Set.finite_empty
    · rw [sphere_eq_pair_of_finrank_eq_one h hp]
      simp
  have ht : ⇑(IsometryEquiv.addLeft x) '' sphere (0 : E) r = sphere x r := by simp
  rw [← ht]
  exact hs.image _

/-- Every sphere in a one-dimensional real normed space is discrete. -/
theorem discreteTopology_sphere_of_finrank_eq_one (h : finrank ℝ E = 1) (x : E) (r : ℝ) :
    DiscreteTopology (sphere x r) :=
  have := finite_sphere_of_finrank_eq_one h x r
  inferInstance

/-- On the unit sphere of a one-dimensional real normed space, a point and its antipode lie in
distinct path components. -/
theorem zerothHomotopy_mk_neg_ne (h : finrank ℝ E = 1) (p : sphere (0 : E) 1) :
    ZerothHomotopy.mk (-p) ≠ ZerothHomotopy.mk p :=
  have := discreteTopology_sphere_of_finrank_eq_one h 0 1
  fun hc ↦ ne_neg_of_mem_unit_sphere ℝ p
    (ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace hc).symm

/-- On the unit sphere of a one-dimensional real normed space, the path component of `-p` is the
unique path component other than that of `p`. -/
@[instance_reducible]
def zerothHomotopySphereUnique (h : finrank ℝ E = 1) (p : sphere (0 : E) 1) :
    Unique {c : ZerothHomotopy (sphere (0 : E) 1) // c ≠ ZerothHomotopy.mk p} :=
  haveI := discreteTopology_sphere_of_finrank_eq_one h 0 1
  { default := ⟨ZerothHomotopy.mk (-p), zerothHomotopy_mk_neg_ne h p⟩
    uniq := by
      rintro ⟨c, hc⟩
      obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
      have hx : (x : E) ∈ ({(p : E), -(p : E)} : Set E) :=
        sphere_eq_pair_of_finrank_eq_one h p.2 ▸ x.2
      rcases hx with hx | hx
      · exact absurd (congrArg ZerothHomotopy.mk (Subtype.ext hx)) hc
      · exact Subtype.ext (congrArg ZerothHomotopy.mk (Subtype.ext hx)) }

@[simp]
lemma zerothHomotopySphereUnique_default (h : finrank ℝ E = 1) (p : sphere (0 : E) 1) :
    @default _ (@Unique.instInhabited _ (zerothHomotopySphereUnique h p)) =
      ⟨ZerothHomotopy.mk (-p), zerothHomotopy_mk_neg_ne h p⟩ := by
  rfl

end TauCeti
