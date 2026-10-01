/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.Normed.Module.Ball.Action
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import TauCeti.Topology.PathComponent

/-!
# The zero-sphere

The unit sphere of a one-dimensional real normed space consists of a point `p` on it and its
antipode `-p`.  It is therefore finite and discrete, and its path components are its two points:
the component of `-p` is the only path component other than that of `p`.

These are the inputs for the degree-zero computation of the reduced homology of spheres, which is
the base case of the induction on dimension through the suspension isomorphism.

## Main results

* `TauCeti.sphere_eq_pair_of_finrank_eq_one`: the unit sphere is `{p, -p}`.
* `TauCeti.discreteTopology_sphere_of_finrank_eq_one`: the unit sphere is discrete.
* `TauCeti.zerothHomotopySphereUnique`: the path component of `-p` is the unique path component
  other than that of `p`.
-/

public section

open Metric Module

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The unit sphere of a one-dimensional real normed space consists of a point on it and its
antipode. -/
theorem sphere_eq_pair_of_finrank_eq_one (h : finrank ℝ E = 1) {p : E}
    (hp : p ∈ sphere (0 : E) 1) : sphere (0 : E) 1 = {p, -p} := by
  have hp' : ‖p‖ = 1 := by simpa using hp
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hp'
  ext x
  simp only [mem_sphere_zero_iff_norm, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' p hp0).mp h x
    rw [norm_smul, hp', mul_one, Real.norm_eq_abs] at hx
    rcases (abs_eq zero_le_one).mp hx with rfl | rfl
    · simp
    · simp
  · rintro (rfl | rfl)
    · exact hp'
    · simpa using hp'

/-- The unit sphere of a one-dimensional real normed space is finite. -/
theorem finite_sphere_of_finrank_eq_one (h : finrank ℝ E = 1) : Finite (sphere (0 : E) 1) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ h
  obtain ⟨p, hp⟩ := NormedSpace.sphere_nonempty (E := E) (x := 0).mpr zero_le_one
  rw [sphere_eq_pair_of_finrank_eq_one h hp]
  infer_instance

/-- The unit sphere of a one-dimensional real normed space is discrete. -/
theorem discreteTopology_sphere_of_finrank_eq_one (h : finrank ℝ E = 1) :
    DiscreteTopology (sphere (0 : E) 1) :=
  have := finite_sphere_of_finrank_eq_one h
  inferInstance

/-- On the unit sphere of a one-dimensional real normed space, a point and its antipode lie in
distinct path components. -/
theorem zerothHomotopy_mk_neg_ne (h : finrank ℝ E = 1) (p : sphere (0 : E) 1) :
    ZerothHomotopy.mk (-p) ≠ ZerothHomotopy.mk p :=
  have := discreteTopology_sphere_of_finrank_eq_one h
  fun hc ↦ ne_neg_of_mem_unit_sphere ℝ p
    (ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace hc).symm

/-- On the unit sphere of a one-dimensional real normed space, the path component of `-p` is the
unique path component other than that of `p`. -/
@[instance_reducible]
def zerothHomotopySphereUnique (h : finrank ℝ E = 1) (p : sphere (0 : E) 1) :
    Unique {c : ZerothHomotopy (sphere (0 : E) 1) // c ≠ ZerothHomotopy.mk p} :=
  haveI := discreteTopology_sphere_of_finrank_eq_one h
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
