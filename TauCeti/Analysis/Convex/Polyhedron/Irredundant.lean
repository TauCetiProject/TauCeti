/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Extreme

import TauCeti.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Irredundant presentations of a polyhedron

Let `P = {x | c j ≤ f j x for every j}` be the polyhedron cut out by a finite family of linear
functionals `f : ι → Module.Dual 𝕜 E` and constants `c : ι → 𝕜`, over a linearly ordered field
(`TauCeti.polyhedron f c`). The presentation `(f, c)` is *irredundant* when every constraint `j`
is the only active one at some point of `P`, so that each constraint contributes a facet of `P`
and no facet is listed twice.

The main result is that an irredundant presentation with nonzero functionals is determined by
the polyhedron up to relabelling the constraints and rescaling each of them by a positive
factor (`TauCeti.polyhedron_eq_iff_exists_equiv`): if `(g, d)` is another such presentation,
indexed by `κ`, then `P = polyhedron g d` exactly when there are a bijection `e : ι ≃ κ` and
positive scalars `r j` with `g (e j) = r j • f j` and `d (e j) = r j * c j`. This is how a
polytope recovers its inward facet normals and support constants from its shape.

The proof is local. Near a point `x` of `P` only the constraints active at `x` matter: moving
from `x` in direction `w` stays in `P` for small positive times exactly when `0 ≤ f j w` for every
constraint `j` active at `x` (`TauCeti.exists_pos_add_smul_mem_polyhedron_iff`). At a point where
only `j` is active, the directions entering `P` therefore form the half-space `{w | 0 ≤ f j w}`.
Every constraint `k` of `(g, d)` active there is nonnegative on this half-space, hence a
nonnegative multiple of `f j` (`Module.Dual.apply_eq_mul_apply_of_nonneg`), and since the
half-space is proper one of these multiples is positive
(`TauCeti.exists_pos_smul_eq_of_activeSet_eq_singleton`). Two constraints that are positive
multiples of each other are active at the same points, so irredundancy of both presentations
makes the matching a bijection.

The hypothesis that the functionals are nonzero cannot be dropped: the single constraint
`0 ≤ 0` is an irredundant presentation of the whole space, as is the empty family.

## Main results

* `TauCeti.exists_pos_add_smul_mem_polyhedron_iff`: the directions entering a polyhedron at a
  point are those on which the active functionals are nonnegative.
* `TauCeti.exists_pos_smul_eq_of_activeSet_eq_singleton`: at a point of a facet of an
  irredundant presentation, some constraint of any other presentation of the same polyhedron is
  a positive multiple of the facet constraint.
* `TauCeti.polyhedron_eq_iff_exists_equiv`: two irredundant presentations with nonzero
  functionals cut out the same polyhedron exactly when they agree up to relabelling and positive
  rescaling of the constraints.

## References

* A. Schrijver, *Theory of Linear and Integer Programming*, Wiley, 1986, Section 8.4.
-/

public section

open Set

namespace TauCeti

variable {𝕜 E ι κ : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

variable {f : ι → Module.Dual 𝕜 E} {c : ι → 𝕜} {x w : E} {j : ι}

/-- A direction `w` entering a polyhedron at `x` is nonnegative on every functional active at
`x`. -/
theorem nonneg_of_add_smul_mem_polyhedron (hj : j ∈ activeSet f c x) {t : 𝕜} (ht : 0 < t)
    (hxw : x + t • w ∈ polyhedron f c) : 0 ≤ f j w := by
  have h := mem_polyhedron.1 hxw j
  rw [map_add, map_smul, smul_eq_mul, mem_activeSet.1 hj] at h
  exact nonneg_of_mul_nonneg_right (by linarith) ht

/-- **Directions entering a polyhedron.** At a point `x` of a polyhedron cut out by finitely many
half-spaces, moving in direction `w` stays in the polyhedron for some positive time exactly when
every functional active at `x` is nonnegative on `w`. -/
theorem exists_pos_add_smul_mem_polyhedron_iff [Finite ι] (hx : x ∈ polyhedron f c) :
    (∃ t : 𝕜, 0 < t ∧ x + t • w ∈ polyhedron f c) ↔ ∀ j ∈ activeSet f c x, 0 ≤ f j w := by
  refine ⟨fun ⟨t, ht, hxw⟩ j hj ↦ nonneg_of_add_smul_mem_polyhedron hj ht hxw, fun hw ↦ ?_⟩
  obtain ⟨t, ht, hslack⟩ := exists_pos_forall_add_smul_mem_polyhedron hx w
  exact ⟨t, ht, hslack t (abs_of_pos ht).le fun j hj ↦ mul_nonneg ht.le (hw j hj)⟩

variable {g : κ → Module.Dual 𝕜 E} {d : κ → 𝕜}

/-- **A facet determines its constraint.** Let `x` be a point of a polyhedron at which the
constraint `j` of the presentation `(f, c)` is the only active one, with `f j ≠ 0`. Then every
other finite presentation `(g, d)` of the same polyhedron has a constraint `k`, active at `x`,
which is a positive multiple of the constraint `j`. -/
theorem exists_pos_smul_eq_of_activeSet_eq_singleton [Finite ι] [Finite κ]
    (hP : polyhedron f c = polyhedron g d) (hx : x ∈ polyhedron f c)
    (hxj : activeSet f c x = {j}) (hfj : f j ≠ 0) :
    ∃ k ∈ activeSet g d x, ∃ r : 𝕜, 0 < r ∧ g k = r • f j ∧ d k = r * c j := by
  have hx' : x ∈ polyhedron g d := hP ▸ hx
  -- Both presentations see the same entering directions at `x`.
  have hdir (w : E) : (∀ k ∈ activeSet g d x, 0 ≤ g k w) ↔ 0 ≤ f j w := by
    rw [← exists_pos_add_smul_mem_polyhedron_iff hx', ← hP,
      exists_pos_add_smul_mem_polyhedron_iff hx, hxj]
    simp
  obtain ⟨v, hv⟩ : ∃ v, f j v = -1 := by
    obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 hfj
    exact ⟨-(f j v)⁻¹ • v, by simp [inv_mul_cancel₀ (by simpa using hv)]⟩
  -- So each constraint of `(g, d)` active at `x` is a nonnegative multiple of `f j`.
  have hmul (k : κ) (hk : k ∈ activeSet g d x) : ∃ r : 𝕜, 0 ≤ r ∧ g k = r • f j :=
    ⟨g k (-v), (hdir (-v)).2 (by simp [hv]) k hk, LinearMap.ext fun w ↦
      (f j).apply_eq_mul_apply_of_nonneg (g k) (by simp [hv]) (fun w hw ↦ (hdir w).2 hw k hk) w⟩
  -- The direction `v` leaves the half-space `0 ≤ f j`, so one of them excludes it.
  obtain ⟨k, hk, hkv⟩ : ∃ k ∈ activeSet g d x, g k v < 0 := by
    by_contra! h
    have := (hdir v).1 h
    linarith
  obtain ⟨r, hr, hgk⟩ := hmul k hk
  have hr : 0 < r := by
    rw [hgk, LinearMap.smul_apply, hv, smul_eq_mul] at hkv
    exact hr.lt_of_ne fun h ↦ by simp [← h] at hkv
  refine ⟨k, hk, r, hr, hgk, ?_⟩
  rw [← mem_activeSet.1 hk, hgk, LinearMap.smul_apply, smul_eq_mul,
    mem_activeSet.1 (hxj.symm ▸ mem_singleton j : j ∈ activeSet f c x)]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A constraint and a nonzero multiple of it are active at the same points. -/
theorem mem_activeSet_iff_of_smul_eq {k : κ} {r : 𝕜} (hr : r ≠ 0) (hg : g k = r • f j)
    (hd : d k = r * c j) (y : E) : k ∈ activeSet g d y ↔ j ∈ activeSet f c y := by
  simp [hg, hd, mul_right_inj' hr]

/-- **Uniqueness of irredundant presentations.** Two finite irredundant presentations of
polyhedra by nonzero functionals cut out the same polyhedron exactly when they agree up to
relabelling the constraints and rescaling each constraint by a positive factor. -/
theorem polyhedron_eq_iff_exists_equiv [Finite ι] [Finite κ] (hf : ∀ j, f j ≠ 0)
    (hg : ∀ k, g k ≠ 0) (hfc : ∀ j, ∃ x ∈ polyhedron f c, activeSet f c x = {j})
    (hgd : ∀ k, ∃ x ∈ polyhedron g d, activeSet g d x = {k}) :
    polyhedron f c = polyhedron g d ↔ ∃ (e : ι ≃ κ) (r : ι → 𝕜), ∀ j,
      0 < r j ∧ g (e j) = r j • f j ∧ d (e j) = r j * c j := by
  constructor
  · intro hP
    choose x hx hxj using hfc
    choose y hy hyk using hgd
    choose φ hφ r hr hgφ hdφ using fun j ↦
      exists_pos_smul_eq_of_activeSet_eq_singleton hP (hx j) (hxj j) (hf j)
    choose ψ hψ s hs hfψ hcψ using fun k ↦
      exists_pos_smul_eq_of_activeSet_eq_singleton hP.symm (hy k) (hyk k) (hg k)
    -- Matched constraints are active at the same points, so the witness of a facet detects
    -- which constraint it is matched with.
    have hψφ (j : ι) : ψ (φ j) = j := by
      have := (mem_activeSet_iff_of_smul_eq (hs (φ j)).ne' (hfψ (φ j)) (hcψ (φ j)) (x j)).2
        (hφ j)
      rwa [hxj j, mem_singleton_iff] at this
    have hφψ (k : κ) : φ (ψ k) = k := by
      have := (mem_activeSet_iff_of_smul_eq (hr (ψ k)).ne' (hgφ (ψ k)) (hdφ (ψ k)) (y k)).2
        (hψ k)
      rwa [hyk k, mem_singleton_iff] at this
    exact ⟨⟨φ, ψ, hψφ, hφψ⟩, r, fun j ↦ ⟨hr j, hgφ j, hdφ j⟩⟩
  · rintro ⟨e, r, h⟩
    ext y
    simp only [mem_polyhedron, ← e.forall_congr_right (q := fun k ↦ d k ≤ g k y)]
    refine forall_congr' fun j ↦ ?_
    rw [(h j).2.1, (h j).2.2, LinearMap.smul_apply, smul_eq_mul, mul_le_mul_iff_right₀ (h j).1]

end TauCeti
