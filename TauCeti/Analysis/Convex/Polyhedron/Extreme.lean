/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.LinearAlgebra.Dual.Defs

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Extreme points of a polyhedron

Let `f : ι → Module.Dual 𝕜 E` be a finite family of linear functionals on a vector space over a
linearly ordered field, and `c : ι → 𝕜`. The *polyhedron* they cut out is the intersection of
half-spaces

`P = {x | c j ≤ f j x for every j}`

(`TauCeti.polyhedron f c`). A constraint `j` is *active* at `x` when `f j x = c j`
(`TauCeti.activeSet f c x`).

The vertices of `P` are characterized by their active constraints: a point `x` of `P` is an
extreme point exactly when the only vector annihilated by every active functional at `x` is zero
(`TauCeti.mem_extremePoints_polyhedron_iff`). If some nonzero `w` is annihilated by the active
functionals, the inactive constraints have slack at `x`, so `x ± t w` stays in `P` for a small
`t > 0` and `x` is the midpoint of a nondegenerate segment. Conversely, if `x` lies in an open
segment of `P`, every active constraint is attained at both ends, so the segment is parallel to
a vector annihilated by the active functionals. In finite dimension this says that the active
functionals span the dual space.

For each set `s` of constraints, the points of `P` where every constraint in `s` is active form
an extreme subset of `P` (`TauCeti.isExtreme_polyhedron_inter_setOf_subset_activeSet`), the face
cut out by `s`. The extreme points of a face are therefore vertices of `P` at which every
constraint in `s` is active.

## Main definitions

* `TauCeti.polyhedron f c`: the polyhedron `{x | ∀ j, c j ≤ f j x}`.
* `TauCeti.activeSet f c x`: the constraints active at `x`.

## Main results

* `TauCeti.convex_polyhedron`: a polyhedron is convex.
* `TauCeti.isExtreme_polyhedron_inter_setOf_subset_activeSet`: the face where a set of
  constraints is active is an extreme subset.
* `TauCeti.mem_extremePoints_polyhedron_iff`: the vertices are the points of the polyhedron at
  which the active functionals have no common nonzero zero.

## References

* A. Schrijver, *Theory of Linear and Integer Programming*, Wiley, 1986, Section 8.5.
-/

public section

open Set

namespace TauCeti

variable {𝕜 E ι : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The constraints `j` that are active at `x`, those with `f j x = c j`. -/
def activeSet (f : ι → Module.Dual 𝕜 E) (c : ι → 𝕜) (x : E) : Set ι :=
  {j | f j x = c j}

@[simp]
theorem mem_activeSet {f : ι → Module.Dual 𝕜 E} {c : ι → 𝕜} {x : E} {j : ι} :
    j ∈ activeSet f c x ↔ f j x = c j := Iff.rfl

variable [LinearOrder 𝕜]

/-- The polyhedron `{x | ∀ j, c j ≤ f j x}` cut out by the half-spaces `c j ≤ f j x`. -/
def polyhedron (f : ι → Module.Dual 𝕜 E) (c : ι → 𝕜) : Set E :=
  {x | ∀ j, c j ≤ f j x}

variable {f : ι → Module.Dual 𝕜 E} {c : ι → 𝕜} {x : E} {j : ι}

@[simp]
theorem mem_polyhedron : x ∈ polyhedron f c ↔ ∀ j, c j ≤ f j x := Iff.rfl

variable [IsStrictOrderedRing 𝕜]

/-- A polyhedron is convex. -/
theorem convex_polyhedron : Convex 𝕜 (polyhedron f c) := by
  intro x hx y hy a b ha hb hab j
  calc c j = a * c j + b * c j := by rw [← add_mul, hab, one_mul]
    _ ≤ a * f j x + b * f j y := by gcongr <;> simp_all
    _ = f j (a • x + b • y) := by simp

/-- If `x` lies in the open segment between two points of a polyhedron, every constraint active
at `x` is active at both endpoints. -/
theorem mem_activeSet_of_mem_openSegment {x₁ x₂ : E} (hx₁ : x₁ ∈ polyhedron f c)
    (hx₂ : x₂ ∈ polyhedron f c) (hx : x ∈ openSegment 𝕜 x₁ x₂) (hj : j ∈ activeSet f c x) :
    j ∈ activeSet f c x₁ ∧ j ∈ activeSet f c x₂ := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
  have h₁ := hx₁ j
  have h₂ := hx₂ j
  simp only [mem_activeSet, map_add, map_smul, smul_eq_mul] at hj ⊢
  have hsum : a * (f j x₁ - c j) + b * (f j x₂ - c j) = 0 := by
    linear_combination hj - c j * hab
  have e₁ : a * (f j x₁ - c j) = 0 := by
    nlinarith [mul_nonneg ha.le (sub_nonneg.2 h₁), mul_nonneg hb.le (sub_nonneg.2 h₂)]
  have e₂ : b * (f j x₂ - c j) = 0 := by
    nlinarith [mul_nonneg ha.le (sub_nonneg.2 h₁), mul_nonneg hb.le (sub_nonneg.2 h₂)]
  exact ⟨sub_eq_zero.1 ((mul_eq_zero.1 e₁).resolve_left ha.ne'),
    sub_eq_zero.1 ((mul_eq_zero.1 e₂).resolve_left hb.ne')⟩

/-- The points of a polyhedron at which every constraint in `s` is active form an extreme subset
of the polyhedron: the face cut out by `s`. -/
theorem isExtreme_polyhedron_inter_setOf_subset_activeSet (s : Set ι) :
    IsExtreme 𝕜 (polyhedron f c) (polyhedron f c ∩ {x | s ⊆ activeSet f c x}) := by
  refine ⟨inter_subset_left, fun x₁ hx₁ x₂ hx₂ x hx hseg ↦ ?_⟩
  exact ⟨hx₁, fun j hj ↦ (mem_activeSet_of_mem_openSegment hx₁ hx₂ hseg (hx.2 hj)).1⟩

/-- **Vertices of a polyhedron.** A point `x` of a polyhedron cut out by finitely many
half-spaces is an extreme point exactly when the only vector annihilated by all the functionals
active at `x` is zero. -/
theorem mem_extremePoints_polyhedron_iff [Finite ι] :
    x ∈ extremePoints 𝕜 (polyhedron f c) ↔
      x ∈ polyhedron f c ∧ ∀ w, (∀ j ∈ activeSet f c x, f j w = 0) → w = 0 := by
  have := Fintype.ofFinite ι
  constructor
  · rintro ⟨hx, hext⟩
    refine ⟨hx, fun w hw ↦ ?_⟩
    -- The inactive constraints have slack at `x`, so `x ± t w` stays in the polyhedron for
    -- `t = (1 + S)⁻¹`, where `S` bounds every ratio `|f j w| / (f j x - c j)`.
    set S := ∑ j, |f j w| / (f j x - c j) with hS
    have hterm (j : ι) : 0 ≤ |f j w| / (f j x - c j) :=
      div_nonneg (abs_nonneg _) (sub_nonneg.2 (hx j))
    have hS₀ : 0 ≤ S := Finset.sum_nonneg fun j _ ↦ hterm j
    set t := (1 + S)⁻¹ with ht
    have ht₀ : 0 < t := inv_pos.2 (by linarith)
    have hbound (j : ι) : t * |f j w| ≤ f j x - c j := by
      rcases (sub_nonneg.2 (hx j)).eq_or_lt with h | h
      · rw [hw j (sub_eq_zero.1 h.symm)]
        simp [← h]
      · have hle : |f j w| / (f j x - c j) ≤ S :=
          Finset.single_le_sum (fun j _ ↦ hterm j) (Finset.mem_univ j)
        rw [div_le_iff₀ h] at hle
        rw [ht, inv_mul_le_iff₀ (by linarith)]
        nlinarith [abs_nonneg (f j w)]
    have hmem (s : 𝕜) (hs : |s| ≤ t) : x + s • w ∈ polyhedron f c := fun j ↦ by
      have h := hbound j
      have : |s * f j w| ≤ t * |f j w| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
      simp only [map_add, map_smul, smul_eq_mul]
      linarith [neg_abs_le (s * f j w)]
    have hseg : x ∈ openSegment 𝕜 (x + t • w) (x + (-t) • w) :=
      ⟨2⁻¹, 2⁻¹, by norm_num, by norm_num, by norm_num, by
        rw [smul_add, smul_add, add_add_add_comm, ← add_smul, ← smul_assoc, ← smul_assoc,
          ← add_smul]
        norm_num⟩
    have h := hext (hmem t (abs_of_pos ht₀).le) (hmem (-t) (by simp [abs_of_pos ht₀])) hseg
    exact (smul_eq_zero.1 (add_eq_left.1 h)).resolve_left ht₀.ne'
  · rintro ⟨hx, hker⟩
    refine mem_extremePoints_iff_left.2 ⟨hx, fun x₁ hx₁ x₂ hx₂ hseg ↦ ?_⟩
    refine (sub_eq_zero.1 (hker _ fun j hj ↦ ?_))
    rw [map_sub, mem_activeSet.1 (mem_activeSet_of_mem_openSegment hx₁ hx₂ hseg hj).1,
      mem_activeSet.1 hj, sub_self]

end TauCeti
