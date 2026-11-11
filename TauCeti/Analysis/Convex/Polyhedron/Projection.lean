/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.FourierMotzkin
public import TauCeti.Analysis.Convex.Sweep.Basic
public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Basic.Finite.Prod
import Mathlib.Tactic.Linarith

/-!
# One-parameter projections of convex polyhedra

Eliminating a nonnegative real parameter produces a finite family of continuous
affine inequalities. The resulting rows are the original rows with nonnegative
parameter coefficient and the pairwise resultants of a negative and a positive
coefficient. The family is explicit and uses no division, so additional scalar
properties of its rows can be checked directly.

As an application, adding a negative ray to a convex polyhedron preserves
polyhedrality without any transversality or boundedness assumption.

Adapted from `Mei/Analysis/Convex/Polyhedron/Projection.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7`, released under Apache 2.0.
Original copyright (c) 2026 Mei contributors; original author: Codex.
-/

public section

namespace TauCeti

/-- The rows remaining after elimination of a nonnegative parameter: rows with
nonnegative coefficient, and pairs of a negative with a positive coefficient.
The abbreviation makes the sum constructors available for inspecting resultant rows. -/
abbrev NonnegElimIndex {ι : Type*} (a : ι → ℝ) :=
  {i : ι // 0 ≤ a i} ⊕ ({i : ι // a i < 0} × {i : ι // 0 < a i})

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- The explicit continuous affine rows obtained by eliminating `t ≥ 0` from
`g i y + a i * t ≤ 0`. Pair rows use only multiplication and subtraction. -/
def nonnegElimFamily (g : ι → (V →ᴬ[ℝ] ℝ)) (a : ι → ℝ) :
    NonnegElimIndex a → (V →ᴬ[ℝ] ℝ)
  | .inl i => g i.val
  | .inr (i, j) => a j.val • g i.val - a i.val • g j.val

/-- A retained single row evaluates as its original affine functional. -/
@[simp]
theorem nonnegElimFamily_single_apply (g : ι → (V →ᴬ[ℝ] ℝ)) (a : ι → ℝ)
    (i : {i : ι // 0 ≤ a i}) (y : V) :
    nonnegElimFamily g a (.inl i) y = g i.val y := (rfl)

/-- A paired resultant evaluates as the division-free linear combination of its rows. -/
@[simp]
theorem nonnegElimFamily_pair_apply (g : ι → (V →ᴬ[ℝ] ℝ)) (a : ι → ℝ)
    (i : {i : ι // a i < 0}) (j : {i : ι // 0 < a i}) (y : V) :
    nonnegElimFamily g a (.inr (i, j)) y = a j.val * g i.val y - a i.val * g j.val y :=
  (rfl)

/-- A retained row has the original linear part. -/
@[simp]
theorem nonnegElimFamily_single_linear (g : ι → (V →ᴬ[ℝ] ℝ)) (a : ι → ℝ)
    (i : {i : ι // 0 ≤ a i}) :
    (nonnegElimFamily g a (.inl i)).toAffineMap.linear = (g i.val).toAffineMap.linear :=
  (rfl)

/-- The linear part of a resultant is the same combination of the original linear parts. -/
@[simp]
theorem nonnegElimFamily_pair_linear (g : ι → (V →ᴬ[ℝ] ℝ)) (a : ι → ℝ)
    (i : {i : ι // a i < 0}) (j : {i : ι // 0 < a i}) :
    (nonnegElimFamily g a (.inr (i, j))).toAffineMap.linear =
      a j.val • (g i.val).toAffineMap.linear - a i.val • (g j.val).toAffineMap.linear :=
  (rfl)

/-- Membership in the one-parameter projection is given by the explicit finite
family of resultant affine inequalities. -/
theorem exists_nonneg_affine_le_iff [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {a : ι → ℝ} {y : V} :
    (∃ t : ℝ, 0 ≤ t ∧ ∀ i, g i y + a i * t ≤ 0) ↔
      ∀ k : NonnegElimIndex a, nonnegElimFamily g a k y ≤ 0 := by
  have he : (∃ t : ℝ, 0 ≤ t ∧ ∀ i, g i y + a i * t ≤ 0) ↔
      ∃ t : ℝ, 0 ≤ t ∧ ∀ i, a i * t ≤ -g i y := by
    constructor
    · rintro ⟨t, ht, h⟩
      exact ⟨t, ht, fun i => by linarith [h i]⟩
    · rintro ⟨t, ht, h⟩
      exact ⟨t, ht, fun i => by linarith [h i]⟩
  rw [he, TauCeti.exists_nonneg_mul_le_iff]
  constructor
  · rintro ⟨hsingle, hpair⟩ k
    rcases k with i | ⟨i, j⟩
    · exact neg_nonneg.mp (hsingle i.val i.property)
    · rw [nonnegElimFamily_pair_apply]
      have h := hpair i.val j.val i.property j.property
      simp only [mul_neg] at h
      linarith
  · intro h
    constructor
    · intro i hi
      exact neg_nonneg.mpr (h (.inl ⟨i, hi⟩))
    · intro i j hi hj
      have hp := h (.inr (⟨i, hi⟩, ⟨j, hj⟩))
      rw [nonnegElimFamily_pair_apply] at hp
      simp only [mul_neg]
      linarith

/-- An explicit presentation of a nonnegative one-parameter projection. -/
theorem setOf_exists_nonneg_affine_le_eq [Finite ι]
    (g : ι → (V →ᴬ[ℝ] ℝ)) (a : ι → ℝ) :
    {y : V | ∃ t : ℝ, 0 ≤ t ∧ ∀ i, g i y + a i * t ≤ 0} =
      {y : V | ∀ k : NonnegElimIndex a, nonnegElimFamily g a k y ≤ 0} := by
  ext y
  exact exists_nonneg_affine_le_iff

/-- Convex polyhedrality is preserved by elimination of a nonnegative parameter. -/
theorem isConvexPolyhedron_setOf_exists_nonneg_affine_le [Finite ι]
    (g : ι → (V →ᴬ[ℝ] ℝ)) (a : ι → ℝ) :
    TauCeti.IsConvexPolyhedron {y : V | ∃ t : ℝ, 0 ≤ t ∧ ∀ i, g i y + a i * t ≤ 0} := by
  rw [setOf_exists_nonneg_affine_le_eq]
  exact TauCeti.isConvexPolyhedron_setOf_forall _

/-- The resultant presentation for adding a negative ray to a finite family of
closed affine halfspaces. The parameter slopes are the linear parts evaluated at `n`. -/
theorem setOf_exists_nonneg_add_smul_forall_le_eq [Finite ι]
    (g : ι → (V →ᴬ[ℝ] ℝ)) (n : V) :
    {y : V | ∃ t : ℝ, 0 ≤ t ∧ ∀ i, g i (y + t • n) ≤ 0} =
      {y : V | ∀ k : NonnegElimIndex (fun i => (g i).linear n),
        nonnegElimFamily g (fun i => (g i).linear n) k y ≤ 0} := by
  have he (j : ι) (y : V) (t : ℝ) :
      g j (y + t • n) = g j y + (g j).linear n * t := by
    rw [add_comm y]
    simpa [vadd_eq_add, mul_comm, add_comm] using (g j).toAffineMap.map_vadd y (t • n)
  simp_rw [he]
  exact setOf_exists_nonneg_affine_le_eq g (fun i => (g i).linear n)

/-- Sweeping any convex polyhedron along a negative ray preserves polyhedrality,
including tangent vectors and arbitrary unbounded bases. -/
theorem IsConvexPolyhedron.sweep {P : Set V}
    (hP : IsConvexPolyhedron P) (n : V) : IsConvexPolyhedron (Set.sweep ℝ P n) := by
  obtain ⟨k, g, rfl⟩ := isConvexPolyhedron_iff.mp hP
  have he : Set.sweep ℝ {x | ∀ j, g j x ≤ 0} n =
      {y | ∃ t : ℝ, 0 ≤ t ∧ ∀ j, g j (y + t • n) ≤ 0} := by
    ext y
    exact Set.mem_sweep_iff
  rw [he, setOf_exists_nonneg_add_smul_forall_le_eq]
  exact isConvexPolyhedron_setOf_forall _

end TauCeti
