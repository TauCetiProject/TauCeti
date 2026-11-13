/-
Copyright (c) 2026 The Tau Ceti contributors and Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.Map
public import TauCeti.Algebra.DirectSum.DegreeTail

/-!
# Positive gradings and degree submodules

A positive grading is supported on the nonzero degrees of positive degree data.
For any internal module grading, the pieces of degree above a cutoff span a homogeneous
submodule `PositiveDegrees.degreeSubmodule`, characterized by the vanishing of all components of
degree at most the cutoff. For a positive grading, the zero cutoff submodule is the whole module.

These submodules provide degree filtrations without requiring freeness or finite rank of the
homogeneous pieces. Homogeneous linear maps preserve them at the cutoffs prescribed by a
positive degree map, without a decomposition or positive support on the target.

Adapted from `Mei/Algebra/PositiveDegrees/Grading.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` and
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7`, released under Apache 2.0.
-/

public section

namespace TauCeti

variable {N R M : Type*} [AddCommMonoid N] [Semiring R] [AddCommMonoid M] [Module R M]

/-- A grading is positive when its pieces vanish outside the nonzero allowed degrees. -/
class IsPositiveGrading (d : PositiveDegrees N) (ℒ : N → Submodule R M) : Prop where
  /-- The only possibly nonzero pieces have nonzero allowed degree. -/
  eq_bot : ∀ n, n ∉ d.monoid ∨ n = 0 → ℒ n = ⊥

namespace PositiveDegrees

variable (d : PositiveDegrees N) (ℒ : N → Submodule R M)

/-- The sum of the homogeneous pieces of degree strictly greater than `k`. -/
def degreeSubmodule (k : ℕ) : Submodule R M :=
  DirectSum.degreeTail ℒ d.degree (k + 1)

/-- The defining sum for the degree submodule. -/
theorem degreeSubmodule_def (k : ℕ) :
    d.degreeSubmodule ℒ k = ⨆ n : {n : N // (k : ℤ) < d.degree n}, ℒ n := by
  rw [degreeSubmodule, DirectSum.degreeTail_def, iSup_subtype]
  congr 1

/-- A homogeneous piece above the cutoff lies in the degree submodule. -/
theorem le_degreeSubmodule {n : N} {k : ℕ} (hn : (k : ℤ) < d.degree n) :
    ℒ n ≤ d.degreeSubmodule ℒ k := by
  rw [degreeSubmodule]
  exact DirectSum.le_degreeTail ℒ d.degree (by omega)

/-- Degree submodules decrease as the cutoff increases. -/
theorem degreeSubmodule_antitone : Antitone (d.degreeSubmodule ℒ) := by
  intro k l h
  simp only [degreeSubmodule]
  exact DirectSum.degreeTail_antitone ℒ d.degree (Nat.succ_le_succ h)

/-- A homogeneous linear map carries degree submodules into degree submodules
at the cutoffs prescribed by its positive degree map. Only the source grading
needs positive support; no direct-sum decomposition is required. -/
theorem map_degreeSubmodule_le {N' M' : Type*} [AddCommMonoid N']
    [AddCommMonoid M'] [Module R M'] {e : PositiveDegrees N'}
    (T : PositiveDegreeMap d e) (ℒ' : N' → Submodule R M')
    [IsPositiveGrading d ℒ] (f : M →ₗ[R] M')
    (hf : ∀ n, ℒ n ≤ (ℒ' (T n)).comap f) (k : ℕ) :
    (d.degreeSubmodule ℒ (T.modulus k)).map f ≤ e.degreeSubmodule ℒ' k := by
  rw [degreeSubmodule_def, Submodule.map_iSup]
  refine iSup_le fun n => ?_
  by_cases hn : n.val ∈ d.monoid
  · exact (Submodule.map_le_iff_le_comap.mpr (hf n.val)).trans
      (e.le_degreeSubmodule ℒ' (T.degree_gt k hn n.property))
  · rw [IsPositiveGrading.eq_bot (d := d) (ℒ := ℒ) n.val (Or.inl hn),
      Submodule.map_bot]
    exact bot_le

variable [DecidableEq N] [DirectSum.Decomposition ℒ]

/-- Membership means that all components of degree at most the cutoff vanish. -/
theorem mem_degreeSubmodule_iff {x : M} {k : ℕ} :
    x ∈ d.degreeSubmodule ℒ k ↔
      ∀ n, d.degree n ≤ k → (DirectSum.decompose ℒ x n : M) = 0 := by
  rw [degreeSubmodule, DirectSum.mem_degreeTail_iff]
  have hcut (n : N) : d.degree n < ((k + 1 : ℕ) : ℤ) ↔ d.degree n ≤ k := by omega
  simp only [hcut]

/-- A homogeneous element is above the cutoff exactly when it is zero or its degree is above it. -/
theorem mem_degreeSubmodule_of_mem_iff {n : N} {x : M} {k : ℕ} (hx : x ∈ ℒ n) :
    x ∈ d.degreeSubmodule ℒ k ↔ x = 0 ∨ (k : ℤ) < d.degree n := by
  constructor
  · intro h
    by_cases hn : (k : ℤ) < d.degree n
    · exact Or.inr hn
    · refine Or.inl ?_
      simpa only [DirectSum.decompose_of_mem_same ℒ hx] using
        (d.mem_degreeSubmodule_iff ℒ).mp h n (le_of_not_gt hn)
  · rintro (rfl | hn)
    · exact Submodule.zero_mem _
    · exact d.le_degreeSubmodule ℒ hn hx

/-- Every degree submodule is closed under taking homogeneous components. -/
theorem degreeSubmodule_isHomogeneous (k : ℕ) :
    DirectSum.SetLike.IsHomogeneous ℒ (d.degreeSubmodule ℒ k) := by
  intro n x hx
  by_cases hn : (k : ℤ) < d.degree n
  · exact d.le_degreeSubmodule ℒ hn (DirectSum.decompose ℒ x n).property
  · rw [(d.mem_degreeSubmodule_iff ℒ).mp hx n (le_of_not_gt hn)]
    exact Submodule.zero_mem _

variable [IsPositiveGrading d ℒ]

omit [DecidableEq N] [DirectSum.Decomposition ℒ] in
/-- A positive grading has no pieces of nonpositive degree. -/
theorem eq_bot_of_degree_nonpos (n : N) (hn : d.degree n ≤ 0) : ℒ n = ⊥ := by
  by_cases h : n ∈ d.monoid ∧ n ≠ 0
  · exact absurd (d.degree_pos h.1 h.2) (not_lt.mpr hn)
  · exact IsPositiveGrading.eq_bot (d := d) (ℒ := ℒ) n (by tauto)

/-- All of a positively graded module lies above the zero cutoff. -/
@[simp]
theorem degreeSubmodule_zero : d.degreeSubmodule ℒ 0 = ⊤ := by
  rw [eq_top_iff, ← (DirectSum.Decomposition.isInternal ℒ).submodule_iSup_eq_top]
  refine iSup_le fun n => ?_
  by_cases hn : (0 : ℤ) < d.degree n
  · exact d.le_degreeSubmodule ℒ hn
  · rw [d.eq_bot_of_degree_nonpos ℒ n (not_lt.mp hn)]
    exact bot_le

end PositiveDegrees
end TauCeti
