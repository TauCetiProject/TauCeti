/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Cone.Basic
public import TauCeti.Geometry.Toric.Algebraic.Lattice.Basic

/-!
# Salience from a positive integral functional

A lattice-rational cone carrying an integral functional which is strictly positive on its nonzero
lattice points contains no line. The real extension of the functional is nonnegative on every
generator of the cone, and vanishes on a nonnegative combination of generators only when every
generator with nonzero coefficient is zero.
-/

public section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- A lattice-rational cone which carries an integral functional strictly positive on its nonzero
lattice points is salient. -/
theorem IsLatticeRational.salient_of_forall_pos (hσ : IsLatticeRational i σ)
    (hi : IsIntegralLattice i) (δ : N →+ ℤ) (hδ : ∀ n, i n ∈ σ → n ≠ 0 → 0 < δ n) :
    (σ : ConvexCone ℝ V).Salient := by
  obtain ⟨s, rfl⟩ := isLatticeRational_iff.mp hσ
  -- The real extension of `δ` is nonnegative on the cone and detects zero there.
  have key (x : V) (hx : x ∈ PointedCone.hull ℝ (i '' (s : Set N))) :
      0 ≤ hi.realCharacter δ x ∧ (hi.realCharacter δ x = 0 → x = 0) := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, hn, rfl⟩ := hy
      by_cases h0 : i n = 0
      · simp [h0]
      · have := hδ n (PointedCone.subset_hull ⟨n, hn, rfl⟩) fun h => h0 (h ▸ map_zero i)
        simp only [IsIntegralLattice.realCharacter_apply]
        exact ⟨by positivity, fun h => absurd (by exact_mod_cast h) this.ne'⟩
    | zero => simp
    | add x y _ _ hx hy =>
      refine ⟨by simpa using add_nonneg hx.1 hy.1, fun h => ?_⟩
      have hx0 : hi.realCharacter δ x = 0 := by
        simp only [map_add] at h; linarith [hx.1, hy.1]
      have hy0 : hi.realCharacter δ y = 0 := by
        simp only [map_add] at h; linarith [hx.1, hy.1]
      simp [hx.2 hx0, hy.2 hy0]
    | smul c x _ hx =>
      rw [← Nonneg.coe_smul, map_smul, smul_eq_mul]
      refine ⟨mul_nonneg c.2 hx.1, fun h => ?_⟩
      rcases mul_eq_zero.mp h with h | h
      · simp [h]
      · simp [hx.2 h]
  intro x hx hx0 hnx
  have h1 := (key x hx).1
  have h2 := (key (-x) hnx).1
  rw [map_neg] at h2
  exact hx0 ((key x hx).2 (le_antisymm (by linarith) h1))

end TauCeti.Toric
