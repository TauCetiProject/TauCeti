/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Modular.Stabilizer
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# No elliptic points for `Γ₁(N)` at level at least four

For `N ≥ 4`, the action of `Γ₁(N)` on the upper half-plane has trivial point
stabilizers. The same holds for its effective image in `PSL(2, ℝ)`, the group acting
on the analytic modular curve. Thus neither order-two nor order-three elliptic
points contribute to the dimension formulas at these levels.

The central matrices are handled separately: `-I` belongs to `Γ₁(N)` only when
`N ∣ 2`. For a noncentral matrix fixing a point, its integral trace lies strictly
between `-2` and `2`, whereas membership in `Γ₁(N)` makes that trace congruent to `2`
modulo `N`.

## Main results

* `eq_one_of_mem_Gamma1_of_smul_eq_self`: only the identity in `Γ₁(N)` fixes a point.
* `stabilizer_Gamma1_eq_bot`: triviality of the integral point stabilizers.
* `stabilizer_Gamma1_map_eq_bot`: triviality of the effective real point stabilizers.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §2.3.
-/

public section

open Matrix Matrix.SpecialLinearGroup MulAction UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

namespace TauCeti

variable {N : ℕ} {γ : SL(2, ℤ)} {z : ℍ}

/-- At level `N ≥ 4`, an element of `Γ₁(N)` fixing a point of the upper half-plane
is the identity. -/
theorem eq_one_of_mem_Gamma1_of_smul_eq_self (hN : 4 ≤ N) (hγ : γ ∈ Gamma1 N)
    (hz : γ • z = z) : γ = 1 := by
  have hc : γ ∈ Subgroup.center SL(2, ℤ) := by
    by_contra hc
    have ht := ModularGroup.trace_sq_lt_four_of_smul_eq_self_of_not_mem_center hz hc
    have hdiv : (N : ℤ) ∣ 2 - (γ : Matrix (Fin 2) (Fin 2) ℤ).trace := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp
      obtain ⟨ha, hd, -⟩ := (Gamma1_mem N γ).mp hγ
      simp only [Matrix.trace_fin_two, Int.cast_sub, Int.cast_add, Int.cast_ofNat, ha, hd]
      ring
    have hnonneg : 0 ≤ 2 - (γ : Matrix (Fin 2) (Fin 2) ℤ).trace := by nlinarith
    have hlt : 2 - (γ : Matrix (Fin 2) (Fin 2) ℤ).trace < (N : ℤ) := by
      have hN' : (4 : ℤ) ≤ N := by exact_mod_cast hN
      nlinarith
    have heq := Int.eq_zero_of_dvd_of_nonneg_of_lt hnonneg hlt hdiv
    nlinarith
  rcases mem_center_iff_eq_one_or_eq_neg_one.mp hc with h | rfl
  · exact h
  · have hdiv := neg_one_mem_Gamma1_iff.mp hγ
    have := Nat.le_of_dvd (by norm_num : 0 < (2 : ℕ)) hdiv
    omega

/-- All point stabilizers in `Γ₁(N)` are trivial at level `N ≥ 4`. -/
@[simp]
theorem stabilizer_Gamma1_eq_bot (hN : 4 ≤ N) (z : ℍ) :
    stabilizer (Gamma1 N) z = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  exact eq_one_of_mem_Gamma1_of_smul_eq_self hN g.2
    (by simpa only [mem_stabilizer_iff, Subgroup.smul_def] using hg)

/-- The effective image of `Γ₁(N)` in `PSL(2, ℝ)` has no elliptic stabilizers
at level `N ≥ 4`. -/
@[simp]
theorem stabilizer_Gamma1_map_eq_bot (hN : 4 ≤ N) (z : ℍ) :
    stabilizer ((Gamma1 N).map sl2zToPSL2R) z = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  obtain ⟨γ, hγ, hγg⟩ := g.2
  have hfix : γ • z = z := by
    have h := hg
    rw [mem_stabilizer_iff, Subgroup.smul_def, ← hγg, ← psl2zToPSL2R_mk,
      psl2zToPSL2R_smul, pslMk_smul] at h
    exact h
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  simp only [← hγg, eq_one_of_mem_Gamma1_of_smul_eq_self hN hγ hfix, map_one,
    Subgroup.coe_one]

end TauCeti
