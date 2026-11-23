/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Elliptic.Gamma.Zero
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Fuchsian

/-!
# The elliptic points of `Γ₁(N)`

For `N ≥ 4`, the action of `Γ₁(N)` on the upper half-plane has trivial point
stabilizers. The same holds for its effective image in `PSL(2, ℝ)`, the group acting
on the analytic modular curve. Thus neither order-two nor order-three elliptic
points contribute to the dimension formulas at these levels.

The central matrices are handled separately: `-I` belongs to `Γ₁(N)` only when
`N ∣ 2`. For a noncentral matrix fixing a point, its integral trace lies strictly
between `-2` and `2`, whereas membership in `Γ₁(N)` makes that trace congruent to `2`
modulo `N` (`CongruenceSubgroup.dvd_two_sub_trace_of_mem_Gamma1`).

The same congruence gives the counts `ε₂` and `ε₃` of the dimension formulas for `Γ₁(N)` at
every level. A conjugate of `S` has trace `0` and a conjugate of `T⁻¹ S` has trace `-1`, so
neither lies in `Γ₁(N)` unless `N ∣ 2`, resp. `N ∣ 3`. At the remaining levels `1`, `2` and `3`
every unit modulo `N` is `±1`, so `Γ₁(N)` and `Γ₀(N)` have the same effective image
(`TauCeti.Gamma1_map_eq_Gamma0_map`), and the counts are those of `Γ₀(N)`: `ε₂ = 1` exactly at
the levels `1` and `2`, and `ε₃ = 1` exactly at the levels `1` and `3`.

## Main results

* `eq_one_of_mem_Gamma1_of_smul_eq_self`: only the identity in `Γ₁(N)` fixes a point.
* `stabilizer_Gamma1_eq_bot`: triviality of the integral point stabilizers.
* `stabilizer_Gamma1_map_eq_bot`: triviality of the effective real point stabilizers.
* `card_orderTwoElliptic_Gamma1`, `card_orderThreeElliptic_Gamma1`: the counts `ε₂` and `ε₃` of
  `Γ₁(N)` at every level.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §§2.3, 3.9.
-/

public section

open Matrix Matrix.SpecialLinearGroup MulAction UpperHalfPlane CongruenceSubgroup ModularGroup
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
    have hdiv := dvd_two_sub_trace_of_mem_Gamma1 hγ
    have hnonneg : 0 ≤ 2 - (γ : Matrix (Fin 2) (Fin 2) ℤ).trace := by nlinarith
    have hlt : 2 - (γ : Matrix (Fin 2) (Fin 2) ℤ).trace < (N : ℤ) := by
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
  exact eq_one_of_mem_Gamma1_of_smul_eq_self hN g.property
    (by simpa only [mem_stabilizer_iff, Subgroup.smul_def] using hg)

/-- The effective image of `Γ₁(N)` in `PSL(2, ℝ)` has no elliptic stabilizers
at level `N ≥ 4`. -/
@[simp]
theorem stabilizer_Gamma1_map_eq_bot (hN : 4 ≤ N) (z : ℍ) :
    stabilizer ((Gamma1 N).map sl2zToPSL2R) z = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  obtain ⟨γ, hγ, hγg⟩ := g.property
  have hfix : γ • z = z := by
    have h := hg
    rw [mem_stabilizer_iff, Subgroup.smul_def, ← hγg, ← psl2zToPSL2R_mk,
      psl2zToPSL2R_smul, pslMk_smul] at h
    exact h
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  simp only [← hγg, eq_one_of_mem_Gamma1_of_smul_eq_self hN hγ hfix, map_one,
    Subgroup.coe_one]

/-- A conjugate of `S`, of trace `0`, lies in `Γ₁(N)` only if `N ∣ 2`. -/
private theorem conj_S_notMem_Gamma1 (hN : ¬(N : ℤ) ∣ 2) : γ * S * γ⁻¹ ∉ Gamma1 N := fun h ↦ by
  have hdvd := dvd_two_sub_trace_of_conj_mem_Gamma1 h
  -- `S = !![0, -1; 1, 0]` has trace `0`
  rw [coe_S, Matrix.trace_fin_two_of] at hdvd
  exact hN (by simpa using hdvd)

/-- A conjugate of `T⁻¹ S`, of trace `-1`, lies in `Γ₁(N)` only if `N ∣ 3`. -/
private theorem conj_T_inv_mul_S_notMem_Gamma1 (hN : ¬(N : ℤ) ∣ 3) :
    γ * (T⁻¹ * S) * γ⁻¹ ∉ Gamma1 N := fun h ↦ by
  have hdvd := dvd_two_sub_trace_of_conj_mem_Gamma1 h
  -- `T⁻¹ S = !![1, -1; 0, 1] * !![0, -1; 1, 0] = !![-1, -1; 1, 0]` has trace `-1`
  rw [coe_mul, coe_T_inv, coe_S, Matrix.mul_fin_two, Matrix.trace_fin_two_of] at hdvd
  exact hN (by simpa using hdvd)

/-- **The count `ε₂(Γ₁(N))`**: `Γ₁(N)` has one elliptic point of order two at the levels `1` and
`2`, and none at any other level. -/
theorem card_orderTwoElliptic_Gamma1 :
    Nat.card {q : orbitRel.Quotient ((Gamma1 N).map sl2zToPSL2R) ℍ //
      cardStabilizerOnOrbit q = 2} = if N = 1 ∨ N = 2 then 1 else 0 := by
  split_ifs with hN
  · rw [Gamma1_map_eq_Gamma0_map (by rcases hN with rfl | rfl <;> decide),
      card_orderTwoElliptic_Gamma0]
    rcases hN with rfl | rfl <;> rw [Nat.card_eq_fintype_card] <;> decide
  · refine (Gamma1 N).card_orderTwoElliptic_map_eq_zero fun _ ↦ conj_S_notMem_Gamma1 fun h ↦ hN ?_
    exact (Nat.dvd_prime Nat.prime_two).mp (Int.natCast_dvd_natCast.mp h)

/-- **The count `ε₃(Γ₁(N))`**: `Γ₁(N)` has one elliptic point of order three at the levels `1`
and `3`, and none at any other level. -/
theorem card_orderThreeElliptic_Gamma1 :
    Nat.card {q : orbitRel.Quotient ((Gamma1 N).map sl2zToPSL2R) ℍ //
      cardStabilizerOnOrbit q = 3} = if N = 1 ∨ N = 3 then 1 else 0 := by
  split_ifs with hN
  · rw [Gamma1_map_eq_Gamma0_map (by rcases hN with rfl | rfl <;> decide),
      card_orderThreeElliptic_Gamma0]
    rcases hN with rfl | rfl <;> rw [Nat.card_eq_fintype_card] <;> decide
  · refine (Gamma1 N).card_orderThreeElliptic_map_eq_zero fun _ ↦
      conj_T_inv_mul_S_notMem_Gamma1 fun h ↦ hN ?_
    exact (Nat.dvd_prime Nat.prime_three).mp (Int.natCast_dvd_natCast.mp h)

end TauCeti
