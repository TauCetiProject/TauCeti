/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Count.Basic
public import TauCeti.NumberTheory.NumberField.Global.RayClass.MainTerm
import TauCeti.NumberTheory.NumberField.Global.Counting.Ray.Ideal.Count
import TauCeti.NumberTheory.NumberField.Global.Counting.RayFundamentalDomain.LatticeCount
import TauCeti.NumberTheory.NumberField.Global.Counting.RayFundamentalDomain.MainTerm
import TauCeti.NumberTheory.NumberField.Global.RayClass.Count.Reindex
import TauCeti.RingTheory.Ideal.CoprimeCoset

/-!
# The asymptotic count of the integral ideals of a ray class

Let `𝔪` be a modulus of a number field `K` of degree `n`.  This file proves that the number of
nonzero integral ideals prime to `𝔪` in a fixed ray class with absolute norm at most `x` is
`rayClassIdealMainTerm 𝔪 * x + O(x ^ (1 - 1 / n))`, with the same main term and the same power
saving for every class.

## Main results

* `TauCeti.GlobalNumberFields.isBigO_rayClassIdealCountingFunction_sub`: the ray class ideal
  counting function of a class is `rayClassIdealMainTerm 𝔪 * x + O(x ^ (1 - 1 / [K : ℚ]))`.
* `TauCeti.GlobalNumberFields.rayClassIdealCount`: the ray class ideal counting function is
  `rayClassIdealMainTerm 𝔪 * x + O(x ^ (1 - δ))` for some `δ > 0` uniform in the class.
-/

public section

open Asymptotics Filter MeasureTheory Module NumberField NumberField.mixedEmbedding
open scoped nonZeroDivisors Pointwise

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

private theorem rayClassIdealCountingFunction_mul_card_eq_ncard (𝔪 : Modulus K)
    {c : RayClassGroup 𝔪} (𝔞 : integralIdealsPrimeTo 𝔪) (h𝔞 : idealClass 𝔪 𝔞 = c⁻¹)
    (h𝔞0 : (𝔞 : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰) {ξ : 𝓞 K} (hξ𝔞 : ξ ∈ (𝔞 : Ideal (𝓞 K)))
    (hξ𝔪 : ξ - 1 ∈ 𝔪.finitePart) (x : ℝ) :
    rayClassIdealCountingFunction 𝔪 c x * Nat.card (unitsCongruenceTorsion 𝔪) =
      ((rayFundamentalDomain 𝔪 ∩
          {y | mixedEmbedding.norm y ≤ x * Ideal.absNorm (𝔞 : Ideal (𝓞 K))}) ∩
        (mixedEmbedding K (ξ : K) +ᵥ
          (congruenceLattice 𝔪 (FractionalIdeal.mk0 K ⟨𝔞, h𝔞0⟩) : Set (mixedSpace K)))).ncard := by
  -- as `𝔞` lies in the inverse class and `ξ ∈ 𝔞` is congruent to one modulo `𝔪₀`, the ideals of
  -- `c` of norm at most `x`, counted with the roots of unity congruent to one modulo `𝔪`, match
  -- the points of norm at most `x · N𝔞` of the coset `ξ + Λ` of the congruence lattice of `𝔞`
  -- in the ray fundamental domain
  rw [rayClassIdealCountingFunction_eq_card_dvd_and_idealClass_eq_one 𝔪 𝔞 h𝔞 x,
    card_idealClass_eq_one_dvd_norm_le, ← Nat.card_coe_set_eq, Set.inter_right_comm,
    ← rayIdealSet_eq_inter_vadd 𝔪 ⟨𝔞, h𝔞0⟩ hξ𝔞 hξ𝔪]
  exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter _ (mixedEmbedding.norm · ≤ _))

private theorem exists_mem_idealClass_inv_and_sub_one_mem (𝔪 : Modulus K) (c : RayClassGroup 𝔪) :
    ∃ 𝔞 : integralIdealsPrimeTo 𝔪, idealClass 𝔪 𝔞 = c⁻¹ ∧
      (𝔞 : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰ ∧ ∃ ξ ∈ (𝔞 : Ideal (𝓞 K)), ξ - 1 ∈ 𝔪.finitePart := by
  obtain ⟨𝔞, h𝔞⟩ := idealClass_surjective 𝔪 c⁻¹
  refine ⟨𝔞, h𝔞, mem_nonZeroDivisors_of_ne_zero
    (NumberFieldArithmetic.mem_integralIdealsAway_iff.mp 𝔞.prop).1, ?_⟩
  -- `𝔞` is coprime to `𝔪₀`, so it contains an element congruent to one modulo `𝔪₀`
  exact Ideal.isCoprime_iff_exists_mem_and_sub_one_mem.mp <| Ideal.isCoprime_iff_sup_eq.mpr
    (Modulus.isCoprimeTo_iff_sup_eq_top.mp (Modulus.mem_integralIdealsPrimeTo.mp 𝔞.prop)).2

private theorem exists_abs_rayClassIdealCountingFunction_sub_le (𝔪 : Modulus K)
    {c : RayClassGroup 𝔪} (𝔞 : integralIdealsPrimeTo 𝔪) (h𝔞 : idealClass 𝔪 𝔞 = c⁻¹)
    (h𝔞0 : (𝔞 : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰) {ξ : 𝓞 K} (hξ𝔞 : ξ ∈ (𝔞 : Ideal (𝓞 K)))
    (hξ𝔪 : ξ - 1 ∈ 𝔪.finitePart) : ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |(rayClassIdealCountingFunction 𝔪 c x : ℝ) - rayClassIdealMainTerm 𝔪 * x| ≤
        C * x ^ (1 - (finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨A, -, hA⟩ := exists_abs_ncard_rayFundamentalDomain_inter_norm_le_inter_vadd_sub_le 𝔪
    (FractionalIdeal.mk0 K ⟨𝔞, h𝔞0⟩)
  set N : ℝ := (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ)
  have hN : 1 ≤ N := Nat.one_le_cast.mpr (Ideal.absNorm_pos_of_nonZeroDivisors ⟨_, h𝔞0⟩)
  have hw : 0 < (Nat.card (unitsCongruenceTorsion 𝔪) : ℝ) := Nat.cast_pos.mpr Nat.card_pos
  refine ⟨A * N ^ (1 - (finrank ℚ K : ℝ)⁻¹) / Nat.card (unitsCongruenceTorsion 𝔪), fun x hx ↦ ?_⟩
  have hcount := hA (mixedEmbedding K (ξ : K)) (x * N) (one_le_mul_of_one_le_of_one_le hx hN)
  -- the lattice-point count is `w` times the ideal count, and its main term `w` times ours,
  -- where `w` is the number of roots of unity congruent to one modulo `𝔪`
  rw [← rayClassIdealCountingFunction_mul_card_eq_ncard 𝔪 𝔞 h𝔞 _ hξ𝔞 hξ𝔪 x, Nat.cast_mul,
    mul_left_comm _ x, measureReal_div_covolume_congruenceLattice_mul_absNorm 𝔪 ⟨𝔞, h𝔞0⟩,
    Real.mul_rpow (zero_le_one.trans hx) (zero_le_one.trans hN)] at hcount
  rw [div_mul_eq_mul_div, le_div_iff₀ hw, ← abs_of_pos hw, ← abs_mul]
  refine le_of_eq_of_le ?_ (hcount.trans_eq ?_)
  · ring_nf
  · ring

/-- **The ray class ideal count of a single class, with an explicit power saving.**  The number
of nonzero integral ideals prime to `𝔪` in the ray class `c` with norm at most `x` is
`rayClassIdealMainTerm 𝔪 * x + O(x ^ (1 - 1 / [K : ℚ]))`. -/
theorem isBigO_rayClassIdealCountingFunction_sub (𝔪 : Modulus K) (c : RayClassGroup 𝔪) :
    (fun x : ℝ => (rayClassIdealCountingFunction 𝔪 c x : ℝ) - rayClassIdealMainTerm 𝔪 * x) =O[atTop]
      fun x : ℝ => x ^ (1 - (finrank ℚ K : ℝ)⁻¹) := by
  -- an ideal `𝔞` of the inverse class and an element of `𝔞` congruent to one modulo `𝔪₀` place
  -- the counted points in one coset of a congruence lattice
  obtain ⟨𝔞, h𝔞, h𝔞0, ξ, hξ𝔞, hξ𝔪⟩ := exists_mem_idealClass_inv_and_sub_one_mem 𝔪 c
  obtain ⟨C, hC⟩ := exists_abs_rayClassIdealCountingFunction_sub_le 𝔪 𝔞 h𝔞 h𝔞0 hξ𝔞 hξ𝔪
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _)]
  exact hC x hx

/-- **The ray class ideal count.**  For every modulus `𝔪` there is a power saving `δ > 0` such
that, in each ray class `c` of `𝔪`, the number of nonzero integral ideals prime to `𝔪` of norm at
most `x` is `rayClassIdealMainTerm 𝔪 * x + O(x ^ (1 - δ))`.  One can take `δ = 1 / [K : ℚ]`;
for that explicit exponent, use `isBigO_rayClassIdealCountingFunction_sub` instead. -/
theorem rayClassIdealCount (𝔪 : Modulus K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : RayClassGroup 𝔪,
      (fun x : ℝ =>
          (rayClassIdealCountingFunction 𝔪 c x : ℝ) - rayClassIdealMainTerm 𝔪 * x) =O[atTop]
        (fun x : ℝ => x ^ (1 - δ)) :=
  ⟨(finrank ℚ K : ℝ)⁻¹, by simp [finrank_pos], isBigO_rayClassIdealCountingFunction_sub 𝔪⟩

end TauCeti.GlobalNumberFields
