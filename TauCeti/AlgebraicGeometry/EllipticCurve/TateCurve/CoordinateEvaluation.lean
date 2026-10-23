/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.AnnulusEvaluation
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Coordinates
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Specialization
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import TauCeti.Analysis.SpecificLimits.Normed
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Comparing formal and analytic Tate coordinates

On the strict annulus `‖q‖ < ‖u‖ < 1`, the bilateral Tate coordinate series agree with evaluation
of the integral bivariate formal coordinates at `u` and `v = q / u`. Consequently the analytic
coordinates satisfy the specialized Tate equation. The comparison regroups the convergent
geometric expansions along the monomials `u^(d(n+1)) v^(dn)` and their transposes.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, §V.3.
* J. Tate, *A review of non-Archimedean elliptic functions* (1995).
-/

public section

open PowerSeries ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace TauCeti

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

private def positiveRay (c : ℕ → ℤ) (p : ℕ × ℕ) : ℤ :=
  if p.2 < p.1 ∧ p.1 - p.2 ∣ p.2 then c (p.1 - p.2) else 0

private def rayIndex (p : ℕ × ℕ) : ℕ × ℕ :=
  ((p.1 + 1) * (p.2 + 1), p.1 * (p.2 + 1))

private theorem rayIndex_injective : Function.Injective rayIndex := by
  intro p r h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [rayIndex] at h₁ h₂
  have hd : p.2 = r.2 := by nlinarith
  have hn : p.1 = r.1 := by rw [← hd] at h₂; nlinarith
  exact Prod.ext hn hd

private theorem mem_range_rayIndex (p : ℕ × ℕ) :
    p ∈ Set.range rayIndex ↔ p.2 < p.1 ∧ p.1 - p.2 ∣ p.2 := by
  constructor
  · rintro ⟨⟨n, d⟩, rfl⟩
    simp only [rayIndex]
    have h : (n + 1) * (d + 1) - n * (d + 1) = d + 1 := by simp [Nat.add_mul]
    exact ⟨by nlinarith, by rw [h]; exact dvd_mul_left _ _⟩
  · rintro ⟨hlt, n, hn⟩
    refine ⟨(n, p.1 - p.2 - 1), ?_⟩
    have hd : p.1 - p.2 - 1 + 1 = p.1 - p.2 := by omega
    apply Prod.ext <;> simp only [rayIndex, hd]
    all_goals nlinarith [Nat.sub_add_cancel hlt.le]

private theorem tsum_positiveRay (c : ℕ → ℤ) (u v : K) (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) :
    (∑' p : ℕ × ℕ, (positiveRay c p : K) * u ^ p.1 * v ^ p.2) =
      ∑' n : ℕ, ∑' d : ℕ, (c (d + 1) : K) * (u ^ (n + 1) * v ^ n) ^ (d + 1) := by
  have hs := (summable_norm_intCast_mul_pow_mul_pow (K := K) (positiveRay c) hu hv).of_norm
  have hr := rayIndex_injective.tsum_eq (f := fun p : ℕ × ℕ ↦
    (positiveRay c p : K) * u ^ p.1 * v ^ p.2) (by
      intro p hp
      by_contra h
      have := (mem_range_rayIndex p).not.mp h
      simp [positiveRay, this] at hp)
  rw [← hr]
  have hp := (hs.comp_injective rayIndex_injective).tsum_prod
  simp only [Function.comp_apply] at hp
  rw [hp]
  apply tsum_congr₂
  intro n d
  have hd : (n + 1) * (d + 1) - n * (d + 1) = d + 1 := by simp [Nat.add_mul]
  have hlt : n * (d + 1) < (n + 1) * (d + 1) := by nlinarith
  simp only [rayIndex, positiveRay, hlt, hd, dvd_mul_left, and_self, ite_true]
  rw [mul_pow, ← pow_mul, ← pow_mul]
  ring

private theorem eval_tate_expansion (f : ℤ⟦X⟧⟦X⟧) (c₀ cp cm : ℕ → ℤ)
    (hc : ∀ a b, coeff a (coeff b f) =
      (if a = b then c₀ a else 0) + positiveRay cp (a, b) + positiveRay cm (b, a))
    (u v : K) (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) :
    evalIntBivariateSeries u hu v hv f =
      (∑' d : ℕ, (c₀ d : K) * (u * v) ^ d) +
      (∑' n : ℕ, ∑' d : ℕ, (cp (d + 1) : K) * (u ^ (n + 1) * v ^ n) ^ (d + 1)) +
      (∑' n : ℕ, ∑' d : ℕ, (cm (d + 1) : K) * (v ^ (n + 1) * u ^ n) ^ (d + 1)) := by
  let diag : ℕ × ℕ → ℤ := fun p ↦ if p.1 = p.2 then c₀ p.1 else 0
  have hd := (summable_norm_intCast_mul_pow_mul_pow (K := K) diag hu hv).of_norm
  have hp := (summable_norm_intCast_mul_pow_mul_pow (K := K) (positiveRay cp) hu hv).of_norm
  have hm := (summable_norm_intCast_mul_pow_mul_pow (K := K)
    (fun p ↦ positiveRay cm p.swap) hu hv).of_norm
  have he : evalIntBivariateSeries u hu v hv f =
      ∑' p : ℕ × ℕ, (((diag p : K) * u ^ p.1 * v ^ p.2 +
        (positiveRay cp p : K) * u ^ p.1 * v ^ p.2) +
        (positiveRay cm p.swap : K) * u ^ p.1 * v ^ p.2) := by
    rw [evalIntBivariateSeries_eq_tsum]
    apply tsum_congr
    rintro ⟨a, b⟩
    rw [hc]
    simp only [Int.cast_add, diag, Prod.swap_prod_mk]
    ring
  rw [he, (hd.add hp).tsum_add hm, hd.tsum_add hp, tsum_positiveRay cp u v hu hv]
  have hdiag : (∑' p : ℕ × ℕ, (diag p : K) * u ^ p.1 * v ^ p.2) =
      ∑' d : ℕ, (c₀ d : K) * (u * v) ^ d := by
    rw [hd.tsum_prod]
    apply tsum_congr
    intro a
    rw [tsum_eq_single a]
    · simp [diag, mul_pow, mul_assoc]
    · intro b hb
      simp [diag, Ne.symm hb]
  have hminus : (∑' p : ℕ × ℕ, (positiveRay cm p.swap : K) * u ^ p.1 * v ^ p.2) =
      ∑' p : ℕ × ℕ, (positiveRay cm p : K) * v ^ p.1 * u ^ p.2 := by
    rw [← (Equiv.prodComm ℕ ℕ).tsum_eq]
    apply tsum_congr
    intro p
    simp only [Equiv.prodComm_apply, Prod.swap_swap, Prod.fst_swap, Prod.snd_swap]
    ring
  rw [hdiag, hminus, tsum_positiveRay cm v u hv hu]

private theorem eval_tateFormalX_expansion (u v : K) (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) :
    evalIntBivariateSeries u hu v hv (tateFormalX ℤ) =
      -2 * divisorSumAt 1 (u * v) +
      (∑' n : ℕ, (u ^ (n + 1) * v ^ n) / (1 - u ^ (n + 1) * v ^ n) ^ 2) +
      (∑' n : ℕ, (v ^ (n + 1) * u ^ n) / (1 - v ^ (n + 1) * u ^ n) ^ 2) := by
  have hc (a b : ℕ) : coeff a (coeff b (tateFormalX ℤ)) =
      (if a = b then -2 * (σ 1 a : ℤ) else 0) +
        positiveRay (fun d ↦ (d : ℤ)) (a, b) + positiveRay (fun d ↦ (d : ℤ)) (b, a) := by
    rcases lt_trichotomy a b with h | rfl | h
    · simp [positiveRay, coeff_coeff_tateFormalX, h.ne, h,
        not_lt_of_gt h, Nat.dist_eq_sub_of_le h.le, min_eq_left h.le]
    · simp [positiveRay]
    · simp [positiveRay, coeff_coeff_tateFormalX, h.ne', h,
        not_lt_of_gt h, Nat.dist_eq_sub_of_le_right h.le, min_eq_right h.le]
  have he := eval_tate_expansion (tateFormalX ℤ) (fun d ↦ -2 * (σ 1 d : ℤ))
    (fun d ↦ (d : ℤ)) (fun d ↦ (d : ℤ)) hc u v hu hv
  simp only [Int.cast_natCast] at he
  simp_rw [tsum_natCast_succ_mul_pow_succ _ (norm_pow_succ_mul_pow_lt_one u v hu hv.le _),
    tsum_natCast_succ_mul_pow_succ _ (norm_pow_succ_mul_pow_lt_one v u hv hu.le _)] at he
  rw [he]
  congr 2
  simp [divisorSumAt_def, ← tsum_mul_left, mul_assoc]

private theorem eval_tateFormalY_expansion (u v : K) (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) :
    evalIntBivariateSeries u hu v hv (tateFormalY ℤ) =
      divisorSumAt 1 (u * v) +
      (∑' n : ℕ, (u ^ (n + 1) * v ^ n) ^ 2 / (1 - u ^ (n + 1) * v ^ n) ^ 3) +
      (∑' n : ℕ, -(v ^ (n + 1) * u ^ n) / (1 - v ^ (n + 1) * u ^ n) ^ 3) := by
  have hc (a b : ℕ) : coeff a (coeff b (tateFormalY ℤ)) =
      (if a = b then (σ 1 a : ℤ) else 0) +
        positiveRay (fun d ↦ (d.choose 2 : ℤ)) (a, b) +
        positiveRay (fun d ↦ -((d + 1).choose 2 : ℤ)) (b, a) := by
    rcases lt_trichotomy a b with h | rfl | h
    · simp [positiveRay, coeff_coeff_tateFormalY, h.ne, h,
        not_lt_of_gt h, Nat.dist_eq_sub_of_le h.le, min_eq_left h.le]
    · simp [positiveRay]
    · simp [positiveRay, coeff_coeff_tateFormalY, h.ne', h,
        not_lt_of_gt h, Nat.dist_eq_sub_of_le_right h.le, min_eq_right h.le]
  have he := eval_tate_expansion (tateFormalY ℤ) (fun d ↦ (σ 1 d : ℤ))
    (fun d ↦ (d.choose 2 : ℤ)) (fun d ↦ -((d + 1).choose 2 : ℤ)) hc u v hu hv
  simp only [Int.cast_neg, Int.cast_natCast] at he
  simp_rw [tsum_choose_two_mul_pow_succ _ (norm_pow_succ_mul_pow_lt_one u v hu hv.le _),
    tsum_neg_choose_two_mul_pow_succ _ (norm_pow_succ_mul_pow_lt_one v u hv hu.le _)] at he
  simpa only [divisorSumAt_def, Int.cast_natCast] using he

/-- Evaluation of the formal first Tate coordinate agrees with the bilateral coordinate when
both `u` and `v` have norm less than one and the Tate parameter is `u v`. -/
@[simp]
theorem evalIntBivariateSeries_tateFormalX (u v : Kˣ)
    (hu : ‖(u : K)‖ < 1) (hv : ‖(v : K)‖ < 1) :
    evalIntBivariateSeries (u : K) hu (v : K) hv (tateFormalX ℤ) =
      tateUniformizationX (u * v) u := by
  have hq : ‖((u * v : Kˣ) : K)‖ < 1 := norm_mul_lt_one _ _ hu hv
  have hs := summable_tateUniformizationX (u * v) hq u
  have hp : Summable (fun n : ℕ ↦ (u : K) ^ (n + 1) * (v : K) ^ n /
      (1 - (u : K) ^ (n + 1) * (v : K) ^ n) ^ 2) := by
    simpa only [Function.comp_def, Units.val_mul_zpow_natCast_mul] using
      hs.comp_injective Nat.cast_injective
  have hn : Function.Injective (fun n : ℕ ↦ -((n : ℤ) + 1)) := by
    intro a b h
    exact Nat.cast_injective (add_right_cancel (neg_injective h))
  have hm : Summable (fun n : ℕ ↦ (v : K) ^ (n + 1) * (u : K) ^ n /
      (1 - (v : K) ^ (n + 1) * (u : K) ^ n) ^ 2) := by
    simpa only [Function.comp_def, Units.val_mul_zpow_neg_natCast_succ_mul,
      inv_div_one_sub_inv_sq]
      using hs.comp_injective hn
  rw [eval_tateFormalX_expansion _ _ hu hv, tateUniformizationX_def,
    ← tsum_nat_add_neg_add_one hs]
  simp_rw [Units.val_mul_zpow_natCast_mul, Units.val_mul_zpow_neg_natCast_succ_mul,
    inv_div_one_sub_inv_sq]
  rw [hp.tsum_add hm, Units.val_mul]
  ring

/-- Evaluation of the formal second Tate coordinate agrees with the bilateral coordinate when
both `u` and `v` have norm less than one and the Tate parameter is `u v`. -/
@[simp]
theorem evalIntBivariateSeries_tateFormalY (u v : Kˣ)
    (hu : ‖(u : K)‖ < 1) (hv : ‖(v : K)‖ < 1) :
    evalIntBivariateSeries (u : K) hu (v : K) hv (tateFormalY ℤ) =
      tateUniformizationY (u * v) u := by
  have hq : ‖((u * v : Kˣ) : K)‖ < 1 := norm_mul_lt_one _ _ hu hv
  have hs := summable_tateUniformizationY (u * v) hq u
  have hp : Summable (fun n : ℕ ↦ ((u : K) ^ (n + 1) * (v : K) ^ n) ^ 2 /
      (1 - (u : K) ^ (n + 1) * (v : K) ^ n) ^ 3) := by
    simpa only [Function.comp_def, Units.val_mul_zpow_natCast_mul] using
      hs.comp_injective Nat.cast_injective
  have hn : Function.Injective (fun n : ℕ ↦ -((n : ℤ) + 1)) := by
    intro a b h
    exact Nat.cast_injective (add_right_cancel (neg_injective h))
  have hm : Summable (fun n : ℕ ↦ -((v : K) ^ (n + 1) * (u : K) ^ n) /
      (1 - (v : K) ^ (n + 1) * (u : K) ^ n) ^ 3) := by
    simpa only [Function.comp_def, Units.val_mul_zpow_neg_natCast_succ_mul,
      inv_sq_div_one_sub_inv_cube]
      using hs.comp_injective hn
  rw [eval_tateFormalY_expansion _ _ hu hv, tateUniformizationY_def,
    ← tsum_nat_add_neg_add_one hs]
  simp_rw [Units.val_mul_zpow_natCast_mul, Units.val_mul_zpow_neg_natCast_succ_mul,
    inv_sq_div_one_sub_inv_cube]
  rw [hp.tsum_add hm, Units.val_mul]
  ring

/-- On the strict annulus `‖q‖ < ‖u‖ < 1`, the bilateral Tate coordinates satisfy the equation of
`tateCurveAt q`. No assumption on the characteristic or discreteness of the norm is needed. -/
theorem equation_tateUniformizationX_tateUniformizationY (q u : Kˣ)
    (hqu : ‖(q : K)‖ < ‖(u : K)‖) (hu : ‖(u : K)‖ < 1) :
    (tateCurveAt q (hqu.trans hu)).toAffine.Equation
      (tateUniformizationX q u) (tateUniformizationY q u) := by
  have hv : ‖((q / u : Kˣ) : K)‖ < 1 := by
    rw [Units.val_div_eq_div_val, norm_div, div_lt_one (norm_pos_iff.mpr u.ne_zero)]
    exact hqu
  have huv : u * (q / u) = q := by simp [div_eq_mul_inv, mul_left_comm]
  have h := equation_eval_tateFormalX_tateFormalY (u : K) hu (q / u : Kˣ) hv
  rw [evalIntBivariateSeries_tateFormalX, evalIntBivariateSeries_tateFormalY] at h
  simpa only [← Units.val_mul, huv, tateCurveAt_def] using h

end TauCeti

end
