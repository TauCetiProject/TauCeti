/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import TauCeti.GroupTheory.FiniteAbelian.SubgroupAverage
import TauCeti.NumberTheory.FrobeniusRiesz.CapReplacement

/-!
# Averaging Frobenius character remainders over translates

In the character expansion of a Frobenius-restricted Riesz sum, the indices contributing
at a thick place are `d * u * s * t⁻¹`, with translate `u`, thick point `s` and top `t`.
After replacing the thick caps by a common cap and dropping the thin terms, averaging over
the translate subgroup keeps only the characters trivial on it. The original Frobenius
normalization then gives the ratio of the thick count to the full index count. This reduces the
estimate to weighted character sums over the tops.

The application and normalization come from L. Alpöge's
`Deduction.CharacterBalanceMoves.core` and `Deduction.CharacterBalanceMoves.one_char`
(`Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean`).
-/

public section

open Finset
open scoped BigOperators ComplexConjugate

namespace Subgroup

variable {G ι κ : Type*} [Group G]

open scoped Classical in
/-- Averaging frozen thick terms retains only the characters trivial on `H`. The factor
`steps.card * b * T.card / J.card` uses the full index set `J`, not the thick translate. -/
theorem expect_sum_sum_expect_ite_mem_image_eq_card_mul_sum_filter (H : Subgroup G) [Fintype H]
    (J tops : Finset G) (T : Finset H) (steps : Finset κ) (C : Finset ι) (χ : ι → G →* ℂ) (d : G)
    (b : ℝ) (F : ι → G → ℂ) (hunit : ∀ i ∈ C, ∀ t ∈ tops, ‖χ i t‖ = 1)
    (hJ : ∀ u : H, ∀ t ∈ tops, ∀ s ∈ T, d * u * s * t⁻¹ ∈ J) :
    (𝔼 u : H, ∑ t ∈ tops, ∑ _k ∈ steps, 𝔼 g ∈ J,
      if g ∈ T.image (fun s : H ↦ d * u * s * t⁻¹) then
        ∑ i ∈ C, conj (χ i g) * ((b : ℂ) * F i t) else 0) =
      ((steps.card : ℂ) * (b : ℂ) * T.card / J.card) *
        ∑ i ∈ C.filter (fun i ↦ (χ i).comp H.subtype = 1),
          conj (χ i d) * ∑ t ∈ tops, χ i t * F i t := by
  classical
  let χc (i : ι) : G →* ℂ := (Complex.conjAe.toRingHom.toMonoidHom).comp (χ i)
  have heval (i : ι) (g : G) : χc i g = conj (χ i g) := rfl
  have hc (i : ι) : (χc i).comp H.subtype = 1 ↔ (χ i).comp H.subtype = 1 := by
    have hinj (z : ℂ) : conj z = 1 ↔ z = 1 := by
      refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
      simpa using congrArg (conj : ℂ → ℂ) h
    simp [MonoidHom.ext_iff, χc, hinj]
  have hnorm (i : ι) (hi : i ∈ C) (t : G) (ht : t ∈ tops) :
      conj (χ i t⁻¹) = χ i t := by
    rw [map_inv, Complex.inv_eq_conj (hunit i hi t ht), Complex.conj_conj]
  have hthick (u : H) (t : G) (ht : t ∈ tops) :
      (𝔼 g ∈ J, if g ∈ T.image (fun s : H ↦ d * u * s * t⁻¹) then
        ∑ i ∈ C, conj (χ i g) * ((b : ℂ) * F i t) else 0) =
        (∑ s ∈ T, ∑ i ∈ C, ((b : ℂ) * F i t) * χc i ((d * t⁻¹) * u * s)) / J.card := by
    rw [expect_eq_sum_div_card, ← sum_filter,
      filter_mem_eq_inter, inter_eq_right.mpr (image_subset_iff.mpr (hJ u t ht)),
      sum_image (fun s _ s' _ h ↦ Subtype.ext (mul_left_cancel (mul_right_cancel h)))]
    congr 1
    refine sum_congr rfl fun s _ ↦ sum_congr rfl fun i _ ↦ ?_
    rw [← heval]
    simp only [map_mul]
    ac_rfl
  have htop (t : G) (ht : t ∈ tops) :
      (𝔼 u : H, ∑ _k ∈ steps, 𝔼 g ∈ J,
        if g ∈ T.image (fun s : H ↦ d * u * s * t⁻¹) then
          ∑ i ∈ C, conj (χ i g) * ((b : ℂ) * F i t) else 0) =
        ((steps.card : ℂ) * (b : ℂ) * T.card / J.card) *
          ∑ i ∈ C.filter (fun i ↦ (χ i).comp H.subtype = 1),
            conj (χ i d) * (χ i t * F i t) := by
    simp_rw [hthick _ t ht, sum_const, nsmul_eq_mul, div_eq_mul_inv, ← mul_expect,
      ← expect_mul, H.expect_sum_sum_mul_apply_mul_eq_card_mul_sum_filter, hc]
    simp only [mul_sum, sum_mul]
    refine sum_congr rfl fun i hi ↦ ?_
    rw [heval, map_mul, map_mul, hnorm i (mem_filter.mp hi).1 t ht]
    ring
  rw [expect_sum_comm, sum_congr rfl htop, ← mul_sum, sum_comm]
  simp only [mul_sum]

open scoped Classical in
/-- Compare the averaged character remainder with the projected thick contribution. The
cap replacement and the subgroup projection use the same full index count, even when the
thick set is empty. This isolates the top sums for comparison with a prescribed coset law. -/
theorem norm_expect_sum_scaledRemainder_sub_card_mul_sum_filter_le [Finite G]
    (H : Subgroup G) [Fintype H] (J tops : Finset G) (T : Finset H) (steps : Finset κ)
    (C : Finset ι) (χ : ι → G →* ℂ) (d : G) (R : ι → ℝ → ℂ)
    (a : G → ℝ) (w : H → G → κ → G → ℝ) {x b b' D X S : ℝ}
    (hJ : ∀ u : H, ∀ t ∈ tops, ∀ s ∈ T, d * u * s * t⁻¹ ∈ J)
    (hx : 3 ≤ x) (hD : 0 ≤ D) (hXb : b' * X ≤ x * b)
    (hscale : ∀ t ∈ tops, |a t / b - x| ≤ 1)
    (hthick : ∀ (u : H) t, t ∈ tops → ∀ k ∈ steps, ∀ s ∈ T,
      w u t k (d * u * s * t⁻¹) ∈ Set.Icc b (b + D))
    (hthin : ∀ (u : H) t, t ∈ tops → ∀ k ∈ steps, ∀ g ∈ J,
      (∀ s ∈ T, d * u * s * t⁻¹ ≠ g) → w u t k g ∈ Set.Icc 0 (2 * b'))
    (hsaving : ∀ i ∈ C, ∀ y ≥ X / 3, ‖R i y‖ ≤ S * y)
    (hvariation : ∀ t ∈ tops, ∀ i ∈ C, ∀ v ∈ Set.Icc b (b + D),
      ‖(v : ℂ) * R i (a t / v) - (b : ℂ) * R i (a t / b)‖ ≤ 3 * (a t / b) * (v - b))
    (hthickCost : (C.card : ℝ) * (3 * (x + 1) * D) ≤ b / x)
    (hthinCost : (C.card : ℝ) * ((x + 1) * b * S) ≤ b / x) :
    ‖(𝔼 u : H, ∑ t ∈ tops, ∑ k ∈ steps, 𝔼 g ∈ J,
        ∑ i ∈ C, conj (χ i g) * ((w u t k g : ℂ) * R i (a t / w u t k g))) -
      ((steps.card : ℂ) * (b : ℂ) * T.card / J.card) *
        ∑ i ∈ C.filter (fun i ↦ (χ i).comp H.subtype = 1),
          conj (χ i d) * ∑ t ∈ tops, χ i t * R i (a t / b)‖ ≤
      (tops.card : ℝ) * steps.card * (b / x) := by
  classical
  -- The frozen average in the cap estimate is normalized by `J`, so it projects exactly.
  rw [← H.expect_sum_sum_expect_ite_mem_image_eq_card_mul_sum_filter J tops T steps C χ d b
    (fun i t ↦ R i (a t / b))
    (fun i _ t _ ↦ ((χ i).isOfFinOrder (isOfFinOrder_of_finite t)).norm_eq_one) hJ]
  refine TauCeti.norm_expect_sum_scaledRemainder_sub_thick_le_of_costs J C (univ : Finset H)
    tops steps (fun (u : H) t ↦ T.image fun s : H ↦ d * u * s * t⁻¹)
    (fun g i ↦ conj (χ i g)) R a w
    hx hD hXb hscale (fun g _ i _ ↦ ?_) (fun u _ t ht k hk g _ hg ↦ ?_)
    (fun u _ t ht k hk g hg hnot ↦ ?_) hsaving hvariation hthickCost hthinCost
  · rw [Complex.norm_conj, ((χ i).isOfFinOrder (isOfFinOrder_of_finite g)).norm_eq_one]
  · obtain ⟨s, hs, rfl⟩ := mem_image.mp hg
    exact hthick u t ht k hk s hs
  · exact hthin u t ht k hk g hg (fun s hs heq ↦ hnot (mem_image.mpr ⟨s, hs, heq⟩))

end Subgroup
