/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Splitting real polynomials along the imaginary axis

A real polynomial `f` none of whose complex roots lies on the imaginary axis factors over `ℝ` as
`f = p * q`, where every complex root of `p` lies in the open left half-plane and every complex
root of `q` in the open right half-plane
(`Polynomial.exists_eq_mul_forall_re_neg_forall_re_pos`). Applied to the minimal polynomial of a
hyperbolic linear operator, the two factors cut out its stable and unstable subspaces.

The factorization is built one root at a time: a real polynomial vanishing at `z` is divisible by
a real factor of positive degree whose complex roots all have the real part of `z`, namely
`X - z` when `z` is real and the quadratic `(X - z) (X - conj z)` otherwise
(`Polynomial.exists_dvd_forall_aeval_eq_zero_re_eq`).
-/

public section

open ComplexConjugate

namespace Polynomial

/-- A real polynomial vanishing at `z : ℂ` has a factor of positive degree all of whose complex
roots have the same real part as `z`. -/
theorem exists_dvd_forall_aeval_eq_zero_re_eq {f : ℝ[X]} {z : ℂ} (hz : aeval z f = 0) :
    ∃ m : ℝ[X], m ∣ f ∧ 0 < m.natDegree ∧ ∀ w : ℂ, aeval w m = 0 → w.re = z.re := by
  by_cases him : z.im = 0
  · refine ⟨X - C z.re, ?_, by rw [natDegree_X_sub_C]; exact one_pos, fun w hw ↦ ?_⟩
    · have hzr : z = algebraMap ℝ ℂ z.re := Complex.ext rfl (by simp [him])
      rw [hzr, aeval_algebraMap_apply_eq_algebraMap_eval, map_eq_zero] at hz
      exact dvd_iff_isRoot.mpr hz
    · simp only [map_sub, aeval_X, aeval_C, sub_eq_zero] at hw
      rw [hw, Complex.coe_algebraMap, Complex.ofReal_re]
  · refine ⟨_, quadratic_dvd_of_aeval_eq_zero_im_ne_zero f hz him, ?_, fun w hw ↦ ?_⟩
    · have : (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)).natDegree = 2 := by compute_degree!
      lia
    · -- The quadratic factor is `(X - z) (X - conj z)`, so `w` is `z` or `conj z`.
      have h : (w - z) * (w - conj z) = 0 := by
        simp only [map_add, map_sub, map_pow, aeval_X, map_mul, aeval_C] at hw
        have h1 := Complex.add_conj z
        have h2 := Complex.mul_conj' z
        push_cast at hw h1
        linear_combination hw - w * h1 + h2
      rcases mul_eq_zero.mp h with h | h
      · rw [sub_eq_zero.mp h]
      · rw [sub_eq_zero.mp h, Complex.conj_re]

/-- **Splitting along the imaginary axis.** A real polynomial without complex roots on the
imaginary axis is a product `p * q` of real polynomials whose complex roots lie in the open left
half-plane for `p` and in the open right half-plane for `q`. -/
theorem exists_eq_mul_forall_re_neg_forall_re_pos {f : ℝ[X]}
    (hf : ∀ z : ℂ, aeval z f = 0 → z.re ≠ 0) :
    ∃ p q : ℝ[X], f = p * q ∧ (∀ z : ℂ, aeval z p = 0 → z.re < 0) ∧
      ∀ z : ℂ, aeval z q = 0 → 0 < z.re := by
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
  | _ n ih =>
  by_cases hroot : ∃ z : ℂ, aeval z f = 0
  swap
  · simp only [not_exists] at hroot
    exact ⟨f, 1, (mul_one f).symm, fun z hz ↦ absurd hz (hroot z), fun z hz ↦ by simp at hz⟩
  obtain ⟨z, hz⟩ := hroot
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf 0 (map_zero _) Complex.zero_re
  -- Split off a factor `m` whose roots share the real part of `z`, and recurse on the cofactor.
  obtain ⟨m, ⟨g, rfl⟩, hm, hmre⟩ := exists_dvd_forall_aeval_eq_zero_re_eq hz
  have hdeg : g.natDegree < n := by
    rw [← hn, natDegree_mul (left_ne_zero_of_mul hf0) (right_ne_zero_of_mul hf0)]
    lia
  obtain ⟨p, q, rfl, hp, hq⟩ := ih _ hdeg (f := g) (fun w hw ↦ hf w (by simp [hw])) rfl
  rcases (hf z hz).lt_or_gt with hneg | hpos
  · refine ⟨m * p, q, (mul_assoc _ _ _).symm, fun w hw ↦ ?_, hq⟩
    rcases mul_eq_zero.mp ((map_mul _ _ _).symm.trans hw) with hw | hw
    · exact (hmre w hw).trans_lt hneg
    · exact hp w hw
  · refine ⟨p, m * q, mul_left_comm _ _ _, hp, fun w hw ↦ ?_⟩
    rcases mul_eq_zero.mp ((map_mul _ _ _).symm.trans hw) with hw | hw
    · exact hpos.trans_eq (hmre w hw).symm
    · exact hq w hw

end Polynomial
