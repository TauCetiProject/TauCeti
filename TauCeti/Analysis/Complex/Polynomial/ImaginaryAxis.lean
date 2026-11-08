/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Real polynomials without roots on the imaginary axis

A real polynomial without complex roots on the imaginary axis splits as a product `p = pₛ * pᵤ`
of two coprime real polynomials, where every complex root of `pₛ` lies in the open left
half-plane and every complex root of `pᵤ` in the open right half-plane
(`Polynomial.exists_isCoprime_mul_eq_of_re_ne_zero`).

This is the algebraic half of the stable/unstable splitting of a hyperbolic linear operator `A`:
applied to an annihilating polynomial of `A`, such as its characteristic polynomial, it decomposes
the space into the kernels of `pₛ(A)` and `pᵤ(A)`, on which the flow of `A` contracts in forward
and in backward time respectively.

The factors are the products of the irreducible factors of `p` whose roots lie in either
half-plane. This is well defined because all complex roots of an irreducible real polynomial have
the same real part (`Irreducible.re_eq_of_aeval_eq_zero`): such a polynomial is either linear,
with a single real root, or quadratic, with a pair of complex conjugate roots.

## Main results

* `Irreducible.re_eq_of_aeval_eq_zero`: the complex roots of an irreducible real polynomial have
  equal real parts.
* `Polynomial.exists_isCoprime_mul_eq_of_re_ne_zero`: the factorization of a real polynomial
  without roots on the imaginary axis into a left half-plane and a right half-plane factor.
* `Polynomial.exists_pos_forall_re_lt_neg_of_re_lt_zero`: the roots of a complex polynomial in
  the open left half-plane stay a positive distance away from the imaginary axis.
-/

public section

open Polynomial

/-- **The complex roots of an irreducible real polynomial have the same real part.** Such a
polynomial is linear with a single real root, or quadratic with a pair of complex conjugate
roots. -/
theorem Irreducible.re_eq_of_aeval_eq_zero {p : ℝ[X]} (hp : Irreducible p) {z w : ℂ}
    (hz : aeval z p = 0) (hw : aeval w p = 0) : z.re = w.re := by
  -- `w` is a root of every nonconstant divisor of `p`, whose cofactor is a unit.
  have hdvd {q : ℝ[X]} (hq : ¬IsUnit q) (hqp : q ∣ p) : aeval w q = 0 := by
    obtain ⟨r, rfl⟩ := hqp
    have hr : IsUnit r := (hp.isUnit_or_isUnit rfl).resolve_left hq
    rw [map_mul] at hw
    exact (mul_eq_zero.mp hw).resolve_right ((hr.map (aeval w)).ne_zero)
  by_cases him : z.im = 0
  · -- A real root `a` makes `X - C a` a divisor of `p`, so `w` is a root of `X - C a`.
    have hzr : z = (z.re : ℂ) := Complex.ext rfl (by simp [him])
    have hXdvd : X - C z.re ∣ p := by
      rw [dvd_iff_isRoot, IsRoot, ← Complex.ofReal_eq_zero, ← Complex.coe_algebraMap,
        ← aeval_algebraMap_apply_eq_algebraMap_eval, Complex.coe_algebraMap, ← hzr, hz]
    have := hdvd (not_isUnit_X_sub_C _) hXdvd
    rw [map_sub, aeval_X, aeval_C, Complex.coe_algebraMap, sub_eq_zero] at this
    simp [this]
  · -- A non-real root `z` makes `X² - 2 Re z X + |z|²` a divisor of `p`, whose complex roots are
    -- `z` and its conjugate.
    have hQ (w : ℂ) : aeval w (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) : ℝ[X]) =
        (w - z) * (w - (starRingEnd ℂ) z) := by
      simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, Complex.coe_algebraMap,
        Complex.ofReal_ofNat]
      have h2 : ((2 * z.re : ℝ) : ℂ) = 2 * z.re := by push_cast; rfl
      linear_combination w * Complex.add_conj z - Complex.mul_conj' z + w * h2
    have hunit : ¬IsUnit (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) : ℝ[X]) := fun hu ↦
      (hu.map (aeval z)).ne_zero (by rw [hQ, sub_self, zero_mul])
    have := hdvd hunit (quadratic_dvd_of_aeval_eq_zero_im_ne_zero p hz him)
    rcases mul_eq_zero.mp ((hQ w).symm.trans this) with h | h
    · rw [sub_eq_zero.mp h]
    · rw [sub_eq_zero.mp h, Complex.conj_re]

namespace Polynomial

/-- **A uniform margin from the imaginary axis.** If every root of a complex polynomial `q` lies
in the open left half-plane, then all of them lie to the left of `-β` for some `β > 0`. -/
theorem exists_pos_forall_re_lt_neg_of_re_lt_zero {q : ℂ[X]}
    (hq : ∀ z : ℂ, q.eval z = 0 → z.re < 0) :
    ∃ β : ℝ, 0 < β ∧ ∀ z : ℂ, q.eval z = 0 → z.re < -β := by
  have hq0 : q ≠ 0 := fun h ↦ lt_irrefl _ (hq 0 (by simp [h]))
  rcases q.roots.toFinset.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun z hz ↦ ?_⟩
    have : z ∈ q.roots.toFinset := by simp [hq0, hz]
    simp [he] at this
  · -- Half the largest real part of a root is a margin.
    obtain ⟨z₀, hz₀, hmax⟩ := q.roots.toFinset.exists_max_image (fun z ↦ z.re) hne
    have hz₀q : q.eval z₀ = 0 := by simpa [hq0] using hz₀
    refine ⟨-z₀.re / 2, by linarith [hq z₀ hz₀q], fun z hz ↦ ?_⟩
    linarith [hq z₀ hz₀q, hmax z (by simp [hq0, hz])]

/-- **Stable–unstable factorization of a real polynomial.** A real polynomial `p` without complex
roots on the imaginary axis is the product `pₛ * pᵤ` of two coprime real polynomials, where every
complex root of `pₛ` has negative real part and every complex root of `pᵤ` has positive real
part. -/
theorem exists_isCoprime_mul_eq_of_re_ne_zero (p : ℝ[X])
    (hp : ∀ z : ℂ, aeval z p = 0 → z.re ≠ 0) :
    ∃ ps pu : ℝ[X], IsCoprime ps pu ∧ ps * pu = p ∧ (∀ z : ℂ, aeval z ps = 0 → z.re < 0) ∧
      ∀ z : ℂ, aeval z pu = 0 → 0 < z.re := by
  classical
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hp 0 (map_zero _) Complex.zero_re
  -- Sort the irreducible factors of `p` by the half-plane containing their roots.
  let S : ℝ[X] → Prop := fun q ↦ ∀ z : ℂ, aeval z q = 0 → z.re < 0
  let F := UniqueFactorizationMonoid.normalizedFactors p
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hp0
  have hroot (s : Multiset ℝ[X]) (z : ℂ) (h : aeval z s.prod = 0) : ∃ q ∈ s, aeval z q = 0 := by
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at h
    exact h
  have hs (z : ℂ) (h : aeval z ((F.filter S).prod * (u : ℝ[X])) = 0) : z.re < 0 := by
    rw [map_mul] at h
    obtain ⟨q, hq, hqz⟩ :=
      hroot _ z ((mul_eq_zero.mp h).resolve_right (u.isUnit.map (aeval z)).ne_zero)
    exact (Multiset.mem_filter.mp hq).2 z hqz
  have hu' (z : ℂ) (h : aeval z (F.filter (¬S ·)).prod = 0) : 0 < z.re := by
    obtain ⟨q, hq, hqz⟩ := hroot _ z h
    obtain ⟨hqF, hqS⟩ := Multiset.mem_filter.mp hq
    obtain ⟨w, hw, hwre⟩ : ∃ w : ℂ, aeval w q = 0 ∧ 0 ≤ w.re := by
      simpa [S] using hqS
    have hzw := (UniqueFactorizationMonoid.irreducible_of_normalized_factor q hqF
      ).re_eq_of_aeval_eq_zero hqz hw
    have hz0 := hp z (aeval_eq_zero_of_dvd_aeval_eq_zero
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hqF) hqz)
    exact lt_of_le_of_ne (hzw ▸ hwre) (Ne.symm hz0)
  refine ⟨(F.filter S).prod * (u : ℝ[X]), (F.filter (¬S ·)).prod, ?_, ?_, hs, hu'⟩
  · refine (isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ _ _).2 fun z ↦ ?_
    by_cases hz : aeval z ((F.filter S).prod * (u : ℝ[X])) = 0
    · exact .inr fun hz' ↦ (hs z hz).not_gt (hu' z hz')
    · exact .inl hz
  · rw [mul_right_comm, Multiset.prod_filter_mul_prod_filter_not, hu]

end Polynomial
