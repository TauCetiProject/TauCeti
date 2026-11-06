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
-/

public section

open Polynomial

namespace Polynomial

/-- A root of an irreducible real polynomial `p` is a root of every nonconstant divisor of `p`,
since the cofactor of such a divisor is a unit. -/
private theorem aeval_eq_zero_of_dvd_of_irreducible {p q : ℝ[X]} (hp : Irreducible p)
    (hq : ¬IsUnit q) (hqp : q ∣ p) {w : ℂ} (hw : aeval w p = 0) : aeval w q = 0 := by
  obtain ⟨r, rfl⟩ := hqp
  have hr : IsUnit r := (hp.isUnit_or_isUnit rfl).resolve_left hq
  rw [map_mul] at hw
  exact (mul_eq_zero.mp hw).resolve_right ((hr.map (aeval w)).ne_zero)

/-- Two real polynomials with no common complex root, not both zero, are coprime. -/
private theorem isCoprime_of_forall_aeval {p q : ℝ[X]} (h0 : ¬(p = 0 ∧ q = 0))
    (h : ∀ z : ℂ, aeval z p = 0 → aeval z q ≠ 0) : IsCoprime p q := by
  refine EuclideanDomain.isCoprime_of_dvd h0 fun d hd hd0 hdp hdq ↦ ?_
  obtain ⟨z, hz⟩ : ∃ z : ℂ, aeval z d = 0 :=
    IsAlgClosed.exists_aeval_eq_zero ℂ d fun hdeg ↦ hd (isUnit_iff_degree_eq_zero.mpr hdeg)
  exact h z (aeval_eq_zero_of_dvd_aeval_eq_zero hdp hz) (aeval_eq_zero_of_dvd_aeval_eq_zero hdq hz)

end Polynomial

/-- **The complex roots of an irreducible real polynomial have the same real part.** Such a
polynomial is linear with a single real root, or quadratic with a pair of complex conjugate
roots. -/
theorem Irreducible.re_eq_of_aeval_eq_zero {p : ℝ[X]} (hp : Irreducible p) {z w : ℂ}
    (hz : aeval z p = 0) (hw : aeval w p = 0) : z.re = w.re := by
  by_cases him : z.im = 0
  · -- A real root `a` makes `X - C a` a divisor of `p`, so `w` is a root of `X - C a`.
    have hzr : z = (z.re : ℂ) := Complex.ext rfl (by simp [him])
    have hdvd : X - C z.re ∣ p := by
      rw [dvd_iff_isRoot, IsRoot, ← Complex.ofReal_eq_zero, ← Complex.coe_algebraMap,
        ← aeval_algebraMap_apply_eq_algebraMap_eval, Complex.coe_algebraMap, ← hzr, hz]
    have := aeval_eq_zero_of_dvd_of_irreducible hp (not_isUnit_X_sub_C _) hdvd hw
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
    have := aeval_eq_zero_of_dvd_of_irreducible hp hunit
      (quadratic_dvd_of_aeval_eq_zero_im_ne_zero p hz him) hw
    rcases mul_eq_zero.mp ((hQ w).symm.trans this) with h | h
    · rw [sub_eq_zero.mp h]
    · rw [sub_eq_zero.mp h, Complex.conj_re]

namespace Polynomial

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
  · refine isCoprime_of_forall_aeval (fun h ↦ ?_) fun z hz hz' ↦ (hs z hz).not_gt (hu' z hz')
    have h0 := h.2
    rw [Multiset.prod_eq_zero_iff, Multiset.mem_filter] at h0
    exact UniqueFactorizationMonoid.zero_notMem_normalizedFactors p h0.1
  · rw [mul_right_comm, Multiset.prod_filter_mul_prod_filter_not, hu]

end Polynomial
