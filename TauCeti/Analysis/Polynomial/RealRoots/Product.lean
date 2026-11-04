/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Products of a real polynomial over the complex roots of another

Let `p` and `f` be real polynomials. The nonreal complex roots of `p` come in conjugate pairs
`z, conj z` of equal multiplicity, and such a pair contributes
`f(z) f(conj z) = |f(z)|² ≥ 0` to the product of `f` over the complex roots of `p`. Hence that
product is a nonnegative real multiple of the product of `f` over the real roots of `p`, all roots
counted with multiplicity. In particular the two products have the same sign whenever the first is
nonzero.

This is the polynomial input for reading off the sign of `det (f(A))` for a real square matrix `A`
from its real eigenvalues alone.

## Main results

* `Polynomial.exists_prod_aroots_eq_mul_prod_roots`: for some real `c ≥ 0`,
  `∏_{z ∈ p.aroots ℂ} f(z) = c ∏_{x ∈ p.roots} f(x)`.
-/

public section

open ComplexConjugate

namespace Polynomial

/-- The product of a real polynomial `f` over the complex roots of a real polynomial `p` is a
nonnegative real multiple of its product over the real roots of `p`, all roots counted with
multiplicity. The nonnegative factor is the contribution `|f(z)|²` of the conjugate pairs of
nonreal roots. -/
theorem exists_prod_aroots_eq_mul_prod_roots (p f : ℝ[X]) :
    ∃ c : ℝ, 0 ≤ c ∧
      ((p.aroots ℂ).map fun z ↦ aeval z f).prod = ((c * (p.roots.map f.eval).prod : ℝ) : ℂ) := by
  induction hn : (p.aroots ℂ).card using Nat.strong_induction_on generalizing p with
  | _ n ih =>
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨1, zero_le_one, by simp⟩
  by_cases hr : ∃ r : ℝ, p.IsRoot r
  · -- Split off a real linear factor `X - r`.
    obtain ⟨r, hr⟩ := hr
    obtain ⟨q, rfl⟩ := dvd_iff_isRoot.mpr hr
    have hroots := aroots_mul (S := ℂ) hp
    rw [aroots_X_sub_C] at hroots
    obtain ⟨c, hc, h⟩ := ih _ (by simp [← hn, hroots]) q rfl
    refine ⟨c, hc, ?_⟩
    rw [hroots, roots_mul hp, roots_X_sub_C, Multiset.map_add, Multiset.prod_add, h,
      Multiset.map_add, Multiset.prod_add]
    rw [Multiset.map_singleton, Multiset.prod_singleton, Multiset.map_singleton,
      Multiset.prod_singleton, aeval_algebraMap_apply_eq_algebraMap_eval, Complex.coe_algebraMap]
    push_cast
    ring
  by_cases hz : ∃ z : ℂ, aeval z p = 0
  · -- Split off the real quadratic factor `(X - conj z) (X - z)` of a nonreal root `z`.
    obtain ⟨z, hz⟩ := hz
    have him : z.im ≠ 0 := by
      intro him
      refine hr ⟨z.re, ?_⟩
      have : (z.re : ℂ) = z := Complex.ext rfl (by simp [him])
      rw [← this, ← Complex.coe_algebraMap, aeval_algebraMap_apply_eq_algebraMap_eval] at hz
      simpa using hz
    obtain ⟨q, rfl⟩ := quadratic_dvd_of_aeval_eq_zero_im_ne_zero p hz him
    set Q : ℝ[X] := X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)
    have hQ : Q.map (algebraMap ℝ ℂ) = (X - C (conj z)) * (X - C z) := by
      have : Q.map (algebraMap ℝ ℂ) = X ^ 2 - C (↑(2 * z.re) : ℂ) * X + C (‖z‖ ^ 2 : ℂ) := by
        simp [Q]
      rw [this, ← Complex.add_conj, map_add, ← Complex.mul_conj', map_mul]
      ring
    have hQroots : Q.aroots ℂ = {conj z, z} := by
      rw [aroots_def, hQ, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
        roots_X_sub_C, roots_X_sub_C]
      rfl
    -- A real root of `Q` would be a real root of `p = Q q`.
    have hQreal : Q.roots = 0 := Multiset.eq_zero_of_forall_notMem fun x hx ↦
      hr ⟨x, by simp [(isRoot_of_mem_roots hx).eq_zero]⟩
    have hroots := aroots_mul (S := ℂ) hp
    rw [hQroots] at hroots
    obtain ⟨c, hc, h⟩ := ih _ (by simp [← hn, hroots]) q rfl
    refine ⟨Complex.normSq (aeval z f) * c, mul_nonneg (Complex.normSq_nonneg _) hc, ?_⟩
    rw [hroots, roots_mul hp, hQreal, zero_add, Multiset.map_add, Multiset.prod_add, h]
    simp [aeval_conj, Complex.normSq_eq_conj_mul_self]
    ring
  · -- With no complex root at all, both products are empty.
    refine ⟨1, zero_le_one, ?_⟩
    rw [Multiset.eq_zero_of_forall_notMem fun z hz' ↦ hz ⟨z, (mem_aroots.1 hz').2⟩,
      Multiset.eq_zero_of_forall_notMem fun x hx ↦ hr ⟨x, (mem_roots hp).1 hx⟩]
    simp

end Polynomial
