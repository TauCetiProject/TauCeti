/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.WithTop.Untop0
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import TauCeti.Algebra.Order.Archimedean.Basic
public import TauCeti.RingTheory.Valuation.AddValuation

/-!
# Equivalent real additive valuations differ by a positive factor

Two additive valuations are equivalent (`AddValuation.IsEquiv`) when they induce the same preorder
on the ring. For additive valuations with values in `WithTop ℝ` this order determines the valuation
only up to scale: `v` and `w` are equivalent exactly when `w = c • v` for some real `c > 0`, read
in `WithTop ℝ` with `⊤` fixed (`AddValuation.isEquiv_iff_exists_map_mul_eq`). So the class of a
real additive valuation does not determine its scale; fixing the scale requires an extra datum,
such as a norm together with a base (`AddValuation.eq_of_norm_eq_rpow`).

This is the additive form of Mathlib's comparison of equivalent real absolute values on a field,
`AbsoluteValue.isEquiv_iff_exists_rpow_eq`, whose rational-approximation argument is adapted here.
It holds on every ring: equivalent valuations compare the integer multiples `p * v x` and
`q * v y` of their values in the same way (`AddValuation.IsEquiv.intCast_mul_untop₀_le_iff`), and
this already forces a common ratio, with no inverses needed
(`TauCeti.mul_eq_mul_of_forall_intCast_mul_le_iff`).

## Main results

* `AddValuation.IsEquiv.intCast_mul_untop₀_le_iff`: equivalent real additive valuations compare
  integer multiples of their values in the same way.
* `AddValuation.isEquiv_iff_exists_map_mul_eq`: two real additive valuations are equivalent if and
  only if one is a positive real multiple of the other.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition 3.3 (equivalent valuations).
-/

public section

namespace AddValuation

variable {R : Type*} [Ring R] {v w : AddValuation R (WithTop ℝ)}

/-- The value of a monomial `x ^ a * y ^ b` in two elements of finite value. -/
private theorem map_pow_mul_pow (u : AddValuation R (WithTop ℝ)) {x y : R} (hx : u x ≠ ⊤)
    (hy : u y ≠ ⊤) (a b : ℕ) :
    u (x ^ a * y ^ b) = ((a * (u x).untop₀ + b * (u y).untop₀ : ℝ) : WithTop ℝ) := by
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hx
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hy
  rw [u.map_mul, u.map_pow, u.map_pow, ← hs, ← ht, WithTop.untop₀_coe, WithTop.untop₀_coe,
    ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul, nsmul_eq_mul]

/-- For elements of finite value, comparing the integer multiples `p * u x` and `q * u y` amounts to
comparing the values of two monomials in `x` and `y`, one for each side after splitting `p` and
`q` into positive and negative parts. -/
private theorem intCast_mul_untop₀_le_iff_map_le_map (u : AddValuation R (WithTop ℝ)) {x y : R}
    (hx : u x ≠ ⊤) (hy : u y ≠ ⊤) (p q : ℤ) :
    p * (u x).untop₀ ≤ q * (u y).untop₀ ↔
      u (x ^ p.toNat * y ^ (-q).toNat) ≤ u (x ^ (-p).toNat * y ^ q.toNat) := by
  rw [map_pow_mul_pow u hx hy, map_pow_mul_pow u hx hy, WithTop.coe_le_coe]
  have hp : ((p.toNat : ℤ) : ℝ) - (((-p).toNat : ℤ) : ℝ) = p := by
    rw [← Int.cast_sub, Int.toNat_sub_toNat_neg]
  have hq : ((q.toNat : ℤ) : ℝ) - (((-q).toNat : ℤ) : ℝ) = q := by
    rw [← Int.cast_sub, Int.toNat_sub_toNat_neg]
  simp only [Int.cast_natCast] at hp hq
  rw [← hp, ← hq]
  constructor <;> intro hle <;> linarith

/-- Equivalent real additive valuations compare integer multiples of their values in the same way,
values `⊤` being read as zero through `WithTop.untop₀`. -/
theorem IsEquiv.intCast_mul_untop₀_le_iff (h : v.IsEquiv w) (x y : R) (p q : ℤ) :
    p * (v x).untop₀ ≤ q * (v y).untop₀ ↔ p * (w x).untop₀ ≤ q * (w y).untop₀ := by
  have htop : ∀ {z : R}, v z = ⊤ → w z = ⊤ := fun {z} hz ↦ by
    rwa [← not_ne_iff, ← h.ne_top, not_ne_iff]
  -- For finite values, both sides compare the values of the same two monomials.
  have hfin : ∀ {x y : R}, v x ≠ ⊤ → v y ≠ ⊤ → ∀ p q : ℤ,
      (p * (v x).untop₀ ≤ q * (v y).untop₀ ↔ p * (w x).untop₀ ≤ q * (w y).untop₀) :=
    fun hx hy p q ↦ by
      rw [intCast_mul_untop₀_le_iff_map_le_map v hx hy,
        intCast_mul_untop₀_le_iff_map_le_map w (h.ne_top.1 hx) (h.ne_top.1 hy)]
      exact isEquiv_iff_val_le_val.1 h
  by_cases hx : v x = ⊤
  · by_cases hy : v y = ⊤
    · simp [hx, hy, htop hx, htop hy]
    -- Both sides compare `0` with a multiple of the finite value at `y`.
    simpa [hx, htop hx] using hfin hy hy 0 q
  by_cases hy : v y = ⊤
  · simpa [hy, htop hy] using hfin hx hx p 0
  exact hfin hx hy p q

/-- Equivalent real additive valuations have the same sign at each element. -/
private theorem IsEquiv.untop₀_nonpos_iff_and_nonneg_iff (h : v.IsEquiv w) (x : R) :
    ((v x).untop₀ ≤ 0 ↔ (w x).untop₀ ≤ 0) ∧ (0 ≤ (v x).untop₀ ↔ 0 ≤ (w x).untop₀) := by
  have h₁ := h.intCast_mul_untop₀_le_iff x x 1 0
  have h₂ := h.intCast_mul_untop₀_le_iff x x (-1) 0
  simp only [Int.cast_one, Int.cast_zero, Int.cast_neg, one_mul, zero_mul, neg_mul,
    neg_nonpos] at h₁ h₂
  exact ⟨h₁, h₂⟩

/-- Equivalent real additive valuations differ by a positive factor, values `⊤` being read as zero
through `WithTop.untop₀`. -/
private theorem IsEquiv.exists_pos_untop₀_eq_mul (h : v.IsEquiv w) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, (w x).untop₀ = c * (v x).untop₀ := by
  have hsign := h.untop₀_nonpos_iff_and_nonneg_iff
  by_cases hnt : ∃ y, (v y).untop₀ ≠ 0
  swap
  · -- If every value of `v` is `0` or `⊤`, the same holds for `w`, and any factor works.
    simp only [not_exists, not_not] at hnt
    refine ⟨1, one_pos, fun x ↦ ?_⟩
    rw [hnt x, mul_zero]
    exact le_antisymm ((hsign x).1.1 (hnt x).le) ((hsign x).2.1 (hnt x).ge)
  -- Otherwise compare every element with a fixed element `y` of finite nonzero value, at which
  -- `v` and `w` have the same strict sign.
  obtain ⟨y, hy0⟩ := hnt
  refine ⟨(w y).untop₀ / (v y).untop₀, ?_, fun x ↦ ?_⟩
  · rcases hy0.lt_or_gt with hv | hv
    · exact div_pos_of_neg_of_neg (lt_of_le_of_ne ((hsign y).1.1 hv.le)
        fun h0 ↦ hv.not_ge ((hsign y).2.2 h0.ge)) hv
    · exact div_pos (lt_of_le_of_ne ((hsign y).2.1 hv.le)
        fun h0 ↦ hv.not_ge ((hsign y).1.2 h0.ge)) hv
  rw [div_mul_eq_mul_div, eq_div_iff hy0]
  exact TauCeti.mul_eq_mul_of_forall_intCast_mul_le_iff (h.intCast_mul_untop₀_le_iff x y)

/-- **Class and scale.** Two real additive valuations are equivalent, that is, induce the same
order on the ring, if and only if one is a positive real multiple of the other. The multiple acts
on finite values and fixes `⊤`. -/
theorem isEquiv_iff_exists_map_mul_eq :
    v.IsEquiv w ↔ ∃ c : ℝ, 0 < c ∧ ∀ x, WithTop.map (c * ·) (v x) = w x := by
  constructor
  · intro h
    obtain ⟨c, hc, hcx⟩ := h.exists_pos_untop₀_eq_mul
    refine ⟨c, hc, fun x ↦ ?_⟩
    by_cases hx : v x = ⊤
    · rw [hx, WithTop.map_top, eq_comm, ← not_ne_iff, ← h.ne_top, hx, not_ne_iff]
    rw [← WithTop.coe_untop₀_of_ne_top hx, ← WithTop.coe_untop₀_of_ne_top (h.ne_top.1 hx),
      WithTop.map_coe, hcx x]
  · rintro ⟨c, hc, hw⟩
    refine isEquiv_iff_val_le_val.2 fun {x y} ↦ ?_
    rw [← hw, ← hw]
    exact ((WithTop.strictMono_map_iff.2 (strictMono_mul_left_of_pos hc)).le_iff_le).symm

end AddValuation
