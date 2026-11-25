/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import TauCeti.Algebra.CharP.LocalRing
import Mathlib.Algebra.CharP.Algebra

/-!
# Basic facts about valuative relations

General lemmas about `ValuativeRel` that Mathlib does not yet provide.

## Main results

* `TauCeti.ValuativeRel.not_vle_zero_of_isUnit` : If `f` is a unit, then `¬ f ≤ᵥ 0`.
* `Units.vle_inv_mul_iff_mul_vle` and `Units.inv_mul_vle_iff_vle_mul` : move a unit across a
  valuation comparison; `Units.one_vle_inv_mul_iff` and `Units.inv_mul_vle_one_iff` are their
  special cases with bound `1`.
* `TauCeti.natCast_ne_zero_of_isUnit` and `TauCeti.two_ne_zero_of_isUnit_two`: an integer
  that is a unit in the ring of integers is nonzero in the ambient ring.
* `TauCeti.valuativeExtension_self`: every valuative commutative semiring is a valuative extension
  of itself.
* `TauCeti.valuation_le_one_of_sub_sq_le_one`: if an integral element differs from a square by
  an integral element, then the square root is integral.
* `TauCeti.one_add_pow_ne_zero_of_valuation_lt_one`: a positive power of an element of valuation
  less than one cannot equal `-1`.
* `TauCeti.valueGroup_valuation_eq_top`: the `valueGroup` of the canonical valuation of any ring
  with a valuative relation is `⊤`.
* `TauCeti.valuation_lt_one_iff_mem_image_maximalIdeal`: in a field, the elements of valuation
  less than one are the image of the maximal ideal of the ring of integers.
* `TauCeti.natCast_eq_zero_iff_ringChar_eq_ringChar_residueField_and_dvd`: a positive integer
  vanishes in a field exactly when the field has the characteristic `p` of its residue field and
  `p` divides the integer.

## References

`TauCeti.ValuativeRel.not_vle_zero_of_isUnit` is ported from the open Mathlib pull request
[leanprover-community/mathlib4#38009](https://github.com/leanprover-community/mathlib4/pull/38009);
this copy is deleted in favour of the Mathlib declaration once that pull request reaches the
pinned Mathlib.
-/

public section

section

variable {A : Type*} [Semiring A] [ValuativeRel A]

namespace TauCeti.ValuativeRel

/-- If `f` is a unit, then `¬ f ≤ᵥ 0`. -/
theorem not_vle_zero_of_isUnit {f : A} (hf : IsUnit f) : ¬ f ≤ᵥ (0 : A) := by
  obtain ⟨u, rfl⟩ := hf
  intro h
  simpa [Units.inv_mul, ValuativeRel.not_vle.mpr ValuativeRel.zero_vlt_one] using
    ValuativeRel.mul_vle_mul_right h ↑u⁻¹

end TauCeti.ValuativeRel

namespace Units

/-- For a unit `ϖ`, `a ≤ᵥ ϖ⁻¹ * b` exactly when `ϖ * a ≤ᵥ b`. This is the unit analogue of
Mathlib's `ValuativeRel.vle_div_iff` (stated there for a nonzero divisor in a division ring), in
the shape of the ordered-group lemma `le_inv_mul_iff_mul_le`. -/
@[simp]
theorem vle_inv_mul_iff_mul_vle (ϖ : Aˣ) {a b : A} :
    a ≤ᵥ (ϖ⁻¹ : Aˣ) * b ↔ (ϖ : A) * a ≤ᵥ b := by
  -- multiply `ϖ * a ≤ᵥ b` by `ϖ⁻¹`, which is nonzero for `≤ᵥ`, and cancel `ϖ⁻¹ * ϖ`
  rw [← ValuativeRel.mul_vle_mul_iff_right (y := (ϖ : A) * a)
    (ValuativeRel.not_vle.mp (TauCeti.ValuativeRel.not_vle_zero_of_isUnit ϖ⁻¹.isUnit)),
    ϖ.inv_mul_cancel_left]

/-- For a unit `ϖ`, `ϖ⁻¹ * a ≤ᵥ b` exactly when `a ≤ᵥ ϖ * b`. This is the unit analogue of
Mathlib's `ValuativeRel.div_vle_iff` (stated there for a nonzero divisor in a division ring), in
the shape of the ordered-group lemma `inv_mul_le_iff_le_mul`. -/
@[simp]
theorem inv_mul_vle_iff_vle_mul (ϖ : Aˣ) {a b : A} :
    (ϖ⁻¹ : Aˣ) * a ≤ᵥ b ↔ a ≤ᵥ (ϖ : A) * b := by
  -- the case `ϖ⁻¹` of `Units.vle_inv_mul_iff_mul_vle`, read backwards
  simpa only [inv_inv] using (vle_inv_mul_iff_mul_vle ϖ⁻¹ (a := a) (b := b)).symm

/-- For a unit `ϖ`, `1 ≤ᵥ ϖ⁻¹ * a` exactly when `ϖ ≤ᵥ a`: the case `1` of
`Units.vle_inv_mul_iff_mul_vle`, and the unit analogue of Mathlib's
`ValuativeRel.one_vle_div_iff`. -/
theorem one_vle_inv_mul_iff (ϖ : Aˣ) {a : A} : 1 ≤ᵥ (ϖ⁻¹ : Aˣ) * a ↔ (ϖ : A) ≤ᵥ a := by
  simp

/-- For a unit `ϖ`, `ϖ⁻¹ * a ≤ᵥ 1` exactly when `a ≤ᵥ ϖ`: the case `1` of
`Units.inv_mul_vle_iff_vle_mul`, and the unit analogue of Mathlib's
`ValuativeRel.div_vle_one_iff`. -/
theorem inv_mul_vle_one_iff (ϖ : Aˣ) {a : A} : (ϖ⁻¹ : Aˣ) * a ≤ᵥ 1 ↔ a ≤ᵥ (ϖ : A) := by
  simp

end Units

end

open ValuativeRel

namespace TauCeti

/-- A commutative semiring equipped with a valuative relation is a valuative extension of itself. -/
instance valuativeExtension_self (K : Type*) [CommSemiring K] [ValuativeRel K] :
    ValuativeExtension K K := ⟨by intro a b; simp⟩

variable {K : Type*} [Ring K] [ValuativeRel K]

/-- A natural number that is a unit in the integer ring is nonzero in the ambient ring. -/
theorem natCast_ne_zero_of_isUnit {n : ℕ}
    (hn : IsUnit (n : (valuation K).integer)) : (n : K) ≠ 0 := by
  have hunit : IsUnit (n : K) := by
    simpa only [map_natCast] using hn.map (Subring.subtype ((valuation K).integer))
  intro h
  exact ValuativeRel.not_vle_zero_of_isUnit hunit (by simp [h])

/-- If `2` is a unit in the integer ring, it is nonzero in the ambient ring. -/
theorem two_ne_zero_of_isUnit_two (h2 : IsUnit (2 : (valuation K).integer)) : (2 : K) ≠ 0 := by
  exact_mod_cast natCast_ne_zero_of_isUnit (K := K) (n := 2) (by exact_mod_cast h2)

/-- If an element of valuation at most one differs from a square by an element of valuation at
most one, then the square root also has valuation at most one. -/
theorem valuation_le_one_of_sub_sq_le_one {u ξ : K} (hu : valuation K u ≤ 1)
    (hξ : valuation K (u - ξ ^ 2) ≤ 1) : valuation K ξ ≤ 1 := by
  rw [← pow_le_one_iff two_ne_zero, ← map_pow]
  simpa using (valuation K).map_sub_le hu hξ

/-- A positive power of an element of valuation less than one cannot equal `-1`. -/
theorem one_add_pow_ne_zero_of_valuation_lt_one {x : K} (hx : valuation K x < 1)
    {n : ℕ} (hn : n ≠ 0) : 1 + x ^ n ≠ 0 := by
  have hxpow : valuation K (x ^ n) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le hx hn
  intro h
  simpa [h] using (valuation K).map_one_add_of_lt hxpow

variable (K) in
/-- The value group of the canonical valuation of a ring with a valuative relation is the entire
group of units `(ValueGroupWithZero K)ˣ`. -/
@[simp]
theorem valueGroup_valuation_eq_top :
    MonoidWithZeroHom.valueGroup (valuation K : K →*₀ ValueGroupWithZero K) = ⊤ := by
  refine (Subgroup.eq_top_iff' _).2 fun γ ↦ (MonoidWithZeroHom.mem_valueGroup_iff_of_comm _).2 ?_
  -- write `γ = v a / v b` with `a, b` of positive valuation; then `v b * γ = v a`
  obtain ⟨a, b, hab⟩ := exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq γ
  have hb := valuation_posSubmonoid_ne_zero b
  exact ⟨b, hb, a, by simp [← hab, mul_div_cancel₀ _ hb]⟩

/-- An element of a field has valuation below `1` exactly when it lies in the maximal ideal of the
ring of integers. -/
theorem valuation_lt_one_iff_mem_image_maximalIdeal {K : Type*} [Field K] [ValuativeRel K]
    {x : K} :
    valuation K x < 1 ↔
      x ∈ ((↑) : (valuation K).integer → K) ''
        ↑(IsLocalRing.maximalIdeal (valuation K).integer) := by
  refine ⟨fun hx ↦ ⟨⟨x, (Valuation.mem_integer_iff _ _).2 hx.le⟩,
    (valuation K).mem_maximalIdeal_iff.2 hx, rfl⟩, ?_⟩
  rintro ⟨c, hc, rfl⟩
  exact (valuation K).mem_maximalIdeal_iff.1 hc

/-- A positive integer `n` vanishes in a field `K` with a valuative relation exactly when `K` has
equal characteristic `p`, the characteristic of its residue field, and `p ∣ n`. -/
theorem natCast_eq_zero_iff_ringChar_eq_ringChar_residueField_and_dvd {K : Type*} [Field K]
    [ValuativeRel K] {n : ℕ} (hn : 0 < n) :
    (n : K) = 0 ↔ ringChar K = ringChar (IsLocalRing.ResidueField (valuation K).integer) ∧
      ringChar (IsLocalRing.ResidueField (valuation K).integer) ∣ n := by
  refine ⟨fun h ↦ ?_, fun ⟨h, hdvd⟩ ↦ (ringChar.spec K n).2 (h ▸ hdvd)⟩
  have hdvd := (ringChar.spec K n).1 h
  have hK : ringChar K ≠ 0 := by
    rintro hK
    rw [hK, zero_dvd_iff] at hdvd
    omega
  -- The ring of integers embeds in `K`, so it has the same characteristic.
  have : CharP (valuation K).integer (ringChar K) :=
    (Subring.subtype _).charP Subtype.val_injective _
  have hO : ringChar (valuation K).integer = ringChar K := ringChar.eq _ _
  rw [IsLocalRing.ringChar_residueField_of_prime_ringChar
    (hO ▸ CharP.char_prime_of_ne_zero K hK), hO]
  exact ⟨rfl, hdvd⟩

end TauCeti
