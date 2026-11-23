/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base

import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.LinearCombination

/-!
# `ι`-weights of elements of a coefficient field

Let `E` be a field, `ι : E →+* ℂ` a field embedding and `q` a real number. The *`ι`-weight* of
`α ∈ E` relative to `q` is the real number `w_{ι,q}(α) = 2 log_q ‖ι α‖`, so that
`‖ι α‖ = q ^ (w_{ι,q}(α) / 2)` when `α ≠ 0` and `q > 0`, `q ≠ 1`. An element `α` is *`ι`-pure of
weight `β`* if it is nonzero and its `ι`-weight is `β`. In Deligne's proof of the Weil
conjectures, `E` is an algebraic closure of `ℚ_ℓ` (or a finite extension of `ℚ_ℓ`), `ι` an
abstract field embedding into `ℂ`, which is neither canonical nor continuous, and `q` the size of
the finite base field; the real weights of a Frobenius module are the `ι`-weights of the
eigenvalues of geometric Frobenius.

On nonzero elements the `ι`-weight is a group homomorphism from `Eˣ` to `ℝ`: it adds under
products and changes sign under inverses. Raising both `α` and `q` to the same nonzero power, as
in a finite extension of the base field, does not change it, and it transports along
compositions of field embeddings. A positive rational `q ≠ 1` has weight `2` relative to itself,
so the Tate line, on which geometric Frobenius acts by `q⁻¹`, has weight `-2`; roots of unity
have weight `0`.

The `ι`-weight depends on `ι`: in `ℚ(√2)` the element `1 + √2` has weights `2 log₂ (1 + √2)` and
`-2 log₂ (1 + √2)` relative to `2` at the two real embeddings. An element of integer `ι`-weight
need not be algebraic: an embedding of `ℚ(t)` sending `t` to a transcendental complex number of
absolute value `√2` gives `t` the weight `1` relative to `2`. Both examples close the file.

## Main definitions

* `TauCeti.iotaWeight ι q α`: the `ι`-weight `2 log_q ‖ι α‖` of `α` relative to `q`.
* `TauCeti.IsIotaPure ι q β α`: `α` is nonzero and has `ι`-weight `β` relative to `q`.

## Main results

* `TauCeti.norm_apply_eq_rpow_iotaWeight`: for `α ≠ 0`, `‖ι α‖ = q ^ (w_{ι,q}(α) / 2)`.
* `TauCeti.isIotaPure_iff_norm_apply_eq`: `α` is `ι`-pure of weight `β` exactly when
  `‖ι α‖ = q ^ (β / 2)`.
* `TauCeti.iotaWeight_mul`, `TauCeti.iotaWeight_inv`, `TauCeti.iotaWeight_zpow`: weights add under
  products of nonzero elements, and are negated by inverses.
* `TauCeti.iotaWeight_pow_pow`: replacing `α` and `q` by `α ^ r` and `q ^ r` for `r ≠ 0` does not
  change the weight.
* `TauCeti.iotaWeight_comp`: the weight at `ι ∘ τ` of `α` is the weight at `ι` of `τ α`.
* `TauCeti.isIotaPure_ratCast_self_zpow`: for a positive rational `q ≠ 1`, `q ^ k` is `ι`-pure of
  weight `2 * k` relative to `q`.
* `TauCeti.isIotaPure_zero_of_pow_eq_one`: roots of unity are `ι`-pure of weight `0`.

## References

* P. Deligne, *La conjecture de Weil. II*, Publ. Math. IHÉS 52 (1980), §1.2, (1.2.6) and
  Remarque (1.2.8).
-/

public section

open Polynomial Real

namespace TauCeti

variable {E F : Type*} [Field E] [Field F] (ι : E →+* ℂ) {q β γ : ℝ} {α α' : E}

/-- The *`ι`-weight* of `α` relative to `q`: the real number `2 log_q ‖ι α‖`. When `q > 0`,
`q ≠ 1` and `α ≠ 0`, it is the unique real `w` with `‖ι α‖ = q ^ (w / 2)`. Its value at `α = 0`
is the junk value `0`. -/
noncomputable def iotaWeight (q : ℝ) (α : E) : ℝ :=
  2 * logb q ‖ι α‖

theorem iotaWeight_def (q : ℝ) (α : E) : iotaWeight ι q α = 2 * logb q ‖ι α‖ :=
  (rfl)

/-- An element `α` is *`ι`-pure of weight `β`* relative to `q` if it is nonzero and its
`ι`-weight relative to `q` is `β`. -/
structure IsIotaPure (q β : ℝ) (α : E) : Prop where
  /-- An `ι`-pure element is nonzero. -/
  ne_zero : α ≠ 0
  /-- The `ι`-weight of an `ι`-pure element of weight `β` is `β`. -/
  iotaWeight_eq : iotaWeight ι q α = β

variable {ι}

theorem isIotaPure_iff : IsIotaPure ι q β α ↔ α ≠ 0 ∧ iotaWeight ι q α = β :=
  ⟨fun h ↦ ⟨h.ne_zero, h.iotaWeight_eq⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- A nonzero element is `ι`-pure of its own `ι`-weight. -/
theorem isIotaPure_iotaWeight (hα : α ≠ 0) : IsIotaPure ι q (iotaWeight ι q α) α :=
  ⟨hα, rfl⟩

/-- An element has at most one `ι`-weight. -/
theorem IsIotaPure.unique (h : IsIotaPure ι q β α) (h' : IsIotaPure ι q γ α) : β = γ :=
  h.iotaWeight_eq.symm.trans h'.iotaWeight_eq

/-! ### Weights and absolute values -/

/-- For `q > 0`, `q ≠ 1` and `α ≠ 0`, the absolute value of `ι α` is `q` raised to half the
`ι`-weight of `α`. -/
theorem norm_apply_eq_rpow_iotaWeight (hq₀ : 0 < q) (hq₁ : q ≠ 1) (hα : α ≠ 0) :
    ‖ι α‖ = q ^ (iotaWeight ι q α / 2) := by
  rw [iotaWeight_def, mul_div_cancel_left₀ _ two_ne_zero,
    rpow_logb hq₀ hq₁ (norm_pos_iff.mpr ((map_ne_zero ι).mpr hα))]

/-- For `q > 0`, `q ≠ 1` and `α ≠ 0`, the `ι`-weight of `α` is `β` exactly when
`‖ι α‖ = q ^ (β / 2)`. -/
theorem iotaWeight_eq_iff (hq₀ : 0 < q) (hq₁ : q ≠ 1) (hα : α ≠ 0) :
    iotaWeight ι q α = β ↔ ‖ι α‖ = q ^ (β / 2) := by
  rw [iotaWeight_def, eq_comm (a := ‖ι α‖),
    ← logb_eq_iff_rpow_eq hq₀ hq₁ (norm_pos_iff.mpr ((map_ne_zero ι).mpr hα))]
  constructor <;> intro h <;> linarith

/-- For `q > 0` and `q ≠ 1`, `α` is `ι`-pure of weight `β` relative to `q` exactly when
`‖ι α‖ = q ^ (β / 2)`. The modulus condition forces `α ≠ 0`. -/
theorem isIotaPure_iff_norm_apply_eq (hq₀ : 0 < q) (hq₁ : q ≠ 1) :
    IsIotaPure ι q β α ↔ ‖ι α‖ = q ^ (β / 2) := by
  refine ⟨fun h ↦ (iotaWeight_eq_iff hq₀ hq₁ h.ne_zero).mp h.iotaWeight_eq, fun h ↦ ?_⟩
  have hα : α ≠ 0 := by
    rintro rfl
    rw [map_zero, norm_zero] at h
    exact (rpow_pos_of_pos hq₀ _).ne' h.symm
  exact ⟨hα, (iotaWeight_eq_iff hq₀ hq₁ hα).mpr h⟩

/-! ### The weight homomorphism -/

@[simp]
theorem iotaWeight_zero : iotaWeight ι q 0 = 0 := by
  simp [iotaWeight_def]

@[simp]
theorem iotaWeight_one : iotaWeight ι q 1 = 0 := by
  simp [iotaWeight_def]

/-- The `ι`-weight of a product of nonzero elements is the sum of their weights. -/
theorem iotaWeight_mul (hα : α ≠ 0) (hα' : α' ≠ 0) :
    iotaWeight ι q (α * α') = iotaWeight ι q α + iotaWeight ι q α' := by
  simp only [iotaWeight_def, map_mul, norm_mul]
  rw [logb_mul (norm_ne_zero_iff.mpr ((map_ne_zero ι).mpr hα))
    (norm_ne_zero_iff.mpr ((map_ne_zero ι).mpr hα')), mul_add]

/-- The `ι`-weight of an inverse is the negative of the weight. -/
@[simp]
theorem iotaWeight_inv (α : E) : iotaWeight ι q α⁻¹ = -iotaWeight ι q α := by
  simp [iotaWeight_def, logb_inv]

/-- The `ι`-weight of a quotient of nonzero elements is the difference of their weights. -/
theorem iotaWeight_div (hα : α ≠ 0) (hα' : α' ≠ 0) :
    iotaWeight ι q (α / α') = iotaWeight ι q α - iotaWeight ι q α' := by
  rw [div_eq_mul_inv, iotaWeight_mul hα (inv_ne_zero hα'), iotaWeight_inv, sub_eq_add_neg]

/-- The `ι`-weight of `α ^ n` is `n` times the weight of `α`. -/
@[simp]
theorem iotaWeight_pow (α : E) (n : ℕ) : iotaWeight ι q (α ^ n) = n * iotaWeight ι q α := by
  simp only [iotaWeight_def, map_pow, norm_pow, logb_pow]
  ring

/-- The `ι`-weight of `α ^ n` is `n` times the weight of `α`, for every integer `n`. -/
@[simp]
theorem iotaWeight_zpow (α : E) (n : ℤ) : iotaWeight ι q (α ^ n) = n * iotaWeight ι q α := by
  simp only [iotaWeight_def, map_zpow₀, norm_zpow, logb, log_zpow]
  ring

/-- Raising both `α` and `q` to the same nonzero power `r` does not change the `ι`-weight. This is
the effect on weights of replacing a finite base field with `q` elements by its extension of
degree `r`, which replaces geometric Frobenius by its `r`-th power. -/
theorem iotaWeight_pow_pow (α : E) {r : ℕ} (hr : r ≠ 0) :
    iotaWeight ι (q ^ r) (α ^ r) = iotaWeight ι q α := by
  have hr' : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  simp only [iotaWeight_def, map_pow, norm_pow, logb, log_pow]
  rw [mul_div_mul_left _ _ hr']

/-- The `ι`-weight transports along compositions of field embeddings: the weight of `α` at
`ι ∘ τ` is the weight of `τ α` at `ι`. -/
@[simp]
theorem iotaWeight_comp (τ : F →+* E) (q : ℝ) (α : F) :
    iotaWeight (ι.comp τ) q α = iotaWeight ι q (τ α) :=
  (rfl)

/-! ### Purity under the weight calculus -/

/-- The product of elements `ι`-pure of weights `β` and `γ` is `ι`-pure of weight `β + γ`. -/
theorem IsIotaPure.mul (h : IsIotaPure ι q β α) (h' : IsIotaPure ι q γ α') :
    IsIotaPure ι q (β + γ) (α * α') :=
  ⟨mul_ne_zero h.ne_zero h'.ne_zero, by
    rw [iotaWeight_mul h.ne_zero h'.ne_zero, h.iotaWeight_eq, h'.iotaWeight_eq]⟩

/-- The inverse of an element `ι`-pure of weight `β` is `ι`-pure of weight `-β`. -/
theorem IsIotaPure.inv (h : IsIotaPure ι q β α) : IsIotaPure ι q (-β) α⁻¹ :=
  ⟨inv_ne_zero h.ne_zero, by rw [iotaWeight_inv, h.iotaWeight_eq]⟩

/-- The `n`-th power of an element `ι`-pure of weight `β` is `ι`-pure of weight `n * β`. -/
theorem IsIotaPure.zpow (h : IsIotaPure ι q β α) (n : ℤ) : IsIotaPure ι q (n * β) (α ^ n) :=
  ⟨zpow_ne_zero n h.ne_zero, by rw [iotaWeight_zpow, h.iotaWeight_eq]⟩

/-- The `n`-th power of an element `ι`-pure of weight `β` is `ι`-pure of weight `n * β`. -/
theorem IsIotaPure.pow (h : IsIotaPure ι q β α) (n : ℕ) : IsIotaPure ι q (n * β) (α ^ n) :=
  ⟨pow_ne_zero n h.ne_zero, by rw [iotaWeight_pow, h.iotaWeight_eq]⟩

/-- The quotient of elements `ι`-pure of weights `β` and `γ` is `ι`-pure of weight `β - γ`. -/
theorem IsIotaPure.div (h : IsIotaPure ι q β α) (h' : IsIotaPure ι q γ α') :
    IsIotaPure ι q (β - γ) (α / α') := by
  rw [div_eq_mul_inv, sub_eq_add_neg]
  exact h.mul h'.inv

/-- For `r ≠ 0`, `α ^ r` is `ι`-pure of weight `β` relative to `q ^ r` exactly when `α` is
`ι`-pure of weight `β` relative to `q`. -/
theorem isIotaPure_pow_pow_iff {r : ℕ} (hr : r ≠ 0) :
    IsIotaPure ι (q ^ r) β (α ^ r) ↔ IsIotaPure ι q β α := by
  rw [isIotaPure_iff, isIotaPure_iff, iotaWeight_pow_pow α hr, pow_ne_zero_iff hr]

/-- `α` is `ι ∘ τ`-pure of weight `β` exactly when `τ α` is `ι`-pure of weight `β`. -/
@[simp]
theorem isIotaPure_comp_iff (τ : F →+* E) {α : F} :
    IsIotaPure (ι.comp τ) q β α ↔ IsIotaPure ι q β (τ α) := by
  rw [isIotaPure_iff, isIotaPure_iff, iotaWeight_comp, _root_.map_ne_zero]

/-! ### Rational powers of `q` and roots of unity -/

/-- A positive rational number `q ≠ 1` has `ι`-weight `2` relative to itself. -/
theorem iotaWeight_ratCast_self {q : ℚ} (hq₀ : 0 < q) (hq₁ : q ≠ 1) :
    iotaWeight ι q (q : E) = 2 := by
  have hnorm : ‖ι q‖ = q := by simp [hq₀.le]
  have hq₀' : (0 : ℝ) < q := by exact_mod_cast hq₀
  have hq₁' : (q : ℝ) ≠ 1 := by exact_mod_cast hq₁
  rw [iotaWeight_def, hnorm, logb_self_eq_one_iff.mpr ⟨hq₀'.ne', hq₁', by linarith⟩, mul_one]

/-- For a positive rational number `q ≠ 1`, `q ^ k` is `ι`-pure of weight `2 * k` relative to `q`.
With `k = -1` this is the weight `-2` of the Tate line, on which geometric Frobenius acts by
`q⁻¹`. -/
theorem isIotaPure_ratCast_self_zpow {q : ℚ} (hq₀ : 0 < q) (hq₁ : q ≠ 1) (k : ℤ) :
    IsIotaPure ι q (2 * k) ((q : E) ^ k) := by
  have := ι.charZero
  have hq0 : (q : E) ≠ 0 := Rat.cast_ne_zero.mpr hq₀.ne'
  have h := (isIotaPure_iotaWeight (ι := ι) (q := (q : ℝ)) hq0).zpow k
  rwa [iotaWeight_ratCast_self hq₀ hq₁, mul_comm (k : ℝ)] at h

/-- A root of unity has `ι`-weight `0` for every `ι` and every `q`. -/
theorem isIotaPure_zero_of_pow_eq_one {n : ℕ} (hn : n ≠ 0) (hα : α ^ n = 1) :
    IsIotaPure ι q 0 α := by
  refine ⟨fun h ↦ by simp [h, zero_pow hn] at hα, ?_⟩
  have h1 : ‖ι α‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hα, map_one]) hn
  rw [iotaWeight_def, h1, logb_one, mul_zero]

/-! ### Examples -/

/- The `ι`-weight depends on `ι`. In `ℚ(√2) = ℚ[X] / (X² - 2)`, the two real embeddings give
`1 + √2` the weights `2 log₂ (1 + √2)` and `-2 log₂ (1 + √2)` relative to `2`, because
`(√2 - 1) (√2 + 1) = 1`. -/
example :
    letI : Fact (Irreducible (X ^ 2 - C 2 : ℚ[X])) :=
      ⟨irreducible_X_pow_sub_C_of_prime Nat.prime_two fun b hb ↦ irrational_sqrt_two ⟨|b|, by
        have hb' : (b : ℝ) ^ 2 = 2 := by exact_mod_cast hb
        rw [Rat.cast_abs, ← Real.sqrt_sq_eq_abs, hb']⟩⟩
    ∃ ι₁ ι₂ : AdjoinRoot (X ^ 2 - C 2 : ℚ[X]) →+* ℂ,
      iotaWeight ι₁ 2 (1 + AdjoinRoot.root _) = 2 * logb 2 (1 + √2) ∧
      iotaWeight ι₂ 2 (1 + AdjoinRoot.root _) = -(2 * logb 2 (1 + √2)) := by
  have hs : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt zero_le_two
  have hs' : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast hs
  have hlt := Real.one_lt_sqrt_two
  refine ⟨AdjoinRoot.lift (algebraMap ℚ ℂ) (√2 : ℝ) (by simp [eval₂_sub, hs']),
    AdjoinRoot.lift (algebraMap ℚ ℂ) (-(√2 : ℝ)) (by simp [eval₂_sub, hs']), ?_, ?_⟩
  · have hnorm : ‖(1 + ((√2 : ℝ) : ℂ))‖ = 1 + √2 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_of_nonneg (by positivity)]
    unfold iotaWeight
    rw [map_add, map_one, AdjoinRoot.lift_root, hnorm]
  · -- The key step: `|1 - √2| = √2 - 1 = (1 + √2)⁻¹`.
    have hnorm : ‖1 + -((√2 : ℝ) : ℂ)‖ = (1 + √2)⁻¹ := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_neg, ← Complex.ofReal_add, Complex.norm_real,
        Real.norm_eq_abs, abs_of_neg (by linarith)]
      refine eq_inv_of_mul_eq_one_left ?_
      linear_combination hs
    unfold iotaWeight
    rw [map_add, map_one, AdjoinRoot.lift_root, hnorm, logb_inv, mul_neg]

/- An element of integer `ι`-weight need not be algebraic. For a transcendental complex number
`z` of absolute value `√2`, an embedding of `ℚ(t)` sending `t` to `z` makes `t` pure of weight `1`
relative to `2`, although `t` is transcendental over `ℚ` (Mathlib's `RatFunc.transcendental_X`). -/
example (z : ℂ) (hz : Transcendental ℚ z) (hz2 : ‖z‖ = √2) :
    ∃ ι : RatFunc ℚ →+* ℂ, ι RatFunc.X = z ∧ IsIotaPure ι 2 1 RatFunc.X := by
  have hinj : Function.Injective (aeval z : ℚ[X] →ₐ[ℚ] ℂ) := transcendental_iff_injective.mp hz
  refine ⟨RatFunc.liftRingHom (aeval z).toRingHom
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj), by simp, ?_⟩
  rw [isIotaPure_iff_norm_apply_eq two_pos (by norm_num), RatFunc.liftRingHom_X]
  simp [hz2, Real.sqrt_eq_rpow]

end TauCeti
