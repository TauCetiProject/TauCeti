/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Coprod.Basic
public import TauCeti.GroupTheory.TriangleGroup.Basic
import TauCeti.Algebra.Group.Equiv.Pow
import TauCeti.Data.ZMod.MonoidHomEquiv
import TauCeti.GroupTheory.Coprod.Factors
import TauCeti.GroupTheory.CoprodI.Word

/-!
# Free-product triangle groups `Δ(a, b, 0)`

When the third parameter of the oriented triangle group `Δ(a, b, c)` is `0`, the power relator
`z ^ 0 = 1` is trivial and the product relator `z * y * x = 1` eliminates `z = (y * x)⁻¹`, leaving
no relation between `x` and `y` beyond `x ^ a = 1` and `y ^ b = 1`. Thus `Δ(a, b, 0)` is
isomorphic to the free product `Multiplicative (ZMod a) ∗ Multiplicative (ZMod b)` for all natural
numbers `a` and `b` (including `a = 0` or `b = 0`, where `ZMod 0 = ℤ`).

As a consequence of this decomposition, `x a b 0` and `y a b 0` have exact orders `a` and `b`,
while `z a b 0` has infinite order (`orderOf (z a b 0) = 0`) whenever `a ≠ 1` and `b ≠ 1`.

## Main definitions and results

* `TauCeti.TriangleGroup.equivCoprod`: the isomorphism
  `TriangleGroup a b 0 ≃* Monoid.Coprod (Multiplicative (ZMod a)) (Multiplicative (ZMod b))`.
* `TauCeti.TriangleGroup.orderOf_x_zero`, `TauCeti.TriangleGroup.orderOf_y_zero`,
  `TauCeti.TriangleGroup.not_isOfFinOrder_z_zero`,
  `TauCeti.TriangleGroup.orderOf_z_zero_of_ne_one`,
  `TauCeti.TriangleGroup.orderOf_z_zero_one_left`,
  `TauCeti.TriangleGroup.orderOf_z_zero_one_right`,
  `TauCeti.TriangleGroup.orderOf_z_zero`: exact orders of the three generators.
-/

public section

noncomputable section

namespace TauCeti.TriangleGroup

/-- **Free-product decomposition of `Δ(a, b, 0)`.** For all `a b : ℕ`, the triangle group
`TriangleGroup a b 0` is isomorphic to `Multiplicative (ZMod a) ∗ Multiplicative (ZMod b)`,
sending `x` to `inl (ofAdd 1)` and `y` to `inr (ofAdd 1)`. -/
def equivCoprod (a b : ℕ) :
    TriangleGroup a b 0 ≃* Monoid.Coprod (Multiplicative (ZMod a)) (Multiplicative (ZMod b)) :=
  MonoidHom.toMulEquiv
    (lift (.inl (.ofAdd 1)) (.inr (.ofAdd 1)) (.inr (.ofAdd 1) * .inl (.ofAdd 1))⁻¹
      (by rw [← map_pow, ofAdd_one_pow_modulus_eq_one, map_one])
      (by rw [← map_pow, ofAdd_one_pow_modulus_eq_one, map_one])
      (pow_zero _)
      (by rw [mul_assoc, inv_mul_cancel]))
    (Monoid.Coprod.lift
      ((zmodMonoidHomEquiv a _).symm ⟨x a b 0, x_pow a b 0⟩)
      ((zmodMonoidHomEquiv b _).symm ⟨y a b 0, y_pow a b 0⟩))
    (by ext <;> simp)
    (Monoid.Coprod.hom_ext
      (TauCeti.zmodMonoidHom_ext (by simp))
      (TauCeti.zmodMonoidHom_ext (by simp)))

/-- `equivCoprod` maps the first generator `x a b 0` to `inl (ofAdd 1)`. -/
@[simp]
theorem equivCoprod_x (a b : ℕ) :
    equivCoprod a b (x a b 0) = .inl (.ofAdd 1) := by
  simp [equivCoprod]

/-- `equivCoprod` maps the second generator `y a b 0` to `inr (ofAdd 1)`. -/
@[simp]
theorem equivCoprod_y (a b : ℕ) :
    equivCoprod a b (y a b 0) = .inr (.ofAdd 1) := by
  simp [equivCoprod]

/-- `equivCoprod` maps the third generator `z a b 0` to `inl (ofAdd (-1)) * inr (ofAdd (-1))`. -/
@[simp]
theorem equivCoprod_z (a b : ℕ) :
    equivCoprod a b (z a b 0) = .inl (.ofAdd (-1)) * .inr (.ofAdd (-1)) := by
  simp [equivCoprod]

/-- The inverse of `equivCoprod` sends `inl (ofAdd 1)` to `x a b 0`. -/
@[simp]
theorem equivCoprod_symm_inl_ofAdd_one (a b : ℕ) :
    (equivCoprod a b).symm (.inl (.ofAdd 1)) = x a b 0 := by
  rw [← equivCoprod_x a b, MulEquiv.symm_apply_apply]

/-- The inverse of `equivCoprod` sends `inr (ofAdd 1)` to `y a b 0`. -/
@[simp]
theorem equivCoprod_symm_inr_ofAdd_one (a b : ℕ) :
    (equivCoprod a b).symm (.inr (.ofAdd 1)) = y a b 0 := by
  rw [← equivCoprod_y a b, MulEquiv.symm_apply_apply]

/-- The inverse of `equivCoprod` sends `inl (ofAdd k)` to `x a b 0 ^ k`. -/
@[simp]
theorem equivCoprod_symm_inl_ofAdd_intCast (a b : ℕ) (k : ℤ) :
    (equivCoprod a b).symm (.inl (.ofAdd (k : ZMod a))) = x a b 0 ^ k := by
  simpa using
    zmodMonoidHom_map_ofAdd_intCast ((equivCoprod a b).symm.toMonoidHom.comp Monoid.Coprod.inl) k

/-- The inverse of `equivCoprod` sends `inr (ofAdd k)` to `y a b 0 ^ k`. -/
@[simp]
theorem equivCoprod_symm_inr_ofAdd_intCast (a b : ℕ) (k : ℤ) :
    (equivCoprod a b).symm (.inr (.ofAdd (k : ZMod b))) = y a b 0 ^ k := by
  simpa using
    zmodMonoidHom_map_ofAdd_intCast ((equivCoprod a b).symm.toMonoidHom.comp Monoid.Coprod.inr) k

/-- The first generator `x a b 0` of `Δ(a, b, 0)` has order `a` (for `a = 0`, infinite order). -/
@[simp]
theorem orderOf_x_zero (a b : ℕ) : orderOf (x a b 0) = a := by
  rw [← (equivCoprod a b).orderOf_eq, equivCoprod_x,
    orderOf_injective (Monoid.Coprod.inl :
      Multiplicative (ZMod a) →* Monoid.Coprod (Multiplicative (ZMod a)) (Multiplicative (ZMod b)))
      Monoid.Coprod.inl_injective (.ofAdd 1),
    orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

/-- The second generator `y a b 0` of `Δ(a, b, 0)` has order `b` (for `b = 0`, infinite order). -/
@[simp]
theorem orderOf_y_zero (a b : ℕ) : orderOf (y a b 0) = b := by
  rw [← (equivCoprod a b).orderOf_eq, equivCoprod_y,
    orderOf_injective (Monoid.Coprod.inr :
      Multiplicative (ZMod b) →* Monoid.Coprod (Multiplicative (ZMod a)) (Multiplicative (ZMod b)))
      Monoid.Coprod.inr_injective (.ofAdd 1),
    orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

-- Alternating reduced word `(of x * of y) ^ (n + 1)` in `CoprodI` over `Bool`.
private noncomputable def alternatingWord {M : Bool → Type*} [∀ b, Monoid (M b)]
    (x : M false) (y : M true) (hx : x ≠ 1) (hy : y ≠ 1) :
    (n : ℕ) → {w : Monoid.CoprodI.Word M //
      w.prod = (Monoid.CoprodI.of x * Monoid.CoprodI.of y) ^ (n + 1) ∧
        w.fstIdx = some false}
  | 0 =>
    let wy := Monoid.CoprodI.Word.cons y Monoid.CoprodI.Word.empty
      (by simp [Monoid.CoprodI.Word.fstIdx]) hy
    let wxy := Monoid.CoprodI.Word.cons x wy (by simp [wy]) hx
    ⟨wxy, by simp [wxy, wy], by simp [wxy]⟩
  | n + 1 =>
    let ⟨w, hprod, hfst⟩ := alternatingWord x y hx hy n
    let wy := Monoid.CoprodI.Word.cons y w (by simp [hfst]) hy
    let wxy := Monoid.CoprodI.Word.cons x wy (by simp [wy]) hx
    ⟨wxy, by
      rw [show n + 1 + 1 = (n + 1) + 1 from rfl, pow_succ', ← hprod]
      simp [wxy, wy, mul_assoc],
      by simp [wxy]⟩

/-- When `a ≠ 1` and `b ≠ 1`, the third generator `z a b 0 = (y a b 0 * x a b 0)⁻¹` of
`Δ(a, b, 0)` has infinite order. -/
theorem not_isOfFinOrder_z_zero {a b : ℕ} (ha : a ≠ 1) (hb : b ≠ 1) :
    ¬IsOfFinOrder (z a b 0) := by
  rw [← (equivCoprod a b).isOfFinOrder_iff, equivCoprod_z,
    ← (Monoid.Coprod.equivCoprodI (M := Multiplicative (ZMod a))
      (N := Multiplicative (ZMod b))).isOfFinOrder_iff,
    map_mul, Monoid.Coprod.equivCoprodI_inl, Monoid.Coprod.equivCoprodI_inr,
    isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, hpow⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let x₀ : Monoid.Coprod.Factors (Multiplicative (ZMod a)) (Multiplicative (ZMod b)) false :=
    ULift.up (.ofAdd (-1))
  let y₀ : Monoid.Coprod.Factors (Multiplicative (ZMod a)) (Multiplicative (ZMod b)) true :=
    ULift.up (.ofAdd (-1))
  have hx : x₀ ≠ 1 := fun h => ofAdd_neg_one_ne_one_of_ne_one ha (congrArg ULift.down h)
  have hy : y₀ ≠ 1 := fun h => ofAdd_neg_one_ne_one_of_ne_one hb (congrArg ULift.down h)
  obtain ⟨w, hprod, hfst⟩ := alternatingWord x₀ y₀ hx hy k
  have hempty : w = Monoid.CoprodI.Word.empty :=
    Monoid.CoprodI.Word.prod_injective (by
      simpa [x₀, y₀, Monoid.CoprodI.Word.prod_empty] using hprod.trans hpow)
  rw [hempty] at hfst
  simp [Monoid.CoprodI.Word.fstIdx] at hfst

/-- When `a ≠ 1` and `b ≠ 1`, `orderOf (z a b 0) = 0`. -/
theorem orderOf_z_zero_of_ne_one {a b : ℕ} (ha : a ≠ 1) (hb : b ≠ 1) :
    orderOf (z a b 0) = 0 :=
  orderOf_eq_zero (not_isOfFinOrder_z_zero ha hb)

/-- When `a = 1`, `x 1 b 0 = 1`, so `z 1 b 0 = (y 1 b 0)⁻¹` has order `b`. -/
@[simp]
theorem orderOf_z_zero_one_left (b : ℕ) : orderOf (z 1 b 0) = b := by
  have hx : x 1 b 0 = 1 := by simpa using x_pow 1 b 0
  rw [z_eq, hx, mul_one, orderOf_inv, orderOf_y_zero]

/-- When `b = 1`, `y a 1 0 = 1`, so `z a 1 0 = (x a 1 0)⁻¹` has order `a`. -/
@[simp]
theorem orderOf_z_zero_one_right (a : ℕ) : orderOf (z a 1 0) = a := by
  have hy : y a 1 0 = 1 := by simpa using y_pow a 1 0
  rw [z_eq, hy, one_mul, orderOf_inv, orderOf_x_zero]

/-- Exact order of the third generator `z a b 0` in `Δ(a, b, 0)` for all `a, b : ℕ`. -/
theorem orderOf_z_zero (a b : ℕ) :
    orderOf (z a b 0) = if a = 1 then b else if b = 1 then a else 0 := by
  split_ifs with ha hb
  · subst ha; exact orderOf_z_zero_one_left b
  · subst hb; exact orderOf_z_zero_one_right a
  · exact orderOf_z_zero_of_ne_one ha hb

end TauCeti.TriangleGroup
