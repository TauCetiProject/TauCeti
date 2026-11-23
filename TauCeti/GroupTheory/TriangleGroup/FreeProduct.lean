/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Coprod.Basic
public import TauCeti.GroupTheory.TriangleGroup.Basic
import TauCeti.Algebra.Group.Conj
import TauCeti.Algebra.Group.Equiv.Pow
import TauCeti.Data.ZMod.MonoidHomEquiv
import TauCeti.GroupTheory.Abelianization.Coprod
import TauCeti.GroupTheory.Coprod.Torsion

/-!
# Free-product triangle groups `Δ(a, b, 0)`

When the third parameter of the oriented triangle group `Δ(a, b, c)` is `0`, the power relator
`z ^ 0 = 1` is trivial and the product relator `z * y * x = 1` eliminates `z = (y * x)⁻¹`, leaving
no relation between `x` and `y` beyond `x ^ a = 1` and `y ^ b = 1`. Thus `Δ(a, b, 0)` is
isomorphic to the free product `Multiplicative (ZMod a) ∗ Multiplicative (ZMod b)` for all natural
numbers `a` and `b` (including `a = 0` or `b = 0`, where `ZMod 0 = ℤ`).

As consequences of this decomposition:
* `x a b 0` and `y a b 0` have exact orders `a` and `b`, while `z a b 0` has infinite order
  (`orderOf (z a b 0) = 0`) whenever `a ≠ 1` and `b ≠ 1`;
* every element of finite order in `Δ(a, b, 0)` is conjugate to an integer power of `x a b 0` or
  `y a b 0`;
* the abelianization of `Δ(a, b, 0)`, written additively, is `ZMod a × ZMod b` (and `ZMod (a * b)`
  when `a` and `b` are coprime).

## Main definitions and results

* `TauCeti.TriangleGroup.equivCoprod`: the isomorphism
  `TriangleGroup a b 0 ≃* Monoid.Coprod (Multiplicative (ZMod a)) (Multiplicative (ZMod b))`.
* `TauCeti.TriangleGroup.orderOf_x_zero`, `TauCeti.TriangleGroup.orderOf_y_zero`,
  `TauCeti.TriangleGroup.not_isOfFinOrder_z_zero`,
  `TauCeti.TriangleGroup.orderOf_z_zero_of_ne_one`: exact orders of the three generators.
* `TauCeti.TriangleGroup.exists_isConj_x_zpow_or_y_zpow_of_isOfFinOrder`: torsion classification
  in `Δ(a, b, 0)`.
* `TauCeti.TriangleGroup.abelianizationZeroAddEquivProd`,
  `TauCeti.TriangleGroup.abelianizationZeroAddEquivZMod`: additive abelianization of `Δ(a, b, 0)`.
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
  rw [← (equivCoprod a b).orderOf_eq, equivCoprod_x, Monoid.Coprod.orderOf_inl,
    orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

/-- The second generator `y a b 0` of `Δ(a, b, 0)` has order `b` (for `b = 0`, infinite order). -/
@[simp]
theorem orderOf_y_zero (a b : ℕ) : orderOf (y a b 0) = b := by
  rw [← (equivCoprod a b).orderOf_eq, equivCoprod_y, Monoid.Coprod.orderOf_inr,
    orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

/-- When `a ≠ 1` and `b ≠ 1`, the third generator `z a b 0 = (y a b 0 * x a b 0)⁻¹` of
`Δ(a, b, 0)` has infinite order. -/
theorem not_isOfFinOrder_z_zero {a b : ℕ} (ha : a ≠ 1) (hb : b ≠ 1) :
    ¬IsOfFinOrder (z a b 0) := by
  rw [← (equivCoprod a b).isOfFinOrder_iff, equivCoprod_z]
  exact Monoid.Coprod.not_isOfFinOrder_inl_mul_inr
    (ofAdd_neg_one_ne_one_of_ne_one ha) (ofAdd_neg_one_ne_one_of_ne_one hb)

/-- When `a ≠ 1` and `b ≠ 1`, `orderOf (z a b 0) = 0`. -/
theorem orderOf_z_zero_of_ne_one {a b : ℕ} (ha : a ≠ 1) (hb : b ≠ 1) :
    orderOf (z a b 0) = 0 :=
  orderOf_eq_zero (not_isOfFinOrder_z_zero ha hb)

/-- Every element of finite order in `Δ(a, b, 0)` is conjugate to an integer power of `x a b 0` or
of `y a b 0`. -/
theorem exists_isConj_x_zpow_or_y_zpow_of_isOfFinOrder {a b : ℕ} {g : TriangleGroup a b 0}
    (hg : IsOfFinOrder g) :
    (∃ k : ℤ, IsConj g (x a b 0 ^ k) ∧ IsOfFinOrder (x a b 0 ^ k)) ∨
      (∃ k : ℤ, IsConj g (y a b 0 ^ k) ∧ IsOfFinOrder (y a b 0 ^ k)) := by
  have hg' : IsOfFinOrder (equivCoprod a b g) := (equivCoprod a b).isOfFinOrder_iff.mpr hg
  rcases Monoid.Coprod.exists_isConj_inl_or_inr_of_isOfFinOrder hg' with
    ⟨u, hconj, -⟩ | ⟨v, hconj, -⟩
  · obtain ⟨k, rfl⟩ := Multiplicative.mem_zpowers_ofAdd_one u
    have h : IsConj g (x a b 0 ^ k) :=
      (equivCoprod a b).isConj_apply_iff.mp (by simpa using hconj)
    exact Or.inl ⟨k, h, h.isOfFinOrder hg⟩
  · obtain ⟨k, rfl⟩ := Multiplicative.mem_zpowers_ofAdd_one v
    have h : IsConj g (y a b 0 ^ k) :=
      (equivCoprod a b).isConj_apply_iff.mp (by simpa using hconj)
    exact Or.inr ⟨k, h, h.isOfFinOrder hg⟩

/-- **Abelianization of `Δ(a, b, 0)`.** Written additively, the abelianization of
`TriangleGroup a b 0` is canonically isomorphic to `ZMod a × ZMod b`, sending the classes of `x`,
`y`, `z` to `(1, 0)`, `(0, 1)`, `(-1, -1)`. -/
def abelianizationZeroAddEquivProd (a b : ℕ) :
    Additive (Group.Abelianization (TriangleGroup a b 0)) ≃+ ZMod a × ZMod b :=
  ((((equivCoprod a b).abelianizationCongr.trans Group.Abelianization.coprodMulEquiv).trans
    (Group.Abelianization.equivOfComm.symm.prodCongr
      Group.Abelianization.equivOfComm.symm)).trans
    (MulEquiv.prodMultiplicative (ZMod a) (ZMod b)).symm).toAdditive.trans
    (AddEquiv.additiveMultiplicative (ZMod a × ZMod b))

/-- `abelianizationZeroAddEquivProd` maps the class of `x a b 0` to `(1, 0)`. -/
@[simp]
theorem abelianizationZeroAddEquivProd_x (a b : ℕ) :
    abelianizationZeroAddEquivProd a b (.ofMul (.of (x a b 0))) = (1, 0) := by
  simp [abelianizationZeroAddEquivProd, MulEquiv.prodCongr]

/-- `abelianizationZeroAddEquivProd` maps the class of `y a b 0` to `(0, 1)`. -/
@[simp]
theorem abelianizationZeroAddEquivProd_y (a b : ℕ) :
    abelianizationZeroAddEquivProd a b (.ofMul (.of (y a b 0))) = (0, 1) := by
  simp [abelianizationZeroAddEquivProd, MulEquiv.prodCongr]

/-- `abelianizationZeroAddEquivProd` maps the class of `z a b 0` to `(-1, -1)`. -/
@[simp]
theorem abelianizationZeroAddEquivProd_z (a b : ℕ) :
    abelianizationZeroAddEquivProd a b (.ofMul (.of (z a b 0))) = (-1, -1) := by
  rw [z_eq]
  simp

/-- When `a` and `b` are coprime, the additive abelianization of `Δ(a, b, 0)` is isomorphic to
`ZMod (a * b)` via the Chinese remainder theorem. -/
def abelianizationZeroAddEquivZMod {a b : ℕ} (h : a.Coprime b) :
    Additive (Group.Abelianization (TriangleGroup a b 0)) ≃+ ZMod (a * b) :=
  (abelianizationZeroAddEquivProd a b).trans (ZMod.chineseRemainder h).symm.toAddEquiv

/-- `ZMod.chineseRemainder h` carries `abelianizationZeroAddEquivZMod h` back to
`abelianizationZeroAddEquivProd a b`. -/
@[simp]
theorem chineseRemainder_abelianizationZeroAddEquivZMod {a b : ℕ} (h : a.Coprime b)
    (u : Additive (Group.Abelianization (TriangleGroup a b 0))) :
    ZMod.chineseRemainder h (abelianizationZeroAddEquivZMod h u) =
      abelianizationZeroAddEquivProd a b u := by
  simp [abelianizationZeroAddEquivZMod]

end TauCeti.TriangleGroup
