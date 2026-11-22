/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.DualitySignature.Universal

import Mathlib.CategoryTheory.Category.Preorder

/-!
# Non-pivotality of the free rigid category on a coupon-free signature

In the free rigid category `S.FreeRigid` on a duality signature `S` with no coupons, there is no
morphism in either direction between a generating object `of a` and its double right dual
`((of a)ᘁ)ᘁ` or double left dual `ᘁ(ᘁ(of a))`. This witnesses that autonomous coherence does not
collapse double duals without a pivotal structure.

## Proof idea

We interpret `S.FreeRigid` into a small thin rigid category `LambekObj` of monotone integer maps
`ℤ → ℤ` satisfying `f (n + 2) = f n + 2` (a concrete Lambek pregroup under Galois adjunction).
Sending every generating object to `n ↦ 2 * (n / 2)` maps `of a` to `(0, 0)` and maps both
`((of a)ᘁ)ᘁ` and `ᘁ(ᘁ(of a))` to `(-1, 1)`, which is incomparable with `(0, 0)` in the pointwise
order.

## Main results

* `FreeRigid.isEmpty_hom_of_doubleRightDual`, `FreeRigid.isEmpty_hom_doubleRightDual_of`,
  `FreeRigid.isEmpty_iso_of_doubleRightDual`: no morphisms or isomorphisms between `of a` and
  `((of a)ᘁ)ᘁ` when `S.Coupon` is empty.
* `FreeRigid.isEmpty_hom_of_doubleLeftDual`, `FreeRigid.isEmpty_hom_doubleLeftDual_of`,
  `FreeRigid.isEmpty_iso_of_doubleLeftDual`: left-dual counterparts.

## References

* J. Lambek, *Type grammar revisited*, Logical Aspects of Computational Linguistics (LACL 1997),
  Lecture Notes in Comput. Sci. 1582 (1999), 1–27.
* P. Selinger, *A survey of graphical languages for monoidal categories*, New Structures for
  Physics, Lecture Notes in Phys. 813 (2011), §4.
-/

public section

universe u v

open CategoryTheory MonoidalCategory ExactPairing

namespace TauCeti.DualitySignature.FreeRigid

variable {S : DualitySignature.{u, v}}

/-- A monotone map `f : ℤ → ℤ` satisfying `f (n + 2) = f n + 2`, represented by its values
`(ev, od)` at `0` and `1` with `ev ≤ od ≤ ev + 2`. -/
@[ext]
private structure LambekObj where
  ev : ℤ
  od : ℤ
  ev_le_od : ev ≤ od
  od_le_ev_add_two : od ≤ ev + 2

namespace LambekObj

private def eval (x : LambekObj) (n : ℤ) : ℤ :=
  2 * (n / 2) + if n % 2 = 0 then x.ev else x.od
private theorem eval_mono (x : LambekObj) {m n : ℤ} (h : m ≤ n) : x.eval m ≤ x.eval n := by
  have := x.ev_le_od; have := x.od_le_ev_add_two; dsimp only [eval]; omega
private instance : PartialOrder LambekObj where
  le x y := x.ev ≤ y.ev ∧ x.od ≤ y.od
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := LambekObj.ext (le_antisymm h₁.1 h₂.1) (le_antisymm h₁.2 h₂.2)
private theorem le_iff_eval_le {x y : LambekObj} : x ≤ y ↔ ∀ n, x.eval n ≤ y.eval n := by
  refine ⟨fun ⟨hev, hod⟩ n ↦ by dsimp only [eval]; omega, fun h ↦ ?_⟩
  have h0 := h 0; have h1 := h 1; dsimp only [eval] at h0 h1; exact ⟨by omega, by omega⟩
private theorem eq_of_eval_eq {x y : LambekObj} (h : ∀ n, x.eval n = y.eval n) : x = y :=
  le_antisymm (le_iff_eval_le.2 fun n ↦ (h n).le) (le_iff_eval_le.2 fun n ↦ (h n).ge)
private def one : LambekObj := ⟨0, 1, by omega, by omega⟩
private theorem one_eval (n : ℤ) : one.eval n = n := by dsimp only [one, eval]; omega
private def mul (x y : LambekObj) : LambekObj where
  ev := x.eval y.ev
  od := x.eval y.od
  ev_le_od := x.eval_mono y.ev_le_od
  od_le_ev_add_two := by
    have := x.ev_le_od; have := x.od_le_ev_add_two; have := y.ev_le_od; have := y.od_le_ev_add_two
    dsimp only [eval]; omega
private theorem mul_eval (x y : LambekObj) (n : ℤ) : (mul x y).eval n = x.eval (y.eval n) := by
  have := x.ev_le_od; have := x.od_le_ev_add_two; dsimp only [mul, eval]; omega
private def rdual (x : LambekObj) : LambekObj where
  ev := min (2 * ((-x.ev + 1) / 2)) (2 * ((-x.od + 1) / 2) + 1)
  od := min (2 * ((2 - x.ev) / 2)) (2 * ((2 - x.od) / 2) + 1)
  ev_le_od := by have := x.ev_le_od; have := x.od_le_ev_add_two; omega
  od_le_ev_add_two := by have := x.ev_le_od; have := x.od_le_ev_add_two; omega
private theorem rdual_coev (x : LambekObj) : one ≤ mul x (rdual x) := le_iff_eval_le.2 fun n ↦ by
  rw [one_eval, mul_eval]; have := x.ev_le_od; have := x.od_le_ev_add_two
  dsimp only [rdual, eval]; omega
private theorem rdual_ev (x : LambekObj) : mul (rdual x) x ≤ one := le_iff_eval_le.2 fun n ↦ by
  rw [one_eval, mul_eval]; have := x.ev_le_od; have := x.od_le_ev_add_two
  dsimp only [rdual, eval]; omega
private def ldual (x : LambekObj) : LambekObj where
  ev := max (2 * ((-x.ev) / 2)) (2 * ((-x.od) / 2) + 1)
  od := max (2 * ((1 - x.ev) / 2)) (2 * ((1 - x.od) / 2) + 1)
  ev_le_od := by have := x.ev_le_od; have := x.od_le_ev_add_two; omega
  od_le_ev_add_two := by have := x.ev_le_od; have := x.od_le_ev_add_two; omega
private theorem ldual_coev (x : LambekObj) : one ≤ mul (ldual x) x := le_iff_eval_le.2 fun n ↦ by
  rw [one_eval, mul_eval]; have := x.ev_le_od; have := x.od_le_ev_add_two
  dsimp only [ldual, eval]; omega
private theorem ldual_ev (x : LambekObj) : mul x (ldual x) ≤ one := le_iff_eval_le.2 fun n ↦ by
  rw [one_eval, mul_eval]; have := x.ev_le_od; have := x.od_le_ev_add_two
  dsimp only [ldual, eval]; omega
private instance : MonoidalCategory LambekObj where
  tensorObj := mul
  whiskerLeft X _ _ f := homOfLE <| le_iff_eval_le.2 fun n ↦ by
    rw [mul_eval, mul_eval]; exact X.eval_mono (le_iff_eval_le.1 (leOfHom f) n)
  whiskerRight f Y := homOfLE <| le_iff_eval_le.2 fun n ↦ by
    rw [mul_eval, mul_eval]; exact le_iff_eval_le.1 (leOfHom f) (Y.eval n)
  tensorHom {X₁ Y₁ X₂ Y₂} f g := homOfLE <| le_iff_eval_le.2 fun n ↦ by
    rw [mul_eval, mul_eval]
    exact (le_iff_eval_le.1 (leOfHom f) (X₂.eval n)).trans
      (Y₁.eval_mono (le_iff_eval_le.1 (leOfHom g) n))
  tensorUnit := one
  associator _ _ _ := eqToIso <| eq_of_eval_eq fun _ ↦ by simp only [mul_eval]
  leftUnitor _ := eqToIso <| eq_of_eval_eq fun _ ↦ by simp only [mul_eval, one_eval]
  rightUnitor _ := eqToIso <| eq_of_eval_eq fun _ ↦ by simp only [mul_eval, one_eval]
private instance : RightRigidCategory LambekObj where
  rightDual X :=
    { rightDual := rdual X
      exact := { coevaluation' := homOfLE (rdual_coev X), evaluation' := homOfLE (rdual_ev X) } }
private instance : LeftRigidCategory LambekObj where
  leftDual X :=
    { leftDual := ldual X
      exact := { coevaluation' := homOfLE (ldual_coev X), evaluation' := homOfLE (ldual_ev X) } }
private instance : RigidCategory LambekObj where
private def base : LambekObj := ⟨0, 0, by omega, by omega⟩
end LambekObj

private theorem isEmpty_lift_base [IsEmpty S.Coupon] {X Y : S.FreeRigid}
    (h : ¬ ((lift (fun _ ↦ LambekObj.base) isEmptyElim).obj X ≤
      (lift (fun _ ↦ LambekObj.base) isEmptyElim).obj Y)) : IsEmpty (X ⟶ Y) :=
  ⟨fun f ↦ h (leOfHom ((lift (fun _ ↦ LambekObj.base) isEmptyElim).map f))⟩

/-- In the free rigid category on a coupon-free duality signature, there is no morphism from a
generating object `of a` to its double right dual `((of a)ᘁ)ᘁ`. -/
theorem isEmpty_hom_of_doubleRightDual [IsEmpty S.Coupon] (a : S.Obj) :
    IsEmpty (of a ⟶ ((of a)ᘁ)ᘁ) :=
  isEmpty_lift_base fun h ↦ absurd (show (0 : ℤ) ≤ -1 from h.1) (by decide)

/-- In the free rigid category on a coupon-free duality signature, there is no morphism from the
double right dual `((of a)ᘁ)ᘁ` of a generating object back to `of a`. -/
theorem isEmpty_hom_doubleRightDual_of [IsEmpty S.Coupon] (a : S.Obj) :
    IsEmpty (((of a)ᘁ)ᘁ ⟶ of a) :=
  isEmpty_lift_base fun h ↦ absurd (show (1 : ℤ) ≤ 0 from h.2) (by decide)

/-- In the free rigid category on a coupon-free duality signature, no generating object is
isomorphic to its double right dual. -/
theorem isEmpty_iso_of_doubleRightDual [IsEmpty S.Coupon] (a : S.Obj) :
    IsEmpty (of a ≅ ((of a)ᘁ)ᘁ) :=
  ⟨fun e ↦ (isEmpty_hom_of_doubleRightDual a).false e.hom⟩

/-- In the free rigid category on a coupon-free duality signature, there is no morphism from a
generating object `of a` to its double left dual `ᘁ(ᘁ(of a))`. -/
theorem isEmpty_hom_of_doubleLeftDual [IsEmpty S.Coupon] (a : S.Obj) :
    IsEmpty (of a ⟶ ᘁ(ᘁ(of a))) :=
  isEmpty_lift_base fun h ↦ absurd (show (0 : ℤ) ≤ -1 from h.1) (by decide)

/-- In the free rigid category on a coupon-free duality signature, there is no morphism from the
double left dual `ᘁ(ᘁ(of a))` of a generating object back to `of a`. -/
theorem isEmpty_hom_doubleLeftDual_of [IsEmpty S.Coupon] (a : S.Obj) :
    IsEmpty ((ᘁ(ᘁ(of a))) ⟶ of a) :=
  isEmpty_lift_base fun h ↦ absurd (show (1 : ℤ) ≤ 0 from h.2) (by decide)

/-- In the free rigid category on a coupon-free duality signature, no generating object is
isomorphic to its double left dual. -/
theorem isEmpty_iso_of_doubleLeftDual [IsEmpty S.Coupon] (a : S.Obj) :
    IsEmpty (of a ≅ ᘁ(ᘁ(of a))) :=
  ⟨fun e ↦ (isEmpty_hom_of_doubleLeftDual a).false e.hom⟩

end TauCeti.DualitySignature.FreeRigid
