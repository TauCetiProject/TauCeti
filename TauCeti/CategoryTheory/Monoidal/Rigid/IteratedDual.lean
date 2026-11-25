/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Iterated duals in a rigid monoidal category

For an object `X` of a right (resp. left) rigid monoidal category, `TauCeti.iteratedRightDual n X`
(resp. `TauCeti.iteratedLeftDual n X`) is the `n`-fold right dual `Xᘁ⋯ᘁ` (resp. left dual
`ᘁ⋯ᘁX`), using the duals chosen by the rigid structure. In a rigid monoidal category these
combine into the iterated dual at an integer level, `TauCeti.iteratedDual n X`: the `n`-fold right
dual for `n ≥ 0` and the `-n`-fold left dual for `n < 0`.

Taking one more dual shifts the level by one (`TauCeti.iteratedDualRightDualIso`,
`TauCeti.iteratedDualLeftDualIso`). Where this cancels a dual of the opposite handedness, the
identification `(ᘁY)ᘁ ≅ Y` or `ᘁ(Yᘁ) ≅ Y` is Mathlib's comparison `rightDualIso` or `leftDualIso`
between two duals of the same object. Two duals of the same handedness are never identified, so
no pivotal structure is used.

The integer-level convention is that of Joyal and Street, *Planar diagrams and tensor
algebra*, §2: the right dual of an object at level `n` is at level `n + 1`.
-/

public section

open CategoryTheory MonoidalCategory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Right

variable [RightRigidCategory C]

/-- The `n`-fold iterated right dual `X ↦ Xᘁ` of an object of a right rigid monoidal category. -/
@[expose]
def iteratedRightDual : ℕ → C → C
  | 0, X => X
  | n + 1, X => (iteratedRightDual n X)ᘁ

@[simp] theorem iteratedRightDual_zero (X : C) : iteratedRightDual 0 X = X := rfl

@[simp] theorem iteratedRightDual_succ (n : ℕ) (X : C) :
    iteratedRightDual (n + 1) X = (iteratedRightDual n X)ᘁ := rfl

end Right

section Left

variable [LeftRigidCategory C]

/-- The `n`-fold iterated left dual `X ↦ ᘁX` of an object of a left rigid monoidal category. -/
@[expose]
def iteratedLeftDual : ℕ → C → C
  | 0, X => X
  | n + 1, X => (ᘁ(iteratedLeftDual n X) : C)

@[simp] theorem iteratedLeftDual_zero (X : C) : iteratedLeftDual 0 X = X := rfl

@[simp] theorem iteratedLeftDual_succ (n : ℕ) (X : C) :
    iteratedLeftDual (n + 1) X = (ᘁ(iteratedLeftDual n X) : C) := rfl

end Left

variable [RigidCategory C]

/-- The iterated dual of `X` at integer level `n`: the `n`-fold right dual for `n ≥ 0` and the
`-n`-fold left dual for `n < 0`. This is the object assigned to a letter at level `n` of a
winding word. -/
@[expose]
def iteratedDual : ℤ → C → C
  | .ofNat n, X => iteratedRightDual n X
  | .negSucc n, X => iteratedLeftDual (n + 1) X

@[simp] theorem iteratedDual_natCast (n : ℕ) (X : C) :
    iteratedDual (n : ℤ) X = iteratedRightDual n X := rfl

/-- At level `(n : ℤ) + 1` the iterated dual is the right dual of the `n`-fold iterated right
dual. -/
@[simp] theorem iteratedDual_natCast_add_one (n : ℕ) (X : C) :
    iteratedDual ((n : ℤ) + 1) X = (iteratedRightDual n X)ᘁ :=
  -- `(n : ℤ) + 1` reduces by definition to `.ofNat (n + 1)`, so this holds by `rfl`.
  rfl

@[simp] theorem iteratedDual_negSucc (n : ℕ) (X : C) :
    iteratedDual (.negSucc n) X = iteratedLeftDual (n + 1) X := rfl

@[simp] theorem iteratedDual_zero (X : C) : iteratedDual 0 X = X := rfl

@[simp] theorem iteratedDual_neg_natCast (n : ℕ) (X : C) :
    iteratedDual (-(n : ℤ)) X = iteratedLeftDual n X := by
  cases n with
  | zero => rfl
  | succ n => rfl

/-- Raising the level by one takes a right dual. For negative levels this cancels a left dual,
through the comparison `(ᘁY)ᘁ ≅ Y` between two right duals of `ᘁY`. -/
noncomputable def iteratedDualRightDualIso :
    (n : ℤ) → (X : C) → (iteratedDual n X)ᘁ ≅ iteratedDual (n + 1) X
  -- `Int.add` computes on constructors: `.ofNat n + 1`, `.negSucc 0 + 1` and
  -- `.negSucc (n + 1) + 1` reduce by definition to `.ofNat (n + 1)`, `.ofNat 0` and
  -- `.negSucc n`, so each case's target is definitionally the stated iterated dual.
  | .ofNat _, _ => Iso.refl _
  | .negSucc 0, X => rightDualIso (RightRigidCategory.rightDual (ᘁX)).exact HasLeftDual.exact
  | .negSucc (n + 1), X =>
    rightDualIso (RightRigidCategory.rightDual (ᘁ(iteratedLeftDual (n + 1) X))).exact
      HasLeftDual.exact

/-- Lowering the level by one takes a left dual. For positive levels this cancels a right dual,
through the comparison `ᘁ(Yᘁ) ≅ Y` between two left duals of `Yᘁ`. -/
noncomputable def iteratedDualLeftDualIso :
    (n : ℤ) → (X : C) → (ᘁ(iteratedDual n X) : C) ≅ iteratedDual (n - 1) X
  -- `Int.sub` computes on constructors: `.ofNat 0 - 1` and `.negSucc n - 1` reduce by definition
  -- to `.negSucc 0` and `.negSucc (n + 1)`, so those cases are `Iso.refl`. For `.ofNat (n + 1)`
  -- the level `n` is reached only through `Int.subNatNat`, so that case uses `eqToIso`.
  | .ofNat 0, _ => Iso.refl _
  | .ofNat (n + 1), X =>
    leftDualIso (LeftRigidCategory.leftDual (iteratedRightDual n X)ᘁ).exact HasRightDual.exact ≪≫
      eqToIso (by simp)
  | .negSucc _, _ => Iso.refl _

/-! The following equation lemmas hold by `rfl`: the cast `(n : ℤ)` is `.ofNat n` by definition,
and `(n : ℤ) + 1` reduces to `.ofNat (n + 1)`, so the defining pattern match fires. -/

@[simp] theorem iteratedDualRightDualIso_natCast (n : ℕ) (X : C) :
    iteratedDualRightDualIso (n : ℤ) X = Iso.refl _ := (rfl)

@[simp] theorem iteratedDualRightDualIso_negSucc_zero (X : C) :
    iteratedDualRightDualIso (.negSucc 0) X =
      rightDualIso (RightRigidCategory.rightDual (ᘁX)).exact HasLeftDual.exact := (rfl)

@[simp] theorem iteratedDualRightDualIso_negSucc_succ (n : ℕ) (X : C) :
    iteratedDualRightDualIso (.negSucc (n + 1)) X =
      rightDualIso (RightRigidCategory.rightDual (ᘁ(iteratedLeftDual (n + 1) X))).exact
        HasLeftDual.exact := (rfl)

@[simp] theorem iteratedDualLeftDualIso_zero (X : C) :
    iteratedDualLeftDualIso 0 X = Iso.refl _ := (rfl)

@[simp] theorem iteratedDualLeftDualIso_natCast_add_one (n : ℕ) (X : C) :
    iteratedDualLeftDualIso ((n : ℤ) + 1) X =
      leftDualIso (LeftRigidCategory.leftDual (iteratedRightDual n X)ᘁ).exact HasRightDual.exact ≪≫
        eqToIso (by simp) := (rfl)

@[simp] theorem iteratedDualLeftDualIso_negSucc (n : ℕ) (X : C) :
    iteratedDualLeftDualIso (.negSucc n) X = Iso.refl _ := (rfl)

end TauCeti
