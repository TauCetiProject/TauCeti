/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Bimodule

/-!
# Derivations into bimodules

This file defines derivations from a possibly noncommutative algebra into a bimodule.  The right
action is expressed, as usual in Mathlib, as a left action of the opposite algebra.  These
derivations are the maps represented by noncommutative universal one-forms.

Unlike `Derivation`, which currently treats commutative algebras and symmetric modules,
`BimoduleDerivation` uses the associative Leibniz rule
`D (a * b) = a • D b + op b • D a`.
-/

public section

open MulOpposite

namespace TauCeti

universe u v w

/-- A derivation from an associative unital algebra into a bimodule.

The left action is the `A`-action and the right action is the `Aᵐᵒᵖ`-action.  We include
`D 1 = 0` in the data so that the definition works over semirings and non-cancellative additive
targets as well as over rings. -/
structure BimoduleDerivation (k : Type u) (A : Type v) (M : Type w)
    [CommSemiring k] [Semiring A] [AddCommMonoid M] [Algebra k A]
    [Module k M] [Module A M] [Module Aᵐᵒᵖ M] extends A →ₗ[k] M where
  protected map_one_eq_zero' : toLinearMap 1 = 0
  protected leibniz' (a b : A) :
    toLinearMap (a * b) = a • toLinearMap b + op b • toLinearMap a

namespace BimoduleDerivation

variable {k : Type u} {A : Type v} {M : Type w}
  [CommSemiring k] [Semiring A] [AddCommMonoid M] [Algebra k A]
  [Module k M] [Module A M] [Module Aᵐᵒᵖ M]

instance : FunLike (BimoduleDerivation k A M) A M where
  coe D := D.toLinearMap
  coe_injective D E h := by
    cases D with
    | mk d hd hl =>
      cases E with
      | mk e he el =>
        congr
        exact LinearMap.ext fun a ↦ congrFun h a

instance : AddMonoidHomClass (BimoduleDerivation k A M) A M where
  map_add D := D.toLinearMap.map_add
  map_zero D := D.toLinearMap.map_zero

instance : Coe (BimoduleDerivation k A M) (A →ₗ[k] M) := ⟨fun D ↦ D.toLinearMap⟩

/-- Coercion to the underlying linear map preserves the underlying function. -/
@[simp]
theorem coe_toLinearMap (D : BimoduleDerivation k A M) :
    ⇑(D : A →ₗ[k] M) = D := rfl

/-- Two bimodule derivations are equal when they agree on every input. -/
@[ext]
theorem ext {D E : BimoduleDerivation k A M} (h : ∀ a, D a = E a) : D = E :=
  DFunLike.ext D E h

/-- A bimodule derivation sends the unit to zero. -/
@[simp]
theorem map_one_eq_zero (D : BimoduleDerivation k A M) : D 1 = 0 :=
  D.map_one_eq_zero'

/-- The associative Leibniz rule for a bimodule derivation. -/
@[simp]
theorem leibniz (D : BimoduleDerivation k A M) (a b : A) :
    D (a * b) = a • D b + op b • D a :=
  D.leibniz' a b

/-- A bimodule derivation is linear over the ground semiring. -/
@[simp]
theorem map_smul (D : BimoduleDerivation k A M) (r : k) (a : A) :
    D (r • a) = r • D a :=
  D.toLinearMap.map_smul r a

end BimoduleDerivation

end TauCeti
