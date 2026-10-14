/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Algebra.Module.Bimodule

/-!
# Derivations into bimodules

This file defines derivations from a possibly noncommutative algebra into a bimodule.  The right
action is expressed, as usual in Mathlib, as a left action of the opposite algebra.  These
derivations are the maps represented by noncommutative universal one-forms.

Unlike `Derivation`, which currently treats commutative algebras and symmetric modules,
`BimoduleDerivation` uses the associative Leibniz rule
`D (a * b) = a • D b + op b • D a`.

A derivation of a possibly nonunital algebra `A` into a bimodule over its forced unitization
extends by zero on the scalar summand to a derivation of `Unitization k A`; see
`BimoduleDerivation.ofUnitization`.
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

/-- A bimodule derivation vanishes on scalars. -/
@[simp]
theorem map_algebraMap (D : BimoduleDerivation k A M) (r : k) : D (algebraMap k A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one_eq_zero, smul_zero]

end BimoduleDerivation

section Unitization

variable {k : Type u} {A : Type v} {M : Type w} [CommSemiring k] [NonUnitalSemiring A]
  [Module k A] [IsScalarTower k A A] [SMulCommClass k A A] [AddCommMonoid M] [Module k M]
  [Module (Unitization k A) M] [Module (Unitization k A)ᵐᵒᵖ M]
  [IsScalarTower k (Unitization k A) M] [IsScalarTower k (Unitization k A)ᵐᵒᵖ M]

namespace BimoduleDerivation

/-- Extend a derivation on a nonunital algebra by zero on the scalar summand of its forced
unitization. -/
def ofUnitization (D : A →ₗ[k] M)
    (hD : ∀ a b, D (a * b) = (a : Unitization k A) • D b +
      op (b : Unitization k A) • D a) :
    BimoduleDerivation k (Unitization k A) M where
  toLinearMap := D.comp (Unitization.sndHom k k A)
  map_one_eq_zero' := by simp
  leibniz' := fun x y ↦ by
    simp only [LinearMap.comp_apply, Unitization.sndHom_apply]
    have left_decomp (z : Unitization k A) (m : M) :
        z • m = z.fst • m + (z.snd : Unitization k A) • m := by
      conv_lhs => rw [← Unitization.inl_fst_add_inr_snd_eq z]
      rw [add_smul, ← Unitization.algebraMap_eq_inl, IsScalarTower.algebraMap_smul]
    have right_decomp (z : Unitization k A) (m : M) :
        op z • m = z.fst • m + op (z.snd : Unitization k A) • m := by
      conv_lhs => rw [← Unitization.inl_fst_add_inr_snd_eq z]
      rw [op_add, add_smul, ← Unitization.algebraMap_eq_inl, ← MulOpposite.algebraMap_apply,
        IsScalarTower.algebraMap_smul]
    rw [Unitization.snd_mul, map_add, map_add, LinearMap.map_smul, LinearMap.map_smul, hD,
      left_decomp x, right_decomp y]
    abel

/-- Extending by zero and then evaluating on the original algebra recovers the derivation. -/
@[simp]
theorem ofUnitization_inr (D : A →ₗ[k] M)
    (hD : ∀ a b, D (a * b) = (a : Unitization k A) • D b +
      op (b : Unitization k A) • D a) (a : A) :
    ofUnitization D hD (a : Unitization k A) = D a := by
  unfold ofUnitization
  rfl

end BimoduleDerivation

end Unitization

end TauCeti
