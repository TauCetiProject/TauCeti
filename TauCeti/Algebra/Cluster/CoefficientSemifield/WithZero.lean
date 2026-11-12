/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSemifield.Hom
public import TauCeti.Algebra.Group.Units.ZeroSumFree
public import Mathlib.Algebra.Ring.WithZero

/-!
# Adjoining zero to a coefficient semifield

Adjoining an absorbing zero turns a coefficient semifield into a zero-sum-free semifield.
Conversely, the units of a zero-sum-free semifield inherit auxiliary addition from the
semifield. These operations are compatible with semiring maps and with extension by zero.
-/

@[expose] public section

namespace TauCeti.CoefficientSemifield

variable {P : Type*} [CoefficientSemifield P]

/-- Auxiliary addition extends by an identity, and every nonzero element is invertible. -/
instance : Semifield (WithZero P) where
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl

instance : ZeroSumFree (WithZero P) :=
  ZeroSumFree.of_add_eq_zero fun a b h => by
    induction a using WithZero.recZeroCoe <;> induction b using WithZero.recZeroCoe
    all_goals simp_all [← WithZero.coe_add]

end TauCeti.CoefficientSemifield

namespace TauCeti.CoefficientSemifieldHom

variable {P Q : Type*} [CoefficientSemifield P] [CoefficientSemifield Q]

/-- Extend a coefficient homomorphism by sending the adjoined zero to zero. -/
def withZeroMap (f : CoefficientSemifieldHom P Q) : WithZero P →+* WithZero Q :=
  { WithZero.map' f.toMonoidHom with
    map_add' := by
      intro a b
      induction a using WithZero.recZeroCoe <;> induction b using WithZero.recZeroCoe
      all_goals simp [← WithZero.coe_add, map_add] }

@[simp]
theorem withZeroMap_coe (f : CoefficientSemifieldHom P Q) (p : P) :
    f.withZeroMap (p : WithZero P) = (f p : WithZero Q) := rfl

/-- A semiring map restricts to a homomorphism on the units of zero-sum-free semifields. -/
def mapUnits {S T : Type*} [Semifield S] [Semifield T] [ZeroSumFree S] [ZeroSumFree T]
    (f : S →+* T) : CoefficientSemifieldHom Sˣ Tˣ where
  __ := Units.map f.toMonoidHom
  map_add' a b := Units.ext (map_add f (a : S) (b : S))

@[simp]
theorem val_mapUnits {S T : Type*} [Semifield S] [Semifield T] [ZeroSumFree S] [ZeroSumFree T]
    (f : S →+* T) (a : Sˣ) : (mapUnits f a : T) = f a := rfl

/-- The multiplicative identification of `(WithZero P)ˣ` with `P` preserves addition. -/
def unitsWithZero : CoefficientSemifieldHom (WithZero P)ˣ P where
  __ := WithZero.unitsWithZeroEquiv.toMonoidHom
  map_add' a b := WithZero.coe_injective <| by
    change WithZero.coe (WithZero.unitsWithZeroEquiv (a + b)) =
      WithZero.coe (WithZero.unitsWithZeroEquiv a + WithZero.unitsWithZeroEquiv b)
    simp only [WithZero.coe_add, WithZero.coe_unitsWithZeroEquiv_eq_units_val,
      Units.val_add_of_subsingleton_addUnits]

@[simp]
theorem coe_unitsWithZero (a : (WithZero P)ˣ) :
    (unitsWithZero (P := P) a : WithZero P) = (a : WithZero P) :=
  WithZero.coe_unitsWithZeroEquiv_eq_units_val a

end TauCeti.CoefficientSemifieldHom

namespace TauCeti.CoefficientSemifield

/-- The canonical identification of a zero-sum-free semifield with the result of adjoining zero
to its units also preserves addition. -/
noncomputable def withZeroUnitsRingEquiv (S : Type*) [Semifield S] [ZeroSumFree S] :
    WithZero Sˣ ≃+* S := by
  classical
  exact { WithZero.withZeroUnitsEquiv with
    map_add' := by
      intro a b
      induction a using WithZero.recZeroCoe <;> induction b using WithZero.recZeroCoe
      all_goals simp [← WithZero.coe_add] }

@[simp]
theorem withZeroUnitsRingEquiv_coe {S : Type*} [Semifield S] [ZeroSumFree S] (a : Sˣ) :
    withZeroUnitsRingEquiv S (a : WithZero Sˣ) = (a : S) := rfl

end TauCeti.CoefficientSemifield
