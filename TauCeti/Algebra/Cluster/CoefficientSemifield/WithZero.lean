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

public section

namespace TauCeti.CoefficientSemifield

variable {P : Type*} [CoefficientSemifield P]

/-- Auxiliary addition extends by an identity, and every nonzero element is invertible. -/
instance : Semifield (WithZero P) where
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl

instance : Subsingleton (AddUnits (WithZero P)) :=
  Subsingleton.addUnits_of_isAddUnit fun a ha => by
    obtain ⟨b, h⟩ := ha.exists_neg
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
    f.withZeroMap (p : WithZero P) = (f p : WithZero Q) := (rfl)

/-- Extension by zero preserves the identity ring homomorphism. -/
@[simp]
theorem withZeroMap_id : withZeroMap (CoefficientSemifieldHom.id P) = RingHom.id (WithZero P) := by
  apply RingHom.ext
  intro p
  induction p using WithZero.recZeroCoe <;> simp

/-- Extension by zero preserves composition of ring homomorphisms. -/
@[simp]
theorem withZeroMap_comp {R : Type*} [CoefficientSemifield R]
    (f : CoefficientSemifieldHom P Q) (g : CoefficientSemifieldHom Q R) :
    (g.comp f).withZeroMap = g.withZeroMap.comp f.withZeroMap := by
  apply RingHom.ext
  intro p
  induction p using WithZero.recZeroCoe <;> simp

/-- A semiring map restricts to a homomorphism on the units of zero-sum-free semifields. -/
def mapUnits {S T : Type*} [Semifield S] [Semifield T] [Subsingleton (AddUnits S)]
    [Subsingleton (AddUnits T)] (f : S →+* T) : CoefficientSemifieldHom Sˣ Tˣ where
  __ := Units.map f.toMonoidHom
  map_add' a b := Units.ext (map_add f (a : S) (b : S))

@[simp]
theorem val_mapUnits {S T : Type*} [Semifield S] [Semifield T] [Subsingleton (AddUnits S)]
    [Subsingleton (AddUnits T)] (f : S →+* T) (a : Sˣ) : (mapUnits f a : T) = f a := (rfl)

/-- Restriction to units preserves the identity ring homomorphism. -/
@[simp]
theorem mapUnits_id {S : Type*} [Semifield S] [Subsingleton (AddUnits S)] :
    mapUnits (RingHom.id S) = CoefficientSemifieldHom.id Sˣ :=
  CoefficientSemifieldHom.ext fun _ => Units.ext (by simp)

/-- Restriction to units preserves composition of ring homomorphisms. -/
@[simp]
theorem mapUnits_comp {S T U : Type*} [Semifield S] [Semifield T] [Semifield U]
    [Subsingleton (AddUnits S)] [Subsingleton (AddUnits T)] [Subsingleton (AddUnits U)]
    (f : S →+* T) (g : T →+* U) : mapUnits (g.comp f) = (mapUnits g).comp (mapUnits f) :=
  CoefficientSemifieldHom.ext fun _ => Units.ext (by simp)

/-- The multiplicative identification of `(WithZero P)ˣ` with `P` preserves addition. -/
def unitsWithZero : CoefficientSemifieldHom (WithZero P)ˣ P where
  __ := WithZero.unitsWithZeroEquiv.toMonoidHom
  map_add' a b := WithZero.coe_injective (by simp)

@[simp]
theorem coe_unitsWithZero (a : (WithZero P)ˣ) :
    (unitsWithZero (P := P) a : WithZero P) = (a : WithZero P) :=
  WithZero.coe_unitsWithZeroEquiv_eq_units_val a

end TauCeti.CoefficientSemifieldHom

namespace TauCeti.CoefficientSemifield

/-- The canonical identification of a zero-sum-free semifield with the result of adjoining zero
to its units also preserves addition. -/
noncomputable def withZeroUnitsRingEquiv (S : Type*) [Semifield S] [Subsingleton (AddUnits S)] :
    WithZero Sˣ ≃+* S := by
  classical
  exact { WithZero.withZeroUnitsEquiv with
    map_add' := by
      intro a b
      induction a using WithZero.recZeroCoe <;> induction b using WithZero.recZeroCoe
      all_goals simp [← WithZero.coe_add] }

@[simp]
theorem withZeroUnitsRingEquiv_coe {S : Type*} [Semifield S] [Subsingleton (AddUnits S)] (a : Sˣ) :
    withZeroUnitsRingEquiv S (a : WithZero Sˣ) = (a : S) := (rfl)

/-- The inverse comparison sends a unit to its canonical nonzero embedding. -/
@[simp]
theorem withZeroUnitsRingEquiv_symm_coe {S : Type*} [Semifield S] [Subsingleton (AddUnits S)]
    (a : Sˣ) : (withZeroUnitsRingEquiv S).symm (a : S) = (a : WithZero Sˣ) :=
  (withZeroUnitsRingEquiv S).symm_apply_eq.mpr (withZeroUnitsRingEquiv_coe a).symm

end TauCeti.CoefficientSemifield
