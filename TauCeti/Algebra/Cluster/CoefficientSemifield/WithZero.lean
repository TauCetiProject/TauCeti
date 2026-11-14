/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSemifield.Hom
public import TauCeti.Algebra.Group.WithOne.Units
public import Mathlib.Algebra.Ring.WithZero

/-!
# Adjoining zero to a coefficient semifield

To apply semiring and localization constructions to coefficient semifields, adjoin an absorbing
zero to obtain `Semifield (WithZero P)`. Extension by zero (`CoefficientSemifieldHom.withZeroMap`)
and restriction to the units of a zero-sum-free semifield (`CoefficientSemifieldHom.mapUnits`)
are functorial. This file also bundles the addition-preserving comparisons between `P` and
`(WithZero P)ˣ`, and between `S` and `WithZero Sˣ`; the coefficient-semifield structure on `Sˣ`
is defined in `Basic.lean`.
-/

public section

namespace TauCeti.CoefficientSemifield

/-- Auxiliary addition extends by an identity, and every nonzero element is invertible. -/
instance {P : Type*} [CoefficientSemifield P] : Semifield (WithZero P) where
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl

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

namespace TauCeti.CoefficientSemifieldHom

open CoefficientSemifield

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

/-- Extension by zero preserves the identity homomorphism of coefficient semifields. -/
@[simp]
theorem withZeroMap_id : withZeroMap (CoefficientSemifieldHom.id P) = RingHom.id (WithZero P) := by
  apply RingHom.ext
  intro p
  induction p using WithZero.recZeroCoe <;> simp

/-- Extension by zero preserves composition of coefficient homomorphisms. -/
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

/-- The forward map of `WithZero.unitsWithZeroEquiv`, bundled as a coefficient homomorphism. -/
def unitsWithZero : CoefficientSemifieldHom (WithZero P)ˣ P where
  __ := WithZero.unitsWithZeroEquiv.toMonoidHom
  map_add' a b := WithZero.coe_injective (by simp)

theorem unitsWithZero_apply (a : (WithZero P)ˣ) :
    unitsWithZero (P := P) a = WithZero.unzero a.ne_zero := (rfl)

@[simp]
theorem coe_unitsWithZero (a : (WithZero P)ˣ) :
    (unitsWithZero (P := P) a : WithZero P) = (a : WithZero P) :=
  WithZero.coe_unitsWithZeroEquiv_eq_units_val a

/-- Embed a coefficient semifield into the units after adjoining zero. -/
def withZeroUnits : CoefficientSemifieldHom P (WithZero P)ˣ where
  __ := MonoidHom.mk' (fun p : P => Units.mk0 (G₀ := WithZero P) (p : WithZero P)
      WithZero.coe_ne_zero) (fun _ _ => Units.ext (by simp))
  map_add' a b := Units.ext (by simp [← WithZero.coe_add])

@[simp]
theorem coe_withZeroUnits (p : P) : (withZeroUnits (P := P) p : WithZero P) = p := by
  simp [withZeroUnits]

@[simp]
theorem withZeroUnits_unzero (a : (WithZero P)ˣ) :
    withZeroUnits (WithZero.unzero a.ne_zero) = a := Units.ext (by simp)

@[simp]
theorem unitsWithZero_withZeroUnits (p : P) : unitsWithZero (withZeroUnits p) = p := by
  apply WithZero.coe_injective
  simp

@[simp]
theorem withZeroUnits_unitsWithZero (a : (WithZero P)ˣ) :
    withZeroUnits (unitsWithZero a) = a := Units.ext (by simp)

@[simp]
theorem unitsWithZero_comp_withZeroUnits :
    (unitsWithZero (P := P)).comp withZeroUnits = CoefficientSemifieldHom.id P :=
  CoefficientSemifieldHom.ext fun p => by simp [comp_apply]

/-- The two coefficient comparisons on `P` and `(WithZero P)ˣ` are inverse. -/
theorem withZeroUnits_comp_unitsWithZero :
    (withZeroUnits (P := P)).comp unitsWithZero = CoefficientSemifieldHom.id (WithZero P)ˣ :=
  CoefficientSemifieldHom.ext fun a => by simp [comp_apply, unitsWithZero_apply]

/-- Restriction to units converts `withZeroMap` to composition with the coefficient map. -/
@[simp]
theorem unitsWithZero_map_withZeroMap (f : CoefficientSemifieldHom P Q) :
    (unitsWithZero (P := Q)).comp (mapUnits f.withZeroMap) = f.comp unitsWithZero := by
  ext a
  apply WithZero.coe_injective
  simp only [comp_apply, coe_unitsWithZero, val_mapUnits]
  rw [← WithZero.coe_unzero a.ne_zero, withZeroMap_coe]
  simp [unitsWithZero_apply]

/-- Extension by zero converts the unit comparison into `withZeroMap`. -/
@[simp]
theorem mapUnits_withZeroMap (f : CoefficientSemifieldHom P Q) :
    (mapUnits f.withZeroMap).comp withZeroUnits = withZeroUnits.comp f :=
  CoefficientSemifieldHom.ext fun _ => Units.ext (by simp)

open CoefficientSemifield in
/-- Extension by zero is compatible with the zero-sum-free/unit comparison. -/
@[simp]
theorem withZeroUnitsRingEquiv_naturality {S T : Type*} [Semifield S] [Semifield T]
    [Subsingleton (AddUnits S)] [Subsingleton (AddUnits T)] (f : S →+* T) :
    f.comp (withZeroUnitsRingEquiv S : WithZero Sˣ →+* S) =
      (withZeroUnitsRingEquiv T : WithZero Tˣ →+* T).comp (mapUnits f).withZeroMap := by
  ext a
  induction a using WithZero.recZeroCoe <;> simp

end TauCeti.CoefficientSemifieldHom

namespace TauCeti.CoefficientSemifield

variable {P Q : Type*} [CoefficientSemifield P] [CoefficientSemifield Q]

/-- The addition-preserving identification of `(WithZero P)ˣ` with `P`. -/
def unitsWithZeroEquiv : (WithZero P)ˣ ≃+* P :=
  { WithZero.unitsWithZeroEquiv with
    map_add' := CoefficientSemifieldHom.unitsWithZero.map_add }

theorem coe_unitsWithZeroEquiv (a : (WithZero P)ˣ) :
    (unitsWithZeroEquiv (P := P) a : WithZero P) = (a : WithZero P) :=
  WithZero.coe_unitsWithZeroEquiv_eq_units_val a

theorem coe_unitsWithZeroEquiv_symm (p : P) :
    (unitsWithZeroEquiv.symm p : WithZero P) = (p : WithZero P) := by
  rw [show unitsWithZeroEquiv (P := P).symm p =
    WithZero.unitsWithZeroEquiv.symm p from rfl]
  simp

@[simp]
theorem unitsWithZeroEquiv_apply (a : (WithZero P)ˣ) :
    unitsWithZeroEquiv (P := P) a = CoefficientSemifieldHom.unitsWithZero a := (rfl)

@[simp]
theorem unitsWithZeroEquiv_symm_apply (p : P) :
    unitsWithZeroEquiv (P := P).symm p = CoefficientSemifieldHom.withZeroUnits p :=
  Units.ext (coe_unitsWithZeroEquiv_symm p)

end TauCeti.CoefficientSemifield
