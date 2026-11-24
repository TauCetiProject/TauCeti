/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.WithZero
public import TauCeti.Algebra.Cluster.CoefficientSemifield.Hom
public import TauCeti.Algebra.Group.WithOne.Units

/-!
# Adjoining zero to a coefficient semifield

Adjoining an absorbing zero to a coefficient semifield `P` gives a semifield `WithZero P` in which
a sum vanishes only when every summand does. Conversely, the units `Sˣ` of such a semifield `S`
form a coefficient semifield (`TauCeti.CoefficientSemifield.instUnits`). The two constructions are
inverse: `TauCeti.CoefficientSemifield.unitsWithZeroRingEquiv` identifies `(WithZero P)ˣ` with
`P`, and `TauCeti.CoefficientSemifield.withZeroUnitsRingEquiv` identifies `WithZero Sˣ` with `S`,
both preserving multiplication and addition.

They also identify the homomorphisms. A homomorphism of coefficient semifields extends by zero to
a semiring map (`TauCeti.CoefficientSemifieldHom.withZeroMap`), and a semiring map restricts to
the units (`RingHom.mapUnits`). Both operations respect identities and composition, they are
compatible with the two comparisons, and each is a bijection on homomorphisms
(`TauCeti.CoefficientSemifieldHom.withZeroMapEquiv` and
`TauCeti.CoefficientSemifieldHom.mapUnitsEquiv`).

This is how semiring constructions, such as localization, produce coefficient semifields and
their homomorphisms.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compos. Math. 143 (2007),
  §2.
-/

public section

noncomputable section

namespace TauCeti

namespace CoefficientSemifield

variable {P : Type*} [CoefficientSemifield P]

/-- Adjoining an absorbing zero to a coefficient semifield gives a semifield, whose addition
extends the auxiliary addition with `0` as its identity. -/
instance instSemifieldWithZero : Semifield (WithZero P) where
  nnqsmul := _
  nnqsmul_def := fun _ _ ↦ rfl

/-- The units of `WithZero P` are identified with `P`, preserving multiplication and the
auxiliary addition. -/
def unitsWithZeroRingEquiv : (WithZero P)ˣ ≃+* P :=
  { WithZero.unitsWithZeroEquiv with
    map_add' a b := WithZero.coe_injective <| by simp }

@[simp]
theorem coe_unitsWithZeroRingEquiv_apply (a : (WithZero P)ˣ) :
    ((unitsWithZeroRingEquiv a : P) : WithZero P) = a :=
  WithZero.coe_unitsWithZeroEquiv_eq_units_val a

@[simp]
theorem val_unitsWithZeroRingEquiv_symm_apply (p : P) :
    ((unitsWithZeroRingEquiv.symm p : (WithZero P)ˣ) : WithZero P) = p := by
  simpa using (coe_unitsWithZeroRingEquiv_apply (unitsWithZeroRingEquiv.symm p)).symm

variable (S : Type*) [Semifield S] [Subsingleton (AddUnits S)]

/-- A semifield in which sums vanish only when every summand does is obtained from its units by
adjoining zero, compatibly with multiplication and addition. -/
def withZeroUnitsRingEquiv : WithZero Sˣ ≃+* S :=
  letI := Classical.decPred fun a : S ↦ a = 0
  { WithZero.withZeroUnitsEquiv with
    map_add' a b := by
      induction a using WithZero.recZeroCoe <;> induction b using WithZero.recZeroCoe <;>
        simp [← WithZero.coe_add] }

variable {S}

@[simp]
theorem withZeroUnitsRingEquiv_coe (a : Sˣ) : withZeroUnitsRingEquiv S a = a := by
  simp [withZeroUnitsRingEquiv]

@[simp]
theorem withZeroUnitsRingEquiv_symm_val (a : Sˣ) : (withZeroUnitsRingEquiv S).symm a = a := by
  rw [RingEquiv.symm_apply_eq, withZeroUnitsRingEquiv_coe]

end CoefficientSemifield

open CoefficientSemifield

namespace CoefficientSemifieldHom

variable {P Q R : Type*} [CoefficientSemifield P] [CoefficientSemifield Q] [CoefficientSemifield R]

/-- Extend a homomorphism of coefficient semifields to a semiring map by sending zero to zero. -/
def withZeroMap (f : CoefficientSemifieldHom P Q) : WithZero P →+* WithZero Q :=
  { WithZero.map' f.toMonoidHom with
    map_add' a b := by
      induction a using WithZero.recZeroCoe <;> induction b using WithZero.recZeroCoe <;>
        simp [← WithZero.coe_add] }

@[simp]
theorem withZeroMap_coe (f : CoefficientSemifieldHom P Q) (p : P) :
    f.withZeroMap p = f p :=
  (rfl)

@[simp]
theorem withZeroMap_id :
    (CoefficientSemifieldHom.id P).withZeroMap = RingHom.id (WithZero P) := by
  ext a
  induction a using WithZero.recZeroCoe <;> simp

@[simp]
theorem withZeroMap_comp (g : CoefficientSemifieldHom Q R) (f : CoefficientSemifieldHom P Q) :
    (g.comp f).withZeroMap = g.withZeroMap.comp f.withZeroMap := by
  ext a
  induction a using WithZero.recZeroCoe <;> simp

end CoefficientSemifieldHom

end TauCeti

namespace RingHom

open TauCeti CoefficientSemifield

variable {S T U : Type*} [Semifield S] [Semifield T] [Semifield U] [Subsingleton (AddUnits S)]
  [Subsingleton (AddUnits T)] [Subsingleton (AddUnits U)]

/-- Restrict a semiring map between semifields in which sums vanish only when every summand does
to a homomorphism of the coefficient semifields of units. -/
def mapUnits (f : S →+* T) : CoefficientSemifieldHom Sˣ Tˣ :=
  { Units.map f.toMonoidHom with map_add' a b := Units.ext (map_add f (a : S) b) }

@[simp]
theorem val_mapUnits (f : S →+* T) (a : Sˣ) : (f.mapUnits a : T) = f (a : S) :=
  (rfl)

@[simp]
theorem mapUnits_id : (RingHom.id S).mapUnits = CoefficientSemifieldHom.id Sˣ := by
  ext
  simp

@[simp]
theorem mapUnits_comp (g : T →+* U) (f : S →+* T) :
    (g.comp f).mapUnits = g.mapUnits.comp f.mapUnits := by
  ext
  simp

/-- Restricting a semiring map to the units and extending back by zero recovers the map, under
the identifications `WithZero Sˣ ≃+* S` and `WithZero Tˣ ≃+* T`. -/
@[simp]
theorem withZeroUnitsRingEquiv_withZeroMap_mapUnits (f : S →+* T) (a : WithZero Sˣ) :
    withZeroUnitsRingEquiv T (f.mapUnits.withZeroMap a) = f (withZeroUnitsRingEquiv S a) := by
  induction a using WithZero.recZeroCoe <;> simp

end RingHom

namespace TauCeti.CoefficientSemifieldHom

open CoefficientSemifield

variable {P Q : Type*} [CoefficientSemifield P] [CoefficientSemifield Q]

/-- Extending a homomorphism by zero and restricting to the units recovers it, under the
identifications `(WithZero P)ˣ ≃+* P` and `(WithZero Q)ˣ ≃+* Q`. -/
@[simp]
theorem unitsWithZeroRingEquiv_mapUnits_withZeroMap (f : CoefficientSemifieldHom P Q)
    (a : (WithZero P)ˣ) :
    unitsWithZeroRingEquiv (f.withZeroMap.mapUnits a) = f (unitsWithZeroRingEquiv a) := by
  obtain ⟨p, rfl⟩ := unitsWithZeroRingEquiv.symm.surjective a
  apply WithZero.coe_injective
  simp

/-- Homomorphisms of coefficient semifields `P → Q` correspond to semiring maps
`WithZero P →+* WithZero Q`, by extension by zero. -/
def withZeroMapEquiv : CoefficientSemifieldHom P Q ≃ (WithZero P →+* WithZero Q) where
  toFun := withZeroMap
  invFun g := unitsWithZeroRingEquiv.toCoefficientSemifieldHom.comp
    (g.mapUnits.comp unitsWithZeroRingEquiv.symm.toCoefficientSemifieldHom)
  left_inv f := by ext; simp
  right_inv g := by
    ext a
    induction a using WithZero.recZeroCoe <;> simp

@[simp]
theorem withZeroMapEquiv_apply (f : CoefficientSemifieldHom P Q) :
    withZeroMapEquiv f = f.withZeroMap :=
  (rfl)

@[simp]
theorem withZeroMap_withZeroMapEquiv_symm (g : WithZero P →+* WithZero Q) :
    (withZeroMapEquiv.symm g).withZeroMap = g :=
  withZeroMapEquiv.apply_symm_apply g

/-- Extension by zero is injective on homomorphisms. -/
theorem withZeroMap_injective :
    Function.Injective (withZeroMap : CoefficientSemifieldHom P Q → WithZero P →+* WithZero Q) :=
  withZeroMapEquiv.injective

variable {S T : Type*} [Semifield S] [Semifield T] [Subsingleton (AddUnits S)]
  [Subsingleton (AddUnits T)]

/-- Semiring maps between semifields in which sums vanish only when every summand does correspond
to homomorphisms of their coefficient semifields of units, by restriction. -/
def mapUnitsEquiv : (S →+* T) ≃ CoefficientSemifieldHom Sˣ Tˣ where
  toFun := RingHom.mapUnits
  invFun g := (withZeroUnitsRingEquiv T : WithZero Tˣ →+* T).comp
    (g.withZeroMap.comp (withZeroUnitsRingEquiv S).symm)
  left_inv f := by ext; simp
  right_inv g := by ext; simp

@[simp]
theorem mapUnitsEquiv_apply (f : S →+* T) : mapUnitsEquiv f = f.mapUnits :=
  (rfl)

@[simp]
theorem mapUnits_mapUnitsEquiv_symm (g : CoefficientSemifieldHom Sˣ Tˣ) :
    (mapUnitsEquiv.symm g).mapUnits = g :=
  mapUnitsEquiv.apply_symm_apply g

/-- Restriction to units is injective on semiring maps. -/
theorem mapUnits_injective : Function.Injective (RingHom.mapUnits : (S →+* T) → _) :=
  mapUnitsEquiv.injective

end TauCeti.CoefficientSemifieldHom
