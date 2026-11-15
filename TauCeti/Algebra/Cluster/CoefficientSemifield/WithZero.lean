/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.WithZero
public import TauCeti.Algebra.Cluster.CoefficientSemifield.Hom
public import TauCeti.Algebra.Group.Units.Subsingleton

/-!
# Zero adjunction and unit correspondence for coefficient semifields

Adjoining an absorbing zero to a coefficient semifield `P` gives a zero-sum-free `Semifield`
`WithZero P` whose addition and multiplication are Mathlib's given operations on `WithZero P`.
Conversely, restricting a zero-sum-free semifield `S` to its unit group `Sˣ` gives a coefficient
semifield (`TauCeti.CoefficientSemifield.instUnits`).

These two constructions are mutually inverse up to canonical `RingEquiv`s, and extension by zero
and restriction to units identify `TauCeti.CoefficientSemifieldHom`s with `RingHom`s between
zero-sum-free semifields without changing instances at any use.

## Main declarations

* `TauCeti.CoefficientSemifield.instSemifieldWithZero`: `WithZero P` is a `Semifield` (with
  `Subsingleton (AddUnits (WithZero P))` from `TauCeti.instSubsingletonAddUnitsWithZero`).
* `TauCeti.CoefficientSemifield.toUnitsWithZero`: addition-preserving multiplicative equivalence
  `P ≃+* (WithZero P)ˣ`.
* `TauCeti.CoefficientSemifield.withZeroUnitsEquiv`: semiring equivalence `WithZero Sˣ ≃+* S` for
  a zero-sum-free semifield `S`, and `TauCeti.CoefficientSemifield.withZeroCongr` lifting `P ≃+* Q`
  to `WithZero P ≃+* WithZero Q`.
* `TauCeti.CoefficientSemifieldHom.unitsMap`, `TauCeti.CoefficientSemifieldHom.liftWithZero`,
  `TauCeti.CoefficientSemifieldHom.mapWithZero`, and their bundled equivalences
  `liftWithZeroEquiv`, `mapWithZeroEquiv`, and `unitsMapEquiv`.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compos. Math. 143 (2007), §2.
-/

public section

namespace RingEquiv

/-- Reinterpret an addition- and multiplication-preserving equivalence between coefficient
semifields as a `TauCeti.CoefficientSemifieldHom`. -/
def toCoefficientSemifieldHom {P Q : Type*} [TauCeti.CoefficientSemifield P]
    [TauCeti.CoefficientSemifield Q] (e : P ≃+* Q) :
    TauCeti.CoefficientSemifieldHom P Q :=
  { e.toMulEquiv.toMonoidHom, e.toAddEquiv.toAddHom with }

@[simp]
theorem coe_toCoefficientSemifieldHom {P Q : Type*} [TauCeti.CoefficientSemifield P]
    [TauCeti.CoefficientSemifield Q] (e : P ≃+* Q) :
    ⇑e.toCoefficientSemifieldHom = e :=
  (rfl)

@[simp]
theorem toCoefficientSemifieldHom_refl (P : Type*) [TauCeti.CoefficientSemifield P] :
    (RingEquiv.refl P).toCoefficientSemifieldHom = .id P := by
  ext
  simp

@[simp]
theorem toCoefficientSemifieldHom_trans {P Q R : Type*} [TauCeti.CoefficientSemifield P]
    [TauCeti.CoefficientSemifield Q] [TauCeti.CoefficientSemifield R]
    (e₁ : P ≃+* Q) (e₂ : Q ≃+* R) :
    (e₁.trans e₂).toCoefficientSemifieldHom =
      e₂.toCoefficientSemifieldHom.comp e₁.toCoefficientSemifieldHom := by
  ext
  simp

@[simp]
theorem symm_comp_toCoefficientSemifieldHom {P Q : Type*} [TauCeti.CoefficientSemifield P]
    [TauCeti.CoefficientSemifield Q] (e : P ≃+* Q) :
    e.symm.toCoefficientSemifieldHom.comp e.toCoefficientSemifieldHom = .id P := by
  ext x
  simp

@[simp]
theorem toCoefficientSemifieldHom_comp_symm {P Q : Type*} [TauCeti.CoefficientSemifield P]
    [TauCeti.CoefficientSemifield Q] (e : P ≃+* Q) :
    e.toCoefficientSemifieldHom.comp e.symm.toCoefficientSemifieldHom = .id Q := by
  ext x
  simp

end RingEquiv

namespace TauCeti

namespace CoefficientSemifield

/-- Adjoining `0` to a coefficient semifield `P` produces a `Semifield` using Mathlib's given
`WithZero` addition and multiplication. Together with `instSubsingletonAddUnitsWithZero`, this
makes `WithZero P` a zero-sum-free semifield. -/
instance instSemifieldWithZero {P : Type*} [CoefficientSemifield P] :
    Semifield (WithZero P) where
  __ := WithZero.instAddCommMonoid
  __ := WithZero.instCommGroupWithZero
  __ := WithZero.instDistrib
  __ := (AddMonoidWithOne.unary : AddMonoidWithOne (WithZero P))
  nnqsmul := _
  nnqsmul_def _ _ := rfl

/-! ### Comparison equivalences -/

section Comparisons

/-- Every coefficient semifield `P` is canonically isomorphic (for both multiplication and
auxiliary addition) to the unit group of `WithZero P`. -/
def toUnitsWithZero (P : Type*) [CoefficientSemifield P] : P ≃+* (WithZero P)ˣ where
  __ := WithZero.unitsWithZeroEquiv.symm
  map_add' a b := Units.ext (WithZero.coe_add a b)

@[simp, norm_cast]
theorem val_toUnitsWithZero {P : Type*} [CoefficientSemifield P] (p : P) :
    ((toUnitsWithZero P p : (WithZero P)ˣ) : WithZero P) = p :=
  (rfl)

@[simp]
theorem coe_toUnitsWithZero_symm {P : Type*} [CoefficientSemifield P] (u : (WithZero P)ˣ) :
    (((toUnitsWithZero P).symm u : P) : WithZero P) = u :=
  WithZero.coe_unzero u.ne_zero

@[simp]
theorem toUnitsWithZero_symm_mk0 {P : Type*} [CoefficientSemifield P] (p : P)
    (hp : (p : WithZero P) ≠ 0) :
    (toUnitsWithZero P).symm (Units.mk0 (p : WithZero P) hp) = p :=
  (rfl)

/-- Adjoining `0` to the unit group of a zero-sum-free semifield `S` recovers `S` as a semiring. -/
noncomputable def withZeroUnitsEquiv (S : Type*) [Semifield S] [Subsingleton (AddUnits S)] :
    WithZero Sˣ ≃+* S :=
  letI := Classical.decPred fun a : S => a = 0
  { WithZero.withZeroUnitsEquiv with
    map_add' := fun a b => by
      induction a <;> induction b <;> simp [← WithZero.coe_add] }

@[simp]
theorem withZeroUnitsEquiv_coe {S : Type*} [Semifield S] [Subsingleton (AddUnits S)] (u : Sˣ) :
    withZeroUnitsEquiv S u = u :=
  (rfl)

@[simp]
theorem withZeroUnitsEquiv_symm_coe {S : Type*} [Semifield S] [Subsingleton (AddUnits S)]
    (u : Sˣ) :
    (withZeroUnitsEquiv S).symm (u : S) = u :=
  (withZeroUnitsEquiv S).symm_apply_apply u

theorem withZeroUnitsEquiv_symm_of_ne_zero {S : Type*} [Semifield S] [Subsingleton (AddUnits S)]
    {s : S} (hs : s ≠ 0) :
    (withZeroUnitsEquiv S).symm s = Units.mk0 s hs := by
  apply (withZeroUnitsEquiv S).injective
  simp

end Comparisons

end CoefficientSemifield

namespace CoefficientSemifieldHom

open CoefficientSemifield

section UnitsMap

variable {S T U : Type*} [Semifield S] [Subsingleton (AddUnits S)]
  [Semifield T] [Subsingleton (AddUnits T)] [Semifield U] [Subsingleton (AddUnits U)]

/-- Restriction of a semiring homomorphism between zero-sum-free semifields to their unit groups,
as a homomorphism of coefficient semifields. -/
def unitsMap (F : S →+* T) : CoefficientSemifieldHom Sˣ Tˣ where
  __ := Units.map F.toMonoidHom
  map_add' a b := Units.ext (map_add F (a : S) (b : S))

@[simp, norm_cast]
theorem val_unitsMap (F : S →+* T) (u : Sˣ) :
    ((unitsMap F u : Tˣ) : T) = F u :=
  (rfl)

@[simp]
theorem unitsMap_id : unitsMap (RingHom.id S) = .id Sˣ := by
  ext u
  simp

@[simp]
theorem unitsMap_comp (G : T →+* U) (F : S →+* T) :
    unitsMap (G.comp F) = (unitsMap G).comp (unitsMap F) := by
  ext u
  simp

end UnitsMap

section LiftWithZero

variable {P Q R : Type*} [CoefficientSemifield P] [CoefficientSemifield Q] [CoefficientSemifield R]
  {S T : Type*} [Semifield S] [Subsingleton (AddUnits S)]
  [Semifield T] [Subsingleton (AddUnits T)]

/-- Extend a coefficient-semifield homomorphism `P → Sˣ` by `0 ↦ 0` to a semiring homomorphism
`WithZero P →+* S`. -/
def liftWithZero (f : CoefficientSemifieldHom P Sˣ) : WithZero P →+* S where
  __ := WithZero.lift' ((Units.coeHom S).comp f.toMonoidHom)
  map_add' x y := by
    induction x <;> induction y <;> simp [← WithZero.coe_add, map_add]

@[simp]
theorem liftWithZero_coe (f : CoefficientSemifieldHom P Sˣ) (p : P) :
    liftWithZero f p = f p :=
  (rfl)

/-- Extension by zero and restriction to units identify `CoefficientSemifieldHom P Sˣ` with
`WithZero P →+* S`. -/
def liftWithZeroEquiv : CoefficientSemifieldHom P Sˣ ≃ (WithZero P →+* S) where
  toFun := liftWithZero
  invFun F := (unitsMap F).comp (toUnitsWithZero P).toCoefficientSemifieldHom
  left_inv f := by
    ext p
    simp
  right_inv F := by
    ext x
    induction x <;> simp

@[simp]
theorem liftWithZeroEquiv_apply (f : CoefficientSemifieldHom P Sˣ) :
    liftWithZeroEquiv f = liftWithZero f :=
  (rfl)

@[simp, norm_cast]
theorem val_liftWithZeroEquiv_symm_apply (F : WithZero P →+* S) (p : P) :
    ((liftWithZeroEquiv.symm F p : Sˣ) : S) = F p := by
  simp [liftWithZeroEquiv]

theorem comp_liftWithZero (G : S →+* T) (f : CoefficientSemifieldHom P Sˣ) :
    G.comp (liftWithZero f) = liftWithZero ((unitsMap G).comp f) := by
  ext x
  induction x <;> simp

/-! ### Functoriality of `WithZero` and compatibility with comparisons -/

/-- Extend `f : CoefficientSemifieldHom P Q` by `0 ↦ 0` to `WithZero P →+* WithZero Q`. -/
def mapWithZero (f : CoefficientSemifieldHom P Q) : WithZero P →+* WithZero Q :=
  liftWithZero ((toUnitsWithZero Q).toCoefficientSemifieldHom.comp f)

@[simp]
theorem mapWithZero_coe (f : CoefficientSemifieldHom P Q) (p : P) :
    mapWithZero f p = f p := by
  simp [mapWithZero]

@[simp]
theorem mapWithZero_id : mapWithZero (.id P) = RingHom.id (WithZero P) := by
  ext x
  induction x <;> simp

@[simp]
theorem mapWithZero_comp (g : CoefficientSemifieldHom Q R) (f : CoefficientSemifieldHom P Q) :
    mapWithZero (g.comp f) = (mapWithZero g).comp (mapWithZero f) := by
  ext x
  induction x <;> simp

/-- Restricting `mapWithZero f` to units intertwines `toUnitsWithZero P` and `toUnitsWithZero Q`. -/
@[simp]
theorem unitsMap_mapWithZero_comp_toUnitsWithZero (f : CoefficientSemifieldHom P Q) :
    (unitsMap (mapWithZero f)).comp (toUnitsWithZero P).toCoefficientSemifieldHom =
      (toUnitsWithZero Q).toCoefficientSemifieldHom.comp f := by
  ext p
  simp

@[simp]
theorem unitsMap_mapWithZero_toUnitsWithZero (f : CoefficientSemifieldHom P Q) (p : P) :
    unitsMap (mapWithZero f) (toUnitsWithZero P p) = toUnitsWithZero Q (f p) :=
  Units.ext (by simp)

/-- Lift an addition- and multiplication-preserving equivalence `P ≃+* Q` of coefficient semifields
by `0 ↦ 0` to `WithZero P ≃+* WithZero Q`. -/
def _root_.TauCeti.CoefficientSemifield.withZeroCongr (e : P ≃+* Q) :
    WithZero P ≃+* WithZero Q :=
  RingEquiv.ofRingHom
    (mapWithZero e.toCoefficientSemifieldHom)
    (mapWithZero e.symm.toCoefficientSemifieldHom)
    (by rw [← mapWithZero_comp, RingEquiv.toCoefficientSemifieldHom_comp_symm, mapWithZero_id])
    (by rw [← mapWithZero_comp, RingEquiv.symm_comp_toCoefficientSemifieldHom, mapWithZero_id])

@[simp]
theorem _root_.TauCeti.CoefficientSemifield.withZeroCongr_coe (e : P ≃+* Q) (p : P) :
    withZeroCongr e p = e p := by
  simp [withZeroCongr]

@[simp]
theorem _root_.TauCeti.CoefficientSemifield.withZeroCongr_symm (e : P ≃+* Q) :
    (withZeroCongr e).symm = withZeroCongr e.symm :=
  (rfl)

/-- Extension by zero and restriction to units identify homomorphisms of coefficient semifields
with semiring homomorphisms between their zero adjunctions. -/
def mapWithZeroEquiv : CoefficientSemifieldHom P Q ≃ (WithZero P →+* WithZero Q) where
  toFun := mapWithZero
  invFun F :=
    (toUnitsWithZero Q).symm.toCoefficientSemifieldHom.comp
      ((unitsMap F).comp (toUnitsWithZero P).toCoefficientSemifieldHom)
  left_inv f := by
    ext p
    simp [comp_apply]
  right_inv F := by
    ext x
    induction x <;> simp

@[simp]
theorem mapWithZeroEquiv_apply (f : CoefficientSemifieldHom P Q) :
    mapWithZeroEquiv f = mapWithZero f :=
  (rfl)

@[simp]
theorem mapWithZeroEquiv_symm_apply (F : WithZero P →+* WithZero Q) (p : P) :
    mapWithZeroEquiv.symm F p =
      (toUnitsWithZero Q).symm (unitsMap F (toUnitsWithZero P p)) := by
  simp [mapWithZeroEquiv]

/-- Extending `unitsMap F` by zero intertwines `withZeroUnitsEquiv S` and `withZeroUnitsEquiv T`. -/
@[simp]
theorem liftWithZero_unitsMap (F : S →+* T) :
    liftWithZero (unitsMap F) = F.comp (withZeroUnitsEquiv S : WithZero Sˣ →+* S) := by
  ext x
  induction x <;> simp

@[simp]
theorem withZeroUnitsEquiv_comp_mapWithZero_unitsMap (F : S →+* T) :
    (withZeroUnitsEquiv T : WithZero Tˣ →+* T).comp (mapWithZero (unitsMap F)) =
      F.comp (withZeroUnitsEquiv S : WithZero Sˣ →+* S) := by
  ext x
  induction x <;> simp

/-- Restriction to units and extension by zero identify semiring homomorphisms between
zero-sum-free semifields with coefficient-semifield homomorphisms between their unit groups. -/
noncomputable def unitsMapEquiv : (S →+* T) ≃ CoefficientSemifieldHom Sˣ Tˣ where
  toFun := unitsMap
  invFun g := (liftWithZero g).comp ((withZeroUnitsEquiv S).symm : S →+* WithZero Sˣ)
  left_inv F := by
    ext s
    by_cases hs : s = 0
    · simp [hs]
    · simp [withZeroUnitsEquiv_symm_of_ne_zero hs]
  right_inv g := by
    ext u
    simp

@[simp]
theorem unitsMapEquiv_apply (F : S →+* T) :
    unitsMapEquiv F = unitsMap F :=
  (rfl)

end LiftWithZero

end CoefficientSemifieldHom

/-! ### Checks -/

-- `ℕ` is zero-sum-free, yet `1 + 1 = 2` is not a unit in `ℕ`; a nontrivial ring (`ℤ`) is not
-- zero-sum-free.
example : Subsingleton (AddUnits ℕ) ∧ ¬ IsUnit ((1 : ℕ) + 1) ∧ ¬ Subsingleton (AddUnits ℤ) :=
  ⟨inferInstance, by decide, not_subsingleton_addUnits_of_nontrivial ℤ⟩

-- Both round trips (`P ≃+* (WithZero P)ˣ` and `WithZero Sˣ ≃+* S`) preserve auxiliary addition
-- using the given operations without changing instances.
example {P : Type*} [CoefficientSemifield P] (a b : P) :
    (CoefficientSemifield.toUnitsWithZero P).symm
        (CoefficientSemifield.toUnitsWithZero P a + CoefficientSemifield.toUnitsWithZero P b) =
      a + b := by
  simp [← map_add]

example {S : Type*} [Semifield S] [Subsingleton (AddUnits S)] (x y : S) :
    CoefficientSemifield.withZeroUnitsEquiv S
        ((CoefficientSemifield.withZeroUnitsEquiv S).symm x +
          (CoefficientSemifield.withZeroUnitsEquiv S).symm y) =
      x + y := by
  simp [← map_add]

end TauCeti
