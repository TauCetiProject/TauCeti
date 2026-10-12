/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.Picard
public import TauCeti.RingTheory.FractionalIdeal.Basic
public import Mathlib.GroupTheory.Congruence.Hom
import TauCeti.RingTheory.FractionalIdeal.Operations

/-!
# The ideal class monoid of a number-field order

The nonzero fractional ideals of an order `O` in a number field `K` form a commutative monoid under
multiplication, but when `O` is not the maximal order some of them are not invertible, so they
cannot all be classes in the Picard group `Pic O`. Two nonzero fractional ideals are *homothetic*
when one is a nonzero scalar multiple of the other. The ideal class monoid `IdealClassMonoid O` is
the quotient of the monoid of nonzero fractional ideals by homothety. Every nonzero fractional
ideal has a class here, including the proper noninvertible ideals of a non-Gorenstein order, and no
class is given an inverse it does not have: a class is a unit exactly when its representatives are
invertible fractional ideals, and the unit group of the ideal class monoid is the Picard group.

## Main definitions

* `TauCeti.GlobalNumberFields.NumberFieldOrder.homothetyCon`: the homothety congruence on the
  nonzero fractional ideals of an order.
* `TauCeti.GlobalNumberFields.IdealClassMonoid`: the ideal class monoid of an order.
* `TauCeti.GlobalNumberFields.IdealClassMonoid.mk`: the class of a nonzero fractional ideal.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.mkIdealClassMonoid`: the class of a proper
  fractional ideal.
* `TauCeti.GlobalNumberFields.IdealClassMonoid.lift`: the universal property of the quotient.
* `TauCeti.GlobalNumberFields.IdealClassMonoid.multiplierRing`: the multiplier ring of a class,
  with `IdealClassMonoid.IsProper` for the classes of proper fractional ideals.
* `TauCeti.GlobalNumberFields.IdealClassMonoid.picEquivUnits`: the Picard group of an order is the
  unit group of its ideal class monoid.

## Main results

* `TauCeti.GlobalNumberFields.IdealClassMonoid.mk_eq_mk_iff`: two nonzero fractional ideals have
  the same class exactly when they are homothetic.
* `TauCeti.GlobalNumberFields.IdealClassMonoid.mk_eq_one_iff`: the class of a nonzero fractional
  ideal is trivial exactly when the ideal is principal.
* `TauCeti.GlobalNumberFields.IdealClassMonoid.isUnit_mk_iff`: the class of a nonzero fractional
  ideal is a unit exactly when the ideal is invertible.

## References

* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
-/

public section
noncomputable section

open FractionalIdeal
open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

namespace NumberFieldOrder

variable (O : NumberFieldOrder K)

/-- The monoid of nonzero fractional ideals of an order. Unlike
`NumberFieldOrder.invertibleProperFractionalIdeals`, it contains the noninvertible ideals.
Membership is nonvanishing, by `mem_nonZeroDivisors_iff_ne_zero`. -/
abbrev nonzeroFractionalIdeals := (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)⁰

/-- Two nonzero fractional ideals of an order are homothetic when one is a nonzero scalar multiple
of the other. Homothety is a congruence on the monoid of nonzero fractional ideals. -/
def homothetyCon : Con O.nonzeroFractionalIdeals where
  r I J := ∃ x : Kˣ, spanSingleton (nonZeroDivisors O.toSubalgebra) (x : K) *
    (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) = J
  iseqv :=
    { refl I := ⟨1, by rw [Units.val_one, spanSingleton_one, one_mul]⟩
      symm := by
        rintro I J ⟨x, hx⟩
        refine ⟨x⁻¹, ?_⟩
        rw [← hx, spanSingleton_inv_mul_cancel_left]
      trans := by
        rintro I J L ⟨x, hx⟩ ⟨y, hy⟩
        refine ⟨y * x, ?_⟩
        rw [← hy, ← hx, ← mul_assoc, spanSingleton_mul_spanSingleton, Units.val_mul] }
  mul' := by
    rintro I I' J J' ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨x * y, ?_⟩
    rw [Submonoid.coe_mul, Submonoid.coe_mul, ← hx, ← hy, Units.val_mul,
      ← spanSingleton_mul_spanSingleton]
    ring

/-- Two nonzero fractional ideals are homothetic exactly when one is a nonzero scalar multiple of
the other. -/
theorem homothetyCon_iff {I J : O.nonzeroFractionalIdeals} :
    O.homothetyCon I J ↔ ∃ x : Kˣ, spanSingleton (nonZeroDivisors O.toSubalgebra) (x : K) *
      (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) = J :=
  Iff.rfl

end NumberFieldOrder

/-- The ideal class monoid of an order: its nonzero fractional ideals up to homothety. Noninvertible
fractional ideals have a class here, and `IdealClassMonoid.picEquivUnits` identifies the unit group
with the Picard group `Pic O`. -/
def IdealClassMonoid (O : NumberFieldOrder K) : Type _ :=
  O.homothetyCon.Quotient

instance (O : NumberFieldOrder K) : CommMonoid (IdealClassMonoid O) :=
  inferInstanceAs (CommMonoid O.homothetyCon.Quotient)

instance (O : NumberFieldOrder K) : Inhabited (IdealClassMonoid O) := ⟨1⟩

namespace IdealClassMonoid

variable (O : NumberFieldOrder K)

/-- The ideal class of a nonzero fractional ideal of an order. -/
def mk : O.nonzeroFractionalIdeals →* IdealClassMonoid O :=
  O.homothetyCon.mk'

/-- Every ideal class has a nonzero fractional-ideal representative. -/
theorem mk_surjective : Function.Surjective (mk O) :=
  Con.mk'_surjective

/-- To prove a statement about every ideal class, it suffices to prove it for the class of each
nonzero fractional ideal. -/
@[elab_as_elim]
theorem induction_on {P : IdealClassMonoid O → Prop} (c : IdealClassMonoid O)
    (h : ∀ I : O.nonzeroFractionalIdeals, P (mk O I)) : P c :=
  Con.induction_on c h

/-- Two nonzero fractional ideals have the same ideal class exactly when they are homothetic. -/
@[simp]
theorem mk_eq_mk_iff {I J : O.nonzeroFractionalIdeals} :
    mk O I = mk O J ↔ ∃ x : Kˣ, spanSingleton (nonZeroDivisors O.toSubalgebra) (x : K) *
      (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) = J :=
  Con.eq _

/-- The ideal class of a nonzero fractional ideal is trivial exactly when the ideal is principal. -/
@[simp]
theorem mk_eq_one_iff {I : O.nonzeroFractionalIdeals} :
    mk O I = 1 ↔ ∃ x : Kˣ, spanSingleton (nonZeroDivisors O.toSubalgebra) (x : K) =
      (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) := by
  rw [← map_one (mk O), eq_comm, mk_eq_mk_iff]
  simp

/-- The ideal class of a nonzero fractional ideal is a unit of the ideal class monoid exactly when
the ideal is invertible. Noninvertible ideals therefore have classes that are not units. -/
@[simp]
theorem isUnit_mk_iff {I : O.nonzeroFractionalIdeals} :
    IsUnit (mk O I) ↔ IsUnit (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨J, hJ⟩ := mk_surjective O (u⁻¹ : (IdealClassMonoid O)ˣ)
    have hIJ : mk O (I * J) = 1 := by
      rw [map_mul, ← hu, hJ, Units.mul_inv]
    obtain ⟨x, hx⟩ := (mk_eq_one_iff O).mp hIJ
    have hx' : IsUnit (spanSingleton (nonZeroDivisors O.toSubalgebra) (x : K)) :=
      isUnit_spanSingleton x.isUnit
    rw [hx, Submonoid.coe_mul] at hx'
    exact isUnit_of_mul_isUnit_left hx'
  · intro hI
    obtain ⟨J, hJ⟩ := hI.exists_right_inv
    have hJ0 : J ≠ 0 := ne_zero_of_mul_eq_one J I (by rwa [mul_comm])
    have hIJ : I * ⟨J, mem_nonZeroDivisors_of_ne_zero hJ0⟩ = 1 := Subtype.ext hJ
    exact (IsUnit.of_mul_eq_one _ hIJ).map (mk O)

section Lift

variable {M : Type*} [Monoid M]

/-- **The universal property of the ideal class monoid.** A homomorphism on nonzero fractional
ideals that is constant on homothety classes descends to the ideal class monoid. -/
def lift (φ : O.nonzeroFractionalIdeals →* M) (h : O.homothetyCon ≤ Con.ker φ) :
    IdealClassMonoid O →* M :=
  Con.lift O.homothetyCon φ h

/-- The descended homomorphism agrees with the original one on ideal classes. -/
@[simp]
theorem lift_mk (φ : O.nonzeroFractionalIdeals →* M) (h : O.homothetyCon ≤ Con.ker φ)
    (I : O.nonzeroFractionalIdeals) : lift O φ h (mk O I) = φ I :=
  Con.lift_coe h I

/-- A homomorphism out of the ideal class monoid is determined by its values on the classes of
nonzero fractional ideals. -/
theorem lift_unique (φ : O.nonzeroFractionalIdeals →* M) (h : O.homothetyCon ≤ Con.ker φ)
    (ψ : IdealClassMonoid O →* M) (hψ : ∀ I, ψ (mk O I) = φ I) : ψ = lift O φ h :=
  Con.lift_unique h ψ (MonoidHom.ext hψ)

end Lift

variable {O}

/-- The multiplier ring of an ideal class: the common multiplier ring of its representatives, which
`NumberFieldOrder.multiplierRing_mul_spanSingleton` shows is unchanged by homothety. -/
def multiplierRing (c : IdealClassMonoid O) : Subring K :=
  Con.liftOn c (fun I => O.multiplierRing I) fun I J h => by
    obtain ⟨x, hx⟩ := h
    rw [← hx, mul_comm, O.multiplierRing_mul_spanSingleton _ x.ne_zero]

/-- The multiplier ring of the class of a nonzero fractional ideal is its multiplier ring. -/
@[simp]
theorem multiplierRing_mk (I : O.nonzeroFractionalIdeals) :
    (mk O I).multiplierRing = O.multiplierRing I :=
  Con.liftOn_coe _ _ _ I

/-- An ideal class is proper when its multiplier ring is the order, that is, when its
representatives are proper fractional ideals. -/
def IsProper (c : IdealClassMonoid O) : Prop :=
  c.multiplierRing = O.toSubalgebra.toSubring

/-- Properness of an ideal class is equality of its multiplier ring with the order. -/
theorem isProper_def (c : IdealClassMonoid O) :
    c.IsProper ↔ c.multiplierRing = O.toSubalgebra.toSubring :=
  Iff.rfl

/-- The class of a nonzero fractional ideal is proper exactly when the ideal is. -/
@[simp]
theorem isProper_mk_iff {I : O.nonzeroFractionalIdeals} :
    (mk O I).IsProper ↔ O.IsProperFractionalIdeal I := by
  rw [isProper_def, multiplierRing_mk, O.isProperFractionalIdeal_def]

/-- Every unit of the ideal class monoid is a proper class; the converse fails for non-Gorenstein
orders, whose proper noninvertible ideals have proper nonunit classes. -/
theorem isProper_of_isUnit {c : IdealClassMonoid O} (hc : IsUnit c) : c.IsProper := by
  induction c using induction_on with
  | h I =>
    rw [isUnit_mk_iff] at hc
    exact isProper_mk_iff.mpr (O.isProperFractionalIdeal_of_isUnit hc)

variable (O)

/-- The unit of the ideal class monoid given by the class of an invertible fractional ideal. -/
def unitsMk : O.invertibleProperFractionalIdeals →* (IdealClassMonoid O)ˣ :=
  (Units.map (mk O)).comp unitsNonZeroDivisorsEquiv.symm.toMonoidHom

/-- The unit attached to an invertible fractional ideal is its ideal class. -/
@[simp]
theorem coe_unitsMk (I : O.invertibleProperFractionalIdeals) :
    (unitsMk O I : IdealClassMonoid O) = mk O ⟨I, I.isUnit.mem_nonZeroDivisors⟩ :=
  (Units.coe_map _ _).trans
    (congrArg (mk O) (Subtype.ext (val_unitsNonZeroDivisorsEquiv_symm_apply_coe I)))

/-- Every unit of the ideal class monoid is the class of an invertible fractional ideal. -/
theorem unitsMk_surjective : Function.Surjective (unitsMk O) := by
  intro u
  obtain ⟨I, hI⟩ := mk_surjective O (u : IdealClassMonoid O)
  have hI' : IsUnit (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) :=
    (isUnit_mk_iff O).mp (hI ▸ u.isUnit)
  refine ⟨hI'.unit, Units.ext ?_⟩
  rw [coe_unitsMk, ← hI]
  exact congrArg (mk O) (Subtype.ext hI'.unit_spec)

/-- An invertible fractional ideal has trivial unit class exactly when it is principal: the kernel
of `unitsMk` is the image of `Kˣ` under `toPrincipalIdeal`. -/
theorem ker_unitsMk : (unitsMk O).ker = (toPrincipalIdeal O.toSubalgebra K).range := by
  ext I
  rw [MonoidHom.mem_ker, MonoidHom.mem_range, Units.ext_iff, Units.val_one, coe_unitsMk,
    mk_eq_one_iff]
  simp only [toPrincipalIdeal_eq_iff]

/-- **The Picard group is the unit group of the ideal class monoid.** The class of an invertible
fractional ideal in `Pic O` corresponds to its class in `IdealClassMonoid O`. -/
def picEquivUnits : Pic O ≃* (IdealClassMonoid O)ˣ :=
  (ClassGroup.equiv K).trans
    ((QuotientGroup.quotientMulEquivOfEq (ker_unitsMk O).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (unitsMk_surjective O)))

/-- The Picard class of an invertible fractional ideal corresponds to its unit class in the ideal
class monoid. -/
@[simp]
theorem picEquivUnits_mkPic (I : O.invertibleProperFractionalIdeals) :
    picEquivUnits O (O.mkPic I) = unitsMk O I := by
  have hI : Units.mapEquiv (MulEquiv.refl (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)) I
      = I := Units.ext (Units.coe_mapEquiv _ I)
  simp only [picEquivUnits, NumberFieldOrder.mkPic, MulEquiv.trans_apply, ClassGroup.equiv_mk,
    canonicalEquiv_self, RingEquiv.coe_mulEquiv_refl, hI, QuotientGroup.mk'_apply,
    QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse_apply, QuotientGroup.kerLift_mk]

end IdealClassMonoid

namespace NumberFieldOrder

variable (O : NumberFieldOrder K)

/-- The ideal class of a proper fractional ideal of an order. Proper fractional ideals are nonzero,
so no separate nonvanishing hypothesis is needed. -/
def mkIdealClassMonoid (I : O.properFractionalIdeals) : IdealClassMonoid O :=
  IdealClassMonoid.mk O ⟨I, mem_nonZeroDivisors_of_ne_zero I.2.ne_zero⟩

/-- The class of a proper fractional ideal is its class as a nonzero fractional ideal. -/
@[simp]
theorem mkIdealClassMonoid_eq_mk (I : O.properFractionalIdeals) :
    O.mkIdealClassMonoid I =
      IdealClassMonoid.mk O ⟨I, mem_nonZeroDivisors_of_ne_zero I.2.ne_zero⟩ := by
  rfl

end NumberFieldOrder

end TauCeti.GlobalNumberFields
