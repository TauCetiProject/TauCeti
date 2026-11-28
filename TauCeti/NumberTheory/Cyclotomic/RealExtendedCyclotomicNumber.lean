/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Cyclotomic.CompatibleTower.Real
public import TauCeti.NumberTheory.Cyclotomic.ExtendedCyclotomicNumber
public import TauCeti.NumberTheory.NumberField.Cyclotomic.MaximalRealSubfield

import Mathlib.RingTheory.Norm.Transitivity
import TauCeti.RingTheory.Norm.Equiv

/-!
# Real extended cyclotomic numbers

In a compatible rational cyclotomic tower write `K_m = ℚ(ζ_m)` and `K_m⁺` for its
maximal real subfield. The real extended cyclotomic number `c_m⁺` is the norm to `K_m⁺`
of the extended number `c_m = N_{K_{mp}/K_m}(1 - ζ_{mp})`. For `m > 2` this norm
is a product of two complex conjugates. At conductors one and two it is the identity.

Norm transitivity in the square of full and real fields carries the norm relations of
`c_m` to `c_m⁺`. At a prime `ℓ ∤ mp` with `mp > 1`, the Euler factor acts through the restriction
of the inverse arithmetic Frobenius on `K_m` to `K_m⁺`. These are the norm relations
used to build the cyclotomic Euler system over the real fields.

The conductor formulas specialize
`TauCeti.IsCyclotomicExtension.Rat.algebraMap_norm_maximalRealSubfield_of_le_two` and
`NumberField.IsCMField.complexEmbedding_algebraMap_norm`. The descent uses
`TauCeti.CompatibleCyclotomicTower.norm_extendedCyclotomicNumber_mul_of_dvd`,
`TauCeti.CompatibleCyclotomicTower.norm_extendedCyclotomicNumber_mul_eq_div`, and
`AlgEquiv.restrictNormal_norm`. The identification of the residue-class automorphism with
arithmetic Frobenius is
`TauCeti.NumberField.isArithFrobAt_iff_galEquivZMod_eq_unitOfCoprime`, and
`IsArithFrobAt.restrictNormal` gives its action on the real subfield.

## References

* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Chapter III, §2.1.
-/

public section

noncomputable section

open ComplexConjugate IntermediateField _root_.NumberField Polynomial
open IsCyclotomicExtension.Rat

namespace TauCeti.CompatibleCyclotomicTower

variable {Ω : Type*} [Field Ω] [CharZero Ω] (T : CompatibleCyclotomicTower Ω)

variable (p m : ℕ) [NeZero m]

/-- The real extended cyclotomic number `c_m⁺`, obtained by taking the relative norm of
`c_m` to the maximal real subfield. -/
def realExtendedCyclotomicNumber [NeZero p] : T.realField m :=
  Algebra.norm (T.realField m) (T.extendedCyclotomicNumber ℚ p m)

/-- The norm from the full cyclotomic field to its maximal real subfield sends `c_m` to
`c_m⁺`. -/
@[simp]
theorem norm_extendedCyclotomicNumber_realField [NeZero p] :
    Algebra.norm (T.realField m) (T.extendedCyclotomicNumber ℚ p m) =
      T.realExtendedCyclotomicNumber p m :=
  (rfl)

/-- The real extended cyclotomic number is nonzero whenever `mp > 1`. -/
theorem realExtendedCyclotomicNumber_ne_zero [NeZero p] (h : m * p ≠ 1) :
    T.realExtendedCyclotomicNumber p m ≠ 0 := by
  rw [← T.norm_extendedCyclotomicNumber_realField]
  exact Algebra.norm_ne_zero_iff.mpr (T.extendedCyclotomicNumber_ne_zero ℚ p m h)

/-- The real extended cyclotomic number as a unit, for `mp > 1`. -/
def realExtendedCyclotomicUnit [NeZero p] (h : m * p ≠ 1) : (T.realField m)ˣ :=
  Units.mk0 _ (T.realExtendedCyclotomicNumber_ne_zero p m h)

/-- The unit-valued family has the underlying real extended cyclotomic number as its value. -/
@[simp]
theorem coe_realExtendedCyclotomicUnit [NeZero p] (h : m * p ≠ 1) :
    (T.realExtendedCyclotomicUnit p m h : T.realField m) =
      T.realExtendedCyclotomicNumber p m :=
  (rfl)

/-- At levels above two, `c_m⁺` is the product of `c_m` and its complex conjugate. -/
theorem complexEmbedding_realExtendedCyclotomicNumber_of_two_lt [NeZero p]
    (hm : 2 < m) (φ : T.field ℚ m →+* ℂ) :
    φ (algebraMap (T.realField m) (T.field ℚ m) (T.realExtendedCyclotomicNumber p m)) =
      φ (T.extendedCyclotomicNumber ℚ p m) * conj (φ (T.extendedCyclotomicNumber ℚ p m)) := by
  have := _root_.IsCyclotomicExtension.Rat.isCMField (T.field ℚ m) ⟨m, Set.mem_singleton m, hm⟩
  exact _root_.NumberField.IsCMField.complexEmbedding_algebraMap_norm φ _

/-- At levels above two every complex embedding sends `c_m⁺` to a number with positive real part. -/
theorem re_complexEmbedding_realExtendedCyclotomicNumber_pos [NeZero p]
    (hm : 2 < m) (φ : T.field ℚ m →+* ℂ) :
    0 < (φ (algebraMap (T.realField m) (T.field ℚ m) (T.realExtendedCyclotomicNumber p m))).re := by
  have hmp : 1 < m * p :=
    (by omega : 1 < m).trans_le (Nat.le_mul_of_pos_right _ (NeZero.pos p))
  rw [T.complexEmbedding_realExtendedCyclotomicNumber_of_two_lt p m hm φ, Complex.mul_conj,
    Complex.ofReal_re, Complex.normSq_pos]
  exact (_root_.map_ne_zero φ).2 (T.extendedCyclotomicNumber_ne_zero ℚ p m hmp.ne')

/-- At levels one and two the real norm has degree one, so `c_m⁺` maps to `c_m`. -/
theorem algebraMap_realExtendedCyclotomicNumber_of_le_two [NeZero p] (hm : m ≤ 2) :
    algebraMap (T.realField m) (T.field ℚ m) (T.realExtendedCyclotomicNumber p m) =
      T.extendedCyclotomicNumber ℚ p m := by
  exact IsCyclotomicExtension.Rat.algebraMap_norm_maximalRealSubfield_of_le_two m hm _

/-- At conductor one the real number equals the prime `p`. -/
@[simp]
theorem realExtendedCyclotomicNumber_one [Fact p.Prime] :
    T.realExtendedCyclotomicNumber p 1 = p := by
  apply (algebraMap (T.realField 1) (T.field ℚ 1)).injective
  rw [T.algebraMap_realExtendedCyclotomicNumber_of_le_two p 1 (by decide), map_natCast,
    T.extendedCyclotomicNumber_one ℚ (cyclotomic.irreducible_rat (NeZero.pos p))]

variable {p m} {ℓ : ℕ}

/-- If `ℓ ∣ mp`, the norm from level `mℓ` to `m` carries `c_{mℓ}⁺` to `c_m⁺`.
This includes the prime used to extend the family. -/
theorem norm_realExtendedCyclotomicNumber_mul_of_dvd [NeZero p] [NeZero ℓ] (h : ℓ ∣ m * p) :
    letI := T.realFieldAlgebra (dvd_mul_right m ℓ)
    Algebra.norm (T.realField m) (T.realExtendedCyclotomicNumber p (m * ℓ)) =
      T.realExtendedCyclotomicNumber p m := by
  let := T.realFieldAlgebra (dvd_mul_right m ℓ)
  let := T.fieldAlgebra ℚ (dvd_mul_right m ℓ)
  rw [← T.norm_extendedCyclotomicNumber_realField p (m * ℓ),
    NumberField.norm_norm_maximalRealSubfield_comm (T.field ℚ m) (T.field ℚ (m * ℓ)),
    T.norm_extendedCyclotomicNumber_mul_of_dvd ℚ (cyclotomic.irreducible_rat (NeZero.pos _)) h,
    T.norm_extendedCyclotomicNumber_realField]

/-- At a prime `ℓ ∤ mp` with `mp > 1`, the norm from level `mℓ` to `m` is the quotient of `c_m⁺`
by its inverse arithmetic Frobenius conjugate in the real cyclotomic field. -/
theorem norm_realExtendedCyclotomicNumber_mul_eq_div [NeZero p] [Fact ℓ.Prime]
    (hcop : ℓ.Coprime (m * p)) (hmp : 1 < m * p) :
    letI := T.realFieldAlgebra (dvd_mul_right m ℓ)
    Algebra.norm (T.realField m) (T.realExtendedCyclotomicNumber p (m * ℓ)) =
      T.realExtendedCyclotomicNumber p m /
        ((galEquivZMod m (T.field ℚ m)).symm
          (ZMod.unitOfCoprime ℓ (hcop.coprime_dvd_right (dvd_mul_right m p)))⁻¹).restrictNormal
            (T.realField m) (T.realExtendedCyclotomicNumber p m) := by
  let := T.realFieldAlgebra (dvd_mul_right m ℓ)
  let := T.fieldAlgebra ℚ (dvd_mul_right m ℓ)
  rw [← T.norm_extendedCyclotomicNumber_realField p (m * ℓ),
    NumberField.norm_norm_maximalRealSubfield_comm (T.field ℚ m) (T.field ℚ (m * ℓ)),
    T.norm_extendedCyclotomicNumber_mul_eq_div ℚ (cyclotomic.irreducible_rat (NeZero.pos _))
      (cyclotomic.irreducible_rat (NeZero.pos _)) hcop hmp]
  simp only [map_div' (Algebra.norm _) Algebra.norm_inv,
    ← T.norm_extendedCyclotomicNumber_realField, AlgEquiv.restrictNormal_norm]

end TauCeti.CompatibleCyclotomicTower
