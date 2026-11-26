/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
`c_m` to `c_m⁺`. At a prime `ℓ ∤ mp`, the Euler factor acts through the restriction
of the inverse arithmetic Frobenius on `K_m` to `K_m⁺`. These are the norm relations
used to build the cyclotomic Euler system over the real fields.

## References

* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Chapter III, §2.1.
-/

public section

noncomputable section

open ComplexConjugate IntermediateField NumberField Polynomial
open IsCyclotomicExtension.Rat

namespace TauCeti.CompatibleCyclotomicTower

variable {Ω : Type*} [Field Ω] [CharZero Ω] (T : CompatibleCyclotomicTower Ω)

/-- The maximal real subfield of the rational cyclotomic field at level `m`. -/
abbrev realField (m : ℕ) [NeZero m] : Subfield (T.field ℚ m) :=
  maximalRealSubfield (T.field ℚ m)

/-- The real cyclotomic field is abelian over `ℚ`. -/
instance isAbelianGalois_realField (m : ℕ) [NeZero m] : IsAbelianGalois ℚ (T.realField m) := by
  have := IsCyclotomicExtension.isAbelianGalois {m} ℚ (T.field ℚ m)
  exact IsAbelianGalois.of_algHom (T.realField m).subtype.toRatAlgHom

/-- For `m ∣ n`, the algebra on `K_n⁺` over `K_m⁺` given by restricting the inclusion of
the full cyclotomic fields. -/
abbrev realFieldAlgebra {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n) :
    Algebra (T.realField m) (T.realField n) :=
  let f := (inclusion (T.field_le ℚ h)).toRingHom
  (f.restrict (T.realField m) (T.realField n) fun x hx ↦
    (mem_maximalRealSubfield_iff (f x)).2 fun φ ↦
      (mem_maximalRealSubfield_iff x).1 hx (φ.comp f)).toAlgebra

/-- The inclusion of real fields is the restriction of the inclusion of full fields. -/
@[simp]
theorem coe_algebraMap_realField {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n)
    (x : T.realField m) :
    letI := T.realFieldAlgebra h
    letI := T.fieldAlgebra ℚ h
    ((algebraMap (T.realField m) (T.realField n) x : T.realField n) : T.field ℚ n) =
      algebraMap (T.field ℚ m) (T.field ℚ n) (x : T.field ℚ m) :=
  (rfl)

/-- Taking norms to the maximal real subfields commutes with taking norms down the
cyclotomic tower. -/
theorem norm_realField_norm {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n) (x : T.field ℚ n) :
    letI := T.realFieldAlgebra h
    letI := T.fieldAlgebra ℚ h
    Algebra.norm (T.realField m) (Algebra.norm (T.realField n) x) =
      Algebra.norm (T.realField m) (Algebra.norm (T.field ℚ m) x) := by
  let := T.realFieldAlgebra h
  let := T.fieldAlgebra ℚ h
  let : Algebra (T.realField m) (T.field ℚ n) :=
    ((algebraMap (T.field ℚ m) (T.field ℚ n)).comp (T.realField m).subtype).toAlgebra
  have hreal : IsScalarTower (T.realField m) (T.realField n) (T.field ℚ n) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hfull : IsScalarTower (T.realField m) (T.field ℚ m) (T.field ℚ n) :=
    IsScalarTower.of_algebraMap_eq' rfl
  calc
    _ = Algebra.norm (T.realField m) x :=
      @Algebra.norm_norm _ _ _ _ _ _ _ _ _ _ hreal _ x
    _ = _ := (@Algebra.norm_norm _ _ _ _ _ _ _ _ _ _ hfull _ x).symm

variable (p m : ℕ) [NeZero p] [NeZero m]

/-- The real extended cyclotomic number `c_m⁺`, obtained by taking the relative norm of
`c_m` to the maximal real subfield. -/
def realExtendedCyclotomicNumber : T.realField m :=
  Algebra.norm (T.realField m) (T.extendedCyclotomicNumber ℚ p m)

/-- The norm from the full cyclotomic field to its maximal real subfield sends `c_m` to
`c_m⁺`. -/
theorem realExtendedCyclotomicNumber_def :
    T.realExtendedCyclotomicNumber p m =
      Algebra.norm (T.realField m) (T.extendedCyclotomicNumber ℚ p m) :=
  (rfl)

/-- The real extended cyclotomic number is nonzero whenever `mp > 1`. -/
theorem realExtendedCyclotomicNumber_ne_zero (h : m * p ≠ 1) :
    T.realExtendedCyclotomicNumber p m ≠ 0 := by
  exact Algebra.norm_ne_zero_iff.mpr (T.extendedCyclotomicNumber_ne_zero ℚ p m h)

/-- At levels above two, `c_m⁺` is the product of `c_m` and its complex conjugate. -/
theorem complexEmbedding_realExtendedCyclotomicNumber_of_two_lt
    (hm : 2 < m) (φ : T.field ℚ m →+* ℂ) :
    φ (algebraMap (T.realField m) (T.field ℚ m) (T.realExtendedCyclotomicNumber p m)) =
      φ (T.extendedCyclotomicNumber ℚ p m) * conj (φ (T.extendedCyclotomicNumber ℚ p m)) := by
  rw [T.realExtendedCyclotomicNumber_def,
    IsCyclotomicExtension.Rat.algebraMap_norm_maximalRealSubfield_of_two_lt m hm, map_mul,
    IsCyclotomicExtension.Rat.complexEmbedding_galEquivZMod_symm_neg_one_apply]

/-- At levels above two every complex embedding sends `c_m⁺` to a positive real number. -/
theorem re_complexEmbedding_realExtendedCyclotomicNumber_pos
    (hm : 2 < m) (φ : T.field ℚ m →+* ℂ) :
    0 < (φ (algebraMap (T.realField m) (T.field ℚ m) (T.realExtendedCyclotomicNumber p m))).re := by
  have hmp : 1 < m * p :=
    (by omega : 1 < m).trans_le (Nat.le_mul_of_pos_right _ (NeZero.pos p))
  rw [T.complexEmbedding_realExtendedCyclotomicNumber_of_two_lt p m hm φ, Complex.mul_conj,
    Complex.ofReal_re, Complex.normSq_pos]
  exact (_root_.map_ne_zero φ).2 (T.extendedCyclotomicNumber_ne_zero ℚ p m hmp.ne')

/-- At levels one and two the real norm has degree one, so `c_m⁺` maps to `c_m`. -/
theorem algebraMap_realExtendedCyclotomicNumber_of_le_two (hm : m ≤ 2) :
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

variable {p m} {ℓ : ℕ} [NeZero ℓ]

/-- If `ℓ ∣ mp`, the norm from level `mℓ` to `m` carries `c_{mℓ}⁺` to `c_m⁺`.
This includes the prime used to extend the family. -/
theorem norm_realExtendedCyclotomicNumber_mul_of_dvd (h : ℓ ∣ m * p) :
    letI := T.realFieldAlgebra (dvd_mul_right m ℓ)
    Algebra.norm (T.realField m) (T.realExtendedCyclotomicNumber p (m * ℓ)) =
      T.realExtendedCyclotomicNumber p m := by
  let := T.realFieldAlgebra (dvd_mul_right m ℓ)
  let := T.fieldAlgebra ℚ (dvd_mul_right m ℓ)
  rw [T.realExtendedCyclotomicNumber_def p (m * ℓ), T.norm_realField_norm (dvd_mul_right m ℓ),
    T.norm_extendedCyclotomicNumber_mul_of_dvd h, T.realExtendedCyclotomicNumber_def]

/-- At a prime `ℓ ∤ mp`, the norm from level `mℓ` to `m` is the quotient of `c_m⁺`
by its inverse arithmetic Frobenius conjugate in the real cyclotomic field. -/
theorem norm_realExtendedCyclotomicNumber_mul_eq_div [Fact ℓ.Prime]
    (hcop : ℓ.Coprime (m * p)) (hmp : 1 < m * p) :
    letI := T.realFieldAlgebra (dvd_mul_right m ℓ)
    Algebra.norm (T.realField m) (T.realExtendedCyclotomicNumber p (m * ℓ)) =
      T.realExtendedCyclotomicNumber p m /
        ((galEquivZMod m (T.field ℚ m)).symm
          (ZMod.unitOfCoprime ℓ (hcop.coprime_dvd_right (dvd_mul_right m p)))⁻¹).restrictNormal
            (T.realField m) (T.realExtendedCyclotomicNumber p m) := by
  let := T.realFieldAlgebra (dvd_mul_right m ℓ)
  let := T.fieldAlgebra ℚ (dvd_mul_right m ℓ)
  rw [T.realExtendedCyclotomicNumber_def p (m * ℓ), T.norm_realField_norm (dvd_mul_right m ℓ),
    T.norm_extendedCyclotomicNumber_mul_eq_div hcop hmp, div_eq_mul_inv, map_mul, Algebra.norm_inv,
    ← AlgEquiv.restrictNormal_norm, ← div_eq_mul_inv, T.realExtendedCyclotomicNumber_def]

end TauCeti.CompatibleCyclotomicTower
