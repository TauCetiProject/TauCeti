/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Basic
public import TauCeti.RingTheory.DedekindDomain.Ideal.Ray.Basic

/-!
# Finite ray class groups of number fields

For a number field, the Dedekind-domain finite ray class group of a nonzero ideal is canonically
the existing ray class group of the modulus having that finite part and no real places.  This file
provides that comparison and identifies both quotient maps and both integral-ideal class maps.

The comparison lets finite-only arguments work over arbitrary Dedekind domains and then specialize
without introducing a second number-field ray class carrier.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The support of a finite-part modulus is the generic finite ray support of its ideal. -/
@[simp]
theorem Modulus.support_ofFinitePart (m : Ideal (RingOfIntegers K)) (hm : m ≠ ⊥) :
    (Modulus.ofFinitePart m hm).support =
      Ideal.finiteRaySupport m hm := by
  ext v
  rw [Modulus.mem_support_iff, Ideal.mem_finiteRaySupport_iff,
    Modulus.ofFinitePart_finitePart]

/-- For a modulus with no infinite part, number-field congruence is exactly the generic finite
multiplicative congruence. -/
@[simp]
theorem isCongrOne_ofFinitePart_iff {m : Ideal (RingOfIntegers K)} {hm : m ≠ ⊥} {x : Kˣ} :
    IsCongrOne (Modulus.ofFinitePart m hm) x ↔
      x ∈ m.congruenceSubgroup K hm := by
  rw [isCongrOne_iff_mem_congruenceSubgroup_and_pos]
  simp

/-- Fractional ideals prime to `m`, in the generic and number-field presentations. -/
def finiteIdealsPrimeToEquiv (m : Ideal (RingOfIntegers K)) (hm : m ≠ ⊥) :
    NumberFieldArithmetic.idealsAway K (Ideal.finiteRaySupport m hm) ≃*
      idealsPrimeTo (Modulus.ofFinitePart m hm) :=
  MulEquiv.subgroupCongr <|
    congrArg (NumberFieldArithmetic.idealsAway K) (Modulus.support_ofFinitePart m hm).symm

/-- The prime-to-ideal comparison does not change the underlying fractional ideal. -/
@[simp]
theorem coe_finiteIdealsPrimeToEquiv (m : Ideal (RingOfIntegers K)) (hm : m ≠ ⊥)
    (I : NumberFieldArithmetic.idealsAway K
      (Ideal.finiteRaySupport m hm)) :
    (finiteIdealsPrimeToEquiv m hm I : (FractionalIdeal (RingOfIntegers K)⁰ K)ˣ) = I :=
  (rfl)

/-- The inverse prime-to-ideal comparison does not change the underlying fractional ideal. -/
@[simp]
theorem coe_finiteIdealsPrimeToEquiv_symm (m : Ideal (RingOfIntegers K)) (hm : m ≠ ⊥)
    (I : idealsPrimeTo (Modulus.ofFinitePart m hm)) :
    ((finiteIdealsPrimeToEquiv m hm).symm I : (FractionalIdeal (RingOfIntegers K)⁰ K)ˣ) = I :=
  (rfl)

/-- Under the prime-to-ideal comparison, the generic finite ray is the ray of the corresponding
number-field modulus. -/
theorem map_finiteRay_eq_ray (m : Ideal (RingOfIntegers K)) (hm : m ≠ ⊥) :
    Subgroup.map (finiteIdealsPrimeToEquiv m hm : _ →* _)
        (Ideal.finiteRay (K := K) m hm) =
      ray (Modulus.ofFinitePart m hm) := by
  ext J
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨I, hI, rfl⟩
    obtain ⟨x, hx, hxI⟩ := Ideal.mem_finiteRay_iff.mp hI
    exact mem_ray_iff.mpr ⟨x, isCongrOne_ofFinitePart_iff.mpr hx, by simpa using hxI⟩
  · intro hJ
    obtain ⟨x, hx, hxJ⟩ := mem_ray_iff.mp hJ
    refine ⟨(finiteIdealsPrimeToEquiv m hm).symm J, ?_, by simp⟩
    exact Ideal.mem_finiteRay_iff.mpr
      ⟨x, isCongrOne_ofFinitePart_iff.mp hx, by simpa using hxJ⟩

private theorem finiteRay_le_comparison_ker (m : Ideal (RingOfIntegers K)) (hm : m ≠ ⊥) :
    Ideal.finiteRay (K := K) m hm ≤
      ((rayClassMk (Modulus.ofFinitePart m hm)).comp
        (finiteIdealsPrimeToEquiv m hm).toMonoidHom).ker := by
  intro I hI
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, rayClassMk_eq_one_iff,
    ← map_finiteRay_eq_ray]
  exact ⟨I, hI, rfl⟩

private theorem ray_le_comparison_symm_ker (m : Ideal (RingOfIntegers K)) (hm : m ≠ ⊥) :
    ray (Modulus.ofFinitePart m hm) ≤
      ((Ideal.finiteRayClassMk (K := K) m hm).comp
        (finiteIdealsPrimeToEquiv m hm).symm.toMonoidHom).ker := by
  intro I hI
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Ideal.finiteRayClassMk_eq_one_iff]
  rw [← map_finiteRay_eq_ray] at hI
  obtain ⟨J, hJ, rfl⟩ := hI
  simpa using hJ

private def finiteRayClassComparisonHom (m : Ideal (RingOfIntegers K)) (hm : m ≠ ⊥) :
    Ideal.FiniteRayClassGroup m hm K →*
      RayClassGroup (Modulus.ofFinitePart m hm) :=
  Ideal.finiteRayClassLift
    ((rayClassMk (Modulus.ofFinitePart m hm)).comp
      (finiteIdealsPrimeToEquiv m hm).toMonoidHom)
    (finiteRay_le_comparison_ker m hm)

private def finiteRayClassComparisonSymmHom (m : Ideal (RingOfIntegers K)) (hm : m ≠ ⊥) :
    RayClassGroup (Modulus.ofFinitePart m hm) →*
      Ideal.FiniteRayClassGroup m hm K :=
  rayClassLift
    ((Ideal.finiteRayClassMk (K := K) m hm).comp
      (finiteIdealsPrimeToEquiv m hm).symm.toMonoidHom)
    (ray_le_comparison_symm_ker m hm)

/-- The Dedekind-domain finite ray class group agrees canonically with the number-field ray class
group having empty infinite part. -/
def finiteRayClassGroupEquiv (m : Ideal (RingOfIntegers K)) (hm : m ≠ ⊥) :
    Ideal.FiniteRayClassGroup m hm K ≃*
      RayClassGroup (Modulus.ofFinitePart m hm) where
  toFun := finiteRayClassComparisonHom m hm
  invFun := finiteRayClassComparisonSymmHom m hm
  left_inv c := by
    obtain ⟨I, rfl⟩ := Ideal.finiteRayClassMk_surjective m hm c
    simp [finiteRayClassComparisonHom, finiteRayClassComparisonSymmHom]
  right_inv c := by
    obtain ⟨I, rfl⟩ := rayClassMk_surjective (Modulus.ofFinitePart m hm) c
    simp [finiteRayClassComparisonHom, finiteRayClassComparisonSymmHom]
  map_mul' x y := map_mul (finiteRayClassComparisonHom m hm) x y

/-- The finite-ray-class comparison carries the generic quotient map to the number-field quotient
map without changing the ideal representative. -/
@[simp]
theorem finiteRayClassGroupEquiv_finiteRayClassMk (m : Ideal (RingOfIntegers K)) (hm : m ≠ ⊥)
    (I : NumberFieldArithmetic.idealsAway K
      (Ideal.finiteRaySupport m hm)) :
    finiteRayClassGroupEquiv m hm
        (Ideal.finiteRayClassMk m hm I) =
      rayClassMk (Modulus.ofFinitePart m hm) (finiteIdealsPrimeToEquiv m hm I) := by
  simp [finiteRayClassGroupEquiv, finiteRayClassComparisonHom]

/-- Integral ideals prime to `m`, in the generic and number-field presentations. -/
def finiteIntegralIdealsPrimeToEquiv (m : Ideal (RingOfIntegers K)) (hm : m ≠ ⊥) :
    NumberFieldArithmetic.integralIdealsAway
        (Ideal.finiteRaySupport m hm) ≃*
      integralIdealsPrimeTo (Modulus.ofFinitePart m hm) :=
  MulEquiv.submonoidCongr <|
    congrArg NumberFieldArithmetic.integralIdealsAway (Modulus.support_ofFinitePart m hm).symm

/-- The integral prime-to-ideal comparison does not change the underlying ideal. -/
@[simp]
theorem coe_finiteIntegralIdealsPrimeToEquiv (m : Ideal (RingOfIntegers K)) (hm : m ≠ ⊥)
    (I : NumberFieldArithmetic.integralIdealsAway
      (Ideal.finiteRaySupport m hm)) :
    ((finiteIntegralIdealsPrimeToEquiv m hm I :
      integralIdealsPrimeTo (Modulus.ofFinitePart m hm)) : Ideal (RingOfIntegers K)) = I :=
  (rfl)

/-- The finite-ray-class comparison identifies the generic and number-field classes of an integral
ideal prime to the finite part. -/
@[simp]
theorem finiteRayClassGroupEquiv_finiteIdealClass (m : Ideal (RingOfIntegers K)) (hm : m ≠ ⊥)
    (I : NumberFieldArithmetic.integralIdealsAway
      (Ideal.finiteRaySupport m hm)) :
    finiteRayClassGroupEquiv m hm
        (Ideal.finiteIdealClass (K := K) m hm I) =
      idealClass (Modulus.ofFinitePart m hm) (finiteIntegralIdealsPrimeToEquiv m hm I) := by
  rw [Ideal.finiteIdealClass_apply, idealClass_apply,
    finiteRayClassGroupEquiv_finiteRayClassMk]
  congr 1
  exact Subtype.ext (Units.ext (by
    simp only [NumberFieldArithmetic.coe_integralIdealsAwayHom,
      coe_finiteIdealsPrimeToEquiv, coe_finiteIntegralIdealsPrimeToEquiv]))

end TauCeti.GlobalNumberFields
