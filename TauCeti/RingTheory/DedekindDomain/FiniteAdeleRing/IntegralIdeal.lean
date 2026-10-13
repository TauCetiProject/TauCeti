/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup
public import TauCeti.RingTheory.DedekindDomain.Ideal.Away

/-!
# Integral ideals of integral finite ideles

A finite idele defines an integral ideal exactly when each of its coordinates is integral.
Restricting the fractional-ideal map therefore gives a surjective monoid homomorphism to
the nonzero integral ideals. Its fibres are the orbits of the everywhere-integral units.
An integral finite idele need not have integral inverse; these ideles form a monoid,
whereas `integralUnits` is a group.

Restricting further to ideles that are local units on a finite set `S` gives
`TauCeti.toIntegralIdealsAway`, a surjective homomorphism to
`TauCeti.NumberFieldArithmetic.integralIdealsAway S`, with the same fibre criterion.

The construction uses `FiniteAdeleRing.toFractionalIdeal` and Mathlib's
`FractionalIdeal.le_one_iff_exists_coeIdeal`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section
noncomputable section

open IsDedekindDomain HeightOneSpectrum
open scoped nonZeroDivisors

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A finite-idele order is nonnegative exactly when its coordinate is integral. -/
theorem adicOrd_nonneg_iff (x : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) :
    0 ≤ adicOrd x v ↔ (x : 𝔸ᶠ[R, K]) v ∈ v.adicCompletionIntegers K := by
  rw [adicOrd_def, neg_nonneg, mem_adicCompletionIntegers,
    ← WithZero.exp_zero, ← WithZero.log_le_iff_le_exp
      (valued_coe_units_apply_ne_zero x v)]

/-- The fractional ideal of a finite idele is integral exactly when all its coordinates are. -/
@[simp]
theorem toFractionalIdeal_le_one_iff (x : 𝔸ᶠ[R, K]ˣ) :
    (toFractionalIdeal x : FractionalIdeal R⁰ K) ≤ 1 ↔
      (x : 𝔸ᶠ[R, K]) ∈ integralAdeles R K := by
  rw [mem_integralAdeles]
  refine ⟨fun h v ↦ ?_, fun h ↦ ?_⟩
  · rw [← adicOrd_nonneg_iff, ← count_coe_toFractionalIdeal]
    simpa only [FractionalIdeal.count_one] using
      FractionalIdeal.count_mono K v (Units.ne_zero (toFractionalIdeal x)) h
  · rw [toFractionalIdeal_apply]
    have hmap := (Units.coeHom (FractionalIdeal R⁰ K)).map_finprod
      (hasFiniteMulSupport_unitOfPrime_zpow_adicOrd x)
    simp only [Units.coeHom_apply] at hmap
    rw [hmap]
    apply finprod_induction (fun I : FractionalIdeal R⁰ K ↦ I ≤ 1) le_rfl
      (fun _ _ hI hJ ↦ (mul_le_mul' hI hJ).trans_eq (one_mul _))
    intro v
    have hv := (adicOrd_nonneg_iff x v).mpr (h v)
    rw [Units.val_zpow_eq_zpow_val, coe_unitOfPrime,
      ← Int.toNat_of_nonneg hv, zpow_natCast]
    exact pow_le_one' FractionalIdeal.coeIdeal_le_one _

variable (R K) in
/-- Finite ideles whose underlying adeles are integral at every finite place. -/
def integralFiniteIdeles : Submonoid 𝔸ᶠ[R, K]ˣ :=
  (integralAdeles R K).toSubmonoid.comap (Units.coeHom _)

/-- Membership in the integral finite-idele monoid is integrality of the underlying adele. -/
@[simp]
theorem mem_integralFiniteIdeles {x : 𝔸ᶠ[R, K]ˣ} :
    x ∈ integralFiniteIdeles R K ↔ (x : 𝔸ᶠ[R, K]) ∈ integralAdeles R K :=
  Iff.rfl

private theorem exists_integralIdeal (x : integralFiniteIdeles R K) :
    ∃ I : (Ideal R)⁰, (I : FractionalIdeal R⁰ K) = toFractionalIdeal (x : 𝔸ᶠ[R, K]ˣ) := by
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp
    ((toFractionalIdeal_le_one_iff _).mpr x.2)
  have hI0 : I ≠ 0 := by
    intro h
    exact Units.ne_zero (toFractionalIdeal (x : 𝔸ᶠ[R, K]ˣ)) (by simpa [h] using hI.symm)
  exact ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩, hI⟩

/-- The nonzero integral ideal defined by an integral finite idele. -/
def toIntegralIdeal : integralFiniteIdeles R K →* (Ideal R)⁰ where
  toFun x := (exists_integralIdeal x).choose
  map_one' := by
    apply Subtype.ext
    apply FractionalIdeal.coeIdeal_injective (K := K)
    simpa using (exists_integralIdeal (1 : integralFiniteIdeles R K)).choose_spec
  map_mul' x y := by
    apply Subtype.ext
    apply FractionalIdeal.coeIdeal_injective (K := K)
    simp only [Submonoid.coe_mul, FractionalIdeal.coeIdeal_mul]
    rw [(exists_integralIdeal (x * y)).choose_spec,
      (exists_integralIdeal x).choose_spec, (exists_integralIdeal y).choose_spec,
      Submonoid.coe_mul, map_mul]
    exact Units.val_mul _ _

/-- The integral-ideal map agrees with the fractional-ideal map. -/
@[simp]
theorem coe_toIntegralIdeal (x : integralFiniteIdeles R K) :
    (toIntegralIdeal x : FractionalIdeal R⁰ K) = toFractionalIdeal (x : 𝔸ᶠ[R, K]ˣ) :=
  (exists_integralIdeal x).choose_spec

/-- Every nonzero integral ideal is defined by an integral finite idele. -/
theorem toIntegralIdeal_surjective : Function.Surjective (toIntegralIdeal (R := R) (K := K)) := by
  intro I
  obtain ⟨x, hx⟩ := toFractionalIdeal_surjective (FractionalIdeal.mk0 K I)
  have hxint : x ∈ integralFiniteIdeles R K := by
    rw [mem_integralFiniteIdeles, ← toFractionalIdeal_le_one_iff, hx, FractionalIdeal.coe_mk0]
    exact FractionalIdeal.coeIdeal_le_one
  refine ⟨⟨x, hxint⟩, Subtype.ext (FractionalIdeal.coeIdeal_injective (K := K) ?_)⟩
  dsimp only
  rw [coe_toIntegralIdeal, hx, FractionalIdeal.coe_mk0]

/-- An integral finite idele defines the unit ideal exactly when it is an everywhere-integral
unit. -/
@[simp]
theorem toIntegralIdeal_eq_one_iff (x : integralFiniteIdeles R K) :
    toIntegralIdeal x = 1 ↔ (x : 𝔸ᶠ[R, K]ˣ) ∈ integralUnits R K := by
  rw [← ker_toFractionalIdeal, MonoidHom.mem_ker]
  constructor
  · intro h
    apply Units.ext
    rw [← coe_toIntegralIdeal, h]
    simp
  · intro h
    apply Subtype.ext
    apply FractionalIdeal.coeIdeal_injective (K := K)
    dsimp only
    rw [coe_toIntegralIdeal, h]
    simp

/-- Two integral finite ideles define the same ideal exactly when their ratio is an
everywhere-integral unit. -/
theorem toIntegralIdeal_eq_iff (x y : integralFiniteIdeles R K) :
    toIntegralIdeal x = toIntegralIdeal y ↔
      (x : 𝔸ᶠ[R, K]ˣ) / (y : 𝔸ᶠ[R, K]ˣ) ∈ integralUnits R K := by
  rw [← ker_toFractionalIdeal, MonoidHom.mem_ker, map_div, div_eq_one]
  constructor
  · intro h
    apply Units.ext
    rw [← coe_toIntegralIdeal, ← coe_toIntegralIdeal, h]
  · intro h
    apply Subtype.ext
    apply FractionalIdeal.coeIdeal_injective (K := K)
    dsimp only
    rw [coe_toIntegralIdeal, coe_toIntegralIdeal, h]

end IsDedekindDomain.FiniteAdeleRing

namespace TauCeti

open IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- Integral finite ideles that are local units at every place in `S`. -/
def integralFiniteIdelesAway (S : Finset (HeightOneSpectrum R)) :
    Submonoid (integralFiniteIdeles R K) :=
  (NumberFieldArithmetic.idealsAway K S).toSubmonoid.comap
    (toFractionalIdeal.comp (integralFiniteIdeles R K).subtype)

/-- The excluded places are precisely those at which the orders must vanish. -/
@[simp]
theorem mem_integralFiniteIdelesAway_iff (S : Finset (HeightOneSpectrum R))
    (x : integralFiniteIdeles R K) :
    x ∈ integralFiniteIdelesAway (K := K) S ↔ ∀ v ∈ S, adicOrd (x : 𝔸ᶠ[R, K]ˣ) v = 0 := by
  simp [integralFiniteIdelesAway, count_coe_toFractionalIdeal]

/-- The integral ideal away from `S` defined by an integral finite idele locally a unit on `S`.
This map takes values in the existing integral prime-to monoid. -/
def toIntegralIdealsAway (S : Finset (HeightOneSpectrum R)) :
    integralFiniteIdelesAway (K := K) S →* NumberFieldArithmetic.integralIdealsAway S :=
  (((Ideal R)⁰).subtype.comp
    (toIntegralIdeal.comp (integralFiniteIdelesAway (K := K) S).subtype)).codRestrict _ fun x ↦ by
    simp only [MonoidHom.comp_apply, Submonoid.subtype_apply]
    rw [NumberFieldArithmetic.mem_integralIdealsAway_iff_count_eq_zero (K := K)]
    refine ⟨nonZeroDivisors.coe_ne_zero (toIntegralIdeal x.1), fun v hv ↦ ?_⟩
    rw [coe_toIntegralIdeal, count_coe_toFractionalIdeal]
    exact (mem_integralFiniteIdelesAway_iff S x.1).mp x.2 v hv

/-- The prime-to integral-ideal map is the restriction of the integral-ideal map. -/
@[simp]
theorem coe_toIntegralIdealsAway (S : Finset (HeightOneSpectrum R))
    (x : integralFiniteIdelesAway (K := K) S) :
    (toIntegralIdealsAway S x : Ideal R) = (toIntegralIdeal x.1 : Ideal R) :=
  (rfl)

/-- Every integral ideal prime to `S` comes from an integral finite idele locally a unit on `S`.
-/
theorem toIntegralIdealsAway_surjective (S : Finset (HeightOneSpectrum R)) :
    Function.Surjective (toIntegralIdealsAway (K := K) S) := by
  intro I
  let J : (Ideal R)⁰ := ⟨I, NumberFieldArithmetic.integralIdealsAway_le_nonZeroDivisors S I.2⟩
  obtain ⟨x, hx⟩ := toIntegralIdeal_surjective (K := K) J
  have hxS : x ∈ integralFiniteIdelesAway (K := K) S := by
    rw [mem_integralFiniteIdelesAway_iff]
    intro v hv
    have hcount : FractionalIdeal.count K v (toIntegralIdeal x : FractionalIdeal R⁰ K) =
        adicOrd (x : 𝔸ᶠ[R, K]ˣ) v := by simp
    rw [← hcount, hx]
    exact (NumberFieldArithmetic.mem_integralIdealsAway_iff_count_eq_zero.mp I.2).2 v hv
  refine ⟨⟨x, hxS⟩, Subtype.ext ?_⟩
  rw [coe_toIntegralIdealsAway, hx]

/-- The integral prime-to map has unit ideal exactly on the everywhere-integral units. -/
@[simp]
theorem toIntegralIdealsAway_eq_one_iff (S : Finset (HeightOneSpectrum R))
    (x : integralFiniteIdelesAway (K := K) S) :
    toIntegralIdealsAway S x = 1 ↔ (x.1 : 𝔸ᶠ[R, K]ˣ) ∈ integralUnits R K := by
  rw [← toIntegralIdeal_eq_one_iff]
  constructor
  · intro h
    apply Subtype.ext
    simpa only [coe_toIntegralIdealsAway, Submonoid.coe_one] using congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    simp only [coe_toIntegralIdealsAway, h, Submonoid.coe_one]

/-- Two integral finite ideles locally units on `S` define the same prime-to ideal exactly
when their ratio is an everywhere-integral unit. -/
theorem toIntegralIdealsAway_eq_iff (S : Finset (HeightOneSpectrum R))
    (x y : integralFiniteIdelesAway (K := K) S) :
    toIntegralIdealsAway S x = toIntegralIdealsAway S y ↔
      (x.1 : 𝔸ᶠ[R, K]ˣ) / (y.1 : 𝔸ᶠ[R, K]ˣ) ∈ integralUnits R K := by
  simpa only [← Subtype.coe_inj, coe_toIntegralIdealsAway] using
    toIntegralIdeal_eq_iff x.1 y.1

end TauCeti
