/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Away
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.IntegralIdeal

/-!
# Integral finite ideles and integral ideals away from a finite set

Integral finite ideles that are local units at a finite set `S` map onto
`NumberFieldArithmetic.integralIdealsAway S`. The map is a monoid homomorphism and its
fibres are exactly the everywhere-integral-unit orbits. After passage to fractional ideals,
it agrees with `toIdealsAway` and `NumberFieldArithmetic.integralIdealsAwayHom`.

This identifies the integral part of the finite-idele dictionary with the existing monoid
of prime-to ideals, so integral ray-class representatives can be handled adelically.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section
noncomputable section

open IsDedekindDomain HeightOneSpectrum IsDedekindDomain.FiniteAdeleRing
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- Integral finite ideles that are local units at every place in `S`. -/
def integralFiniteIdelesAway (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Submonoid (integralFiniteIdeles (𝓞 K) K) :=
  (adicOrdAway S).toSubmonoid.comap (integralFiniteIdeles (𝓞 K) K).subtype

/-- The excluded places are precisely those at which the orders must vanish. -/
@[simp]
theorem mem_integralFiniteIdelesAway_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : integralFiniteIdeles (𝓞 K) K) :
    x ∈ integralFiniteIdelesAway S ↔ ∀ v ∈ S, adicOrd (x : 𝔸ᶠ[𝓞 K, K]ˣ) v = 0 := by
  simp [integralFiniteIdelesAway]

/-- The integral ideal away from `S` defined by an integral finite idele locally a unit on `S`.
This map takes values in the existing integral prime-to monoid. -/
def toIntegralIdealsAway (S : Finset (HeightOneSpectrum (𝓞 K))) :
    integralFiniteIdelesAway S →* NumberFieldArithmetic.integralIdealsAway S :=
  (((Ideal (𝓞 K))⁰).subtype.comp
    (toIntegralIdeal.comp (integralFiniteIdelesAway S).subtype)).codRestrict _ fun x ↦ by
    simp only [MonoidHom.comp_apply, Submonoid.subtype_apply]
    rw [NumberFieldArithmetic.mem_integralIdealsAway_iff_count_eq_zero (K := K)]
    refine ⟨nonZeroDivisors.coe_ne_zero (toIntegralIdeal x.1), fun v hv ↦ ?_⟩
    rw [coe_toIntegralIdeal, count_coe_toFractionalIdeal]
    exact (mem_integralFiniteIdelesAway_iff S x.1).mp x.2 v hv

/-- The prime-to integral-ideal map is the restriction of the integral-ideal map. -/
@[simp]
theorem coe_toIntegralIdealsAway (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : integralFiniteIdelesAway S) :
    (toIntegralIdealsAway S x : Ideal (𝓞 K)) = (toIntegralIdeal x.1 : Ideal (𝓞 K)) :=
  (rfl)

/-- Every integral ideal prime to `S` comes from an integral finite idele locally a unit on `S`.
-/
theorem toIntegralIdealsAway_surjective (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective (toIntegralIdealsAway (K := K) S) := by
  intro I
  let J : (Ideal (𝓞 K))⁰ := ⟨I, NumberFieldArithmetic.integralIdealsAway_le_nonZeroDivisors S I.2⟩
  obtain ⟨x, hx⟩ := toIntegralIdeal_surjective (K := K) J
  have hxS : x ∈ integralFiniteIdelesAway S := by
    rw [mem_integralFiniteIdelesAway_iff]
    intro v hv
    have hcount : FractionalIdeal.count K v (toIntegralIdeal x : FractionalIdeal (𝓞 K)⁰ K) =
        adicOrd (x : 𝔸ᶠ[𝓞 K, K]ˣ) v := by simp
    rw [← hcount, hx]
    exact (NumberFieldArithmetic.mem_integralIdealsAway_iff_count_eq_zero.mp I.2).2 v hv
  refine ⟨⟨x, hxS⟩, Subtype.ext ?_⟩
  rw [coe_toIntegralIdealsAway, hx]

/-- The integral prime-to map has unit ideal exactly on the everywhere-integral units. -/
@[simp]
theorem toIntegralIdealsAway_eq_one_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : integralFiniteIdelesAway S) :
    toIntegralIdealsAway S x = 1 ↔ (x.1 : 𝔸ᶠ[𝓞 K, K]ˣ) ∈ integralUnits (𝓞 K) K := by
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
theorem toIntegralIdealsAway_eq_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x y : integralFiniteIdelesAway S) :
    toIntegralIdealsAway S x = toIntegralIdealsAway S y ↔
      (x.1 : 𝔸ᶠ[𝓞 K, K]ˣ) / (y.1 : 𝔸ᶠ[𝓞 K, K]ˣ) ∈ integralUnits (𝓞 K) K := by
  simpa only [← Subtype.coe_inj, coe_toIntegralIdealsAway] using
    toIntegralIdeal_eq_iff x.1 y.1

/-- Passing to the fractional prime-to ideals agrees with the finite-idele map. -/
@[simp]
theorem integralIdealsAwayHom_toIntegralIdealsAway
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : integralFiniteIdelesAway S) :
    NumberFieldArithmetic.integralIdealsAwayHom K S (toIntegralIdealsAway S x) =
      toIdealsAway S ⟨(x.1 : 𝔸ᶠ[𝓞 K, K]ˣ),
        (mem_adicOrdAway_iff S _).mpr ((mem_integralFiniteIdelesAway_iff S x.1).mp x.2)⟩ := by
  apply Subtype.ext
  apply Units.ext
  simp only [NumberFieldArithmetic.coe_integralIdealsAwayHom,
    coe_toIntegralIdealsAway, coe_toIntegralIdeal, toIdealsAway_apply]

end TauCeti.GlobalNumberFields
