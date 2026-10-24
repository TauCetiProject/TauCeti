/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.IntegralIdeal

/-!
# Finite ideles and fractional ideals away from a finite set

Let `R` be a Dedekind domain with fraction field `K`, and let `S` be a finite set of height one
primes of `R`. The finite-idele valuation `adicOrd` records the multiplicity of every height one
prime in the fractional ideal attached to a finite idele by `FiniteAdeleRing.toFractionalIdeal`.
This file restricts that dictionary to the prime-to carrier `NumberFieldArithmetic.idealsAway K S`
used by ray classes: vanishing of the orders on `S` is exactly membership in `idealsAway K S`, so
the finite ideles that are local units at every place of `S` map onto `idealsAway K S`, with kernel
the everywhere-integral units.

This is the fractional counterpart of `TauCeti.toIntegralIdealsAway`, which does the same for
integral finite ideles and the integral prime-to monoid `integralIdealsAway S`. The two maps agree
after passing from integral to fractional ideals, so adelic constructions can move between local
valuations and the single prime-to ideal carrier, integrally or fractionally, without introducing
a second notion of an ideal prime to `S`.

## Main definitions

* `TauCeti.finiteIdelesAway`: the finite ideles whose orders vanish at every place of `S`.
* `TauCeti.toIdealsAway`: the homomorphism from these finite ideles to `idealsAway K S`.

## Main results

* `TauCeti.toFractionalIdeal_mem_idealsAway_iff`: the fractional ideal of a finite idele is prime
  to `S` exactly when its orders vanish on `S`.
* `TauCeti.toIdealsAway_surjective` and `TauCeti.ker_toIdealsAway`: `toIdealsAway` is surjective,
  with kernel the everywhere-integral units, so `idealsAway K S` is the quotient of the finite
  ideles that are local units on `S` by `∏_v 𝒪_vˣ`.
* `TauCeti.integralIdealsAwayHom_toIntegralIdealsAway`: compatibility with the integral map
  `toIntegralIdealsAway`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section
noncomputable section

open IsDedekindDomain HeightOneSpectrum IsDedekindDomain.FiniteAdeleRing
open scoped nonZeroDivisors

namespace TauCeti

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A finite idele defines an ideal away from `S` exactly when its orders vanish on `S`. -/
theorem toFractionalIdeal_mem_idealsAway_iff (S : Finset (HeightOneSpectrum R))
    (x : 𝔸ᶠ[R, K]ˣ) :
    toFractionalIdeal x ∈ NumberFieldArithmetic.idealsAway K S ↔ ∀ v ∈ S, adicOrd x v = 0 := by
  simp only [NumberFieldArithmetic.mem_idealsAway_iff, count_coe_toFractionalIdeal]

variable (K) in
/-- The finite ideles whose orders vanish at every place of `S`, that is, the finite ideles that
are local units at every place of `S`. -/
def finiteIdelesAway (S : Finset (HeightOneSpectrum R)) : Subgroup 𝔸ᶠ[R, K]ˣ :=
  (NumberFieldArithmetic.idealsAway K S).comap toFractionalIdeal

/-- Membership in `finiteIdelesAway K S` means vanishing orders at every place of `S`. -/
@[simp]
theorem mem_finiteIdelesAway_iff (S : Finset (HeightOneSpectrum R)) (x : 𝔸ᶠ[R, K]ˣ) :
    x ∈ finiteIdelesAway K S ↔ ∀ v ∈ S, adicOrd x v = 0 := by
  rw [finiteIdelesAway, Subgroup.mem_comap, toFractionalIdeal_mem_idealsAway_iff]

variable (K) in
/-- The ideal away from `S` attached to a finite idele that is a local unit at every place of
`S`. -/
def toIdealsAway (S : Finset (HeightOneSpectrum R)) :
    finiteIdelesAway K S →* NumberFieldArithmetic.idealsAway K S :=
  (toFractionalIdeal.comp (finiteIdelesAway K S).subtype).codRestrict _ fun x ↦ x.property

/-- `toIdealsAway` is the restriction of the fractional-ideal map of finite ideles. -/
@[simp]
theorem coe_toIdealsAway (S : Finset (HeightOneSpectrum R)) (x : finiteIdelesAway K S) :
    (toIdealsAway K S x : (FractionalIdeal R⁰ K)ˣ) = toFractionalIdeal (x : 𝔸ᶠ[R, K]ˣ) :=
  (rfl)

/-- The kernel of `toIdealsAway` consists of the everywhere-integral units. -/
theorem ker_toIdealsAway (S : Finset (HeightOneSpectrum R)) :
    (toIdealsAway K S).ker = (integralUnits R K).comap (finiteIdelesAway K S).subtype := by
  refine (MonoidHom.ker_codRestrict _ _ _).trans ?_
  rw [← MonoidHom.comap_ker, ker_toFractionalIdeal]

/-- A finite idele that is a local unit on `S` defines the unit ideal exactly when it is an
everywhere-integral unit. -/
@[simp]
theorem toIdealsAway_eq_one_iff (S : Finset (HeightOneSpectrum R)) (x : finiteIdelesAway K S) :
    toIdealsAway K S x = 1 ↔ (x : 𝔸ᶠ[R, K]ˣ) ∈ integralUnits R K := by
  rw [← MonoidHom.mem_ker, ker_toIdealsAway, Subgroup.mem_comap, Subgroup.subtype_apply]

/-- Every fractional ideal away from `S` is the ideal of a finite idele that is a local unit at
every place of `S`. -/
theorem toIdealsAway_surjective (S : Finset (HeightOneSpectrum R)) :
    Function.Surjective (toIdealsAway K S) := by
  intro I
  obtain ⟨x, hx⟩ := toFractionalIdeal_surjective (I : (FractionalIdeal R⁰ K)ˣ)
  have hx_mem : x ∈ finiteIdelesAway K S := by
    rw [finiteIdelesAway, Subgroup.mem_comap, hx]
    exact I.property
  exact ⟨⟨x, hx_mem⟩, Subtype.ext hx⟩

variable (K) in
/-- The finite-idele orders of a representative of an integral ideal are its ideal multiplicities.

In particular, these orders are nonnegative everywhere and vanish on the excluded finite set. -/
theorem exists_forall_adicOrd_eq_count_integralIdealsAway (S : Finset (HeightOneSpectrum R))
    (I : NumberFieldArithmetic.integralIdealsAway (R := R) S) :
    ∃ x : 𝔸ᶠ[R, K]ˣ, ∀ v : HeightOneSpectrum R,
      adicOrd x v = FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) := by
  obtain ⟨x, hx⟩ := exists_forall_adicOrd_eq_count
    (NumberFieldArithmetic.integralIdealsAwayHom K S I : (FractionalIdeal R⁰ K)ˣ)
  exact ⟨x, fun v ↦ (hx v).trans (congrArg (FractionalIdeal.count K v)
    (NumberFieldArithmetic.coe_integralIdealsAwayHom S I))⟩

/-- Passing from integral to fractional prime-to ideals turns the integral finite-idele map
`toIntegralIdealsAway` into `toIdealsAway`. -/
@[simp]
theorem integralIdealsAwayHom_toIntegralIdealsAway (S : Finset (HeightOneSpectrum R))
    (x : integralFiniteIdelesAway (K := K) S) :
    NumberFieldArithmetic.integralIdealsAwayHom K S (toIntegralIdealsAway S x) =
      toIdealsAway K S ⟨(x.1 : 𝔸ᶠ[R, K]ˣ),
        (mem_finiteIdelesAway_iff S _).mpr ((mem_integralFiniteIdelesAway_iff S x.1).mp x.2)⟩ := by
  apply Subtype.ext
  apply Units.ext
  simp only [NumberFieldArithmetic.coe_integralIdealsAwayHom, coe_toIntegralIdealsAway,
    coe_toIntegralIdeal, coe_toIdealsAway]

end TauCeti
