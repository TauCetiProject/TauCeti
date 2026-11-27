/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ClassNumber.AdmissibleAbs
public import Mathlib.NumberTheory.ClassNumber.Finite
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import TauCeti.NumberTheory.NumberField.AutomorphismAction
import TauCeti.RingTheory.DedekindDomain.Prufer
import TauCeti.RingTheory.IntegralClosure.Transfer

/-!
# The integral closure of `𝓞 K` in an extension of a number field

For a finite extension `L` of a number field `K`, the integral closure of `𝓞 K` in `L` is the
integral closure of `ℤ` in `L` — that is `TauCeti.IsIntegralClosure.tower_bot` applied along
`ℤ → 𝓞 K → L` — hence isomorphic to `𝓞 L`. Two consequences transfer along that identification
and are the finiteness inputs of the Mordell–Weil descent: the class group of the integral closure
is finite, and its unit group is finitely generated. The unit rank and the triviality of the class
group transfer as well; they turn the descent bound into a number for a given curve.

All four are stated for `integralClosure (𝓞 K) L` rather than for `𝓞 L`, because that is the ring
the descent actually produces — `WeierstrassCurve.Affine.ringOfIntegersFactor` is an integral
closure in a quotient `K[X] ⧸ (p)`, not a ring of integers presented as such.

For an algebraic, possibly infinite, extension `L` of `K`, such as `K^alg`, the integral closure
of `𝓞 K` in `L` plays the role of the ring of integers of `L`. The instances of the last section
record that its fraction field is `L`, that its localizations at primes are valuation rings, and
that for a group acting on `L` by `K`-automorphisms with fixed field `K`, such as `Gal(L/K)`, its
invariants are `𝓞 K`.

## Main results

* `NumberField.finite_classGroup_integralClosure` : the **class number theorem** for it.
* `NumberField.fg_units_integralClosure` : the finite-generation half of **Dirichlet's unit
  theorem** for it.
* `NumberField.finrank_units_integralClosure` : its unit group has rank the unit rank of `L`.
* `NumberField.isPrincipalIdealRing_integralClosure_iff` : it is a principal ideal domain exactly
  when `L` has class number one.
* `NumberField.isFractionRing_integralClosure`,
  `NumberField.preValuationRing_atPrime_integralClosure` and
  `NumberField.isInvariant_integralClosure` : for an algebraic extension `L`, the integral closure
  has fraction field `L`, is a Prüfer domain, and has invariants `𝓞 K` under a group with fixed
  field `K`.

## References

* [M. Stoll, *EllipticCurves*](https://github.com/MichaelStollBayreuth/EllipticCurves), commit
  `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, `EllipticCurves/Mathlib/Basic.lean`, Apache-2.0.
  That file collects general-purpose results its author flags as Mathlib candidates;
  `NumberField.finite_classGroup_integralClosure` and `NumberField.fg_units_integralClosure` are
  adapted from it essentially verbatim. The `ℤ → 𝓞 K → L` identification they rest on is
  `TauCeti.IsIntegralClosure.tower_bot`, credited to Stacks in its own module.
-/

public section

open NumberField

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

section Finiteness

variable [NumberField K] [FiniteDimensional K L]

/-- The **class number theorem** for the integral closure of `𝓞 K` in a finite extension `L`
of the number field `K`: its class group is finite. -/
theorem NumberField.finite_classGroup_integralClosure :
    Finite (ClassGroup (integralClosure (𝓞 K) L)) := by
  have : NumberField L := .of_module_finite K L
  have := TauCeti.IsIntegralClosure.tower_bot (R := ℤ) (A := 𝓞 K) (B := L)
    (C := integralClosure (𝓞 K) L)
  have := ClassGroup.fintypeOfAdmissibleOfFinite ℚ L
    (S := integralClosure (𝓞 K) L) AbsoluteValue.absIsAdmissible
  exact Finite.of_fintype _

/-- **Dirichlet's unit theorem** (finite generation) for the integral closure of `𝓞 K` in a
finite extension `L` of the number field `K`: its unit group is finitely generated. -/
theorem NumberField.fg_units_integralClosure :
    Group.FG (integralClosure (𝓞 K) L)ˣ := by
  have : NumberField L := .of_module_finite K L
  have e : integralClosure (𝓞 K) L ≃ₐ[𝓞 K] (𝓞 L) :=
    IsIntegralClosure.equiv (𝓞 K) (integralClosure (𝓞 K) L) L (𝓞 L)
  have : Group.FG (𝓞 L)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  exact Group.fg_of_surjective
    (f := (Units.mapEquiv e.symm.toRingEquiv.toMulEquiv).toMonoidHom)
    (Units.mapEquiv e.symm.toRingEquiv.toMulEquiv).surjective

end Finiteness

section Invariants

variable [NumberField L]

/-- The unit group of the integral closure of `𝓞 K` in a number field `L` has rank the unit rank
of `L`. -/
theorem NumberField.finrank_units_integralClosure :
    Module.finrank ℤ (Additive (integralClosure (𝓞 K) L)ˣ) = NumberField.Units.rank L := by
  let e : integralClosure (𝓞 K) L ≃ₐ[𝓞 K] (𝓞 L) :=
    IsIntegralClosure.equiv (𝓞 K) (integralClosure (𝓞 K) L) L (𝓞 L)
  rw [(Units.mapEquiv e.toRingEquiv.toMulEquiv).toAdditive.toIntLinearEquiv.finrank_eq,
    NumberField.Units.finrank_eq]

/-- The integral closure of `𝓞 K` in a number field `L` is a principal ideal domain exactly when
`L` has class number one. -/
theorem NumberField.isPrincipalIdealRing_integralClosure_iff :
    IsPrincipalIdealRing (integralClosure (𝓞 K) L) ↔ NumberField.classNumber L = 1 := by
  let e : integralClosure (𝓞 K) L ≃ₐ[𝓞 K] (𝓞 L) :=
    IsIntegralClosure.equiv (𝓞 K) (integralClosure (𝓞 K) L) L (𝓞 L)
  rw [NumberField.classNumber_eq_one_iff]
  exact ⟨fun _ ↦ .of_surjective e.toRingEquiv e.surjective,
    fun _ ↦ .of_surjective e.symm.toRingEquiv e.symm.surjective⟩

end Invariants

section Algebraic

variable {K L}

/-- If a group acts on `L` by `K`-algebra automorphisms with fixed field `K`, the elements of the
integral closure of `𝓞 K` in `L` fixed by the group are those of `𝓞 K`. -/
instance NumberField.isInvariant_integralClosure {G : Type*} [Group G] [MulSemiringAction G L]
    [SMulCommClass G K L] [Algebra.IsInvariant K L G] :
    Algebra.IsInvariant (𝓞 K) (integralClosure (𝓞 K) L) G where
  isInvariant b hb := by
    obtain ⟨k, hk⟩ := Algebra.IsInvariant.isInvariant (A := K) (G := G) (b : L)
      fun g ↦ congr_arg Subtype.val (hb g)
    have hint : IsIntegral ℤ (algebraMap K L k) := by
      rw [hk]
      exact isIntegral_trans (R := ℤ) (A := 𝓞 K) _ b.property
    exact ⟨⟨k, (isIntegral_algHom_iff ((Algebra.ofId K L).restrictScalars ℤ)
      (algebraMap K L).injective).mp hint⟩, Subtype.ext hk⟩

variable [NumberField K] [Algebra.IsAlgebraic K L]

/-- The integral closure of `𝓞 K` in an algebraic, possibly infinite, extension `L` of the number
field `K` has fraction field `L`. -/
instance NumberField.isFractionRing_integralClosure : IsFractionRing (integralClosure (𝓞 K) L) L :=
  have : Algebra.IsAlgebraic (𝓞 K) L :=
    (IsFractionRing.comap_isAlgebraic_iff (K := K)).mpr inferInstance
  integralClosure.isFractionRing_of_algebraic fun _ hx ↦
    IsFractionRing.to_map_eq_zero_iff.mp ((map_eq_zero (algebraMap K L)).mp
      ((IsScalarTower.algebraMap_apply (𝓞 K) K L _).symm.trans hx))

/-- **The integral closure of `𝓞 K` in an algebraic extension is a Prüfer domain**: its
localizations at primes are valuation rings. This is Tau Ceti's
`IsIntegralClosure.preValuationRing_atPrime` for `𝓞 K`. -/
instance NumberField.preValuationRing_atPrime_integralClosure (Q : Ideal (integralClosure (𝓞 K) L))
    [Q.IsPrime] : PreValuationRing (Localization.AtPrime Q) :=
  IsIntegralClosure.preValuationRing_atPrime (𝓞 K) K L Q

end Algebraic

end
