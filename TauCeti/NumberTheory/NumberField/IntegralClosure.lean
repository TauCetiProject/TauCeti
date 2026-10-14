/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ClassNumber.AdmissibleAbs
public import Mathlib.NumberTheory.ClassNumber.Finite
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import TauCeti.RingTheory.IntegralClosure.Transfer

/-!
# The integral closure of `𝓞 K` in a finite extension of number fields

For a finite extension `L` of a number field `K`, the integral closure of `𝓞 K` in `L` is the
integral closure of `ℤ` in `L` — that is `TauCeti.IsIntegralClosure.tower_bot` applied along
`ℤ → 𝓞 K → L` — hence isomorphic to `𝓞 L`. Two consequences transfer along that identification
and are the finiteness inputs of the Mordell–Weil descent: the class group of the integral closure
is finite, and its unit group is finitely generated. The arithmetic invariants that the explicit
`2`-descent bound is stated in transfer as well: the unit rank of the integral closure is the unit
rank of `L`, and it is a principal ideal domain exactly when `𝓞 L` is.

Both are stated for `integralClosure (𝓞 K) L` rather than for `𝓞 L`, because that is the ring the
descent actually produces — `WeierstrassCurve.Affine.ringOfIntegersFactor` is an integral closure
in a quotient `K[X] ⧸ (p)`, not a ring of integers presented as such.

## Main definitions

* `NumberField.integralClosureEquivRingOfIntegers` : the identification of the integral closure
  with `𝓞 L`, the identity on underlying elements of `L`
  (`NumberField.algebraMap_integralClosureEquivRingOfIntegers`).

## Main results

* `NumberField.finite_classGroup_integralClosure` : the **class number theorem** for it.
* `NumberField.fg_units_integralClosure` : the finite-generation half of **Dirichlet's unit
  theorem** for it.
* `NumberField.finrank_units_integralClosure` : its unit rank is the unit rank of `L`.
* `NumberField.isPrincipalIdealRing_integralClosure_iff` : it is a principal ideal domain exactly
  when `𝓞 L` is.

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

/-- The integral closure of `𝓞 K` in a finite extension `L` of the number field `K` is the ring of
integers of `L`. -/
noncomputable def NumberField.integralClosureEquivRingOfIntegers :
    integralClosure (𝓞 K) L ≃ₐ[𝓞 K] 𝓞 L :=
  have : NumberField L := .of_module_finite K L
  IsIntegralClosure.equiv (𝓞 K) (integralClosure (𝓞 K) L) L (𝓞 L)

/-- `NumberField.integralClosureEquivRingOfIntegers` is the identity on the underlying elements
of `L`. -/
@[simp]
theorem NumberField.algebraMap_integralClosureEquivRingOfIntegers
    (x : integralClosure (𝓞 K) L) :
    algebraMap (𝓞 L) L (integralClosureEquivRingOfIntegers K L x) = x :=
  have : NumberField L := .of_module_finite K L
  IsIntegralClosure.algebraMap_equiv (𝓞 K) (integralClosure (𝓞 K) L) L (𝓞 L) x

/-- **Dirichlet's unit theorem** (finite generation) for the integral closure of `𝓞 K` in a
finite extension `L` of the number field `K`: its unit group is finitely generated. -/
theorem NumberField.fg_units_integralClosure :
    Group.FG (integralClosure (𝓞 K) L)ˣ := by
  have : NumberField L := .of_module_finite K L
  let e := (integralClosureEquivRingOfIntegers K L).toRingEquiv.toMulEquiv
  have : Group.FG (𝓞 L)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  exact Group.fg_of_surjective (f := (Units.mapEquiv e.symm).toMonoidHom)
    (Units.mapEquiv e.symm).surjective

/-- The unit rank of the integral closure of `𝓞 K` in a finite extension `L` of the number field `K`
is the unit rank `r₁ + r₂ - 1` of `L`. -/
theorem NumberField.finrank_units_integralClosure [NumberField L] :
    Module.finrank ℤ (Additive (integralClosure (𝓞 K) L)ˣ) = Units.rank L := by
  rw [← Units.finrank_eq L]
  let e := (integralClosureEquivRingOfIntegers K L).toRingEquiv.toMulEquiv
  exact (Units.mapEquiv e).toAdditive.toIntLinearEquiv.finrank_eq

/-- The integral closure of `𝓞 K` in a finite extension `L` of the number field `K` is a principal
ideal domain exactly when the ring of integers of `L` is, that is when `L` has class number `1`. -/
theorem NumberField.isPrincipalIdealRing_integralClosure_iff :
    IsPrincipalIdealRing (integralClosure (𝓞 K) L) ↔ IsPrincipalIdealRing (𝓞 L) :=
  let e := (integralClosureEquivRingOfIntegers K L).toRingEquiv
  ⟨fun _ ↦ .of_surjective e.toRingHom e.surjective,
    fun _ ↦ .of_surjective e.symm.toRingHom e.symm.surjective⟩

end
