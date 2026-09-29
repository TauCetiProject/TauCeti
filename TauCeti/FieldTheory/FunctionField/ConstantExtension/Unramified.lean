/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic
public import TauCeti.FieldTheory.FunctionField.Different.Derivative

import Mathlib.FieldTheory.PrimitiveElement

/-!
# Unramified constant field extensions

Let `k' / k` be finite and separable and suppose that `F'` is the compositum `F k'`. Then
`F' / F` is separable and is unramified at every place.

These are the local inputs to the comparison of the divisor theories of `F / k` and `F' / k'`.
Vanishing different exponents say that the different divisor of `F' / F` is zero, and
`e(P' | P) = 1` says that no place of `F` ramifies in `F'`, so the conorm of the point divisor of
a place of `F` is the sum of the point divisors of the places of `F'` above it with no
multiplicities, leaving the residue degrees as the only local data to track.  The genus,
divisor-degree and Riemann–Roch comparisons of Stichtenoth, Section III.6 consume these local
facts, but do not follow from them alone: they also need the constant field of `F'`, the
comparison of degrees normalised over `k` with those normalised over `k'`, and base change for
the Riemann–Roch spaces `L(D)`, none of which is proved here.

Separability is inherited by scalar extension, which is
`TauCeti.isSeparable_of_constantCompositum_eq_top`. For unramifiedness, choose a primitive element
`c` of `k' / k`. Its image generates `F' / F`, while the derivative of the minimal polynomial of
`c` evaluated at `c` is a nonzero element of `k'`, so its image in `F'` is a constant and hence a
unit at every place of `F'`. The derivative criterion for the different therefore makes every
different exponent vanish.

## Main results

* `TauCeti.Place.differentExponent_eq_zero_of_constantCompositum_eq_top`: every different
  exponent of the constant extension vanishes.
* `TauCeti.Place.isUnramifiedAt_of_constantCompositum_eq_top`: each corresponding local model is
  unramified.
* `TauCeti.Place.ramificationIdx_eq_one_of_constantCompositum_eq_top`: every place has
  ramification index one.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Proposition 3.6.3(a).
-/

public section

open Polynomial

open scoped IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

namespace Place

/-- **Every different exponent of a finite separable constant extension vanishes** (Stichtenoth,
Proposition 3.6.3(a)): for a place `P'` of `F' / k'` lying over the place `P = P'.restrict k F` of
`F / k`, the different exponent `d(P' ∣ P)` is zero, so the different divisor of `F' / F` is the
zero divisor. -/
theorem differentExponent_eq_zero_of_constantCompositum_eq_top
    [FiniteDimensional k k'] [Algebra.IsSeparable k k']
    (hcomp : constantCompositum F k' F' = ⊤) (P' : Place k' F') :
    letI := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
    letI := isSeparable_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
    differentExponent k F P' = 0 := by
  let := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
  let := isSeparable_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
  obtain ⟨c, hc⟩ := Field.exists_primitive_element k k'
  let y : F' := algebraMap k' F' c
  have hgen : F⟮y⟯ = ⊤ := by
    rw [← hcomp, constantCompositum_eq_adjoin_of_adjoin_eq_top F k' F' {c} hc]
    simp [y]
  have hpmonic : ((minpoly k c).map (algebraMap k F)).Monic :=
    (minpoly.monic (Algebra.IsSeparable.isIntegral k c)).map _
  have hpcoeff : ∀ i, ((minpoly k c).map (algebraMap k F)).coeff i ∈
      (P'.restrict k F).integers := by
    intro i
    rw [coeff_map]
    exact (P'.restrict k F).algebraMap_mem_integers _
  have hmap_aeval (q : k[X]) :
      aeval (algebraMap k' F' c) q = algebraMap k' F' (aeval c q) := by
    simpa only [IsScalarTower.toAlgHom_apply] using
      aeval_algHom_apply (IsScalarTower.toAlgHom k k' F') c q
  have hroot : aeval y ((minpoly k c).map (algebraMap k F)) = 0 := by
    dsimp [y]
    rw [aeval_map_algebraMap, hmap_aeval, minpoly.aeval, map_zero]
  have hderiv_ne : aeval c (derivative (minpoly k c)) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable k c).aeval_derivative_ne_zero (minpoly.aeval k c)
  have hderiv : P'.valuation
      (aeval y (derivative ((minpoly k c).map (algebraMap k F)))) = 1 := by
    dsimp [y]
    rw [derivative_map, aeval_map_algebraMap, hmap_aeval]
    exact Valuation.IsTrivialOn.eq_one _ hderiv_ne
  exact differentExponent_eq_zero_of_valuation_aeval_derivative_eq_one
    k F hgen hpmonic hpcoeff hroot hderiv

/-- **A finite separable constant extension is unramified at every place** (Stichtenoth,
Proposition 3.6.3(a)), in Mathlib's local formulation: for a place `P'` of `F' / k'` over
`P = P'.restrict k F`, the local model of `F'` at `P` — the integral closure of the valuation ring
`𝒪_P` in `F'` — is unramified at the centre of `P'`, so `P'` is unramified over `P` with separable
residue extension. -/
theorem isUnramifiedAt_of_constantCompositum_eq_top
    [FiniteDimensional k k'] [Algebra.IsSeparable k k']
    (hcomp : constantCompositum F k' F' = ⊤) (P' : Place k' F') :
    letI := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
    letI := isSeparable_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
    Algebra.IsUnramifiedAt ((P'.restrict k F).integers)
      (centerIntegralClosure k F P').asIdeal := by
  let := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
  let := isSeparable_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
  exact (differentExponent_eq_zero_iff k F P').mp
    (differentExponent_eq_zero_of_constantCompositum_eq_top hcomp P')

/-- Every place in a finite separable constant extension has ramification index one. -/
theorem ramificationIdx_eq_one_of_constantCompositum_eq_top
    [FiniteDimensional k k'] [Algebra.IsSeparable k k']
    (hcomp : constantCompositum F k' F' = ⊤) (P' : Place k' F') :
    ramificationIdx F P' = 1 := by
  let _ : FiniteDimensional F F' :=
    finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
  let _ : Algebra.IsSeparable F F' :=
    isSeparable_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
  have := isUnramifiedAt_of_constantCompositum_eq_top (k := k) (k' := k') (F := F) hcomp P'
  rw [ramificationIdx_eq_ramificationIdx_center (R := (P'.restrict k F).integers) k F P'
    (algebraMap_mem_integers_of_mem_integralClosure k F P'), ← centerIntegralClosure_def]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

end Place

end TauCeti
