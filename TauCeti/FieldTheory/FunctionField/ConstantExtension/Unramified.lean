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

Separability is inherited by scalar extension: each adjoined constant is separable over `k`, and
hence over the larger field `F`. For unramifiedness, choose a primitive element `c` of `k' / k`.
Its image generates `F' / F`, while the derivative of its minimal polynomial is a nonzero constant
and hence a unit at every place of `F'`. The derivative criterion for the different therefore makes
every different exponent vanish.

## Main results

* `TauCeti.isSeparable_of_constantCompositum_eq_top`: a separable extension of the constants
  produces a separable compositum over the original function field.
* `TauCeti.Place.differentExponent_eq_zero_of_constantCompositum_eq_top`: every different
  exponent of the constant extension vanishes.
* `TauCeti.Place.isUnramifiedAt_constantCompositum_eq_top`: each corresponding local model is
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

/-- A separable extension of the constant field produces a separable compositum over the
original field. -/
theorem isSeparable_of_constantCompositum_eq_top [Algebra.IsSeparable k k']
    (hcomp : constantCompositum F k' F' = ⊤) : Algebra.IsSeparable F F' := by
  rw [← IntermediateField.isSeparable_top]
  rw [← hcomp, constantCompositum_def,
    IntermediateField.isSeparable_adjoin_iff_isSeparable]
  rintro y ⟨c, rfl⟩
  exact IsSeparable.tower_top F <|
    (Algebra.IsSeparable.isSeparable k c).map (IsScalarTower.toAlgHom k k' F')
      (algebraMap k' F').injective

namespace Place

/-- Every different exponent in a finite separable constant extension vanishes, provided the
compositum is separable over the original field.

The `FiniteDimensional F F'` and `Algebra.IsSeparable F F'` instances are the ambient parameters
of `differentExponent`; `TauCeti.finiteDimensional_of_constantCompositum_eq_top` and
`TauCeti.isSeparable_of_constantCompositum_eq_top` construct them from the other hypotheses. -/
theorem differentExponent_eq_zero_of_constantCompositum_eq_top
    [FiniteDimensional k k'] [Algebra.IsSeparable k k'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F']
    (hcomp : constantCompositum F k' F' = ⊤) (P' : Place k' F') :
    differentExponent k F P' = 0 := by
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

/-- The local model of a finite separable constant extension is unramified at every place,
provided the compositum is separable over the original field. -/
theorem isUnramifiedAt_constantCompositum_eq_top
    [FiniteDimensional k k'] [Algebra.IsSeparable k k'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F']
    (hcomp : constantCompositum F k' F' = ⊤) (P' : Place k' F') :
    Algebra.IsUnramifiedAt ((P'.restrict k F).integers)
      (centerIntegralClosure k F P').asIdeal :=
  (differentExponent_eq_zero_iff k F P').mp
    (differentExponent_eq_zero_of_constantCompositum_eq_top hcomp P')

/-- Every place in a finite separable constant extension has ramification index one.

Unlike the local-model formulations, this statement constructs the finite-dimensionality and
separability instances for `F' / F` internally. -/
theorem ramificationIdx_eq_one_of_constantCompositum_eq_top
    [FiniteDimensional k k'] [Algebra.IsSeparable k k']
    (hcomp : constantCompositum F k' F' = ⊤) (P' : Place k' F') :
    ramificationIdx F P' = 1 := by
  let _ : FiniteDimensional F F' :=
    finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
  let _ : Algebra.IsSeparable F F' :=
    isSeparable_of_constantCompositum_eq_top (k := k) (k' := k') hcomp
  have hd := differentExponent_eq_zero_of_constantCompositum_eq_top
    (k := k) (k' := k') (F := F) hcomp P'
  have hle := ramificationIdx_le_differentExponent_add_one k F P'
  rw [hd] at hle
  exact Nat.le_antisymm (by simpa using hle) (ramificationIdx_pos F P')

end Place

end TauCeti
