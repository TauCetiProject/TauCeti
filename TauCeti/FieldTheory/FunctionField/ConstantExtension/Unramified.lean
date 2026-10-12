/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic
public import TauCeti.FieldTheory.FunctionField.Different.Derivative
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Eisenstein

import TauCeti.FieldTheory.FunctionField.Place.Extension.Tower

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

Read backwards, unramifiedness detects new constants.  If `k` is exact in `F`, a finite separable
extension with a totally ramified place has no new constants: any finite separable extension of
constants is unramified, and multiplicativity of ramification indices prevents it from occurring
inside a totally ramified extension.  This is how the exactness of the constants of Kummer covers
is established.

## Main results

* `TauCeti.Place.differentExponent_eq_zero_of_constantCompositum_eq_top`: every different
  exponent of the constant extension vanishes.
* `TauCeti.Place.isUnramifiedAt_of_constantCompositum_eq_top`: each corresponding local model is
  unramified.
* `TauCeti.Place.ramificationIdx_eq_one_of_constantCompositum_eq_top`: every place has
  ramification index one.
* `TauCeti.isIntegrallyClosedIn_of_isTotallyRamified`: a finite separable extension with a
  totally ramified place acquires no new constants.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Proposition 3.6.3(a), and
the argument of Proposition 3.7.3(c).
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

/-! ### Ramification keeps the constant field exact -/

section Ramified

/-- **A finite separable extension with a totally ramified place acquires no new constants**:
if `k` is the exact constant field of `F` and some place of `F'` is totally ramified over `F`,
then `k` is also the exact constant field of `F'`.

This is the exact-constant-field criterion used for Kummer extensions
(Stichtenoth, Proposition 3.7.3(c)). -/
theorem isIntegrallyClosedIn_of_isTotallyRamified [FiniteDimensional F F']
    [Algebra.IsSeparable F F'] (hex : IsIntegrallyClosedIn k F) {P' : Place k F'}
    (hP' : P'.IsTotallyRamified F) : IsIntegrallyClosedIn k F' := by
  -- Adjoining a constant `c : F'` algebraic over `k` gives a finite separable constant extension
  -- `E = F(c)` of `F`, so the restriction of the totally ramified place to `E` is unramified.
  -- Multiplicativity of ramification indices and degrees then forces `E = F`, after which
  -- exactness of `k` in `F` gives `c ∈ k`.
  refine isIntegrallyClosedIn_iff_forall_isAlgebraic.2 fun c hc ↦ ?_
  have hci : IsIntegral k c := hc.isIntegral
  let K := k⟮c⟯
  let E := constantCompositum F K F'
  let : FiniteDimensional k K := IntermediateField.adjoin.finiteDimensional hci
  let : Algebra.IsSeparable k K := by
    rw [IntermediateField.isSeparable_adjoin_simple_iff_isSeparable, IsSeparable,
      ← Polynomial.separable_map (algebraMap k F),
      minpoly.map_algebraMap_of_isIntegrallyClosedIn hex hci]
    exact Algebra.IsSeparable.isSeparable F c
  let : Algebra K E := ((algebraMap K F').codRestrict E fun a ↦
    algebraMap_mem_constantCompositum F K F' a).toAlgebra
  let : Algebra k E := ((algebraMap k F').codRestrict E fun a ↦ by
    rw [IsScalarTower.algebraMap_apply k F F']
    exact IntermediateField.algebraMap_mem E (algebraMap k F a)).toAlgebra
  let : IsScalarTower k F E := .of_algebraMap_eq fun a ↦ by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply k F F' a
  let : IsScalarTower k K E := .of_algebraMap_eq fun a ↦ by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply k K F' a
  let : IsScalarTower k E F' := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply k F E, ← IsScalarTower.algebraMap_apply F E F',
      ← IsScalarTower.algebraMap_apply k F F']
  let : IsScalarTower K E F' := .of_algebraMap_eq fun a ↦
    (RingHom.codRestrict_apply (algebraMap K F') E
      (algebraMap_mem_constantCompositum F K F') a).symm
  let Q : Place K E := Place.constantsEquiv k K E (P'.restrict k E)
  have hQ : Q.ramificationIdx F = 1 := Place.ramificationIdx_eq_one_of_constantCompositum_eq_top
    (k := k) ((constantCompositum_eq_top_iff F K F' E).2 rfl) Q
  have hQ' : (P'.restrict k E).ramificationIdx F = 1 := by
    simpa only [Q, Place.ramificationIdx_def, Place.valuation_constantsEquiv] using hQ
  have htower := Place.ramificationIdx_restrict_mul (k₁ := k) (F₀ := F)
    (F₁ := E) P'
  have hle : Module.finrank F F' ≤ Module.finrank E F' := by
    calc
      Module.finrank F F' = Place.ramificationIdx F P' :=
        ((Place.isTotallyRamified_iff F).mp hP').symm
      _ = Place.ramificationIdx E P' * (P'.restrict k E).ramificationIdx F := htower
      _ = Place.ramificationIdx E P' := by rw [hQ', mul_one]
      _ ≤ Module.finrank E F' := Place.ramificationIdx_le_finrank E P'
  have hEbot : E = ⊥ := (IntermediateField.eq_of_le_of_finrank_le' bot_le <| by
    rwa [IntermediateField.finrank_bot']).symm
  have hcmem : c ∈ E := algebraMap_mem_constantCompositum F K F'
    ⟨c, IntermediateField.mem_adjoin_simple_self k c⟩
  rw [hEbot, IntermediateField.mem_bot] at hcmem
  obtain ⟨a, rfl⟩ := hcmem
  obtain ⟨b, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp
    (isIntegral_algebraMap_iff.mp hci)
  exact ⟨b, IsScalarTower.algebraMap_apply k F F' b⟩

end Ramified

end TauCeti
