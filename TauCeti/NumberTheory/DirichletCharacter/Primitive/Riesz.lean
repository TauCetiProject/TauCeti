/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Primitive.RayClass
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.RemainderMellin
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.VonMangoldt
public import TauCeti.NumberTheory.LFunctions.Hecke.RieszRemainder.Basic
import Mathlib.NumberTheory.LSeries.Injectivity
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.VonMangoldtCoeff

/-!
# Riesz coefficients and Mellin expressions over ℚ

Under `PrimitiveDirichletCharacter.toPrimitiveRayClassCharacter`, the ideal von Mangoldt
coefficients grouped by norm become `χ(n) Λ(n)`. This identifies the inputs to first Riesz
smoothing on the two sides. The main-term correction uses the Dirichlet logarithmic derivative
for nontrivial characters and Euler's constant for the trivial character. The meromorphic
Mellin expressions also agree: their normalization from punctured germs does not depend on
which value the input L-function takes at its pole.
-/

public section

open ArithmeticFunction Filter TauCeti.LFunctions
open scoped LSeries.notation

namespace TauCeti.PrimitiveDirichletCharacter

/-- Grouping the ideal von Mangoldt coefficients of a rational primitive ray class character
by norm gives the twisted von Mangoldt coefficients of the corresponding Dirichlet character. -/
@[simp] theorem normCoeff_vonMangoldtTransform_toPrimitiveRayClassCharacter
    (ψ : PrimitiveDirichletCharacter) (n : ℕ) :
    normCoeff ℚ (IdealArithmeticFunction.vonMangoldtTransform
      (toPrimitiveRayClassCharacter ψ).character.toUnitaryIdealWeight.toIdealArithmeticFunction)
        n = ψ.character n * Λ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  let χ := (toPrimitiveRayClassCharacter ψ).character.toUnitaryIdealWeight
  let f := χ.toIdealArithmeticFunction
  have habs {s : ℂ} (hs : 1 < s.re) : idealAbscissaOfAbsConv ℚ f < s.re :=
    idealAbscissaOfAbsConv_lt_re_of_bounded (f := f) (C := 1) (fun I ↦ by
      simpa [f] using χ.norm_le_one I) hs
  have hsum {s : ℂ} (hs : 1 < s.re) :=
    IdealArithmeticFunction.summable_idealTerm_vonMangoldtTransform (f := f) (habs hs)
  have htwo : 1 < (2 : ℂ).re := by norm_num
  have hseries : LSeries (normCoeff ℚ f) = LSeries (↗ψ.character) := by
    funext s
    exact LSeries_congr (fun {_} hk ↦ ψ.normCoeff_toPrimitiveRayClassCharacter hk) s
  suffices normCoeff ℚ f.vonMangoldtTransform n = (↗ψ.character * ↗Λ) n by
    simpa only [Pi.mul_apply] using this
  refine LSeries.eq_of_LSeries_eventually_eq (f := normCoeff ℚ f.vonMangoldtTransform)
    (g := ↗ψ.character * ↗Λ) ?_ ?_ ?_ hn
  · exact (LSeriesSummable_normCoeff ℚ (hsum htwo)).abscissaOfAbsConv_le.trans_lt
      (EReal.coe_lt_top _)
  · have hχ := DirichletCharacter.LSeriesSummable_twist_vonMangoldt ψ.character htwo
    exact hχ.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx' : 1 < (x : ℂ).re := by simpa using hx
    have hxval : idealAbscissaOfAbsConv ℚ χ.val.toIdealArithmeticFunction < (x : ℂ).re := by
      rw [← χ.toIdealArithmeticFunction_eq_val]
      exact habs hx'
    have hlog := χ.val.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform hxval
    rw [← χ.toIdealArithmeticFunction_eq_val] at hlog
    rw [LSeries_normCoeff ℚ (hsum hx'), ← neg_inj, ← hlog, hseries, logDeriv_apply,
      DirichletCharacter.LSeries_twist_vonMangoldt_eq _ hx', neg_div, neg_neg]

/-- The rational ray class remainder of a nontrivial primitive Dirichlet character uses the
Dirichlet coefficients and the Dirichlet logarithmic derivative at `1`. -/
theorem rieszRemainder_toPrimitiveRayClassCharacter_of_ne_one
    (ψ : PrimitiveDirichletCharacter) (hψ : ψ ≠ 1) (y : ℝ) :
    (toPrimitiveRayClassCharacter ψ).rieszRemainder y =
      rieszSum (fun n ↦ ψ.character n * Λ n) y + (y : ℂ) * logDeriv ψ.character.LFunction 1 := by
  have hη : toPrimitiveRayClassCharacter ψ ≠ 1 := by
    rw [← toPrimitiveRayClassCharacter_one]
    exact fun h ↦ hψ (toPrimitiveRayClassCharacter.injective h)
  have hχ : ψ.character ≠ 1 := by
    intro h
    exact hψ (by rw [← of_character ψ, h, of_one])
  have hL : heckeLFunctionC (toPrimitiveRayClassCharacter ψ).character = ψ.character.LFunction :=
    funext fun _ ↦ ψ.heckeLFunctionC_toPrimitiveRayClassCharacter_apply (.inr hχ)
  have hcoeff : (toPrimitiveRayClassCharacter ψ).rieszCoeff = fun n : ℕ ↦ ψ.character n * Λ n :=
    (PrimitiveRayClassCharacter.rieszCoeff_def _).trans
      (funext (normCoeff_vonMangoldtTransform_toPrimitiveRayClassCharacter ψ))
  rw [PrimitiveRayClassCharacter.rieszRemainder_of_ne_one _ hη, hcoeff, hL]

/-- For the trivial rational ray class character the coefficients are `Λ(n)` and the
logarithmic main term uses Euler's constant. -/
theorem rieszRemainder_one_rat (y : ℝ) :
    (1 : PrimitiveRayClassCharacter ℚ).rieszRemainder y =
      rieszSum (fun n ↦ (Λ n : ℂ)) y +
        ((y * (1 + Real.eulerMascheroniConstant) - y * Real.log y : ℝ) : ℂ) := by
  have h := funext (normCoeff_vonMangoldtTransform_toPrimitiveRayClassCharacter 1)
  simp only [← PrimitiveRayClassCharacter.rieszCoeff_def, toPrimitiveRayClassCharacter_one,
    PrimitiveRayClassCharacter.rieszCoeff_one] at h
  have hχ (n : ℕ) : (1 : PrimitiveDirichletCharacter).character n = 1 := by
    rw [character_one, MulChar.one_apply]
    have : Subsingleton (ZMod (1 : PrimitiveDirichletCharacter).level) := by
      rw [level_one]
      exact (inferInstance : Subsingleton (ZMod 1))
    exact isUnit_of_subsingleton _
  simp only [PrimitiveRayClassCharacter.rieszRemainder_one,
    NumberField.eulerKroneckerConstant_rat, h, hχ, one_mul]

/-- The first Riesz Mellin expressions of a primitive Dirichlet character and its rational
ray class character agree as meromorphic normal forms. -/
@[simp] theorem rieszRemainderMellin_toPrimitiveRayClassCharacter
    (ψ : PrimitiveDirichletCharacter) :
    rieszRemainderMellin (heckeLFunctionC (toPrimitiveRayClassCharacter ψ).character) =
      rieszRemainderMellin ψ.character.LFunction :=
  rieszRemainderMellin_congr ψ.heckeLFunctionC_toPrimitiveRayClassCharacter_eventuallyEq

end TauCeti.PrimitiveDirichletCharacter
