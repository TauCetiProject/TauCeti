/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Hecke.Basic
public import TauCeti.Analysis.Meromorphic.ZeroFree
import TauCeti.Analysis.Calculus.LogDeriv.Symmetry
import TauCeti.Analysis.Meromorphic.Conj
import TauCeti.Analysis.Meromorphic.Continuation.Conjugate
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Regroup

/-!
# Conjugation of presented Hecke L-functions

The inverse of a ray class character has the conjugate Hecke L-function at conjugate arguments.
The identity holds in meromorphic normal form on the whole plane and so also identifies orders
and logarithmic derivatives. In particular, the inverse character has the same zero-free right
half-planes, and its logarithmic derivative at `1` is the conjugate of the original one.
-/

public section

open scoped ComplexConjugate

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- The continued Hecke L-function of the inverse character is the reflection of the original
one. The equality includes the canonical values at poles. -/
theorem heckeLFunctionC_inv (χ : RayClassCharacter 𝔪) :
    heckeLFunctionC χ⁻¹ = conj ∘ heckeLFunctionC χ ∘ conj := by
  have hseries :
      LSeries (normCoeff K χ⁻¹.toUnitaryIdealWeight.toIdealArithmeticFunction) =
        conj ∘ LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction) ∘ conj := by
    funext s
    simp only [RayClassCharacter.toUnitaryIdealWeight_inv,
      UnitaryIdealWeight.toIdealArithmeticFunction_eq_val, UnitaryIdealWeight.val_conj,
      MultiplicativeIdealWeight.toIdealArithmeticFunction_conj]
    simpa [Complex.star_def] using
      LSeries_normCoeff_star K χ.toUnitaryIdealWeight.val.toIdealArithmeticFunction (conj s)
  simp only [heckeLFunctionC_def, hseries, meromorphicContinuation_conj_conj]

/-- Inversion and reflection of the argument conjugate the continued Hecke L-value. -/
@[simp]
theorem heckeLFunctionC_inv_conj (χ : RayClassCharacter 𝔪) (s : ℂ) :
    heckeLFunctionC χ⁻¹ (conj s) = conj (heckeLFunctionC χ s) := by
  simp [heckeLFunctionC_inv]

/-- Inverting the character reflects the meromorphic orders of its L-function. -/
@[simp]
theorem meromorphicOrderAt_heckeLFunctionC_inv_conj (χ : RayClassCharacter 𝔪) (s : ℂ) :
    meromorphicOrderAt (heckeLFunctionC χ⁻¹) (conj s) =
      meromorphicOrderAt (heckeLFunctionC χ) s := by
  rw [heckeLFunctionC_inv, meromorphicOrderAt_conj_conj, Complex.conj_conj]

/-- A presented Hecke L-function and that of the inverse character have the same zero-free
right half-planes. -/
@[simp]
theorem zeroFreeRightOf_heckeLFunctionC_inv_iff (χ : RayClassCharacter 𝔪) (σ : ℝ) :
    ZeroFreeRightOf σ (heckeLFunctionC χ⁻¹) ↔ ZeroFreeRightOf σ (heckeLFunctionC χ) := by
  rw [heckeLFunctionC_inv, zeroFreeRightOf_conj_conj_iff]

/-- Inversion and reflection of the argument conjugate the logarithmic derivative of the
continued Hecke L-function. -/
@[simp]
theorem logDeriv_heckeLFunctionC_inv_conj (χ : RayClassCharacter 𝔪) (s : ℂ) :
    logDeriv (heckeLFunctionC χ⁻¹) (conj s) = conj (logDeriv (heckeLFunctionC χ) s) := by
  simp [heckeLFunctionC_inv, logDeriv_conj_conj]

end TauCeti.LFunctions
