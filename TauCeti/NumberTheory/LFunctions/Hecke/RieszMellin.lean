/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.BigOperators
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.RemainderMellin
public import TauCeti.NumberTheory.LFunctions.Hecke.Conjugate

/-!
# Conjugation of Hecke Riesz Mellin expressions

Taking the inverse ray class character reflects the normalized Mellin expression across the real
axis. Thus an inverse-paired average, the expression that corresponds to the real part of a
Riesz remainder, has conjugation symmetry, as does any finite real-weighted sum of such averages.
The equality includes the canonical values of the individual expressions at poles.

The application to real parts of Riesz remainders follows the normalization in L. Alpöge's
`Deduction.Gm` and `Deduction.Gchi_conj`.
-/

public section

open ComplexConjugate

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- Inverting a ray class character and reflecting the argument conjugate the normalized Riesz
Mellin value. No primitivity assumption is needed. -/
@[simp] theorem rieszRemainderMellin_heckeLFunctionC_inv_conj {𝔪 : Modulus K}
    (χ : RayClassCharacter 𝔪) (s : ℂ) :
    rieszRemainderMellin (heckeLFunctionC χ⁻¹) (conj s) =
      conj (rieszRemainderMellin (heckeLFunctionC χ) s) := by
  simp [heckeLFunctionC_inv]

/-- The real-weighted sum of the inverse-paired Hecke Riesz Mellin expressions is invariant
under reflection across the real axis followed by complex conjugation. The support of the
weights need not be closed under inversion. -/
theorem conj_finsupp_sum_rieszRemainderMellin_heckeLFunctionC
    (w : PrimitiveRayClassCharacter K →₀ ℝ) (s : ℂ) :
    conj (w.sum fun ψ c ↦ (c : ℂ) *
      ((rieszRemainderMellin (heckeLFunctionC ψ.character) (conj s) +
        rieszRemainderMellin (heckeLFunctionC ψ⁻¹.character) (conj s)) / 2)) =
      w.sum fun ψ c ↦ (c : ℂ) *
        ((rieszRemainderMellin (heckeLFunctionC ψ.character) s +
          rieszRemainderMellin (heckeLFunctionC ψ⁻¹.character) s) / 2) := by
  rw [Finsupp.sum, map_sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun ψ _ ↦ ?_
  have h := rieszRemainderMellin_heckeLFunctionC_inv_conj ψ.character (conj s)
  rw [Complex.conj_conj] at h
  simp only [PrimitiveRayClassCharacter.character_inv, ← h,
    rieszRemainderMellin_heckeLFunctionC_inv_conj, map_mul, map_div₀, map_add,
    Complex.conj_ofReal, map_ofNat, Complex.conj_conj]
  rw [add_comm]

end TauCeti.LFunctions
