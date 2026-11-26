/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import TauCeti.Algebra.Polynomial.Derivative

/-!
# Polynomials over discrete valuation rings

For a polynomial `f` with unit leading coefficient over a discrete valuation ring `A`, the
additive valuation of the `(f.natDegree - 1)`-th coefficient of `f.derivative` equals the
additive valuation of `f.natDegree`. More generally, for a polynomial `f` of positive degree `n`,
the infimum `⨅ i : Fin n, (n • addVal A (f.coeff (i + 1) * (i + 1)) + (i + 1))` is finite if
and only if `f.derivative ≠ 0`.
-/

public section

namespace Polynomial

open IsDiscreteValuationRing

/-- For a polynomial `f` with unit leading coefficient over a discrete valuation ring `A`, the
additive valuation of the `(f.natDegree - 1)`-th coefficient of `f.derivative` equals
`addVal A (f.natDegree : A)`. -/
theorem addVal_coeff_derivative_natDegree_sub_one_of_isUnit_leadingCoeff
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (f : A[X]) (hu : IsUnit f.leadingCoeff) :
    addVal A ((derivative f).coeff (f.natDegree - 1)) = addVal A (f.natDegree : A) := by
  rw [coeff_derivative_natDegree_sub_one, addVal_mul, (addVal_eq_zero_iff).mpr hu, zero_add]

end Polynomial

namespace TauCeti

open Polynomial IsDiscreteValuationRing

/-- For a polynomial `f : R[X]` of positive degree `n` over a discrete valuation ring `R`, the
derivative valuation infimum `⨅ i : Fin n, (n • addVal R (f.coeff (i + 1) * (i + 1)) + (i + 1))`
is finite if and only if `f.derivative ≠ 0`. -/
theorem iInf_addVal_derivative_add_one_lt_top_iff
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {n : ℕ} (hn : 0 < n) {f : R[X]} (hdeg : f.natDegree = n) :
    (⨅ i : Fin n, n • addVal R (f.coeff (i + 1) * (i + 1)) + ((i : ℕ) + 1 : ℕ∞)) < ⊤ ↔
      f.derivative ≠ 0 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [iInf_lt_top]
  constructor
  · rintro ⟨i, hi⟩ hzero
    have hcoeff : f.coeff ((i : ℕ) + 1) * (((i : ℕ) : R) + 1) = 0 := by
      simpa [coeff_derivative] using congrArg (fun p : R[X] ↦ p.coeff i) hzero
    rw [hcoeff, addVal_zero] at hi
    cases n with
    | zero => omega
    | succ _ => simp at hi
  · intro hf'
    refine ⟨⟨f.derivative.natDegree, hdeg ▸ natDegree_derivative_lt (hdeg ▸ hn.ne')⟩, ?_⟩
    have hne :
        f.coeff (f.derivative.natDegree + 1) * ((f.derivative.natDegree : R) + 1) ≠ 0 := by
      rw [← coeff_derivative, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hf'
    lift addVal R (f.coeff (f.derivative.natDegree + 1) *
        ((f.derivative.natDegree : R) + 1)) to ℕ using
          (fun h ↦ hne (addVal_eq_top_iff.mp h)) with v hv
    rw [nsmul_eq_mul]
    exact_mod_cast ENat.natCast_lt_top (n * v + (f.derivative.natDegree + 1))

end TauCeti
