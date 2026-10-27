/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.MinimalPolynomial
import Mathlib.RingTheory.Polynomial.RationalRoot
import TauCeti.RingTheory.Affinoid.Integral
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniqueFactorization

/-!
# Minimal equations with zero divisors and nilpotents

The dual-number algebra over a Tate algebra has a nonzero square-zero generator. Its minimal
polynomial is `X²`, and the minimal-equation formula for the supremum seminorm gives value zero
on this generator. The formula therefore applies without reducing the target algebra.

The algebraic divisibility theorem also applies to products over the integers, without a field
as coefficient ring. These checks distinguish torsion-freeness from the domain assumption.
-/

public section

open Polynomial

section Product

-- A product with two components, over a base which is not a field.
example {p : ℤ[X]} (hp : aeval ((0, 1) : ℤ × ℤ) p = 0) :
    minpoly ℤ ((0, 1) : ℤ × ℤ) ∣ p := by
  have hs : IsIntegral ℤ ((0, 1) : ℤ × ℤ) :=
    ⟨X * (X - 1), monic_X.mul (monic_X_sub_C 1), by
      ext <;> simp⟩
  exact TauCeti.minpoly.isIntegrallyClosed_dvd_of_isTorsionFree hs hp

end Product

namespace TauCeti.Examples

open _root_.MvPowerSeries (IsRestricted)

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "T" => IsRestricted.subring (R := K) (fun _ : Fin 1 ↦ 1)
local notation "D" => AdjoinRoot ((X : T[X]) ^ 2)

-- The generator is nonzero, so this is a nonreduced target, not a zero-algebra check.
example : AdjoinRoot.root ((X : T[X]) ^ 2) ≠ 0 := by
  simpa only [AdjoinRoot.mk_X] using
    AdjoinRoot.mk_ne_zero_of_natDegree_lt (monic_X_pow 2) (X_ne_zero (R := T)) (by simp)

example : AdjoinRoot.root ((X : T[X]) ^ 2) ^ 2 = 0 := by
  rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]

/-- The dual-number generator retains its minimal equation of degree two and has
supremum seminorm zero. -/
theorem tateDualNumbers_minpoly_and_supSeminorm :
    minpoly T (AdjoinRoot.root ((X : T[X]) ^ 2)) = X ^ 2 ∧
    supSeminorm K (AdjoinRoot.root ((X : T[X]) ^ 2)) = 0 := by
  have : Module.Free T D := (monic_X_pow 2).free_adjoinRoot
  have : Module.Finite T D := (monic_X_pow 2).finite_adjoinRoot
  have hD : IsAffinoidAlgebra K D := (isAffinoidAlgebra_tate (K := K) (σ := Fin 1)).of_finite
  have h := hD.supSeminorm_eq_iSup_minpoly_coeff_rpow (A := T)
    (AdjoinRoot.root ((X : T[X]) ^ 2))
  have hs := AdjoinRoot.isIntegral_root' (monic_X_pow (R := T) 2)
  have hmin : minpoly T (AdjoinRoot.root ((X : T[X]) ^ 2)) = X ^ 2 := by
    have hdiv := TauCeti.minpoly.isIntegrallyClosed_dvd_of_isTorsionFree (p := X ^ 2) hs (by simp)
    have hrev : X ^ 2 ∣ minpoly T (AdjoinRoot.root ((X : T[X]) ^ 2)) := by
      rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
      exact minpoly.aeval _ _
    exact eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hs) (monic_X_pow 2) hdiv
      (natDegree_le_of_dvd hrev (minpoly.ne_zero hs)) |>.symm
  refine ⟨hmin, ?_⟩
  rw [hmin, natDegree_X_pow] at h
  have ht (i : Fin 2) : supSeminorm K (((X : T[X]) ^ 2).coeff i) ^
      (1 / (2 - i : ℝ)) = 0 := by
    rw [coeff_X_pow, ite_eq_right (Nat.ne_of_lt i.isLt), supSeminorm_zero, Real.zero_rpow]
    exact one_div_ne_zero (sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_lt i.isLt).symm))
  simpa only [Nat.cast_ofNat, ht, ciSup_const] using h

end TauCeti.Examples
