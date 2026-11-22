/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Data.ENat.Monoid
import TauCeti.RingTheory.KrullDimension.Secant
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Tests for secant sequences

In `ℚ⟦X⟧`, of dimension one, both `[X]` and `[X²]` are secant: secancy does not single out a
uniformizer. Over any local ring, `[0]` and `[1]` are never secant for a nonzero module, and a
repeated entry `[r, r]` is never secant, since the second `r` acts on a module it already kills.
-/

open TauCeti Module IsLocalRing PowerSeries

/-- `X` lowers the dimension of `ℚ⟦X⟧` from one to zero. -/
example : IsSecant ℚ⟦X⟧ [(X : ℚ⟦X⟧)] := by
  have hX : (X : ℚ⟦X⟧) ∈ maximalIdeal ℚ⟦X⟧ := by
    simp [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
  have hdrop := supportDim_quotSMulTop_succ_eq_supportDim
    (IsSMulRegular.of_ne_zero (M := ℚ⟦X⟧) X_ne_zero) hX
  rw [supportDim_self_eq_ringKrullDim, IsDiscreteValuationRing.ringKrullDim_eq_one] at hdrop
  rw [isSecant_singleton_iff, supportDim_self_eq_ringKrullDim,
    IsDiscreteValuationRing.ringKrullDim_eq_one]
  exact ⟨hX, ENat.WithBot.lt_natCast_of_add_one_eq (k := 1) hdrop⟩

/-- `[X²]` is secant for `ℚ⟦X⟧` as well. -/
example (h : IsSecant ℚ⟦X⟧ [(X : ℚ⟦X⟧)]) : IsSecant ℚ⟦X⟧ [(X : ℚ⟦X⟧) ^ 2] :=
  (isSecant_append_pow_cons_iff [] [] X two_ne_zero).2 h

/-- `[0]` is never secant for a finite module: dividing by `0` does not change the support. -/
example {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] : ¬ IsSecant M [(0 : R)] := by
  rw [isSecant_singleton_iff, supportDim, supportDim, support_quotSMulTop,
    PrimeSpectrum.zeroLocus_singleton_zero, Set.inter_univ]
  exact fun h ↦ lt_irrefl _ h.2

/-- `[1]` is never secant, since `1 ∉ 𝔪`. -/
example {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] :
    ¬ IsSecant M [(1 : R)] :=
  fun h ↦ (maximalIdeal.isMaximal R).ne_top
    ((Ideal.eq_top_iff_one _).2 (h.mem_maximalIdeal 1 List.mem_cons_self))

/-- A repeated entry `[r, r]` is never secant for a finite module. -/
example {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (r : R) : ¬ IsSecant M [r, r] := by
  rw [isSecant_cons_iff, isSecant_singleton_iff]
  rintro ⟨-, -, -, h⟩
  rw [supportDim, supportDim, support_quotSMulTop, support_quotSMulTop,
    Set.inter_assoc, Set.inter_self] at h
  exact lt_irrefl _ h

/-- Only the empty list is secant for the zero module. -/
example {R : Type*} [CommRing R] [IsLocalRing R] (rs : List R) :
    IsSecant (PUnit : Type) rs ↔ rs = [] :=
  isSecant_iff_eq_nil
