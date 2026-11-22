/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Finsupp.Basic

/-!
# Symmetries of the simple-pole divisor at `0` and `1`

Both the Riemann zeta function and the Dedekind zeta function of any number field have simple
poles at `0` and `1`, represented in `AnalyticLFunctionData` by the polar divisor
`Finsupp.single 0 1 + Finsupp.single 1 1`. This file records its invariance under complex
conjugation `s ↦ conj s` and functional-equation reflection `s ↦ 1 - conj s`.
-/

public section

open Complex ComplexConjugate

namespace TauCeti.LFunctions

/-- Conjugation preserves the simple-pole divisor at `0` and `1`. -/
theorem mapDomain_conj_single_zero_add_single_one :
    (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1).mapDomain conj =
      Finsupp.single 0 1 + Finsupp.single 1 1 := by
  simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single, map_zero, map_one]

/-- Evaluation of `Finsupp.single 0 1 + Finsupp.single 1 1` is invariant under conjugation. -/
theorem single_zero_add_single_one_conj (s : ℂ) :
    (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) (conj s) =
      (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) s := by
  have h := congrArg (fun d : ℂ →₀ ℕ ↦ d (conj s)) mapDomain_conj_single_zero_add_single_one.symm
  rwa [Finsupp.mapDomain_apply_of_injective (starRingEnd ℂ).injective] at h

/-- The simple-pole divisor at `0` and `1` is invariant under `s ↦ 1 - conj s`. -/
theorem single_zero_add_single_one_one_sub_conj (s : ℂ) :
    (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) (1 - conj s) =
      (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) s := by
  have h0 : (0 : ℂ) = 1 - conj s ↔ (1 : ℂ) = s := by
    rw [eq_comm, sub_eq_zero, eq_comm]
    exact (map_eq_one_iff _ (starRingEnd ℂ).injective).trans eq_comm
  have h1 : (1 : ℂ) = 1 - conj s ↔ (0 : ℂ) = s := by
    rw [eq_comm, sub_eq_self]
    exact (map_eq_zero_iff _ (starRingEnd ℂ).injective).trans eq_comm
  simp only [Finsupp.add_apply, Finsupp.single_apply, h0, h1]
  rw [add_comm]

end TauCeti.LFunctions
