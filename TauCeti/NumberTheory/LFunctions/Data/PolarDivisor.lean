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

Both the completed Riemann zeta function and the completed Dedekind zeta function of any number
field have simple poles at `0` and `1`, represented in `AnalyticLFunctionData` by the polar
divisor `Finsupp.single 0 1 + Finsupp.single 1 1`. This file records its invariance under complex
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

/-- Functional-equation reflection `z ↦ 1 - conj z` preserves the simple-pole divisor at `0`
and `1`. -/
theorem mapDomain_one_sub_conj_single_zero_add_single_one :
    (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1).mapDomain (fun z ↦ 1 - conj z) =
      Finsupp.single 0 1 + Finsupp.single 1 1 := by
  simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single, map_zero, map_one, sub_zero,
    sub_self, add_comm]

/-- The simple-pole divisor at `0` and `1` is invariant under `s ↦ 1 - conj s`. -/
theorem single_zero_add_single_one_one_sub_conj (s : ℂ) :
    (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) (1 - conj s) =
      (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) s := by
  have hinj : Function.Injective (fun z : ℂ ↦ 1 - conj z) :=
    fun z w h ↦ (starRingEnd ℂ).injective (sub_right_inj.mp h)
  have h := congrArg (fun d : ℂ →₀ ℕ ↦ d (1 - conj s))
    mapDomain_one_sub_conj_single_zero_add_single_one.symm
  rwa [Finsupp.mapDomain_apply_of_injective hinj] at h

end TauCeti.LFunctions
