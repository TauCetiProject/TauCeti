/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Basic
import Mathlib.Algebra.Module.LinearMap.DivisionRing
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Analysis.Normed.Module.LipschitzHyperplane

/-!
# Test vector fields vanishing normally on a hyperplane

A test vector field whose normal component `f ∘ χ` vanishes on a hyperplane `{f = a}` has normal
component `O (|f - a|)`: `StrongDual.exists_abs_apply_le_mul_abs_sub`.
-/

public section

open TopologicalSpace TestFunction
open scoped Distributions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A test vector field whose normal component `f ∘ χ` vanishes on the hyperplane `{f = a}` has
normal component `O (|f - a|)`. -/
theorem StrongDual.exists_abs_apply_le_mul_abs_sub (f : StrongDual ℝ E) (a : ℝ) {Ω : Opens E}
    {χ : 𝓓(Ω, E)} (hχ : ∀ x, f x = a → f (χ x) = 0) : ∃ C, ∀ x, |f (χ x)| ≤ C * |f x - a| := by
  by_cases hf : f = 0
  · exact ⟨0, fun x => by simp [hf]⟩
  obtain ⟨v, hv⟩ : ∃ v, f v = 1 :=
    LinearMap.surjective_iff_ne_zero.mpr (fun h => hf (ContinuousLinearMap.coe_injective
      (by simpa using h))) 1
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (χ.hasCompactSupport.comp_left (g := f) f.map_zero)
    (f.contDiff.comp (χ.contDiff.of_le (by simp))) one_ne_zero
  exact ⟨L * ‖v‖, fun x => by
    simpa using hL.norm_le_mul_abs_sub_of_eq_zero (f := f) hv hχ x⟩
