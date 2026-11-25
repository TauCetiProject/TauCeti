/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Meromorphic.TrailingCoefficient

/-!
# Trailing coefficients under scaling of the variable

Mathlib's `meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt` shows that the
trailing coefficient is invariant under translation of the variable. Scaling the variable by a
nonzero constant `c` instead multiplies it by `c ^ n`, where `n` is the meromorphic order:
`TauCeti.meromorphicTrailingCoeffAt_comp_mul_const`. Both are special cases of Mathlib's
`MeromorphicAt.meromorphicTrailingCoeffAt_comp`.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- Scaling the variable by a nonzero constant `c` multiplies the trailing coefficient by
`c ^ n`, where `n` is the meromorphic order at the scaled point. -/
theorem meromorphicTrailingCoeffAt_comp_mul_const {f : 𝕜 → E} {x c : 𝕜} (hc : c ≠ 0) :
    meromorphicTrailingCoeffAt (f ∘ (· * c)) x =
      c ^ (meromorphicOrderAt f (x * c)).untop₀ • meromorphicTrailingCoeffAt f (x * c) := by
  classical
  by_cases hf : MeromorphicAt f (x * c)
  · have hlin : (fun z ↦ z * c - x * c) = (fun _ ↦ c) * (· - x) := by
      funext z
      simp only [Pi.mul_apply]
      ring
    have hnc : ¬EventuallyConst (· * c) (𝓝 x) := by
      have hg : AnalyticAt 𝕜 (· * c) x := by fun_prop
      simp [eventuallyConst_iff_analyticOrderAt_sub_eq_top,
        hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero (by simp [hc])]
    rw [MeromorphicAt.meromorphicTrailingCoeffAt_comp (g := (· * c)) hf (by fun_prop) hnc, hlin,
      analyticAt_const.meromorphicAt.meromorphicTrailingCoeffAt_mul (by fun_prop),
      meromorphicTrailingCoeffAt_const, meromorphicTrailingCoeffAt_id_sub_const]
    simp
  · have hcomp : ¬MeromorphicAt (f ∘ (· * c)) x := fun h ↦ hf <| by
      simpa [Function.comp_def, mul_assoc, hc] using
        (show MeromorphicAt (f ∘ (· * c)) ((x * c) * c⁻¹) by simpa [hc] using h).comp_analyticAt
          (g := (· * c⁻¹)) (by fun_prop)
    simp [hf, hcomp]

end TauCeti
