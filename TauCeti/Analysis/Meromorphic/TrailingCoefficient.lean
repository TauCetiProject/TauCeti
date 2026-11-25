/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import TauCeti.Analysis.Calculus.IteratedDeriv.Leibniz

/-!
# Trailing coefficients of analytic germs and under scaling

At an analytic germ of order `n`, the trailing coefficient is the `n`-th Taylor coefficient
(`AnalyticAt.meromorphicTrailingCoeffAt_eq_inv_factorial_smul_iteratedDeriv`).

Mathlib's `meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt` shows that the
trailing coefficient is invariant under translation of the variable. Scaling the variable by a
nonzero constant `c` instead multiplies it by `c ^ n`, where `n` is the meromorphic order:
`TauCeti.meromorphicTrailingCoeffAt_comp_mul_const`. Both are special cases of Mathlib's
`MeromorphicAt.meromorphicTrailingCoeffAt_comp`.
-/

public section

open Filter Topology

/-- At an analytic point of finite order `n`, the trailing coefficient is the Taylor
coefficient of degree `n`. -/
theorem AnalyticAt.meromorphicTrailingCoeffAt_eq_inv_factorial_smul_iteratedDeriv
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {f : 𝕜 → E} {x : 𝕜} {n : ℕ}
    (hf : AnalyticAt 𝕜 f x) (hn : analyticOrderAt f x = n) :
    meromorphicTrailingCoeffAt f x = (n.factorial : 𝕜)⁻¹ • iteratedDeriv n f x := by
  obtain ⟨g, hg, hg₀, heq⟩ := hf.analyticOrderAt_eq_natCast.mp hn
  have hlocal : f =ᶠ[𝓝 x] fun z ↦ (z - x) ^ n • g z := heq
  have hpunct : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ (n : ℤ) • g z := by
    simpa only [zpow_natCast] using hlocal.filter_mono nhdsWithin_le_nhds
  rw [hg.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hg₀ hpunct,
    hlocal.iteratedDeriv_eq n,
    TauCeti.iteratedDeriv_pow_sub_smul_self hg.contDiffAt,
    ← Nat.cast_smul_eq_nsmul 𝕜, inv_smul_smul₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero)]

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
