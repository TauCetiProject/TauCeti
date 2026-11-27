/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Topology.Algebra.InfiniteSum.Module
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# The derivative of the periodization in the last coordinate

For a compactly supported map `f : E × ℝ → F`, the integer translates `(x, t) ↦ f (x, t + n)` are
locally finite (`TauCeti.exists_finset_eventually_eq_zero_add_intCast`), so the periodization
`Σₙ f (x, t + n)` is `C^k` when `f` is (`TauCeti.contDiff_tsum_add_intCast`). This file computes
its derivative: it is the sum of the translates of the derivative of `f`
(`TauCeti.fderiv_tsum_add_intCast_apply`).

* `TauCeti.fderiv_add_intCast_eq_zero`: a translate that vanishes near a point has vanishing
  derivative there.
* `TauCeti.fderiv_tsum_add_intCast_apply`: the derivative of the periodization of a compactly
  supported differentiable map is the sum of the translates of its derivative.
-/

public section

open Filter Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : E × ℝ → F}

/-- A translate that vanishes near `z` has vanishing derivative at `z`: if every translate
`w ↦ f (w.1, w.2 + n)` with `n ∉ S` vanishes near `z`, then `Df (z.1, z.2 + n) = 0` for `n ∉ S`. -/
theorem fderiv_add_intCast_eq_zero {S : Finset ℤ} {z : E × ℝ}
    (hS : ∀ᶠ w in 𝓝 z, ∀ n ∉ S, f (w.1, w.2 + n) = 0) {n : ℤ} (hn : n ∉ S) :
    fderiv ℝ f (z.1, z.2 + n) = 0 := by
  have h0 : (fun w : E × ℝ ↦ f (w.1, w.2 + n)) =ᶠ[𝓝 z] fun _ ↦ 0 := hS.mono fun w hw ↦ hw n hn
  rw [← fderiv_comp_add_snd, h0.fderiv_eq]
  simp

/-- **The derivative of the periodization is the sum of the translates of the derivative.** For a
compactly supported differentiable map `f`, the derivative of `z ↦ ∑ₙ f (z.1, z.2 + n)` at `z` in
the direction `v` is `∑ₙ Df (z.1, z.2 + n) v`. -/
theorem fderiv_tsum_add_intCast_apply (hf : Differentiable ℝ f) (hc : HasCompactSupport f)
    (z v : E × ℝ) :
    fderiv ℝ (fun w : E × ℝ ↦ ∑' n : ℤ, f (w.1, w.2 + n)) z v =
      ∑' n : ℤ, fderiv ℝ f (z.1, z.2 + n) v := by
  obtain ⟨S, hS⟩ := exists_finset_eventually_eq_zero_add_intCast hc z
  have hd (n : ℤ) : DifferentiableAt ℝ (fun w : E × ℝ ↦ f (w.1, w.2 + n)) z :=
    hf.differentiableAt.comp z
      (differentiableAt_fst.prodMk (differentiableAt_snd.add_const _))
  -- Near `z` the periodization is the finite sum over `S`.
  have hev : (fun w : E × ℝ ↦ ∑' n : ℤ, f (w.1, w.2 + n)) =ᶠ[𝓝 z]
      fun w ↦ ∑ n ∈ S, f (w.1, w.2 + n) := hS.mono fun w hw ↦ tsum_eq_sum hw
  rw [tsum_eq_sum fun n hn ↦ by rw [fderiv_add_intCast_eq_zero hS hn, zero_apply],
    hev.fderiv_eq, fderiv_fun_sum fun n _ ↦ hd n, sum_apply]
  simp only [fderiv_comp_add_snd]

end TauCeti
