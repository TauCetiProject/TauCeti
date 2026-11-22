/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Monotonicity of Fréchet derivatives of monotone functions

If a map `f : E → F` between preordered real topological vector spaces is monotone on a
neighbourhood of `x` and has Fréchet derivative `f'` at `x`, then `f'` is monotone, provided
addition preserves order in both `E` and `F` (`IsOrderedAddMonoid`), positive scaling preserves
order in `E` (`PosSMulMono ℝ E`), and the order on `F` is topologically closed
(`OrderClosedTopology F`). The proof tests the integer-scaled directional difference quotients
`n • (f (x + (n : ℝ)⁻¹ • v) - f x)` as `n → ∞` and passes to the limit via the order-closed
topology on `F`, requiring no scalar-monotonicity hypothesis on `F`.

## Main results

* `HasFDerivAt.monotone_of_monotoneOn`: a Fréchet derivative of a function monotone on a
  neighbourhood of the point is monotone when addition preserves order in both spaces, positive
  scaling preserves order in the domain, and the codomain order is topologically closed.
* `HasFDerivAt.monotone_of_monotone`: the corresponding global-monotonicity specialization under
  the same order hypotheses.
-/

public section

open Filter Set
open scoped Topology

variable {E F : Type*}
  [AddCommGroup E] [Preorder E] [IsOrderedAddMonoid E] [TopologicalSpace E] [Module ℝ E]
  [ContinuousAdd E] [ContinuousSMul ℝ E] [PosSMulMono ℝ E]
  [AddCommGroup F] [Preorder F] [IsOrderedAddMonoid F] [TopologicalSpace F] [Module ℝ F]
  [ContinuousAdd F] [ContinuousSMul ℝ F] [OrderClosedTopology F]

/-- If `f` is monotone on a neighbourhood of `x` and has Fréchet derivative `f'` at `x`, then `f'`
is monotone, provided addition preserves order in both spaces, positive scaling preserves order in
the domain, and the codomain order is topologically closed. -/
theorem HasFDerivAt.monotone_of_monotoneOn {f : E → F} {f' : E →L[ℝ] F} {x : E} {s : Set E}
    (hf : HasFDerivAt f f' x) (hs : s ∈ 𝓝 x) (hm : MonotoneOn f s) : Monotone f' := by
  intro u w huw
  rw [← sub_nonneg, ← map_sub]
  set v : E := w - u
  have hv : 0 ≤ v := sub_nonneg.2 huw
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hd : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • v) atTop (𝓝 0) := by
    simpa only [zero_smul] using hinv.smul_const v
  have hmem : ∀ᶠ n : ℕ in atTop, x + (n : ℝ)⁻¹ • v ∈ s :=
    (by simpa using hd.const_add x :
      Tendsto (fun n : ℕ => x + (n : ℝ)⁻¹ • v) atTop (𝓝 x)).eventually hs
  have hslope : Tendsto (fun n : ℕ => (n : ℝ) • (f (x + (n : ℝ)⁻¹ • v) - f x))
      atTop (𝓝 (f' v)) := by
    refine hf.hasFDerivWithinAt.lim hd (Eventually.of_forall fun _ => mem_univ _)
      (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [smul_smul, mul_inv_cancel₀ (Nat.cast_pos.2 hn).ne', one_smul]
  refine ge_of_tendsto hslope ?_
  filter_upwards [hmem] with n hn
  have hle : x ≤ x + (n : ℝ)⁻¹ • v :=
    le_add_of_nonneg_right (smul_nonneg (inv_nonneg.2 (Nat.cast_nonneg n)) hv)
  have hdiff : 0 ≤ f (x + (n : ℝ)⁻¹ • v) - f x := sub_nonneg.2 (hm (mem_of_mem_nhds hs) hn hle)
  simpa only [Nat.cast_smul_eq_nsmul] using nsmul_nonneg hdiff n

/-- If `f` is globally monotone and has Fréchet derivative `f'` at `x`, then `f'` is monotone,
provided addition preserves order in both spaces, positive scaling preserves order in the domain,
and the codomain order is topologically closed. -/
theorem HasFDerivAt.monotone_of_monotone {f : E → F} {f' : E →L[ℝ] F} {x : E}
    (hf : HasFDerivAt f f' x) (hm : Monotone f) : Monotone f' :=
  hf.monotone_of_monotoneOn univ_mem (hm.monotoneOn _)
