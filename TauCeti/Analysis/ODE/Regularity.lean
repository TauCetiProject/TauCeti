/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Regularity of solutions to first-order ODEs

This file contains the basic regularity theorem that a solution of a first-order equation gains one
derivative over a right-hand side that is already differentiable on its range. The parameter
set only needs unique derivatives, so the result also applies at closed interval endpoints. It
holds over any nontrivially normed field and for finite or infinite order of differentiability.
A solution of a time-dependent equation `x' = X(t, x)` with a jointly continuous right-hand side
is `C¹` (`TauCeti.contDiff_one_of_hasDerivAt`).
The same holds for a linear equation `f' = A_t f` whose coefficient `A` is `C^n` in `t`
(`TauCeti.contDiff_succ_of_hasDerivAt_clm_apply`).
For a field that is Lipschitz in time and state, a bound on the speed of a solution gives
a Lipschitz constant for its velocity (`IsIntegralCurveOn.lipschitzOnWith_velocity`).
-/

public section

open Set
open scoped ContDiff NNReal

/-- On a convex time set, a solution with speed at most `B` has `(K + L * B)`-Lipschitz
velocity if the field is `K`-Lipschitz in time and `L`-Lipschitz in state along the solution's
range. -/
theorem IsIntegralCurveOn.lipschitzOnWith_velocity {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {y : ℝ → E} {f : ℝ → E → E} {s : Set ℝ}
    {K L B : ℝ≥0} (hy : IsIntegralCurveOn y f s) (hs : Convex ℝ s)
    (hK : ∀ u ∈ y '' s, LipschitzOnWith K (fun t ↦ f t u) s)
    (hL : ∀ t ∈ s, LipschitzOnWith L (f t) (y '' s))
    (hB : ∀ t ∈ s, ‖f t (y t)‖₊ ≤ B) :
    LipschitzOnWith (K + L * B) (fun t ↦ f t (y t)) s := by
  have hyLip := hs.lipschitzOnWith_of_nnNorm_hasDerivWithin_le (fun t ht ↦ hy t ht) hB
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro t ht r hr
  calc
    dist (f t (y t)) (f r (y r)) ≤ dist (f t (y t)) (f r (y t)) +
        dist (f r (y t)) (f r (y r)) := dist_triangle _ _ _
    _ ≤ K * dist t r + L * dist (y t) (y r) :=
      add_le_add ((hK _ (mem_image_of_mem y ht)).dist_le_mul t ht r hr)
        ((hL r hr).dist_le_mul _ (mem_image_of_mem y ht) _ (mem_image_of_mem y hr))
    _ ≤ K * dist t r + L * (B * dist t r) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (hyLip.dist_le_mul t ht r hr) L.coe_nonneg)
    _ = (↑(K + L * B) : ℝ) * dist t r := by push_cast; ring

namespace TauCeti

/-- A solution of a first-order equation with a `C^n` right-hand side is `C^(n + 1)`
within any parameter set with unique derivatives. The order `n` may be infinite: a solution
of an equation with a smooth right-hand side is smooth. -/
theorem contDiffOn_succ_of_hasDerivWithinAt_comp {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞} {f : 𝕜 → F} {v : F → F} {s : Set 𝕜}
    {u : Set F} (hs : UniqueDiffOn 𝕜 s) (hv : ContDiffOn 𝕜 n v u) (hfu : MapsTo f s u)
    (hf : ∀ t ∈ s, HasDerivWithinAt f (v (f t)) s t) :
    ContDiffOn 𝕜 (n + 1) f s := by
  have key (m : ℕ) (hm : m ≤ n + 1) : ContDiffOn 𝕜 m f s := by
    induction m with
    | zero => exact contDiffOn_zero.mpr fun t ht ↦ (hf t ht).continuousWithinAt
    | succ m ih =>
      have hmn : (m : ℕ∞) ≤ n := by simpa using hm
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_derivWithin hs]
      refine ⟨fun t ht ↦ (hf t ht).differentiableWithinAt, by simp, ?_⟩
      exact ((hv.of_le (mod_cast hmn)).comp (ih (hmn.trans le_self_add)) hfu).congr
        fun t ht ↦ (hf t ht).derivWithin (hs t ht)
  exact_mod_cast contDiffOn_iff_forall_nat_le.mpr key

/-- A solution of a time-dependent first-order equation `x' = X(t, x)` with a jointly continuous
right-hand side is `C¹`. -/
theorem contDiff_one_of_hasDerivAt {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {X : 𝕜 → F → F} {x : 𝕜 → F}
    (hX : Continuous (Function.uncurry X)) (hx : ∀ t, HasDerivAt x (X t (x t)) t) :
    ContDiff 𝕜 1 x := by
  refine contDiff_one_iff_deriv.2 ⟨fun t ↦ (hx t).differentiableAt, ?_⟩
  rw [funext fun t ↦ (hx t).deriv]
  exact hX.comp (continuous_id.prodMk (continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt))

/-- A solution of a linear equation `f' = A_t f` whose coefficient `A` is `C^n` is `C^(n + 1)`.
The order `n` may be infinite. -/
theorem contDiff_succ_of_hasDerivAt_clm_apply {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞} {A : 𝕜 → F →L[𝕜] F} {f : 𝕜 → F}
    (hA : ContDiff 𝕜 n A) (hf : ∀ t, HasDerivAt f (A t (f t)) t) :
    ContDiff 𝕜 (n + 1) f := by
  have key (m : ℕ) (hm : m ≤ n + 1) : ContDiff 𝕜 m f := by
    induction m with
    | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.2 fun t ↦ (hf t).continuousAt)
    | succ m ih =>
      have hmn : (m : ℕ∞) ≤ n := by simpa using hm
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨fun t ↦ (hf t).differentiableAt, by simp, ?_⟩
      rw [show deriv f = fun t ↦ A t (f t) from funext fun t ↦ (hf t).deriv]
      exact (hA.of_le (mod_cast hmn)).clm_apply (ih (hmn.trans le_self_add))
  exact_mod_cast contDiff_iff_forall_nat_le.mpr key

end TauCeti

end
