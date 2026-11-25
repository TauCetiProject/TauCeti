/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Deriv.Comp
import TauCeti.Analysis.Convex.Strong

/-!
# The first variation at a minimizer

Let `f` be a real energy on a real normed space `E`. This file records the first-order conditions
at a minimizer.

* **Affine constraints.** If `u` is a local minimizer of `f` on the affine subspace `u + W` and
  `f` is Fréchet differentiable at `u`, then the first variation `df(u) v` vanishes for every
  `v ∈ W` (`IsLocalMinOn.hasFDerivAt_apply_eq_zero_of_mem`). For `W = E` this is Fermat's
  theorem `IsLocalMin.hasFDerivAt_eq_zero`.
* **Convex constraints.** If `u` is a local minimizer of `f` on a convex set `C` and `f` has
  derivative `f'` at `u` within `C`, then the **variational inequality** `f'(v - u) ≥ 0` holds for
  every `v ∈ C` (`IsLocalMinOn.hasFDerivWithinAt_apply_sub_nonneg`), since `v - u` lies in the
  positive tangent cone of `C` at `u`. Conversely, for `f` convex on `C` the variational inequality
  makes `u` a global minimizer on `C` (`ConvexOn.isMinOn_of_forall_hasFDerivWithinAt_nonneg`), so
  for convex energies the two are equivalent
  (`ConvexOn.isMinOn_iff_forall_hasFDerivWithinAt_nonneg`).
* **Directional derivatives.** The same inequality holds for the one-sided derivative of
  `t ↦ f(u + t (v - u))` at `0⁺`, wherever it exists, without differentiability of `f`
  (`IsLocalMinOn.nonneg_of_hasDerivWithinAt_lineMap`).

The two-sided form, `f' y = 0` when both `y` and `-y` are tangent to the constraint, is Mathlib's
`IsLocalMinOn.hasFDerivWithinAt_eq_zero` and `IsLocalMinOn.fderivWithin_eq_zero`.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, Definition 4.3 and the remark on
  critical points following it.
-/

public section

open Filter Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ}
  {u : E}

/-- **The first variation vanishes at a minimizer on an affine subspace.** If `u` is a local
minimizer of `f` on the affine subspace `u + W = {w | w - u ∈ W}` and `f` has Fréchet derivative
`f'` at `u`, then `f' v = 0` for every `v ∈ W`. -/
theorem IsLocalMinOn.hasFDerivAt_apply_eq_zero_of_mem {W : Submodule ℝ E}
    (h : IsLocalMinOn f {w | w - u ∈ W} u) (hf : HasFDerivAt f f' u) {v : E} (hv : v ∈ W) :
    f' v = 0 := by
  -- Along the line `t ↦ u + t • v`, which stays in `u + W`, `u` is an unconstrained minimizer.
  have hline : Tendsto (fun t : ℝ ↦ u + t • v) (𝓝 0) (𝓝[{w | w - u ∈ W}] u) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun t ↦ ?_⟩
    · exact Continuous.tendsto' (by fun_prop) 0 u (by simp)
    · simpa using W.smul_mem t hv
  have hmin : IsLocalMin (fun t : ℝ ↦ f (u + t • v)) 0 := by
    filter_upwards [hline.eventually h] with t ht
    simpa using ht
  have hd : HasDerivAt (fun t : ℝ ↦ f (u + t • v)) (f' v) 0 := by
    have := hf.comp_hasDerivAt_of_eq (0 : ℝ)
      (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u) (by simp)
    rw [one_smul] at this
    exact this
  exact hmin.hasDerivAt_eq_zero hd

/-- **The variational inequality.** If `u` is a local minimizer of `f` on a convex set `C` and `f`
has derivative `f'` at `u` within `C`, then `0 ≤ f' (v - u)` for every `v ∈ C`. -/
theorem IsLocalMinOn.hasFDerivWithinAt_apply_sub_nonneg {C : Set E}
    (h : IsLocalMinOn f C u) (hC : Convex ℝ C) (hu : u ∈ C) (hf : HasFDerivWithinAt f f' C u)
    {v : E} (hv : v ∈ C) : 0 ≤ f' (v - u) :=
  h.hasFDerivWithinAt_nonneg hf
    (sub_mem_posTangentConeAt_of_segment_subset (hC.segment_subset hu hv))

/-- **The variational inequality characterizes minimizers of convex energies.** If `f` is convex
on `C`, `u ∈ C`, `f` has derivative `f'` at `u` within `C` and `0 ≤ f' (v - u)` for every `v ∈ C`,
then `u` minimizes `f` on `C`. -/
theorem ConvexOn.isMinOn_of_forall_hasFDerivWithinAt_nonneg {C : Set E} (hfc : ConvexOn ℝ C f)
    (hu : u ∈ C) (hf : HasFDerivWithinAt f f' C u) (h : ∀ v ∈ C, 0 ≤ f' (v - u)) :
    IsMinOn f C u := fun v hv ↦
  (le_add_of_nonneg_right (h v hv)).trans (hfc.add_le_of_hasFDerivWithinAt hu hv hf)

/-- **Minimizers of a convex energy on a convex set.** If `f` is convex on `C`, `u ∈ C` and `f` has
derivative `f'` at `u` within `C`, then `u` minimizes `f` on `C` exactly when the variational
inequality `0 ≤ f' (v - u)` holds for every `v ∈ C`. -/
theorem ConvexOn.isMinOn_iff_forall_hasFDerivWithinAt_nonneg {C : Set E} (hfc : ConvexOn ℝ C f)
    (hu : u ∈ C) (hf : HasFDerivWithinAt f f' C u) :
    IsMinOn f C u ↔ ∀ v ∈ C, 0 ≤ f' (v - u) :=
  ⟨fun h _ hv ↦ h.isLocalMinOn.hasFDerivWithinAt_apply_sub_nonneg hfc.1 hu hf hv,
    hfc.isMinOn_of_forall_hasFDerivWithinAt_nonneg hu hf⟩

/-- **The variational inequality for one-sided directional derivatives.** If `u` is a local
minimizer of `f` on a convex set `C`, `v ∈ C`, and `t ↦ f (u + t • (v - u))` has right derivative
`d` at `0`, then `0 ≤ d`. No differentiability of `f` is assumed. -/
theorem IsLocalMinOn.nonneg_of_hasDerivWithinAt_lineMap {C : Set E} (h : IsLocalMinOn f C u)
    (hC : Convex ℝ C) (hu : u ∈ C) {v : E} (hv : v ∈ C) {d : ℝ}
    (hd : HasDerivWithinAt (fun t : ℝ ↦ f (u + t • (v - u))) d (Ici 0) 0) : 0 ≤ d := by
  -- For `t ∈ [0, 1]` the point `u + t • (v - u)` lies in `C`, so `0` is a local minimizer of the
  -- restriction to `[0, 1]`.
  have hline : Tendsto (fun t : ℝ ↦ u + t • (v - u)) (𝓝[Icc 0 1] 0) (𝓝[C] u) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht ↦ ?_⟩
    · refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      exact Continuous.tendsto' (by fun_prop) 0 u (by simp)
    · have := hC.add_smul_sub_mem hu hv ht
      simpa using this
  have hmin : IsLocalMinOn (fun t : ℝ ↦ f (u + t • (v - u))) (Icc 0 1) 0 := by
    filter_upwards [hline.eventually h] with t ht
    simpa using ht
  have h1 : (1 : ℝ) ∈ posTangentConeAt (Icc (0 : ℝ) 1) 0 :=
    mem_posTangentConeAt_of_segment_subset (by simp [segment_eq_Icc])
  simpa using hmin.hasFDerivWithinAt_nonneg
    ((hd.mono Icc_subset_Ici_self).hasFDerivWithinAt) h1
