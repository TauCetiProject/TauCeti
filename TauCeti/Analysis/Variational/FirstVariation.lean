/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Convex.Function
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Analysis.Convex.Strong

/-!
# The first variation at a minimizer

Let `f` be a real energy on a real normed space `E`. This file records the first-order conditions
at a minimizer.

* **Affine constraints.** If `u` is a local minimizer of `f` on an affine subspace `S` and `f` has
  derivative `f'` at `u` within `S`, then the first variation `f' v` vanishes for every `v` in the
  direction of `S` (`IsLocalMinOn.hasFDerivWithinAt_apply_eq_zero_of_mem_direction`), since `v`
  and `-v` are both tangent to `S`. For `S = ⊤` this is Fermat's theorem
  `IsLocalMin.hasFDerivAt_eq_zero`.
* **Convex constraints.** If `u` is a local minimizer of `f` on a set `C` that is star-convex at
  `u` (for instance a convex set containing `u`) and `f` has derivative `f'` at `u` within `C`,
  then the **variational inequality** `f'(v - u) ≥ 0` holds for every `v ∈ C`
  (`IsLocalMinOn.hasFDerivWithinAt_apply_sub_nonneg`), since `v - u` lies in the positive tangent
  cone of `C` at `u`. Conversely, for `f` convex on `C` the variational inequality makes `u` a
  global minimizer on `C` (`ConvexOn.isMinOn_of_hasFDerivWithinAt_of_forall_apply_sub_nonneg`),
  so for convex energies the two are equivalent (`ConvexOn.isMinOn_iff_forall_apply_sub_nonneg`).
* **Directional derivatives.** The same inequality holds for the one-sided derivative of
  `t ↦ f(u + t (v - u))` at `0⁺`, wherever it exists, without differentiability of `f`
  (`IsLocalMinOn.nonneg_of_hasDerivWithinAt_add_smul_sub`).

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

/-- **The first variation vanishes at a minimizer on an affine subspace.** If `u ∈ S` is a local
minimizer of `f` on the affine subspace `S` and `f` has derivative `f'` at `u` within `S`, then
`f' v = 0` for every `v` in the direction of `S`. -/
theorem IsLocalMinOn.hasFDerivWithinAt_apply_eq_zero_of_mem_direction {S : AffineSubspace ℝ E}
    (hu : u ∈ S) (h : IsLocalMinOn f S u) (hf : HasFDerivWithinAt f f' S u) {v : E}
    (hv : v ∈ S.direction) : f' v = 0 :=
  -- Both `v` and `-v` are tangent to `S` at `u`, since the segments to `u ± v` stay in `S`.
  have hT {w : E} (hw : w ∈ S.direction) : w ∈ posTangentConeAt (S : Set E) u :=
    mem_posTangentConeAt_of_segment_subset
      (S.convex.segment_subset hu (by simpa [add_comm] using S.vadd_mem_of_mem_direction hw hu))
  h.hasFDerivWithinAt_eq_zero hf (hT hv) (hT (S.direction.neg_mem hv))

/-- **The variational inequality.** If `u` is a local minimizer of `f` on a set `C` that is
star-convex at `u` (for instance a convex set containing `u`) and `f` has derivative `f'` at `u`
within `C`, then `0 ≤ f' (v - u)` for every `v ∈ C`. -/
theorem IsLocalMinOn.hasFDerivWithinAt_apply_sub_nonneg {C : Set E}
    (h : IsLocalMinOn f C u) (hC : StarConvex ℝ u C) (hf : HasFDerivWithinAt f f' C u)
    {v : E} (hv : v ∈ C) : 0 ≤ f' (v - u) :=
  h.hasFDerivWithinAt_nonneg hf (sub_mem_posTangentConeAt_of_segment_subset (hC.segment_subset hv))

/-- **The variational inequality characterizes minimizers of convex energies.** If `f` is convex
on `C`, `u ∈ C`, `f` has derivative `f'` at `u` within `C` and `0 ≤ f' (v - u)` for every `v ∈ C`,
then `u` minimizes `f` on `C`. -/
theorem ConvexOn.isMinOn_of_hasFDerivWithinAt_of_forall_apply_sub_nonneg {C : Set E}
    (hfc : ConvexOn ℝ C f) (hu : u ∈ C) (hf : HasFDerivWithinAt f f' C u)
    (h : ∀ v ∈ C, 0 ≤ f' (v - u)) : IsMinOn f C u := fun v hv ↦
  (le_add_of_nonneg_right (h v hv)).trans (hfc.add_le_of_hasFDerivWithinAt hu hv hf)

/-- **Minimizers of a convex energy on a convex set.** If `f` is convex on `C`, `u ∈ C` and `f` has
derivative `f'` at `u` within `C`, then `u` minimizes `f` on `C` exactly when the variational
inequality `0 ≤ f' (v - u)` holds for every `v ∈ C`. -/
theorem ConvexOn.isMinOn_iff_forall_apply_sub_nonneg {C : Set E} (hfc : ConvexOn ℝ C f)
    (hu : u ∈ C) (hf : HasFDerivWithinAt f f' C u) :
    IsMinOn f C u ↔ ∀ v ∈ C, 0 ≤ f' (v - u) :=
  ⟨fun h _ hv ↦ h.isLocalMinOn.hasFDerivWithinAt_apply_sub_nonneg (hfc.1.starConvex hu) hf hv,
    hfc.isMinOn_of_hasFDerivWithinAt_of_forall_apply_sub_nonneg hu hf⟩

/-- **The variational inequality for one-sided directional derivatives.** If `u` is a local
minimizer of `f` on a set `C` that is star-convex at `u`, `v ∈ C`, and `t ↦ f (u + t • (v - u))`
has right derivative `d` at `0`, then `0 ≤ d`. No differentiability of `f` is assumed. -/
theorem IsLocalMinOn.nonneg_of_hasDerivWithinAt_add_smul_sub {C : Set E} (h : IsLocalMinOn f C u)
    (hC : StarConvex ℝ u C) {v : E} (hv : v ∈ C) {d : ℝ}
    (hd : HasDerivWithinAt (fun t : ℝ ↦ f (u + t • (v - u))) d (Ici 0) 0) : 0 ≤ d := by
  -- For `t ∈ [0, 1]` the point `u + t • (v - u)` lies in `C`, so `0` is a local minimizer of the
  -- restriction to `[0, ∞)`.
  have hline : Tendsto (fun t : ℝ ↦ u + t • (v - u)) (𝓝[Ici 0] 0) (𝓝[C] u) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      exact Continuous.tendsto' (by fun_prop) 0 u (by simp)
    · filter_upwards [Icc_mem_nhdsGE one_pos] with t ht
      exact hC.add_smul_sub_mem hv ht.1 ht.2
  have hmin : IsLocalMinOn (fun t : ℝ ↦ f (u + t • (v - u))) (Ici 0) 0 := by
    filter_upwards [hline.eventually h] with t ht
    simpa using ht
  exact hmin.hasDerivWithinAt_Ici_nonneg hd
