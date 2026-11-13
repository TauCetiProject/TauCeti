/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.LyapunovPerron.Local
import TauCeti.Analysis.ODE.LyapunovPerron.Convergence
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Local invariant graphs for differentiable vector fields

At a zero `x` of a finite-dimensional `C^n` vector field `V`, suppose its derivative `A`
admits an exponential dichotomy with commuting stable projection `P`. Confined forward
solutions in displacement coordinates, restricted to a small stable parameter window, form a
`C^n` graph over `range P`; confined backward solutions, restricted to a small unstable
parameter window, form a `C^n` graph over `range (1 - P)`. Both graphs are tangent to their
linear subspaces at the origin. No inner product, symmetry of `A`, gradient representation,
or completeness of the nonlinear flow is required.

The radii of confinement and of the graph domain are chosen from local regularity of `V`.
The graph descriptions include every confined solution whose initial stable or unstable
coordinate lies in the respective parameter window, not just the solutions constructed by
the fixed-point argument. Each confined solution tends to the equilibrium in the
appropriate time direction. These are local graph theorems, not assertions that global
stable sets are embedded or that graphs depend differentiably on a vector-field parameter.

The construction uses the cutoff graphs of
`ContinuousLinearMap.localStableGraphMap` and `ContinuousLinearMap.localUnstableGraphMap`.
It applies their small-nonlinearity estimates to `V (x + z) - A z`, whose derivative at zero
vanishes. This is the vector-field form of the localization argument used for gradients in
`TauCeti.Analysis.Calculus.Morse.LocalInvariantManifold`.

The graphs depend continuously in `C¹` on the vector field. Let `Vs i` be `C¹` vector fields
whose derivatives converge to the derivative of `V`, uniformly on a neighbourhood of `x`, and
whose zeros `xs i` converge to `x`. The zero may move and the linearization of `Vs i` at `xs i`
need not be `A`. Reading every remainder `z ↦ Vs i (xs i + z) - A z` against the fixed
dichotomy of `A`, one confinement radius and one parameter radius serve `V` and, eventually,
every `Vs i`. The local stable graphs of `Vs i` at `xs i` then converge uniformly to that of
`V` at `x`, and so do their derivatives on the compact piece of the graph over a closed
parameter ball. The same holds for the local unstable graphs. Transversality arguments for
stable and unstable manifolds use this continuity of their compact pieces under `C¹`-small
perturbations of the field.

## Main results

* `ContinuousLinearMap.exists_localStableGraph_of_contDiffAt` and
  `ContinuousLinearMap.exists_localUnstableGraph_of_contDiffAt`: the local stable and unstable
  sets of a `C^n` vector field at a hyperbolic zero are `C^n` graphs.
* `ContinuousLinearMap.exists_localStableGraph_tendstoUniformlyOn_fderiv` and
  `ContinuousLinearMap.exists_localUnstableGraph_tendstoUniformlyOn_fderiv`: these graphs depend
  continuously in `C¹` on the vector field.

## References

* C. Chicone, *Ordinary Differential Equations with Applications*, second edition,
  Springer, 2006, §4.3 (the stable-manifold theorem and the dependence of invariant manifolds
  on the vector field).
* W. A. Coppel, *Dichotomies in Stability Theory*, Springer, 1978, Chapter 5
  (the Lyapunov–Perron construction).
-/

public section

open Filter Metric Set Topology
open scoped NNReal

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {V : E → E} {x : E} {n : ℕ} {A : E →L[ℝ] E} {K α : ℝ≥0}

/-- A positive Lipschitz constant small enough for the cut-off Lyapunov--Perron construction with
dichotomy constants `K` and `α`. -/
private theorem exists_pos_two_mul_mul_lt (hα : 0 < α) :
    ∃ ε : ℝ≥0, 0 < ε ∧ 2 * K * (ε * 2) < α := by
  refine ⟨α / (8 * (K + 1)), by positivity, ?_⟩
  have hαR : (0 : ℝ) < α := hα
  apply NNReal.coe_lt_coe.1
  push_cast
  rw [div_mul_eq_mul_div, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
  nlinarith [mul_nonneg α.coe_nonneg K.coe_nonneg]

/-- Local regularity makes the nonlinear remainder small on a ball and uniformly smooth
there; the smaller graph-parameter ball stays strictly inside that ball. -/
private theorem exists_vectorField_remainder_data (hn : 1 ≤ n) (hV : ContDiffAt ℝ n V x)
    (hA : HasFDerivAt V A x) (hα : 0 < α) :
    ∃ ε : ℝ≥0, ∃ r > 0, ∃ ρ > 0,
      LipschitzOnWith ε (fun z ↦ V (x + z) - A z) (closedBall 0 r) ∧
      HasFDerivAt (fun z ↦ V (x + z) - A z) (0 : E →L[ℝ] E) 0 ∧
      2 * K * (ε * 2) < α ∧
      UniformContDiffOn ℝ n (fun z ↦ V (x + z) - A z) (ball 0 r) ∧
      (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ρ < r ∧
      (∀ z ∈ closedBall (0 : E) ρ,
        (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ‖z‖ < r) := by
  let N : E → E := fun z ↦ V (x + z) - A z
  have hN : ContDiffAt ℝ n N 0 := by
    have hVx : ContDiffAt ℝ n V (x + 0) := by simpa using hV
    exact (hVx.comp 0 (contDiffAt_const.add contDiffAt_id)).sub A.contDiff.contDiffAt
  have hVx : HasFDerivAt (fun z ↦ V (x + z)) A 0 := by
    rw [hasFDerivAt_comp_add_left]
    simpa using hA
  have hN' : HasFDerivAt N (0 : E →L[ℝ] E) 0 := by
    simpa only [N, Pi.sub_def, sub_self] using hVx.sub A.hasFDerivAt
  obtain ⟨ε, hε, hsmall⟩ := exists_pos_two_mul_mul_lt (K := K) hα
  have hN1 : ContDiffAt ℝ 1 N 0 := hN.of_le (by exact_mod_cast hn)
  obtain ⟨s, hs, hNs⟩ := (hN1.hasStrictFDerivAt hN' one_ne_zero).exists_lipschitzOnWith_of_nnNorm_lt
    ε (by simpa using hε)
  obtain ⟨r₁, hr₁, hr₁s⟩ := Metric.mem_nhds_iff.1 hs
  obtain ⟨r₂, hr₂, hNn⟩ := hN.exists_uniformContDiffOn_closedBall
  let r := min (r₁ / 2) r₂
  have hr : 0 < r := lt_min (by positivity) hr₂
  have hsmallR : 2 * (K : ℝ) * ((ε : ℝ) * 2) < α := by exact_mod_cast hsmall
  have hbound : 0 ≤ (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) :=
    div_nonneg K.coe_nonneg (by have := (div_lt_one (show (0 : ℝ) < α from hα)).2 hsmallR; linarith)
  obtain ⟨ρ, hρ, hρr⟩ := exists_pos_mul_lt hr
    ((K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α))
  refine ⟨ε, r, hr, ρ, hρ, hNs.mono ?_, hN', hsmall, hNn.mono ?_, hρr, ?_⟩
  · exact (closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (by linarith))).trans hr₁s
  · exact ball_subset_closedBall.trans (closedBall_subset_closedBall (min_le_right _ _))
  · intro z hz
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hz) hbound).trans_lt hρr

/-- The remainder `z ↦ w (c + z) - A z` of a `C¹` field `w` at a base point `c` is `ε`-Lipschitz on
the closed ball of radius `r` when `‖Dw - A‖ ≤ ε` on the closed ball of radius `r` around `c`; its
derivative `z ↦ Dw (c + z) - A` is uniformly continuous on the open ball, by compactness. -/
private theorem remainder_data_of_nnNorm_fderiv_sub_le {w : E → E} {c : E} {S : Set E}
    (hS : IsOpen S) (hw : ContDiffOn ℝ 1 w S) {r : ℝ} (hrS : closedBall c r ⊆ S) {ε : ℝ≥0}
    (hwA : ∀ y ∈ closedBall c r, ‖fderiv ℝ w y - A‖₊ ≤ ε) :
    LipschitzOnWith ε (fun z ↦ w (c + z) - A z) (closedBall 0 r) ∧
      (∀ z ∈ closedBall (0 : E) r,
        HasFDerivAt (fun z ↦ w (c + z) - A z) (fderiv ℝ w (c + z) - A) z) ∧
      UniformContinuousOn (fun z ↦ fderiv ℝ w (c + z) - A) (ball 0 r) := by
  have hmem {z : E} (hz : z ∈ closedBall (0 : E) r) : c + z ∈ closedBall c r := by
    simpa [dist_eq_norm] using hz
  have hd {z : E} (hz : z ∈ closedBall (0 : E) r) :
      HasFDerivAt (fun z ↦ w (c + z) - A z) (fderiv ℝ w (c + z) - A) z :=
    ((hasFDerivAt_comp_add_left c).2 ((hw.contDiffAt (hS.mem_nhds (hrS (hmem hz)))).differentiableAt
      one_ne_zero).hasFDerivAt).sub A.hasFDerivAt
  have huc : UniformContinuousOn (fderiv ℝ w) (closedBall c r) :=
    (isCompact_closedBall c r).uniformContinuousOn_of_continuous
      ((hw.continuousOn_fderiv_of_isOpen hS le_rfl).mono hrS)
  refine ⟨(convex_closedBall 0 r).lipschitzOnWith_of_nnNorm_hasFDerivWithin_le
    (fun z hz ↦ (hd hz).hasFDerivWithinAt) (fun z hz ↦ hwA _ (hmem hz)), fun z hz ↦ hd hz, ?_⟩
  exact (uniformContinuous_id.sub uniformContinuous_const).comp_uniformContinuousOn
    (huc.comp (uniformContinuous_const.add uniformContinuous_id).uniformContinuousOn
      fun z hz ↦ hmem (ball_subset_closedBall hz))

variable {ι : Type*} {l : Filter ι} {Vs : ι → E → E} {xs : ι → E} {U : Set E}

/-- **Remainders of a `C¹`-convergent family of vector fields.** Let `Vs i` be `C¹` near `x`, with
zeros `xs i → x` and derivatives converging uniformly to the derivative of `V`, which vanishes at
`x` with derivative `A`. Read against the fixed linear part `A`, one radius `r` and one Lipschitz
constant `ε` serve the remainder of `V` at `x` and, eventually, the remainders of `Vs i` at
`xs i`; these remainders and their derivatives converge uniformly on the closed ball of
radius `r`. -/
private theorem exists_vectorField_remainder_tendsto (hU : U ∈ 𝓝 x)
    (hVU : ContDiffOn ℝ 1 V U) (hx : V x = 0) (hA : HasFDerivAt V A x)
    (hVsU : ∀ᶠ i in l, ContDiffOn ℝ 1 (Vs i) U) (hxs : Tendsto xs l (𝓝 x))
    (hVsx : ∀ᶠ i in l, Vs i (xs i) = 0)
    (hVs' : TendstoUniformlyOn (fun i ↦ fderiv ℝ (Vs i)) (fderiv ℝ V) l U) (hα : 0 < α) :
    ∃ ε : ℝ≥0, ∃ r > 0, 2 * K * (ε * 2) < α ∧
      LipschitzOnWith ε (fun z ↦ V (x + z) - A z) (closedBall 0 r) ∧
      (∀ z ∈ closedBall (0 : E) r,
        HasFDerivAt (fun z ↦ V (x + z) - A z) (fderiv ℝ V (x + z) - A) z) ∧
      UniformContinuousOn (fun z ↦ fderiv ℝ V (x + z) - A) (ball 0 r) ∧
      (∀ᶠ i in l, Vs i (xs i) = 0 ∧
        LipschitzOnWith ε (fun z ↦ Vs i (xs i + z) - A z) (closedBall 0 r) ∧
        (∀ z ∈ closedBall (0 : E) r,
          HasFDerivAt (fun z ↦ Vs i (xs i + z) - A z) (fderiv ℝ (Vs i) (xs i + z) - A) z) ∧
        UniformContinuousOn (fun z ↦ fderiv ℝ (Vs i) (xs i + z) - A) (ball 0 r)) ∧
      TendstoUniformlyOn (fun i z ↦ Vs i (xs i + z) - A z) (fun z ↦ V (x + z) - A z) l
        (closedBall 0 r) ∧
      TendstoUniformlyOn (fun i z ↦ fderiv ℝ (Vs i) (xs i + z) - A)
        (fun z ↦ fderiv ℝ V (x + z) - A) l (closedBall 0 r) := by
  obtain ⟨ε, hε, hsmall⟩ := exists_pos_two_mul_mul_lt (K := K) hα
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.1 hU
  have hVR : ContDiffOn ℝ 1 V (ball x R) := hVU.mono hRU
  obtain ⟨δ, hδ, hδA⟩ := Metric.continuousAt_iff.1
    ((hVR.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).continuousAt (ball_mem_nhds x hR))
    (ε / 2) (by positivity)
  rw [hA.fderiv] at hδA
  -- Work on the compact ball of radius `2 r` around `x`, on which every field is `C¹` and
  -- `DV` is `ε / 2`-close to `A`; it contains the `r`-balls around the nearby zeros.
  obtain ⟨r, hr, hrR, hrδ⟩ : ∃ r > 0, r ≤ R / 4 ∧ r ≤ δ / 4 :=
    ⟨min (R / 4) (δ / 4), lt_min (by positivity) (by positivity), min_le_left _ _,
      min_le_right _ _⟩
  have hbig : closedBall x (2 * r) ⊆ ball x R := closedBall_subset_ball (by linarith)
  have hVA (y : E) (hy : y ∈ closedBall x (2 * r)) : ‖fderiv ℝ V y - A‖ < ε / 2 := by
    rw [← dist_eq_norm]
    exact hδA ((mem_closedBall.1 hy).trans_lt (by linarith))
  have hshift {c : E} (hc : dist c x ≤ r) : closedBall c r ⊆ closedBall x (2 * r) :=
    closedBall_subset_closedBall' (by linarith)
  have hxx : dist x x ≤ r := by simpa using hr.le
  obtain ⟨hN, hNd, hN'⟩ := remainder_data_of_nnNorm_fderiv_sub_le isOpen_ball hVR
    ((hshift hxx).trans hbig) fun y hy ↦ by
      rw [← NNReal.coe_le_coe, coe_nnNorm]
      linarith [hVA y (hshift hxx hy), ε.coe_nonneg]
  -- Eventually the zero `xs i` is `r`-close to `x` and `D(Vs i)` is `ε / 2`-close to `DV`.
  have hnear : ∀ᶠ i in l, ContDiffOn ℝ 1 (Vs i) U ∧ Vs i (xs i) = 0 ∧ dist (xs i) x ≤ r ∧
      ∀ y ∈ U, ‖fderiv ℝ (Vs i) y - fderiv ℝ V y‖ < ε / 2 := by
    filter_upwards [hVsU, hVsx, Metric.tendsto_nhds.1 hxs r hr,
      Metric.tendstoUniformlyOn_iff.1 hVs' (ε / 2) (by positivity)] with i hi hix hxr hi'
    exact ⟨hi, hix, hxr.le, fun y hy ↦ by simpa [dist_eq_norm, norm_sub_rev] using hi' y hy⟩
  have hT : ∀ᶠ i in l, MapsTo (xs i + ·) (closedBall (0 : E) r) (closedBall x (2 * r)) :=
    hnear.mono fun i hi z hz ↦ hshift hi.2.2.1 (by simpa [dist_eq_norm] using hz)
  have hgood : ∀ᶠ i in l, Vs i (xs i) = 0 ∧
      LipschitzOnWith ε (fun z ↦ Vs i (xs i + z) - A z) (closedBall 0 r) ∧
      (∀ z ∈ closedBall (0 : E) r,
        HasFDerivAt (fun z ↦ Vs i (xs i + z) - A z) (fderiv ℝ (Vs i) (xs i + z) - A) z) ∧
      UniformContinuousOn (fun z ↦ fderiv ℝ (Vs i) (xs i + z) - A) (ball 0 r) :=
    hnear.mono fun i hi ↦ ⟨hi.2.1, remainder_data_of_nnNorm_fderiv_sub_le
    isOpen_ball (hi.1.mono hRU) ((hshift hi.2.2.1).trans hbig) fun y hy ↦ by
      rw [← NNReal.coe_le_coe, coe_nnNorm]
      linarith [hi.2.2.2 y (hRU (hbig (hshift hi.2.2.1 hy))), hVA y (hshift hi.2.2.1 hy),
        norm_sub_le_norm_sub_add_norm_sub (fderiv ℝ (Vs i) y) (fderiv ℝ V y) A]⟩
  -- Reading `D(Vs i)` at the moving base points `xs i` costs only the uniform continuity of `DV`.
  have hconv' : TendstoUniformlyOn (fun i z ↦ fderiv ℝ (Vs i) (xs i + z) - A)
      (fun z ↦ fderiv ℝ V (x + z) - A) l (closedBall 0 r) :=
    ((hVs'.mono (hbig.trans hRU)).comp_tendstoUniformlyOn
      ((isCompact_closedBall x (2 * r)).uniformContinuousOn_of_continuous
        ((hVR.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).mono hbig))
      ((hxs.tendstoUniformlyOn_const _).add (tendstoUniformlyOn_const id l _)) hT
      fun z hz ↦ hshift hxx (by simpa [dist_eq_norm] using hz)).sub
      (tendstoUniformlyOn_const (fun _ ↦ A) l _)
  refine ⟨ε, r, hr, hsmall, hN, hNd, hN', hgood, ?_, hconv'⟩
  -- The remainders agree at `0`, so the mean value theorem converts uniform convergence of their
  -- derivatives on the convex ball into uniform convergence of their values.
  refine Metric.tendstoUniformlyOn_iff.2 fun e he ↦ ?_
  obtain ⟨d, hd, hde⟩ := exists_pos_mul_lt he r
  filter_upwards [hgood, Metric.tendstoUniformlyOn_iff.1 hconv' d hd] with i hi hi' z hz
  have hmvt := (convex_closedBall (0 : E) r).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun w hw ↦ ((hi.2.2.1 w hw).sub (hNd w hw)).hasFDerivWithinAt)
    (fun w hw ↦ by simpa [dist_eq_norm, norm_sub_rev] using (hi' w hw).le)
    (mem_closedBall_self hr.le) hz
  rw [dist_eq_norm, norm_sub_rev]
  calc _ ≤ d * ‖z‖ := by simpa [hi.1, hx] using hmvt
    _ ≤ d * r := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hz) hd.le
    _ < e := by linarith

/-- **Regularized remainders of a `C¹`-convergent family.** Under the hypotheses of
`TauCeti.exists_vectorField_remainder_tendsto`, the remainders `F i` and their derivatives `F' i`
can be chosen to satisfy the hypotheses of the cut-off construction at every index: they agree
eventually with `z ↦ Vs i (xs i + z) - A z` and its derivative, and at the remaining indices with
the remainder of `V`. The parameter radius `ρ` keeps every Lyapunov--Perron solution with a
parameter in the closed ball of radius `ρ` strictly inside the ball of confinement. -/
private theorem exists_vectorField_remainder_tendsto_data (hU : U ∈ 𝓝 x)
    (hVU : ContDiffOn ℝ 1 V U) (hx : V x = 0) (hA : HasFDerivAt V A x)
    (hVsU : ∀ᶠ i in l, ContDiffOn ℝ 1 (Vs i) U) (hxs : Tendsto xs l (𝓝 x))
    (hVsx : ∀ᶠ i in l, Vs i (xs i) = 0)
    (hVs' : TendstoUniformlyOn (fun i ↦ fderiv ℝ (Vs i)) (fderiv ℝ V) l U) (hα : 0 < α) :
    ∃ ε : ℝ≥0, ∃ r > 0, ∃ ρ > 0, ∃ F : ι → E → E, ∃ F' : ι → E → E →L[ℝ] E,
      2 * K * (ε * 2) < α ∧ (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ρ < r ∧
      (∀ z ∈ closedBall (0 : E) ρ, (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ‖z‖ < r) ∧
      LipschitzOnWith ε (fun z ↦ V (x + z) - A z) (closedBall 0 r) ∧
      (∀ z ∈ ball (0 : E) r,
        HasFDerivAt (fun z ↦ V (x + z) - A z) (fderiv ℝ V (x + z) - A) z) ∧
      UniformContinuousOn (fun z ↦ fderiv ℝ V (x + z) - A) (ball 0 r) ∧
      (∀ i, LipschitzOnWith ε (F i) (closedBall 0 r)) ∧ (∀ i, F i 0 = 0) ∧
      (∀ i, ∀ z ∈ ball (0 : E) r, HasFDerivAt (F i) (F' i z) z) ∧
      (∀ i, UniformContinuousOn (F' i) (ball 0 r)) ∧
      TendstoUniformlyOn F (fun z ↦ V (x + z) - A z) l (closedBall 0 r) ∧
      TendstoUniformlyOn F' (fun z ↦ fderiv ℝ V (x + z) - A) l (ball 0 r) ∧
      ∀ᶠ i in l, ∀ z, A z + F i z = Vs i (xs i + z) := by
  classical
  obtain ⟨ε, r, hr, hsmall, hN, hNd, hN', hgood, hconv, hconv'⟩ :=
    exists_vectorField_remainder_tendsto (K := K) hU hVU hx hA hVsU hxs hVsx hVs' hα
  -- The indices at which the remainder of `Vs i` satisfies the estimates of the construction.
  let good : ι → Prop := fun i ↦ Vs i (xs i) = 0 ∧
    LipschitzOnWith ε (fun z ↦ Vs i (xs i + z) - A z) (closedBall 0 r) ∧
    (∀ z ∈ closedBall (0 : E) r,
      HasFDerivAt (fun z ↦ Vs i (xs i + z) - A z) (fderiv ℝ (Vs i) (xs i + z) - A) z) ∧
    UniformContinuousOn (fun z ↦ fderiv ℝ (Vs i) (xs i + z) - A) (ball 0 r)
  let F : ι → E → E := fun i ↦
    if good i then fun z ↦ Vs i (xs i + z) - A z else fun z ↦ V (x + z) - A z
  let F' : ι → E → E →L[ℝ] E := fun i ↦
    if good i then fun z ↦ fderiv ℝ (Vs i) (xs i + z) - A else fun z ↦ fderiv ℝ V (x + z) - A
  have hFgood : ∀ᶠ i in l, F i = (fun z ↦ Vs i (xs i + z) - A z) ∧
      F' i = fun z ↦ fderiv ℝ (Vs i) (xs i + z) - A :=
    hgood.mono fun i hi ↦ by
      have hi : good i := hi
      simp [F, F', hi]
  obtain ⟨ρ, hρ, hρr⟩ := exists_pos_mul_lt hr ((K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α))
  have hB : 0 ≤ (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) := by
    have hsmallR : 2 * (K : ℝ) * ((ε : ℝ) * 2) < α := by exact_mod_cast hsmall
    have := (div_lt_one (NNReal.coe_pos.2 hα)).2 hsmallR
    exact div_nonneg K.coe_nonneg (by linarith)
  refine ⟨ε, r, hr, ρ, hρ, F, F', hsmall, hρr, fun z hz ↦
    (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hz) hB).trans_lt hρr,
    hN, fun z hz ↦ hNd z (ball_subset_closedBall hz), hN', fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_,
    fun i ↦ ?_, hconv.congr (hFgood.mono fun i hi ↦ by rw [hi.1]; exact fun _ _ ↦ rfl),
    (hconv'.mono ball_subset_closedBall).congr
      (hFgood.mono fun i hi ↦ by rw [hi.2]; exact fun _ _ ↦ rfl),
    hFgood.mono fun i hi z ↦ by simp [hi.1]⟩
  · by_cases hi : good i <;> simp only [F, hi, ↓reduceIte]
    exacts [hi.2.1, hN]
  · by_cases hi : good i
    · simp [F, hi, hi.1]
    · simp [F, hi, hx]
  · by_cases hi : good i <;> simp only [F, F', hi, ↓reduceIte]
    exacts [fun z hz ↦ hi.2.2.1 z (ball_subset_closedBall hz),
      fun z hz ↦ hNd z (ball_subset_closedBall hz)]
  · by_cases hi : good i <;> simp only [F', hi, ↓reduceIte]
    exacts [hi.2.2.2, hN']

end TauCeti

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (A P : E →L[ℝ] E) {V : E → E} {x : E} {n : ℕ} {K α : ℝ≥0}
  (hs : ∀ t : ℝ, 0 ≤ t → ∀ z : E,
    ‖NormedSpace.exp (t • A) (P z)‖ ≤ K * Real.exp (-α * t) * ‖z‖)
  (hu : ∀ t : ℝ, t ≤ 0 → ∀ z : E,
    ‖NormedSpace.exp (t • A) (z - P z)‖ ≤ K * Real.exp (α * t) * ‖z‖)
  (hα : 0 < α) (hP : IsIdempotentElem P) (hAP : Commute A P)
  (hn : 1 ≤ n) (hV : ContDiffAt ℝ n V x) (hx : V x = 0) (hA : HasFDerivAt V A x)

include hs hu hα hP hAP hn hV hx hA

/-- **Local stable graph for a `C^n` vector field.** At an equilibrium whose derivative has
an exponential dichotomy, all forward solutions confined to a sufficiently small ball,
truncated in the stable coordinate, form a Lipschitz `C^n` graph tangent to `range P`.
Every forward solution confined to that ball tends to the equilibrium. -/
theorem exists_localStableGraph_of_contDiffAt :
    ∃ r > 0, ∃ ρ > 0, ∃ g : E → E, ∃ C : ℝ≥0,
      LipschitzWith C g ∧ g 0 = 0 ∧ HasFDerivAt g (0 : E →L[ℝ] E) 0 ∧
      (∀ z ∈ closedBall (0 : E) ρ, ContDiffAt ℝ n g z) ∧
      (∀ z, P (g z) = 0) ∧ (∀ z, g (P z) = g z) ∧
      {z : E | (∃ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ V (x + w)) (Ici 0) ∧
        y 0 = z ∧ MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖P z‖ ≤ ρ} =
        (fun z ↦ z + g z) '' (Set.range P ∩ closedBall 0 ρ) ∧
      (∀ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ V (x + w)) (Ici 0) →
        MapsTo y (Ici 0) (closedBall 0 r) → Tendsto y atTop (𝓝 0)) := by
  obtain ⟨ε, r, hr, ρ, hρ, hN, hN', hsmall, hNn, hρbound, hball⟩ :=
    TauCeti.exists_vectorField_remainder_data (K := K) hn hV hA hα
  let N : E → E := fun z ↦ V (x + z) - A z
  have hN0 : N 0 = 0 := by simp [N, hx]
  have hfield : (fun (_ : ℝ) z ↦ A z + N z) = fun (_ : ℝ) z ↦ V (x + z) := by
    funext _ z
    simp [N]
  let g := localStableGraphMap A P N r hs hu hr.le hN hsmall
  refine ⟨r, hr, ρ, hρ, g, _, lipschitzWith_localStableGraphMap hs hu hr.le hN hsmall,
    localStableGraphMap_zero hs hu hr.le hN hsmall hN0,
    hasFDerivAt_localStableGraphMap_zero hs hu hr.le hN hsmall hN0 hN',
    fun z hz ↦ contDiffAt_localStableGraphMap_of_uniformContDiffOn hs hu hr.le hN hsmall
      hN0 hNn (hball z hz),
    apply_localStableGraphMap hs hu hr.le hN hsmall hP hAP,
    localStableGraphMap_map hs hu hr.le hN hsmall hP, ?_, ?_⟩
  · have hset := setOf_exists_isIntegralCurveOn_mapsTo_closedBall_eq_image hs hu hr.le hN
      hsmall hN0 hP hAP hρbound.le
    rwa [hfield] at hset
  · intro y hy hmaps
    exact tendsto_of_isIntegralCurveOn_mapsTo_closedBall hs hu hN hsmall hN0 hP hAP
      (hfield ▸ hy) hmaps

/-- **Local unstable graph for a `C^n` vector field.** At the same equilibrium as in the
stable graph theorem, backward solutions confined to a sufficiently small ball, truncated
in the unstable coordinate, form a Lipschitz `C^n` graph tangent to `range (1 - P)`.
Every backward solution confined to that ball tends to the equilibrium as time tends to
negative infinity. -/
theorem exists_localUnstableGraph_of_contDiffAt :
    ∃ r > 0, ∃ ρ > 0, ∃ g : E → E, ∃ C : ℝ≥0,
      LipschitzWith C g ∧ g 0 = 0 ∧ HasFDerivAt g (0 : E →L[ℝ] E) 0 ∧
      (∀ z ∈ closedBall (0 : E) ρ, ContDiffAt ℝ n g z) ∧
      (∀ z, (ContinuousLinearMap.id ℝ E - P) (g z) = 0) ∧
      (∀ z, g ((ContinuousLinearMap.id ℝ E - P) z) = g z) ∧
      {z : E | (∃ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ V (x + w)) (Iic 0) ∧
        y 0 = z ∧ MapsTo y (Iic 0) (closedBall 0 r)) ∧ ‖z - P z‖ ≤ ρ} =
        (fun z ↦ z + g z) '' (Set.range (ContinuousLinearMap.id ℝ E - P) ∩ closedBall 0 ρ) ∧
      (∀ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ V (x + w)) (Iic 0) →
        MapsTo y (Iic 0) (closedBall 0 r) → Tendsto y atBot (𝓝 0)) := by
  obtain ⟨ε, r, hr, ρ, hρ, hN, hN', hsmall, hNn, hρbound, hball⟩ :=
    TauCeti.exists_vectorField_remainder_data (K := K) hn hV hA hα
  let N : E → E := fun z ↦ V (x + z) - A z
  have hN0 : N 0 = 0 := by simp [N, hx]
  have hfield : (fun (_ : ℝ) z ↦ A z + N z) = fun (_ : ℝ) z ↦ V (x + z) := by
    funext _ z
    simp [N]
  let g := localUnstableGraphMap A P N r hs hu hr.le hN hsmall
  refine ⟨r, hr, ρ, hρ, g, _, lipschitzWith_localUnstableGraphMap hs hu hr.le hN hsmall,
    localUnstableGraphMap_zero hs hu hr.le hN hsmall hN0,
    hasFDerivAt_localUnstableGraphMap_zero hs hu hr.le hN hsmall hN0 hN',
    fun z hz ↦ contDiffAt_localUnstableGraphMap_of_uniformContDiffOn hs hu hr.le hN hsmall
      hN0 hNn (hball z hz), ?_,
    localUnstableGraphMap_sub_map hs hu hr.le hN hsmall hP, ?_, ?_⟩
  · intro z
    simp only [sub_apply, id_apply, sub_eq_zero]
    exact (apply_localUnstableGraphMap hs hu hr.le hN hsmall hP hAP z).symm
  · have hset := setOf_exists_isIntegralCurveOn_Iic_mapsTo_closedBall_eq_image hs hu hr.le hN
      hsmall hN0 hP hAP hρbound.le
    rwa [hfield] at hset
  · intro y hy hmaps
    exact tendsto_atBot_of_isIntegralCurveOn_mapsTo_closedBall hs hu hN hsmall hN0 hP hAP
      (hfield ▸ hy) hmaps

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (A P : E →L[ℝ] E) {V : E → E} {x : E} {K α : ℝ≥0}
  {ι : Type*} {l : Filter ι} {Vs : ι → E → E} {xs : ι → E} {U : Set E}
  (hs : ∀ t : ℝ, 0 ≤ t → ∀ z : E,
    ‖NormedSpace.exp (t • A) (P z)‖ ≤ K * Real.exp (-α * t) * ‖z‖)
  (hu : ∀ t : ℝ, t ≤ 0 → ∀ z : E,
    ‖NormedSpace.exp (t • A) (z - P z)‖ ≤ K * Real.exp (α * t) * ‖z‖)
  (hα : 0 < α) (hP : IsIdempotentElem P) (hAP : Commute A P)
  (hU : U ∈ 𝓝 x) (hVU : ContDiffOn ℝ 1 V U) (hx : V x = 0) (hA : HasFDerivAt V A x)
  (hVsU : ∀ᶠ i in l, ContDiffOn ℝ 1 (Vs i) U) (hxs : Tendsto xs l (𝓝 x))
  (hVsx : ∀ᶠ i in l, Vs i (xs i) = 0)
  (hVs' : TendstoUniformlyOn (fun i ↦ fderiv ℝ (Vs i)) (fderiv ℝ V) l U)

include hs hu hα hP hAP hU hVU hx hA hVsU hxs hVsx hVs'

/-- **Local stable graphs depend continuously in `C¹` on the vector field.** Let `V` be a `C¹`
vector field near a zero `x` whose derivative `A` has an exponential dichotomy with commuting
stable projection `P`. Let `Vs i` be `C¹` vector fields whose derivatives converge to the derivative
of `V` uniformly on a neighbourhood of `x`, and whose zeros `xs i` converge to `x`; this makes
`Vs i` converge to `V` in `C¹` near `x`. Then for one confinement radius `r` and one
parameter radius `ρ`, the local stable set of `V` at `x` and, eventually, the local stable set of
`Vs i` at `xs i`, both read in displacement coordinates and truncated by `‖P z‖ ≤ ρ`, are the
graphs over `range P ∩ closedBall 0 ρ` of maps `g` and `G i` that are `C¹` on the closed ball of
radius `ρ`. The maps `G i` converge to `g` uniformly, and their derivatives converge uniformly on
the closed ball of radius `ρ`. -/
theorem exists_localStableGraph_tendstoUniformlyOn_fderiv :
    ∃ r > 0, ∃ ρ > 0, ∃ g : E → E, ∃ G : ι → E → E,
      {z : E | (∃ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ V (x + w)) (Ici 0) ∧
        y 0 = z ∧ MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖P z‖ ≤ ρ} =
        (fun z ↦ z + g z) '' (Set.range P ∩ closedBall 0 ρ) ∧
      (∀ z ∈ closedBall (0 : E) ρ, ContDiffAt ℝ 1 g z) ∧
      (∀ᶠ i in l, {z : E | (∃ y : ℝ → E,
          IsIntegralCurveOn y (fun _ w ↦ Vs i (xs i + w)) (Ici 0) ∧
          y 0 = z ∧ MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖P z‖ ≤ ρ} =
          (fun z ↦ z + G i z) '' (Set.range P ∩ closedBall 0 ρ) ∧
        ∀ z ∈ closedBall (0 : E) ρ, ContDiffAt ℝ 1 (G i) z) ∧
      TendstoUniformly G g l ∧
      TendstoUniformlyOn (fun i ↦ fderiv ℝ (G i)) (fderiv ℝ g) l (closedBall 0 ρ) := by
  obtain ⟨ε, r, hr, ρ, hρ, F, F', hsmall, hρr, hball, hN, hNd, hN', hF, hF0, hFd, hF', hFN,
    hFN', hfield⟩ :=
    TauCeti.exists_vectorField_remainder_tendsto_data (K := K) hU hVU hx hA hVsU hxs hVsx hVs' hα
  have hN0 : V (x + 0) - A 0 = 0 := by simp [hx]
  refine ⟨r, hr, ρ, hρ, localStableGraphMap A P _ r hs hu hr.le hN hsmall,
    fun i ↦ localStableGraphMap A P (F i) r hs hu hr.le (hF i) hsmall, ?_,
    fun z hz ↦ contDiffAt_localStableGraphMap hs hu hr.le hN hsmall hN0 hNd hN' (hball z hz),
    hfield.mono fun i hi ↦ ⟨?_, fun z hz ↦ contDiffAt_localStableGraphMap hs hu hr.le (hF i)
      hsmall (hF0 i) (hFd i) (hF' i) (hball z hz)⟩,
    tendstoUniformly_localStableGraphMap hs hu hr.le hN hF hsmall (fun _ ↦ hsmall) hFN,
    tendstoUniformlyOn_fderiv_localStableGraphMap hs hu hr.le hN hF hsmall hF0 hFd hF' hFN hFN'
      (fun _ ↦ mem_closedBall_zero_iff.1) hρr⟩
  · have hset := setOf_exists_isIntegralCurveOn_mapsTo_closedBall_eq_image hs hu hr.le hN
      hsmall hN0 hP hAP hρr.le
    have hfieldV : (fun (_ : ℝ) z ↦ A z + (V (x + z) - A z)) = fun _ w ↦ V (x + w) := by
      funext _ z
      abel
    rwa [hfieldV] at hset
  · have hset := setOf_exists_isIntegralCurveOn_mapsTo_closedBall_eq_image hs hu hr.le (hF i)
      hsmall (hF0 i) hP hAP hρr.le
    have hfieldVs : (fun (_ : ℝ) z ↦ A z + F i z) = fun _ w ↦ Vs i (xs i + w) := by
      funext _ z
      exact hi z
    rwa [hfieldVs] at hset

/-- **Local unstable graphs depend continuously in `C¹` on the vector field.** Under the
hypotheses of `ContinuousLinearMap.exists_localStableGraph_tendstoUniformlyOn_fderiv`, the local
unstable sets of `V` at `x` and, eventually, of `Vs i` at `xs i`, read in displacement coordinates
and truncated by `‖z - P z‖ ≤ ρ`, are the graphs over `range (1 - P) ∩ closedBall 0 ρ` of maps `g`
and `G i` that are `C¹` on the closed ball of radius `ρ`. The maps `G i` converge to `g` uniformly,
and their derivatives converge uniformly on the closed ball of radius `ρ`. -/
theorem exists_localUnstableGraph_tendstoUniformlyOn_fderiv :
    ∃ r > 0, ∃ ρ > 0, ∃ g : E → E, ∃ G : ι → E → E,
      {z : E | (∃ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ V (x + w)) (Iic 0) ∧
        y 0 = z ∧ MapsTo y (Iic 0) (closedBall 0 r)) ∧ ‖z - P z‖ ≤ ρ} =
        (fun z ↦ z + g z) '' (Set.range (ContinuousLinearMap.id ℝ E - P) ∩ closedBall 0 ρ) ∧
      (∀ z ∈ closedBall (0 : E) ρ, ContDiffAt ℝ 1 g z) ∧
      (∀ᶠ i in l, {z : E | (∃ y : ℝ → E,
          IsIntegralCurveOn y (fun _ w ↦ Vs i (xs i + w)) (Iic 0) ∧
          y 0 = z ∧ MapsTo y (Iic 0) (closedBall 0 r)) ∧ ‖z - P z‖ ≤ ρ} =
          (fun z ↦ z + G i z) '' (Set.range (ContinuousLinearMap.id ℝ E - P) ∩ closedBall 0 ρ) ∧
        ∀ z ∈ closedBall (0 : E) ρ, ContDiffAt ℝ 1 (G i) z) ∧
      TendstoUniformly G g l ∧
      TendstoUniformlyOn (fun i ↦ fderiv ℝ (G i)) (fderiv ℝ g) l (closedBall 0 ρ) := by
  obtain ⟨ε, r, hr, ρ, hρ, F, F', hsmall, hρr, hball, hN, hNd, hN', hF, hF0, hFd, hF', hFN,
    hFN', hfield⟩ :=
    TauCeti.exists_vectorField_remainder_tendsto_data (K := K) hU hVU hx hA hVsU hxs hVsx hVs' hα
  have hN0 : V (x + 0) - A 0 = 0 := by simp [hx]
  refine ⟨r, hr, ρ, hρ, localUnstableGraphMap A P _ r hs hu hr.le hN hsmall,
    fun i ↦ localUnstableGraphMap A P (F i) r hs hu hr.le (hF i) hsmall, ?_,
    fun z hz ↦ contDiffAt_localUnstableGraphMap hs hu hr.le hN hsmall hN0 hNd hN' (hball z hz),
    hfield.mono fun i hi ↦ ⟨?_, fun z hz ↦ contDiffAt_localUnstableGraphMap hs hu hr.le (hF i)
      hsmall (hF0 i) (hFd i) (hF' i) (hball z hz)⟩,
    tendstoUniformly_localUnstableGraphMap hs hu hr.le hN hF hsmall (fun _ ↦ hsmall) hFN,
    tendstoUniformlyOn_fderiv_localUnstableGraphMap hs hu hr.le hN hF hsmall hF0 hFd hF' hFN
      hFN' (fun _ ↦ mem_closedBall_zero_iff.1) hρr⟩
  · have hset := setOf_exists_isIntegralCurveOn_Iic_mapsTo_closedBall_eq_image hs hu hr.le hN
      hsmall hN0 hP hAP hρr.le
    simp only [sub_apply, id_apply] at hset
    have hfieldV : (fun (_ : ℝ) z ↦ A z + (V (x + z) - A z)) = fun _ w ↦ V (x + w) := by
      funext _ z
      abel
    rwa [hfieldV] at hset
  · have hset := setOf_exists_isIntegralCurveOn_Iic_mapsTo_closedBall_eq_image hs hu hr.le
      (hF i) hsmall (hF0 i) hP hAP hρr.le
    simp only [sub_apply, id_apply] at hset
    have hfieldVs : (fun (_ : ℝ) z ↦ A z + F i z) = fun _ w ↦ Vs i (xs i + w) := by
      funext _ z
      exact hi z
    rwa [hfieldVs] at hset

end ContinuousLinearMap
