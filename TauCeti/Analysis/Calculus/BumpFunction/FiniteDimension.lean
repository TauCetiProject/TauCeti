/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Extending finite-dimensional smooth germs

A function smooth on an open set has a globally smooth, compactly supported representative
which agrees with it near a prescribed compact subset, has topological support in that open set,
and vanishes wherever the original function does. This allows local smooth fields to be used in
global integral identities, and lets cut-off vector fields keep the rest points of the original.

A function which is smooth, of finite or infinite order, on a neighbourhood of a point of a
finite-dimensional real normed space agrees near that point with a globally smooth function of
the same order. A smooth bump function performs the extension while preserving the original
function near the base point. Since the bump is compactly supported, so is the representative,
and a representative of order at least one is moreover globally Lipschitz.

Dually, a function smooth outside a compact set agrees near every point outside a larger compact
set with a globally smooth function, obtained by cutting it off near the origin
(`TauCeti.exists_contDiff_eventually_eventuallyEq`). This lets estimates at infinity be proved for
globally smooth functions only.

A function which is `C^n` at every point of a sphere can be filled in across the open ball it
bounds: it agrees near every point outside the ball with a function which is `C^n` at every point
of the closed ball (`TauCeti.exists_contDiffAt_closedBall_eventuallyEq`).

These general calculus lemmas are used by the parameter-dependent ODE construction for the
Lie-group exponential, and by the construction of a local flow out of the global solution of a
globally Lipschitz field. Filling in a hole reduces Stokes' formula on a disc with
holes to Stokes' formula on a closed disc.
-/

public section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function smooth on an open set has a globally smooth, compactly supported representative
agreeing with it near every point of any prescribed compact subset of that set. The representative
vanishes wherever the function does. -/
theorem ContDiffOn.exists_contDiff_eventuallyEq_on_isCompact [FiniteDimensional ℝ E]
    {n : ℕ∞} {f : E → F} {K U : Set E} (hf : ContDiffOn ℝ n f U)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ g : E → F, ContDiff ℝ n g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      Function.support g ⊆ Function.support f ∧ ∀ x ∈ K, g =ᶠ[nhds x] f := by
  obtain ⟨ψ, hψ, -, hψone, hψcpt, hψsupp⟩ := hK.exists_contDiff_cutoff_eventuallyEq_one hU hKU
  have hg : ContDiff ℝ n (fun x ↦ ψ x • f x) := by
    apply ContMDiff.contDiff
    refine contMDiff_of_tsupport fun x hx ↦ ?_
    have hxU : x ∈ U := hψsupp (tsupport_smul_subset_left ψ f hx)
    exact ((hψ.of_le (by simp)).contDiffAt.smul
      ((hf x hxU).contDiffAt (hU.mem_nhds hxU))).contMDiffAt
  refine ⟨fun x ↦ ψ x • f x, hg, hψcpt.smul_right,
    (tsupport_smul_subset_left ψ f).trans hψsupp, Function.support_smul_subset_right ψ f, ?_⟩
  intro x hx
  filter_upwards [hψone x hx] with y hy
  simp only [hy, one_smul]

/-- A function which is smooth on a neighbourhood of a point of a finite-dimensional real normed
space agrees near that point with a compactly supported globally smooth function of the same
order. -/
theorem ContDiffOn.exists_contDiff_eventuallyEq_of_finiteDimensional
    [FiniteDimensional ℝ E] {n : ℕ∞} {f : E → F} {x : E} {s : Set E}
    (hfs : ContDiffOn ℝ n f s) (hs : s ∈ nhds x) :
    ∃ g : E → F, ContDiff ℝ n g ∧ HasCompactSupport g ∧ g =ᶠ[nhds x] f := by
  obtain ⟨U, hUs, hU, hxU⟩ := mem_nhds_iff.mp hs
  obtain ⟨g, hg, hgc, -, -, hgf⟩ :=
    (hfs.mono hUs).exists_contDiff_eventuallyEq_on_isCompact isCompact_singleton hU
      (Set.singleton_subset_iff.mpr hxU)
  exact ⟨g, hg, hgc, hgf x (Set.mem_singleton x)⟩

/-- A finite-order smooth germ on a finite-dimensional real normed space has a compactly supported
globally smooth representative of the same order. -/
theorem ContDiffAt.exists_contDiff_eventuallyEq_of_finiteDimensional
    [FiniteDimensional ℝ E] (n : ℕ) {f : E → F} {x : E}
    (hf : ContDiffAt ℝ n f x) :
    ∃ g : E → F, ContDiff ℝ n g ∧ HasCompactSupport g ∧ g =ᶠ[nhds x] f :=
  let ⟨s, hs, hfs⟩ := hf.contDiffOn le_rfl (by simp)
  hfs.exists_contDiff_eventuallyEq_of_finiteDimensional hs

/-- A function which is smooth of order at least one on a neighbourhood of a point of a
finite-dimensional real normed space agrees near that point with a globally smooth **and globally
Lipschitz** function of the same order: the compactly supported representative above has a bounded
derivative. -/
theorem ContDiffOn.exists_lipschitzWith_contDiff_eventuallyEq_of_finiteDimensional
    [FiniteDimensional ℝ E] {n : ℕ∞} {f : E → F} {x : E} {s : Set E}
    (hf : ContDiffOn ℝ (n + 1) f s) (hs : s ∈ nhds x) :
    ∃ (g : E → F) (K : NNReal), ContDiff ℝ (n + 1) g ∧ LipschitzWith K g ∧ g =ᶠ[nhds x] f := by
  obtain ⟨g, hg, hgsupp, hgf⟩ := hf.exists_contDiff_eventuallyEq_of_finiteDimensional hs
  obtain ⟨C, hC⟩ := hg.lipschitzWith_of_hasCompactSupport hgsupp (by simp)
  exact ⟨g, C, hg, hC, hgf⟩

namespace TauCeti

open Filter Topology

/-- A function smooth outside a compact set agrees, near every point outside a larger compact set,
with a globally smooth function. -/
theorem exists_contDiff_eventually_eventuallyEq [FiniteDimensional ℝ E] {n : ℕ∞} {f : E → F}
    (hf : ∀ᶠ x in cocompact E, ContDiffAt ℝ n f x) :
    ∃ g : E → F, ContDiff ℝ n g ∧ ∀ᶠ x in cocompact E, g =ᶠ[𝓝 x] f := by
  obtain ⟨R, -, hR⟩ :=
    hasBasis_cobounded_norm.eventually_iff.mp (Metric.cobounded_eq_cocompact (α := E) ▸ hf)
  set r := max R 0 + 1
  let b : ContDiffBump (0 : E) := ⟨r, r + 1, by positivity, by linarith⟩
  refine ⟨fun x ↦ (1 - b x) • f x, contDiff_iff_contDiffAt.2 fun x ↦ ?_, ?_⟩
  · by_cases hx : ‖x‖ < r
    · -- Near the ball of radius `r` the cutoff vanishes.
      refine contDiffAt_const (c := (0 : F)).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
      rw [b.one_of_mem_closedBall (by simpa using hy.le), sub_self, zero_smul]
    · exact (contDiffAt_const.sub b.contDiff.contDiffAt).smul
        (hR (Set.mem_ofPred.mpr (by linarith [le_max_left R 0, not_lt.mp hx])))
  · filter_upwards [(tendsto_norm_cocompact_atTop (E := E)).eventually_gt_atTop (r + 1)] with x hx
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    rw [b.zero_of_le_dist (by simpa using hy.le), sub_zero, one_smul]

open Metric

/-- **Filling a hole.** A function which is `C^n` at every point of the sphere `dist x c = r` of a
finite-dimensional real normed space agrees, near every point outside the open ball
`dist x c < r`, with a function which is `C^n` at every point of the closed ball. Nothing is
assumed about the function inside the ball: a bump function cuts it off there, away from the
sphere. -/
theorem exists_contDiffAt_closedBall_eventuallyEq [FiniteDimensional ℝ E] {n : ℕ} {f : E → F}
    {c : E} {r : ℝ} (hf : ∀ x ∈ sphere c r, ContDiffAt ℝ n f x) :
    ∃ g : E → F, (∀ x ∈ closedBall c r, ContDiffAt ℝ n g x) ∧
      ∀ x ∉ ball c r, g =ᶠ[nhds x] f := by
  rcases le_or_gt r 0 with hr | hr
  · -- A closed ball of nonpositive radius lies in its sphere.
    refine ⟨f, fun x hx ↦ hf x (mem_sphere.2 ?_), fun x _ ↦ .rfl⟩
    exact le_antisymm (mem_closedBall.1 hx) (hr.trans dist_nonneg)
  -- The points of the closed ball at which `f` is not `C^n` lie in a smaller concentric ball.
  have hU : IsOpen {x | ContDiffAt ℝ n f x} :=
    isOpen_iff_mem_nhds.2 fun x hx ↦ hx.eventually (by simp)
  obtain ⟨r', hr'r, hK⟩ := exists_lt_subset_ball (isClosed_closedBall.sdiff hU) fun x hx ↦
    mem_ball.2 <| (mem_closedBall.1 hx.1).lt_of_ne fun h ↦ hx.2 (hf x (mem_sphere.2 h))
  set a := max r' (r / 2)
  have ha : 0 < a := lt_max_of_lt_right (half_pos hr)
  have har : a < r := max_lt hr'r (half_lt_self hr)
  let χ : ContDiffBump c := ⟨a, (a + r) / 2, ha, by linarith⟩
  refine ⟨fun x ↦ (1 - χ x) • f x, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rcases lt_or_ge (dist x c) a with h | h
    · -- Deep inside the ball the cut-off function vanishes.
      refine contDiffAt_const (c := (0 : F)).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ball.mem_nhds (mem_ball.2 h)] with y hy
      rw [χ.one_of_mem_closedBall (ball_subset_closedBall hy), sub_self, zero_smul]
    · -- Elsewhere in the closed ball `f` is `C^n`.
      have hfx : ContDiffAt ℝ n f x := by
        by_contra hfx
        exact (mem_ball.1 (ball_subset_ball (le_max_left r' (r / 2)) (hK ⟨hx, hfx⟩))).not_ge h
      exact (contDiffAt_const.sub χ.contDiffAt).smul hfx
  · -- Outside the ball the bump vanishes.
    have hx' : (a + r) / 2 < dist x c := by
      rw [mem_ball, not_lt] at hx
      linarith
    filter_upwards [(isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds
      hx'] with y hy
    rw [χ.zero_of_le_dist (x := y) hy.le, sub_zero, one_smul]

end TauCeti
