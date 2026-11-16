/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Sequences
import TauCeti.Topology.ContinuousMap.Ascoli

/-!
# Equicontinuity from bounds on derivatives

A family of differentiable maps on an open subset of a proper real normed space is
equicontinuous if its derivatives are uniformly bounded on each compact subset. The
mean-value inequality supplies a common Lipschitz bound on a small ball around each point.
This criterion is useful when applying Arzelà–Ascoli to families controlled by interior
estimates, without requiring a global bound on the derivatives.

Applied to the derivatives themselves, Arzelà–Ascoli gives convergence in `C¹`
(`TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_fderiv`): if `uₙ → v` pointwise on an open
subset of a finite-dimensional space, with values in a finite-dimensional space, and the
derivatives `Duₙ` are equicontinuous and bounded at each point, then along a subsequence
`Duₙ → Dv` locally uniformly, and `v` is `C¹`. Equicontinuity of the derivatives is what interior
estimates for second derivatives provide.
-/

public section

open Filter Metric Set Topology
open scoped NNReal

namespace TauCeti

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Set E} {u : ι → E → F}

/-- Uniform bounds on derivatives on compact subsets of an open set imply equicontinuity
there. No compactness or completeness assumption on the target is needed. -/
theorem equicontinuousOn_of_forall_isCompact_norm_fderiv_le
    (hΩ : IsOpen Ω) (hu : ∀ i, DifferentiableOn ℝ (u i) Ω)
    (hb : ∀ C, IsCompact C → C ⊆ Ω → ∃ M, ∀ i, ∀ x ∈ C, ‖fderiv ℝ (u i) x‖ ≤ M) :
    EquicontinuousOn u Ω := by
  rw [← equicontinuous_restrict_iff]
  intro x
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp hΩ x x.2
  have hball : closedBall (x : E) (r / 2) ⊆ Ω :=
    (closedBall_subset_ball (by linarith : r / 2 < r)).trans hrΩ
  obtain ⟨M, hM⟩ := hb _ (isCompact_closedBall (x : E) (r / 2)) hball
  let L : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  have hLip : ∀ i, LipschitzOnWith L (u i) (closedBall (x : E) (r / 2)) := by
    intro i
    apply (convex_closedBall (x : E) (r / 2)).lipschitzOnWith_of_nnNorm_fderiv_le (𝕜 := ℝ)
    · intro y hy
      exact (hu i y (hball hy)).differentiableAt (hΩ.mem_nhds (hball hy))
    · intro y hy
      exact_mod_cast (hM i y hy).trans (le_max_left M 0)
  have hmod : Continuous (fun y : Ω ↦ (L : ℝ) * dist (x : E) (y : E)) :=
    continuous_const.mul (continuous_const.dist continuous_subtype_val)
  apply Metric.equicontinuousAt_of_continuity_modulus
    (fun y : Ω ↦ (L : ℝ) * dist (x : E) (y : E))
    (by simpa using (hmod.continuousAt (x := x)).tendsto) _
  have hnear : ∀ᶠ y : Ω in 𝓝 x, (y : E) ∈ ball (x : E) (r / 2) :=
    continuous_subtype_val.continuousAt (ball_mem_nhds (x : E) (by positivity))
  filter_upwards [hnear] with y hy i
  exact (hLip i).dist_le_mul _ (mem_closedBall_self (by positivity)) _
    (ball_subset_closedBall hy)

/-- **Arzelà–Ascoli in `C¹`.** Let `uₙ` be differentiable on an open subset `Ω` of a
finite-dimensional space, with values in a finite-dimensional space, and converge pointwise on
`Ω` to `v`. If the derivatives `Duₙ` are equicontinuous on `Ω` and bounded at each point, then
`v` is `C¹` on `Ω` and, along a subsequence, `Duₙ → Dv` locally uniformly on `Ω`. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn_fderiv [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {u : ℕ → E → F} {v : E → F} (hΩ : IsOpen Ω)
    (hu : ∀ n, DifferentiableOn ℝ (u n) Ω) (hequi : EquicontinuousOn (fun n ↦ fderiv ℝ (u n)) Ω)
    (hbd : ∀ x ∈ Ω, ∃ M, ∀ n, ‖fderiv ℝ (u n) x‖ ≤ M)
    (hlim : ∀ x ∈ Ω, Tendsto (fun n ↦ u n x) atTop (𝓝 (v x))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ContDiffOn ℝ 1 v Ω ∧
      TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (u (φ n))) (fderiv ℝ v) atTop Ω := by
  classical
  let : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  let U : ℕ → C(Ω, E →L[ℝ] F) := fun n ↦
    ⟨Ω.domRestrict (fderiv ℝ (u n)), (hequi.continuousOn n).domRestrict⟩
  have hcompact : IsCompact (closure (range U)) :=
    ArzelaAscoli.isCompact_closure_range_of_equicontinuous
      ((equicontinuous_restrict_iff _).mpr hequi) fun x ↦
        ⟨closedBall 0 (hbd x x.2).choose, isCompact_closedBall _ _,
          fun n ↦ mem_closedBall_zero_iff.2 ((hbd x x.2).choose_spec n)⟩
  obtain ⟨a, -, φ, hφ, hlimU⟩ := hcompact.tendsto_subseq (x := U)
    (fun n ↦ subset_closure (mem_range_self n))
  -- Extend the limit of the derivatives by zero off `Ω`.
  let G : E → E →L[ℝ] F := fun z ↦ if hz : z ∈ Ω then a ⟨z, hz⟩ else 0
  have hG : G ∘ (Subtype.val : Ω → E) = fun x : Ω ↦ a x := by
    funext x
    simp [G, x.2]
  have hconv : TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (u (φ n))) G atTop Ω := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe, hG]
    exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlimU
  -- The limit of the derivatives is the derivative of the limit.
  have hderiv : ∀ x ∈ Ω, HasFDerivAt v (G x) x := fun x hx ↦
    hasFDerivAt_of_tendstoLocallyUniformlyOn hΩ hconv
      (fun n y hy ↦ ((hu (φ n)) y hy).differentiableAt (hΩ.mem_nhds hy) |>.hasFDerivAt)
      (fun y hy ↦ (hlim y hy).comp hφ.tendsto_atTop) hx
  have hfd : EqOn (fderiv ℝ v) G Ω := fun x hx ↦ (hderiv x hx).fderiv
  have hGc : ContinuousOn G Ω := hconv.continuousOn (Eventually.of_forall fun n ↦
    (hequi.comp φ).continuousOn n).frequently
  refine ⟨φ, hφ, ?_, hconv.congr_right fun x hx ↦ (hfd hx).symm⟩
  exact (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hΩ).2
    ⟨fun x hx ↦ (hderiv x hx).differentiableAt.differentiableWithinAt, by simp,
      contDiffOn_zero.2 (hGc.congr hfd)⟩

end TauCeti
