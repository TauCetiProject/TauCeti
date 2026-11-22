/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Chart
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Uniform tameness on compact windows of a manifold

Let `ω` be a nondegenerate two-form on a manifold `M` with finite-dimensional model space, such as
a closed symplectic manifold, and let `J(z, x)` be almost complex structures on the tangent spaces
of `M` depending on a domain point `z ∈ ℝ × ℝ`, as in the Floer equation
`(du - X_K)^{0,1} = 0`. The convergence and energy estimates for Floer solutions in a manifold
measure tangent vectors through a `C¹` map `e : M → F` into a normed space, such as the Whitney
embedding of a closed manifold, and assume that the structures are *uniformly tame* through `e`:
there is one constant `c > 0` with

`c ‖d e v‖² ≤ ω(v, J(z, x) v)`

for every tangent vector `v` at `x`. This is the form of tameness taken by the manifold-target
theorems on the ends of Floer cylinders and pairs of pants
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer`)
and on convergence of solutions and of rescaled bubbles.

This file derives it from pointwise tameness: if the structures `J(z, x)`, read in the charts of
`M`, are continuous, and `J(z, x)` is tamed by `ω_x` for `z` in a compact set `D` and `x` in a
compact set `K`, then a single constant `c > 0` works on `D × K`
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_forall_mul_norm_mvfderiv_sq_le`). No
injectivity of `d e` is needed, and tameness is only assumed on `D × K`, not on a neighbourhood:
it is an open condition. The constant is found chart by chart. In the chart at a point `α` of `K`
the form `ω(·, J ·)` is a continuous family of bilinear forms on the model space
(`TauCeti.SmoothTwoForm.associatedBilinFormInChartAt`), positive at `α` and so, by continuity
and compactness of `D`, at least half its minimum at `α` on a neighbourhood of `α`
(`IsCompact.eventually_forall_mul_norm_sq_le`), where `d e` is bounded in the chart coordinates.
Compactness of `K` then needs finitely many charts (`IsCompact.induction_on`).

For a jointly continuous family of structures
(`TauCeti.ContMDiffAlmostComplexStructureFamily`), continuity in the charts is automatic
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_forall_mul_norm_mvfderiv_sq_le_of_family`).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 4.1,
  on the energy of curves for tame almost complex structures and its comparison with the norm of
  the derivative.
-/

public section

noncomputable section

open Bundle ContinuousLinearMap Filter Metric Set Topology
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {e : M → F}

namespace SmoothTwoForm

variable {ω : SmoothTwoForm I M} {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}

/-- **Uniform tameness near a point.** If the structures are continuous in the chart at a point
`α` and tamed by `ω_α` at every domain point of a compact set `D`, then they are uniformly tame
through a `C¹` map `e` on a neighbourhood of `α`. -/
theorem IsNondegenerate.exists_mem_nhds_forall_mul_norm_mvfderiv_sq_le (hω : ω.IsNondegenerate)
    {α : M} {D : Set (ℝ × ℝ)} (hD : IsCompact D)
    (hJ : ContinuousOn (Floer.almostComplexInChartAt I α J) (D ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ D, (hω.symplecticFormAt α).Tames (J z α)) (he : ContMDiff I 𝓘(ℝ, F) 1 e) :
    ∃ V ∈ 𝓝 α, ∃ c > 0, ∀ z ∈ D, ∀ x ∈ V, ∀ v : TangentSpace I x,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v) := by
  set φ := extChartAt I α
  set T := trivializationAt E (TangentSpace I) α
  set y₀ := φ α
  set b := ω.associatedBilinFormInChartAt α J
  -- A compact neighbourhood `L = closedBall y₀ r ∩ range I` of `y₀` inside the chart target.
  obtain ⟨r₀, hr₀, hr₀t⟩ :=
    Metric.mem_nhdsWithin_iff.1 (extChartAt_target_mem_nhdsWithin (I := I) α)
  set L := closedBall y₀ (r₀ / 2) ∩ range I
  have hL : IsCompact L := (isCompact_closedBall y₀ _).inter_right I.isClosed_range
  have hLt : L ⊆ φ.target := fun y hy ↦
    hr₀t ⟨mem_ball.2 ((mem_closedBall.1 hy.1).trans_lt (half_lt_self hr₀)), hy.2⟩
  have hbc : ContinuousOn b (D ×ˢ φ.target) :=
    continuousOn_associatedBilinFormInChartAt (fun _ hp ↦ hp.2) hJ
  -- By tameness at `α` the form is coercive at `y₀`, with a constant `c₀`, and stays coercive with
  -- the constant `c₀ / 2` near `y₀`.
  obtain ⟨c₀, hc₀, hc₀b⟩ := hD.exists_pos_forall_mul_norm_sq_le (b := fun z ↦ b (z, y₀))
    (hbc.comp (continuousOn_id.prodMk continuousOn_const) fun z hz ↦
      ⟨hz, mem_extChartAt_target α⟩)
    fun z hz a ha ↦ by
      obtain ⟨v, rfl⟩ : ∃ v : TangentSpace I α, T.continuousLinearMapAt ℝ α v = a :=
        ⟨T.symmL ℝ α a, Trivialization.continuousLinearMapAt_symmL _
          (FiberBundle.mem_baseSet_trivializationAt' α) a⟩
      rw [ω.associatedBilinFormInChartAt_extChartAt J z (mem_extChartAt_source α), ←
        IsNondegenerate.symplecticFormAt_apply hω]
      exact hJt z hz v fun hv ↦ ha (by rw [hv, map_zero])
  have hφ : Tendsto φ (𝓝 α) (𝓝[φ.target] y₀) :=
    tendsto_nhdsWithin_iff.2 ⟨continuousAt_extChartAt α,
      eventually_of_mem (extChartAt_source_mem_nhds α) fun _ hx ↦ φ.map_source hx⟩
  have hcoer := hφ.eventually (hD.eventually_forall_mul_norm_sq_le hbc
    (mem_extChartAt_target α) (half_lt_self hc₀) hc₀b)
  -- The differential of `e` is bounded by `B` times the chart coordinates over `L`.
  obtain ⟨B, hB⟩ := he.contMDiffOn.exists_forall_norm_mvfderiv_le_mul_norm hL hLt
  refine ⟨φ.source ∩ φ ⁻¹' ball y₀ (r₀ / 2) ∩ {x | ∀ z ∈ D, ∀ a,
      c₀ / 2 * ‖a‖ ^ 2 ≤ b (z, φ x) a a},
    inter_mem (inter_mem (extChartAt_source_mem_nhds α)
      ((continuousAt_extChartAt α).preimage_mem_nhds (ball_mem_nhds _ (half_pos hr₀)))) hcoer,
    c₀ / (2 * (B ^ 2 + 1)), by positivity, fun z hz x hx v ↦ ?_⟩
  have hyL : φ x ∈ L := ⟨mem_closedBall.2 (mem_ball.1 hx.1.2).le,
    extChartAt_target_subset_range α (φ.map_source hx.1.1)⟩
  set a := T.continuousLinearMapAt ℝ x v
  have hlow := hx.2 z hz a
  rw [ω.associatedBilinFormInChartAt_extChartAt J z hx.1.1,
    ← IsNondegenerate.symplecticFormAt_apply hω] at hlow
  -- Since `‖d e v‖ ≤ B ‖a‖`, the constant `c₀ / (2 (B² + 1))` works.
  have hq : c₀ / (2 * (B ^ 2 + 1)) * B ^ 2 ≤ c₀ / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
    nlinarith [sq_nonneg B]
  calc c₀ / (2 * (B ^ 2 + 1)) * ‖mvfderiv I e x v‖ ^ 2
      ≤ c₀ / (2 * (B ^ 2 + 1)) * B ^ 2 * ‖a‖ ^ 2 := by
        rw [mul_assoc, ← mul_pow]; gcongr; exact hB x hx.1.1 hyL v
    _ ≤ _ := by gcongr
    _ ≤ _ := hlow

/-- **Uniform tameness on compact windows of a manifold.** Let `ω` be a nondegenerate two-form on
`M`, let `D ⊆ ℝ × ℝ` and `K ⊆ M` be compact, and let the structures `J(z, x)` be continuous in the
chart at every point of `K` and tamed by `ω_x` for `z ∈ D` and `x ∈ K`. For every `C¹` map
`e : M → F` into a normed space there is a constant `c > 0` with
`c ‖d e v‖² ≤ ω(v, J(z, x) v)` for every `z ∈ D`, `x ∈ K` and tangent vector `v` at `x`. -/
theorem IsNondegenerate.exists_pos_forall_mul_norm_mvfderiv_sq_le (hω : ω.IsNondegenerate)
    {D : Set (ℝ × ℝ)} {K : Set M} (hD : IsCompact D) (hK : IsCompact K)
    (hJ : ∀ α ∈ K, ContinuousOn (Floer.almostComplexInChartAt I α J)
      (D ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ D, ∀ x ∈ K, (hω.symplecticFormAt x).Tames (J z x))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) :
    ∃ c > 0, ∀ z ∈ D, ∀ x ∈ K, ∀ v : TangentSpace I x,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v) := by
  -- The local constants near the points of `K` combine, through finitely many of them, into one.
  refine hK.induction_on (p := fun S ↦ ∃ c > 0, ∀ z ∈ D, ∀ x ∈ S, ∀ v : TangentSpace I x,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    ⟨1, one_pos, fun _ _ _ hx ↦ absurd hx (notMem_empty _)⟩
    (fun _ _ hst ⟨c, hc, h⟩ ↦ ⟨c, hc, fun z hz x hx ↦ h z hz x (hst hx)⟩)
    (fun _ _ ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩ ↦ ⟨min c₁ c₂, lt_min hc₁ hc₂, fun z hz x hx v ↦ ?_⟩)
    fun α hα ↦ ?_
  · rcases hx with hx | hx
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans (h₁ z hz x hx v)
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans (h₂ z hz x hx v)
  · obtain ⟨V, hV, hVt⟩ := hω.exists_mem_nhds_forall_mul_norm_mvfderiv_sq_le hD (hJ α hα)
      (fun z hz ↦ hJt z hz α hα) he
    exact ⟨V, mem_nhdsWithin_of_mem_nhds hV, hVt⟩

/-- **Uniform tameness of a continuous family on compact windows.** For a jointly continuous family
`J(z, x)` of almost complex structures over the domain `ℝ × ℝ`, tamed by the nondegenerate form
`ω` at the points of compact sets `D ⊆ ℝ × ℝ` and `K ⊆ M`, and a `C¹` map `e : M → F`, there is a
constant `c > 0` with `c ‖d e v‖² ≤ ω(v, J(z, x) v)` for `z ∈ D`, `x ∈ K`. -/
theorem IsNondegenerate.exists_pos_forall_mul_norm_mvfderiv_sq_le_of_family {n : ℕ∞}
    (hω : ω.IsNondegenerate) (J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) n)
    {D : Set (ℝ × ℝ)} {K : Set M} (hD : IsCompact D) (hK : IsCompact K)
    (hJt : ∀ z ∈ D, ∀ x ∈ K, (hω.symplecticFormAt x).Tames (J.almostComplexStructureAt (z, x)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) :
    ∃ c > 0, ∀ z ∈ D, ∀ x ∈ K, ∀ v : TangentSpace I x,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J.almostComplexStructureAt (z, x) v) :=
  hω.exists_pos_forall_mul_norm_mvfderiv_sq_le (J := fun z x ↦ J.almostComplexStructureAt (z, x))
    hD hK (fun α _ ↦ by
      rw [Floer.almostComplexInChartAt_eq_inChart J 0 α]
      refine (J.contDiffOn_inChart (0, α)).continuousOn.mono fun p hp ↦ ?_
      simpa only [extChartAt_prod, PartialEquiv.prod_target, extChartAt_model_space_eq_id,
        PartialEquiv.refl_target, mem_prod, mem_univ, true_and] using hp.2) hJt he

end SmoothTwoForm

end TauCeti
