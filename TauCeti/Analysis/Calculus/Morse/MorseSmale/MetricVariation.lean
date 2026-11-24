/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Fredholm
import TauCeti.Analysis.Calculus.BumpFunction.Path
import TauCeti.Analysis.InnerProductSpace.RankOne
import TauCeti.Analysis.ODE.Caratheodory
import TauCeti.LinearAlgebra.Submodule.Quotient
import TauCeti.MeasureTheory.Function.L2Space

/-!
# Localized metric variations make the linearized gradient trajectory equation onto

Let `f` be a `C²` function on a finite-dimensional real inner product space `E`, and `γ` a
negative gradient trajectory, `γ' = -∇f(γ)`. Linearizing the trajectory equation at `γ` gives the
trajectory operator `D_γ ξ = ξ' + Hess f(γ) ξ` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)`
(`TauCeti.WeakDerivStep.trajectoryOperator`). Changing the metric changes the equation as well.
For a field `H` of symmetric operators, the metric `⟪(1 + ε H x) u, v⟫` has gradient
`(1 + ε H)⁻¹ ∇f`, whose derivative at `ε = 0` is `-H ∇f`. So the derivative of the trajectory
equation `(γ + ξ)' + (1 + ε H)⁻¹ ∇f(γ + ξ) = 0` in the direction of the metric variation `H` is
minus the path

`s ↦ H (γ s) (∇f (γ s))`,

and the universal linearization, in the trajectory and the metric together, is
`(ξ, H) ↦ D_γ ξ - H(γ) ∇f(γ)`. The **metric variations** along `γ` localized in a set `U`
(`TauCeti.metricVariations f γ U`) are the classes in `L²(ℝ, E)` of these paths, for smooth
compactly supported symmetric fields `H` supported in `U`.

This file proves that these variations make the universal linearization onto as soon as `U` is a
neighbourhood of one point `γ s₀` of the trajectory that is not a critical point of `f`
(`TauCeti.range_trajectoryOperator_sup_span_metricVariations_eq_top`): the range of `D_γ` and the
metric variations together span `L²(ℝ, E)`, for a trajectory between nondegenerate critical
points. Finitely many variations already suffice
(`TauCeti.exists_finset_subset_metricVariations_range_trajectoryOperator_sup_span_eq_top`), since
the cokernel of `D_γ` is finite-dimensional. These statements hold at the given inner product of
`E`, and are the surjectivity input for the universal linearization in the Fredholm-theoretic
proof that Morse–Smale metrics are generic: the variations need only be localized near one
regular point of the trajectory.

The proof goes through the cokernel. A path `v` orthogonal to the range of `D_γ` agrees almost
everywhere with a solution `w` of the formal adjoint equation `w' = Hess f(γ) w`
(`WeakDerivStep.exists_hasDerivAt_adjoint_of_mem_orthogonal_range_trajectoryOperator`), and if
`w` vanishes at one time it vanishes identically, by uniqueness for linear equations. If
`w (s₀) ≠ 0`, take the symmetric operator
`B u = ⟪∇f(γ s₀), u⟫ w(s₀) + ⟪w(s₀), u⟫ ∇f(γ s₀)`, for which `⟪B ∇f(γ s₀), w(s₀)⟫ > 0`, and a
bump function `ψ` at `γ s₀`. Since `f` strictly decreases along `γ` near the regular point
`γ s₀`, and decreases along all of `γ`, a small enough bump meets the trajectory only at times
close to `s₀`, where `⟪B ∇f(γ s), w(s)⟫ > 0`. So the variation `H = ψ B` pairs positively with
`v` (`TauCeti.eq_zero_of_mem_orthogonal_range_trajectoryOperator_of_forall_inner_eq_zero`). The
range of `D_γ` is closed with finite codimension, so the sum of the range and the span of the
variations is closed, and its orthogonal complement is zero.

## Main definitions

* `TauCeti.metricVariations f γ U`: the metric variations along `γ` localized in `U`.

## Main results

* `TauCeti.eq_zero_of_mem_orthogonal_range_trajectoryOperator_of_forall_inner_eq_zero`: a path
  orthogonal to the range of `D_γ` and to the metric variations localized near a regular point of
  `γ` vanishes.
* `TauCeti.range_trajectoryOperator_sup_span_metricVariations_eq_top`: the range of `D_γ` and the
  metric variations span `L²(ℝ, E)`.
* `TauCeti.exists_finset_subset_metricVariations_range_trajectoryOperator_sup_span_eq_top`:
  finitely many metric variations suffice.

## References

* M. Schwarz, *Morse Homology*, Progress in Mathematics **111**, Birkhäuser, 1993, Chapter 2
  (transversality of the universal section by variations of the metric, through the cokernel of
  the linearized operator).
* D. Salamon, *Morse theory, the Conley index and Floer homology*, Bull. London Math. Soc. **22**
  (1990), 113--140 (genericity of Morse–Smale metrics by the Sard–Smale theorem, with the
  cokernel killed by metric variations and unique continuation for the adjoint equation).
-/

public section

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal Gradient RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {γ : ℝ → E}

variable (f γ) in
/-- The **metric variations** along `γ` localized in `U`: the classes in `L²(ℝ, E)` of the paths
`s ↦ H (γ s) (∇f (γ s))`, for smooth compactly supported fields `H` of symmetric operators with
support in `U`. For the metric `⟪(1 + ε H x) u, v⟫`, this path is minus the derivative at `ε = 0`
of the gradient `(1 + ε H)⁻¹ ∇f` along `γ`, the direction in which varying the metric moves the
gradient trajectory equation at `γ`. -/
def metricVariations (U : Set E) :
    Set (Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))) :=
  {g | ∃ H : E → E →L[ℝ] E, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ U ∧
    (∀ x, IsSelfAdjoint (H x)) ∧
    g =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ H (γ s) (∇ f (γ s))}

/-- Membership in the metric variations. -/
theorem mem_metricVariations {U : Set E}
    {g : Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))} :
    g ∈ metricVariations f γ U ↔ ∃ H : E → E →L[ℝ] E, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      tsupport H ⊆ U ∧ (∀ x, IsSelfAdjoint (H x)) ∧
      g =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
        fun s ↦ H (γ s) (∇ f (γ s)) :=
  Iff.rfl

/-- Metric variations localized in a smaller set are metric variations localized in a larger
one. -/
theorem metricVariations_mono {U V : Set E} (h : U ⊆ V) :
    metricVariations f γ U ⊆ metricVariations f γ V :=
  fun _ ⟨H, hH, hc, hU, hsa, hg⟩ ↦ ⟨H, hH, hc, hU.trans h, hsa, hg⟩

/-! ### A metric variation pairing positively with a given path -/

open InnerProductSpace in
/-- Near a point `γ s₀` of a negative gradient trajectory which is not a critical point of `f`, a
continuous path `w` with `w s₀ ≠ 0` pairs positively with the path of some metric variation
localized in a given neighbourhood of `γ s₀`. The variation is `H = ψ B` for a bump function `ψ`
at `γ s₀` and the symmetric operator `B u = ⟪∇f(γ s₀), u⟫ w(s₀) + ⟪w(s₀), u⟫ ∇f(γ s₀)`, which
pairs `∇f(γ s)` positively with `w s` for `s` near `s₀`; the bump is so small that the trajectory
only meets it at such times (`TauCeti.exists_contDiff_tsupport_subset_integral_comp_mul_pos`). -/
private theorem exists_integral_inner_metricVariation_pos (hf : ContDiff ℝ 2 f)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) {U : Set E} {s₀ : ℝ} (hU : U ∈ 𝓝 (γ s₀))
    (hcrit : ∇ f (γ s₀) ≠ 0) {w : ℝ → E} (hwc : Continuous w) (hw0 : w s₀ ≠ 0) :
    ∃ H : E → E →L[ℝ] E, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ U ∧
      (∀ x, IsSelfAdjoint (H x)) ∧ HasCompactSupport (fun s ↦ H (γ s) (∇ f (γ s))) ∧
      0 < ∫ s, ⟪H (γ s) (∇ f (γ s)), w s⟫ := by
  set B := rankOne ℝ (w s₀) (∇ f (γ s₀)) + rankOne ℝ (∇ f (γ s₀)) (w s₀) with hB
  have hBsa : IsSelfAdjoint B := by
    rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint, hB, map_add, adjoint_rankOne,
      adjoint_rankOne, add_comm]
  have hg : Continuous fun t ↦ ∇ f (γ t) :=
    (hf.continuous_gradient (by norm_num)).comp hγ.continuous
  have hq : Continuous fun s ↦ ⟪B (∇ f (γ s)), w s⟫ := (B.continuous.comp hg).inner hwc
  -- A small ball around `γ s₀` meets the trajectory only at times close to `s₀`.
  have hvisit : comap γ (𝓝 (γ s₀)) ≤ 𝓝 s₀ := by
    intro S hS
    obtain ⟨δ, hδ, hδS⟩ := Metric.mem_nhds_iff.1 hS
    obtain ⟨r, hr, hrs⟩ := hγ.exists_pos_forall_dist_lt_mem_Ioo
      (fun t ↦ hf.differentiable (by norm_num) _) hcrit hδ
    exact mem_comap.2 ⟨Metric.ball (γ s₀) r, Metric.ball_mem_nhds _ hr,
      fun s hs ↦ hδS (by rw [Real.ball_eq_Ioo]; exact hrs s hs)⟩
  obtain ⟨ψ, hψ, hψc, hψU, hψγ, hpos⟩ := exists_contDiff_tsupport_subset_integral_comp_mul_pos
    hγ.continuous hvisit hU hq (inner_rankOne_add_rankOne_apply_pos hcrit hw0)
  refine ⟨fun x ↦ ψ x • B, hψ.smul contDiff_const, hψc.smul_right,
    (tsupport_smul_subset_left _ _).trans hψU, fun x ↦ (IsSelfAdjoint.all (ψ x)).smul hBsa,
    hψγ.mono fun s hs h ↦ hs (by simp [h]), ?_⟩
  simpa only [smul_apply, real_inner_smul_left] using hpos

/-! ### The cokernel is detected by metric variations -/

/-- **Paths orthogonal to the range and to the metric variations vanish.** Let `f` be `C²` and `γ`
a negative gradient trajectory, and let `U` be a neighbourhood of a point `γ s₀` of the trajectory
which is not a critical point of `f`. A path `v ∈ L²(ℝ, E)` orthogonal to the range of the
linearized operator `D_γ ξ = ξ' + Hess f(γ) ξ` and to every metric variation localized in `U`
vanishes. -/
theorem eq_zero_of_mem_orthogonal_range_trajectoryOperator_of_forall_inner_eq_zero
    (hf : ContDiff ℝ 2 f) (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x))
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator f (γ s))
    {U : Set E} {s₀ : ℝ} (hU : U ∈ 𝓝 (γ s₀)) (hcrit : ∇ f (γ s₀) ≠ 0)
    {v : Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}
    (hv : v ∈ (WeakDerivStep.trajectoryOperator (p := 2) AL).rangeᗮ)
    (hvar : ∀ g ∈ metricVariations f γ U, ⟪g, v⟫ = 0) : v = 0 := by
  have hvol : volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ) = volume := by simp
  have hH : Continuous fun s ↦ hessianOperator f (γ s) :=
    (hf.contDiff_hessianOperator (m := 0) (by norm_num)).continuous.comp hγ.continuous
  -- `v` is a solution of the adjoint equation `w' = Hess f(γ) w`, the Hessian being symmetric.
  obtain ⟨w, hw, hvw⟩ :=
    WeakDerivStep.exists_hasDerivAt_adjoint_of_mem_orthogonal_range_trajectoryOperator hH hAL hv
  have hw' (s : ℝ) : HasDerivAt w (hessianOperator f (γ s) (w s)) s := by
    simpa only [(hf.contDiffAt.isSelfAdjoint_hessianOperator).adjoint_eq] using hw s
  by_contra hv0
  -- A solution vanishing at one time vanishes identically.
  have hw0 : w s₀ ≠ 0 := by
    intro h
    have hw00 : w = fun _ ↦ 0 := hH.eq_of_hasDerivAt_clm_apply hw' (fun s ↦ by
      simpa using hasDerivAt_const s (0 : E)) h
    exact hv0 (Lp.eq_zero_iff_ae_eq_zero.2 (hvw.trans (.of_forall fun s ↦ by simp [hw00])))
  obtain ⟨H, hHs, hHc, hHU, hHsa, hpath_supp, hpos⟩ := exists_integral_inner_metricVariation_pos
    hf hγ hU hcrit (continuous_iff_continuousAt.2 fun s ↦ (hw' s).continuousAt) hw0
  -- The path of `H` lies in `L²(ℝ, E)`, as a metric variation localized in `U`.
  have hmem : MemLp (fun s ↦ H (γ s) (∇ f (γ s))) 2
      (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)) := by
    rw [hvol]
    exact ((hHs.continuous.comp hγ.continuous).clm_apply
      ((hf.continuous_gradient (by norm_num)).comp hγ.continuous)).memLp_of_hasCompactSupport
        hpath_supp
  have hint : ∫ s, ⟪H (γ s) (∇ f (γ s)), w s⟫ = ⟪hmem.toLp _, v⟫ := by
    rw [L2.toLp_inner_of_ae_eq hmem hvw, hvol]
  exact hpos.ne' (hint.trans (hvar _ ⟨H, hHs, hHc, hHU, hHsa, hmem.coeFn_toLp⟩))

/-! ### Surjectivity of the universal linearization -/

/-- **Localized metric variations make the linearized operator onto.** Let `f` be a `C²` function
on a finite-dimensional real inner product space and `γ` a negative gradient trajectory from a
nondegenerate critical point `p` at `-∞` to a nondegenerate critical point `q` at `+∞`. If `U` is
a neighbourhood of a point `γ s₀` of the trajectory which is not a critical point of `f`, the range
of the linearized operator `ξ ↦ ξ' + Hess f(γ) ξ` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` and the metric
variations localized in `U` together span `L²(ℝ, E)`. In other words, the universal linearization
`(ξ, H) ↦ D_γ ξ - H(γ) ∇f(γ)` of the trajectory equation, in the trajectory and the metric, is
onto. -/
theorem range_trajectoryOperator_sup_span_metricVariations_eq_top
    (hf : ContDiff ℝ 2 f) (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) {p q : E}
    (hp : IsNondegenerateCriticalPoint f p) (hq : IsNondegenerateCriticalPoint f q)
    (hbot : Tendsto γ atBot (𝓝 p)) (htop : Tendsto γ atTop (𝓝 q))
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator f (γ s))
    {U : Set E} {s₀ : ℝ} (hU : U ∈ 𝓝 (γ s₀)) (hcrit : ∇ f (γ s₀) ≠ 0) :
    (WeakDerivStep.trajectoryOperator (p := 2) AL).range ⊔
      Submodule.span ℝ (metricVariations f γ U) = ⊤ := by
  have hD := hγ.isFredholm_trajectoryOperator_hessianOperator hf hp hq hbot htop hAL
  have := hD.finite_coker
  -- The sum contains the closed range, of finite codimension, so it is closed.
  have hK : IsClosed (((WeakDerivStep.trajectoryOperator (p := 2) AL).range ⊔
      Submodule.span ℝ (metricVariations f γ U) : Submodule ℝ _) : Set
        (Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)))) :=
    Submodule.isClosed_mono_of_finiteDimensional_quotient hD.isClosed_range le_sup_left
  have := hK.completeSpace_coe
  rw [← Submodule.orthogonal_eq_bot_iff, eq_bot_iff]
  intro v hv
  rw [← Submodule.inf_orthogonal] at hv
  exact eq_zero_of_mem_orthogonal_range_trajectoryOperator_of_forall_inner_eq_zero hf hγ hAL hU
    hcrit hv.1 fun g hg ↦ (Submodule.mem_orthogonal _ _).1 hv.2 g (Submodule.subset_span hg)

/-- **Finitely many localized metric variations make the linearized operator onto.** Under the
hypotheses of `TauCeti.range_trajectoryOperator_sup_span_metricVariations_eq_top`, finitely many
metric variations localized in `U` already span `L²(ℝ, E)` together with the range of the
linearized operator `ξ ↦ ξ' + Hess f(γ) ξ`: its cokernel is finite-dimensional. -/
theorem exists_finset_subset_metricVariations_range_trajectoryOperator_sup_span_eq_top
    (hf : ContDiff ℝ 2 f) (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) {p q : E}
    (hp : IsNondegenerateCriticalPoint f p) (hq : IsNondegenerateCriticalPoint f q)
    (hbot : Tendsto γ atBot (𝓝 p)) (htop : Tendsto γ atTop (𝓝 q))
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator f (γ s))
    {U : Set E} {s₀ : ℝ} (hU : U ∈ 𝓝 (γ s₀)) (hcrit : ∇ f (γ s₀) ≠ 0) :
    ∃ t : Finset (Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))),
      (t : Set _) ⊆ metricVariations f γ U ∧
        (WeakDerivStep.trajectoryOperator (p := 2) AL).range ⊔ Submodule.span ℝ t = ⊤ := by
  have := (hγ.isFredholm_trajectoryOperator_hessianOperator hf hp hq hbot htop hAL).finite_coker
  exact Submodule.exists_finset_subset_sup_span_eq_top
    (range_trajectoryOperator_sup_span_metricVariations_eq_top hf hγ hp hq hbot htop hAL hU hcrit)

end TauCeti
