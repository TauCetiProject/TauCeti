/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Fredholm
public import TauCeti.Analysis.ODE.TrajectoryOperator.FreeEndpoint
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
`(ξ, H) ↦ D_γ ξ - H(γ) ∇f(γ)`.

When the ends of `γ` are degenerate critical points, as along a trajectory between two critical
manifolds of a Morse–Bott function, the trajectory operator is studied on the spaces weighted by
`exp w` for a weight `w` with slopes `δ±` at `±∞`. Multiplication by `exp w` identifies them with
the unweighted spaces and conjugates `D_γ` to `ξ ↦ ξ' + (Hess f(γ) - w') ξ`, and it sends the path
of a metric variation to `s ↦ exp (w s) • H (γ s) (∇f (γ s))`. The **metric variations** along `γ`
localized in a set `U`, with weight `w` (`TauCeti.metricVariations f γ w U`), form the subspace of
`L²(ℝ, E)` of the classes of these paths, for smooth compactly supported symmetric fields `H`
supported in `U`. The unweighted variations are those of weight `0`.

This file proves that these variations make the universal linearization onto as soon as `U` is a
neighbourhood of one point `γ s₀` of the trajectory that is not a critical point of `f`:

* for every continuous shift `c` and weight `w`, a path orthogonal to the range of
  `ξ ↦ ξ' + (Hess f(γ) - c) ξ` and to the metric variations of weight `w` vanishes
  (`TauCeti.eq_zero_of_mem_orthogonal_range_trajectoryOperator_of_forall_inner_eq_zero`), so the
  range and the variations span `L²(ℝ, E)` whenever the range is closed of finite codimension, as
  for a Fredholm operator
  (`TauCeti.range_trajectoryOperator_sup_metricVariations_eq_top_of_isClosed_of_coFG`);
* along a trajectory between nondegenerate critical points, without weights
  (`TauCeti.range_trajectoryOperator_sup_metricVariations_eq_top`), and finitely many variations
  already suffice
  (`TauCeti.exists_finset_subset_metricVariations_range_trajectoryOperator_sup_span_eq_top`);
* along a trajectory between possibly degenerate critical points `p` and `q`, on the weighted
  spaces whose slopes `δ±` are not eigenvalues of `Hess f(p)` and `Hess f(q)`
  (`TauCeti.range_trajectoryOperator_sub_smul_id_sup_metricVariations_eq_top`), and also for the
  operator extended by free endpoint variables, which records the trajectories converging to
  points of the critical manifolds rather than to `p` and `q` themselves
  (`TauCeti.range_coprod_endTailL_sup_metricVariations_eq_top`).

For a finite family of trajectories, such as the pieces of a broken trajectory, one metric
variation serves all of them at once when it is localized in windows near regular points of each
trajectory that the other trajectories avoid: every family of paths in `L²(ℝ, E)` is then reached
by the operators along the trajectories and the paths of a single field `H`
(`TauCeti.exists_forall_sub_ae_eq_of_forall_range_sup_metricVariations_eq_top`). Windows cut out
by the regular levels of `f` are avoided by the other trajectories as soon as the ranges of values
of `f` along them overlap at most at their ends, as for consecutive pieces of a broken trajectory
(`TauCeti.exists_forall_sub_ae_eq_of_forall_mem_nhds_range_sup_metricVariations_eq_top`). These
statements hold at the given inner product of `E`, and are the surjectivity input for the universal
linearization in the Fredholm-theoretic proofs that Morse–Smale metrics, and metrics transverse
along the broken trajectories of a Morse–Bott function, are generic.

The proof goes through the cokernel. A path `v` orthogonal to the range of
`ξ ↦ ξ' + (Hess f(γ) - c) ξ` agrees almost everywhere with a solution `u` of the formal adjoint
equation `u' = (Hess f(γ) - c) u`
(`WeakDerivStep.exists_hasDerivAt_adjoint_of_mem_orthogonal_range_trajectoryOperator`), and if
`u` vanishes at one time it vanishes identically, by uniqueness for linear equations. If
`u (s₀) ≠ 0`, take the symmetric operator
`B x = ⟪∇f(γ s₀), x⟫ u(s₀) + ⟪u(s₀), x⟫ ∇f(γ s₀)`, for which `⟪B ∇f(γ s₀), u(s₀)⟫ > 0`, and a
bump function `ψ` at `γ s₀`. Since `f` strictly decreases along `γ` near the regular point
`γ s₀`, and decreases along all of `γ`, a small enough bump meets the trajectory only at times
close to `s₀`, where `⟪B ∇f(γ s), exp (w s) • u(s)⟫ > 0`. So the variation `H = ψ B` pairs
positively with `v`
(`TauCeti.eq_zero_of_mem_orthogonal_range_trajectoryOperator_of_forall_inner_eq_zero`). When the
range is closed with finite codimension, as a Fredholm range is, the sum of the range and the
variations is closed, and its orthogonal complement is zero
(`TauCeti.range_trajectoryOperator_sup_metricVariations_eq_top_of_isClosed_of_coFG`).

## Main definitions

* `TauCeti.metricVariations f γ w U`: the metric variations along `γ` localized in `U`, with
  weight `w`.

## Main results

* `TauCeti.eq_zero_of_mem_orthogonal_range_trajectoryOperator_of_forall_inner_eq_zero`: a path
  orthogonal to the range of `ξ ↦ ξ' + (Hess f(γ) - c) ξ` and to the metric variations localized
  near a regular point of `γ` vanishes.
* `TauCeti.range_trajectoryOperator_sup_metricVariations_eq_top`: the range of `D_γ` and the
  metric variations span `L²(ℝ, E)`.
* `TauCeti.exists_finset_subset_metricVariations_range_trajectoryOperator_sup_span_eq_top`:
  finitely many metric variations suffice.
* `TauCeti.range_trajectoryOperator_sub_smul_id_sup_metricVariations_eq_top` and
  `TauCeti.range_coprod_endTailL_sup_metricVariations_eq_top`: the same on weighted spaces, along
  a trajectory between possibly degenerate critical points, without and with free endpoint
  variables.
* `TauCeti.exists_forall_sub_ae_eq_of_forall_range_sup_metricVariations_eq_top` and
  `TauCeti.exists_forall_sub_ae_eq_of_forall_mem_nhds_range_sup_metricVariations_eq_top`: one
  metric variation localized in disjoint windows serves a finite family of trajectories at once.

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

/-- The smooth compactly supported fields of symmetric operators supported in `U`, those whose
paths make up the metric variations. -/
private def symmetricFields (U : Set E) : Submodule ℝ (E → E →L[ℝ] E) where
  carrier := {H | ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ U ∧
    ∀ x, IsSelfAdjoint (H x)}
  add_mem' := fun ⟨hH₁, hc₁, hU₁, hsa₁⟩ ⟨hH₂, hc₂, hU₂, hsa₂⟩ ↦ ⟨hH₁.add hH₂, hc₁.add hc₂,
    (tsupport_add _ _).trans (union_subset hU₁ hU₂), fun x ↦ (hsa₁ x).add (hsa₂ x)⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp, fun _ ↦ .zero _⟩
  smul_mem' a H := fun ⟨hH, hc, hU, hsa⟩ ↦ by
    have hsupp : tsupport (fun x ↦ a • H x) ⊆ tsupport H := tsupport_smul_subset_right (fun _ ↦ a) H
    exact ⟨hH.const_smul a, hc.mono' ((subset_tsupport _).trans hsupp), hsupp.trans hU,
      fun x ↦ (IsSelfAdjoint.all a).smul (hsa x)⟩

variable (f γ) in
/-- The **metric variations** along `γ` localized in `U`, with weight `w`: the subspace of
`L²(ℝ, E)` of the classes of the paths `s ↦ exp (w s) • H (γ s) (∇f (γ s))`, for smooth compactly
supported fields `H` of symmetric operators with support in `U`. For the metric
`⟪(1 + ε H x) u, v⟫`, the path `s ↦ H (γ s) (∇f (γ s))` is minus the derivative at `ε = 0` of the
gradient `(1 + ε H)⁻¹ ∇f` along `γ`, the direction in which varying the metric moves the gradient
trajectory equation at `γ`; multiplying by `exp w` reads it in the coordinates which identify the
spaces weighted by `exp w` with the unweighted ones. The unweighted variations have weight `0`. -/
def metricVariations (w : ℝ → ℝ) (U : Set E) :
    Submodule ℝ (Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))) where
  carrier := {g | ∃ H : E → E →L[ℝ] E, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ U ∧
    (∀ x, IsSelfAdjoint (H x)) ∧
    g =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ Real.exp (w s) • H (γ s) (∇ f (γ s))}
  add_mem' := by
    rintro g₁ g₂ ⟨H₁, hH₁, hc₁, hU₁, hsa₁, hg₁⟩ ⟨H₂, hH₂, hc₂, hU₂, hsa₂, hg₂⟩
    obtain ⟨hH, hc, hU, hsa⟩ : H₁ + H₂ ∈ symmetricFields U :=
      add_mem (s := symmetricFields U) ⟨hH₁, hc₁, hU₁, hsa₁⟩ ⟨hH₂, hc₂, hU₂, hsa₂⟩
    refine ⟨H₁ + H₂, hH, hc, hU, hsa, ?_⟩
    filter_upwards [Lp.coeFn_add g₁ g₂, hg₁, hg₂] with s hs h₁ h₂
    simp only [hs, Pi.add_apply, h₁, h₂, add_apply, smul_add]
  zero_mem' := by
    obtain ⟨hH, hc, hU, hsa⟩ := (symmetricFields U).zero_mem
    exact ⟨0, hH, hc, hU, hsa, (Lp.coeFn_zero _ _ _).trans (.of_forall fun s ↦ by simp)⟩
  smul_mem' := by
    rintro a g ⟨H, hH, hc, hU, hsa, hg⟩
    obtain ⟨hH', hc', hU', hsa'⟩ : a • H ∈ symmetricFields U :=
      (symmetricFields U).smul_mem a ⟨hH, hc, hU, hsa⟩
    refine ⟨a • H, hH', hc', hU', hsa', ?_⟩
    filter_upwards [Lp.coeFn_smul a g, hg] with s hs h
    simp only [hs, Pi.smul_apply, h, smul_apply, smul_comm a]

/-- Membership in the metric variations. -/
theorem mem_metricVariations {w : ℝ → ℝ} {U : Set E}
    {g : Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))} :
    g ∈ metricVariations f γ w U ↔ ∃ H : E → E →L[ℝ] E, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      tsupport H ⊆ U ∧ (∀ x, IsSelfAdjoint (H x)) ∧
      g =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
        fun s ↦ Real.exp (w s) • H (γ s) (∇ f (γ s)) :=
  Iff.rfl

/-- Metric variations localized in a smaller set are metric variations localized in a larger
one. -/
theorem metricVariations_mono {w : ℝ → ℝ} {U V : Set E} (h : U ⊆ V) :
    metricVariations f γ w U ≤ metricVariations f γ w V :=
  fun _ ⟨H, hH, hc, hU, hsa, hg⟩ ↦ ⟨H, hH, hc, hU.trans h, hsa, hg⟩

/-! ### A metric variation pairing positively with a given path -/

open InnerProductSpace in
/-- Near a point `γ s₀` of a negative gradient trajectory which is not a critical point of `f`, a
continuous path `u` with `u s₀ ≠ 0` pairs positively with the path of some metric variation
localized in a given neighbourhood of `γ s₀`. The variation is `H = ψ B` for a bump function `ψ`
at `γ s₀` and the symmetric operator `B x = ⟪∇f(γ s₀), x⟫ u(s₀) + ⟪u(s₀), x⟫ ∇f(γ s₀)`, which
pairs `∇f(γ s)` positively with `u s` for `s` near `s₀`; the bump is so small that the trajectory
only meets it at such times (`TauCeti.exists_contDiff_tsupport_subset_integral_comp_mul_pos`). -/
private theorem exists_integral_inner_metricVariation_pos (hf : ContDiff ℝ 2 f)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) {U : Set E} {s₀ : ℝ} (hU : U ∈ 𝓝 (γ s₀))
    (hcrit : ∇ f (γ s₀) ≠ 0) {u : ℝ → E} (huc : Continuous u) (hu0 : u s₀ ≠ 0) :
    ∃ H : E → E →L[ℝ] E, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ U ∧
      (∀ x, IsSelfAdjoint (H x)) ∧ HasCompactSupport (fun s ↦ H (γ s) (∇ f (γ s))) ∧
      0 < ∫ s, ⟪H (γ s) (∇ f (γ s)), u s⟫ := by
  set B := rankOne ℝ (u s₀) (∇ f (γ s₀)) + rankOne ℝ (∇ f (γ s₀)) (u s₀) with hB
  have hBsa : IsSelfAdjoint B := by
    rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint, hB, map_add, adjoint_rankOne,
      adjoint_rankOne, add_comm]
  have hg : Continuous fun t ↦ ∇ f (γ t) :=
    (hf.continuous_gradient (by norm_num)).comp hγ.continuous
  have hq : Continuous fun s ↦ ⟪B (∇ f (γ s)), u s⟫ := (B.continuous.comp hg).inner huc
  -- A small ball around `γ s₀` meets the trajectory only at times close to `s₀`.
  have hvisit : comap γ (𝓝 (γ s₀)) ≤ 𝓝 s₀ := by
    intro S hS
    obtain ⟨δ, hδ, hδS⟩ := Metric.mem_nhds_iff.1 hS
    obtain ⟨r, hr, hrs⟩ := hγ.exists_pos_forall_dist_lt_mem_Ioo
      (fun t ↦ hf.differentiable (by norm_num) _) hcrit hδ
    exact mem_comap.2 ⟨Metric.ball (γ s₀) r, Metric.ball_mem_nhds _ hr,
      fun s hs ↦ hδS (by rw [Real.ball_eq_Ioo]; exact hrs s hs)⟩
  obtain ⟨ψ, hψ, hψc, hψU, hψγ, hpos⟩ := exists_contDiff_tsupport_subset_integral_comp_mul_pos
    hγ.continuous hvisit hU hq (inner_rankOne_add_rankOne_apply_pos hcrit hu0)
  refine ⟨fun x ↦ ψ x • B, hψ.smul contDiff_const, hψc.smul_right,
    (tsupport_smul_subset_left _ _).trans hψU, fun x ↦ (IsSelfAdjoint.all (ψ x)).smul hBsa,
    hψγ.mono fun s hs h ↦ hs (by simp [h]), ?_⟩
  simpa only [smul_apply, real_inner_smul_left] using hpos

/-! ### The cokernel is detected by metric variations -/

/-- **Paths orthogonal to the range and to the metric variations vanish.** Let `f` be `C²` and `γ`
a negative gradient trajectory, and let `U` be a neighbourhood of a point `γ s₀` of the trajectory
which is not a critical point of `f`. For continuous `c` and `w`, a path `v ∈ L²(ℝ, E)` orthogonal
to the range of the operator `ξ ↦ ξ' + (Hess f(γ) - c) ξ` and to every metric variation of weight
`w` localized in `U` vanishes. For `c = w'` this operator is the linearized operator `D_γ` read on
the spaces weighted by `exp w`; for `c = w = 0` it is `D_γ` itself. -/
theorem eq_zero_of_mem_orthogonal_range_trajectoryOperator_of_forall_inner_eq_zero
    (hf : ContDiff ℝ 2 f) (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) {c w : ℝ → ℝ}
    (hc : Continuous c) (hw : Continuous w)
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator f (γ s) - c s • ContinuousLinearMap.id ℝ E)
    {U : Set E} {s₀ : ℝ} (hU : U ∈ 𝓝 (γ s₀)) (hcrit : ∇ f (γ s₀) ≠ 0)
    {v : Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}
    (hv : v ∈ (WeakDerivStep.trajectoryOperator (p := 2) AL).rangeᗮ)
    (hvar : ∀ g ∈ metricVariations f γ w U, ⟪g, v⟫ = 0) : v = 0 := by
  have hvol : volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ) = volume := by simp
  have hA : Continuous fun s ↦ hessianOperator f (γ s) - c s • ContinuousLinearMap.id ℝ E :=
    ((hf.contDiff_hessianOperator (m := 0) (by norm_num)).continuous.comp hγ.continuous).sub
      (hc.smul continuous_const)
  -- `v` is a solution of the adjoint equation `u' = (Hess f(γ) - c) u`, the coefficient being
  -- symmetric.
  obtain ⟨u, hu, hvu⟩ :=
    WeakDerivStep.exists_hasDerivAt_adjoint_of_mem_orthogonal_range_trajectoryOperator hA hAL hv
  have hu' (s : ℝ) :
      HasDerivAt u ((hessianOperator f (γ s) - c s • ContinuousLinearMap.id ℝ E) (u s)) s := by
    have hsa : IsSelfAdjoint (hessianOperator f (γ s) - c s • ContinuousLinearMap.id ℝ E) :=
      hf.contDiffAt.isSelfAdjoint_hessianOperator.sub
        ((IsSelfAdjoint.all (c s)).smul (IsSelfAdjoint.one _))
    simpa only [hsa.adjoint_eq] using hu s
  have huc : Continuous u := continuous_iff_continuousAt.2 fun s ↦ (hu' s).continuousAt
  by_contra hv0
  -- A solution vanishing at one time vanishes identically.
  have hu0 : u s₀ ≠ 0 := by
    intro h
    have hu00 : u = fun _ ↦ 0 := hA.eq_of_hasDerivAt_clm_apply hu' (fun s ↦ by
      simpa using hasDerivAt_const s (0 : E)) h
    exact hv0 (Lp.eq_zero_iff_ae_eq_zero.2 (hvu.trans (.of_forall fun s ↦ by simp [hu00])))
  obtain ⟨H, hHs, hHc, hHU, hHsa, hpath_supp, hpos⟩ := exists_integral_inner_metricVariation_pos
    hf hγ hU hcrit (hw.rexp.smul huc) (smul_ne_zero (Real.exp_pos _).ne' hu0)
  -- The weighted path of `H` lies in `L²(ℝ, E)`, as a metric variation localized in `U`.
  have hmem : MemLp (fun s ↦ Real.exp (w s) • H (γ s) (∇ f (γ s))) 2
      (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)) := by
    rw [hvol]
    exact (hw.rexp.smul ((hHs.continuous.comp hγ.continuous).clm_apply
      ((hf.continuous_gradient (by norm_num)).comp hγ.continuous))).memLp_of_hasCompactSupport
        hpath_supp.smul_left
  have hint : ∫ s, ⟪H (γ s) (∇ f (γ s)), Real.exp (w s) • u s⟫ = ⟪hmem.toLp _, v⟫ := by
    simp only [L2.toLp_inner_of_ae_eq hmem hvu, hvol, real_inner_smul_left, real_inner_smul_right]
  exact hpos.ne' (hint.trans (hvar _ ⟨H, hHs, hHc, hHU, hHsa, hmem.coeFn_toLp⟩))

/-! ### Surjectivity of the universal linearization -/

/-- **Localized metric variations make a linearized operator with closed range of finite
codimension onto.** Let `f` be `C²`, `γ` a negative gradient trajectory, and `U` a neighbourhood
of a point `γ s₀` of the trajectory which is not a critical point of `f`. For continuous `c` and
`w`, if the operator `ξ ↦ ξ' + (Hess f(γ) - c) ξ` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` has closed
range of finite codimension, as a Fredholm operator does, then its range and the metric variations
of weight `w` localized in `U` together span `L²(ℝ, E)`. -/
theorem range_trajectoryOperator_sup_metricVariations_eq_top_of_isClosed_of_coFG
    (hf : ContDiff ℝ 2 f) (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) {c w : ℝ → ℝ}
    (hc : Continuous c) (hw : Continuous w)
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator f (γ s) - c s • ContinuousLinearMap.id ℝ E)
    {U : Set E} {s₀ : ℝ} (hU : U ∈ 𝓝 (γ s₀)) (hcrit : ∇ f (γ s₀) ≠ 0)
    (hDc : IsClosed ((WeakDerivStep.trajectoryOperator (p := 2) AL).range :
      Set (Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)))))
    (hDf : (WeakDerivStep.trajectoryOperator (p := 2) AL).range.CoFG) :
    (WeakDerivStep.trajectoryOperator (p := 2) AL).range ⊔ metricVariations f γ w U = ⊤ := by
  have := hDf
  -- The sum contains the closed range, of finite codimension, so it is closed.
  have hK : IsClosed (((WeakDerivStep.trajectoryOperator (p := 2) AL).range ⊔
      metricVariations f γ w U : Submodule ℝ _) : Set
        (Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)))) :=
    Submodule.isClosed_mono_of_finiteDimensional_quotient hDc le_sup_left
  have := hK.completeSpace_coe
  rw [← Submodule.orthogonal_eq_bot_iff, eq_bot_iff]
  intro v hv
  rw [← Submodule.inf_orthogonal] at hv
  exact eq_zero_of_mem_orthogonal_range_trajectoryOperator_of_forall_inner_eq_zero hf hγ hc hw hAL
    hU hcrit hv.1 fun g hg ↦ (Submodule.mem_orthogonal _ _).1 hv.2 g hg

/-- **Localized metric variations make the linearized operator onto.** Let `f` be a `C²` function
on a finite-dimensional real inner product space and `γ` a negative gradient trajectory from a
nondegenerate critical point `p` at `-∞` to a nondegenerate critical point `q` at `+∞`. If `U` is
a neighbourhood of a point `γ s₀` of the trajectory which is not a critical point of `f`, the range
of the linearized operator `ξ ↦ ξ' + Hess f(γ) ξ` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` and the
unweighted metric variations localized in `U` together span `L²(ℝ, E)`. In other words, the
universal linearization `(ξ, H) ↦ D_γ ξ - H(γ) ∇f(γ)` of the trajectory equation, in the
trajectory and the metric, is onto. -/
theorem range_trajectoryOperator_sup_metricVariations_eq_top
    (hf : ContDiff ℝ 2 f) (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) {p q : E}
    (hp : IsNondegenerateCriticalPoint f p) (hq : IsNondegenerateCriticalPoint f q)
    (hbot : Tendsto γ atBot (𝓝 p)) (htop : Tendsto γ atTop (𝓝 q))
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator f (γ s))
    {U : Set E} {s₀ : ℝ} (hU : U ∈ 𝓝 (γ s₀)) (hcrit : ∇ f (γ s₀) ≠ 0) :
    (WeakDerivStep.trajectoryOperator (p := 2) AL).range ⊔ metricVariations f γ 0 U = ⊤ := by
  have hD := hγ.isFredholm_trajectoryOperator_hessianOperator hf hp hq hbot htop hAL
  exact range_trajectoryOperator_sup_metricVariations_eq_top_of_isClosed_of_coFG hf hγ
    (c := fun _ ↦ 0) continuous_const continuous_const (hAL.trans (.of_forall fun s ↦ by simp))
    hU hcrit hD.isClosed_range hD.finite_coker

/-- **Finitely many localized metric variations make the linearized operator onto.** Under the
hypotheses of `TauCeti.range_trajectoryOperator_sup_metricVariations_eq_top`, finitely many
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
      (t : Set (Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)))) ⊆
        metricVariations f γ 0 U ∧
        (WeakDerivStep.trajectoryOperator (p := 2) AL).range ⊔ Submodule.span ℝ t = ⊤ := by
  have := (hγ.isFredholm_trajectoryOperator_hessianOperator hf hp hq hbot htop hAL).finite_coker
  refine Submodule.exists_finset_subset_sup_span_eq_top ?_
  rw [Submodule.span_eq]
  exact range_trajectoryOperator_sup_metricVariations_eq_top hf hγ hp hq hbot htop hAL hU hcrit

/-! ### Weighted spaces and free endpoint variables -/

/-- **Localized metric variations make the weighted linearized operator onto.** Let `f` be a `C²`
function on a finite-dimensional real inner product space and `γ` a negative gradient trajectory
from a critical point `p` at `-∞` to a critical point `q` at `+∞`, which may be degenerate, as for
a trajectory between two critical manifolds of a Morse–Bott function. Let `c` be a continuous
slope tending to `δ±` at `±∞`, where `δ⁻` is not an eigenvalue of `Hess f(p)` and `δ⁺` is not an
eigenvalue of `Hess f(q)`. If `U` is a neighbourhood of a point `γ s₀` of the trajectory which is
not a critical point of `f`, then for every continuous weight `w` the range of the operator
`ξ ↦ ξ' + (Hess f(γ) - c) ξ` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` and the metric variations of weight
`w` localized in `U` together span `L²(ℝ, E)`. For `c = w'` this is the surjectivity of the
universal linearization on the spaces weighted by `exp w`. -/
theorem range_trajectoryOperator_sub_smul_id_sup_metricVariations_eq_top
    (hf : ContDiff ℝ 2 f) (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) {p q : E}
    (hbot : Tendsto γ atBot (𝓝 p)) (htop : Tendsto γ atTop (𝓝 q))
    {c : ℝ → ℝ} (hc : Continuous c) {δminus δplus : ℝ}
    (hcbot : Tendsto c atBot (𝓝 δminus)) (hctop : Tendsto c atTop (𝓝 δplus))
    (hδminus : ¬Module.End.HasEigenvalue (hessianOperator f p : E →ₗ[ℝ] E) δminus)
    (hδplus : ¬Module.End.HasEigenvalue (hessianOperator f q : E →ₗ[ℝ] E) δplus)
    {w : ℝ → ℝ} (hw : Continuous w)
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator f (γ s) - c s • ContinuousLinearMap.id ℝ E)
    {U : Set E} {s₀ : ℝ} (hU : U ∈ 𝓝 (γ s₀)) (hcrit : ∇ f (γ s₀) ≠ 0) :
    (WeakDerivStep.trajectoryOperator (p := 2) AL).range ⊔ metricVariations f γ w U = ⊤ := by
  have hH := (hf.contDiff_hessianOperator (m := 0) (by norm_num)).continuous
  have hD := WeakDerivStep.isFredholm_trajectoryOperator_sub_smul_id (hH.comp hγ.continuous)
    hf.contDiffAt.isSelfAdjoint_hessianOperator.isSymmetric
    hf.contDiffAt.isSelfAdjoint_hessianOperator.isSymmetric
    ((hH.tendsto p).comp hbot) ((hH.tendsto q).comp htop) hc hcbot hctop hδminus hδplus AL hAL
  exact range_trajectoryOperator_sup_metricVariations_eq_top_of_isClosed_of_coFG hf hγ hc hw hAL
    hU hcrit hD.isClosed_range hD.finite_coker

/-- **Localized metric variations make the linearized operator with free endpoint variables
onto.** Under the hypotheses of
`TauCeti.range_trajectoryOperator_sub_smul_id_sup_metricVariations_eq_top`, adjoin to the operator
`ξ ↦ ξ' + (Hess f(γ) - c) ξ` free endpoint variables in finitely many subspaces `K i`, through
cutoffs `χ i` and the weight `w` (`TauCeti.WeakDerivStep.endTailL`). The range of the extended
operator and the metric variations of weight `w` localized in `U` together span `L²(ℝ, E)`. For a
trajectory between critical manifolds `C` and `D` of a Morse–Bott function, with `c = w'`, the free
variables `T C = ker Hess f(p)` at `-∞` and `T D = ker Hess f(q)` at `+∞`, this is the
surjectivity of the universal linearization of the equation of the trajectories from `C` to `D`,
whose ends move in the critical manifolds. -/
theorem range_coprod_endTailL_sup_metricVariations_eq_top
    (hf : ContDiff ℝ 2 f) (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) {p q : E}
    (hbot : Tendsto γ atBot (𝓝 p)) (htop : Tendsto γ atTop (𝓝 q))
    {c : ℝ → ℝ} (hc : Continuous c) {δminus δplus : ℝ}
    (hcbot : Tendsto c atBot (𝓝 δminus)) (hctop : Tendsto c atTop (𝓝 δplus))
    (hδminus : ¬Module.End.HasEigenvalue (hessianOperator f p : E →ₗ[ℝ] E) δminus)
    (hδplus : ¬Module.End.HasEigenvalue (hessianOperator f q : E →ₗ[ℝ] E) δplus)
    {w : ℝ → ℝ} (hw : Continuous w)
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator f (γ s) - c s • ContinuousLinearMap.id ℝ E)
    {ι : Type*} [Fintype ι] {χ : ι → ℝ → ℝ} {K : ι → Submodule ℝ E}
    (hmem : ∀ i, ∀ v ∈ K i, MemLp (endTail w (χ i) (fun s ↦ hessianOperator f (γ s)) v) 2)
    {U : Set E} {s₀ : ℝ} (hU : U ∈ 𝓝 (γ s₀)) (hcrit : ∇ f (γ s₀) ≠ 0) :
    ((WeakDerivStep.trajectoryOperator (p := 2) AL).coprod
      (WeakDerivStep.endTailL w χ (fun s ↦ hessianOperator f (γ s)) hmem)).range ⊔
        metricVariations f γ w U = ⊤ := by
  refine eq_top_iff.2 ((range_trajectoryOperator_sub_smul_id_sup_metricVariations_eq_top hf hγ
    hbot htop hc hcbot hctop hδminus hδplus hw hAL hU hcrit).ge.trans (sup_le_sup_right ?_ _))
  rintro _ ⟨ξ, rfl⟩
  exact ⟨(ξ, 0), by simp⟩

/-! ### Finite families of trajectories -/

/-- **One metric variation for finitely many trajectories.** Let `γ j`, for `j` in a finite type,
be paths, and `T j` linear maps into `L²(ℝ, E)` whose ranges span `L²(ℝ, E)` together with the
metric variations along `γ j` of weight `w j` localized in `U j`. If the path `γ j` avoids every
other window `U i`, then for every family `g` of paths in `L²(ℝ, E)` there are `x j` and one smooth
compactly supported field `H` of symmetric operators supported in the union of the windows with
`g j - T j (x j) = exp (w j) • H (γ j) (∇f (γ j))` for every `j`. Applied to the linearized
operators along the pieces of a broken trajectory, it makes the universal linearization of the
product of their trajectory equations onto, by one variation of the metric in disjoint windows;
the matching conditions between consecutive pieces are not part of this statement. -/
theorem exists_forall_sub_ae_eq_of_forall_range_sup_metricVariations_eq_top {ι : Type*}
    [Finite ι] {γ : ι → ℝ → E} {w : ι → ℝ → ℝ} {U : ι → Set E} {X : ι → Type*}
    [∀ j, AddCommGroup (X j)] [∀ j, Module ℝ (X j)]
    (T : ∀ j, X j →ₗ[ℝ] Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)))
    (hT : ∀ j, LinearMap.range (T j) ⊔ metricVariations f (γ j) (w j) (U j) = ⊤)
    (hdisj : ∀ i j, i ≠ j → ∀ s, γ j s ∉ U i)
    (g : ι → Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))) :
    ∃ x : ∀ j, X j, ∃ H : E → E →L[ℝ] E, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      tsupport H ⊆ ⋃ j, U j ∧ (∀ y, IsSelfAdjoint (H y)) ∧
      ∀ j, g j - T j (x j) =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
        fun s ↦ Real.exp (w j s) • H (γ j s) (∇ f (γ j s)) := by
  have := Fintype.ofFinite ι
  -- Split each `g j` into a value of `T j` and a metric variation along `γ j`.
  choose y hy z hz hyz using fun j ↦
    Submodule.mem_sup.1 ((hT j).symm ▸ Submodule.mem_top (x := g j))
  choose x hx using hy
  choose H hHs hHc hHU hHsa hHz using hz
  -- The sum of the fields is supported in the union of the windows.
  obtain ⟨hsHs, hsHc, hsHU, hsHsa⟩ : ∑ i, H i ∈ symmetricFields (⋃ j, U j) :=
    Submodule.sum_mem _ fun i _ ↦ ⟨hHs i, hHc i, (hHU i).trans (subset_iUnion _ i), hHsa i⟩
  refine ⟨x, ∑ i, H i, hsHs, hsHc, hsHU, hsHsa, fun j ↦ ?_⟩
  -- Along `γ j` only the field `H j` is seen, since `γ j` avoids the other windows.
  have hγj (s : ℝ) : (∑ i, H i) (γ j s) = H j (γ j s) := by
    rw [Finset.sum_apply, Finset.sum_eq_single j (fun i _ hij ↦ image_eq_zero_of_notMem_tsupport
      fun h ↦ hdisj i j hij s (hHU i h)) (by simp)]
  rw [hx, ← hyz j, add_sub_cancel_left]
  filter_upwards [hHz j] with s hs
  rw [hs, hγj]

/-- **One metric variation for a broken trajectory, in windows at regular levels.** Let `f` be
differentiable and `γ j`, for `j` in a finite type, negative gradient trajectories from `p j` to
`q j` whose ranges of values `[f (q j), f (p j)]` overlap at most at their ends, as for the
consecutive pieces of a broken trajectory. Let `γ j (s₀ j)` be a regular point of each, and `T j`
linear maps into `L²(ℝ, E)` whose ranges span `L²(ℝ, E)` together with the metric variations along
`γ j` of weight `w j` localized in any neighbourhood of `γ j (s₀ j)`, as for the linearized
operators of `TauCeti.range_trajectoryOperator_sup_metricVariations_eq_top`,
`TauCeti.range_trajectoryOperator_sub_smul_id_sup_metricVariations_eq_top` and
`TauCeti.range_coprod_endTailL_sup_metricVariations_eq_top`. Then for all neighbourhoods `U j` of
`γ j (s₀ j)` and every family `g` of paths in `L²(ℝ, E)` there are `x j` and one smooth compactly
supported field `H` of symmetric operators supported in the union of the windows
`U j ∩ f⁻¹ (f (q j), f (p j))`, which the other trajectories avoid, with
`g j - T j (x j) = exp (w j) • H (γ j) (∇f (γ j))` for every `j`. -/
theorem exists_forall_sub_ae_eq_of_forall_mem_nhds_range_sup_metricVariations_eq_top {ι : Type*}
    [Finite ι] (hf : Differentiable ℝ f) {γ : ι → ℝ → E}
    (hγ : ∀ j, IsIntegralCurve (γ j) (fun _ x ↦ -∇ f x)) {p q : ι → E}
    (hbot : ∀ j, Tendsto (γ j) atBot (𝓝 (p j))) (htop : ∀ j, Tendsto (γ j) atTop (𝓝 (q j)))
    (hlevel : ∀ i j, i ≠ j → f (p j) ≤ f (q i) ∨ f (p i) ≤ f (q j))
    {s₀ : ι → ℝ} (hcrit : ∀ j, ∇ f (γ j (s₀ j)) ≠ 0) {w : ι → ℝ → ℝ} {X : ι → Type*}
    [∀ j, AddCommGroup (X j)] [∀ j, Module ℝ (X j)]
    (T : ∀ j, X j →ₗ[ℝ] Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)))
    (hT : ∀ j, ∀ V ∈ 𝓝 (γ j (s₀ j)),
      LinearMap.range (T j) ⊔ metricVariations f (γ j) (w j) V = ⊤)
    {U : ι → Set E} (hU : ∀ j, U j ∈ 𝓝 (γ j (s₀ j)))
    (g : ι → Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))) :
    ∃ x : ∀ j, X j, ∃ H : E → E →L[ℝ] E, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      tsupport H ⊆ ⋃ j, U j ∩ f ⁻¹' Ioo (f (q j)) (f (p j)) ∧ (∀ y, IsSelfAdjoint (H y)) ∧
      ∀ j, g j - T j (x j) =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
        fun s ↦ Real.exp (w j s) • H (γ j s) (∇ f (γ j s)) := by
  have hdiff (j : ι) (t : ℝ) : DifferentiableAt ℝ f (γ j t) := hf _
  have hfc (x : E) : ContinuousAt f x := hf.continuous.continuousAt
  have hW (j : ι) : U j ∩ f ⁻¹' Ioo (f (q j)) (f (p j)) ∈ 𝓝 (γ j (s₀ j)) :=
    inter_mem (hU j) ((hfc _).preimage_mem_nhds (isOpen_Ioo.mem_nhds
      ((hγ j).mem_Ioo_comp_neg_gradient (hdiff j) (hfc _) (hfc _) (hbot j) (htop j) (hcrit j))))
  -- The values of `f` along `γ j` lie in `[f (q j), f (p j)]`, which misses the levels of the
  -- other windows.
  have hdisj (i j : ι) (hij : i ≠ j) (s : ℝ) : γ j s ∉ U i ∩ f ⁻¹' Ioo (f (q i)) (f (p i)) := by
    rintro ⟨-, h₁, h₂⟩
    have hs := (hγ j).mem_Icc_comp_neg_gradient (hdiff j) (hfc _) (hfc _) (hbot j) (htop j) s
    rcases hlevel i j hij with h | h
    · exact (h₁.trans_le (hs.2.trans h)).false
    · exact (h₂.trans_le (h.trans hs.1)).false
  exact exists_forall_sub_ae_eq_of_forall_range_sup_metricVariations_eq_top T
    (fun j ↦ hT j _ (hW j)) hdisj g

end TauCeti
