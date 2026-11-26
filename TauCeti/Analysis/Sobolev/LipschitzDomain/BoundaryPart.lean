/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Frontier
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Intrinsic
public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart
import TauCeti.Analysis.InnerProductSpace.OfLinearIsometry
import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov
import TauCeti.Analysis.Sobolev.W1p.BoundaryPart.ChangeOfVariables
import TauCeti.MeasureTheory.Function.Lp.Restriction

/-!
# Boundary parts of a Lipschitz domain and the Poincaré–Friedrichs inequality

Let `Ω ⊆ ℝ × E` be a bounded Lipschitz domain, `σ` normalized `dim E`-dimensional Euclidean
Hausdorff measure on `frontier Ω`, `T : W^{1,p}(Ω) → Lᵖ(frontier Ω, σ)` the trace operator
(`TauCeti.W1p.frontierTrace`), `1 ≤ p < ∞`, and `Γ` a set. This file proves three facts about the
space `W^{1,p}_Γ(Ω)` of Sobolev functions vanishing on `Γ` (`TauCeti.w1pVanishingOnSubmodule`).

* With no boundary part, nothing is imposed: `W^{1,p}_∅(Ω) = W^{1,p}(Ω)`, because restrictions of
  test functions on the whole space are dense in `W^{1,p}(Ω)`.
* Every `u ∈ W^{1,p}_Γ(Ω)` has trace zero `σ`-almost everywhere on `Γ`. The generators vanish on
  `closure Γ` and are continuous up to the boundary, so their traces vanish there, and the trace is
  continuous. No regularity of `Γ` is used.
* **Poincaré–Friedrichs**: if `Ω` is moreover connected and `Γ` charges the frontier,
  `σ(Γ) > 0`, there is a constant `C` with `‖u‖_{Lᵖ(Ω)} ≤ C ‖∇u‖_{Lᵖ(Ω)}` for every
  `u ∈ W^{1,p}_Γ(Ω)`. The argument is Peetre's compact-error estimate, in the form
  `TauCeti.W1p.exists_norm_value_le_mul_norm_gradient_of_isCompactOperator` shared with
  Poincaré–Wirtinger, with Rellich compactness of `W^{1,p}(Ω) → Lᵖ(Ω)`
  (`TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith`) as the compact error. It
  needs the gradient to have no kernel on the closed subspace `W^{1,p}_Γ(Ω)`: a function there
  with zero gradient is a constant `c` on the connected `Ω`, its trace is `c`, and the trace
  vanishes on `Γ`, a set of positive surface measure, so `c = 0`.

The hypothesis `σ(Γ) > 0` cannot be dropped: for `Γ = ∅` the constant `1` has zero gradient and
nonzero norm. Neither can connectedness: on two disjoint balls with `Γ` on the frontier of the
first, the function equal to `0` on the first ball and `1` on the second is a counterexample.

The last two facts also hold on a bounded Lipschitz domain `U` of a finite-dimensional inner
product space such as `EuclideanSpace ℝ ι`, where boundary-value problems are stated, with the
trace `TauCeti.W1p.frontierTraceOfIsLipschitzDomain` and `(dim U - 1)`-dimensional surface measure.
The vanishing of the trace on `Γ` is proved as on the model space, for every additive Haar
measure. The Poincaré–Friedrichs inequality is transported from the model space along a boundary
chart of `U`, an affine isometry onto a Lipschitz domain of `ℝ × E`.

## Main declarations

* `TauCeti.w1pVanishingOnSubmodule_empty_of_isLipschitzDomainWith`: `W^{1,p}_∅(Ω) = W^{1,p}(Ω)`.
* `TauCeti.W1p.frontierTrace_ae_eq_zero_of_mem_w1pVanishingOnSubmodule`: functions in
  `W^{1,p}_Γ(Ω)` have zero trace on `Γ`.
* `TauCeti.W1p.exists_norm_value_le_mul_norm_gradient_of_mem_w1pVanishingOnSubmodule`: the
  Poincaré–Friedrichs inequality on `W^{1,p}_Γ(Ω)`, and its form
  `W1p.exists_norm_value_le_mul_norm_gradient_of_mem_w1pVanishingOnSubmodule_of_affineIsometryEquiv`
  on an open set carried onto `Ω` by an affine isometry, such as a domain in `EuclideanSpace ℝ ι`.
* `TauCeti.W1p.frontierTraceOfIsLipschitzDomain_ae_eq_zero_of_mem_w1pVanishingOnSubmodule`,
  `TauCeti.W1p.frontierTraceOfIsLipschitzDomain_ae_eq_of_sub_mem_w1pVanishingOnSubmodule` and
  `W1p.exists_norm_value_le_mul_norm_gradient_of_mem_w1pVanishingOnSubmodule_of_isLipschitzDomain`:
  the zero trace on `Γ`, the Dirichlet condition it gives, and the Poincaré–Friedrichs inequality
  on a Lipschitz domain of a Euclidean space.

## References

* S. Bauer, D. Pauly, M. Schomburg, *The Maxwell compactness property in bounded weak Lipschitz
  domains with mixed boundary conditions*, SIAM J. Math. Anal. 48 (2016), Theorem 4.8 (the
  Poincaré–Friedrichs inequality for `p = 2` in dimension three).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.1, Theorem 1 (the compactness
  argument for Poincaré inequalities).
-/

public section

noncomputable section

open Filter MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal Distributions

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Γ : Set (WithLp 2 (ℝ × E))}

/-- **No boundary part, no condition.** On a bounded Lipschitz domain and for `p < ∞`,
`W^{1,p}_∅(Ω)` is all of `W^{1,p}(Ω)`: every restriction of a test function on the whole space is
a generator, and these are dense. -/
theorem w1pVanishingOnSubmodule_empty_of_isLipschitzDomainWith (hp : p ≠ (∞ : ℝ≥0∞))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    w1pVanishingOnSubmodule volume Ω p ∅ = ⊤ :=
  eq_top_iff.2 fun u _ => (W1p.denseRange_restrictL_ofTestFunctionₗ_top hp hΩ hb).induction_on u
    (w1pVanishingOnSubmodule volume Ω p ∅).isClosed fun _ =>
      W1p.restrictL_ofTestFunctionₗ_mem_w1pVanishingOnSubmodule (by simp)

/-- **Functions vanishing on `Γ` have zero trace on `Γ`.** On a bounded Lipschitz domain and for
`p < ∞`, the trace of every `u ∈ W^{1,p}_Γ(Ω)` vanishes almost everywhere on `Γ` for surface
measure on the frontier. No regularity of `Γ` is assumed. -/
theorem W1p.frontierTrace_ae_eq_zero_of_mem_w1pVanishingOnSubmodule (hp : p ≠ (∞ : ℝ≥0∞))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {u : W1p volume Ω p}
    (hu : u ∈ w1pVanishingOnSubmodule volume Ω p Γ) :
    W1p.frontierTrace hp hΩ hb u =ᵐ[((μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E))))).restrict Γ] 0 := by
  set σ := (μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
    (frontier (Ω : Set (WithLp 2 (ℝ × E))))
  -- Vanishing on `Γ` is the kernel of a continuous linear map, hence a closed condition.
  let R := (LpToLpRestrictCLM (WithLp 2 (ℝ × E)) ℝ ℝ σ p Γ).comp (W1p.frontierTrace hp hΩ hb)
  have hclosed : IsClosed {v : W1p volume Ω p | R v = 0} := isClosed_eq R.continuous
    continuous_const
  have h := w1pVanishingOnSubmodule_subset_of_isClosed hclosed (fun φ hφ => ?_) hu
  · exact (LpToLpRestrictCLM_eq_zero_iff (𝕜 := ℝ) Γ _).1 h
  -- A generator is continuous up to the boundary, so its trace is itself, which is zero on
  -- `closure Γ`.
  rw [mem_ofPred, ContinuousLinearMap.comp_apply, LpToLpRestrictCLM_eq_zero_iff (𝕜 := ℝ)]
  filter_upwards [ae_restrict_of_ae (W1p.frontierTrace_ae_eq_of_continuousOn hp hΩ hb
      φ.continuous.continuousOn (W1p.value_restrictL_ofTestFunctionₗ_ae le_top φ)),
    ae_restrict_of_ae_restrict_of_subset subset_closure
      (ae_restrict_mem (μ := σ) isClosed_closure.measurableSet)] with x hx hxΓ
  rw [hx, Pi.zero_apply]
  exact image_eq_zero_of_notMem_tsupport (hφ.notMem_of_mem_right hxΓ)

/-- On a connected domain, a function of `W^{1,p}_Γ(Ω)` with zero gradient vanishes when `Γ`
charges the frontier: it is a constant, which is its trace, and the trace vanishes on `Γ`. -/
private theorem W1p.eq_zero_of_gradient_eq_zero_of_mem_w1pVanishingOnSubmodule
    (hp : p ≠ (∞ : ℝ≥0∞)) (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    (hconn : IsPreconnected (Ω : Set (WithLp 2 (ℝ × E))))
    (hΓ : (μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E)))
      (Γ ∩ frontier (Ω : Set (WithLp 2 (ℝ × E)))) ≠ 0)
    {u : W1p volume Ω p} (hu : u ∈ w1pVanishingOnSubmodule volume Ω p Γ)
    (hgrad : W1p.gradient u = 0) : u = 0 := by
  obtain ⟨c, hc⟩ := W1p.exists_value_ae_eq_const_of_gradient_eq_zero hconn hgrad
  -- The surface measure on `Γ` is nonzero, so a property holding almost everywhere there holds
  -- somewhere.
  have hne : ((μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E))))).restrict Γ ≠ 0 := by
    rwa [← Measure.measure_univ_ne_zero, Measure.restrict_apply_univ,
      Measure.restrict_apply' isClosed_frontier.measurableSet]
  have : (ae (((μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E))))).restrict Γ)).NeBot := ae_neBot.2 hne
  -- The trace of `u` is `c` on the frontier and `0` on `Γ`.
  obtain ⟨x, hxc, hx0⟩ := ((ae_restrict_of_ae (W1p.frontierTrace_ae_eq_of_continuousOn hp hΩ hb
    (f := fun _ => c) continuousOn_const hc)).and
      (W1p.frontierTrace_ae_eq_zero_of_mem_w1pVanishingOnSubmodule hp hΩ hb hu)).exists
  obtain rfl : c = 0 := by simpa using hxc.symm.trans hx0
  exact W1p.ext_value (by rw [W1p.value_zero]; exact Lp.eq_zero_iff_ae_eq_zero.2 hc)

/-- **The Poincaré–Friedrichs inequality.** Let `Ω` be a bounded connected Lipschitz domain, let
`1 ≤ p < ∞`, and let `Γ` be a set meeting the frontier in a set of positive surface measure. Then
there is a constant `C` with `‖u‖_{Lᵖ(Ω)} ≤ C ‖∇u‖_{Lᵖ(Ω)}` for every `u ∈ W^{1,p}_Γ(Ω)`. The
constant depends on `Ω`, `Γ` and `p`, and is not explicit. -/
theorem W1p.exists_norm_value_le_mul_norm_gradient_of_mem_w1pVanishingOnSubmodule
    (hp : p ≠ (∞ : ℝ≥0∞)) (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    (hconn : IsPreconnected (Ω : Set (WithLp 2 (ℝ × E))))
    (hΓ : (μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E)))
      (Γ ∩ frontier (Ω : Set (WithLp 2 (ℝ × E)))) ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ w1pVanishingOnSubmodule volume Ω p Γ,
      ‖W1p.value u‖ ≤ C * ‖W1p.gradient u‖ := by
  -- The gradient has trivial kernel on the closed subspace `W^{1,p}_Γ(Ω)`.
  have hdisj : Disjoint (W1p.gradientL (mu := volume) (Omega := Ω) (p := p)).ker
      (w1pVanishingOnSubmodule volume Ω p Γ).toSubmodule := by
    rw [Submodule.disjoint_def]
    intro u hgrad hu
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, W1p.gradientL_apply] at hgrad
    exact W1p.eq_zero_of_gradient_eq_zero_of_mem_w1pVanishingOnSubmodule hp hΩ hb hconn hΓ hu
      hgrad
  -- Rellich compactness of the value map makes the gradient bounded below there.
  exact W1p.exists_norm_value_le_mul_norm_gradient_of_isCompactOperator
    (W1p.isCompactOperator_valueL_of_isLipschitzDomainWith hΩ hb)
    (w1pVanishingOnSubmodule volume Ω p Γ).isClosed hdisj

/-- **The Poincaré–Friedrichs inequality on an isometric copy of a Lipschitz domain.** Let an
affine isometry `e` carry the open set `U` of a finite-dimensional inner product space onto a
bounded Lipschitz domain `Ω ⊆ ℝ × E`, let `U` be connected, let `1 ≤ p < ∞`, and let `Γ'` meet
the frontier of `U` in a set of positive surface measure. Then there is a constant `C` with
`‖u‖_{Lᵖ(U)} ≤ C ‖∇u‖_{Lᵖ(U)}` for every `u ∈ W^{1,p}_{Γ'}(U)`. -/
theorem
    W1p.exists_norm_value_le_mul_norm_gradient_of_mem_w1pVanishingOnSubmodule_of_affineIsometryEquiv
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] {U : Opens F} {Γ' : Set F}
    (hp : p ≠ (∞ : ℝ≥0∞)) (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (hΩU : (Ω : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' U)
    (hconn : IsPreconnected (U : Set F))
    (hΓ : (μHE[finrank ℝ E] : Measure F) (Γ' ∩ frontier (U : Set F)) ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ w1pVanishingOnSubmodule volume U p Γ',
      ‖W1p.value u‖ ≤ C * ‖W1p.gradient u‖ := by
  -- Transport the connectedness of `U` and the surface measure of `Γ'` to `Ω` along `e`.
  have hconnΩ : IsPreconnected (Ω : Set (WithLp 2 (ℝ × E))) := by
    rw [hΩU]
    exact e.symm.toHomeomorph.isPreconnected_preimage.2 hconn
  have hΓΩ : (μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E)))
      (e.symm ⁻¹' Γ' ∩ frontier (Ω : Set (WithLp 2 (ℝ × E)))) ≠ 0 := by
    have hfr : ⇑e.symm ⁻¹' frontier (U : Set F) = frontier (e.symm ⁻¹' U) :=
      e.symm.toHomeomorph.preimage_frontier _
    rwa [hΩU, ← hfr, ← preimage_inter, e.symm.isometry.euclideanHausdorffMeasure_preimage,
      e.symm.surjective.range_eq, inter_univ]
  obtain ⟨C, hC, hPF⟩ := W1p.exists_norm_value_le_mul_norm_gradient_of_mem_w1pVanishingOnSubmodule
    hp hΩ hb hconnΩ hΓΩ
  refine ⟨C, hC, fun u hu => ?_⟩
  have h := hPF _ (W1p.compAffineIsometryEquivL_mem_w1pVanishingOnSubmodule e.symm hΩU hu)
  rwa [W1p.norm_value_compAffineIsometryEquivL, W1p.norm_gradient_compAffineIsometryEquivL] at h

/-! ### Bounded Lipschitz domains of a Euclidean space -/

section Intrinsic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {U : Opens F} {Γ' : Set F}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- **Functions vanishing on `Γ` have zero trace on `Γ`, on a Lipschitz domain of a Euclidean
space.** Let `U` be a bounded open subset of a nontrivial finite-dimensional real inner product
space satisfying the Lipschitz-domain condition, let `μ` be an additive Haar measure and
`1 ≤ p < ∞`. The trace (`TauCeti.W1p.frontierTraceOfIsLipschitzDomain`) of every
`u ∈ W^{1,p}_{Γ'}(U)` vanishes almost everywhere on `Γ'` for surface measure on the frontier. No
regularity of `Γ'` is assumed. -/
theorem W1p.frontierTraceOfIsLipschitzDomain_ae_eq_zero_of_mem_w1pVanishingOnSubmodule
    [Nontrivial F] {mu : Measure F} [mu.IsAddHaarMeasure] (hp : p ≠ (∞ : ℝ≥0∞))
    (hU : (U : Set F).IsLipschitzDomain E') (hb : Bornology.IsBounded (U : Set F))
    {u : W1p mu U p} (hu : u ∈ w1pVanishingOnSubmodule mu U p Γ') :
    W1p.frontierTraceOfIsLipschitzDomain (mu := mu) hp hU hb u =ᵐ[((μHE[finrank ℝ F - 1] :
      Measure F).restrict (frontier (U : Set F))).restrict Γ'] 0 := by
  set σ := (μHE[finrank ℝ F - 1] : Measure F).restrict (frontier (U : Set F))
  -- Vanishing on `Γ'` is the kernel of a continuous linear map, hence a closed condition.
  let R := (LpToLpRestrictCLM F ℝ ℝ σ p Γ').comp
    (W1p.frontierTraceOfIsLipschitzDomain (mu := mu) hp hU hb)
  have hclosed : IsClosed {v : W1p mu U p | R v = 0} := isClosed_eq R.continuous
    continuous_const
  have h := w1pVanishingOnSubmodule_subset_of_isClosed hclosed (fun φ hφ => ?_) hu
  · exact (LpToLpRestrictCLM_eq_zero_iff (𝕜 := ℝ) Γ' _).1 h
  -- A generator is continuous up to the boundary, so its trace is itself, which is zero on
  -- `closure Γ'`.
  rw [mem_ofPred, ContinuousLinearMap.comp_apply, LpToLpRestrictCLM_eq_zero_iff (𝕜 := ℝ)]
  filter_upwards [ae_restrict_of_ae (W1p.frontierTraceOfIsLipschitzDomain_ae_eq_of_continuousOn hp
      hU hb φ.continuous.continuousOn
      (W1p.value_restrictL_ofTestFunctionₗ_ae (mu := mu) le_top φ)),
    ae_restrict_of_ae_restrict_of_subset subset_closure
      (ae_restrict_mem (μ := σ) isClosed_closure.measurableSet)] with x hx hxΓ
  rw [hx, Pi.zero_apply]
  exact image_eq_zero_of_notMem_tsupport (hφ.notMem_of_mem_right hxΓ)

/-- **Functions agreeing modulo `W^{1,p}_Γ` have the same trace on `Γ`.** On a bounded Lipschitz
domain `U` of a Euclidean space and for `p < ∞`, if `u - g ∈ W^{1,p}_{Γ'}(U)` then `T u = T g`
almost everywhere on `Γ'` for surface measure on the frontier. This is the Dirichlet condition
`u = g` on `Γ'` that membership of `u - g` in `W^{1,p}_{Γ'}(U)` imposes. -/
theorem W1p.frontierTraceOfIsLipschitzDomain_ae_eq_of_sub_mem_w1pVanishingOnSubmodule
    [Nontrivial F] {mu : Measure F} [mu.IsAddHaarMeasure] (hp : p ≠ (∞ : ℝ≥0∞))
    (hU : (U : Set F).IsLipschitzDomain E') (hb : Bornology.IsBounded (U : Set F))
    {u g : W1p mu U p} (hug : u - g ∈ w1pVanishingOnSubmodule mu U p Γ') :
    W1p.frontierTraceOfIsLipschitzDomain (mu := mu) hp hU hb u =ᵐ[((μHE[finrank ℝ F - 1] :
      Measure F).restrict (frontier (U : Set F))).restrict Γ']
        W1p.frontierTraceOfIsLipschitzDomain (mu := mu) hp hU hb g := by
  have h0 := W1p.frontierTraceOfIsLipschitzDomain_ae_eq_zero_of_mem_w1pVanishingOnSubmodule hp hU
    hb hug
  rw [map_sub] at h0
  filter_upwards [h0, ae_restrict_of_ae (Lp.coeFn_sub
    (W1p.frontierTraceOfIsLipschitzDomain (mu := mu) hp hU hb u)
    (W1p.frontierTraceOfIsLipschitzDomain (mu := mu) hp hU hb g))] with y h1 h2
  rwa [h2, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h1

/-- **The Poincaré–Friedrichs inequality on a Lipschitz domain of a Euclidean space.** Let `U` be
a bounded connected open subset of a finite-dimensional real inner product space `F` satisfying
the Lipschitz-domain condition, let `1 ≤ p < ∞`, and let `Γ'` meet the frontier of `U` in a set of
positive `(dim F - 1)`-dimensional surface measure. Then there is a constant `C` with
`‖u‖_{Lᵖ(U)} ≤ C ‖∇u‖_{Lᵖ(U)}` for every `u ∈ W^{1,p}_{Γ'}(U)`. -/
theorem
    W1p.exists_norm_value_le_mul_norm_gradient_of_mem_w1pVanishingOnSubmodule_of_isLipschitzDomain
    (hp : p ≠ (∞ : ℝ≥0∞)) (hU : (U : Set F).IsLipschitzDomain E')
    (hb : Bornology.IsBounded (U : Set F)) (hconn : IsPreconnected (U : Set F))
    (hΓ : (μHE[finrank ℝ F - 1] : Measure F) (Γ' ∩ frontier (U : Set F)) ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ w1pVanishingOnSubmodule volume U p Γ',
      ‖W1p.value u‖ ≤ C * ‖W1p.gradient u‖ := by
  -- `Γ'` charges the frontier, so the frontier is nonempty and `U` has a boundary chart `g`.
  have hne : (frontier (U : Set F)).Nonempty := by
    by_contra h
    simp [not_nonempty_iff_eq_empty.1 h] at hΓ
  obtain ⟨g, L, hL⟩ := hU.exists_isLipschitzDomainWith_image hb hne
  -- Give `E'` the inner product, finite dimension and Borel structure of its image in `F`.
  let e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E') := g.linearIsometryEquiv
  let _ : InnerProductSpace ℝ E' := .ofLinearIsometry e.symmInr
  have _ : FiniteDimensional ℝ E' := e.finiteDimensional_snd
  let _ : MeasurableSpace E' := borel E'
  have _ : BorelSpace E' := ⟨rfl⟩
  have hdim : finrank ℝ E' = finrank ℝ F - 1 := by
    rw [e.toLinearEquiv.finrank_eq, (WithLp.linearEquiv 2 ℝ (ℝ × E')).finrank_eq,
      Module.finrank_prod, Module.finrank_self]
    omega
  -- `g` carries `U` onto a bounded Lipschitz domain of the model space.
  let W : Opens (WithLp 2 (ℝ × E')) :=
    ⟨g '' (U : Set F), ((isLipschitzDomainWith_iff _ _).1 hL).1⟩
  have hWU : (W : Set (WithLp 2 (ℝ × E'))) = g.symm ⁻¹' U :=
    g.toHomeomorph.image_eq_preimage_symm _
  rw [← hdim] at hΓ
  exact
    W1p.exists_norm_value_le_mul_norm_gradient_of_mem_w1pVanishingOnSubmodule_of_affineIsometryEquiv
      hp hL (g.lipschitzWith.isBounded_image hb) g hWU hconn hΓ

end Intrinsic

end TauCeti
