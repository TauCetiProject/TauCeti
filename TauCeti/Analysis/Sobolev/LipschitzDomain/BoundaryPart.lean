/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Frontier
public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart
import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov
import TauCeti.Analysis.Sobolev.W1p.BoundaryPart.ChangeOfVariables
import TauCeti.Analysis.Sobolev.W1p.BoundaryPart.Localization
import TauCeti.MeasureTheory.Function.Lp.Restriction

/-!
# Boundary parts of a Lipschitz domain and the Poincaré–Friedrichs inequality

Let `Ω ⊆ ℝ × E` be a bounded Lipschitz domain, `σ` normalized `dim E`-dimensional Euclidean
Hausdorff measure on `frontier Ω`, `T : W^{1,p}(Ω) → Lᵖ(frontier Ω, σ)` the trace operator
(`TauCeti.W1p.frontierTrace`), `1 ≤ p < ∞`, and `Γ` a set. This file proves four facts about the
space `W^{1,p}_Γ(Ω)` of Sobolev functions vanishing on `Γ` (`TauCeti.w1pVanishingOnSubmodule`).

* With no boundary part, nothing is imposed: `W^{1,p}_∅(Ω) = W^{1,p}(Ω)`, because restrictions of
  test functions on the whole space are dense in `W^{1,p}(Ω)`.
* Every `u ∈ W^{1,p}_Γ(Ω)` has trace zero `σ`-almost everywhere on `Γ`. The generators vanish on
  `closure Γ` and are continuous up to the boundary, so their traces vanish there, and the trace is
  continuous. No regularity of `Γ` is used.
* Conversely, for `Γ` missing `Ω`, a function whose trace vanishes on `Γ` lies in `W^{1,p}_Γ(Ω)` as
  soon as it does so near each point of `closure Γ ∩ closure (frontier Ω \ Γ)`, the relative
  boundary of `Γ` in the frontier, where the Dirichlet and Neumann parts meet. Membership in
  `W^{1,p}_Γ(Ω)` is local (`TauCeti.mem_w1pVanishingOnSubmodule_of_forall_mem_closure`); away from
  `closure Γ` a cutoff product lies in `W^{1,p}_Γ(Ω)` by density, and near a point around which
  the frontier lies in `Γ` it has zero trace, so it lies in `W^{1,p}_0(Ω)`. In particular the trace
  characterization `W^{1,p}_Γ(Ω) = {u | T u = 0 on Γ}` holds when `closure Γ` and
  `closure (frontier Ω \ Γ)` are disjoint.
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

## Main declarations

* `TauCeti.w1pVanishingOnSubmodule_empty_of_isLipschitzDomainWith`: `W^{1,p}_∅(Ω) = W^{1,p}(Ω)`.
* `TauCeti.W1p.frontierTrace_ae_eq_zero_of_mem_w1pVanishingOnSubmodule`: functions in
  `W^{1,p}_Γ(Ω)` have zero trace on `Γ`.
* `TauCeti.W1p.mem_w1pVanishingOnSubmodule_of_frontierTrace_ae_eq_zero`: the converse reduced to
  neighbourhoods of the relative boundary of `Γ`, and
  `TauCeti.W1p.mem_w1pVanishingOnSubmodule_iff_frontierTrace_ae_eq_zero_of_disjoint_closure`: the
  trace characterization when that relative boundary is empty.
* `TauCeti.W1p.exists_norm_value_le_mul_norm_gradient_of_mem_w1pVanishingOnSubmodule`: the
  Poincaré–Friedrichs inequality on `W^{1,p}_Γ(Ω)`, and its form
  `W1p.exists_norm_value_le_mul_norm_gradient_of_mem_w1pVanishingOnSubmodule_of_affineIsometryEquiv`
  on an open set carried onto `Ω` by an affine isometry, such as a domain in `EuclideanSpace ℝ ι`.

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
open scoped ENNReal NNReal Distributions Gradient ContDiff Topology

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

/-! ### The trace characterization away from the relative boundary of `Γ`

The trace characterization `W^{1,p}_Γ(Ω) = {u | T u = 0 on Γ}` is local. Away from `closure Γ`,
a cutoff product `ψ u` vanishes near `Γ` and lies in `W^{1,p}_Γ(Ω)` outright. Near a point of `Γ`
around which the frontier lies in `Γ`, the trace of `ψ u` is `ψ T u`, which vanishes on the whole
frontier, so `ψ u ∈ W^{1,p}_0(Ω)`. The only points where more is needed are those of
`closure Γ ∩ closure (frontier Ω \ Γ)`, the relative boundary of `Γ` in the frontier, where the
Dirichlet and Neumann parts meet. -/

/-- **Cutoffs supported away from `closure Γ`.** On a bounded Lipschitz domain and for `p < ∞`,
if the support of `ψ` misses `closure Γ`, then `ψ u ∈ W^{1,p}_Γ(Ω)` for every `u ∈ W^{1,p}(Ω)`. -/
theorem W1p.contDiffSMul_mem_w1pVanishingOnSubmodule_of_disjoint (hp : p ≠ (∞ : ℝ≥0∞))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    {ψ : WithLp 2 (ℝ × E) → ℝ} {M : ℝ} (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hψΓ : Disjoint (tsupport ψ) (closure Γ)) (u : W1p volume Ω p) :
    W1p.contDiffSMul ψ hψ hM hψM hgM u ∈ w1pVanishingOnSubmodule volume Ω p Γ := by
  have hu : u ∈ w1pVanishingOnSubmodule volume Ω p ∅ := by
    rw [w1pVanishingOnSubmodule_empty_of_isLipschitzDomainWith hp hΩ hb]
    exact ClosedSubmodule.mem_top
  simpa only [empty_union] using
    W1p.contDiffSMul_mem_w1pVanishingOnSubmodule_union hψ hM hψM hgM hψΓ hu

/-- **Cutoffs supported where the frontier lies in `Γ`.** On a bounded Lipschitz domain and for
`p < ∞`, let `Γ` miss `Ω` and let the trace of `u` vanish almost everywhere on `Γ`. If every
frontier point in the support of `ψ` lies in `Γ`, then `ψ u ∈ W^{1,p}_0(Ω) ⊆ W^{1,p}_Γ(Ω)`. -/
theorem W1p.contDiffSMul_mem_w1pVanishingOnSubmodule_of_frontierTrace_ae_eq_zero
    (hp : p ≠ (∞ : ℝ≥0∞)) (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    (hΓΩ : Disjoint Γ (Ω : Set (WithLp 2 (ℝ × E))))
    {ψ : WithLp 2 (ℝ × E) → ℝ} {M : ℝ} (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hψΓ : frontier (Ω : Set (WithLp 2 (ℝ × E))) ∩ tsupport ψ ⊆ Γ) {u : W1p volume Ω p}
    (hu : W1p.frontierTrace hp hΩ hb u =ᵐ[((μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E))))).restrict Γ] 0) :
    W1p.contDiffSMul ψ hψ hM hψM hgM u ∈ w1pVanishingOnSubmodule volume Ω p Γ := by
  refine w1p0Submodule_le_w1pVanishingOnSubmodule hΓΩ ?_
  rw [W1p.mem_w1p0Submodule_iff_frontierTrace_eq_zero hp hΩ hb, Lp.eq_zero_iff_ae_eq_zero]
  -- The trace of `u` vanishes at almost every frontier point of the support of `ψ`.
  have hS : MeasurableSet (frontier (Ω : Set (WithLp 2 (ℝ × E))) ∩ tsupport ψ) :=
    isClosed_frontier.measurableSet.inter (isClosed_tsupport ψ).measurableSet
  have hu' : ∀ᵐ x ∂(μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      x ∈ frontier (Ω : Set (WithLp 2 (ℝ × E))) ∩ tsupport ψ →
        W1p.frontierTrace hp hΩ hb u x = 0 := by
    rw [Measure.restrict_restrict' isClosed_frontier.measurableSet] at hu
    exact (ae_restrict_iff' hS).1
      (ae_restrict_of_ae_restrict_of_subset (subset_inter hψΓ inter_subset_left) hu)
  -- So the trace `ψ T u` of `ψ u` vanishes almost everywhere on the frontier.
  filter_upwards [W1p.frontierTrace_contDiffSMul_ae hp hΩ hb hψ hM hψM hgM u,
    ae_restrict_of_ae hu', ae_restrict_mem isClosed_frontier.measurableSet] with x hx hux hxF
  rw [hx, Pi.zero_apply]
  by_cases hxψ : x ∈ tsupport ψ
  · rw [hux ⟨hxF, hxψ⟩, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hxψ, zero_mul]

/-- **Reduction of the trace characterization to the relative boundary of `Γ`.** On a bounded
Lipschitz domain and for `p < ∞`, let `Γ` miss `Ω` and let the trace of `u ∈ W^{1,p}(Ω)` vanish
almost everywhere on `Γ`. Suppose that every point of `closure Γ ∩ closure (frontier Ω \ Γ)` has
a neighbourhood `U` such that `ψ u ∈ W^{1,p}_Γ(Ω)` for every smooth `ψ` bounded together with its
gradient on `Ω` and supported in `U`. Then `u ∈ W^{1,p}_Γ(Ω)`. -/
theorem W1p.mem_w1pVanishingOnSubmodule_of_frontierTrace_ae_eq_zero (hp : p ≠ (∞ : ℝ≥0∞))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    (hΓΩ : Disjoint Γ (Ω : Set (WithLp 2 (ℝ × E)))) {u : W1p volume Ω p}
    (hu : W1p.frontierTrace hp hΩ hb u =ᵐ[((μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E))))).restrict Γ] 0)
    (hloc : ∀ x ∈ closure Γ ∩ closure (frontier (Ω : Set (WithLp 2 (ℝ × E))) \ Γ), ∃ U ∈ 𝓝 x,
      ∀ (ψ : WithLp 2 (ℝ × E) → ℝ) (hψ : ContDiff ℝ ∞ ψ) {M : ℝ} (hM : 0 ≤ M)
        (hψM : ∀ y ∈ Ω, |ψ y| ≤ M) (hgM : ∀ y ∈ Ω, ‖∇ ψ y‖ ≤ M), tsupport ψ ⊆ U →
          W1p.contDiffSMul ψ hψ hM hψM hgM u ∈ w1pVanishingOnSubmodule volume Ω p Γ) :
    u ∈ w1pVanishingOnSubmodule volume Ω p Γ := by
  refine mem_w1pVanishingOnSubmodule_of_forall_mem_closure hb fun x _ => ?_
  by_cases hxΓ : x ∈ closure Γ
  · by_cases hxF : x ∈ closure (frontier (Ω : Set (WithLp 2 (ℝ × E))) \ Γ)
    · exact hloc x ⟨hxΓ, hxF⟩
    -- Near `x` every frontier point lies in `Γ`.
    refine ⟨(closure (frontier (Ω : Set (WithLp 2 (ℝ × E))) \ Γ))ᶜ,
      isClosed_closure.isOpen_compl.mem_nhds hxF, fun ψ hψ M hM hψM hgM hψU => ?_⟩
    refine W1p.contDiffSMul_mem_w1pVanishingOnSubmodule_of_frontierTrace_ae_eq_zero hp hΩ hb hΓΩ
      hψ hM hψM hgM (fun y hy => ?_) hu
    by_contra hyΓ
    exact hψU hy.2 (subset_closure ⟨hy.1, hyΓ⟩)
  -- Near `x` there is no point of `closure Γ`.
  exact ⟨(closure Γ)ᶜ, isClosed_closure.isOpen_compl.mem_nhds hxΓ,
    fun ψ hψ M hM hψM hgM hψU => W1p.contDiffSMul_mem_w1pVanishingOnSubmodule_of_disjoint hp hΩ
      hb hψ hM hψM hgM (subset_compl_iff_disjoint_right.1 hψU) u⟩

/-- **The trace characterization for a boundary part that is closed and open in the frontier.**
On a bounded Lipschitz domain and for `p < ∞`, let `Γ` miss `Ω`, and let `closure Γ` be disjoint
from `closure (frontier Ω \ Γ)`, as happens when `Γ` is closed and open in the frontier, such as
one of the two boundary spheres of an annulus. Then `u ∈ W^{1,p}(Ω)` lies in `W^{1,p}_Γ(Ω)`
exactly when its trace vanishes almost everywhere on `Γ`. -/
theorem W1p.mem_w1pVanishingOnSubmodule_iff_frontierTrace_ae_eq_zero_of_disjoint_closure
    (hp : p ≠ (∞ : ℝ≥0∞)) (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    (hΓΩ : Disjoint Γ (Ω : Set (WithLp 2 (ℝ × E))))
    (hΓ : Disjoint (closure Γ) (closure (frontier (Ω : Set (WithLp 2 (ℝ × E))) \ Γ)))
    (u : W1p volume Ω p) :
    u ∈ w1pVanishingOnSubmodule volume Ω p Γ ↔
      W1p.frontierTrace hp hΩ hb u =ᵐ[((μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E))))).restrict Γ] 0 :=
  ⟨W1p.frontierTrace_ae_eq_zero_of_mem_w1pVanishingOnSubmodule hp hΩ hb, fun hu =>
    W1p.mem_w1pVanishingOnSubmodule_of_frontierTrace_ae_eq_zero hp hΩ hb hΓΩ hu
      fun x hx => absurd hx (disjoint_iff_inter_eq_empty.1 hΓ ▸ notMem_empty x)⟩

end TauCeti
