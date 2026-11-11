/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.RellichKondrachov
public import TauCeti.Analysis.Sobolev.W1p.CompactSupport
public import TauCeti.Analysis.Sobolev.W1p.Restriction
public import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Sobolev.W1p.InteriorMorrey
import TauCeti.Analysis.Sobolev.W1p.PreciseRepresentative
import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous
import TauCeti.MeasureTheory.Function.Lp.Subtype
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# Local Rellich compactness for first-order Sobolev functions

Restriction of the values of arbitrary `W^{1,p}(Ω)` functions to an open `V` with compact
closure inside `Ω` is compact into `Lᵖ(V)`, for every `1 ≤ p ≤ ∞`.
No boundary regularity or vanishing trace is required. For finite `p`, a smooth cutoff equal
to one near `closure V` turns each Sobolev function into a zero-boundary Sobolev function on
`Ω`, to which Rellich--Kondrachov applies on a bounded subdomain containing `closure V`.
At `p = ∞`, the precise representatives are uniformly bounded and locally equi-Lipschitz,
so Arzelà–Ascoli on the compact closure gives uniform compactness. This argument does not use
smooth density in the `W^{1,∞}` norm, which is false. This local compactness is used when
passing to limits in interior elliptic estimates and weak-solution arguments.

The global compactness theorem for zero-boundary functions is
`TauCeti.W1p0.isCompactOperator_valueL`.

## Reference

H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
Theorem 9.16 (Rellich--Kondrachov compact embedding on bounded C¹ domains).
The finite-exponent local statement follows by cutoff localization and the zero-boundary
theorem above. For the endpoint, see L. C. Evans, *Partial Differential Equations*,
2nd ed., §5.7 (compact embeddings).
-/

public section

noncomputable section

open Bornology MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Gradient InnerProductSpace BoundedContinuousFunction
open TauCeti.MeasureTheory

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega V : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- Compactness of the value restriction on a bounded ambient domain, by a smooth cutoff. -/
private theorem W1p.isCompactOperator_valueL_restrictL_of_isBounded (hp : p ≠ ∞)
    (hOmega : IsBounded (Omega : Set E))
    (hVc : IsCompact (closure (V : Set E)))
    (hVO : closure (V : Set E) ⊆ (Omega : Set E)) :
    IsCompactOperator
      ((W1p.valueL (mu := mu) (Omega := V) (p := p)).comp
        (W1p.restrictL (SetLike.coe_subset_coe.mp (Subset.trans subset_closure hVO)))) := by
  have hV : V ≤ Omega :=
    SetLike.coe_subset_coe.mp (Subset.trans subset_closure hVO)
  obtain ⟨psi, M, hpsi, _, hpsiOne, hcpt, hts, hM, hpsiM, hgradM⟩ :=
    hVc.exists_contDiff_cutoff_with_bounds Omega.isOpen hVO
  obtain ⟨cutoff, cutoff_apply⟩ := W1p.exists_clm_w1p0_apply_eq_contDiffSMul (mu := mu)
    (Omega := Omega) (p := p) hp hpsi hM (fun x _ => hpsiM x) (fun x _ => hgradM x) hcpt hts
  have hmeasure : mu.restrict (V : Set E) ≤ (1 : ENNReal) • mu.restrict (Omega : Set E) := by
    simpa only [one_smul] using Measure.restrict_mono_set mu
      (SetLike.coe_subset_coe.mpr hV)
  let res : Lp ℝ p (mu.restrict (Omega : Set E)) →L[ℝ] Lp ℝ p (mu.restrict (V : Set E)) :=
    Lp.LpToLpOfMeasureLeSMul (by simp) hmeasure
  have hcompact : IsCompactOperator
      ((res.comp (W1p0.valueL (mu := mu) (Omega := Omega) (p := p))).comp cutoff) :=
    ((W1p0.isCompactOperator_valueL hp hOmega).clm_comp res).comp_clm cutoff
  have hOne : ∀ x ∈ (V : Set E), psi x = 1 := fun x hx =>
    interior_subset (s := psi ⁻¹' {1}) (hpsiOne (subset_closure hx))
  rw [W1p.valueL_comp_restrictL_eq_comp_cutoff hV hpsi hM (fun x _ => hpsiM x)
    (fun x _ => hgradM x) hOne cutoff cutoff_apply res
    (fun f => Lp.coeFn_LpToLpOfMeasureLeSMul (by simp) hmeasure f)]
  exact hcompact

/-- The restrictions to a compact subset of `Ω` of the precise representatives in the unit
ball of `W^{1,∞}(Ω)` have compact closure in the uniform norm. -/
private theorem W1p.isCompact_closure_preciseRepresentative_unitBall
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ (Omega : Set E)) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ∃ f : W1p mu Omega ∞ → K →ᵇ ℝ,
      (∀ u x, f u x = preciseRepresentative mu (W1p.value u) x) ∧
      IsCompact (closure (f '' closedBall 0 1)) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : W1p mu Omega ∞ → K →ᵇ ℝ := fun u =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x => preciseRepresentative mu (W1p.value u) x, by
        have hc := W1p.continuousOn_preciseRepresentative (ENNReal.natCast_lt_top _) u
        exact hc.comp_continuous continuous_subtype_val (fun x => hKΩ x.2)⟩
  refine ⟨f, fun _ _ => rfl, ?_⟩
  obtain ⟨C, hC, hdist⟩ := W1p.exists_dist_preciseRepresentative_le_top (mu := mu)
  obtain ⟨R, hR, hRK⟩ := hK.exists_cthickening_subset_open Omega.isOpen hKΩ
  refine BoundedContinuousFunction.arzela_ascoli (closedBall 0 1)
    (isCompact_closedBall 0 1) _ ?_ ?_
  · rintro _ x ⟨u, hu, rfl⟩
    exact mem_closedBall_zero_iff.2 ((W1p.norm_preciseRepresentative_le u (hKΩ x.2)).trans
      ((W1p.norm_value_le u).trans (mem_closedBall_zero_iff.1 hu)))
  · intro x
    refine equicontinuousAt_of_continuity_modulus (fun y : K => C * dist y x)
      (by
        have hc : Continuous (fun y : K => C * dist y x) := by fun_prop
        simpa using hc.tendsto x)
      _ ?_
    -- For distances below `R / 2`, the local estimate stays inside the fixed thickening of `K`.
    filter_upwards [Metric.ball_mem_nhds x (half_pos hR)] with y hy
    rintro ⟨_, u, hu, rfl⟩
    have hb := mem_closedBall_zero_iff.1 hu
    have hxy : closedBall (y : E) (2 * dist (y : E) x) ⊆ (Omega : Set E) :=
      ((closedBall_subset_cthickening y.2 _).trans
        (cthickening_mono (by
          have hd := mem_ball.1 hy
          rw [Subtype.dist_eq] at hd
          linarith) K)).trans hRK
    rw [dist_comm]
    refine (hdist u hxy).trans ?_
    have hg : ‖W1p.gradient u‖ ≤ 1 := (W1p.norm_gradient_le u).trans hb
    simpa only [Subtype.dist_eq] using mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right hC.le hg) (dist_nonneg : 0 ≤ dist y x)

/-- The endpoint restriction is compact by Arzelà–Ascoli on the compact closure of `V`. -/
private theorem W1p.isCompactOperator_valueL_restrictL_top
    (hVc : IsCompact (closure (V : Set E))) (hVO : closure (V : Set E) ⊆ (Omega : Set E)) :
    IsCompactOperator ((W1p.valueL (mu := mu) (Omega := V) (p := ∞)).comp
      (W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hVO)))) := by
  have hVΩ : V ≤ Omega := SetLike.coe_subset_coe.mp (subset_closure.trans hVO)
  let K := closure (V : Set E)
  have hK : IsCompact K := hVc
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ν : Measure ↥(V : Set E) := mu.comap (Subtype.val : ↥(V : Set E) → E)
  let σ : C((V : Set E), K) := ⟨fun x => ⟨x, subset_closure x.2⟩,
    continuous_subtype_val.subtype_mk _⟩
  let e := Lp.comapSubtypeEquivₗᵢ (E := ℝ) (p := ∞) ℝ mu V.isOpen.measurableSet
  let S : (K →ᵇ ℝ) → Lp ℝ ∞ (mu.restrict (V : Set E)) := fun g =>
    e.symm (BoundedContinuousFunction.toLpTop ν ℝ (g.compContinuous σ))
  have hS : Continuous S := e.symm.continuous.comp
    ((BoundedContinuousFunction.toLpTop ν ℝ).continuous.comp
      (BoundedContinuousFunction.continuous_compContinuous σ))
  obtain ⟨f, hf, hc⟩ :=
    W1p.isCompact_closure_preciseRepresentative_unitBall (mu := mu) hK hVO
  refine (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).2
    ⟨closedBall 0 1, closedBall_mem_nhds _ zero_lt_one, S '' closure (f '' closedBall 0 1),
      hc.image hS, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨f u, subset_closure ⟨u, hu, rfl⟩, ?_⟩
  apply e.injective
  rw [ContinuousLinearMap.comp_apply, W1p.valueL_apply]
  dsimp only [S]
  rw [LinearIsometryEquiv.apply_symm_apply]
  -- Move to the subtype measure, where continuous functions map directly into `Lp`.
  apply Lp.ext
  have heq := W1p.ae_eq_preciseRepresentative u
  filter_upwards [Lp.coeFn_comapSubtypeEquivₗᵢ (𝕜 := ℝ) V.isOpen.measurableSet
      (W1p.value (W1p.restrictL hVΩ u)),
    (ae_restrict_iff_subtype V.isOpen.measurableSet).1
      (W1p.value_restrictL_ae hVΩ u),
    (ae_restrict_iff_subtype V.isOpen.measurableSet).1
      (heq.filter_mono (ae_mono (Measure.restrict_mono_set mu hVΩ))),
    BoundedContinuousFunction.coeFn_toLpTop ν (𝕜 := ℝ) ((f u).compContinuous σ)] with x hx hr hp ht
  simp only [BoundedContinuousFunction.compContinuous_apply, σ, ContinuousMap.coe_mk, hf] at ht
  exact ht.trans (hp.symm.trans (hr.symm.trans hx.symm))

/-- **Local Rellich--Kondrachov compactness.** If `V` has compact closure contained in `Ω` and
`1 ≤ p ≤ ∞`, restriction of values from `W^{1,p}(Ω)` to `Lᵖ(V)` is compact. Neither the
boundedness nor the boundary regularity of `Ω` is required. -/
theorem W1p.isCompactOperator_valueL_restrictL
    (hVc : IsCompact (closure (V : Set E)))
    (hVO : closure (V : Set E) ⊆ (Omega : Set E)) :
    IsCompactOperator
      ((W1p.valueL (mu := mu) (Omega := V) (p := p)).comp
        (W1p.restrictL (SetLike.coe_subset_coe.mp (Subset.trans subset_closure hVO)))) := by
  have hV : V ≤ Omega :=
    SetLike.coe_subset_coe.mp (Subset.trans subset_closure hVO)
  by_cases hp : p = ∞
  · subst p
    exact W1p.isCompactOperator_valueL_restrictL_top hVc hVO
  obtain ⟨R, hR⟩ := hVc.isBounded.subset_ball (0 : E)
  let U : Opens E := Omega ⊓ ⟨Metric.ball (0 : E) R, Metric.isOpen_ball⟩
  have hU : U ≤ Omega := inf_le_left
  have hUc : closure (V : Set E) ⊆ (U : Set E) := by
    intro x hx
    exact ⟨hVO hx, hR hx⟩
  have hVU : V ≤ U := SetLike.coe_subset_coe.mp (Subset.trans subset_closure hUc)
  have hUbdd : IsBounded (U : Set E) :=
    (Metric.isBounded_ball (x := (0 : E)) (r := R)).subset (fun x hx => hx.2)
  have hcompact := W1p.isCompactOperator_valueL_restrictL_of_isBounded
    (mu := mu) (Omega := U) (V := V) hp hUbdd hVc hUc
  have heq : (W1p.valueL (mu := mu) (Omega := V) (p := p)).comp (W1p.restrictL hV) =
      ((W1p.valueL (mu := mu) (Omega := V) (p := p)).comp
        (W1p.restrictL hVU)).comp (W1p.restrictL hU) := by
    ext u
    have hr : W1p.restrictL hV u =
        W1p.restrictL hVU (W1p.restrictL hU u) := by
      exact (W1p.restrictL_restrictL hU hVU u).symm
    simp only [ContinuousLinearMap.comp_apply, hr, Filter.EventuallyEq.rfl]
  rw [heq]
  exact hcompact.comp_clm (W1p.restrictL hU)

end TauCeti

end

end
