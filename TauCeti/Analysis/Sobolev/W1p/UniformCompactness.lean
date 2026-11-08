/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.InteriorMorrey
public import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.Analysis.Sobolev.W1p.PreciseRepresentative
import TauCeti.MeasureTheory.Function.Lp.Subtype
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Uniform compactness of bounded Sobolev functions

Restriction from `W^{1,∞}(Ω)` to `L^∞(V)` is compact when `V` has compact closure inside `Ω`.
The precise representatives of a bounded Sobolev family are uniformly bounded and
locally equi-Lipschitz, so Arzelà–Ascoli on the compact closure gives uniform compactness.
No boundary regularity is needed for this restriction result. Combined with an extension
operator, it gives Rellich compactness up to the boundary of a bounded Lipschitz domain.

The proof uses the local Morrey estimate, including its endpoint exponent one; it does
not use smooth density in the `W^{1,∞}` norm, which is false.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.7 (compact embeddings).
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal BoundedContinuousFunction
open TauCeti.MeasureTheory

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]

/-- The restrictions to a compact subset of `Ω` of the precise representatives in the unit
ball of `W^{1,∞}(Ω)` have compact closure in the uniform norm. -/
private theorem W1p.isCompact_closure_preciseRepresentative_unitBall {Omega : Opens E}
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ (Omega : Set E)) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ∃ f : W1p mu Omega ∞ → K →ᵇ ℝ,
      (∀ u x, f u x = preciseRepresentative mu (W1p.value u) x) ∧
      IsCompact (closure (f '' closedBall 0 1)) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : W1p mu Omega ∞ → K →ᵇ ℝ := fun u =>
    ⟨⟨fun x => preciseRepresentative mu (W1p.value u) x,
      (by
        have hc := W1p.continuousOn_preciseRepresentative (ENNReal.natCast_lt_top _) u
        exact hc.comp_continuous continuous_subtype_val (fun x => hKΩ x.2))⟩,
      ⟨2 * ‖W1p.value u‖, fun x y => (dist_le_norm_add_norm _ _).trans
        (by linarith [W1p.norm_preciseRepresentative_le u (hKΩ x.2),
          W1p.norm_preciseRepresentative_le u (hKΩ y.2)])⟩⟩
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

/-- **Uniform Rellich compactness.** If `V` has compact closure contained in `Ω`, restriction
of `W^{1,∞}(Ω)` values to `L^∞(V)` is compact. No boundary regularity is required. -/
theorem W1p.isCompactOperator_valueL_restrictL_top {Omega V : Opens E}
    (hVc : IsCompact (closure (V : Set E))) (hVO : closure (V : Set E) ⊆ (Omega : Set E)) :
    IsCompactOperator ((W1p.valueL (mu := mu) (Omega := V) (p := ∞)).comp
      (W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hVO)))) := by
  have hV : Bornology.IsBounded (V : Set E) := hVc.isBounded.subset subset_closure
  have hVΩ : V ≤ Omega := SetLike.coe_subset_coe.mp (subset_closure.trans hVO)
  let K := closure (V : Set E)
  have hK : IsCompact K := hVc
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ν : Measure ↥(V : Set E) := mu.comap (Subtype.val : ↥(V : Set E) → E)
  let : IsFiniteMeasure (mu.restrict (V : Set E)) :=
    ⟨by simpa using hV.measure_lt_top⟩
  let : IsFiniteMeasure ν := ⟨by
    dsimp only [ν]
    rw [comap_subtype_coe_apply V.isOpen.measurableSet mu univ]
    simpa using hV.measure_lt_top⟩
  let σ : C((V : Set E), K) := ⟨fun x => ⟨x, subset_closure x.2⟩,
    continuous_subtype_val.subtype_mk _⟩
  let e := Lp.comapSubtypeEquivₗᵢ (E := ℝ) (p := ∞) ℝ mu V.isOpen.measurableSet
  let S : (K →ᵇ ℝ) → Lp ℝ ∞ (mu.restrict (V : Set E)) := fun g =>
    e.symm (BoundedContinuousFunction.toLp ∞ ν ℝ (g.compContinuous σ))
  have hS : Continuous S := e.symm.continuous.comp
    ((BoundedContinuousFunction.toLp ∞ ν ℝ).continuous.comp
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
    BoundedContinuousFunction.coeFn_toLp ∞ ν ℝ ((f u).compContinuous σ)] with x hx hr hp ht
  simp only [BoundedContinuousFunction.compContinuous_apply, σ, ContinuousMap.coe_mk, hf] at ht
  exact ht.trans (hp.symm.trans (hr.symm.trans hx.symm))

end TauCeti
