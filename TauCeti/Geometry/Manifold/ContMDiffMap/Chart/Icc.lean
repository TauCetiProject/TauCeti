/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp
public import TauCeti.Geometry.Manifold.Instances.Icc

/-!
# Interval-valued maps in the weak Whitney topology

A `C^n` map into a closed interval `[a, b]`, `a < b`, is determined by its composite with the
inclusion `[a, b] → ℝ` (`ContMDiffMap.subtypeValIcc`), and the weak Whitney topology sees nothing
beyond that composite: when the model space `E` of the source manifold is locally compact,
composition with the inclusion is an embedding of `C^n⟮I, M; 𝓡∂ 1, Icc a b⟯` into the space of real
`C^n` functions (`ContMDiffMap.isEmbedding_subtypeValIcc_comp`). So continuity of a family of
interval-valued maps can be checked on the real functions, where the linear structure is available.

## Main declarations

* `ContMDiffMap.isEmbedding_subtypeValIcc_comp`: composition with the inclusion `[a, b] → ℝ` is a
  topological embedding, for a locally compact source model.

The reason is that both preferred charts of the interval are affine functions of the real
coordinate, `x ↦ x - a` on `[a, b)` and `x ↦ b - x` on `(a, b]`, with sources cut out by an
inequality on the same affine function. So a chart derivative test on an interval-valued map is a
compact-open condition on the value and on one coordinate derivative of a real function, an
affine image of its composite with the inclusion.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  {a b : ℝ} [Fact (a < b)]

/-- The real coordinate `r ↦ r - a` or `r ↦ b - r` of the preferred chart of `[a, b]` at `y`. -/
private noncomputable def chartCoordIcc (y : Icc a b) : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯ :=
  ⟨fun r ↦ if (y : ℝ) < b then r - a else b - r, by
    split_ifs
    exacts [(contDiff_id.sub contDiff_const).contMDiff, (contDiff_const.sub contDiff_id).contMDiff]⟩

/-- The embedding of the real line as the coordinate line of `EuclideanSpace ℝ (Fin 1)`. -/
private noncomputable def toEuclideanFinOne : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 ↦ ℝ).symm.toContinuousLinearMap

/-- Both preferred charts of `[a, b]` are the coordinate `chartCoordIcc y`, as a point of the
model line. -/
private theorem extChartAt_Icc_eq (y p : Icc a b) :
    extChartAt (𝓡∂ 1) y p = toEuclideanFinOne (chartCoordIcc (n := n) y p) := by
  rw [TauCeti.extChartAt_Icc_apply]
  split_ifs with h <;> ext <;> simp [toEuclideanFinOne, chartCoordIcc, h, uniqueElim_const]

/-- The source of a preferred chart of `[a, b]` is cut out by its coordinate. -/
private theorem mem_extChartAt_Icc_source_iff_chartCoordIcc_lt (y p : Icc a b) :
    p ∈ (extChartAt (𝓡∂ 1) y).source ↔ chartCoordIcc (n := n) y p < b - a := by
  rw [TauCeti.mem_extChartAt_Icc_source_iff_apply_zero_lt, extChartAt_Icc_eq (n := n)]
  simp [toEuclideanFinOne]

/-- The coordinate `chartCoordIcc y` of the preferred chart at `y`, as a function on `[a, b]`. -/
private noncomputable def chartCoordValIcc (y : Icc a b) : C^n⟮𝓡∂ 1, Icc a b; 𝓘(ℝ), ℝ⟯ :=
  (chartCoordIcc y).comp subtypeValIcc

private theorem chartCoordValIcc_apply (y p : Icc a b) :
    chartCoordValIcc (n := n) y p = chartCoordIcc (n := n) y p := by
  rw [chartCoordValIcc, ContMDiffMap.comp_apply, coe_subtypeValIcc]

/-- A chart derivative test of an interval-valued map is a pair of compact-open conditions on
the value and on the `m`-th coordinate derivative of the real function `chartCoordIcc y ∘ f`. -/
private theorem mem_chartJetSet_Icc_iff {x : M} {y : Icc a b} {m : ℕ} (hm : m ≤ n)
    {K : Set (extChartAt I x).target} {V : Set (E [×m]→L[ℝ] EuclideanSpace ℝ (Fin 1))}
    (f : C^n⟮I, M; 𝓡∂ 1, Icc a b⟯) :
    f ∈ chartJetSet x y m K V ↔
      MapsTo (chartIteratedFDeriv ((chartCoordValIcc y).comp f) x 0 (by simp)) K {φ | φ 0 < b - a} ∧
        MapsTo (chartIteratedFDeriv ((chartCoordValIcc y).comp f) x m hm) K
          ((toEuclideanFinOne.compContinuousMultilinearMap :
            (E [×m]→L[ℝ] ℝ) → E [×m]→L[ℝ] EuclideanSpace ℝ (Fin 1)) ⁻¹' V) := by
  set w := (chartCoordValIcc (n := n) y).comp f
  -- The chart reading of `f` at `y` is the real function `w` placed on the model line.
  have hw : extChartAt (𝓡∂ 1) y ∘ f ∘ (extChartAt I x).symm =
      toEuclideanFinOne ∘ (w ∘ (extChartAt I x).symm) := by
    funext q
    simp only [w, Function.comp_apply, ContMDiffMap.comp_apply, chartCoordValIcc_apply,
      extChartAt_Icc_eq (n := n)]
  have hwc : ContDiffOn ℝ n (w ∘ (extChartAt I x).symm) (extChartAt I x).target :=
    (w.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt_symm x)).contDiffOn
  simp only [mem_chartJetSet, ← forall_and, MapsTo, mem_preimage, Set.mem_ofPred_eq]
  refine forall_congr' fun z ↦ imp_congr_right fun _ ↦ and_congr ?_ ?_
  · rw [mem_extChartAt_Icc_source_iff_chartCoordIcc_lt (n := n),
      chartIteratedFDeriv_self_target_apply,
      iteratedFDerivWithin_zero_apply, Function.comp_apply, ContMDiffMap.comp_apply,
      chartCoordValIcc_apply]
  · rw [hw, toEuclideanFinOne.iteratedFDerivWithin_comp_left (hwc z z.property)
      (uniqueDiffOn_extChartAt_target x) z.property hm, chartIteratedFDeriv_self_target_apply]

/-- **Interval-valued maps embed in real functions.** For `a < b` and a locally compact model
space `E` of the source manifold, composition with the inclusion `[a, b] → ℝ` is an embedding of
the weak Whitney space of `C^n` maps into `[a, b]` into that of real `C^n` functions. -/
theorem isEmbedding_subtypeValIcc_comp [LocallyCompactSpace E] :
    IsEmbedding fun f : C^n⟮I, M; 𝓡∂ 1, Icc a b⟯ ↦ (subtypeValIcc (n := n)).comp f := by
  set Φ := fun f : C^n⟮I, M; 𝓡∂ 1, Icc a b⟯ ↦ (subtypeValIcc (n := n)).comp f
  have hΦ : Continuous Φ :=
    continuous_comp_manifoldWeakWhitney.comp (continuous_const.prodMk continuous_id)
  refine ⟨isInducing_iff_nhds.mpr fun f₀ ↦ le_antisymm (hΦ.tendsto f₀).le_comap ?_,
    fun f g hfg ↦ ContMDiffMap.ext fun p ↦ Subtype.val_injective (by
      simpa only [Φ, ContMDiffMap.comp_apply, coe_subtypeValIcc] using congrArg (· p) hfg)⟩
  -- Along the filter pulled back from the real functions, every chart test of `f₀` eventually
  -- holds.
  refine tendsto_id'.mp (tendsto_manifoldWeakWhitney_iff.mpr fun x y m hm K hK V hV hf₀ ↦ ?_)
  set l := comap Φ (𝓝 (Φ f₀))
  have hassoc (f : C^n⟮I, M; 𝓡∂ 1, Icc a b⟯) :
      (chartCoordValIcc y).comp f = (chartCoordIcc y).comp (Φ f) :=
    ContMDiffMap.ext fun _ ↦ rfl
  have hw : Tendsto (fun f ↦ (chartCoordValIcc (n := n) y).comp f) l
      (𝓝 ((chartCoordValIcc y).comp f₀)) := by
    simp only [hassoc]
    exact ((continuous_comp_manifoldWeakWhitney.comp
      (continuous_const.prodMk continuous_id)).tendsto (Φ f₀)).comp tendsto_comap
  have hjet (k : ℕ) (hk : k ≤ n) := ((continuous_chartIteratedFDeriv x k hk).tendsto _).comp hw
  rw [mem_chartJetSet_Icc_iff hm] at hf₀
  have h₀ := (hjet 0 (by simp)).eventually ((ContinuousMap.isOpen_setOfPred_mapsTo hK
    (isOpen_lt (continuous_eval_const 0) continuous_const)).mem_nhds
      hf₀.1)
  have hm' := (hjet m hm).eventually ((ContinuousMap.isOpen_setOfPred_mapsTo hK
    (hV.preimage (ContinuousLinearMap.compContinuousMultilinearMapL ℝ _ _ _
      toEuclideanFinOne).continuous)).mem_nhds hf₀.2)
  filter_upwards [h₀, hm'] with f h₀ hm'
  exact (mem_chartJetSet_Icc_iff hm f).mpr ⟨h₀, hm'⟩

end ContMDiffMap
