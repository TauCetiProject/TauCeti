/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Restriction
public import TauCeti.Analysis.Sobolev.GraphStep.LocalCompactness
public import TauCeti.Analysis.Normed.Operator.Compact.Basic

/-!
# Local Rellich compactness at every Sobolev order

Restriction to a relatively compact open subdomain, followed by forgetting one derivative,
is compact from `W^{k+1,p}` to `W^{k,p}` for every natural `k` and `1 ≤ p ≤ ∞`. Neither
boundedness nor boundary regularity of the ambient open domain is required.

The first-order theorem supplies compactness of the values. At every further graph step,
finite-dimensional vector-valued local Rellich supplies compactness of the highest retained
derivative field. The preceding Sobolev component is compact by induction. The native graph
topology combines the two, giving compactness in the full lower-order Sobolev norm.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 9.16; the higher-order local version follows by applying the first-order theorem
  to the weak derivative fields.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open Bornology Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega V : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

private theorem isCompactOperator_of_components {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] (k : ℕ)
    (T : X →L[ℝ] Wkp mu V p (k + 1))
    (hlo : IsCompactOperator ((lowerOrderL k).comp T))
    (hD : IsCompactOperator ((iteratedGradientL k).comp T)) : IsCompactOperator T := by
  let J := (lowerOrderL (mu := mu) (Omega := V) (p := p) k).prod (iteratedGradientL k)
  have hj : AntilipschitzWith 2 J := J.antilipschitz_of_bound fun u => by
    have h := norm_le_norm_lowerOrder_add_norm_iteratedGradient k u
    have hJu : J u = (lowerOrder k u, iteratedGradient k u) := by
      dsimp only [J]
      rw [ContinuousLinearMap.prod_apply, lowerOrderL_apply k u, iteratedGradientL_apply k u]
    have h₁ : ‖lowerOrder k u‖ ≤ ‖J u‖ := by
      rw [hJu, Prod.norm_def]
      exact le_max_left _ _
    have h₂ : ‖iteratedGradient k u‖ ≤ ‖J u‖ := by
      rw [hJu, Prod.norm_def]
      exact le_max_right _ _
    norm_num only [NNReal.coe_ofNat]
    linarith
  have hJT : IsCompactOperator (J.comp T) := by
    have heq : J.comp T =
        (ContinuousLinearMap.inl ℝ _ _).comp ((lowerOrderL k).comp T) +
          (ContinuousLinearMap.inr ℝ _ _).comp ((iteratedGradientL k).comp T) := by
      apply ContinuousLinearMap.ext
      intro u
      simp [J]
    rw [heq]
    simpa only [FunLike.coe_add, ContinuousLinearMap.coe_comp] using
      (hlo.clm_comp (ContinuousLinearMap.inl ℝ _ _)).add
        (hD.clm_comp (ContinuousLinearMap.inr ℝ _ _))
  apply isCompactOperator_of_totallyBounded_image_closedBall (r := 1) zero_lt_one
  apply (totallyBounded_image_iff (hj.isUniformInducing J.uniformContinuous)).mp
  simpa only [Set.image_image, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_comp, Function.comp_def] using
    hJT.totallyBounded_image_closedBall 1

/-- **Higher-order local Rellich compactness.** Restriction loses one derivative compactly
on every relatively compact open subdomain for every `1 ≤ p ≤ ∞`. -/
theorem isCompactOperator_restrictL_lowerOrderL
    (hVc : IsCompact (closure (V : Set E))) (hVO : closure (V : Set E) ⊆ Omega) :
    ∀ k : ℕ, IsCompactOperator
      ((restrictL (mu := mu) (p := p) (SetLike.coe_subset_coe.mp
        (subset_closure.trans hVO)) k).comp (lowerOrderL k)) := by
  let hV : V ≤ Omega := SetLike.coe_subset_coe.mp (subset_closure.trans hVO)
  intro k
  induction k with
  | zero =>
      have heq : (restrictL (mu := mu) (p := p) hV 0).comp (lowerOrderL 0) =
          (W1p.valueL (mu := mu) (Omega := V) (p := p)).comp (W1p.restrictL hV) := by
        apply ContinuousLinearMap.ext
        intro u
        have hright := ContinuousLinearMap.comp_apply
          (W1p.valueL (mu := mu) (Omega := V) (p := p)) (W1p.restrictL hV) u
        rw [W1p.valueL_apply (W1p.restrictL hV u)] at hright
        refine Eq.trans ?_ ((W1p.value_restrictL hV u).symm.trans hright.symm)
        rw [ContinuousLinearMap.comp_apply, lowerOrderL_apply 0 u, lowerOrder_zero u,
          restrictL_zero]
      rw [heq]
      exact W1p.isCompactOperator_valueL_restrictL hVc hVO
  | succ k ih =>
      let T := (restrictL (mu := mu) (p := p) hV (k + 1)).comp (lowerOrderL (k + 1))
      apply isCompactOperator_of_components k T
      · have heq : (lowerOrderL k).comp T =
            ((restrictL hV k).comp (lowerOrderL k)).comp (lowerOrderL (k + 1)) := by
          apply ContinuousLinearMap.ext
          intro u
          simp only [T, ContinuousLinearMap.comp_apply]
          rw [lowerOrderL_apply k (restrictL hV (k + 1) (lowerOrderL (k + 1) u)),
            lowerOrder_restrictL hV k (lowerOrderL (k + 1) u),
            lowerOrderL_apply k (lowerOrderL (k + 1) u)]
        rw [heq]
        exact ih.comp_clm _
      · let base := (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL
        have heq : (iteratedGradientL k).comp T =
            WeakDerivStep.restrictBaseL base hV := by
          apply ContinuousLinearMap.ext
          intro u
          apply Lp.ext
          simp only [ContinuousLinearMap.comp_apply, T]
          rw [lowerOrderL_apply (k + 1) u,
            iteratedGradientL_apply k (restrictL hV (k + 1) (lowerOrder (k + 1) u))]
          refine (iteratedGradient_restrictL_ae hV k (lowerOrder (k + 1) u)).trans ?_
          rw [iteratedGradient_eq_sobolevStage_iteratedGradientL k (lowerOrder (k + 1) u),
            lowerOrder_succ k u]
          exact (WeakDerivStep.restrictBaseL_apply_ae base hV u).symm
        rw [heq]
        exact WeakDerivStep.isCompactOperator_restrictBaseL base hVc hVO

/-- A bounded sequence in `W^{k+1,p}(Ω)` has a subsequence whose restrictions converge in the
actual `W^{k,p}(V)` norm on every fixed relatively compact open subdomain `V`. -/
theorem exists_subseq_tendsto_restrict_lowerOrder
    (hVc : IsCompact (closure (V : Set E))) (hVO : closure (V : Set E) ⊆ Omega)
    (k : ℕ) {u : ℕ → Wkp mu Omega p (k + 1)} {R : ℝ} (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ w : Wkp mu V p k, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hVO)) k
        (lowerOrder k (u (φ n)))) atTop (𝓝 w) := by
  obtain ⟨w, φ, hφ, hw⟩ :=
    (isCompactOperator_restrictL_lowerOrderL hVc hVO k).exists_subseq_tendsto hu
  refine ⟨w, φ, hφ, ?_⟩
  simpa only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    lowerOrderL_apply k (u (φ _))] using hw

end TauCeti.Wkp
