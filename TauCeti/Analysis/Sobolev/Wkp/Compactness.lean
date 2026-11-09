/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Analysis.Normed.Operator.Compact.Basic

/-!
# A componentwise compactness criterion for `W^{k+1,p}`

An operator into `W^{k+1,p}(Ω)` is compact as soon as its lower-order part in `W^{k,p}(Ω)` and its
highest weak-derivative field are compact. The graph norm of `W^{k+1,p}(Ω)` is bounded by the sum
of the norms of these two components, so the pair of component maps is an antilipschitz embedding
and total boundedness transfers back along it. No boundedness or boundary regularity of `Ω` is
used.

This is the induction step shared by the higher-order Rellich–Kondrachov theorems, both on
compactly contained subdomains and on bounded Lipschitz domains.

## Main declarations

* `TauCeti.Wkp.isCompactOperator_of_isCompactOperator_lowerOrderL_iteratedGradientL`: the
  componentwise compactness criterion.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open MeasureTheory TopologicalSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- An operator into `W^{k+1,p}` is compact as soon as its lower-order part and its highest
derivative field are compact, since the graph norm is controlled by these two components. -/
theorem isCompactOperator_of_isCompactOperator_lowerOrderL_iteratedGradientL
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (k : ℕ)
    (T : X →L[ℝ] Wkp mu Omega p (k + 1))
    (hlo : IsCompactOperator ((lowerOrderL k).comp T))
    (hD : IsCompactOperator ((iteratedGradientL k).comp T)) : IsCompactOperator T := by
  let J := (lowerOrderL (mu := mu) (Omega := Omega) (p := p) k).prod (iteratedGradientL k)
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
  apply (isCompactOperator_iff_totallyBounded_image_closedBall _ zero_lt_one).mpr
  apply (totallyBounded_image_iff (hj.isUniformInducing J.uniformContinuous)).mp
  simpa only [Set.image_image, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_comp, Function.comp_def] using
    hJT.totallyBounded_image_closedBall 1

end TauCeti.Wkp
