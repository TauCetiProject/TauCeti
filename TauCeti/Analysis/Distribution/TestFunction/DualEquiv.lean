/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Distribution
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# Maps on vector-valued tests as operator-valued distributions

Let `F` be a finite-dimensional real normed space, `V` a real normed space and `Ω` an open subset
of a real normed space `E`. A continuous linear map `T` from the `F`-valued test functions
`𝓓^{n}(Ω, F)` to `V` determines the `F →L[ℝ] V`-valued distribution

`ψ ↦ (v ↦ T (ψ • v))`

on the real test functions `𝓓^{n}(Ω, ℝ)`. Conversely, writing an `F`-valued test function
componentwise in a basis `(bᵢ)` of `F`, as `φ = ∑ᵢ (bᵢ* ∘ φ) • bᵢ`, an `F →L[ℝ] V`-valued
distribution `S` determines the map `φ ↦ ∑ᵢ S (bᵢ* ∘ φ) bᵢ`, independently of the basis. These two
constructions are mutually inverse, and both are continuous for the topologies of uniform
convergence on compact sets of tests (`TestFunction.dualEquivDistribution`).

For `V = ℝ`, this identifies functionals on vector-valued tests, such as currents in a Euclidean
chart (where the tests are the differential forms, valued in alternating maps), with Mathlib's
dual-valued distributions `𝓓'^{n}(Ω, F →L[ℝ] ℝ)`. Statements about distributions, for instance a
constancy criterion for distributions all of whose derivatives vanish, thereby transfer
componentwise to functionals on vector-valued tests. The equivalence intertwines the derivatives on
both sides (`TestFunction.dualEquivDistribution_lineDeriv`) and sends integration against a locally
integrable field `G : E → F →L[ℝ] V` to the distribution of `G`
(`TestFunction.dualEquivDistribution_integralAgainstBilinCLM`).

## Main declarations

* `TestFunction.dualEquivDistribution`: the continuous linear equivalence between
  `𝓓^{n}(Ω, F) →L_c[ℝ] V` and `𝓓'^{n}(Ω, F →L[ℝ] V)`.
* `TestFunction.dualEquivDistribution_apply_apply` and
  `TestFunction.dualEquivDistribution_symm_apply_eq_sum`: its formula, and the formula of its
  inverse in an arbitrary basis of `F`.
* `TestFunction.dualEquivDistribution_lineDeriv`: compatibility with directional derivatives, and
  `TestFunction.lineDeriv_dualEquivDistribution_eq_zero`: a functional annihilating all
  derivatives `∂_v φ` gives a distribution with vanishing derivative along `v`.
* `TestFunction.dualEquivDistribution_integralAgainstBilinCLM` and
  `TestFunction.dualEquivDistribution_symm_ofFun`: compatibility with integration against a
  locally integrable function.

## References

* L. Schwartz, *Théorie des distributions à valeurs vectorielles I*, Ann. Inst. Fourier 7 (1957).
-/

public section

noncomputable section

namespace TestFunction

open TopologicalSpace ContinuousLinearMap MeasureTheory
open scoped Distributions CompactConvergenceCLM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ∞}

/-- The continuous linear map underlying `dualEquivDistribution`, written in the basis
`Module.finBasis ℝ F` so that each summand is visibly continuous. -/
private def toDistributionCLM :
    (𝓓^{n}(Ω, F) →L_c[ℝ] V) →L[ℝ] 𝓓'^{n}(Ω, F →L[ℝ] V) :=
  ∑ i, Distribution.mapCLM (smulRightL ℝ F V ((Module.finBasis ℝ F).coord i).toContinuousLinearMap)
    ∘L (postcompCLM (toSpanSingleton ℝ (Module.finBasis ℝ F i))).precompCompactConvergenceCLM V

private theorem toDistributionCLM_apply_apply (T : 𝓓^{n}(Ω, F) →L_c[ℝ] V)
    (ψ : 𝓓^{n}(Ω, ℝ)) (v : F) :
    toDistributionCLM T ψ v = T (postcompCLM (toSpanSingleton ℝ v) ψ) := by
  -- Expand `ψ • v` in the basis inside `T`, and use linearity of `T`.
  conv_rhs => rw [← sum_postcompCLM_toSpanSingleton_coord (Module.finBasis ℝ F)
    (postcompCLM (toSpanSingleton ℝ v) ψ)]
  simp only [postcompCLM_coord_postcompCLM_toSpanSingleton, map_smul, map_sum, toDistributionCLM,
    sum_apply, coe_comp, Function.comp_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Distribution.mapCLM_apply, smulRightL_apply_apply, smulRight_apply,
    LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
  -- The `simps` lemma of `precompCompactConvergenceCLM` returns a plain continuous linear map, so
  -- evaluating it through the `→L_c` type synonym is a definitional unfolding.
  rfl

/-- The continuous linear map underlying the inverse of `dualEquivDistribution`, written in the
basis `Module.finBasis ℝ F`. -/
private def ofDistributionCLM :
    𝓓'^{n}(Ω, F →L[ℝ] V) →L[ℝ] (𝓓^{n}(Ω, F) →L_c[ℝ] V) :=
  ∑ i, (postcompCLM ((Module.finBasis ℝ F).coord i).toContinuousLinearMap
      ).precompCompactConvergenceCLM V ∘L
    Distribution.mapCLM (apply ℝ V (Module.finBasis ℝ F i))

private theorem ofDistributionCLM_apply (S : 𝓓'^{n}(Ω, F →L[ℝ] V)) (φ : 𝓓^{n}(Ω, F)) :
    ofDistributionCLM S φ = ∑ i,
      S (postcompCLM ((Module.finBasis ℝ F).coord i).toContinuousLinearMap φ)
        (Module.finBasis ℝ F i) := by
  simp only [ofDistributionCLM, sum_apply, coe_comp, Function.comp_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- Evaluation of `precompCompactConvergenceCLM` through the `→L_c` type synonym, as in
  -- `toDistributionCLM_apply_apply`.
  change Distribution.mapCLM (apply ℝ V (Module.finBasis ℝ F i)) S
    (postcompCLM ((Module.finBasis ℝ F).coord i).toContinuousLinearMap φ) = _
  rw [Distribution.mapCLM_apply, apply_apply]

private theorem ofDistributionCLM_toDistributionCLM (T : 𝓓^{n}(Ω, F) →L_c[ℝ] V) :
    ofDistributionCLM (toDistributionCLM T) = T := by
  ext φ
  rw [ofDistributionCLM_apply]
  simp_rw [toDistributionCLM_apply_apply]
  rw [← map_sum, sum_postcompCLM_toSpanSingleton_coord]

private theorem toDistributionCLM_ofDistributionCLM (S : 𝓓'^{n}(Ω, F →L[ℝ] V)) :
    toDistributionCLM (ofDistributionCLM S) = S := by
  ext ψ v
  rw [toDistributionCLM_apply_apply, ofDistributionCLM_apply]
  conv_rhs => rw [← (Module.finBasis ℝ F).sum_repr v, map_sum]
  simp [postcompCLM_coord_postcompCLM_toSpanSingleton]

/-- **Maps on vector-valued tests are operator-valued distributions.** For a finite-dimensional
real normed space `F` and a real normed space `V`, the continuous linear maps from the `F`-valued
test functions on `Ω` to `V` correspond to the `F →L[ℝ] V`-valued distributions on `Ω`: a map `T`
corresponds to the distribution `ψ ↦ (v ↦ T (ψ • v))`. Both spaces carry the topology of uniform
convergence on compact sets, and the correspondence is a homeomorphism for these topologies. -/
def dualEquivDistribution : (𝓓^{n}(Ω, F) →L_c[ℝ] V) ≃L[ℝ] 𝓓'^{n}(Ω, F →L[ℝ] V) :=
  ContinuousLinearEquiv.equivOfInverse toDistributionCLM ofDistributionCLM
    ofDistributionCLM_toDistributionCLM toDistributionCLM_ofDistributionCLM

/-- The distribution attached to a continuous linear map `T` on `F`-valued tests evaluates a real
test function `ψ` at `v : F` as `T (ψ • v)`. -/
@[simp]
theorem dualEquivDistribution_apply_apply (T : 𝓓^{n}(Ω, F) →L_c[ℝ] V) (ψ : 𝓓^{n}(Ω, ℝ)) (v : F) :
    dualEquivDistribution T ψ v = T (postcompCLM (toSpanSingleton ℝ v) ψ) :=
  toDistributionCLM_apply_apply T ψ v

/-- The map on `F`-valued tests attached to an `F →L[ℝ] V`-valued distribution `S` evaluates the
test function `ψ • v` as `S ψ v`. -/
@[simp]
theorem dualEquivDistribution_symm_apply_postcompCLM (S : 𝓓'^{n}(Ω, F →L[ℝ] V))
    (ψ : 𝓓^{n}(Ω, ℝ)) (v : F) :
    dualEquivDistribution.symm S (postcompCLM (toSpanSingleton ℝ v) ψ) = S ψ v := by
  rw [← dualEquivDistribution_apply_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- The map on `F`-valued tests attached to an `F →L[ℝ] V`-valued distribution `S`, in an arbitrary
basis `b` of `F`: it sends `φ` to `∑ i, S (bᵢ* ∘ φ) bᵢ`, where `bᵢ*` are the coordinate functionals
of `b`. -/
theorem dualEquivDistribution_symm_apply_eq_sum {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ F)
    (S : 𝓓'^{n}(Ω, F →L[ℝ] V)) (φ : 𝓓^{n}(Ω, F)) :
    dualEquivDistribution.symm S φ =
      ∑ i, S (postcompCLM (b.coord i).toContinuousLinearMap φ) (b i) := by
  conv_lhs => rw [← sum_postcompCLM_toSpanSingleton_coord b φ]
  simp [map_sum]

/-- `dualEquivDistribution` intertwines the derivatives: the derivative `-T (∂_v ·)` of a continuous
linear map `T` on `F`-valued tests corresponds to the distributional derivative of the distribution
attached to `T`. -/
theorem dualEquivDistribution_lineDeriv {k : ℕ∞} (T : 𝓓^{k}(Ω, F) →L_c[ℝ] V) (v : E) :
    dualEquivDistribution (-(lineDerivCLM ℝ v : 𝓓^{n}(Ω, F) →L[ℝ] 𝓓^{k}(Ω, F)
      ).precompCompactConvergenceCLM V T) =
      Distribution.lineDerivCLM v (dualEquivDistribution T) := by
  ext ψ w
  rw [dualEquivDistribution_apply_apply, neg_apply, precompCompactConvergenceCLM_apply,
    Distribution.lineDerivCLM_apply, neg_apply, dualEquivDistribution_apply_apply]
  -- The left side is `-T (∂_v (ψ • w))`, with `T ∘SL ∂_v` applied by definition.
  exact congrArg (fun φ ↦ -T φ) (lineDerivCLM_postcompCLM _ v ψ)

/-- If a continuous linear map `T` on `F`-valued tests annihilates every derivative `∂_v φ` of a
test function, then the distribution attached to `T` has vanishing derivative along `v`. -/
theorem lineDeriv_dualEquivDistribution_eq_zero {k : ℕ∞} {T : 𝓓^{k}(Ω, F) →L_c[ℝ] V} {v : E}
    (hT : ∀ φ : 𝓓^{n}(Ω, F), T (lineDerivCLM ℝ v φ) = 0) :
    (Distribution.lineDerivCLM v (dualEquivDistribution T) : 𝓓'^{n}(Ω, F →L[ℝ] V)) = 0 := by
  rw [← dualEquivDistribution_lineDeriv, ← map_zero dualEquivDistribution]
  congr 1
  ext φ
  rw [neg_apply, precompCompactConvergenceCLM_apply]
  exact neg_eq_zero.mpr (hT φ)

variable [MeasurableSpace E] [OpensMeasurableSpace E]

/-- `dualEquivDistribution` sends integration against a field `G : E → F →L[ℝ] V`, the map
`φ ↦ ∫ x, G x (φ x) ∂μ`, to the distribution `Distribution.ofFun Ω G μ n` of `G`. Both sides vanish
when `G` is not locally integrable on `Ω`. -/
theorem dualEquivDistribution_integralAgainstBilinCLM (G : E → F →L[ℝ] V) (μ : Measure E) :
    dualEquivDistribution (toUniformConvergenceCLM _ V _
      (integralAgainstBilinCLM (apply ℝ V) μ G : 𝓓^{n}(Ω, F) →L[ℝ] V)) =
      Distribution.ofFun Ω G μ n := by
  by_cases hG : LocallyIntegrableOn G Ω μ
  · ext ψ v
    rw [dualEquivDistribution_apply_apply, toUniformConvergenceCLM_apply,
      integralAgainstBilinCLM_eq_integral hG,
      Distribution.ofFun_apply hG, integral_apply (ψ.integrable_smul hG)]
    simp
  · rw [integralAgainstBilinCLM_eq_zero hG, Distribution.ofFun_eq_zero hG]
    -- The zero map of `→L` is the zero of its `→L_c` type synonym.
    exact map_zero dualEquivDistribution

/-- The map on `F`-valued tests attached to the distribution of a field `G : E → F →L[ℝ] V` is
integration against `G`. -/
theorem dualEquivDistribution_symm_ofFun (G : E → F →L[ℝ] V) (μ : Measure E) :
    dualEquivDistribution.symm (Distribution.ofFun Ω G μ n) =
      toUniformConvergenceCLM _ V _
        (integralAgainstBilinCLM (apply ℝ V) μ G : 𝓓^{n}(Ω, F) →L[ℝ] V) := by
  rw [ContinuousLinearEquiv.symm_apply_eq, dualEquivDistribution_integralAgainstBilinCLM]

end TestFunction
