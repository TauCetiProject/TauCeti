/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.RankOne
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Measurable rank-one coefficient reduction

The normalized rank-one operator is strongly measurable when its input and output vectors are.
This remains true when the input vector vanishes: total scalar inversion is Borel measurable,
and no regularity or isolation assumption on the zero set is needed.

For a strongly measurable family of coefficients `C`, linear over an independent normed field,
and vectors `u`, the
operator `rankOneDivNormSq 𝕜 (C u) u` is `𝕜`-linear, agrees with `C` on `u`, and has operator norm
at most `‖C‖`. Thus every `Lᵖ` coefficient bound transfers, with the same seminorm bound, to this
new coefficient. In the complex case this is the solution-dependent absorption of a real-linear
zeroth-order coefficient used in the vector similarity principle. It does not construct a
similarity factor or assert regularity of a solution.

On a finite-dimensional complex normed space, with no inner product of its own, the same
absorption holds up to a constant depending only on the space
(`TauCeti.exists_complexLinear_apply_eq`): the rank-one map is taken for the inner product
transported from a Euclidean space.

The hypotheses are strong measurability, including in infinite-dimensional spaces. Mere Borel
measurability is not silently converted into strong measurability without separability hypotheses.
The solution-dependent complex-linear replacement follows Step 2 of the proof of
McDuff–Salamon's Theorem 2.3.5; this module supplies its strong measurability and `Lᵖ` bounds.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5, proof, Step 2 (coefficient reduction).
-/

public noncomputable section

open InnerProductSpace TauCeti
open scoped ENNReal

namespace MeasureTheory

variable {𝕜 E F X : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [MeasurableSpace X] {μ : Measure X}
  {x : X → E} {y : X → F}

/-- The native rank-one operator is strongly measurable in its two vector arguments. -/
theorem AEStronglyMeasurable.rankOne (hy : AEStronglyMeasurable y μ)
    (hx : AEStronglyMeasurable x μ) :
    AEStronglyMeasurable (fun t => InnerProductSpace.rankOne 𝕜 (y t) (x t)) μ := by
  convert (ContinuousLinearMap.smulRightL 𝕜 E F).aestronglyMeasurable_comp₂
    ((innerSL 𝕜).continuous.comp_aestronglyMeasurable hx) hy using 1
  funext t
  ext v
  simp

/-- Strong measurability of normalized rank-one operators, including zeros of the input vector. -/
theorem AEStronglyMeasurable.rankOneDivNormSq (hy : AEStronglyMeasurable y μ)
    (hx : AEStronglyMeasurable x μ) :
    AEStronglyMeasurable (fun t => TauCeti.rankOneDivNormSq 𝕜 (y t) (x t)) μ := by
  have hs : AEStronglyMeasurable (fun t => ((‖x t‖ : 𝕜) ^ 2)⁻¹) μ :=
    ((RCLike.continuous_ofReal.comp_aestronglyMeasurable hx.norm).pow 2).inv₀
  have hr : AEStronglyMeasurable (fun t => InnerProductSpace.rankOne 𝕜 (y t) (x t)) μ :=
    hy.rankOne hx
  convert hs.smul hr using 1
  funext t
  exact rankOneDivNormSq_def (y t) (x t)

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' E]
  [NormedSpace 𝕜' F] {C : X → E →L[𝕜'] F} {p : ℝ≥0∞}

/-- A strongly measurable linear coefficient and solution give a strongly measurable
`𝕜`-linear coefficient matching the original one along the solution. -/
theorem AEStronglyMeasurable.rankOneDivNormSq_apply
    (hC : AEStronglyMeasurable C μ) (hx : AEStronglyMeasurable x μ) :
    AEStronglyMeasurable (fun t => TauCeti.rankOneDivNormSq 𝕜 (C t (x t)) (x t)) μ :=
  (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hC hx).rankOneDivNormSq hx

/-- The coefficient reduction preserves every `Lᵖ` bound, with no finite-dimensional or
nonvanishing assumption on the solution. -/
theorem MemLp.rankOneDivNormSq_apply (hC : MemLp C p μ) (hx : AEStronglyMeasurable x μ) :
    MemLp (fun t => TauCeti.rankOneDivNormSq 𝕜 (C t (x t)) (x t)) p μ :=
  hC.of_le (hC.aestronglyMeasurable.rankOneDivNormSq_apply hx)
    (Filter.Eventually.of_forall fun t => (C t).norm_rankOneDivNormSq_map_le (x t))

end MeasureTheory

namespace TauCeti.MeasureTheory

open _root_.MeasureTheory

variable {𝕜 𝕜' E F X : Type*} [RCLike 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedSpace 𝕜' E] [NormedSpace 𝕜' F]
  [MeasurableSpace X] {μ : Measure X} {C : X → E →L[𝕜'] F} {x : X → E}

/-- The operator-valued `Lᵖ` seminorm cannot increase under the coefficient reduction. -/
theorem eLpNorm_rankOneDivNormSq_apply_le
    (hC : AEStronglyMeasurable C μ)
    (hx : AEStronglyMeasurable x μ) (p : ℝ≥0∞) :
    eLpNorm (fun t => TauCeti.rankOneDivNormSq 𝕜 (C t (x t)) (x t)) p μ ≤ eLpNorm C p μ :=
  eLpNorm_mono_ae (hC.rankOneDivNormSq_apply hx)
    (Filter.Eventually.of_forall fun t => (C t).norm_rankOneDivNormSq_map_le (x t))

end TauCeti.MeasureTheory

namespace TauCeti

open _root_.MeasureTheory

variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V]

variable (X V) in
/-- **A complex-linear coefficient along a solution.** For every map `ξ` and every field `C` of
real-linear endomorphisms of a finite-dimensional complex normed space `V`, there is a field `D`
of complex-linear maps with `D ξ = C ξ` and `‖D‖ ≤ K ‖C‖`, strongly measurable when `C` and `ξ`
are, with a constant `K` depending only on `V`. It is a rank-one map for the inner product
transported from a Euclidean space. -/
theorem exists_complexLinear_apply_eq :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ξ : X → V) (C : X → V →L[ℝ] V), ∃ D : X → V →L[ℂ] V,
      (∀ x, D x (ξ x) = C x (ξ x)) ∧ (∀ x, ‖D x‖ ≤ K * ‖C x‖) ∧
      ∀ μ : Measure X, AEStronglyMeasurable C μ → AEStronglyMeasurable ξ μ →
        AEStronglyMeasurable D μ := by
  let E := EuclideanSpace ℂ (Fin (Module.finrank ℂ V))
  let e : V ≃L[ℂ] E := ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let eR : V →L[ℝ] E := (e : V →L[ℂ] E).restrictScalars ℝ
  let eR' : E →L[ℝ] V := (e.symm : E →L[ℂ] V).restrictScalars ℝ
  refine ⟨‖(e.symm : E →L[ℂ] V)‖ * (‖eR‖ * ‖eR'‖) * ‖(e : V →L[ℂ] E)‖, by positivity,
    fun ξ C ↦ ?_⟩
  let C' : X → E →L[ℝ] E := fun x ↦ eR ∘L C x ∘L eR'
  have hconj : Continuous fun A : E →L[ℂ] E ↦ (e.symm : E →L[ℂ] V) ∘L A ∘L (e : V →L[ℂ] E) :=
    continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  refine ⟨fun x ↦ (e.symm : E →L[ℂ] V) ∘L rankOneDivNormSq ℂ (C' x (e (ξ x))) (e (ξ x)) ∘L
    (e : V →L[ℂ] E), fun x ↦ ?_, fun x ↦ ?_, fun μ hC hξ ↦ ?_⟩
  · have h := (C' x).rankOneDivNormSq_apply_map (𝕜 := ℂ) (e (ξ x))
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [h]
    simp [C', eR, eR']
  · calc ‖(e.symm : E →L[ℂ] V) ∘L rankOneDivNormSq ℂ (C' x (e (ξ x))) (e (ξ x)) ∘L
          (e : V →L[ℂ] E)‖
        ≤ ‖(e.symm : E →L[ℂ] V)‖ * (‖rankOneDivNormSq ℂ (C' x (e (ξ x))) (e (ξ x))‖ *
          ‖(e : V →L[ℂ] E)‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ ‖(e.symm : E →L[ℂ] V)‖ * ((‖eR‖ * (‖C x‖ * ‖eR'‖)) * ‖(e : V →L[ℂ] E)‖) := by
          gcongr
          refine ((C' x).norm_rankOneDivNormSq_map_le _).trans ?_
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _)
      _ = _ := by ring
  · have hC' : AEStronglyMeasurable C' μ :=
      (continuous_const.clm_comp
        (continuous_id.clm_comp continuous_const)).comp_aestronglyMeasurable hC
    exact hconj.comp_aestronglyMeasurable
      (hC'.rankOneDivNormSq_apply (𝕜 := ℂ) (e.continuous.comp_aestronglyMeasurable hξ))

end TauCeti
