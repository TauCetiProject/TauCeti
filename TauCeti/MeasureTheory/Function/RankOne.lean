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
import Mathlib.MeasureTheory.Function.LpSpace.Basic
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
similarity factor or assert regularity of a solution. On a finite-dimensional complex normed
space, which need not carry an inner product, the operator is read in a Euclidean model, and an
`Lᵖ` field of real-linear coefficients still agrees along `u` with an `Lᵖ` field of
complex-linear ones (`MeasureTheory.MemLp.exists_memLp_clm_apply_eq`).

The hypotheses are strong measurability, including in infinite-dimensional spaces. Mere Borel
measurability is not silently converted into strong measurability without separability hypotheses.
The solution-dependent complex-linear replacement follows Step 2 of the proof of
McDuff–Salamon's Theorem 2.3.5; this module supplies its strong measurability and `Lᵖ` bounds.

On a finite-dimensional space without a chosen inner product, an auxiliary Euclidean structure
gives the same reduction for a pair of vector fields: if `y` vanishes wherever `x` does, a
strongly measurable family of linear maps carries `x` to `y`, with norm at most a constant times
`‖y‖ / ‖x‖` (`MeasureTheory.AEStronglyMeasurable.exists_clm_apply_eq`). A pointwise bound
`‖y‖ ≤ M ‖x‖`, as for the difference of two solutions of a nonlinear equation, thus makes the
coefficient bounded.

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
  convert (ContinuousLinearMap.smulRightL 𝕜 𝕜 𝕜 E F).aestronglyMeasurable_comp₂
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

namespace MeasureTheory.AEStronglyMeasurable

variable {𝕜 E F X : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [MeasurableSpace X]
  {μ : Measure X} {x : X → E} {y : X → F}

/-- **A measurable coefficient carrying one vector field to another.** On a finite-dimensional
space `E`, with no inner product assumed, if `y` vanishes wherever `x` does, then there is a
strongly measurable family of linear maps `C t : E → F` with `C t (x t) = y t` and
`‖C t‖ ≤ c ‖y t‖ / ‖x t‖`, for a constant `c` depending only on the norm of `E`. So a pointwise
bound `‖y‖ ≤ M ‖x‖` makes `C` bounded by `c M`. The coefficient is the normalized rank-one
operator for an auxiliary Euclidean structure on `E`. -/
theorem exists_clm_apply_eq (hy : AEStronglyMeasurable y μ) (hx : AEStronglyMeasurable x μ)
    (h0 : ∀ t, x t = 0 → y t = 0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ C : X → E →L[𝕜] F, AEStronglyMeasurable C μ ∧
      (∀ t, C t (x t) = y t) ∧ ∀ t, ‖C t‖ ≤ c * (‖y t‖ / ‖x t‖) := by
  -- Transport to a Euclidean model `T : E ≃ ℝⁿ`, where the rank-one operator is available.
  let T : E ≃L[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 E)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let Tl : E →L[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 E)) := T
  let Ti : EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 E)) →L[𝕜] E := T.symm
  refine ⟨‖Tl‖ * ‖Ti‖, by positivity,
    fun t ↦ (TauCeti.rankOneDivNormSq 𝕜 (y t) (T (x t))).comp Tl, ?_, fun t ↦ ?_, fun t ↦ ?_⟩
  · exact ((ContinuousLinearMap.compL 𝕜 E _ F).flip Tl).continuous.comp_aestronglyMeasurable
      (hy.rankOneDivNormSq (T.continuous.comp_aestronglyMeasurable hx))
  · by_cases hxt : x t = 0
    · simp [hxt, h0 t hxt]
    · exact TauCeti.rankOneDivNormSq_apply_self _ (by simpa using hxt)
  · by_cases hxt : x t = 0
    · simp [hxt]
    -- `‖x‖ ≤ ‖T⁻¹‖ ‖T x‖` converts the bound `‖y‖ / ‖T x‖` into one in terms of `‖x‖`.
    have hTx : 0 < ‖T (x t)‖ := norm_pos_iff.2 (by simpa using hxt)
    have hxle : ‖x t‖ ≤ ‖Ti‖ * ‖T (x t)‖ := by
      simpa [Ti] using Ti.le_opNorm (T (x t))
    have h1 : ‖y t‖ / ‖T (x t)‖ ≤ ‖Ti‖ * (‖y t‖ / ‖x t‖) := by
      rw [mul_div_assoc', div_le_div_iff₀ hTx (norm_pos_iff.2 hxt)]
      calc ‖y t‖ * ‖x t‖ ≤ ‖y t‖ * (‖Ti‖ * ‖T (x t)‖) := by gcongr
        _ = ‖Ti‖ * ‖y t‖ * ‖T (x t)‖ := by ring
    calc ‖(TauCeti.rankOneDivNormSq 𝕜 (y t) (T (x t))).comp Tl‖
        ≤ ‖TauCeti.rankOneDivNormSq 𝕜 (y t) (T (x t))‖ * ‖Tl‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖Ti‖ * (‖y t‖ / ‖x t‖) * ‖Tl‖ := by
          rw [TauCeti.norm_rankOneDivNormSq]
          gcongr
      _ = ‖Tl‖ * ‖Ti‖ * (‖y t‖ / ‖x t‖) := by ring

end MeasureTheory.AEStronglyMeasurable

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

namespace MeasureTheory

variable {V F X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [MeasurableSpace X] {μ : Measure X}
  {C : X → V →L[ℝ] F} {ξ : X → V} {p : ℝ≥0∞}

/-- **A complex-linear coefficient along a solution.** On a finite-dimensional complex normed
space `V`, an `Lᵖ` field `C` of real-linear maps agrees along a strongly measurable `ξ` with an
`Lᵖ` field `D` of complex-linear maps, `D x (ξ x) = C x (ξ x)`. For a linear isomorphism `e` of
`V` onto a Euclidean space, `D x` is the normalized rank-one map `w ↦ ‖e ξ‖⁻² ⟪e ξ, e w⟫ C ξ`. -/
theorem MemLp.exists_memLp_clm_apply_eq (hC : MemLp C p μ) (hξ : AEStronglyMeasurable ξ μ) :
    ∃ D : X → V →L[ℂ] F, MemLp D p μ ∧ ∀ x, D x (ξ x) = C x (ξ x) := by
  let e : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let L₁ : (V →L[ℝ] F) →L[ℝ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℝ] F :=
    (ContinuousLinearMap.compL ℝ _ V F).flip ((e.symm : _ →L[ℂ] V).restrictScalars ℝ)
  let L₂ : (EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℂ] F) →L[ℂ] V →L[ℂ] F :=
    (ContinuousLinearMap.compL ℂ V _ F).flip (e : V →L[ℂ] _)
  refine ⟨fun x ↦ L₂ (rankOneDivNormSq ℂ (L₁ (C x) (e (ξ x))) (e (ξ x))),
    L₂.comp_memLp' ((L₁.comp_memLp' hC).rankOneDivNormSq_apply
      (e.continuous.comp_aestronglyMeasurable hξ)), fun x ↦ ?_⟩
  have h := (L₁ (C x)).rankOneDivNormSq_apply_map (𝕜 := ℂ) (e (ξ x))
  simpa [L₁, L₂] using h

end MeasureTheory
