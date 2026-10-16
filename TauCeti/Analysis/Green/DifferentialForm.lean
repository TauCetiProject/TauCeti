/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Basic
public import TauCeti.Analysis.Green.WindingWeight.Basic
import TauCeti.Analysis.Green.Winding
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap

/-!
# Planar circulation as a manifold differential form

The real linear circulation form converts to the existing degree-one `RoughForm` on the
complex plane. Its manifold exterior derivative evaluates on the positive basis `(1,I)`
to the curl. Thus the AC Green area integral is the coordinate coefficient of the existing
manifold exterior derivative, and its boundary integral is the existing `curveIntegral`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Manifold

namespace TauCeti.Green

/-- The circulation form as an existing rough manifold differential form on the real plane. -/
def manifoldOneForm (P Q : ℂ → ℝ) : RoughForm 𝓘(ℝ, ℂ) ℂ ℝ 1 :=
  fun z ↦ ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace 𝓘(ℝ, ℂ) z) ℝ
    (0 : Fin 1) ((oneForm P Q z).comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap)

/-- Evaluation of the manifold form is evaluation of the real linear circulation form. -/
@[simp]
theorem manifoldOneForm_apply (P Q : ℂ → ℝ) (z : ℂ)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z) :
    manifoldOneForm P Q z v = oneForm P Q z (NormedSpace.fromTangentSpace z (v 0)) := (rfl)

/-- In the plane's canonical chart, the manifold form is the alternating-map encoding of
the circulation form. -/
-- This rule must precede inChartAt_modelSpace, which erases the chart expression
-- before simp can expose the circulation form's alternating-map encoding.
@[simp high]
theorem manifoldOneForm_inChartAt (P Q : ℂ → ℝ) (c : ℂ) :
    (manifoldOneForm P Q).inChartAt c = fun z ↦
      ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℝ (0 : Fin 1) (oneForm P Q z) := by
  rw [RoughForm.inChartAt_modelSpace]
  rfl

/-- Real differentiability of the two coefficients implies differentiability of the existing
alternating-map-valued form. -/
theorem differentiableAt_manifoldOneForm_inChartAt (c : ℂ) {P Q : ℂ → ℝ} {z : ℂ}
    (hP : DifferentiableAt ℝ P z) (hQ : DifferentiableAt ℝ Q z) :
    DifferentiableAt ℝ ((manifoldOneForm P Q).inChartAt c) z := by
  have hlin : DifferentiableAt ℝ (oneForm P Q) z := by
    rw [oneForm_eq_clm]
    exact (hP.smul_const Complex.reCLM).add (hQ.smul_const Complex.imCLM)
  rw [manifoldOneForm_inChartAt]
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ℂ) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.differentiableAt.comp z hlin

/-- The manifold exterior derivative has the curl as its coefficient in the positive real basis. -/
theorem _root_.DifferentiableAt.mextDeriv_manifoldOneForm_apply {P Q : ℂ → ℝ} {z : ℂ}
    (hP : DifferentiableAt ℝ P z) (hQ : DifferentiableAt ℝ Q z) :
    mextDeriv (manifoldOneForm P Q) z
      (fun i ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm (![1, Complex.I] i)) =
        curl P Q z := by
  have h := mextDeriv_def (manifoldOneForm P Q) z
  have he := congrArg (fun L : TangentSpace 𝓘(ℝ, ℂ) z [⋀^Fin 2]→L[ℝ] ℝ ↦
    L (fun i ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm (![1, Complex.I] i))) h
  -- The canonical identification of the plane's tangent space sends this tuple to `(1,I)`.
  change mextDeriv (manifoldOneForm P Q) z _ =
    extDerivWithin ((manifoldOneForm P Q).inChartAt z) (Set.range 𝓘(ℝ, ℂ))
      (extChartAt 𝓘(ℝ, ℂ) z z) ![1, Complex.I] at he
  rw [he, extChartAt_model_space_eq_id]
  simp only [modelWithCornersSelf_coe, range_id, PartialEquiv.refl_coe, id_eq,
    extDerivWithin_univ]
  have hd := differentiableAt_manifoldOneForm_inChartAt z hP hQ
  rw [manifoldOneForm_inChartAt] at hd ⊢
  rw [extDeriv_apply hd]
  have h₁ : (1 : Fin 2).removeNth ![(1 : ℂ), Complex.I] = ![(1 : ℂ)] := by
    ext i
    fin_cases i
    rfl
  suffices fderiv ℝ Q z 1 + -(fderiv ℝ P z Complex.I) = curl P Q z by
    simpa [Fin.sum_univ_succ, h₁, oneForm_apply] using this
  rw [curl, sub_eq_add_neg]

/-- The coordinate form of AC Green agrees with the existing manifold exterior derivative.
The coefficient is integrated against ordinary planar area in the basis `(1,I)`. -/
theorem green_ac_mextDeriv {γ : ℝ → ℂ} {a b : ℝ} {U : Set ℂ} {P Q : ℂ → ℝ}
    (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hU : IsOpen U) (htrace : γ '' uIcc a b ⊆ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    (hindex : ∀ z ∉ U, Contour.windingNumber γ a b z = 0) :
    IntervalIntegrable (circulationFun P Q γ) volume a b ∧
      IntegrableOn (fun z ↦ windingWeight γ a b z *
        mextDeriv (manifoldOneForm P Q) z
          (fun i ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm (![1, Complex.I] i))) U ∧
      (∫ t in a..b, circulationFun P Q γ t) =
        ∫ z in U, windingWeight γ a b z *
          mextDeriv (manifoldOneForm P Q) z
            (fun i ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm (![1, Complex.I] i)) := by
  have heq : EqOn (fun z ↦ windingWeight γ a b z * curl P Q z)
      (fun z ↦ windingWeight γ a b z *
        mextDeriv (manifoldOneForm P Q) z
          (fun i ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm (![1, Complex.I] i))) U := by
    intro z hz
    dsimp only
    rw [DifferentiableAt.mextDeriv_manifoldOneForm_apply
      (((hP z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
      (((hQ z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)]
  have h := green_ac_winding hab hγ hclosed hU htrace hP hQ hindex
  exact ⟨h.1, h.2.1.congr_fun heq hU.measurableSet,
    h.2.2.trans (setIntegral_congr_fun hU.measurableSet heq)⟩

end TauCeti.Green
