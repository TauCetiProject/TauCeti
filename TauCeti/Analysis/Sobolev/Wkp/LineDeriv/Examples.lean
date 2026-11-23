/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Analysis.Sobolev.Wkp.LineDeriv.Classical
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.MeasureTheory.Function.Lp.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# Worked examples for Sobolev directional contractions

Concrete checks for `TauCeti.Wkp.lineDerivL`, `TauCeti.Wkp.iteratedLineDerivZeroL`, and the
classical `ContDiffOn` comparison lemmas on intervals and planar discs:

* On `(0, 1) ⊆ ℝ`, `u(x) = x²` differentiated in direction `3` has value `6x` and weak derivative
  `6` almost everywhere.
* Sharpness of `‖lineDerivL v 0 u‖ ≤ ‖v‖ * ‖iteratedGradient 0 u‖` at exponent `p = ⊤` for
  `u(x) = x²` on `(0, 1)` and `v = 3`.
* On the planar unit disc, `u(x) = x₀ x₁` has commuting coordinate directional derivatives both
  equal to `1` almost everywhere.
-/

noncomputable section

namespace TauCeti.Wkp

open MeasureTheory TopologicalSpace
open scoped ENNReal

/-- On `Ω = (0, 1) ⊆ ℝ`, `u(x) = x²` in `W^{2,p}(Ω)` differentiated in direction `v = 3` has
value `6x` almost everywhere and weak derivative `6 = (D²u)⟨3⟩¹` almost everywhere. -/
example {p : ENNReal} [Fact (1 ≤ p)] :
    let Ω : Opens ℝ := ⟨Set.Ioo 0 1, isOpen_Ioo⟩
    ∃ u : Wkp volume Ω p 2,
      (value 2 u : ℝ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝ)] (fun x : ℝ => x ^ 2) ∧
      (value 1 (lineDerivL (3 : ℝ) 1 u) : ℝ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝ)]
        (fun x : ℝ => 6 * x) ∧
      (iteratedGradient 0 (lineDerivL (3 : ℝ) 1 u) : ℝ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝ)]
        fun _ : ℝ => 6 := by
  intro Ω
  have hf : ContDiff ℝ 2 (fun x : ℝ => x ^ 2) := contDiff_id.pow 2
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume) (Omega := Ω)
    (p := p) 2 isOpen_univ hf.contDiffOn isCompact_Icc Set.Ioo_subset_Icc_self (Set.subset_univ _)
  refine ⟨u, hu, ?_, ?_⟩
  · refine (value_lineDerivL_ae_eq_of_contDiffOn 1 u (3 : ℝ)
      (hf.contDiffOn.of_le one_le_two) hu).trans (.of_forall fun x => ?_)
    dsimp only
    rw [fderiv_eq_smul_deriv, deriv_pow_field, smul_eq_mul]
    norm_num
    ring
  · filter_upwards [iteratedGradient_lineDerivL_ae (3 : ℝ) 0 u,
      iteratedGradient_ae_eq_of_contDiffOn 1 u hf.contDiffOn hu] with x h1 h2
    rw [h1, h2, iteratedGradientChain_succ, iteratedGradientChain_zero]
    have hgrad : gradient (fun y : ℝ => y ^ 2) = fun y : ℝ => 2 * y := by
      ext y
      rw [gradient_eq_deriv', deriv_pow_field]
      norm_num
    rw [hgrad]
    have hd : HasFDerivAt (fun y : ℝ => (2 : ℝ) * y)
        ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) x := by
      simpa using (hasFDerivAt_id x).const_mul (2 : ℝ)
    rw [hd.fderiv, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    norm_num

/-- Sharpness of the componentwise bound `‖lineDerivL v 0 u‖ ≤ ‖v‖ * ‖iteratedGradient 0 u‖`
at exponent `p = ⊤` for `u(x) = x²` on `Ioo 0 1` and `v = 3`: both sides equal `6`. -/
example :
    let Ω : Opens ℝ := ⟨Set.Ioo 0 1, isOpen_Ioo⟩
    ∃ u : Wkp volume Ω ⊤ 1,
      (value 1 u : ℝ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝ)] (fun x : ℝ => x ^ 2) ∧
      ‖lineDerivL (3 : ℝ) 0 u‖ = 6 ∧
      ‖(3 : ℝ)‖ * ‖iteratedGradient 0 u‖ = 6 := by
  intro Ω
  have hf : ContDiff ℝ 1 (fun x : ℝ => x ^ 2) := (contDiff_id.pow 2).of_le one_le_two
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume) (Omega := Ω)
    (p := ⊤) 1 isOpen_univ hf.contDiffOn isCompact_Icc Set.Ioo_subset_Icc_self (Set.subset_univ _)
  have hgrad : ‖iteratedGradient 0 u‖ = 2 := by
    rw [norm_iteratedGradient_eq_lpNorm_of_contDiffOn 0 u hf.contDiffOn hu]
    have h2 : (fun x : ℝ => ‖iteratedFDeriv ℝ 1 (fun y : ℝ => y ^ 2) x‖) =
        fun x : ℝ => ‖(2 : ℝ) * x‖ := funext fun x => by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one, deriv_pow_field]
      norm_num
    have hlp : lpNorm (iteratedFDeriv ℝ 1 (fun y : ℝ => y ^ 2)) ⊤
        (volume.restrict (Ω : Set ℝ)) =
        lpNorm (fun x : ℝ => (2 : ℝ) * x) ⊤ (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
      rw [lpNorm, lpNorm]
      congr 1
      refine eLpNorm_congr_norm_ae
        ((ContinuousOn.continuousOn_iteratedFDeriv hf.contDiffOn Ω.isOpen
          le_rfl).aestronglyMeasurable Ω.isOpen.measurableSet)
        ((continuous_const.mul continuous_id).continuousOn.aestronglyMeasurable
          Ω.isOpen.measurableSet)
        (.of_forall (congrFun h2))
    rw [hlp]
    simpa [Pi.smul_def, zero_lt_one] using
      lpNorm_const_smul (2 : ℝ) (id : ℝ → ℝ) (volume.restrict (Set.Ioo (0 : ℝ) 1)) (p := ∞)
  have hline : ‖lineDerivL (3 : ℝ) 0 u‖ = 6 := by
    have h3 : innerSL ℝ (3 : ℝ) = (3 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
      refine ContinuousLinearMap.ext fun x => ?_
      simp [RCLike.inner_apply, mul_comm]
    rw [lineDerivL_zero_apply, h3, ContinuousLinearMap.smul_compLp,
      ContinuousLinearMap.id_compLp, norm_smul, hgrad]
    norm_num
  refine ⟨u, hu, hline, ?_⟩
  rw [hgrad]
  norm_num

/-- On the open unit ball in `ℝ²`, `u(x) = x₀ * x₁` in `W^{2,p}(B(0, 1))` satisfies
`lineDerivL e₀ 0 (lineDerivL e₁ 1 u) = lineDerivL e₁ 0 (lineDerivL e₀ 1 u)` and both equal `1`
almost everywhere. -/
example {p : ENNReal} [Fact (1 ≤ p)] :
    let E₂ := EuclideanSpace ℝ (Fin 2)
    let Ω : Opens E₂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩
    let e₀ : E₂ := EuclideanSpace.single 0 1
    let e₁ : E₂ := EuclideanSpace.single 1 1
    ∃ u : Wkp volume Ω p 2,
      (value 2 u : E₂ → ℝ) =ᵐ[volume.restrict (Ω : Set E₂)] (fun x : E₂ => x 0 * x 1) ∧
      lineDerivL e₀ 0 (lineDerivL e₁ 1 u) = lineDerivL e₁ 0 (lineDerivL e₀ 1 u) ∧
      (lineDerivL e₀ 0 (lineDerivL e₁ 1 u) : E₂ → ℝ) =ᵐ[volume.restrict (Ω : Set E₂)]
        fun _ : E₂ => 1 := by
  intro E₂ Ω e₀ e₁
  let l₀ : E₂ →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)
  let l₁ : E₂ →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)
  have hl₀ (v : E₂) : l₀ v = v 0 := congrFun (EuclideanSpace.coe_proj ℝ) v
  have hl₁ (v : E₂) : l₁ v = v 1 := congrFun (EuclideanSpace.coe_proj ℝ) v
  have hfun : (fun x : E₂ => x 0 * x 1) = fun x : E₂ => l₀ x * l₁ x :=
    funext fun v => by rw [hl₀, hl₁]
  have hf : ContDiff ℝ 2 (fun x : E₂ => l₀ x * l₁ x) := l₀.contDiff.mul l₁.contDiff
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume) (Omega := Ω)
    (p := p) 2 isOpen_univ hf.contDiffOn (isCompact_closedBall (0 : E₂) 1)
    Metric.ball_subset_closedBall (Set.subset_univ _)
  refine ⟨u, hfun ▸ hu, lineDerivL_comm e₀ e₁ 0 u, ?_⟩
  have hiter : lineDerivL e₀ 0 (lineDerivL e₁ 1 u) = iteratedLineDerivZeroL 2 ![e₁, e₀] u := by
    rw [iteratedLineDerivZeroL_succ, ContinuousLinearMap.comp_apply, Matrix.cons_val_zero,
      iteratedLineDerivZeroL_one]
    simp [Fin.tail]
  rw [hiter]
  refine (iteratedLineDerivZeroL_succ_ae_eq_of_contDiffOn 1 u ![e₁, e₀] hf.contDiffOn hu).trans
    (.of_forall fun x => ?_)
  dsimp only
  rw [iteratedFDeriv_two_apply]
  have hfd : fderiv ℝ (fun y : E₂ => l₀ y * l₁ y) =
      fun y => l₀ y • l₁ + l₁ y • l₀ := by
    ext y v
    have hd : HasFDerivAt (fun z : E₂ => l₀ z * l₁ z) (l₀ y • l₁ + l₁ y • l₀) y :=
      (l₀.hasFDerivAt (x := y)).mul (l₁.hasFDerivAt (x := y))
    rw [hd.fderiv]
  rw [hfd]
  have hd₂ : HasFDerivAt (fun y : E₂ => l₀ y • l₁ + l₁ y • l₀)
      (l₀.smulRight l₁ + l₁.smulRight l₀) x :=
    (l₀.hasFDerivAt.smul_const l₁).add (l₁.hasFDerivAt.smul_const l₀)
  rw [hd₂.fderiv]
  simp [hl₀, hl₁, e₀, e₁]

end TauCeti.Wkp
