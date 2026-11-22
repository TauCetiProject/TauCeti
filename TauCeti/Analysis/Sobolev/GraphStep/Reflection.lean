/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import TauCeti.Analysis.Sobolev.GraphStep.Basic
public import TauCeti.MeasureTheory.Group.Inversion
import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
import TauCeti.MeasureTheory.Group.Measure

/-!
# Time reflection on whole-line weak-derivative graph spaces

For a bounded linear map `ι : D →L[ℝ] H` into a Banach space `H` and an additive Haar measure `μ`
on `ℝ`, time reflection `s ↦ u(-s)` acts as an involutive linear isometry equivalence
`TauCeti.WeakDerivStep.reflectEvolutionEquiv ι` on the whole-line Sobolev graph
`WeakDerivStep μ ⊤ p (ι.compLpL p (μ.restrict ((⊤ : Opens ℝ) : Set ℝ)))`, negating and
reflecting the weak derivative.

## Main declarations

* `TauCeti.WeakDerivStep.reflectEvolutionEquiv`: time reflection `s ↦ u(-s)` as an involutive
  linear isometry equivalence on
  `WeakDerivStep μ ⊤ p (ι.compLpL p (μ.restrict ((⊤ : Opens ℝ) : Set ℝ)))`.
* `TauCeti.WeakDerivStep.prev_reflectEvolutionEquiv`,
  `TauCeti.WeakDerivStep.weakFDeriv_reflectEvolutionEquiv`: action on the base and weak-derivative
  components.
* `TauCeti.WeakDerivStep.reflectEvolutionEquiv_reflectEvolutionEquiv`,
  `TauCeti.WeakDerivStep.reflectEvolutionEquiv_symm`,
  `TauCeti.WeakDerivStep.reflectEvolutionEquiv_trans_self`: involution and inverse identities.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal

section Reflect

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {mu : Measure ℝ} [mu.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "μtop" => (mu.restrict ((⊤ : Opens ℝ) : Set ℝ))

private theorem hasWeakFDerivOn_reflect (ι : D →L[ℝ] H)
    (u : WeakDerivStep mu ⊤ p (ι.compLpL p μtop)) :
    HasWeakFDerivOn mu ⊤
      (ι.compLpL p μtop (negLpₗᵢ ℝ (prev (ι.compLpL p μtop) u)))
      ((-negLpₗᵢ ℝ (weakFDeriv (ι.compLpL p μtop) u) : Lp (ℝ →L[ℝ] H) p μtop) :
        ℝ → ℝ →L[ℝ] H) := by
  have h1 := (hasWeakFDerivOn_base_prev (ι.compLpL p μtop) u).comp_continuousLinearEquiv
    (U := ⊤) (ContinuousLinearEquiv.neg ℝ) (Measure.measurePreserving_neg mu) (Set.mapsTo_univ _ _)
  refine (h1.congr_ae ?_).congr_ae_deriv ?_
  · have hcomp :=
      (Measure.measurePreserving_neg μtop).quasiMeasurePreserving.ae_eq_comp
        (ι.coeFn_compLpL (prev (ι.compLpL p μtop) u))
    filter_upwards [hcomp, ι.coeFn_compLpL (negLpₗᵢ ℝ (prev (ι.compLpL p μtop) u)),
      coeFn_negLpₗᵢ (𝕜 := ℝ) (prev (ι.compLpL p μtop) u)] with s hιneg hιref href
    simpa only [Function.comp_apply, ContinuousLinearEquiv.neg_apply, hιref, href] using hιneg
  · filter_upwards [Lp.coeFn_neg (negLpₗᵢ ℝ (weakFDeriv (ι.compLpL p μtop) u)),
      coeFn_negLpₗᵢ (𝕜 := ℝ) (weakFDeriv (ι.compLpL p μtop) u)] with s hneg href
    rw [hneg, Pi.neg_apply, href]
    ext
    simp

/-- Time reflection `s ↦ u(-s)` as an involutive linear isometry of the evolution Sobolev space
on `ℝ`. -/
def reflectEvolutionEquiv (ι : D →L[ℝ] H) :
    WeakDerivStep mu ⊤ p (ι.compLpL p μtop) ≃ₗᵢ[ℝ] WeakDerivStep mu ⊤ p (ι.compLpL p μtop) where
  toFun u :=
    mk (ι.compLpL p μtop) (negLpₗᵢ ℝ (prev (ι.compLpL p μtop) u))
      (-negLpₗᵢ ℝ (weakFDeriv (ι.compLpL p μtop) u)) (hasWeakFDerivOn_reflect ι u)
  invFun u :=
    mk (ι.compLpL p μtop) (negLpₗᵢ ℝ (prev (ι.compLpL p μtop) u))
      (-negLpₗᵢ ℝ (weakFDeriv (ι.compLpL p μtop) u)) (hasWeakFDerivOn_reflect ι u)
  left_inv u := ext (by simp only [prev_mk, negLpₗᵢ_negLpₗᵢ])
  right_inv u := ext (by simp only [prev_mk, negLpₗᵢ_negLpₗᵢ])
  map_add' u v := ext (by simp only [prev_mk, prev_add, map_add])
  map_smul' c u := ext (by simp only [prev_mk, prev_smul, map_smul, RingHom.id_apply])
  norm_map' u := by
    have hsq : ‖mk (ι.compLpL p μtop) (negLpₗᵢ ℝ (prev (ι.compLpL p μtop) u))
        (-negLpₗᵢ ℝ (weakFDeriv (ι.compLpL p μtop) u))
        (hasWeakFDerivOn_reflect ι u)‖ ^ 2 = ‖u‖ ^ 2 := by
      calc ‖mk (ι.compLpL p μtop) (negLpₗᵢ ℝ (prev (ι.compLpL p μtop) u))
              (-negLpₗᵢ ℝ (weakFDeriv (ι.compLpL p μtop) u))
              (hasWeakFDerivOn_reflect ι u)‖ ^ 2
          = ‖negLpₗᵢ ℝ (prev (ι.compLpL p μtop) u)‖ ^ 2 +
              ‖-negLpₗᵢ ℝ (weakFDeriv (ι.compLpL p μtop) u)‖ ^ 2 := by
            rw [norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq, prev_mk, weakFDeriv_mk]
        _ = ‖prev (ι.compLpL p μtop) u‖ ^ 2 + ‖weakFDeriv (ι.compLpL p μtop) u‖ ^ 2 := by
            rw [norm_neg, (negLpₗᵢ ℝ).norm_map, (negLpₗᵢ ℝ).norm_map]
        _ = ‖u‖ ^ 2 := (norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq _ u).symm
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Time reflection acts on the `Lᵖ(ℝ; D)` path by `TauCeti.negLpₗᵢ`. -/
theorem prev_reflectEvolutionEquiv (ι : D →L[ℝ] H)
    (u : WeakDerivStep mu ⊤ p (ι.compLpL p μtop)) :
    prev (ι.compLpL p μtop) (reflectEvolutionEquiv ι u) =
      negLpₗᵢ ℝ (prev (ι.compLpL p μtop) u) :=
  prev_mk (ι.compLpL p μtop) _ _ _

/-- Time reflection negates and reflects the weak derivative via `TauCeti.negLpₗᵢ`. -/
theorem weakFDeriv_reflectEvolutionEquiv (ι : D →L[ℝ] H)
    (u : WeakDerivStep mu ⊤ p (ι.compLpL p μtop)) :
    weakFDeriv (ι.compLpL p μtop) (reflectEvolutionEquiv ι u) =
      -negLpₗᵢ ℝ (weakFDeriv (ι.compLpL p μtop) u) :=
  weakFDeriv_mk (ι.compLpL p μtop) _ _ _

/-- Time reflection is involutive. -/
theorem reflectEvolutionEquiv_reflectEvolutionEquiv (ι : D →L[ℝ] H)
    (u : WeakDerivStep mu ⊤ p (ι.compLpL p μtop)) :
    reflectEvolutionEquiv ι (reflectEvolutionEquiv ι u) = u :=
  ext (by simp only [prev_reflectEvolutionEquiv, negLpₗᵢ_negLpₗᵢ])

/-- Time reflection is its own inverse. -/
@[simp]
theorem reflectEvolutionEquiv_symm (ι : D →L[ℝ] H) :
    (reflectEvolutionEquiv (mu := mu) (p := p) ι).symm =
      reflectEvolutionEquiv (mu := mu) (p := p) ι :=
  LinearIsometryEquiv.ext fun _ ↦ rfl

/-- Composing time reflection with itself is the identity equivalence. -/
@[simp]
theorem reflectEvolutionEquiv_trans_self (ι : D →L[ℝ] H) :
    (reflectEvolutionEquiv (mu := mu) (p := p) ι).trans
      (reflectEvolutionEquiv (mu := mu) (p := p) ι) = LinearIsometryEquiv.refl ℝ _ :=
  LinearIsometryEquiv.ext (reflectEvolutionEquiv_reflectEvolutionEquiv ι)

end Reflect

end TauCeti.WeakDerivStep
