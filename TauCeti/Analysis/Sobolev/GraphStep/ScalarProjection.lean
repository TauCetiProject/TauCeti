/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.Basic
public import TauCeti.Analysis.Sobolev.W1p.Basic

/-!
# Scalar projections of weak-derivative graph spaces

Applying a continuous linear functional to an `F`-valued Sobolev field gives a scalar Sobolev
function. `TauCeti.WeakDerivStep.toW1pL` bundles this operation as a bounded linear map into
`W1p`, using the Riesz correspondence to turn the projected derivative into a gradient.
Its value is the projected field, and its gradient pairs with a direction as the functional
applied to the original weak derivative.

The preceding space and its field-selection map remain arbitrary. This permits coordinatewise
use of scalar Sobolev estimates without introducing a separate vector-valued Sobolev carrier.
The construction uses `WeakDerivStep` and `W1p.mk`, whose weak derivatives are distributional.

## Reference

L. C. Evans, *Partial Differential Equations*, second edition, Chapter 5, §5.2.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace

variable {E F X : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [SeminormedAddCommGroup X] [NormedSpace ℝ X]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- Apply a continuous linear functional to the field selected by `base`, obtaining a scalar
Sobolev function. Its operator norm is at most `‖ℓ‖ * (‖base‖ + 1)`. -/
def toW1pL (base : X →L[ℝ] Lp F p (mu.restrict Omega)) (ℓ : F →L[ℝ] ℝ) :
    WeakDerivStep mu Omega p base →L[ℝ] W1p mu Omega p := by
  let G : (E →L[ℝ] F) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.compL ℝ E F ℝ ℓ)
  let vL := (ℓ.compLpL p (mu.restrict Omega)).comp (base.comp (prevL base))
  let gL := (G.compLpL p (mu.restrict Omega)).comp (weakFDerivL base)
  have hg (u : WeakDerivStep mu Omega p base) :
      HasWeakFDerivOn mu Omega (vL u) (fun x ↦ innerSL ℝ (gL u x)) := by
    simp only [vL, ContinuousLinearMap.comp_apply, prevL_apply]
    refine (((hasWeakFDerivOn_base_prev base u).clm_comp ℓ).congr_ae
      (Filter.EventuallyEq.symm (ℓ.coeFn_compLpL (base (prev base u))))).congr_ae_deriv ?_
    filter_upwards [G.coeFn_compLpL (weakFDeriv base u)] with x hx
    ext h
    simp only [gL, ContinuousLinearMap.comp_apply, weakFDerivL_apply]
    rw [hx, innerSL_apply_apply]
    simpa only [G, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
      (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E)
        (x := h) (y := ℓ.comp (weakFDeriv base u x))).symm
  let T : WeakDerivStep mu Omega p base →ₗ[ℝ] W1p mu Omega p :=
    { toFun := fun u ↦ W1p.mk (vL u) (gL u) (hg u)
      map_add' := fun u v ↦ W1p.ext_value (by
        simp only [← W1p.valueL_apply, map_add]
        simp only [W1p.valueL_apply, W1p.value_mk])
      map_smul' := fun c u ↦ W1p.ext_value (by
        simp only [← W1p.valueL_apply, map_smul]
        simp only [W1p.valueL_apply, W1p.value_mk, RingHom.id_apply]) }
  have hG : ‖G‖ ≤ ‖ℓ‖ := by
    refine G.opNorm_le_bound (norm_nonneg ℓ) fun D ↦ ?_
    simpa only [G, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.norm_map] using ℓ.opNorm_comp_le D
  refine T.mkContinuous (‖ℓ‖ * (‖base‖ + 1)) fun u ↦ ?_
  calc
    ‖T u‖ ≤ ‖vL u‖ + ‖gL u‖ := by
      simpa only [T, LinearMap.coe_mk, AddHom.coe_mk, W1p.value_mk, W1p.gradient_mk]
        using W1p.norm_le_norm_value_add_norm_gradient (T u)
    _ ≤ ‖ℓ‖ * (‖base‖ * ‖u‖) + ‖ℓ‖ * ‖u‖ := by
      apply add_le_add
      · simp only [vL, ContinuousLinearMap.comp_apply, prevL_apply]
        exact ((ℓ.compLpL p (mu.restrict Omega)).le_opNorm _).trans
          (mul_le_mul (ℓ.norm_compLpL_le)
            ((base.le_opNorm _).trans (mul_le_mul_of_nonneg_left
              (norm_prev_le base u) (norm_nonneg base))) (norm_nonneg _) (norm_nonneg ℓ))
      · simp only [gL, ContinuousLinearMap.comp_apply, weakFDerivL_apply]
        exact ((G.compLpL p (mu.restrict Omega)).le_opNorm _).trans
          (mul_le_mul ((G.norm_compLpL_le).trans hG) (norm_weakFDeriv_le base u)
            (norm_nonneg _) (norm_nonneg ℓ))
    _ = (‖ℓ‖ * (‖base‖ + 1)) * ‖u‖ := by ring

/-- Scalar projection commutes with the value map: its `Lᵖ` class is obtained by applying `ℓ`
to the field selected by `base`. -/
@[simp]
theorem value_toW1pL (base : X →L[ℝ] Lp F p (mu.restrict Omega)) (ℓ : F →L[ℝ] ℝ)
    (u : WeakDerivStep mu Omega p base) :
    W1p.value (toW1pL base ℓ u) = ℓ.compLpL p (mu.restrict Omega) (base (prev base u)) := by
  simp only [toW1pL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    W1p.value_mk, ContinuousLinearMap.comp_apply, prevL_apply]

/-- The gradient of a scalar projection is the Riesz representative of `ℓ ∘ Du`. -/
@[simp]
theorem gradient_toW1pL (base : X →L[ℝ] Lp F p (mu.restrict Omega)) (ℓ : F →L[ℝ] ℝ)
    (u : WeakDerivStep mu Omega p base) :
    W1p.gradient (toW1pL base ℓ u) =
      ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.compL ℝ E F ℝ ℓ)).compLpL p (mu.restrict Omega)
          (weakFDeriv base u) := by
  simp only [toW1pL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    W1p.gradient_mk, ContinuousLinearMap.comp_apply, weakFDerivL_apply]

/-- Pairing the projected gradient with a direction applies `ℓ` to the original weak derivative
in that direction, almost everywhere. -/
theorem inner_gradient_toW1pL_ae (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (ℓ : F →L[ℝ] ℝ) (u : WeakDerivStep mu Omega p base) :
    ∀ᵐ x ∂mu.restrict Omega, ∀ h : E,
      ⟪W1p.gradient (toW1pL base ℓ u) x, h⟫_ℝ = ℓ (weakFDeriv base u x h) := by
  rw [gradient_toW1pL]
  let G : (E →L[ℝ] F) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.compL ℝ E F ℝ ℓ)
  filter_upwards [G.coeFn_compLpL (weakFDeriv base u)] with x hx
  intro h
  rw [hx]
  exact InnerProductSpace.toDual_symm_apply

/-- The scalar projection has an explicit operator-norm bound. -/
theorem norm_toW1pL_le (base : X →L[ℝ] Lp F p (mu.restrict Omega)) (ℓ : F →L[ℝ] ℝ) :
    ‖toW1pL base ℓ‖ ≤ ‖ℓ‖ * (‖base‖ + 1) := by
  unfold toW1pL
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

end TauCeti.WeakDerivStep
