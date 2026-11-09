/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Weight
public import TauCeti.Analysis.PDE.Parabolic.Holder.Backward
import TauCeti.Probability.Finance.LogSpot

/-!
# The weighted log-spot pricing operator on parabolic Hölder spaces

Write `a = σ² / 2`, and let `r` be the short rate. In log-spot coordinates the pricing
operator is `∂ₜ + a ∂ᵧ² + (r - a) ∂ᵧ - r`. Conjugating by the weight `1 + exp y`
turns prices of linear growth in the spot into bounded functions. This file constructs
its coefficients as bounded parabolic Hölder fields and the resulting operator as a
continuous linear map on `ParabolicC2HolderSpace`:

`∂ₜ + a ∂ᵧ² + (r + a (2 sigmoid y - 1)) ∂ᵧ - r (1 - sigmoid y)`.

The second-order coefficient is unchanged, so a positive lower bound for `a` is preserved.
The construction needs no ellipticity or sign assumption; these belong to existence
and comparison theorems. Both `a` and `r` may be parabolic Hölder fields, although the
financial short rate is normally independent of space. The coefficient formulas and
operator identity hold on the closed time slab, using within derivatives at its endpoints.
This is a coefficient and operator adapter, not an existence or replication theorem.

The construction and conjugation identity use
`ParabolicC2HolderSpace.weightFirstOrderCoeff` and
`ParabolicC2HolderSpace.weightZerothOrderCoeff`, with the gradient and Hessian of
`log (1 + exp y)`. The zeroth-order coefficient simplifies to an expression independent
of `a`. Identification with the spot pricing equation uses `TauCeti.Finance.pde_comp_exp`.

## References

* P. Wilmott, S. Howison, J. Dewynne, *The Mathematics of Financial Derivatives*,
  Cambridge University Press, 1995, §5.4.
-/

public section
noncomputable section

namespace TauCeti.Finance

open Set Real Filter Topology ParabolicSpaceTime ContinuousLinearMap
open ParabolicC2HolderSpace
open scoped NNReal

variable {α : ℝ≥0} {t₀ t₁ : ℝ} {ht : t₀ < t₁}

-- These shortcuts keep instance search shallow for the nested coefficient spaces.
private local instance : NormedAddCommGroup (ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance

/-- The first-order coefficient of the weighted log-spot pricing operator, acting on a
spatial gradient by multiplication by `r + a (2 sigmoid y - 1)`. -/
def weightedLogSpotFirstOrderCoeff (hα : α ≤ 1)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  weightFirstOrderCoeff
    ((lsmul ℝ ℝ).compHolder₂ a (HolderSpace.const ((apply ℝ ℝ 1).comp (apply ℝ _ 1))))
    ((lsmul ℝ ℝ).compHolder₂ (r - a) (HolderSpace.const (apply ℝ ℝ 1)))
    (logOneAddExpGrad hα)

/-- The zeroth-order coefficient of the weighted log-spot pricing operator, acting by
multiplication by `-r (1 - sigmoid y)`. -/
def weightedLogSpotZerothOrderCoeff (hα : α ≤ 1)
    (r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) (ℝ →L[ℝ] ℝ) :=
  (lsmul ℝ ℝ).compHolder₂ (-r)
    (HolderSpace.const (ContinuousLinearMap.id ℝ ℝ) -
      HolderSpace.compSlabSpaceL (logOneAddExpGrad hα))

variable (hα : α ≤ 1) (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)

@[simp]
theorem weightedLogSpotFirstOrderCoeff_apply (p : slab (E := ℝ) t₀ t₁)
    (D : ℝ →L[ℝ] ℝ) :
    weightedLogSpotFirstOrderCoeff hα a r p D =
      (r p + a p * (2 * sigmoid (p : ParabolicSpaceTime ℝ).space - 1)) * D 1 := by
  simp [weightedLogSpotFirstOrderCoeff, weightFirstOrderCoeff_apply]
  ring

@[simp]
theorem weightedLogSpotZerothOrderCoeff_apply (p : slab (E := ℝ) t₀ t₁) (v : ℝ) :
    weightedLogSpotZerothOrderCoeff hα r p v =
      -(r p * (1 - sigmoid (p : ParabolicSpaceTime ℝ).space)) * v := by
  simp [weightedLogSpotZerothOrderCoeff]
  ring

/-- The backward pricing operator after division by `1 + exp y`, as a bounded linear
map from bounded order-two parabolic Hölder functions to parabolic Hölder functions. -/
def weightedLogSpotPricingOperatorL :
    ParabolicC2HolderSpace α ℝ ℝ ht →L[ℝ] HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ :=
  backwardParabolicOperatorL (F := ℝ) hα
    ((lsmul ℝ ℝ).compHolder₂ a (HolderSpace.const ((apply ℝ ℝ 1).comp (apply ℝ _ 1))))
    (weightedLogSpotFirstOrderCoeff hα a r) (weightedLogSpotZerothOrderCoeff hα r)

/-- Evaluation of the bounded operator in terms of its derivative fields. -/
@[simp]
theorem weightedLogSpotPricingOperatorL_apply (v : ParabolicC2HolderSpace α ℝ ℝ ht)
    (p : slab (E := ℝ) t₀ t₁) :
    weightedLogSpotPricingOperatorL hα a r v p = timeDerivL v p +
      (a p * spatialSecondFDerivL v p 1 1 +
        (r p + a p * (2 * sigmoid (p : ParabolicSpaceTime ℝ).space - 1)) *
          spatialFDerivL v p 1 -
        r p * (1 - sigmoid (p : ParabolicSpaceTime ℝ).space) * v p) := by
  simp [weightedLogSpotPricingOperatorL, sub_eq_add_neg]

/-- The bounded weighted operator is the classical backward log-spot pricing operator
on `(1 + exp y) v`, divided by the weight. Within time derivatives include the endpoints. -/
theorem one_add_exp_mul_weightedLogSpotPricingOperatorL
    (v : ParabolicC2HolderSpace α ℝ ℝ ht) (x : ℝ) (t : Icc t₀ t₁) :
    (1 + exp x) * weightedLogSpotPricingOperatorL hα a r v (slabMk x t) =
      derivWithin (fun s ↦ (1 + exp x) * timeExtension ht.le v x s) (Icc t₀ t₁) t +
        (a (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦
            (1 + exp y) * v (slabMk y t)) x 1 1 +
          (r (slabMk x t) - a (slabMk x t)) *
            fderiv ℝ (fun y ↦ (1 + exp y) * v (slabMk y t)) x 1 -
          r (slabMk x t) * ((1 + exp x) * v (slabMk x t))) := by
  have h := one_add_exp_smul_parabolicOperatorL_weightCoeff hα
    (A := (lsmul ℝ ℝ).compHolder₂ a
      (HolderSpace.const ((apply ℝ ℝ 1).comp (apply ℝ _ 1))))
    (B := (lsmul ℝ ℝ).compHolder₂ (r - a) (HolderSpace.const (apply ℝ ℝ 1)))
    (C := (lsmul ℝ ℝ).compHolder₂ (-r)
      (HolderSpace.const (ContinuousLinearMap.id ℝ ℝ))) v
    (u := fun p ↦ (1 + exp (p : ParabolicSpaceTime ℝ).space) * v p)
    (fun _ ↦ rfl) x t
  have htime : timeExtension ht.le
      (fun p ↦ (1 + exp (p : ParabolicSpaceTime ℝ).space) * v p) x =
      fun s ↦ (1 + exp x) * timeExtension ht.le v x s := by
    ext s
    simp [timeExtension_def]
  simp only [smul_eq_mul, htime] at h
  have hw := weightedLogSpotPricingOperatorL_apply hα a r v (slabMk x t)
  simp only [space_slabMk] at hw
  have hd := ((v.hasTimeDerivWithinAt x t).const_mul (1 + exp x)).derivWithin
    (uniqueDiffOn_Icc ht t t.2)
  simp [parabolicOperatorL_apply, weightFirstOrderCoeff_apply,
    weightZerothOrderCoeff_apply, space_slabMk] at h
  rw [hw]
  simp only [fderiv_apply_one_eq_deriv]
  -- The supplier uses the forward sign. Negate its identity and add twice the time identity.
  linear_combination -h - 2 * hd

/-- For a price `C` represented by the bounded weighted function `v`, the constructed
operator is the spot pricing equation divided by `1 + exp x`. The local volatility is
specified only through `a = σ² / 2` at the point in question. -/
theorem weightedLogSpotPricingOperatorL_eq_spot
    (v : ParabolicC2HolderSpace α ℝ ℝ ht) {C : ℝ → ℝ → ℝ}
    (hC : ∀ y (s : Icc t₀ t₁), C (exp y) s = (1 + exp y) * v (slabMk y s))
    (x : ℝ) (t : Icc t₀ t₁) (σ : ℝ) (ha : a (slabMk x t) = σ ^ 2 / 2)
    (hCs : ∀ᶠ s in 𝓝 (exp x), DifferentiableAt ℝ (fun s ↦ C s t) s)
    (hCss : DifferentiableAt ℝ (deriv fun s ↦ C s t) (exp x))
    (hCt : DifferentiableAt ℝ (C (exp x)) t) :
    weightedLogSpotPricingOperatorL hα a r v (slabMk x t) =
      (deriv (C (exp x)) t +
        σ ^ 2 * exp x ^ 2 / 2 * deriv (deriv fun s ↦ C s t) (exp x) +
        r (slabMk x t) * (exp x * deriv (fun s ↦ C s t) (exp x) - C (exp x) t)) /
      (1 + exp x) := by
  have hw := one_add_exp_mul_weightedLogSpotPricingOperatorL hα a r v x t
  have hs : (fun y ↦ (1 + exp y) * v (slabMk y t)) = fun y ↦ C (exp y) t :=
    funext fun y ↦ (hC y t).symm
  have htime : derivWithin (fun s ↦ (1 + exp x) * timeExtension ht.le v x s)
      (Icc t₀ t₁) t = deriv (C (exp x)) t := by
    rw [derivWithin_congr (f := C (exp x))
      (fun s hs ↦ by
        rw [timeExtension_of_mem ht.le v x ⟨s, hs⟩]
        exact (hC x ⟨s, hs⟩).symm)
      (by rw [timeExtension_of_mem ht.le v x t]; exact (hC x t).symm)]
    exact hCt.derivWithin (uniqueDiffOn_Icc ht t t.2)
  have hsecond : fderiv ℝ (fderiv ℝ fun y ↦ C (exp y) t) x 1 1 =
      deriv (deriv fun y ↦ C (exp y) t) x := by
    simpa [_root_.iteratedFDeriv_two_apply, iteratedDeriv_succ, iteratedDeriv_one] using
      (iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod (𝕜 := ℝ) (n := 2)
        (f := fun y ↦ C (exp y) t) (x := x) (m := fun _ ↦ 1))
  rw [hs, htime, ha, hsecond, fderiv_apply_one_eq_deriv, ← hC x t] at hw
  have hpde := pde_comp_exp σ (r (slabMk x t)) hCs hCss
  apply (eq_div_iff (by positivity : 1 + exp x ≠ 0)).2
  linear_combination hw + hpde

end TauCeti.Finance
