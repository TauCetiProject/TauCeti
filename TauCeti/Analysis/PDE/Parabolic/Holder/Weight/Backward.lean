/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Backward
public import TauCeti.Analysis.PDE.Parabolic.Holder.Weight.Basic

/-!
# Conjugating the backward parabolic operator by a spatial weight

Let `w = exp ∘ ℓ` be a positive time-independent weight on `ℝⁿ = EuclideanSpace ℝ ι`. The
backward operator `P_back u = ∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u`
(`TauCeti.ParabolicC2HolderSpace.euclideanBackwardParabolicOperatorL`) conjugates by `w` in the
same way as the forward operator
(`TauCeti.ParabolicC2HolderSpace.exp_mul_euclideanParabolicOperatorL_eq`):
`P_back (w v) = w P_back,w v`, with the same conjugated coefficients `b_w`, `c_w`, because `w`
does not depend on time.

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.exp_mul_euclideanBackwardParabolicOperatorL_eq`: the
  conjugation identity for the backward operator.
* `TauCeti.ParabolicC2HolderSpace.euclideanBackwardParabolicOperatorL_weightedCoeff_eq_iff`:
  `P_back,w v = g` exactly when `w v` is a classical solution of `P_back u = w g`.
* `euclideanBackwardParabolicOperatorL_prod_spatialTraceL_weightedCoeff_eq_iff` (in the same
  namespace): the same with the terminal datum, so that the terminal-data map of the conjugated
  operator solves the weighted terminal-value problem.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2 (the substitution
  `u = w v` by a positive weight).
-/

public section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime Real
open scoped NNReal

variable {α : ℝ≥0} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {t₀ t₁ : ℝ} {ht : t₀ < t₁} (hα : α ≤ 1)
  {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {dℓ : ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ}
  {d2ℓ : ι → ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ} {ℓ : EuclideanSpace ℝ ι → ℝ}

include hα

/-- **Conjugation of the backward operator by a spatial weight.** Under the hypotheses of the
forward conjugation identity `exp_mul_euclideanParabolicOperatorL_eq`, the backward operator
`P_back u = ∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u` applied to `u = exp ℓ * v` is `exp ℓ` times the
backward operator with the conjugated coefficients `aⁱʲ`, `b_wⁱ`, `c_w` applied to `v`. -/
theorem exp_mul_euclideanBackwardParabolicOperatorL_eq (hℓ : ContDiff ℝ 2 ℓ)
    (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht) {u : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu : ∀ y (s : Icc t₀ t₁), u y s = exp (ℓ y) * v (slabMk y s))
    (x : EuclideanSpace ℝ ι) (t : Icc t₀ t₁) :
    exp (ℓ x) * euclideanBackwardParabolicOperatorL hα a
        (euclideanWeightedFirstOrderCoeff a b dℓ) (euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ)
        v (slabMk x t) =
      derivWithin (u x) (Icc t₀ t₁) t +
        (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
          ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
          c (slabMk x t) * u x t) := by
  -- Since the weight does not depend on time, `P_back,w v = 2 ∂ₜv - P_w v`, and likewise for `u`.
  have hfwd :=
    exp_mul_euclideanParabolicOperatorL_eq hα (a := a) (b := b) (c := c) hℓ hdℓ hd2ℓ v hu x t
  have htime := derivWithin_eq_exp_smul_timeDerivL v
    (fun y s ↦ (hu y s).trans (smul_eq_mul _ _).symm) x t
  rw [smul_eq_mul] at htime
  rw [euclideanParabolicOperatorL_apply] at hfwd
  rw [euclideanBackwardParabolicOperatorL_apply]
  linear_combination (-2) * htime - hfwd

/-- **Weighted solutions of the backward equation.** For `u = exp ℓ * v` with
`v ∈ C_b^{2+α,1+α/2}`, `v` solves the conjugated backward equation `P_back,w v = g` if and only if
`u` is a classical solution of `P_back u = exp ℓ * g`, with the time derivative of `u` taken
within the closed time interval: forcing terms transform by division by the weight. -/
theorem euclideanBackwardParabolicOperatorL_weightedCoeff_eq_iff (hℓ : ContDiff ℝ 2 ℓ)
    (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht) {u : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu : ∀ y (s : Icc t₀ t₁), u y s = exp (ℓ y) * v (slabMk y s))
    (g : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ) :
    euclideanBackwardParabolicOperatorL hα a (euclideanWeightedFirstOrderCoeff a b dℓ)
        (euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ) v = g ↔
      ∀ (x : EuclideanSpace ℝ ι) (t : Icc t₀ t₁), derivWithin (u x) (Icc t₀ t₁) t +
        (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
          ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
          c (slabMk x t) * u x t) = exp (ℓ x) * g (slabMk x t) := by
  constructor
  · intro h x t
    rw [← exp_mul_euclideanBackwardParabolicOperatorL_eq hα hℓ hdℓ hd2ℓ v hu x t, h]
  · intro h
    refine HolderSpace.ext fun p ↦ ?_
    rw [← slabMk_space_slabTime p]
    have hp := h (p : ParabolicSpaceTime _).space (slabTime p)
    rw [← exp_mul_euclideanBackwardParabolicOperatorL_eq hα hℓ hdℓ hd2ℓ v hu] at hp
    exact mul_left_cancel₀ (exp_pos _).ne' hp

/-- **The weighted terminal-value problem.** For `u = exp ℓ * v` with `v ∈ C_b^{2+α,1+α/2}` on
`ℝⁿ × [t₀, t₁]`, `f ∈ C_b^{α,α/2}` and `g ∈ C_b^{2,α}`, the terminal-data map
`v ↦ (P_back,w v, v(·, t₁))` of the conjugated backward operator sends `v` to `(f, g)` if and only
if `u` is a classical solution of the terminal-value problem `P_back u = exp ℓ * f`,
`u(·, t₁) = exp ℓ * g`: forcing terms and terminal data transform by division by the weight. -/
theorem euclideanBackwardParabolicOperatorL_prod_spatialTraceL_weightedCoeff_eq_iff
    (hℓ : ContDiff ℝ 2 ℓ) (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht) {u : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu : ∀ y (s : Icc t₀ t₁), u y s = exp (ℓ y) * v (slabMk y s))
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    (euclideanBackwardParabolicOperatorL hα a (euclideanWeightedFirstOrderCoeff a b dℓ)
        (euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ)).prod
        (spatialTraceL (F := ℝ) (hab := ht) ⟨t₁, right_mem_Icc.2 ht.le⟩) v = (f, g) ↔
      (∀ (x : EuclideanSpace ℝ ι) (t : Icc t₀ t₁), derivWithin (u x) (Icc t₀ t₁) t +
        (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
          ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
          c (slabMk x t) * u x t) = exp (ℓ x) * f (slabMk x t)) ∧
        ∀ x, u x t₁ = exp (ℓ x) * g x := by
  have hu₁ (x : EuclideanSpace ℝ ι) :
      u x t₁ = exp (ℓ x) * v.spatialTrace ⟨t₁, right_mem_Icc.2 ht.le⟩ x := by
    rw [spatialTrace_apply]
    exact hu x ⟨t₁, right_mem_Icc.2 ht.le⟩
  rw [ContinuousLinearMap.prod_apply, spatialTraceL_apply, Prod.mk.injEq,
    euclideanBackwardParabolicOperatorL_weightedCoeff_eq_iff hα hℓ hdℓ hd2ℓ v hu f]
  refine and_congr_right' ⟨fun h x ↦ by rw [hu₁, h], fun h ↦ CkHolderSpace.ext fun x ↦ ?_⟩
  exact mul_left_cancel₀ (exp_pos (ℓ x)).ne' ((hu₁ x).symm.trans (h x))

end TauCeti.ParabolicC2HolderSpace
