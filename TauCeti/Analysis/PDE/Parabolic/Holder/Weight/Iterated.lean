/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Bilinear
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Solvability
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.TimeIndependent
public import TauCeti.Analysis.PDE.Parabolic.Holder.Weight.Basic
import TauCeti.Analysis.Holder.CompLinear
import TauCeti.Analysis.Holder.Sigmoid
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Basic

/-!
# Weighted parabolic problems at every Hölder order

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have scalar coefficients in the parabolic Hölder space `C_{par,b}^{k+α}`, and let `w = exp ℓ` be a
positive time-independent weight whose logarithm `ℓ` is `C²` with partial derivatives `∂ᵢℓ` and
`∂ᵢ∂ⱼℓ` in `C_b^{k,α}`, so that the derivatives of `ℓ` of orders `1` through `k + 2` are bounded
and those of order `k + 1` and `k + 2` are `α`-Hölder. The logarithm itself may be unbounded, so
`w` may grow or decay exponentially at infinity. The **weighted class of order `k`** consists of
the maps `u` with `u / w ∈ C_{par,b}^{k+2+α}`.

For `u = w v`, the conjugation identity `P u = w P_w v` holds, where `P_w` has the same
second-order coefficients `aⁱʲ` and the coefficients

* `b_wⁱ = bⁱ + ∑ⱼ (aⁱʲ + aʲⁱ) ∂ⱼℓ`;
* `c_w = c + ∑ᵢⱼ aⁱʲ (∂ᵢ∂ⱼℓ + ∂ᵢℓ ∂ⱼℓ) + ∑ᵢ bⁱ ∂ᵢℓ`.

The derivatives of `ℓ` enter as time-independent maps (`TauCeti.CkHolderSpace.compSlabSpaceL`)
multiplied by the coefficients in the algebra `C_{par,b}^{k+α}`
(`ContinuousLinearMap.compParabolicCkHolder₂`), so `b_w` and `c_w` again lie in `C_{par,b}^{k+α}`
and the conjugated problem is a problem of the same type. The order-`k` initial-data and
terminal-data isomorphisms of `P_w`
(`TauCeti.ParabolicCkHolderSpace.euclideanInitialDataCLE`,
`TauCeti.ParabolicCkHolderSpace.euclideanTerminalDataCLE`) are therefore the solution operators of
the weighted Cauchy and terminal-value problems: for data with `F / w ∈ C_{par,b}^{k+α}` and
`G / w ∈ C_b^{k+2,α}`, each problem has exactly one solution in the weighted class of order `k`.
At `k = 0` this is the weighted theory of `C_b^{2+α,1+α/2}`
(`TauCeti.ParabolicC2HolderSpace.existsUnique_exp_mul`), now with data and solutions of every
higher order.

The estimates transport in the same way. With `M = 21 (k + 1)² 2ᵏ` the constant of the product
estimate, `‖b_wⁱ‖ ≤ ‖bⁱ‖ + 2 M ∑ⱼ (‖aⁱʲ‖ + ‖aʲⁱ‖) ‖∂ⱼℓ‖` and similarly for `c_w`, so bounds on the
coefficients and on the derivatives of `ℓ` bound the conjugated coefficients, and the Schauder
estimate of order `k` (`TauCeti.ParabolicCkHolderSpace.exists_norm_le_parabolicOperatorL`) applies
to `P_w`. If `u = w v` is a classical solution of `P u = w g`, then
`‖v‖_{k+2+α} ≤ C (‖g‖_{k+α} + ‖v(·, 0)‖_{C^{k+2,α}})`, with `C` depending only on the dimension,
`α`, `k`, the ellipticity constant, bounds on the norms of the coefficients and of the derivatives
of `ℓ`, and a bound on the horizon. The weighted solution operators of both problems are bounded
uniformly in the same quantities, and for a fixed weight they depend Lipschitz continuously on the
coefficients in operator norm, since `b_w` and `c_w` are linear in `a`, `b`, `c`.

The conjugation identity is the pointwise computation
`TauCeti.PDE.exp_mul_sum_mul_fderiv_fderiv_add_fderiv_add_mul_eq` applied to the time slices of
`v`, together with `∂ₜ(w v) = w ∂ₜv`, since `w` does not depend on time; the values of the
operators of order `k` are read classically through
`TauCeti.ParabolicCkHolderSpace.parabolicOperatorL_slabMk` and
`TauCeti.ParabolicCkHolderSpace.backwardParabolicOperatorL_slabMk`.

## Main declarations

All declarations are in the `TauCeti.ParabolicCkHolderSpace` namespace.

* `euclideanWeightedFirstOrderCoeff` and `euclideanWeightedZerothOrderCoeff`: the coefficients
  `b_w` and `c_w` of the conjugated operator, in `C_{par,b}^{k+α}`.
* `exp_mul_parabolicOperatorL_euclideanWeightedCoeff` and
  `exp_mul_backwardParabolicOperatorL_euclideanWeightedCoeff`: the conjugation identities
  `w P_w v = P (w v)` and `w P_back,w v = P_back (w v)`.
* `parabolicOperatorL_euclideanWeightedCoeff_eq_iff` and
  `backwardParabolicOperatorL_euclideanWeightedCoeff_eq_iff`: `P_w v = g` exactly when `w v` is a
  classical solution of `P u = w g`, and likewise backward.
* `eq_euclideanInitialDataCLE_symm_iff_exp_mul` and `existsUnique_exp_mul`: the weighted Cauchy
  problem of order `k` and its unique solvability.
* `eq_euclideanTerminalDataCLE_symm_iff_exp_mul` and `existsUnique_exp_mul_backward`: the same for
  the weighted terminal-value problem.
* `norm_euclideanWeightedFirstOrderCoeff_le` and `norm_euclideanWeightedZerothOrderCoeff_le`: the
  bounds on the conjugated coefficients.
* `exists_norm_le_of_eq_exp_mul`: the Schauder estimate in the weighted class of order `k`.
* `exists_norm_euclideanInitialDataCLE_weighted_symm_le` and
  `exists_norm_euclideanInitialDataCLE_weighted_symm_sub_le`: the uniform bound on the weighted
  solution operators of the Cauchy problem and their Lipschitz dependence on the coefficients.
* `exists_norm_euclideanTerminalDataCLE_weighted_symm_le` and
  `exists_norm_euclideanTerminalDataCLE_weighted_symm_sub_le`: the same for the weighted
  terminal-value problem.
* `existsUnique_one_add_exp_mul` and `existsUnique_one_add_exp_mul_backward`: on the line, both
  problems are uniquely solvable at every order in the class `u / (1 + exp x) ∈ C_{par,b}^{k+2+α}`,
  since the derivatives of `log (1 + exp x)` of every positive order, the derivatives of the
  sigmoid, lie in `C_b^{k,α}` (`TauCeti.CkHolderSpace.exists_coe_eq_iteratedDeriv_sigmoid`).

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2 (the substitution
  `u = w v` by a positive weight).
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
-/

public section

noncomputable section

namespace TauCeti.ParabolicCkHolderSpace

open Set ParabolicSpaceTime Real
open scoped NNReal

attribute [local instance] instNormedAddCommGroupContinuousLinearMapRealId
  instNormedSpaceRealContinuousLinearMapId instNormedAddCommGroupEuclideanCovector
  instNormedSpaceEuclideanCovector instNormedAddCommGroupEuclideanHessian
  instNormedSpaceEuclideanHessian

variable {k : ℕ} {α : ℝ≥0} {ι : Type*}

/-! ### The conjugated coefficients -/

section Coefficients

variable [Fintype ι] {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- The first-order coefficients `b_wⁱ = bⁱ + ∑ⱼ (aⁱʲ + aʲⁱ) ∂ⱼℓ` of the parabolic operator with
coefficients `aⁱʲ`, `bⁱ` in `C_{par,b}^{k+α}` conjugated by the weight `exp ℓ`, where `dℓ j` is the
partial derivative `∂ⱼℓ`, an element of `C_b^{k,α}` on space. -/
def euclideanWeightedFirstOrderCoeff (hα : α ≤ 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht)
    (dℓ : ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ) (i : ι) :
    ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht :=
  b i + ∑ j, (ContinuousLinearMap.mul ℝ ℝ).compParabolicCkHolder₂ hα (a i j + a j i)
    (CkHolderSpace.compSlabSpaceL ht (dℓ j))

/-- The zeroth-order coefficient `c_w = c + ∑ᵢⱼ aⁱʲ (∂ᵢ∂ⱼℓ + ∂ᵢℓ ∂ⱼℓ) + ∑ᵢ bⁱ ∂ᵢℓ` of the
parabolic operator with coefficients `aⁱʲ`, `bⁱ`, `c` in `C_{par,b}^{k+α}` conjugated by the
weight `exp ℓ`, where `dℓ i` is the partial derivative `∂ᵢℓ` and `d2ℓ i j` is `∂ᵢ∂ⱼℓ`, elements of
`C_b^{k,α}` on space. -/
def euclideanWeightedZerothOrderCoeff (hα : α ≤ 1)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht)
    (dℓ : ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ)
    (d2ℓ : ι → ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ) :
    ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht :=
  c + ∑ i, ∑ j, (ContinuousLinearMap.mul ℝ ℝ).compParabolicCkHolder₂ hα (a i j)
      (CkHolderSpace.compSlabSpaceL ht (d2ℓ i j) +
        (ContinuousLinearMap.mul ℝ ℝ).compParabolicCkHolder₂ hα
          (CkHolderSpace.compSlabSpaceL ht (dℓ i)) (CkHolderSpace.compSlabSpaceL ht (dℓ j))) +
    ∑ i, (ContinuousLinearMap.mul ℝ ℝ).compParabolicCkHolder₂ hα (b i)
      (CkHolderSpace.compSlabSpaceL ht (dℓ i))

variable {a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht}
  {b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht}
  {c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht}
  {dℓ : ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ}
  {d2ℓ : ι → ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ}

@[simp]
theorem euclideanWeightedFirstOrderCoeff_apply (hα : α ≤ 1) (i : ι)
    (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁) :
    euclideanWeightedFirstOrderCoeff hα a b dℓ i p =
      b i p + ∑ j, (a i j p + a j i p) * dℓ j (p : ParabolicSpaceTime _).space := by
  simp [euclideanWeightedFirstOrderCoeff, add_mul]

@[simp]
theorem euclideanWeightedZerothOrderCoeff_apply (hα : α ≤ 1)
    (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁) :
    euclideanWeightedZerothOrderCoeff hα a b c dℓ d2ℓ p =
      c p + ∑ i, ∑ j, a i j p * (d2ℓ i j (p : ParabolicSpaceTime _).space +
          dℓ i (p : ParabolicSpaceTime _).space * dℓ j (p : ParabolicSpaceTime _).space) +
        ∑ i, b i p * dℓ i (p : ParabolicSpaceTime _).space := by
  simp [euclideanWeightedZerothOrderCoeff, mul_add]

/-- Linearity of the conjugated first-order coefficient in the coefficients `aⁱʲ`, `bⁱ`, for a
fixed weight. -/
@[simp]
theorem euclideanWeightedFirstOrderCoeff_sub (hα : α ≤ 1)
    (a' : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht)
    (b' : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht) (i : ι) :
    euclideanWeightedFirstOrderCoeff hα (a - a') (b - b') dℓ i =
      euclideanWeightedFirstOrderCoeff hα a b dℓ i -
        euclideanWeightedFirstOrderCoeff hα a' b' dℓ i :=
  ext fun p ↦ by
    simp only [euclideanWeightedFirstOrderCoeff_apply, coe_sub, Pi.sub_apply, sub_mul, add_mul,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring

/-- Linearity of the conjugated zeroth-order coefficient in the coefficients `aⁱʲ`, `bⁱ`, `c`,
for a fixed weight. -/
@[simp]
theorem euclideanWeightedZerothOrderCoeff_sub (hα : α ≤ 1)
    (a' : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht)
    (b' : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht)
    (c' : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht) :
    euclideanWeightedZerothOrderCoeff hα (a - a') (b - b') (c - c') dℓ d2ℓ =
      euclideanWeightedZerothOrderCoeff hα a b c dℓ d2ℓ -
        euclideanWeightedZerothOrderCoeff hα a' b' c' dℓ d2ℓ :=
  ext fun p ↦ by
    simp only [euclideanWeightedZerothOrderCoeff_apply, coe_sub, Pi.sub_apply, sub_mul,
      Finset.sum_sub_distrib]
    ring

variable (a b c dℓ d2ℓ) in
/-- **Bound on the conjugated first-order coefficient.**
`‖b_wⁱ‖ ≤ ‖bⁱ‖ + 2 M ∑ⱼ (‖aⁱʲ‖ + ‖aʲⁱ‖) ‖∂ⱼℓ‖` in `C_{par,b}^{k+α}`, where `M = 21 (k + 1)² 2ᵏ` is
the constant of the product estimate `ContinuousLinearMap.norm_compParabolicCkHolder₂_le` and the
factor `2` bounds the time-independent lift of `∂ⱼℓ` to the slab
(`TauCeti.CkHolderSpace.norm_compSlabSpaceL_apply_le`). This is the order-`k` form of
`TauCeti.ParabolicC2HolderSpace.norm_euclideanWeightedFirstOrderCoeff_le`. -/
theorem norm_euclideanWeightedFirstOrderCoeff_le (hα : α ≤ 1) (i : ι) :
    ‖euclideanWeightedFirstOrderCoeff hα a b dℓ i‖ ≤
      ‖b i‖ + 2 * (21 * (k + 1) ^ 2 * 2 ^ k) * ∑ j, (‖a i j‖ + ‖a j i‖) * ‖dℓ j‖ := by
  rw [Finset.mul_sum]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun j _ ↦
      (ContinuousLinearMap.norm_mul_compParabolicCkHolder₂_apply_le hα _ _).trans ?_)))
  have h₁ := norm_add_le (a i j) (a j i)
  have h₂ := CkHolderSpace.norm_compSlabSpaceL_apply_le (hab := ht) (dℓ j)
  calc _ ≤ 21 * (k + 1) ^ 2 * 2 ^ k * ((‖a i j‖ + ‖a j i‖) * (2 * ‖dℓ j‖)) := by gcongr
    _ = _ := by ring

variable (a b c dℓ d2ℓ) in
/-- **Bound on the conjugated zeroth-order coefficient.**
`‖c_w‖ ≤ ‖c‖ + 2 M ∑ᵢⱼ ‖aⁱʲ‖ (‖∂ᵢ∂ⱼℓ‖ + 2 M ‖∂ᵢℓ‖ ‖∂ⱼℓ‖) + 2 M ∑ᵢ ‖bⁱ‖ ‖∂ᵢℓ‖` in
`C_{par,b}^{k+α}`, with `M = 21 (k + 1)² 2ᵏ` as in `norm_euclideanWeightedFirstOrderCoeff_le`.
This is the order-`k` form of
`TauCeti.ParabolicC2HolderSpace.norm_euclideanWeightedZerothOrderCoeff_le`. -/
theorem norm_euclideanWeightedZerothOrderCoeff_le (hα : α ≤ 1) :
    ‖euclideanWeightedZerothOrderCoeff hα a b c dℓ d2ℓ‖ ≤
      ‖c‖ + 2 * (21 * (k + 1) ^ 2 * 2 ^ k) * ∑ i, ∑ j, ‖a i j‖ *
          (‖d2ℓ i j‖ + 2 * (21 * (k + 1) ^ 2 * 2 ^ k) * (‖dℓ i‖ * ‖dℓ j‖)) +
        2 * (21 * (k + 1) ^ 2 * 2 ^ k) * ∑ i, ‖b i‖ * ‖dℓ i‖ := by
  set M : ℝ := 21 * (k + 1) ^ 2 * 2 ^ k
  have hS (f : CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ) :=
    CkHolderSpace.norm_compSlabSpaceL_apply_le (hab := ht) f
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)
  · rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦
      (ContinuousLinearMap.norm_mul_compParabolicCkHolder₂_apply_le hα _ _).trans ?_)
    -- The second factor is `∂ᵢ∂ⱼℓ + ∂ᵢℓ ∂ⱼℓ`, lifted to the slab.
    have h : ‖CkHolderSpace.compSlabSpaceL ht (d2ℓ i j) +
        (ContinuousLinearMap.mul ℝ ℝ).compParabolicCkHolder₂ hα
          (CkHolderSpace.compSlabSpaceL ht (dℓ i)) (CkHolderSpace.compSlabSpaceL ht (dℓ j))‖ ≤
        2 * (‖d2ℓ i j‖ + 2 * M * (‖dℓ i‖ * ‖dℓ j‖)) := by
      refine (norm_add_le _ _).trans ?_
      calc _ ≤ 2 * ‖d2ℓ i j‖ + M * ((2 * ‖dℓ i‖) * (2 * ‖dℓ j‖)) :=
            add_le_add (hS _)
              ((ContinuousLinearMap.norm_mul_compParabolicCkHolder₂_apply_le hα _ _).trans
                (by gcongr <;> exact hS _))
        _ = _ := by ring
    calc _ ≤ M * (‖a i j‖ * (2 * (‖d2ℓ i j‖ + 2 * M * (‖dℓ i‖ * ‖dℓ j‖)))) := by gcongr
      _ = _ := by ring
  · rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦
      (ContinuousLinearMap.norm_mul_compParabolicCkHolder₂_apply_le hα _ _).trans ?_)
    calc _ ≤ M * (‖b i‖ * (2 * ‖dℓ i‖)) := by gcongr; exact hS _
      _ = _ := by ring

end Coefficients

/-! ### The conjugation identities -/

section Conjugation

variable [Fintype ι] [DecidableEq ι] {t₀ t₁ : ℝ} {ht : t₀ < t₁} (hα : α ≤ 1)
  {a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht}
  {b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht}
  {c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht}
  {dℓ : ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ}
  {d2ℓ : ι → ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ} {ℓ : EuclideanSpace ℝ ι → ℝ}

omit [DecidableEq ι] in
/-- The time derivative of a weighted map within the slab: if `u (y, s) = exp (ℓ y) * v (y, s)`,
then `∂ₜu (x, t) = exp (ℓ x) * ∂ₜv (x, t)`, also at the initial and terminal times. -/
private theorem derivWithin_eq_exp_mul
    (v : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ ht)
    {u : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu : ∀ y (s : Icc t₀ t₁), u y s = exp (ℓ y) * v (slabMk y s))
    (x : EuclideanSpace ℝ ι) (t : Icc t₀ t₁) :
    derivWithin (u x) (Icc t₀ t₁) t =
      exp (ℓ x) * derivWithin (ParabolicC2HolderSpace.timeExtension ht.le v x) (Icc t₀ t₁) t := by
  have hv := v.hasTimeDerivWithinAt x t
  have hu' : HasDerivWithinAt (u x) (exp (ℓ x) * timeDerivL k α _ ℝ ht v (slabMk x t))
      (Icc t₀ t₁) t :=
    (hv.const_mul (exp (ℓ x))).congr_of_mem (fun s hs ↦ by
      rw [ParabolicC2HolderSpace.timeExtension_of_mem ht.le _ x ⟨s, hs⟩]
      exact hu x ⟨s, hs⟩) t.property
  rw [hu'.derivWithin (uniqueDiffOn_Icc ht t t.property),
    hv.derivWithin (uniqueDiffOn_Icc ht t t.property)]

include hα

/-- **Conjugation by a spatial weight at every order.** Let `ℓ` be `C²` on `ℝⁿ`, with partial
derivatives `∂ᵢℓ = dℓ i` and `∂ᵢ∂ⱼℓ = d2ℓ i j` in `C_b^{k,α}`, and let `u = exp ℓ * v` on the slab
for some `v ∈ C_{par,b}^{k+2+α}`. Then the classical parabolic operator
`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u` is `exp ℓ` times the operator `P_w v` with coefficients
`aⁱʲ`, `b_wⁱ` (`euclideanWeightedFirstOrderCoeff`) and `c_w` (`euclideanWeightedZerothOrderCoeff`)
applied to `v`. The time derivative of `u` is taken within the closed time interval, so the
identity also holds at the initial and terminal times. -/
theorem exp_mul_parabolicOperatorL_euclideanWeightedCoeff (hℓ : ContDiff ℝ 2 ℓ)
    (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (v : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ ht)
    {u : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu : ∀ y (s : Icc t₀ t₁), u y s = exp (ℓ y) * v (slabMk y s))
    (x : EuclideanSpace ℝ ι) (t : Icc t₀ t₁) :
    exp (ℓ x) * parabolicOperatorL hα (euclideanSecondOrderCoeff a)
        (euclideanFirstOrderCoeff (euclideanWeightedFirstOrderCoeff hα a b dℓ))
        (euclideanZerothOrderCoeff (euclideanWeightedZerothOrderCoeff hα a b c dℓ d2ℓ)) v
        (slabMk x t) =
      derivWithin (u x) (Icc t₀ t₁) t -
        (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
          ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
          c (slabMk x t) * u x t) := by
  have hslice : (fun y ↦ u y t) = fun y ↦ exp (ℓ y) * v (slabMk y t) := funext fun y ↦ hu y t
  -- The spatial part is the pointwise conjugation identity applied to the slice of `v` at `t`.
  have hspace := PDE.exp_mul_sum_mul_fderiv_fderiv_add_fderiv_add_mul_eq
    (Matrix.of fun i j ↦ a i j (slabMk x t)) (∑ i, b i (slabMk x t) • EuclideanSpace.single i 1)
    (c (slabMk x t)) (hℓ.contDiffAt (x := x))
    ((v.contDiff_spatialSlice t).of_le (by exact_mod_cast Nat.le_add_left 2 k)).contDiffAt
  rw [parabolicOperatorL_slabMk, mul_sub, ← derivWithin_eq_exp_mul v hu, hslice, hu x t]
  simp only [euclideanSecondOrderCoeff_apply, euclideanFirstOrderCoeff_apply,
    euclideanZerothOrderCoeff_apply, euclideanWeightedFirstOrderCoeff_apply,
    euclideanWeightedZerothOrderCoeff_apply, space_slabMk, hdℓ, hd2ℓ, Matrix.of_apply, map_add,
    map_sum, map_smul, smul_eq_mul, add_mul, Finset.sum_add_distrib] at hspace ⊢
  linear_combination -hspace

/-- **Conjugation of the backward operator by a spatial weight at every order.** Under the
hypotheses of `exp_mul_parabolicOperatorL_euclideanWeightedCoeff`, the backward operator
`P_back u = ∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u` applied to `u = exp ℓ * v` is `exp ℓ` times the
backward operator with the conjugated coefficients `aⁱʲ`, `b_wⁱ`, `c_w` applied to `v`. -/
theorem exp_mul_backwardParabolicOperatorL_euclideanWeightedCoeff (hℓ : ContDiff ℝ 2 ℓ)
    (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (v : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ ht)
    {u : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu : ∀ y (s : Icc t₀ t₁), u y s = exp (ℓ y) * v (slabMk y s))
    (x : EuclideanSpace ℝ ι) (t : Icc t₀ t₁) :
    exp (ℓ x) * backwardParabolicOperatorL hα (euclideanSecondOrderCoeff a)
        (euclideanFirstOrderCoeff (euclideanWeightedFirstOrderCoeff hα a b dℓ))
        (euclideanZerothOrderCoeff (euclideanWeightedZerothOrderCoeff hα a b c dℓ d2ℓ)) v
        (slabMk x t) =
      derivWithin (u x) (Icc t₀ t₁) t +
        (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
          ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
          c (slabMk x t) * u x t) := by
  -- Since the weight does not depend on time, `P_back,w v = 2 ∂ₜv - P_w v`, and likewise for `u`.
  have hfwd := exp_mul_parabolicOperatorL_euclideanWeightedCoeff hα (a := a) (b := b) (c := c)
    hℓ hdℓ hd2ℓ v hu x t
  have htime := derivWithin_eq_exp_mul v hu x t
  rw [parabolicOperatorL_slabMk] at hfwd
  rw [backwardParabolicOperatorL_slabMk]
  linear_combination (-2) * htime - hfwd

/-- **Weighted solutions at every order.** For `u = exp ℓ * v` with `v ∈ C_{par,b}^{k+2+α}`, `v`
solves the conjugated equation `P_w v = g` if and only if `u` is a classical solution of
`P u = exp ℓ * g`, with the time derivative of `u` taken within the closed time interval: forcing
terms transform by division by the weight. -/
theorem parabolicOperatorL_euclideanWeightedCoeff_eq_iff (hℓ : ContDiff ℝ 2 ℓ)
    (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (v : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ ht)
    {u : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu : ∀ y (s : Icc t₀ t₁), u y s = exp (ℓ y) * v (slabMk y s))
    (g : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht) :
    parabolicOperatorL hα (euclideanSecondOrderCoeff a)
        (euclideanFirstOrderCoeff (euclideanWeightedFirstOrderCoeff hα a b dℓ))
        (euclideanZerothOrderCoeff (euclideanWeightedZerothOrderCoeff hα a b c dℓ d2ℓ)) v = g ↔
      ∀ (x : EuclideanSpace ℝ ι) (t : Icc t₀ t₁), derivWithin (u x) (Icc t₀ t₁) t -
        (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
          ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
          c (slabMk x t) * u x t) = exp (ℓ x) * g (slabMk x t) := by
  constructor
  · intro h x t
    rw [← exp_mul_parabolicOperatorL_euclideanWeightedCoeff hα hℓ hdℓ hd2ℓ v hu x t, h]
  · intro h
    refine ext fun p ↦ ?_
    rw [← slabMk_space_slabTime p]
    have hp := h (p : ParabolicSpaceTime _).space (slabTime p)
    rw [← exp_mul_parabolicOperatorL_euclideanWeightedCoeff hα hℓ hdℓ hd2ℓ v hu] at hp
    exact mul_left_cancel₀ (exp_pos _).ne' hp

/-- **Weighted solutions of the backward equation at every order.** For `u = exp ℓ * v` with
`v ∈ C_{par,b}^{k+2+α}`, `v` solves the conjugated backward equation `P_back,w v = g` if and only
if `u` is a classical solution of `P_back u = exp ℓ * g`. -/
theorem backwardParabolicOperatorL_euclideanWeightedCoeff_eq_iff (hℓ : ContDiff ℝ 2 ℓ)
    (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (v : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ ht)
    {u : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu : ∀ y (s : Icc t₀ t₁), u y s = exp (ℓ y) * v (slabMk y s))
    (g : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht) :
    backwardParabolicOperatorL hα (euclideanSecondOrderCoeff a)
        (euclideanFirstOrderCoeff (euclideanWeightedFirstOrderCoeff hα a b dℓ))
        (euclideanZerothOrderCoeff (euclideanWeightedZerothOrderCoeff hα a b c dℓ d2ℓ)) v = g ↔
      ∀ (x : EuclideanSpace ℝ ι) (t : Icc t₀ t₁), derivWithin (u x) (Icc t₀ t₁) t +
        (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
          ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
          c (slabMk x t) * u x t) = exp (ℓ x) * g (slabMk x t) := by
  constructor
  · intro h x t
    rw [← exp_mul_backwardParabolicOperatorL_euclideanWeightedCoeff hα hℓ hdℓ hd2ℓ v hu x t, h]
  · intro h
    refine ext fun p ↦ ?_
    rw [← slabMk_space_slabTime p]
    have hp := h (p : ParabolicSpaceTime _).space (slabTime p)
    rw [← exp_mul_backwardParabolicOperatorL_euclideanWeightedCoeff hα hℓ hdℓ hd2ℓ v hu] at hp
    exact mul_left_cancel₀ (exp_pos _).ne' hp

end Conjugation

/-! ### The weighted Cauchy and terminal-value problems -/

section Solution

variable [Fintype ι] [DecidableEq ι] {T : ℝ≥0} {dℓ : ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ}
  {d2ℓ : ι → ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ} {ℓ : EuclideanSpace ℝ ι → ℝ}

/-- **The weighted Cauchy problem at every order.** Let `w = exp ℓ` be a spatial weight whose
logarithm `ℓ` is `C²` with partial derivatives `∂ᵢℓ = dℓ i` and `∂ᵢ∂ⱼℓ = d2ℓ i j` in `C_b^{k,α}`;
`ℓ` itself may be unbounded. Let `v ∈ C_{par,b}^{k+2+α}` and `u = w v`, and let
`f ∈ C_{par,b}^{k+α}` and `g ∈ C_b^{k+2,α}`. Then `u` is a classical solution of the Cauchy
problem `P u = w f`, `u(·, 0) = w g` if and only if `v` is the image of `(f, g)` under the inverse
of the order-`k` initial-data isomorphism of the conjugated operator `P_w`. -/
theorem eq_euclideanInitialDataCLE_symm_iff_exp_mul (hα₀ : 0 < α) (hα₁ : α < 1)
    {hT : (0 : ℝ) < T} {a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT}
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (hℓ : ContDiff ℝ 2 ℓ) (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (v : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT)
    {u : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu : ∀ y (s : Icc (0 : ℝ) T), u y s = exp (ℓ y) * v (slabMk y s))
    (f : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (g : CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ) :
    v = (euclideanInitialDataCLE hα₀ hα₁ a (euclideanWeightedFirstOrderCoeff hα₁.le a b dℓ)
        (euclideanWeightedZerothOrderCoeff hα₁.le a b c dℓ d2ℓ) ha).symm (f, g) ↔
      (∀ (x : EuclideanSpace ℝ ι) (t : Icc (0 : ℝ) T), derivWithin (u x) (Icc 0 T) t -
        (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
          ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
          c (slabMk x t) * u x t) = exp (ℓ x) * f (slabMk x t)) ∧
        ∀ x, u x 0 = exp (ℓ x) * g x := by
  have hu₀ (x : EuclideanSpace ℝ ι) :
      u x 0 = exp (ℓ x) * v.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ x := by
    rw [spatialTrace_apply]
    exact hu x ⟨0, left_mem_Icc.2 hT.le⟩
  rw [ContinuousLinearEquiv.eq_symm_apply, euclideanInitialDataCLE_apply, initialDataL_apply,
    Prod.mk.injEq, parabolicOperatorL_euclideanWeightedCoeff_eq_iff hα₁.le hℓ hdℓ hd2ℓ v hu]
  refine and_congr_right' ⟨fun h x ↦ by rw [hu₀, h], fun h ↦ CkHolderSpace.ext fun x ↦ ?_⟩
  exact mul_left_cancel₀ (exp_pos (ℓ x)).ne' ((hu₀ x).symm.trans (h x))

/-- **Unique solvability of the weighted Cauchy problem at every order.** Let `w = exp ℓ` be a
spatial weight as in `eq_euclideanInitialDataCLE_symm_iff_exp_mul`. For coefficients in
`C_{par,b}^{k+α}` with `a` uniformly elliptic and data `f ∈ C_{par,b}^{k+α}`, `g ∈ C_b^{k+2,α}`,
there is exactly one `v ∈ C_{par,b}^{k+2+α}` such that `u = w v` is a classical solution of
`P u = w f`, `u(·, 0) = w g`. -/
theorem existsUnique_exp_mul (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    {a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT}
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (hℓ : ContDiff ℝ 2 ℓ) (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (f : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (g : CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ) :
    ∃! v : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT,
      ∀ u : EuclideanSpace ℝ ι → ℝ → ℝ,
        (∀ y (s : Icc (0 : ℝ) T), u y s = exp (ℓ y) * v (slabMk y s)) →
        (∀ (x : EuclideanSpace ℝ ι) (t : Icc (0 : ℝ) T), derivWithin (u x) (Icc 0 T) t -
          (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
              (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
            ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
            c (slabMk x t) * u x t) = exp (ℓ x) * f (slabMk x t)) ∧
          ∀ x, u x 0 = exp (ℓ x) * g x := by
  have key (v : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT)
      (u : EuclideanSpace ℝ ι → ℝ → ℝ)
      (hu : ∀ y (s : Icc (0 : ℝ) T), u y s = exp (ℓ y) * v (slabMk y s)) :=
    eq_euclideanInitialDataCLE_symm_iff_exp_mul hα₀ hα₁ b c ha hℓ hdℓ hd2ℓ v hu f g
  refine ⟨_, fun u hu ↦ (key _ u hu).1 rfl, fun v hv ↦ ?_⟩
  have hext (y : EuclideanSpace ℝ ι) (s : Icc (0 : ℝ) T) :
      exp (ℓ y) * ParabolicC2HolderSpace.timeExtension hT.le v y s =
        exp (ℓ y) * v (slabMk y s) := by
    rw [ParabolicC2HolderSpace.timeExtension_of_mem]
  exact (key v (fun y s ↦ exp (ℓ y) * ParabolicC2HolderSpace.timeExtension hT.le v y s) hext).2
    (hv _ hext)

/-- **The weighted terminal-value problem at every order.** Let `w = exp ℓ` be a spatial weight as
in `eq_euclideanInitialDataCLE_symm_iff_exp_mul`. Let `v ∈ C_{par,b}^{k+2+α}` and `u = w v`, and
let `f ∈ C_{par,b}^{k+α}` and `g ∈ C_b^{k+2,α}`. Then `u` is a classical solution of the
terminal-value problem `∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u = w f`, `u(·, T) = w g` if and only if `v`
is the image of `(f, g)` under the inverse of the order-`k` terminal-data isomorphism of the
conjugated backward operator. -/
theorem eq_euclideanTerminalDataCLE_symm_iff_exp_mul (hα₀ : 0 < α) (hα₁ : α < 1)
    {hT : (0 : ℝ) < T} {a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT}
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (hℓ : ContDiff ℝ 2 ℓ) (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (v : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT)
    {u : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu : ∀ y (s : Icc (0 : ℝ) T), u y s = exp (ℓ y) * v (slabMk y s))
    (f : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (g : CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ) :
    v = (euclideanTerminalDataCLE hα₀ hα₁ a (euclideanWeightedFirstOrderCoeff hα₁.le a b dℓ)
        (euclideanWeightedZerothOrderCoeff hα₁.le a b c dℓ d2ℓ) ha).symm (f, g) ↔
      (∀ (x : EuclideanSpace ℝ ι) (t : Icc (0 : ℝ) T), derivWithin (u x) (Icc 0 T) t +
        (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
          ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
          c (slabMk x t) * u x t) = exp (ℓ x) * f (slabMk x t)) ∧
        ∀ x, u x T = exp (ℓ x) * g x := by
  have hu₁ (x : EuclideanSpace ℝ ι) :
      u x T = exp (ℓ x) * v.spatialTrace ⟨T, right_mem_Icc.2 hT.le⟩ x := by
    rw [spatialTrace_apply]
    exact hu x ⟨T, right_mem_Icc.2 hT.le⟩
  rw [ContinuousLinearEquiv.eq_symm_apply, euclideanTerminalDataCLE_apply, terminalDataL_def,
    ContinuousLinearMap.prod_apply, spatialTraceL_apply, Prod.mk.injEq,
    backwardParabolicOperatorL_euclideanWeightedCoeff_eq_iff hα₁.le hℓ hdℓ hd2ℓ v hu]
  refine and_congr_right' ⟨fun h x ↦ by rw [hu₁, h], fun h ↦ CkHolderSpace.ext fun x ↦ ?_⟩
  exact mul_left_cancel₀ (exp_pos (ℓ x)).ne' ((hu₁ x).symm.trans (h x))

/-- **Unique solvability of the weighted terminal-value problem at every order.** Let `w = exp ℓ`
be a spatial weight as in `eq_euclideanInitialDataCLE_symm_iff_exp_mul`. For coefficients in
`C_{par,b}^{k+α}` with `a` uniformly elliptic and data `f ∈ C_{par,b}^{k+α}`, `g ∈ C_b^{k+2,α}`,
there is exactly one `v ∈ C_{par,b}^{k+2+α}` such that `u = w v` is a classical solution of
`∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u = w f`, `u(·, T) = w g`. -/
theorem existsUnique_exp_mul_backward (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    {a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT}
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (hℓ : ContDiff ℝ 2 ℓ) (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (f : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (g : CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ) :
    ∃! v : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT,
      ∀ u : EuclideanSpace ℝ ι → ℝ → ℝ,
        (∀ y (s : Icc (0 : ℝ) T), u y s = exp (ℓ y) * v (slabMk y s)) →
        (∀ (x : EuclideanSpace ℝ ι) (t : Icc (0 : ℝ) T), derivWithin (u x) (Icc 0 T) t +
          (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
              (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
            ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
            c (slabMk x t) * u x t) = exp (ℓ x) * f (slabMk x t)) ∧
          ∀ x, u x T = exp (ℓ x) * g x := by
  have key (v : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT)
      (u : EuclideanSpace ℝ ι → ℝ → ℝ)
      (hu : ∀ y (s : Icc (0 : ℝ) T), u y s = exp (ℓ y) * v (slabMk y s)) :=
    eq_euclideanTerminalDataCLE_symm_iff_exp_mul hα₀ hα₁ b c ha hℓ hdℓ hd2ℓ v hu f g
  refine ⟨_, fun u hu ↦ (key _ u hu).1 rfl, fun v hv ↦ ?_⟩
  have hext (y : EuclideanSpace ℝ ι) (s : Icc (0 : ℝ) T) :
      exp (ℓ y) * ParabolicC2HolderSpace.timeExtension hT.le v y s =
        exp (ℓ y) * v (slabMk y s) := by
    rw [ParabolicC2HolderSpace.timeExtension_of_mem]
  exact (key v (fun y s ↦ exp (ℓ y) * ParabolicC2HolderSpace.timeExtension hT.le v y s) hext).2
    (hv _ hext)

end Solution

/-! ### Estimates -/

section Estimates

variable [Fintype ι]

variable (ι) in
/-- The bound `K (1 + 6 n M L + 2 n² M (L + 2 M L²))` on the coefficients of the conjugated
operator of order `k`, where `K` bounds the coefficients, `L` bounds the derivatives of the
logarithm of the weight, `n` is the dimension and `M = 21 (k + 1)² 2ᵏ` is the constant of the
product estimate. -/
private def weightedCoeffBound (k : ℕ) (K L : ℝ≥0) : ℝ≥0 :=
  K * (1 + 6 * Fintype.card ι * (21 * (k + 1) ^ 2 * 2 ^ k) * L +
    2 * Fintype.card ι ^ 2 * (21 * (k + 1) ^ 2 * 2 ^ k) *
      (L + 2 * (21 * (k + 1) ^ 2 * 2 ^ k) * L * L))

/-- The coefficients `aⁱʲ` and the weighted coefficients of order `k` are bounded by
`weightedCoeffBound ι k K L` when the coefficients are bounded by `K` and the derivatives of the
logarithm of the weight by `L`. -/
private theorem norm_weightedCoeff_le (hα : α ≤ 1) {t₀ t₁ : ℝ} {ht : t₀ < t₁} {K L : ℝ≥0}
    {a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht}
    {b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht}
    {c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht}
    {dℓ : ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ}
    {d2ℓ : ι → ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ}
    (hak : ∀ i j, ‖a i j‖ ≤ K) (hbk : ∀ i, ‖b i‖ ≤ K) (hck : ‖c‖ ≤ K)
    (hdℓ : ∀ i, ‖dℓ i‖ ≤ L) (hd2ℓ : ∀ i j, ‖d2ℓ i j‖ ≤ L) :
    (∀ i j, ‖a i j‖ ≤ weightedCoeffBound ι k K L) ∧
      (∀ i, ‖euclideanWeightedFirstOrderCoeff hα a b dℓ i‖ ≤ weightedCoeffBound ι k K L) ∧
      ‖euclideanWeightedZerothOrderCoeff hα a b c dℓ d2ℓ‖ ≤ weightedCoeffBound ι k K L := by
  set M : ℝ := 21 * (k + 1) ^ 2 * 2 ^ k
  set n : ℝ := (Fintype.card ι : ℝ)
  have hB : (weightedCoeffBound ι k K L : ℝ) =
      K * (1 + 6 * n * M * L + 2 * n ^ 2 * M * (L + 2 * M * L * L)) := by
    simp only [weightedCoeffBound, M, n]
    push_cast
    ring
  have hK : (0 : ℝ) ≤ K := K.property
  have hL : (0 : ℝ) ≤ L := L.property
  have hM : 0 ≤ M := by positivity
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hb (i : ι) :
      ‖euclideanWeightedFirstOrderCoeff hα a b dℓ i‖ ≤ K + 2 * M * (n * (2 * K * L)) := by
    refine (norm_euclideanWeightedFirstOrderCoeff_le a b dℓ hα i).trans
      (add_le_add (hbk i) (mul_le_mul_of_nonneg_left ?_ (by positivity)))
    calc ∑ j, (‖a i j‖ + ‖a j i‖) * ‖dℓ j‖ ≤ ∑ _j : ι, 2 * (K : ℝ) * L :=
          Finset.sum_le_sum fun j _ ↦ by
            nlinarith [hak i j, hak j i, hdℓ j, norm_nonneg (dℓ j), norm_nonneg (a i j)]
      _ = _ := by simp [n]
  have hc : ‖euclideanWeightedZerothOrderCoeff hα a b c dℓ d2ℓ‖ ≤
      K + 2 * M * (n * (n * (K * (L + 2 * M * (L * L))))) + 2 * M * (n * (K * L)) := by
    refine (norm_euclideanWeightedZerothOrderCoeff_le a b c dℓ d2ℓ hα).trans
      (add_le_add (add_le_add hck (mul_le_mul_of_nonneg_left ?_ (by positivity)))
        (mul_le_mul_of_nonneg_left ?_ (by positivity)))
    · calc ∑ i, ∑ j, ‖a i j‖ * (‖d2ℓ i j‖ + 2 * M * (‖dℓ i‖ * ‖dℓ j‖)) ≤
            ∑ _i : ι, ∑ _j : ι, (K : ℝ) * (L + 2 * M * (L * L)) :=
            Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ by
              gcongr
              · exact hak i j
              · exact hd2ℓ i j
              · exact hdℓ i
              · exact hdℓ j
        _ = _ := by simp [n]
    · calc ∑ i, ‖b i‖ * ‖dℓ i‖ ≤ ∑ _i : ι, (K : ℝ) * L :=
            Finset.sum_le_sum fun i _ ↦ by gcongr; exacts [hbk i, hdℓ i]
        _ = _ := by simp [n]
  rw [hB]
  refine ⟨fun i j ↦ (hak i j).trans (le_mul_of_one_le_right hK ?_), fun i ↦ (hb i).trans ?_,
    hc.trans ?_⟩
  · nlinarith [mul_nonneg (mul_nonneg hn hM) hL,
      mul_nonneg (mul_nonneg (sq_nonneg n) hM) (by positivity : 0 ≤ L + 2 * M * L * L)]
  · rw [show K * (1 + 6 * n * M * L + 2 * n ^ 2 * M * (L + 2 * M * L * L)) =
      (K + 2 * M * (n * (2 * K * L))) + K * (2 * n * M * L + 2 * n ^ 2 * M * (L + 2 * M * L * L))
      by ring]
    exact le_add_of_nonneg_right (by positivity)
  · rw [show K * (1 + 6 * n * M * L + 2 * n ^ 2 * M * (L + 2 * M * L * L)) =
      (K + 2 * M * (n * (n * (K * (L + 2 * M * (L * L))))) + 2 * M * (n * (K * L))) +
        K * (4 * n * M * L) by ring]
    exact le_add_of_nonneg_right (by positivity)

/-- For a fixed weight whose logarithm has derivatives bounded by `L`, the total distance between
the coefficient triples `(a, b_w, c_w)` and `(a', b'_w, c'_w)` of two conjugated operators of order
`k` is at most `1 + 6 M L + 4 M² L²` times the total distance between `(a, b, c)` and
`(a', b', c')`, where `M = 21 (k + 1)² 2ᵏ`. -/
private theorem weightedCoeff_sub_le_mul (hα : α ≤ 1) {t₀ t₁ : ℝ} {ht : t₀ < t₁} {L : ℝ≥0}
    {a a' : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht}
    {b b' : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht}
    {c c' : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ ht}
    {dℓ : ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ}
    {d2ℓ : ι → ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ}
    (hdℓ : ∀ i, ‖dℓ i‖ ≤ L) (hd2ℓ : ∀ i j, ‖d2ℓ i j‖ ≤ L) :
    ∑ i, ∑ j, ‖a i j - a' i j‖ +
        ∑ i, ‖euclideanWeightedFirstOrderCoeff hα a b dℓ i -
          euclideanWeightedFirstOrderCoeff hα a' b' dℓ i‖ +
        ‖euclideanWeightedZerothOrderCoeff hα a b c dℓ d2ℓ -
          euclideanWeightedZerothOrderCoeff hα a' b' c' dℓ d2ℓ‖ ≤
      (1 + 6 * (21 * (k + 1) ^ 2 * 2 ^ k) * L + 4 * (21 * (k + 1) ^ 2 * 2 ^ k) ^ 2 * L ^ 2) *
        (∑ i, ∑ j, ‖a i j - a' i j‖ + ∑ i, ‖b i - b' i‖ + ‖c - c'‖) := by
  set M : ℝ := 21 * (k + 1) ^ 2 * 2 ^ k
  set A := ∑ i, ∑ j, ‖a i j - a' i j‖
  set B := ∑ i, ‖b i - b' i‖
  -- The weighted coefficients are linear in `a`, `b`, `c`, so their differences are the weighted
  -- coefficients of the differences.
  have hbw : ∑ i, ‖euclideanWeightedFirstOrderCoeff hα a b dℓ i -
      euclideanWeightedFirstOrderCoeff hα a' b' dℓ i‖ ≤ B + 4 * M * L * A := by
    calc _ ≤ ∑ i, (‖b i - b' i‖ +
          2 * M * ∑ j, (‖a i j - a' i j‖ + ‖a j i - a' j i‖) * L) :=
          Finset.sum_le_sum fun i _ ↦ by
            rw [← euclideanWeightedFirstOrderCoeff_sub]
            refine (norm_euclideanWeightedFirstOrderCoeff_le _ _ _ hα i).trans
              (add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦
                mul_le_mul_of_nonneg_left (hdℓ j) (by positivity)) (by positivity)))
      _ = _ := by
          have hswap : ∑ i, ∑ j, ‖a j i - a' j i‖ = A := Finset.sum_comm
          simp only [Finset.sum_add_distrib, add_mul, ← Finset.sum_mul, ← Finset.mul_sum, hswap]
          ring
  have hcw : ‖euclideanWeightedZerothOrderCoeff hα a b c dℓ d2ℓ -
      euclideanWeightedZerothOrderCoeff hα a' b' c' dℓ d2ℓ‖ ≤
        ‖c - c'‖ + 2 * M * (L + 2 * M * (L * L)) * A + 2 * M * L * B := by
    rw [← euclideanWeightedZerothOrderCoeff_sub]
    refine (norm_euclideanWeightedZerothOrderCoeff_le _ _ _ _ _ hα).trans ?_
    simp only [Pi.sub_apply]
    have h₁ : ∑ i, ∑ j, ‖a i j - a' i j‖ * (‖d2ℓ i j‖ + 2 * M * (‖dℓ i‖ * ‖dℓ j‖)) ≤
        (L + 2 * M * (L * L)) * A := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ ↦ ?_
      rw [mul_comm]
      gcongr
      · exact hd2ℓ i j
      · exact hdℓ i
      · exact hdℓ j
    have h₂ : ∑ i, ‖b i - b' i‖ * ‖dℓ i‖ ≤ L * B := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ ↦ by rw [mul_comm]; gcongr; exact hdℓ i
    calc _ ≤ ‖c - c'‖ + 2 * M * ((L + 2 * M * (L * L)) * A) + 2 * M * (L * B) := by
          gcongr
      _ = _ := by ring
  refine (add_le_add (add_le_add le_rfl hbw) hcw).trans (sub_nonneg.1 ?_)
  -- The terms in `A`, `B` and `‖c - c'‖` leave nonnegative multiples.
  rw [show (1 + 6 * M * L + 4 * M ^ 2 * L ^ 2) * (A + B + ‖c - c'‖) -
      (A + (B + 4 * M * L * A) + (‖c - c'‖ + 2 * M * (L + 2 * M * (L * L)) * A + 2 * M * L * B)) =
        (4 * M * L + 4 * M ^ 2 * L ^ 2) * B + (6 * M * L + 4 * M ^ 2 * L ^ 2) * ‖c - c'‖ by ring]
  positivity

variable [DecidableEq ι]

/-- **The Schauder estimate in a weighted class at every order.** For `0 < α < 1`, `k : ℕ`, an
ellipticity constant `λ > 0`, a bound `K` on the norms of the coefficients in `C_{par,b}^{k+α}`, a
bound `L` on the norms of the partial derivatives `∂ᵢℓ` and `∂ᵢ∂ⱼℓ` of the logarithm of the weight
in `C_b^{k,α}`, and a bound `T₀` on the horizon, there is a constant `C` with the following
property. On `ℝⁿ × [0, T]`, `T ≤ T₀`, let `u = exp ℓ * v` with `v ∈ C_{par,b}^{k+2+α}`, and let `u`
be a classical solution of `P u = exp ℓ * g` with `g ∈ C_{par,b}^{k+α}`, where
`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`. Then
`‖v‖_{k+2+α} ≤ C (‖g‖_{k+α} + ‖v(·, 0)‖_{C^{k+2,α}})`, that is
`‖u / w‖_{k+2+α} ≤ C (‖P u / w‖_{k+α} + ‖u(·, 0) / w‖_{C^{k+2,α}})`. The weight itself enters only
through `L`. This is the order-`k` form of
`TauCeti.ParabolicC2HolderSpace.exists_norm_le_of_eq_exp_mul`. -/
theorem exists_norm_le_of_eq_exp_mul (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ} (hlam : 0 < lam)
    (k : ℕ) (K L T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT),
        (∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
      ∀ (dℓ : ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ)
        (d2ℓ : ι → ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ),
        (∀ i, ‖dℓ i‖ ≤ L) → (∀ i j, ‖d2ℓ i j‖ ≤ L) →
      ∀ ℓ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ 2 ℓ →
        (∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x) →
        (∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) = d2ℓ i j x) →
      ∀ (v : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT)
        (u : EuclideanSpace ℝ ι → ℝ → ℝ)
        (g : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT),
        (∀ y (s : Icc (0 : ℝ) T), u y s = exp (ℓ y) * v (slabMk y s)) →
        (∀ x (t : Icc (0 : ℝ) T), derivWithin (u x) (Icc 0 T) t -
          (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
              (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
            ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
            c (slabMk x t) * u x t) = exp (ℓ x) * g (slabMk x t)) →
        ‖v‖ ≤ C * (‖g‖ + ‖v.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖) := by
  obtain ⟨C, hC, hest⟩ := exists_norm_le_parabolicOperatorL (ι := ι) hα₀ hα₁ hlam k
    (weightedCoeffBound ι k K L) T₀
  refine ⟨C, hC, fun T hT hTT₀ a b c ha hak hbk hck dℓ d2ℓ hdk hd2k ℓ hℓ hdℓ hd2ℓ v u g hu hP ↦ ?_⟩
  obtain ⟨ha', hb, hc⟩ := norm_weightedCoeff_le hα₁.le hak hbk hck hdk hd2k
  -- The classical equation for `u` is the conjugated equation `P_w v = g` for `v`.
  have hPv := (parabolicOperatorL_euclideanWeightedCoeff_eq_iff hα₁.le hℓ hdℓ hd2ℓ v hu g).2 hP
  have h := hest T hT hTT₀ a _ _ ha ha' hb hc v
  rwa [hPv] at h

/-- **The weighted Cauchy problem at every order: uniform bound on the solution operators.** For
`0 < α < 1`, `k : ℕ`, an ellipticity constant `λ > 0`, a bound `K` on the norms of the coefficients
in `C_{par,b}^{k+α}`, a bound `L` on the norms of the derivatives `∂ᵢℓ`, `∂ᵢ∂ⱼℓ` of the logarithm
of the weight in `C_b^{k,α}` and a bound `T₀` on the horizon, the weighted solution operators on
`ℝⁿ × [0, T]`, `T ≤ T₀`, are bounded uniformly: the solution `u = exp ℓ * v` of
`P u = exp ℓ * f`, `u(·, 0) = exp ℓ * g` (`eq_euclideanInitialDataCLE_symm_iff_exp_mul`) satisfies
`‖v‖_{k+2+α} ≤ C max (‖f‖_{k+α}) (‖g‖_{C^{k+2,α}})`. This is the order-`k` form of
`TauCeti.ParabolicC2HolderSpace.exists_norm_euclideanInitialDataCLE_weighted_symm_le`. -/
theorem exists_norm_euclideanInitialDataCLE_weighted_symm_le (hα₀ : 0 < α) (hα₁ : α < 1)
    {lam : ℝ} (hlam : 0 < lam) (k : ℕ) (K L T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (dℓ : ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ)
        (d2ℓ : ι → ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        (∀ i, ‖dℓ i‖ ≤ L) → (∀ i j, ‖d2ℓ i j‖ ≤ L) →
        ‖(euclideanInitialDataCLE hα₀ hα₁ a (euclideanWeightedFirstOrderCoeff hα₁.le a b dℓ)
          (euclideanWeightedZerothOrderCoeff hα₁.le a b c dℓ d2ℓ)
            ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap‖ ≤ C := by
  obtain ⟨C, hC, hest⟩ := exists_norm_euclideanInitialDataCLE_symm_le (ι := ι) hα₀ hα₁ hlam k
    (weightedCoeffBound ι k K L) T₀
  refine ⟨C, hC, fun T hT hTT₀ a b c dℓ d2ℓ ha hak hbk hck hdℓ hd2ℓ ↦ ?_⟩
  obtain ⟨ha', hb, hc⟩ := norm_weightedCoeff_le hα₁.le hak hbk hck hdℓ hd2ℓ
  exact hest T hT hTT₀ a _ _ ha ha' hb hc

/-- **The weighted Cauchy problem at every order: Lipschitz dependence on the coefficients.**
Under the bounds of `exists_norm_euclideanInitialDataCLE_weighted_symm_le`, for a fixed weight the
weighted solution operators of two Cauchy problems differ in operator norm by at most
`C (∑ᵢⱼ ‖aⁱʲ - a'ⁱʲ‖ + ∑ᵢ ‖bⁱ - b'ⁱ‖ + ‖c - c'‖)`, with the norms of `C_{par,b}^{k+α}`. This is the
order-`k` form of
`TauCeti.ParabolicC2HolderSpace.exists_norm_euclideanInitialDataCLE_weighted_symm_sub_le`. -/
theorem exists_norm_euclideanInitialDataCLE_weighted_symm_sub_le (hα₀ : 0 < α) (hα₁ : α < 1)
    {lam : ℝ} (hlam : 0 < lam) (k : ℕ) (K L T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a a' : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (b b' : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (c c' : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (dℓ : ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ)
        (d2ℓ : ι → ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
        (ha' : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a' i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        (∀ i j, ‖a' i j‖ ≤ K) → (∀ i, ‖b' i‖ ≤ K) → ‖c'‖ ≤ K →
        (∀ i, ‖dℓ i‖ ≤ L) → (∀ i j, ‖d2ℓ i j‖ ≤ L) →
        ‖(euclideanInitialDataCLE hα₀ hα₁ a (euclideanWeightedFirstOrderCoeff hα₁.le a b dℓ)
            (euclideanWeightedZerothOrderCoeff hα₁.le a b c dℓ d2ℓ)
              ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap -
          (euclideanInitialDataCLE hα₀ hα₁ a' (euclideanWeightedFirstOrderCoeff hα₁.le a' b' dℓ)
            (euclideanWeightedZerothOrderCoeff hα₁.le a' b' c' dℓ d2ℓ)
              ⟨lam, hlam, ha'⟩).symm.toContinuousLinearMap‖ ≤
          C * (∑ i, ∑ j, ‖a i j - a' i j‖ + ∑ i, ‖b i - b' i‖ + ‖c - c'‖) := by
  obtain ⟨C, hC, hest⟩ := exists_norm_euclideanInitialDataCLE_symm_sub_le (ι := ι) hα₀ hα₁ hlam k
    (weightedCoeffBound ι k K L) T₀
  set M : ℝ := 21 * (k + 1) ^ 2 * 2 ^ k
  refine ⟨C * (1 + 6 * M * L + 4 * M ^ 2 * L ^ 2), by positivity, fun T hT hTT₀ a a' b b' c c'
    dℓ d2ℓ ha ha' hak hbk hck hak' hbk' hck' hdℓ hd2ℓ ↦ ?_⟩
  obtain ⟨hak₁, hb, hc⟩ := norm_weightedCoeff_le hα₁.le hak hbk hck hdℓ hd2ℓ
  obtain ⟨hak₁', hb', hc'⟩ := norm_weightedCoeff_le hα₁.le hak' hbk' hck' hdℓ hd2ℓ
  refine (hest T hT hTT₀ a a' _ _ _ _ ha ha' hak₁ hb hc hak₁' hb' hc').trans ?_
  exact mul_le_mul_of_nonneg_left (weightedCoeff_sub_le_mul hα₁.le hdℓ hd2ℓ) hC |>.trans_eq
    (by ring)

/-- **The weighted terminal-value problem at every order: uniform bound on the solution
operators.** Under the bounds of `exists_norm_euclideanInitialDataCLE_weighted_symm_le`, the
weighted solution operators of the terminal-value problems on `ℝⁿ × [0, T]`, `T ≤ T₀`, are bounded
uniformly: the solution `u = exp ℓ * v` of `∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u = exp ℓ * f`,
`u(·, T) = exp ℓ * g` (`eq_euclideanTerminalDataCLE_symm_iff_exp_mul`) satisfies
`‖v‖_{k+2+α} ≤ C max (‖f‖_{k+α}) (‖g‖_{C^{k+2,α}})`. This is the order-`k` form of
`TauCeti.ParabolicC2HolderSpace.exists_norm_euclideanTerminalDataCLE_weighted_symm_le`. -/
theorem exists_norm_euclideanTerminalDataCLE_weighted_symm_le (hα₀ : 0 < α) (hα₁ : α < 1)
    {lam : ℝ} (hlam : 0 < lam) (k : ℕ) (K L T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (dℓ : ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ)
        (d2ℓ : ι → ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        (∀ i, ‖dℓ i‖ ≤ L) → (∀ i j, ‖d2ℓ i j‖ ≤ L) →
        ‖(euclideanTerminalDataCLE hα₀ hα₁ a (euclideanWeightedFirstOrderCoeff hα₁.le a b dℓ)
          (euclideanWeightedZerothOrderCoeff hα₁.le a b c dℓ d2ℓ)
            ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap‖ ≤ C := by
  obtain ⟨C, hC, hest⟩ := exists_norm_euclideanTerminalDataCLE_symm_le (ι := ι) hα₀ hα₁ hlam k
    (weightedCoeffBound ι k K L) T₀
  refine ⟨C, hC, fun T hT hTT₀ a b c dℓ d2ℓ ha hak hbk hck hdℓ hd2ℓ ↦ ?_⟩
  obtain ⟨ha', hb, hc⟩ := norm_weightedCoeff_le hα₁.le hak hbk hck hdℓ hd2ℓ
  exact hest T hT hTT₀ a _ _ ha ha' hb hc

/-- **The weighted terminal-value problem at every order: Lipschitz dependence on the
coefficients.** Under the bounds of `exists_norm_euclideanTerminalDataCLE_weighted_symm_le`, for
a fixed weight the weighted solution operators of two terminal-value problems differ in operator
norm by at most `C (∑ᵢⱼ ‖aⁱʲ - a'ⁱʲ‖ + ∑ᵢ ‖bⁱ - b'ⁱ‖ + ‖c - c'‖)`, with the norms of
`C_{par,b}^{k+α}`. This is the order-`k` form of
`TauCeti.ParabolicC2HolderSpace.exists_norm_euclideanTerminalDataCLE_weighted_symm_sub_le`. -/
theorem exists_norm_euclideanTerminalDataCLE_weighted_symm_sub_le (hα₀ : 0 < α) (hα₁ : α < 1)
    {lam : ℝ} (hlam : 0 < lam) (k : ℕ) (K L T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a a' : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (b b' : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (c c' : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (dℓ : ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ)
        (d2ℓ : ι → ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
        (ha' : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a' i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        (∀ i j, ‖a' i j‖ ≤ K) → (∀ i, ‖b' i‖ ≤ K) → ‖c'‖ ≤ K →
        (∀ i, ‖dℓ i‖ ≤ L) → (∀ i j, ‖d2ℓ i j‖ ≤ L) →
        ‖(euclideanTerminalDataCLE hα₀ hα₁ a (euclideanWeightedFirstOrderCoeff hα₁.le a b dℓ)
            (euclideanWeightedZerothOrderCoeff hα₁.le a b c dℓ d2ℓ)
              ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap -
          (euclideanTerminalDataCLE hα₀ hα₁ a' (euclideanWeightedFirstOrderCoeff hα₁.le a' b' dℓ)
            (euclideanWeightedZerothOrderCoeff hα₁.le a' b' c' dℓ d2ℓ)
              ⟨lam, hlam, ha'⟩).symm.toContinuousLinearMap‖ ≤
          C * (∑ i, ∑ j, ‖a i j - a' i j‖ + ∑ i, ‖b i - b' i‖ + ‖c - c'‖) := by
  obtain ⟨C, hC, hest⟩ := exists_norm_euclideanTerminalDataCLE_symm_sub_le (ι := ι) hα₀ hα₁ hlam
    k (weightedCoeffBound ι k K L) T₀
  set M : ℝ := 21 * (k + 1) ^ 2 * 2 ^ k
  refine ⟨C * (1 + 6 * M * L + 4 * M ^ 2 * L ^ 2), by positivity, fun T hT hTT₀ a a' b b' c c'
    dℓ d2ℓ ha ha' hak hbk hck hak' hbk' hck' hdℓ hd2ℓ ↦ ?_⟩
  obtain ⟨hak₁, hb, hc⟩ := norm_weightedCoeff_le hα₁.le hak hbk hck hdℓ hd2ℓ
  obtain ⟨hak₁', hb', hc'⟩ := norm_weightedCoeff_le hα₁.le hak' hbk' hck' hdℓ hd2ℓ
  refine (hest T hT hTT₀ a a' _ _ _ _ ha ha' hak₁ hb hc hak₁' hb' hc').trans ?_
  exact mul_le_mul_of_nonneg_left (weightedCoeff_sub_le_mul hα₁.le hdℓ hd2ℓ) hC |>.trans_eq
    (by ring)

end Estimates

/-! ### The weight `1 + exp x` on the line -/

section Line

variable [Unique ι] {T : ℝ≥0}

/-- On the line `ℝ¹ = EuclideanSpace ℝ ι`, the first and second derivatives of the logarithm
`log (1 + exp x)` of the weight `1 + exp x`, the sigmoid and its derivative, lie in `C_b^{k,α}` for
every `k`. -/
private theorem exists_fderiv_log_one_add_exp_eq (hα : α ≤ 1) :
    ∃ (dℓ : ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ)
      (d2ℓ : ι → ι → CkHolderSpace k α (EuclideanSpace ℝ ι) ℝ),
      (∀ i x, fderiv ℝ (fun x : EuclideanSpace ℝ ι ↦ log (1 + exp (x default))) x
        (EuclideanSpace.single i 1) = dℓ i x) ∧
      ∀ i j x, fderiv ℝ (fderiv ℝ fun x : EuclideanSpace ℝ ι ↦ log (1 + exp (x default))) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = d2ℓ i j x := by
  obtain ⟨f₀, hf₀⟩ := CkHolderSpace.exists_coe_eq_iteratedDeriv_sigmoid (k := k) hα 0
  obtain ⟨f₁, hf₁⟩ := CkHolderSpace.exists_coe_eq_iteratedDeriv_sigmoid (k := k) hα 1
  set P := EuclideanSpace.proj (𝕜 := ℝ) (ι := ι) default
  refine ⟨fun _ ↦ CkHolderSpace.compLinearL P f₀, fun _ _ ↦ CkHolderSpace.compLinearL P f₁,
    fun i x ↦ ?_, fun i j x ↦ ?_⟩
  · rw [fderiv_log_one_add_exp_apply, CkHolderSpace.compLinearL_apply, hf₀, iteratedDeriv_zero]
    simp [P]
  · rw [fderiv_fderiv_log_one_add_exp_apply, CkHolderSpace.compLinearL_apply, hf₁,
      iteratedDeriv_one]
    simp [P]

/-- **The Cauchy problem on the line with the weight `1 + exp x`, at every order.** On the line
`ℝ¹ = EuclideanSpace ℝ ι`, for coefficients in `C_{par,b}^{k+α}` with `a` uniformly elliptic and
data `f ∈ C_{par,b}^{k+α}`, `g ∈ C_b^{k+2,α}`, there is exactly one `v ∈ C_{par,b}^{k+2+α}` such
that `u = (1 + exp x) v` is a classical solution of `P u = (1 + exp x) f`,
`u(·, 0) = (1 + exp x) g`. The solution and the data may grow like `exp x` as `x → ∞`. -/
theorem existsUnique_one_add_exp_mul (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    {a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT}
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (f : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (g : CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ) :
    ∃! v : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT,
      ∀ u : EuclideanSpace ℝ ι → ℝ → ℝ,
        (∀ y (s : Icc (0 : ℝ) T), u y s = (1 + exp (y default)) * v (slabMk y s)) →
        (∀ (x : EuclideanSpace ℝ ι) (t : Icc (0 : ℝ) T), derivWithin (u x) (Icc 0 T) t -
          (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
              (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
            ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
            c (slabMk x t) * u x t) = (1 + exp (x default)) * f (slabMk x t)) ∧
          ∀ x, u x 0 = (1 + exp (x default)) * g x := by
  obtain ⟨dℓ, d2ℓ, hdℓ, hd2ℓ⟩ := exists_fderiv_log_one_add_exp_eq (k := k) (ι := ι) hα₁.le
  have hℓ : ContDiff ℝ 2 fun x : EuclideanSpace ℝ ι ↦ log (1 + exp (x default)) :=
    (contDiff_log_one_add_exp_and_exists_fderiv_eq hα₁.le).1.of_le le_top
  have hw (x : EuclideanSpace ℝ ι) : exp (log (1 + exp (x default))) = 1 + exp (x default) :=
    exp_log (by positivity)
  simpa only [hw] using existsUnique_exp_mul hα₀ hα₁ hT b c ha hℓ hdℓ hd2ℓ f g

/-- **The terminal-value problem on the line with the weight `1 + exp x`, at every order.** On
the line `ℝ¹ = EuclideanSpace ℝ ι`, for coefficients in `C_{par,b}^{k+α}` with `a` uniformly
elliptic and data `f ∈ C_{par,b}^{k+α}`, `g ∈ C_b^{k+2,α}`, there is exactly one
`v ∈ C_{par,b}^{k+2+α}` such that `u = (1 + exp x) v` is a classical solution of
`∂ₜu + a ∂ₓ²u + b ∂ₓu + c u = (1 + exp x) f`, `u(·, T) = (1 + exp x) g`. -/
theorem existsUnique_one_add_exp_mul_backward (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    {a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT}
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (f : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (g : CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ) :
    ∃! v : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT,
      ∀ u : EuclideanSpace ℝ ι → ℝ → ℝ,
        (∀ y (s : Icc (0 : ℝ) T), u y s = (1 + exp (y default)) * v (slabMk y s)) →
        (∀ (x : EuclideanSpace ℝ ι) (t : Icc (0 : ℝ) T), derivWithin (u x) (Icc 0 T) t +
          (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
              (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
            ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
            c (slabMk x t) * u x t) = (1 + exp (x default)) * f (slabMk x t)) ∧
          ∀ x, u x T = (1 + exp (x default)) * g x := by
  obtain ⟨dℓ, d2ℓ, hdℓ, hd2ℓ⟩ := exists_fderiv_log_one_add_exp_eq (k := k) (ι := ι) hα₁.le
  have hℓ : ContDiff ℝ 2 fun x : EuclideanSpace ℝ ι ↦ log (1 + exp (x default)) :=
    (contDiff_log_one_add_exp_and_exists_fderiv_eq hα₁.le).1.of_le le_top
  have hw (x : EuclideanSpace ℝ ι) : exp (log (1 + exp (x default))) = 1 + exp (x default) :=
    exp_log (by positivity)
  simpa only [hw] using existsUnique_exp_mul_backward hα₀ hα₁ hT b c ha hℓ hdℓ hd2ℓ f g

end Line

end TauCeti.ParabolicCkHolderSpace
