/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Operator
public import TauCeti.Analysis.Holder.Algebra
public import TauCeti.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Conjugating parabolic operators by a spatial weight

Let `w = exp ∘ ℓ` be a positive time-independent weight on space. Its logarithm `ℓ` need not be
bounded, so `w` may grow or decay at infinity; only the derivatives of `ℓ` are controlled. For a
map `v` in the bounded order-two parabolic Hölder space `C_b^{2+α,1+α/2}` on the slab
`E × [t₀, t₁]`, the weighted map `u = w v` is in general unbounded, and solving parabolic
equations for such `u` reduces to solving a conjugated equation for `v`. This file supplies that
reduction at order two.

For the weighted map `u(x, t) = exp (ℓ x) • v(x, t)`, the time derivative is `w ∂ₜv` and the
spatial derivatives are

* `D_x u = w (D_x v + Dℓ ⊗ v)`;
* `D_x² u (h, k) = w (D_x² v (h, k) + Dℓ h D_x v k + Dℓ k D_x v h +
  (D²ℓ (h, k) + Dℓ h Dℓ k) v)`.

On `ℝⁿ = EuclideanSpace ℝ ι`, let `P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u` have scalar coefficients in
`C_b^{α,α/2}` (`TauCeti.ParabolicC2HolderSpace.euclideanParabolicOperatorL`). Then

`P u = w P_w v`,

where `P_w` has the same second-order coefficients `aⁱʲ` and the coefficients

* `b_wⁱ = bⁱ + ∑ⱼ (aⁱʲ + aʲⁱ) ∂ⱼℓ`;
* `c_w = c + ∑ᵢⱼ aⁱʲ (∂ᵢ∂ⱼℓ + ∂ᵢℓ ∂ⱼℓ) + ∑ᵢ bⁱ ∂ᵢℓ`.

No symmetry of `a` is assumed; for symmetric `a` the first-order coefficient is
`bⁱ + 2 aⁱʲ ∂ⱼℓ`. When the first and second derivatives of `ℓ` are bounded and `α`-Hölder, the
new coefficients again lie in `C_b^{α,α/2}`: time-independent Hölder fields on space are
parabolically Hölder on the slab (`TauCeti.HolderSpace.compSlabSpaceL`), and bounded Hölder
functions form an algebra. Thus `P u = f` with `u = w v` is equivalent to `P_w v = f / w`, an
equation of the same type in the bounded space, and the initial or terminal trace of `u` is `w`
times that of `v`. A typical weight is `w(x) = 1 + exp x` on the line, whose logarithm has bounded
Hölder derivatives of every positive order (`Real.iteratedDeriv_succ_log_one_add_exp`,
`Real.memHolder_iteratedDeriv_sigmoid`).

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.hasFDerivAt_exp_smul`,
  `TauCeti.ParabolicC2HolderSpace.fderiv_fderiv_exp_smul_apply` and
  `TauCeti.ParabolicC2HolderSpace.hasDerivWithinAt_exp_smul`: the derivatives of the weighted
  map `exp (ℓ x) • v(x, t)`.
* `TauCeti.ParabolicC2HolderSpace.euclideanWeightedFirstOrderCoeff` and
  `TauCeti.ParabolicC2HolderSpace.euclideanWeightedZerothOrderCoeff`: the coefficients `b_w` and
  `c_w` of the conjugated operator.
* `TauCeti.ParabolicC2HolderSpace.exp_mul_euclideanParabolicOperatorL_eq`: the conjugation
  identity `w P_w v = P (w v)`.
* `TauCeti.contDiff_log_one_add_exp_and_exists_fderiv_eq`: the weight `1 + exp x` on the line
  satisfies the hypotheses of the conjugation identity.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2 (the
  substitution `u = w v` by a positive weight, transforming a parabolic equation into one of the
  same type).
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
-/

public section
noncomputable section

namespace TauCeti

open Set ParabolicSpaceTime Real
open scoped NNReal

variable {α : ℝ≥0}

namespace ParabolicC2HolderSpace

/-! ### The derivatives of a weighted map -/

section WeightedMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {t₀ t₁ : ℝ} {ht : t₀ < t₁} {ℓ : E → ℝ}

/-- **The spatial gradient of a weighted map.** If `ℓ` is differentiable at `x`, the weighted map
`y ↦ exp (ℓ y) • v(y, t)` has derivative `exp (ℓ x) • (D_x v + Dℓ ⊗ v)` at `x`. -/
theorem hasFDerivAt_exp_smul {x : E} (hℓ : DifferentiableAt ℝ ℓ x)
    (v : ParabolicC2HolderSpace α E F ht) (t : Icc t₀ t₁) :
    HasFDerivAt (fun y ↦ exp (ℓ y) • v (slabMk y t))
      (exp (ℓ x) • (spatialFDerivL v (slabMk x t) + (fderiv ℝ ℓ x).smulRight (v (slabMk x t))))
      x := by
  convert (hℓ.hasFDerivAt.exp).smul (v.hasSpatialFDerivAt t x) using 1
  ext h
  simp [smul_add, smul_smul]

/-- The spatial gradient of a weighted map, as a function of the base point. -/
theorem fderiv_exp_smul (hℓ : Differentiable ℝ ℓ) (v : ParabolicC2HolderSpace α E F ht)
    (t : Icc t₀ t₁) :
    fderiv ℝ (fun y ↦ exp (ℓ y) • v (slabMk y t)) = fun x ↦
      exp (ℓ x) • (spatialFDerivL v (slabMk x t) + (fderiv ℝ ℓ x).smulRight (v (slabMk x t))) :=
  funext fun x ↦ (hasFDerivAt_exp_smul (hℓ x) v t).fderiv

/-- **The spatial Hessian of a weighted map.** For a `C²` function `ℓ`, the second derivative of
the weighted map `y ↦ exp (ℓ y) • v(y, t)` at `x`, applied to `h` and `k`, is
`exp (ℓ x) • (D_x² v (h, k) + Dℓ h D_x v k + Dℓ k D_x v h + (D²ℓ (h, k) + Dℓ h Dℓ k) v)`. -/
theorem fderiv_fderiv_exp_smul_apply (hℓ : ContDiff ℝ 2 ℓ)
    (v : ParabolicC2HolderSpace α E F ht) (t : Icc t₀ t₁) (x h k : E) :
    fderiv ℝ (fderiv ℝ fun y ↦ exp (ℓ y) • v (slabMk y t)) x h k =
      exp (ℓ x) • (spatialSecondFDerivL v (slabMk x t) h k +
        fderiv ℝ ℓ x h • spatialFDerivL v (slabMk x t) k +
        fderiv ℝ ℓ x k • spatialFDerivL v (slabMk x t) h +
        (fderiv ℝ (fderiv ℝ ℓ) x h k + fderiv ℝ ℓ x h * fderiv ℝ ℓ x k) • v (slabMk x t)) := by
  have hℓ₁ : Differentiable ℝ ℓ := hℓ.differentiable two_ne_zero
  have hDℓ : HasFDerivAt (fderiv ℝ ℓ) (fderiv ℝ (fderiv ℝ ℓ) x) x :=
    ((hℓ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x).hasFDerivAt
  -- The gradient is `exp ℓ • (D_x v + Dℓ ⊗ v)`; differentiate each factor.
  have hG := ((hℓ₁ x).hasFDerivAt.exp).smul ((v.hasSpatialSecondFDerivAt t x).add
    ((ContinuousLinearMap.smulRightL ℝ E F).hasFDerivAt_of_bilinear hDℓ
      (v.hasSpatialFDerivAt t x)))
  have hfun : (fun y ↦ exp (ℓ y) • (spatialFDerivL v (slabMk y t) +
      (fderiv ℝ ℓ y).smulRight (v (slabMk y t)))) =
      (fun y ↦ exp (ℓ y)) • ((fun y ↦ spatialFDerivL v (slabMk y t)) +
        fun y ↦ ContinuousLinearMap.smulRightL ℝ E F (fderiv ℝ ℓ y) (v (slabMk y t))) := by
    ext y : 1
    simp
  rw [fderiv_exp_smul hℓ₁ v t, hfun, hG.fderiv]
  simp only [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply, smul_add,
    ContinuousLinearMap.smulRightL_apply_apply, Pi.add_apply, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  module

/-- **The time derivative of a weighted map.** Since the weight does not depend on time, the
time derivative within the slab of `s ↦ exp (ℓ x) • v(x, s)` is `exp (ℓ x) • ∂ₜv`. -/
theorem hasDerivWithinAt_exp_smul (v : ParabolicC2HolderSpace α E F ht) (x : E)
    (t : Icc t₀ t₁) :
    HasDerivWithinAt (fun s ↦ exp (ℓ x) • timeExtension ht.le v x s)
      (exp (ℓ x) • timeDerivL v (slabMk x t)) (Icc t₀ t₁) t :=
  (v.hasTimeDerivWithinAt x t).const_smul _

end WeightedMap

/-! ### The conjugated operator on Euclidean space -/

section Euclidean

variable {ι : Type*} [Fintype ι] {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- The first-order coefficients `b_wⁱ = bⁱ + ∑ⱼ (aⁱʲ + aʲⁱ) ∂ⱼℓ` of the parabolic operator
with coefficients `aⁱʲ`, `bⁱ` conjugated by the weight `exp ℓ`, where `dℓ j` is the partial
derivative `∂ⱼℓ`, a bounded `α`-Hölder function on space. -/
def euclideanWeightedFirstOrderCoeff
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (dℓ : ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ) (i : ι) :
    HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ :=
  b i + ∑ j, (a i j + a j i) * HolderSpace.compSlabSpaceL (dℓ j)

/-- The zeroth-order coefficient `c_w = c + ∑ᵢⱼ aⁱʲ (∂ᵢ∂ⱼℓ + ∂ᵢℓ ∂ⱼℓ) + ∑ᵢ bⁱ ∂ᵢℓ` of the
parabolic operator with coefficients `aⁱʲ`, `bⁱ`, `c` conjugated by the weight `exp ℓ`, where
`dℓ i` is the partial derivative `∂ᵢℓ` and `d2ℓ i j` is `∂ᵢ∂ⱼℓ`, bounded `α`-Hölder functions on
space. -/
def euclideanWeightedZerothOrderCoeff
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (dℓ : ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ)
    (d2ℓ : ι → ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ) :
    HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ :=
  c + ∑ i, ∑ j, a i j * HolderSpace.compSlabSpaceL (d2ℓ i j + dℓ i * dℓ j) +
    ∑ i, b i * HolderSpace.compSlabSpaceL (dℓ i)

variable {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {dℓ : ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ}
  {d2ℓ : ι → ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ}

@[simp]
theorem euclideanWeightedFirstOrderCoeff_apply (i : ι)
    (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁) :
    euclideanWeightedFirstOrderCoeff a b dℓ i p =
      b i p + ∑ j, (a i j p + a j i p) * dℓ j (p : ParabolicSpaceTime _).space := by
  simp [euclideanWeightedFirstOrderCoeff]

@[simp]
theorem euclideanWeightedZerothOrderCoeff_apply (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁) :
    euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ p =
      c p + ∑ i, ∑ j, a i j p * (d2ℓ i j (p : ParabolicSpaceTime _).space +
          dℓ i (p : ParabolicSpaceTime _).space * dℓ j (p : ParabolicSpaceTime _).space) +
        ∑ i, b i p * dℓ i (p : ParabolicSpaceTime _).space := by
  simp [euclideanWeightedZerothOrderCoeff]

/-- **Conjugation by a spatial weight.** Let `ℓ` be `C²` on `ℝⁿ`, with partial derivatives
`∂ᵢℓ = dℓ i` and `∂ᵢ∂ⱼℓ = d2ℓ i j` bounded and `α`-Hölder, and let `u = exp ℓ • v` on the slab
for some `v ∈ C_b^{2+α,1+α/2}`. Then the classical parabolic operator
`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u` is `exp ℓ` times the operator `P_w v` with coefficients
`aⁱʲ`, `b_wⁱ` (`euclideanWeightedFirstOrderCoeff`) and `c_w`
(`euclideanWeightedZerothOrderCoeff`) applied to `v`. The time derivative of `u` is taken within
the closed time interval, so the identity also holds at the initial and terminal times. -/
theorem exp_mul_euclideanParabolicOperatorL_eq [DecidableEq ι] (hα : α ≤ 1)
    {ℓ : EuclideanSpace ℝ ι → ℝ} (hℓ : ContDiff ℝ 2 ℓ)
    (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht)
    {u : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu : ∀ y (s : Icc t₀ t₁), u y s = exp (ℓ y) * v (slabMk y s))
    (x : EuclideanSpace ℝ ι) (t : Icc t₀ t₁) :
    exp (ℓ x) * euclideanParabolicOperatorL hα a (euclideanWeightedFirstOrderCoeff a b dℓ)
        (euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ) v (slabMk x t) =
      derivWithin (u x) (Icc t₀ t₁) t -
        (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
          ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
          c (slabMk x t) * u x t) := by
  have hslice : (fun y ↦ u y t) = fun y ↦ exp (ℓ y) * v (slabMk y t) := funext fun y ↦ hu y t
  -- The spatial derivatives of `u` at time `t`, from those of the weighted map.
  have hD₁ : fderiv ℝ (fun y ↦ u y t) x = exp (ℓ x) • (spatialFDerivL v (slabMk x t) +
      (fderiv ℝ ℓ x).smulRight (v (slabMk x t))) := by
    rw [hslice]
    simpa only [smul_eq_mul] using
      (hasFDerivAt_exp_smul (hℓ.differentiable two_ne_zero x) v t).fderiv
  have hD₂ (h k : EuclideanSpace ℝ ι) : fderiv ℝ (fderiv ℝ fun y ↦ u y t) x h k =
      exp (ℓ x) * (spatialSecondFDerivL v (slabMk x t) h k +
        fderiv ℝ ℓ x h * spatialFDerivL v (slabMk x t) k +
        fderiv ℝ ℓ x k * spatialFDerivL v (slabMk x t) h +
        (fderiv ℝ (fderiv ℝ ℓ) x h k + fderiv ℝ ℓ x h * fderiv ℝ ℓ x k) * v (slabMk x t)) := by
    rw [hslice]
    simpa only [smul_eq_mul] using fderiv_fderiv_exp_smul_apply hℓ v t x h k
  -- In time, `u x` agrees on the closed interval with the weighted time extension of `v`.
  have htime : derivWithin (u x) (Icc t₀ t₁) t = exp (ℓ x) * timeDerivL v (slabMk x t) := by
    rw [derivWithin_congr (f := fun s ↦ exp (ℓ x) • timeExtension ht.le v x s)
      (fun s hs ↦ by
        simp only [timeExtension_def, projIcc_of_mem ht.le hs, smul_eq_mul]
        exact hu x ⟨s, hs⟩)
      (by simp only [timeExtension_def, projIcc_val, smul_eq_mul]; exact hu x t),
      (hasDerivWithinAt_exp_smul v x t).derivWithin (uniqueDiffOn_Icc ht t t.2), smul_eq_mul]
  rw [htime, hD₁, hu x t]
  simp only [hD₂, euclideanParabolicOperatorL_apply,
    euclideanWeightedFirstOrderCoeff_apply, euclideanWeightedZerothOrderCoeff_apply,
    space_slabMk, _root_.smul_apply, _root_.add_apply, ContinuousLinearMap.smulRight_apply, hdℓ,
    hd2ℓ, smul_eq_mul]
  set H := spatialSecondFDerivL v (slabMk x t)
  set D := spatialFDerivL v (slabMk x t)
  set e : ι → EuclideanSpace ℝ ι := fun i ↦ EuclideanSpace.single i 1
  -- The cross terms `aⁱʲ (∂ᵢℓ ∂ⱼv + ∂ⱼℓ ∂ᵢv)` form the extra first-order coefficient.
  have hswap : ∑ i, ∑ j, a i j (slabMk x t) * (dℓ i x * D (e j)) =
      ∑ i, ∑ j, a j i (slabMk x t) * (dℓ j x * D (e i)) := Finset.sum_comm
  have h₂ : ∑ i, ∑ j, a i j (slabMk x t) * (exp (ℓ x) * (H (e i) (e j) + dℓ i x * D (e j) +
        dℓ j x * D (e i) + (d2ℓ i j x + dℓ i x * dℓ j x) * v (slabMk x t))) =
      exp (ℓ x) * (∑ i, ∑ j, a i j (slabMk x t) * H (e i) (e j) +
        ∑ i, (∑ j, (a i j (slabMk x t) + a j i (slabMk x t)) * dℓ j x) * D (e i) +
        (∑ i, ∑ j, a i j (slabMk x t) * (d2ℓ i j x + dℓ i x * dℓ j x)) * v (slabMk x t)) := by
    calc _ = exp (ℓ x) * (∑ i, ∑ j, a i j (slabMk x t) * H (e i) (e j) +
          ∑ i, ∑ j, a i j (slabMk x t) * (dℓ i x * D (e j)) +
          ∑ i, ∑ j, a i j (slabMk x t) * (dℓ j x * D (e i)) +
          ∑ i, ∑ j, a i j (slabMk x t) * (d2ℓ i j x + dℓ i x * dℓ j x) * v (slabMk x t)) := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
      _ = _ := by
          rw [hswap]
          congr 1
          simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  have h₁ : ∑ i, b i (slabMk x t) * (exp (ℓ x) * (D (e i) + dℓ i x * v (slabMk x t))) =
      exp (ℓ x) * (∑ i, b i (slabMk x t) * D (e i) +
        (∑ i, b i (slabMk x t) * dℓ i x) * v (slabMk x t)) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have h₀ : ∑ i, (b i (slabMk x t) + ∑ j, (a i j (slabMk x t) + a j i (slabMk x t)) * dℓ j x) *
        D (e i) = ∑ i, b i (slabMk x t) * D (e i) +
      ∑ i, (∑ j, (a i j (slabMk x t) + a j i (slabMk x t)) * dℓ j x) * D (e i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ add_mul _ _ _
  rw [h₂, h₁, h₀]
  ring

end Euclidean

end ParabolicC2HolderSpace

/-! ### The weight `1 + exp x` on the line -/

section Line

variable {ι : Type*} [Unique ι]

/-- **The weight `1 + exp x` satisfies the hypotheses of the conjugation identity.** On the line
`ℝ¹ = EuclideanSpace ℝ ι`, the logarithm `ℓ x = log (1 + exp x)` of the weight `1 + exp x` is
smooth, and for every `α ≤ 1` its first and second derivatives are bounded `α`-Hölder functions,
namely the sigmoid and its derivative. Thus
`ParabolicC2HolderSpace.exp_mul_euclideanParabolicOperatorL_eq` applies to the unbounded weight
`exp ℓ = 1 + exp x`. -/
theorem contDiff_log_one_add_exp_and_exists_fderiv_eq (hα : α ≤ 1) :
    ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ ι ↦ log (1 + exp (x default))) ∧
    ∃ (dℓ : ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ)
      (d2ℓ : ι → ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ),
      (∀ i x, fderiv ℝ (fun x : EuclideanSpace ℝ ι ↦ log (1 + exp (x default))) x
        (EuclideanSpace.single i 1) = dℓ i x) ∧
      ∀ i j x, fderiv ℝ (fderiv ℝ fun x : EuclideanSpace ℝ ι ↦ log (1 + exp (x default))) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = d2ℓ i j x := by
  refine ⟨(ContDiff.log (contDiff_const.add contDiff_exp) fun _ ↦ by positivity).comp
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := ι) default).contDiff, ?_⟩
  set P := EuclideanSpace.proj (𝕜 := ℝ) (ι := ι) default
  -- The derivatives of the sigmoid, as bounded Hölder functions of the coordinate.
  have hσ (n : ℕ) : ∃ f : HolderSpace α (EuclideanSpace ℝ ι) ℝ,
      ∀ x, f x = iteratedDeriv n sigmoid (x default) := by
    obtain ⟨C, hC⟩ := exists_abs_iteratedDeriv_sigmoid_le n
    refine ⟨HolderSpace.compLipschitzL P P.lipschitzWith
      (HolderSpace.ofBoundedContinuousFunction (BoundedContinuousFunction.ofNormedAddCommGroup
        (iteratedDeriv n sigmoid) (contDiff_sigmoid.continuous_iteratedDeriv n (by simp)) C
        fun x ↦ by simpa only [Real.norm_eq_abs] using hC x)
        (by
          rw [BoundedContinuousFunction.coe_ofNormedAddCommGroup]
          exact memHolder_iteratedDeriv_sigmoid n hα)), fun x ↦ ?_⟩
    rw [HolderSpace.compLipschitzL_apply, HolderSpace.ofBoundedContinuousFunction_apply,
      BoundedContinuousFunction.coe_ofNormedAddCommGroup]
    simp [P]
  obtain ⟨f₀, hf₀⟩ := hσ 0
  obtain ⟨f₁, hf₁⟩ := hσ 1
  have hℓ (x : EuclideanSpace ℝ ι) : HasFDerivAt (fun x : EuclideanSpace ℝ ι ↦
      log (1 + exp (x default))) (sigmoid (P x) • P) x :=
    (hasDerivAt_log_one_add_exp (P x)).comp_hasFDerivAt x P.hasFDerivAt
  have hfderiv : fderiv ℝ (fun x : EuclideanSpace ℝ ι ↦ log (1 + exp (x default))) =
      fun x ↦ sigmoid (P x) • P := funext fun x ↦ (hℓ x).fderiv
  refine ⟨fun _ ↦ f₀, fun _ _ ↦ f₁, fun i x ↦ ?_, fun i j x ↦ ?_⟩
  · rw [hfderiv, Subsingleton.elim i default, hf₀]
    simp [P]
  · have h₂ : HasFDerivAt (fun y ↦ sigmoid (P y) • P)
        (((sigmoid (P x) * (1 - sigmoid (P x))) • P).smulRight P) x :=
      ((hasDerivAt_sigmoid (P x)).comp_hasFDerivAt x P.hasFDerivAt).smul_const P
    rw [hfderiv, h₂.fderiv, Subsingleton.elim i default, Subsingleton.elim j default, hf₁,
      iteratedDeriv_one, (hasDerivAt_sigmoid _).deriv]
    simp [P]

end Line

end TauCeti

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime ContinuousLinearMap
open scoped NNReal BoundedContinuousFunction

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- A local shortcut for the norm on Hessians, needed for the operator norm on the coefficient
space `(E →L[ℝ] E →L[ℝ] F) →L[ℝ] F` for the reason explained in
`TauCeti.Analysis.PDE.Parabolic.Holder.Operator`. -/
local instance weightNormedAddCommGroupHessian :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on Hessians. -/
local instance weightNormedSpaceHessian : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
/-! ### The pointwise algebra of the conjugation -/

section Bilinear

/-- A local shortcut for the norm on gradients. -/
local instance weightNormedAddCommGroupGradient : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on gradients. -/
local instance weightNormedSpaceGradient : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
/-- A local shortcut for the norm on covectors. -/
local instance weightNormedAddCommGroupCovector : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
/-- A local shortcut for scalar operations on covectors. -/
local instance weightNormedSpaceCovector : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
/-- A local shortcut for the norm on bilinear forms. -/
local instance weightNormedAddCommGroupForm :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
/-- A local shortcut for scalar operations on bilinear forms. -/
local instance weightNormedSpaceForm : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
/-- A local shortcut for the norm on second-order coefficients. -/
local instance weightNormedAddCommGroupSecondCoeff :
    NormedAddCommGroup ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on second-order coefficients. -/
local instance weightNormedSpaceSecondCoeff :
    NormedSpace ℝ ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) := inferInstance
/-- A local shortcut for the norm on first-order coefficients. -/
local instance weightNormedAddCommGroupFirstCoeff :
    NormedAddCommGroup ((E →L[ℝ] F) →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on first-order coefficients. -/
local instance weightNormedSpaceFirstCoeff : NormedSpace ℝ ((E →L[ℝ] F) →L[ℝ] F) := inferInstance
/-- A local shortcut for the norm on zeroth-order coefficients. -/
local instance weightNormedAddCommGroupZerothCoeff : NormedAddCommGroup (F →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on zeroth-order coefficients. -/
local instance weightNormedSpaceZerothCoeff : NormedSpace ℝ (F →L[ℝ] F) := inferInstance


/-- The bilinear map `(A, ℓ) ↦ (H ↦ A (ℓ ⊗ H + H ⊗ ℓ))` giving the correction to `B`. -/
private def firstOrderCorrL :
    ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ((E →L[ℝ] F) →L[ℝ] F) :=
  ((compL ℝ (E →L[ℝ] F) (E →L[ℝ] E →L[ℝ] F) F).flip ∘L
    (smulRightL ℝ E (E →L[ℝ] F) + compL ℝ E F (E →L[ℝ] F) ∘L smulRightL ℝ E F)).flip

private theorem firstOrderCorrL_apply (A : (E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) (ℓ : E →L[ℝ] ℝ)
    (H : E →L[ℝ] F) : firstOrderCorrL A ℓ H = A (ℓ.smulRight H + (ℓ.smulRight H).flip) := by
  simp only [firstOrderCorrL, flip_apply, comp_apply, compL_apply]
  exact congrArg A (by ext h k; simp)

private theorem norm_firstOrderCorrL_le : ‖firstOrderCorrL (E := E) (F := F)‖ ≤ 2 := by
  have hS : ‖smulRightL ℝ E (E →L[ℝ] F) + compL ℝ E F (E →L[ℝ] F) ∘L smulRightL ℝ E F‖ ≤ 2 := by
    refine opNorm_le_bound₂ _ zero_le_two fun ℓ H ↦ ?_
    have hS : (smulRightL ℝ E (E →L[ℝ] F) + compL ℝ E F (E →L[ℝ] F) ∘L smulRightL ℝ E F) ℓ H =
        ℓ.smulRight H + (ℓ.smulRight H).flip := by
      ext h k
      simp
    rw [hS]
    calc _ ≤ ‖ℓ.smulRight H‖ + ‖(ℓ.smulRight H).flip‖ := norm_add_le _ _
      _ = 2 * ‖ℓ‖ * ‖H‖ := by rw [opNorm_flip, norm_smulRight_apply]; ring
  rw [firstOrderCorrL, opNorm_flip]
  refine (opNorm_comp_le _ _).trans ?_
  rw [opNorm_flip]
  nlinarith [norm_compL_le ℝ (E →L[ℝ] F) (E →L[ℝ] E →L[ℝ] F) F,
    norm_nonneg (smulRightL ℝ E (E →L[ℝ] F) + compL ℝ E F (E →L[ℝ] F) ∘L smulRightL ℝ E F)]

/-- The bilinear map `(A, Q) ↦ (y ↦ A (Q ⊗ y))` giving the second-order part of the correction
to `C`. -/
private def zerothOrderCorrL :
    ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] F) :=
  ((compL ℝ F (E →L[ℝ] E →L[ℝ] F) F).flip ∘L precompL E (smulRightL ℝ E F)).flip

private theorem zerothOrderCorrL_apply (A : (E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)
    (Q : E →L[ℝ] E →L[ℝ] ℝ) (y : F) :
    zerothOrderCorrL A Q y = A (precompL E (smulRightL ℝ E F) Q y) := by
  simp [zerothOrderCorrL]

private theorem norm_zerothOrderCorrL_le : ‖zerothOrderCorrL (E := E) (F := F)‖ ≤ 1 := by
  rw [zerothOrderCorrL, opNorm_flip]
  refine (opNorm_comp_le _ _).trans ?_
  rw [opNorm_flip]
  nlinarith [norm_compL_le ℝ F (E →L[ℝ] E →L[ℝ] F) F,
    (norm_precompL_le E (smulRightL ℝ E F)).trans norm_smulRightL_le,
    norm_nonneg (precompL E (smulRightL ℝ E F))]

/-- The bilinear map `(B, ℓ) ↦ (y ↦ B (ℓ ⊗ y))` giving the first-order part of the correction
to `C`. -/
private def gradCorrL : ((E →L[ℝ] F) →L[ℝ] F) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] F) :=
  ((compL ℝ F (E →L[ℝ] F) F).flip ∘L smulRightL ℝ E F).flip

private theorem gradCorrL_apply (B : (E →L[ℝ] F) →L[ℝ] F) (ℓ : E →L[ℝ] ℝ) (y : F) :
    gradCorrL B ℓ y = B (ℓ.smulRight y) := by
  simp [gradCorrL]

private theorem norm_gradCorrL_le : ‖gradCorrL (E := E) (F := F)‖ ≤ 1 := by
  rw [gradCorrL, opNorm_flip]
  refine (opNorm_comp_le _ _).trans ?_
  rw [opNorm_flip]
  nlinarith [norm_compL_le ℝ F (E →L[ℝ] F) F, norm_smulRightL_le (𝕜 := ℝ) (E := E) (Fₗ := F),
    norm_nonneg (smulRightL ℝ E F)]

/-! ### The conjugated coefficients -/

section Coefficients

variable (A : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F))
  (B : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] F) →L[ℝ] F))
  (C : HolderSpace α (slab (E := E) t₀ t₁) (F →L[ℝ] F))
  (ℓ : HolderSpace α E (E →L[ℝ] ℝ)) (M : HolderSpace α E (E →L[ℝ] E →L[ℝ] ℝ))

/-- The first-order coefficient `B_w H = B H + A (ℓ ⊗ H + H ⊗ ℓ)` of the operator conjugated by
the weight `exp φ` with gradient `ℓ = Dφ`, as a field in `C_b^{α,α/2}`. -/
def weightFirstOrderCoeff : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] F) →L[ℝ] F) :=
  B + firstOrderCorrL.compHolder₂ A (HolderSpace.compLipschitzL _ lipschitzWith_slab_space ℓ)

/-- The zeroth-order coefficient `C_w y = C y + A ((M + ℓ ⊗ ℓ) ⊗ y) + B (ℓ ⊗ y)` of the operator
conjugated by the weight `exp φ` with gradient `ℓ = Dφ` and Hessian `M = D²φ`, as a field in
`C_b^{α,α/2}`. -/
def weightZerothOrderCoeff : HolderSpace α (slab (E := E) t₀ t₁) (F →L[ℝ] F) :=
  C + zerothOrderCorrL.compHolder₂ A (HolderSpace.compLipschitzL _ lipschitzWith_slab_space
      (M + (smulRightL ℝ E (E →L[ℝ] ℝ)).compHolder₂ ℓ ℓ)) +
    gradCorrL.compHolder₂ B (HolderSpace.compLipschitzL _ lipschitzWith_slab_space ℓ)

@[simp]
theorem weightFirstOrderCoeff_apply (p : slab (E := E) t₀ t₁) (H : E →L[ℝ] F) :
    weightFirstOrderCoeff A B ℓ p H = B p H +
      A p ((ℓ (p : ParabolicSpaceTime E).space).smulRight H +
        ((ℓ (p : ParabolicSpaceTime E).space).smulRight H).flip) := by
  simp [weightFirstOrderCoeff, firstOrderCorrL_apply]

/-- The zeroth-order coefficient, evaluated: the bilinear form `M + ℓ ⊗ ℓ` is tensored with `y`
through `Q ↦ ((smulRightL ℝ E F).flip y).comp Q`, that is `(h, k) ↦ Q h k • y`. -/
@[simp]
theorem weightZerothOrderCoeff_apply (p : slab (E := E) t₀ t₁) (y : F) :
    weightZerothOrderCoeff A B C ℓ M p y = C p y +
      A p (((smulRightL ℝ E F).flip y).comp (M (p : ParabolicSpaceTime E).space +
        (ℓ (p : ParabolicSpaceTime E).space).smulRight (ℓ (p : ParabolicSpaceTime E).space))) +
      B p ((ℓ (p : ParabolicSpaceTime E).space).smulRight y) := by
  have hQ (Q : E →L[ℝ] E →L[ℝ] ℝ) :
      precompL E (smulRightL ℝ E F) Q y = ((smulRightL ℝ E F).flip y).comp Q := by
    ext h k
    simp
  simp [weightZerothOrderCoeff, zerothOrderCorrL_apply, gradCorrL_apply, hQ]

/-- **Bound on the conjugated first-order coefficient.** `‖B_w‖ ≤ ‖B‖ + 2 ‖A‖ ‖ℓ‖`. -/
theorem norm_weightFirstOrderCoeff_le :
    ‖weightFirstOrderCoeff A B ℓ‖ ≤ ‖B‖ + 2 * ‖A‖ * ‖ℓ‖ := by
  refine (norm_add_le _ _).trans ?_
  gcongr
  refine (norm_compHolder₂_apply_le _ _ _).trans ?_
  gcongr
  · exact norm_firstOrderCorrL_le
  · exact ((HolderSpace.compLipschitzL _ _).le_of_opNorm_le
      (HolderSpace.norm_compLipschitzL_le_one _) _).trans_eq (one_mul _)

/-- **Bound on the conjugated zeroth-order coefficient.**
`‖C_w‖ ≤ ‖C‖ + ‖A‖ (‖M‖ + ‖ℓ‖²) + ‖B‖ ‖ℓ‖`. -/
theorem norm_weightZerothOrderCoeff_le :
    ‖weightZerothOrderCoeff A B C ℓ M‖ ≤ ‖C‖ + ‖A‖ * (‖M‖ + ‖ℓ‖ * ‖ℓ‖) + ‖B‖ * ‖ℓ‖ := by
  have hQ : ‖M + (smulRightL ℝ E (E →L[ℝ] ℝ)).compHolder₂ ℓ ℓ‖ ≤ ‖M‖ + ‖ℓ‖ * ‖ℓ‖ := by
    refine (norm_add_le _ _).trans ?_
    gcongr
    refine (norm_compHolder₂_apply_le _ _ _).trans ?_
    nlinarith [norm_smulRightL_le (𝕜 := ℝ) (E := E) (Fₗ := E →L[ℝ] ℝ), norm_nonneg ℓ]
  have h₁ : ‖zerothOrderCorrL.compHolder₂ A (HolderSpace.compLipschitzL _
      (lipschitzWith_slab_space (a := t₀) (b := t₁))
        (M + (smulRightL ℝ E (E →L[ℝ] ℝ)).compHolder₂ ℓ ℓ))‖ ≤ ‖A‖ * (‖M‖ + ‖ℓ‖ * ‖ℓ‖) := by
    refine (norm_compHolder₂_apply_le _ _ _).trans ?_
    calc _ ≤ 1 * ‖A‖ * (‖M‖ + ‖ℓ‖ * ‖ℓ‖) := by
          gcongr
          · exact norm_zerothOrderCorrL_le
          · exact (((HolderSpace.compLipschitzL _ _).le_of_opNorm_le
              (HolderSpace.norm_compLipschitzL_le_one _) _).trans_eq (one_mul _)).trans hQ
      _ = _ := by ring
  have h₂ : ‖gradCorrL.compHolder₂ B (HolderSpace.compLipschitzL _
      (lipschitzWith_slab_space (a := t₀) (b := t₁)) ℓ)‖ ≤ ‖B‖ * ‖ℓ‖ := by
    refine (norm_compHolder₂_apply_le _ _ _).trans ?_
    calc _ ≤ 1 * ‖B‖ * ‖ℓ‖ := by
          gcongr
          · exact norm_gradCorrL_le
          · exact ((HolderSpace.compLipschitzL _ _).le_of_opNorm_le
      (HolderSpace.norm_compLipschitzL_le_one _) _).trans_eq (one_mul _)
      _ = _ := by ring
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) h₂)
  gcongr

end Coefficients

end Bilinear

/-! ### The conjugation identity -/

section Conjugation

variable {A : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)}
  {B : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] F) →L[ℝ] F)}
  {C : HolderSpace α (slab (E := E) t₀ t₁) (F →L[ℝ] F)}
  {ℓ : HolderSpace α E (E →L[ℝ] ℝ)} {M : HolderSpace α E (E →L[ℝ] E →L[ℝ] ℝ)} {φ : E → ℝ}

/-- **The gradient of a weighted slice.** For `v ∈ C_b^{2+α,1+α/2}` and `ℓ = Dφ`, the slice
`y ↦ exp (φ y) • v (y, t)` has gradient `exp (φ x) • (D_x v + ℓ ⊗ v)` at `x`. -/
theorem hasFDerivAt_exp_smul_slice (hφ : ∀ x, HasFDerivAt φ (ℓ x) x)
    (v : ParabolicC2HolderSpace α E F ht) (t : Icc t₀ t₁) (x : E) :
    HasFDerivAt (fun y ↦ Real.exp (φ y) • v (slabMk y t))
      (Real.exp (φ x) • (spatialFDerivL v (slabMk x t) + (ℓ x).smulRight (v (slabMk x t)))) x := by
  refine (((hφ x).exp).smul (v.hasSpatialFDerivAt t x)).congr_fderiv ?_
  ext h
  simp [smul_add, smul_smul]

/-- **The Hessian of a weighted slice.** For `v ∈ C_b^{2+α,1+α/2}`, `ℓ = Dφ` and `M = D²φ`, the
gradient of `y ↦ exp (φ y) • v (y, t)` has derivative
`exp (φ x) • (D_x²v + ℓ ⊗ D_xv + (ℓ ⊗ D_xv)ᵀ + (M + ℓ ⊗ ℓ) ⊗ v)` at `x`, where `Q ⊗ y` is
`(h, k) ↦ Q h k • y`. -/
theorem hasFDerivAt_fderiv_exp_smul_slice (hφ : ∀ x, HasFDerivAt φ (ℓ x) x)
    (hℓ : ∀ x, HasFDerivAt (fun y ↦ ℓ y) (M x) x) (v : ParabolicC2HolderSpace α E F ht)
    (t : Icc t₀ t₁) (x : E) :
    HasFDerivAt (fderiv ℝ fun y ↦ Real.exp (φ y) • v (slabMk y t))
      (Real.exp (φ x) • (spatialSecondFDerivL v (slabMk x t) +
        ((ℓ x).smulRight (spatialFDerivL v (slabMk x t)) +
          ((ℓ x).smulRight (spatialFDerivL v (slabMk x t))).flip) +
        ((smulRightL ℝ E F).flip (v (slabMk x t))).comp (M x + (ℓ x).smulRight (ℓ x)))) x := by
  rw [funext fun y ↦ (hasFDerivAt_exp_smul_slice hφ v t y).fderiv]
  have hK := (v.hasSpatialSecondFDerivAt t x).add
    ((smulRightL ℝ E F).hasFDerivAt_of_bilinear (hℓ x) (v.hasSpatialFDerivAt t x))
  refine (((hφ x).exp).smul hK).congr_fderiv ?_
  ext h k
  simp [mul_smul]
  module

variable (hα : α ≤ 1)

/-- **The conjugation identity** `w P_w v = P (w v)` for the weight `w = exp φ`. Let `ℓ` and `M`
be the gradient and Hessian of `φ`, and let `u = w v` with `v ∈ C_b^{2+α,1+α/2}`. Then at every
point of the slab, `w` times the conjugated operator applied to `v` is the operator
`P u = ∂ₜu - A·D_x²u - B·D_xu - C·u`, computed from the classical derivatives of `u`. The
function `u` need not be bounded. -/
theorem exp_smul_parabolicOperatorL_weightCoeff (hφ : ∀ x, HasFDerivAt φ (ℓ x) x)
    (hℓ : ∀ x, HasFDerivAt (fun y ↦ ℓ y) (M x) x) (v : ParabolicC2HolderSpace α E F ht)
    {u : slab (E := E) t₀ t₁ → F}
    (hu : ∀ p, u p = Real.exp (φ (p : ParabolicSpaceTime E).space) • v p) (x : E)
    (t : Icc t₀ t₁) :
    Real.exp (φ x) • parabolicOperatorL hα A (weightFirstOrderCoeff A B ℓ)
        (weightZerothOrderCoeff A B C ℓ M) v (slabMk x t) =
      derivWithin (timeExtension ht.le u x) (Icc t₀ t₁) t -
        (A (slabMk x t) (fderiv ℝ (fderiv ℝ fun y ↦ u (slabMk y t)) x) +
          B (slabMk x t) (fderiv ℝ (fun y ↦ u (slabMk y t)) x) +
            C (slabMk x t) (u (slabMk x t))) := by
  have hslice : (fun y ↦ u (slabMk y t)) = fun y ↦ Real.exp (φ y) • v (slabMk y t) :=
    funext fun y ↦ by rw [hu, space_slabMk]
  have htime : timeExtension ht.le u x = Real.exp (φ x) • timeExtension ht.le v x :=
    funext fun s ↦ by simp [timeExtension_def, hu]
  rw [hslice, (hasFDerivAt_fderiv_exp_smul_slice hφ hℓ v t x).fderiv,
    (hasFDerivAt_exp_smul_slice hφ v t x).fderiv, htime,
    ((v.hasTimeDerivWithinAt x t).const_smul (Real.exp (φ x))).derivWithin
      (uniqueDiffOn_Icc ht t t.2), hu]
  simp only [parabolicOperatorL_apply, weightFirstOrderCoeff_apply,
    weightZerothOrderCoeff_apply, space_slabMk, map_smul, map_add, smul_sub, smul_add]
  abel

/-- **Weighted solutions.** `v ∈ C_b^{2+α,1+α/2}` solves the conjugated equation `P_w v = g` if
and only if `u = exp φ • v` is a classical solution of `P u = exp φ • g`: forcing terms transform
by division by the weight. -/
theorem parabolicOperatorL_weightCoeff_eq_iff (hφ : ∀ x, HasFDerivAt φ (ℓ x) x)
    (hℓ : ∀ x, HasFDerivAt (fun y ↦ ℓ y) (M x) x) (v : ParabolicC2HolderSpace α E F ht)
    {u : slab (E := E) t₀ t₁ → F}
    (hu : ∀ p, u p = Real.exp (φ (p : ParabolicSpaceTime E).space) • v p)
    (g : HolderSpace α (slab (E := E) t₀ t₁) F) :
    parabolicOperatorL hα A (weightFirstOrderCoeff A B ℓ) (weightZerothOrderCoeff A B C ℓ M) v =
        g ↔
      ∀ (x : E) (t : Icc t₀ t₁), derivWithin (timeExtension ht.le u x) (Icc t₀ t₁) t -
        (A (slabMk x t) (fderiv ℝ (fderiv ℝ fun y ↦ u (slabMk y t)) x) +
          B (slabMk x t) (fderiv ℝ (fun y ↦ u (slabMk y t)) x) +
            C (slabMk x t) (u (slabMk x t))) =
        Real.exp (φ x) • g (slabMk x t) := by
  constructor
  · intro h x t
    rw [← exp_smul_parabolicOperatorL_weightCoeff hα hφ hℓ v hu x t, h]
  · intro h
    refine HolderSpace.ext fun p ↦ ?_
    rw [← slabMk_space_slabTime p]
    have hp := h (p : ParabolicSpaceTime E).space (slabTime p)
    rw [← exp_smul_parabolicOperatorL_weightCoeff hα hφ hℓ v hu] at hp
    exact smul_right_injective F (Real.exp_pos _).ne' hp

end Conjugation

end TauCeti.ParabolicC2HolderSpace

/-! ### The weight `1 + exp x` on the line -/

namespace TauCeti

open Set ParabolicSpaceTime ContinuousLinearMap Real
open scoped NNReal

variable {α : ℝ≥0} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {t₀ t₁ : ℝ}
  {ht : t₀ < t₁} (hα : α ≤ 1)

/-- A local shortcut for the norm on Hessians on the line, needed for the operator norm on the
coefficient space `(ℝ →L[ℝ] ℝ →L[ℝ] F) →L[ℝ] F`. -/
local instance lineNormedAddCommGroupHessian :
    NormedAddCommGroup (ℝ →L[ℝ] ℝ →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on Hessians on the line. -/
local instance lineNormedSpaceHessian : NormedSpace ℝ (ℝ →L[ℝ] ℝ →L[ℝ] F) := inferInstance

/-- The gradient `x ↦ sigmoid x` of `log (1 + exp x)`, as a bounded `α`-Hölder field of covectors
on `ℝ`. -/
def logOneAddExpGrad : HolderSpace α ℝ (ℝ →L[ℝ] ℝ) :=
  (smulRightL ℝ ℝ ℝ).compHolder₂ (HolderSpace.const 1) <| HolderSpace.ofBoundedContinuousFunction
    (BoundedContinuousFunction.ofNormedAddCommGroup sigmoid continuous_sigmoid 1 fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sigmoid_nonneg x)]
      exact sigmoid_le_one x)
    (by simpa using memHolder_iteratedDeriv_sigmoid 0 hα)

/-- The Hessian `x ↦ sigmoid x (1 - sigmoid x)` of `log (1 + exp x)`, as a bounded `α`-Hölder
field of bilinear forms on `ℝ`. -/
def logOneAddExpHess : HolderSpace α ℝ (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) :=
  (smulRightL ℝ ℝ (ℝ →L[ℝ] ℝ)).compHolder₂ (HolderSpace.const 1) <|
    (smulRightL ℝ ℝ ℝ).compHolder₂ (HolderSpace.const 1) <| HolderSpace.ofBoundedContinuousFunction
      (BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ sigmoid x * (1 - sigmoid x))
        (by fun_prop) 1 fun x ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sigmoid_nonneg x)
            (sub_nonneg.2 (sigmoid_le_one x)))]
          nlinarith [sigmoid_nonneg x, sigmoid_le_one x])
      (by simpa [deriv_sigmoid] using memHolder_iteratedDeriv_sigmoid 1 hα)

@[simp]
theorem logOneAddExpGrad_apply (x : ℝ) :
    logOneAddExpGrad hα x = toSpanSingleton ℝ (sigmoid x) := by
  ext
  simp [logOneAddExpGrad]

@[simp]
theorem logOneAddExpHess_apply (x : ℝ) :
    logOneAddExpHess hα x =
      toSpanSingleton ℝ (toSpanSingleton ℝ (sigmoid x * (1 - sigmoid x))) := by
  ext
  simp [logOneAddExpHess]

/-- `logOneAddExpGrad` is the gradient of `x ↦ log (1 + exp x)`. -/
theorem hasFDerivAt_log_one_add_exp (x : ℝ) :
    HasFDerivAt (fun x ↦ log (1 + exp x)) (logOneAddExpGrad hα x) x := by
  simpa using (hasDerivAt_log_one_add_exp x).hasFDerivAt

/-- `logOneAddExpHess` is the derivative of `logOneAddExpGrad`. -/
theorem hasFDerivAt_logOneAddExpGrad (x : ℝ) :
    HasFDerivAt (fun y ↦ logOneAddExpGrad hα y) (logOneAddExpHess hα x) x := by
  have h := ((toSpanSingletonLIE (𝕜 := ℝ) (E := ℝ)).toContinuousLinearEquiv.hasFDerivAt
    ).comp_hasDerivAt x (hasDerivAt_sigmoid x)
  simp only [logOneAddExpGrad_apply, logOneAddExpHess_apply]
  exact h.hasFDerivAt

/-- **The conjugation identity for the weight `1 + exp x` on `ℝ`.** For `u = (1 + exp x) • v`
with `v ∈ C_b^{2+α,1+α/2}`, the operator `P u` computed from the classical derivatives of `u` is
`(1 + exp x)` times the conjugated operator, whose coefficients are bounded parabolic Hölder fields
built from `sigmoid` and its derivative. -/
theorem ParabolicC2HolderSpace.one_add_exp_smul_parabolicOperatorL_weightCoeff
    {A : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ →L[ℝ] F) →L[ℝ] F)}
    {B : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] F) →L[ℝ] F)}
    {C : HolderSpace α (slab (E := ℝ) t₀ t₁) (F →L[ℝ] F)}
    (v : ParabolicC2HolderSpace α ℝ F ht) {u : slab (E := ℝ) t₀ t₁ → F}
    (hu : ∀ p, u p = (1 + exp (p : ParabolicSpaceTime ℝ).space) • v p) (x : ℝ)
    (t : Icc t₀ t₁) :
    (1 + exp x) • parabolicOperatorL hα A (weightFirstOrderCoeff A B (logOneAddExpGrad hα))
        (weightZerothOrderCoeff A B C (logOneAddExpGrad hα) (logOneAddExpHess hα)) v
        (slabMk x t) =
      derivWithin (timeExtension ht.le u x) (Icc t₀ t₁) t -
        (A (slabMk x t) (fderiv ℝ (fderiv ℝ fun y ↦ u (slabMk y t)) x) +
          B (slabMk x t) (fderiv ℝ (fun y ↦ u (slabMk y t)) x) +
            C (slabMk x t) (u (slabMk x t))) := by
  have hexp (y : ℝ) : exp (log (1 + exp y)) = 1 + exp y := exp_log (by positivity)
  simpa only [hexp] using exp_smul_parabolicOperatorL_weightCoeff hα
    (hasFDerivAt_log_one_add_exp hα) (hasFDerivAt_logOneAddExpGrad hα) v
    (fun p ↦ by rw [hu, hexp]) x t

end TauCeti
