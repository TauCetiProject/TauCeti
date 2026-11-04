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
