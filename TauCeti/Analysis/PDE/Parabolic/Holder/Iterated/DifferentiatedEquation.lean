/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Operator
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.DirectionalDerivative

/-!
# The differentiated parabolic equation

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `ℝⁿ × [0, T]`, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have scalar coefficients in the parabolic Hölder space `C_{par,b}^{k+1+α}`, `α ≤ 1`. For
`u ∈ C_{par,b}^{k+3+α}` and every direction `e`, the directional derivative `∂ₑu` solves the
differentiated equation

`P (∂ₑu) = ∂ₑ(P u) + (∂ₑaⁱʲ) ∂ᵢ∂ⱼu + (∂ₑbⁱ) ∂ᵢu + (∂ₑc) u`

(`TauCeti.ParabolicCkHolderSpace.parabolicOperatorL_spatialLineDerivL`), whose coefficients are
those of `P` read at order `k` and whose forcing has order `k`. On each time slice, `∂ₑ(P u)` is
computed by the product rule, and the derivatives of `u` are reordered by
`TauCeti.ParabolicCkHolderSpace.timeDerivL_spatialLineDerivL` and
`TauCeti.ParabolicCkHolderSpace.spatialLineDerivL_comm`. No ellipticity is needed. In the
higher-order Schauder theory this is how the order of an estimate is raised by one.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.parabolicOperatorL_spatialLineDerivL`: the differentiated
  equation solved by a directional derivative.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section

noncomputable section

namespace TauCeti

open Set ParabolicSpaceTime
open scoped NNReal

namespace ParabolicCkHolderSpace

attribute [local instance] instNormedAddCommGroupContinuousLinearMapRealId
  instNormedSpaceRealContinuousLinearMapId instNormedAddCommGroupEuclideanCovector
  instNormedSpaceEuclideanCovector instNormedAddCommGroupEuclideanHessian
  instNormedSpaceEuclideanHessian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ℝ≥0}

/-- The values of the Euclidean operator, written out in coordinates through the directional
derivatives `∂ᵢ` in the coordinate directions. -/
private theorem parabolicOperatorL_apply_eq_sum (hα : α ≤ 1) {k : ℕ} {T : ℝ≥0}
    {hT : (0 : ℝ) < T} (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (u : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT)
    (p : slab (E := EuclideanSpace ℝ ι) 0 T) :
    parabolicOperatorL hα (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b)
        (euclideanZerothOrderCoeff c) u p =
      timeDerivL k α _ ℝ hT u p -
        (∑ i, ∑ l, a i l p * spatialLineDerivL (EuclideanSpace.single i 1)
            (spatialLineDerivL (EuclideanSpace.single l 1) u) p +
          ∑ i, b i p * spatialLineDerivL (EuclideanSpace.single i 1) u p + c p * u p) := by
  simp [spatialFDerivBCF_apply, ← Matrix.vec_single_eq_const]

/-- The values of the differentiated equation `parabolicOperatorL_spatialLineDerivL`, with the
lower-order part of the forcing written out in coordinates. On each time slice, `∂ₑ(P u)` is
computed by the product rule, and the derivatives of `u` are reordered by
`TauCeti.ParabolicCkHolderSpace.timeDerivL_spatialLineDerivL` and
`TauCeti.ParabolicCkHolderSpace.spatialLineDerivL_comm`. -/
private theorem parabolicOperatorL_spatialLineDerivL_apply (hα : α ≤ 1) {k : ℕ}
    {T : ℝ≥0} {hT : (0 : ℝ) < T}
    (a : ι → ι → ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
    (u : ParabolicCkHolderSpace (k + 1 + 2) α (EuclideanSpace ℝ ι) ℝ hT) (e : EuclideanSpace ℝ ι)
    (p : slab (E := EuclideanSpace ℝ ι) 0 T) :
    parabolicOperatorL hα
        (euclideanSecondOrderCoeff fun i j ↦ inclusionOfLEL hα k.le_succ (a i j))
        (euclideanFirstOrderCoeff fun i ↦ inclusionOfLEL hα k.le_succ (b i))
        (euclideanZerothOrderCoeff (inclusionOfLEL hα k.le_succ c)) (spatialLineDerivL e u) p =
      spatialLineDerivL e (parabolicOperatorL hα (euclideanSecondOrderCoeff a)
          (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c) u) p +
        (∑ i, ∑ l, spatialLineDerivL e (a i l) p *
            spatialLineDerivL (EuclideanSpace.single i 1) (spatialLineDerivL
              (EuclideanSpace.single l 1)
              (inclusionOfLEL hα (Nat.add_le_add_right k.le_succ 2) u)) p +
          ∑ i, spatialLineDerivL e (b i) p * spatialLineDerivL (EuclideanSpace.single i 1)
              (inclusionOfLEL hα (Nat.add_le_add_right k.le_succ 2) u) p +
          spatialLineDerivL e c p * u p) := by
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  have hD := ((timeDerivL _ α _ ℝ hT u).hasSpatialFDerivAt t x).fun_sub
    (((HasFDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
      HasFDerivAt.fun_sum (u := Finset.univ) fun l _ ↦
      ((a i l).hasSpatialFDerivAt t x).fun_mul ((spatialLineDerivL (EuclideanSpace.single i 1)
        (spatialLineDerivL (EuclideanSpace.single l 1) u)).hasSpatialFDerivAt t x)).fun_add
      (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ ((b i).hasSpatialFDerivAt t x).fun_mul
        ((spatialLineDerivL (EuclideanSpace.single i 1) u).hasSpatialFDerivAt t x))).fun_add
      ((c.hasSpatialFDerivAt t x).fun_mul (u.hasSpatialFDerivAt t x)))
  have hPu := hD.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦
    parabolicOperatorL_apply_eq_sum hα a b c u (slabMk y t))
  rw [spatialLineDerivL_slabMk_eq_lineDeriv, (hPu.hasLineDerivAt e).lineDeriv,
    parabolicOperatorL_apply_eq_sum]
  simp only [_root_.sub_apply, _root_.add_apply, FunLike.coe_sum, Finset.sum_apply,
    _root_.smul_apply, smul_eq_mul, ← spatialLineDerivL_apply_eq_spatialFDerivL,
    inclusionOfLEL_apply]
  have h₁ (i : ι) : spatialLineDerivL e (spatialLineDerivL (EuclideanSpace.single i 1) u) =
      spatialLineDerivL (EuclideanSpace.single i 1) (spatialLineDerivL e u) :=
    spatialLineDerivL_comm _ _ _
  have h₂ (i l : ι) : spatialLineDerivL e (spatialLineDerivL (EuclideanSpace.single i 1)
      (spatialLineDerivL (EuclideanSpace.single l 1) u)) =
      spatialLineDerivL (EuclideanSpace.single i 1)
        (spatialLineDerivL (EuclideanSpace.single l 1) (spatialLineDerivL e u)) := by
    rw [spatialLineDerivL_comm, spatialLineDerivL_comm e]
  have hu₁ (i : ι) : spatialLineDerivL (EuclideanSpace.single i 1)
      (inclusionOfLEL hα (Nat.add_le_add_right k.le_succ 2) u) (slabMk x t) =
      spatialLineDerivL (EuclideanSpace.single i 1) u (slabMk x t) := by
    simp only [spatialLineDerivL_apply,
      mixedDerivL_inclusionOfLEL hα _ u (by omega : 2 * 0 + 1 ≤ k + 2)]
  have hu₂ (i l : ι) : spatialLineDerivL (EuclideanSpace.single i 1) (spatialLineDerivL
      (EuclideanSpace.single l 1) (inclusionOfLEL hα (Nat.add_le_add_right k.le_succ 2) u))
        (slabMk x t) = spatialLineDerivL (EuclideanSpace.single i 1)
          (spatialLineDerivL (EuclideanSpace.single l 1) u) (slabMk x t) := by
    simp only [spatialLineDerivL_apply, mixedDerivL_spatialLineDerivL_apply,
      mixedDerivL_inclusionOfLEL hα _ u (by omega : 2 * 0 + 2 ≤ k + 2)]
  simp only [timeDerivL_spatialLineDerivL, h₁, h₂, hu₁, hu₂, Finset.sum_add_distrib,
    mul_comm (spatialLineDerivL e _ _)]
  ring

/-- **The differentiated equation.** Let `α ≤ 1`, let `aⁱʲ`, `bⁱ`, `c` be coefficients in
`C_{par,b}^{k+1+α}`, and let `u ∈ C_{par,b}^{k+3+α}`. For every direction `e`, the directional
derivative `∂ₑu` satisfies

`P (∂ₑu) = ∂ₑ(P u) + (∂ₑaⁱʲ) ∂ᵢ∂ⱼu + (∂ₑbⁱ) ∂ᵢu + (∂ₑc) u`,

where on the left the coefficients of `P` are read at order `k`, and the last three terms are the
spatial operator with the differentiated coefficients, applied to `u` read at order `k + 2`. This
is the product rule together with the commutation of the derivatives of `u`; no ellipticity is
needed. -/
theorem parabolicOperatorL_spatialLineDerivL (hα : α ≤ 1) {k : ℕ} {T : ℝ≥0}
    {hT : (0 : ℝ) < T} (a : ι → ι → ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
    (u : ParabolicCkHolderSpace (k + 1 + 2) α (EuclideanSpace ℝ ι) ℝ hT) (e : EuclideanSpace ℝ ι) :
    parabolicOperatorL hα
        (euclideanSecondOrderCoeff fun i j ↦ inclusionOfLEL hα k.le_succ (a i j))
        (euclideanFirstOrderCoeff fun i ↦ inclusionOfLEL hα k.le_succ (b i))
        (euclideanZerothOrderCoeff (inclusionOfLEL hα k.le_succ c)) (spatialLineDerivL e u) =
      spatialLineDerivL e (parabolicOperatorL hα (euclideanSecondOrderCoeff a)
          (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c) u) +
        spatialOperatorL hα
          (euclideanSecondOrderCoeff fun i j ↦ spatialLineDerivL e (a i j))
          (euclideanFirstOrderCoeff fun i ↦ spatialLineDerivL e (b i))
          (euclideanZerothOrderCoeff (spatialLineDerivL e c))
          (inclusionOfLEL hα (Nat.add_le_add_right k.le_succ 2) u) :=
  ext fun p ↦ by
    rw [parabolicOperatorL_spatialLineDerivL_apply hα a b c u e, coe_add, Pi.add_apply,
      spatialOperatorL_apply]
    simp [spatialFDerivBCF_apply, ← Matrix.vec_single_eq_const]


end ParabolicCkHolderSpace

end TauCeti
