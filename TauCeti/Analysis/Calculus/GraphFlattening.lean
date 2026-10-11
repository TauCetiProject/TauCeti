/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.LinearAlgebra.Prod
import TauCeti.Topology.Algebra.Module.ProjectionGraph
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Flattening a graph boundary

For a continuous real function `γ` on a normed space `E`, the shear
`(t, y) ↦ (t - γ(y), y)` is an ambient homeomorphism of the product `WithLp 2 (ℝ × E)`.
It carries the region `γ(y) < t` to the positive normal half-space and its graph to
height zero. Its inverse adds `γ(y)` to the normal coordinate.

At points where `γ` is differentiable, the derivative is the linear shear
`(s, z) ↦ (s - Dγ(y) z, z)`. Its determinant is one and its operator norm is at
most `1 + ‖Dγ(y)‖`. These are the chart estimates used to transfer Sobolev trace
and extension operators from a half-space to a domain with a graph boundary.
The shear also preserves Lebesgue measure, requiring only continuity of `γ`.
The homeomorphism is the whole-space instance of
`ContinuousLinearMap.projectionGraphChart`; the differential reuses Mathlib's
`ContinuousLinearEquiv.skewProd`.

The ambient product is `WithLp 2 (ℝ × E)`, so it has the Euclidean norm when `E`
is an inner product space. The topology, derivative and norm estimates do not require
finite dimension or an inner product. The determinant results require finite dimension;
volume preservation additionally requires an inner product.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, §§5.4–5.5
(boundary flattening for extension and trace theorems).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E]

/-- The ambient homeomorphism subtracting the height of a continuous graph from the normal
coordinate. -/
def graphFlattening (γ : E → ℝ) (hγ : Continuous γ) :
    WithLp 2 (ℝ × E) ≃ₜ WithLp 2 (ℝ × E) :=
  -- The integer-linear projection works for every normed additive commutative group.
  let e := WithLp.prodContinuousLinearEquiv 2 ℤ ℝ E
  let P := e.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.prod (0 : WithLp 2 (ℝ × E) →L[ℤ] ℝ)
      (WithLp.sndL 2 ℤ ℝ E)))
  let g := fun z : WithLp 2 (ℝ × E) => WithLp.toLp 2 (γ z.snd, (0 : E))
  let hg : Continuous g := (WithLp.prod_continuous_toLp 2 ℝ E).comp
    ((hγ.comp (WithLp.prod_continuous_ofLp 2 ℝ E).snd).prodMk continuous_const)
  let hPg : ∀ v ∈ (P.range : Set _) ∩ Set.univ, P (g v) = 0 := by
    intros
    simp [P, g]
  (P.projectionGraphChart g isOpen_univ hg.continuousOn hPg)
    |>.toHomeomorphOfSourceEqUnivTargetEqUniv (by simp) (by simp)

/-- The graph-flattening map subtracts the graph height. -/
@[simp] theorem graphFlattening_apply (γ : E → ℝ) (hγ : Continuous γ)
    (x : WithLp 2 (ℝ × E)) :
    graphFlattening γ hγ x = WithLp.toLp 2 (x.fst - γ x.snd, x.snd) := by
  apply (WithLp.ext_iff 2).2
  apply Prod.ext <;> simp [graphFlattening]

/-- The inverse graph-flattening map adds the graph height. -/
@[simp] theorem graphFlattening_symm_apply (γ : E → ℝ) (hγ : Continuous γ)
    (x : WithLp 2 (ℝ × E)) :
    (graphFlattening γ hγ).symm x = WithLp.toLp 2 (x.fst + γ x.snd, x.snd) := by
  apply (WithLp.ext_iff 2).2
  apply Prod.ext <;> simp [graphFlattening]

/-- Inverting graph flattening negates the graph height. -/
theorem graphFlattening_symm (γ : E → ℝ) (hγ : Continuous γ) :
    (graphFlattening γ hγ).symm = graphFlattening (-γ) hγ.neg := by
  ext x
  simp

/-- Flattening takes the region strictly above a graph onto the positive normal half-space. -/
theorem graphFlattening_image_lt (γ : E → ℝ) (hγ : Continuous γ) :
    graphFlattening γ hγ '' {x | γ x.snd < x.fst} =
      {x : WithLp 2 (ℝ × E) | 0 < x.fst} := by
  ext x
  rw [(graphFlattening γ hγ).image_eq_preimage_symm]
  simp

/-- Flattening takes the graph itself onto the zero normal hyperplane. -/
theorem graphFlattening_image_eq (γ : E → ℝ) (hγ : Continuous γ) :
    graphFlattening γ hγ '' {x | x.fst = γ x.snd} =
      {x : WithLp 2 (ℝ × E) | x.fst = 0} := by
  ext x
  rw [(graphFlattening γ hγ).image_eq_preimage_symm]
  simp

section Differential

variable [NormedSpace ℝ E]

private theorem coe_graphFlattening_eq_comp (γ : E → ℝ) (hγ : Continuous γ) :
    ⇑(graphFlattening γ hγ) = (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm ∘
      (fun x : WithLp 2 (ℝ × E) => (x.fst - γ x.snd, x.snd)) := by
  funext x
  simp

/-- The linear shear subtracting `L z` from the normal coordinate. This is the derivative of
`graphFlattening` when the graph height has derivative `L`. -/
def graphFlatteningL (L : E →L[ℝ] ℝ) :
    WithLp 2 (ℝ × E) ≃L[ℝ] WithLp 2 (ℝ × E) :=
  let c := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).trans
    (ContinuousLinearEquiv.prodComm ℝ ℝ E)
  (c.trans ((ContinuousLinearEquiv.refl ℝ E).skewProd
    (ContinuousLinearEquiv.refl ℝ ℝ) (-L))).trans c.symm

/-- The linear graph shear has the expected normal and tangential components. -/
@[simp] theorem graphFlatteningL_apply (L : E →L[ℝ] ℝ) (x : WithLp 2 (ℝ × E)) :
    graphFlatteningL L x = WithLp.toLp 2 (x.fst - L x.snd, x.snd) := by
  simp [graphFlatteningL, sub_eq_add_neg]

/-- Inverting a linear graph shear negates its height functional. -/
@[simp] theorem graphFlatteningL_symm (L : E →L[ℝ] ℝ) :
    (graphFlatteningL L).symm = graphFlatteningL (-L) := by
  ext x
  simp [graphFlatteningL, sub_eq_add_neg]

/-- The norm of the linear graph shear is bounded by one plus the norm of the height
functional, in the `WithLp 2` (L²) product norm. -/
theorem norm_graphFlatteningL_le (L : E →L[ℝ] ℝ) :
    ‖(graphFlatteningL L).toContinuousLinearMap‖ ≤ 1 + ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have hx : graphFlatteningL L x = x - WithLp.toLp 2 (L x.snd, 0) := by
    apply (WithLp.ext_iff 2).2
    apply Prod.ext <;> simp
  calc
    ‖graphFlatteningL L x‖ ≤ ‖x‖ + ‖WithLp.toLp 2 (L x.snd, (0 : E))‖ := by
      rw [hx]
      exact norm_sub_le _ _
    _ = ‖x‖ + ‖L x.snd‖ := by rw [WithLp.norm_toLp_fst]
    _ ≤ ‖x‖ + ‖L‖ * ‖x.snd‖ := add_le_add_right (L.le_opNorm _) _
    _ ≤ ‖x‖ + ‖L‖ * ‖x‖ := by
      gcongr
      exact WithLp.norm_snd_le (x := x)
    _ = (1 + ‖L‖) * ‖x‖ := by ring

/-- The derivative of graph flattening is the linear shear of the height derivative. -/
theorem hasFDerivAt_graphFlattening {γ : E → ℝ} (hγ : Continuous γ)
    {x : WithLp 2 (ℝ × E)} {L : E →L[ℝ] ℝ} (hL : HasFDerivAt γ L x.snd) :
    HasFDerivAt (graphFlattening γ hγ) (graphFlatteningL L).toContinuousLinearMap x := by
  rw [coe_graphFlattening_eq_comp]
  refine ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.hasFDerivAt.comp x
    (((WithLp.fstL 2 ℝ ℝ E).hasFDerivAt.sub
      (hL.comp x (WithLp.sndL 2 ℝ ℝ E).hasFDerivAt)).prodMk
        (WithLp.sndL 2 ℝ ℝ E).hasFDerivAt)).congr_fderiv ?_
  ext z
  simp

/-- The Fréchet derivative of graph flattening, at a differentiability point of the height. -/
theorem fderiv_graphFlattening {γ : E → ℝ} (hγ : Continuous γ)
    {x : WithLp 2 (ℝ × E)} (hx : DifferentiableAt ℝ γ x.snd) :
    fderiv ℝ (graphFlattening γ hγ) x =
      (graphFlatteningL (fderiv ℝ γ x.snd)).toContinuousLinearMap :=
  (hasFDerivAt_graphFlattening hγ hx.hasFDerivAt).fderiv

/-- Graph flattening is `C^n` whenever the height function `γ` is `C^n`. -/
theorem contDiff_graphFlattening {n : WithTop ℕ∞} {γ : E → ℝ}
    (hγ : ContDiff ℝ n γ) : ContDiff ℝ n (graphFlattening γ hγ.continuous) := by
  rw [coe_graphFlattening_eq_comp]
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.contDiff (n := n) |>.comp
    (((WithLp.fstL 2 ℝ ℝ E).contDiff.sub
      (hγ.comp (WithLp.sndL 2 ℝ ℝ E).contDiff)).prodMk
        (WithLp.sndL 2 ℝ ℝ E).contDiff)

/-- The inverse graph chart is `C^n` whenever the height function `γ` is `C^n`. -/
theorem contDiff_graphFlattening_symm {n : WithTop ℕ∞} {γ : E → ℝ}
    (hγ : ContDiff ℝ n γ) : ContDiff ℝ n (graphFlattening γ hγ.continuous).symm := by
  rw [graphFlattening_symm]
  exact contDiff_graphFlattening hγ.neg

variable [FiniteDimensional ℝ E]

/-- A linear graph shear has determinant one. -/
@[simp] theorem det_graphFlatteningL (L : E →L[ℝ] ℝ) :
    LinearMap.det (graphFlatteningL L).toLinearEquiv.toLinearMap = 1 := by
  let c := ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).trans
    (ContinuousLinearEquiv.prodComm ℝ ℝ E)).toLinearEquiv
  have he : (graphFlatteningL L).toLinearEquiv =
      (c.trans ((LinearEquiv.refl ℝ E).skewProd
        (LinearEquiv.refl ℝ ℝ) (-L.toLinearMap))).trans c.symm := by
    apply LinearEquiv.ext
    intro x
    simp [c, LinearEquiv.skewProd_apply, sub_eq_add_neg]
  rw [← LinearEquiv.coe_det, he]
  simpa only [LinearEquiv.symm_symm, LinearEquiv.det_skewProd, LinearEquiv.det_refl,
    mul_one, Units.val_one] using congrArg Units.val
      (LinearEquiv.det_conj ((LinearEquiv.refl ℝ E).skewProd
        (LinearEquiv.refl ℝ ℝ) (-L.toLinearMap)) c.symm)

/-- The Jacobian determinant of graph flattening is one wherever the height is differentiable. -/
theorem det_fderiv_graphFlattening {γ : E → ℝ} (hγ : Continuous γ)
    {x : WithLp 2 (ℝ × E)} (hx : DifferentiableAt ℝ γ x.snd) :
    LinearMap.det (fderiv ℝ (graphFlattening γ hγ) x).toLinearMap = 1 := by
  rw [fderiv_graphFlattening hγ hx]
  exact det_graphFlatteningL _

end Differential

section Volume

variable [MeasurableSpace E] [InnerProductSpace ℝ E] [BorelSpace E]
  [FiniteDimensional ℝ E]

/-- A continuous graph-flattening shear preserves Lebesgue measure. Differentiability of the
height function is unnecessary for this change of variables. -/
theorem measurePreserving_graphFlattening (γ : E → ℝ) (hγ : Continuous γ) :
    MeasurePreserving (graphFlattening γ hγ) := by
  have hs : MeasurePreserving (fun p : E × ℝ => (p.1, p.2 - γ p.1))
      ((volume : Measure E).prod volume) ((volume : Measure E).prod volume) :=
    (MeasurePreserving.id volume).skew_product
      (measurable_snd.sub (hγ.measurable.comp measurable_fst))
      (.of_forall fun y => (measurePreserving_sub_right volume (γ y)).map_eq)
  have h := (WithLp.volume_preserving_toLp ℝ E).comp
    (Measure.measurePreserving_swap.comp
      (hs.comp (Measure.measurePreserving_swap.comp
        (WithLp.volume_preserving_ofLp ℝ E))))
  convert h using 1
  ext x
  simp [Function.comp_def]

end Volume

end TauCeti
