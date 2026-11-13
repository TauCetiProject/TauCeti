/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.Calculus.Morse.Basic
public import TauCeti.Analysis.Calculus.Morse.FlowExistence
public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Analysis.Calculus.Morse.Linearization
public import TauCeti.Analysis.Calculus.Morse.Stable
public import TauCeti.Analysis.Calculus.Morse.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.Morse.NormSq
import TauCeti.Analysis.Normed.Lp.ProdLp

/-!
# The split quadratic model of a Morse flow

This file studies the standard split-quadratic example of a negative-gradient flow.  On a product
of real Hilbert spaces, put

`q(x, y) = (‖x‖² - ‖y‖²) / 2`.

Its gradient is `(x, -y)`, so its negative-gradient flow is

`φ t (x, y) = (exp (-t) • x, exp t • y)`.

The explicit flow and its stable and unstable set formulas are defined for real topological
modules with continuous scalar multiplication; only the expanding factor needs to be Hausdorff.
The Fréchet-derivative critical-point characterization holds on arbitrary real inner product spaces,
while the gradient and nondegeneracy statements use real Hilbert spaces.  The stable set
of the origin is the first coordinate plane and the unstable set is the second coordinate plane.
Thus the two sets in this normalized linear example are genuine closed linear subspaces, rather
than only sets defined by asymptotic convergence.  For a general Morse critical point, the metric
and Hessian determine the corresponding linearized gradient flow and its contraction rates.

## Main declarations

* `TauCeti.splitQuadratic`, `TauCeti.continuous_splitQuadratic`,
  `TauCeti.differentiable_splitQuadratic`, `TauCeti.contDiff_splitQuadratic`: the standard split
  quadratic function and its regularity.
* `TauCeti.fderiv_splitQuadratic`, `TauCeti.fderiv_splitQuadratic_eq_zero_iff`,
  `TauCeti.gradient_splitQuadratic`, `TauCeti.hessianOperator_splitQuadratic_apply`,
  `TauCeti.hessianQuadraticForm_splitQuadratic_apply`, `TauCeti.morseIndex_splitQuadratic`: its
  derivatives, unique critical point `0`, Hessian `(x, -y)`, and Morse index `dim Eᵤ`.
* `TauCeti.lipschitzWith_gradient_splitQuadratic`,
  `TauCeti.isNondegenerateCriticalPoint_splitQuadratic_zero`,
  `TauCeti.isNondegenerateCriticalPoint_splitQuadratic_iff`,
  `TauCeti.hasNondegenerateCriticalPointsOn_splitQuadratic`: global `1`-Lipschitz gradient and
  nondegeneracy at `0`.
* `TauCeti.splitQuadraticFlow`, `Flow.isNegativeGradient_splitQuadraticFlow`,
  `TauCeti.negativeGradientFlow_splitQuadratic`, `TauCeti.eq_splitQuadraticFlow_of_isIntegralCurve`,
  `TauCeti.eq_zero_of_isIntegralCurve_splitQuadratic`: explicit negative-gradient flow and global
  trajectory classification.
* `Flow.stableSet_splitQuadraticFlow_zero`: the stable set is the first coordinate plane.
* `Flow.unstableSet_splitQuadraticFlow_zero`: the unstable set is the second coordinate plane.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapters 1--2.
-/

public section

open Filter Function InnerProductSpace Set Topology
open scoped Gradient

noncomputable section

variable {Eₛ Eᵤ : Type*}

namespace TauCeti

section Quadratic

variable [NormedAddCommGroup Eₛ] [NormedAddCommGroup Eᵤ]

/-- The standard split quadratic function, positive on the first factor and negative on the
second.  The factor `2⁻¹` normalizes its gradient to `(x, -y)`. -/
def splitQuadratic (z : WithLp 2 (Eₛ × Eᵤ)) : ℝ :=
  (‖z.fst‖ ^ 2 - ‖z.snd‖ ^ 2) / 2

/-- Evaluation of the standard split quadratic function. -/
@[simp]
theorem splitQuadratic_apply (z : WithLp 2 (Eₛ × Eᵤ)) :
    splitQuadratic z = (‖z.fst‖ ^ 2 - ‖z.snd‖ ^ 2) / 2 :=
  (rfl)

/-- The split quadratic function is continuous on any `L²` product of normed additive groups. -/
@[fun_prop]
theorem continuous_splitQuadratic : Continuous (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) :=
  (((continuous_fst.comp (WithLp.prod_continuous_ofLp 2 Eₛ Eᵤ)).norm.pow 2).sub
    ((continuous_snd.comp (WithLp.prod_continuous_ofLp 2 Eₛ Eᵤ)).norm.pow 2)).div_const 2

/-- The Fréchet derivative of `splitQuadratic` at `z` is `innerSL ℝ (z.fst, -z.snd)`. -/
theorem hasFDerivAt_splitQuadratic [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    (z : WithLp 2 (Eₛ × Eᵤ)) :
    HasFDerivAt (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ))
      (innerSL ℝ (WithLp.toLp 2 (z.fst, -z.snd))) z := by
  convert ((((WithLp.fstL 2 ℝ Eₛ Eᵤ).hasFDerivAt (x := z)).norm_sq.sub
    (((WithLp.sndL 2 ℝ Eₛ Eᵤ).hasFDerivAt (x := z)).norm_sq)).const_mul (2 : ℝ)⁻¹) using 1 <;>
    ext w <;> simp [splitQuadratic, WithLp.prod_inner_apply] <;> ring

/-- Formula for the Fréchet derivative of the split quadratic function. -/
@[simp]
theorem fderiv_splitQuadratic [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    (z : WithLp 2 (Eₛ × Eᵤ)) :
    fderiv ℝ (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) z =
      innerSL ℝ (WithLp.toLp 2 (z.fst, -z.snd)) :=
  (hasFDerivAt_splitQuadratic z).fderiv

/-- The split quadratic function is differentiable on any product of real inner product spaces. -/
@[fun_prop]
theorem differentiable_splitQuadratic [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ] :
    Differentiable ℝ (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) :=
  fun z ↦ (hasFDerivAt_splitQuadratic z).differentiableAt

/-- The origin is the unique critical point of `splitQuadratic` on real inner product spaces. -/
theorem fderiv_splitQuadratic_eq_zero_iff [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    (z : WithLp 2 (Eₛ × Eᵤ)) :
    fderiv ℝ (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) z = 0 ↔ z = 0 := by
  rw [fderiv_splitQuadratic, ← map_zero (innerSL ℝ), innerSL_inj]
  exact ⟨fun h ↦ WithLp.prod_ext (by simpa using congrArg WithLp.fst h)
    (by simpa using congrArg WithLp.snd h), fun h ↦ by simp [h]⟩

/-- The gradient of the split quadratic function is the identity on the first factor and minus
the identity on the second. -/
theorem hasGradientAt_splitQuadratic [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    [CompleteSpace Eₛ] [CompleteSpace Eᵤ]
    (z : WithLp 2 (Eₛ × Eᵤ)) :
    HasGradientAt (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ))
      (WithLp.toLp 2 (z.fst, -z.snd)) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact (hasFDerivAt_splitQuadratic z).congr_fderiv (by ext w; simp)

/-- Formula for the gradient of the split quadratic function. -/
@[simp]
theorem gradient_splitQuadratic [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    [CompleteSpace Eₛ] [CompleteSpace Eᵤ]
    (z : WithLp 2 (Eₛ × Eᵤ)) :
    ∇ (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) z =
      WithLp.toLp 2 (z.fst, -z.snd) := by
  exact (hasGradientAt_splitQuadratic z).gradient

/-- The origin is the unique critical point of the split quadratic function. -/
theorem gradient_splitQuadratic_eq_zero_iff [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    [CompleteSpace Eₛ] [CompleteSpace Eᵤ]
    (z : WithLp 2 (Eₛ × Eᵤ)) :
    ∇ (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) z = 0 ↔ z = 0 := by
  rw [gradient_splitQuadratic]
  refine ⟨fun h ↦ WithLp.prod_ext (by simpa using congrArg WithLp.fst h)
    (by simpa using congrArg WithLp.snd h), ?_⟩
  rintro rfl
  simp

/-- The gradient of the split quadratic function is an isometry of the underlying space, hence in
particular globally `1`-Lipschitz.  This is the hypothesis under which the negative gradient flow
of a function exists on the whole line. -/
theorem lipschitzWith_gradient_splitQuadratic [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    [CompleteSpace Eₛ] [CompleteSpace Eᵤ] :
    LipschitzWith 1 (∇ (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ))) := by
  refine LipschitzWith.of_dist_le_mul fun z w ↦ ?_
  rw [NNReal.coe_one, one_mul, gradient_splitQuadratic, gradient_splitQuadratic,
    WithLp.prod_dist_eq_of_L2, WithLp.prod_dist_eq_of_L2]
  simp

/-- The origin is a nondegenerate critical point of the split quadratic function. -/
theorem isNondegenerateCriticalPoint_splitQuadratic_zero
    [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    [CompleteSpace Eₛ] [CompleteSpace Eᵤ] :
    IsNondegenerateCriticalPoint (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) 0 := by
  -- Polarize the quadratic using the involution `(x, y) ↦ (x, -y)` and the Riesz equivalence.
  let e : WithLp 2 (Eₛ × Eᵤ) ≃L[ℝ] WithLp 2 (Eₛ × Eᵤ) :=
    (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ Eₛ)
      (LinearIsometryEquiv.neg ℝ : Eᵤ ≃ₗᵢ[ℝ] Eᵤ)).toContinuousLinearEquiv
  let half : WithLp 2 (Eₛ × Eᵤ) ≃L[ℝ] WithLp 2 (Eₛ × Eᵤ) :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ)⁻¹ (by norm_num))
  let BEquiv : WithLp 2 (Eₛ × Eᵤ) ≃L[ℝ] WithLp 2 (Eₛ × Eᵤ) →L[ℝ] ℝ :=
    (e.trans half).trans
      (InnerProductSpace.toDual ℝ (WithLp 2 (Eₛ × Eᵤ))).toContinuousLinearEquiv
  let B : WithLp 2 (Eₛ × Eᵤ) →L[ℝ] WithLp 2 (Eₛ × Eᵤ) →L[ℝ] ℝ :=
    BEquiv
  have hsymm : B.flip = B := by
    ext z w
    simp [B, BEquiv, half, e, WithLp.prod_inner_apply, real_inner_comm]
  have hB : B.IsInvertible := by
    exact ⟨BEquiv, rfl⟩
  have h := ContinuousLinearMap.isNondegenerateCriticalPoint_apply_self_of_flip_eq_self B hsymm hB
  convert h using 1
  funext z
  simp [B, BEquiv, half, e, splitQuadratic, WithLp.prod_inner_apply]
  ring

/-- The origin is the unique nondegenerate critical point of the split quadratic function. -/
@[simp]
theorem isNondegenerateCriticalPoint_splitQuadratic_iff
    [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ] [CompleteSpace Eₛ] [CompleteSpace Eᵤ]
    {z : WithLp 2 (Eₛ × Eᵤ)} :
    IsNondegenerateCriticalPoint (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) z ↔ z = 0 :=
  ⟨fun hz ↦ (fderiv_splitQuadratic_eq_zero_iff z).1 hz.fderiv_eq_zero,
    by rintro rfl; exact isNondegenerateCriticalPoint_splitQuadratic_zero⟩

/-- Every critical point of `splitQuadratic` on real Hilbert spaces is nondegenerate. -/
theorem hasNondegenerateCriticalPointsOn_splitQuadratic
    [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ] [CompleteSpace Eₛ] [CompleteSpace Eᵤ] :
    HasNondegenerateCriticalPointsOn (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) univ :=
  hasNondegenerateCriticalPointsOn_iff.2 fun z _ hz ↦
    isNondegenerateCriticalPoint_splitQuadratic_iff.2 ((fderiv_splitQuadratic_eq_zero_iff z).1 hz)

/-- The split quadratic function is smooth on any product of real inner product spaces. -/
@[fun_prop]
theorem contDiff_splitQuadratic [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ] {n : WithTop ℕ∞} :
    ContDiff ℝ n (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) :=
  (((contDiff_norm_sq ℝ).comp (WithLp.fstL 2 ℝ Eₛ Eᵤ).contDiff).sub
    ((contDiff_norm_sq ℝ).comp (WithLp.sndL 2 ℝ Eₛ Eᵤ).contDiff)).div_const 2

/-- The Hessian operator of `splitQuadratic` is `(x, y) ↦ (x, -y)` at every point. -/
@[simp]
theorem hessianOperator_splitQuadratic_apply [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    [CompleteSpace Eₛ] [CompleteSpace Eᵤ] (z v : WithLp 2 (Eₛ × Eᵤ)) :
    hessianOperator (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) z v = WithLp.toLp 2 (v.fst, -v.snd) := by
  let L : WithLp 2 (Eₛ × Eᵤ) →L[ℝ] WithLp 2 (Eₛ × Eᵤ) :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ Eₛ Eᵤ).symm : Eₛ × Eᵤ →L[ℝ] WithLp 2 (Eₛ × Eᵤ)).comp
      ((WithLp.fstL 2 ℝ Eₛ Eᵤ).prod (-WithLp.sndL 2 ℝ Eₛ Eᵤ))
  have hgrad : ∇ (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) = L := by funext w; simp [L]
  rw [← fderiv_gradient, hgrad, L.fderiv]; simp [L]

/-- `splitQuadratic` is half the separated sum of `‖·‖²` and `-‖·‖²`. -/
theorem splitQuadratic_eq_smul_separatedSum :
    (splitQuadratic : WithLp 2 (Eₛ × Eᵤ) → ℝ) =
      (2 : ℝ)⁻¹ • separatedSum (fun x : Eₛ ↦ ‖x‖ ^ 2) (-(fun y : Eᵤ ↦ ‖y‖ ^ 2)) := by
  funext w; simp [splitQuadratic]; ring

/-- The Hessian quadratic form of `splitQuadratic` is `‖v.fst‖² - ‖v.snd‖²` at every point. -/
theorem hessianQuadraticForm_splitQuadratic_apply [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    (z v : WithLp 2 (Eₛ × Eᵤ)) :
    hessianQuadraticForm (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) z v =
      ‖v.fst‖ ^ 2 - ‖v.snd‖ ^ 2 := by
  rw [splitQuadratic_eq_smul_separatedSum, hessianQuadraticForm_smul, smul_apply,
    hessianQuadraticForm_separatedSum_apply (g := -(fun y : Eᵤ ↦ ‖y‖ ^ 2))
      (contDiff_norm_sq ℝ).contDiffAt (contDiff_norm_sq ℝ).contDiffAt.neg,
    hessianQuadraticForm_neg, neg_apply, hessianQuadraticForm_norm_sq, hessianQuadraticForm_norm_sq,
    smul_eq_mul]
  ring

/-- On finite-dimensional inner product spaces, `morseIndex splitQuadratic z = dim Eᵤ`. -/
@[simp]
theorem morseIndex_splitQuadratic [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    [FiniteDimensional ℝ Eₛ] [FiniteDimensional ℝ Eᵤ] (z : WithLp 2 (Eₛ × Eᵤ)) :
    morseIndex (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) z = Module.finrank ℝ Eᵤ := by
  rw [splitQuadratic_eq_smul_separatedSum, morseIndex_def, hessianQuadraticForm_smul,
    QuadraticForm.sigNeg_smul_of_pos _ (by positivity), ← morseIndex_def,
    morseIndex_separatedSum (g := -(fun y : Eᵤ ↦ ‖y‖ ^ 2))
      (contDiff_norm_sq ℝ).contDiffAt (contDiff_norm_sq ℝ).contDiffAt.neg,
    morseIndex_norm_sq, zero_add, ← neg_hessianQuadraticForm_posDef_iff_morseIndex_eq_finrank]
  intro u hu
  rw [neg_apply, hessianQuadraticForm_neg, neg_apply, neg_neg, hessianQuadraticForm_norm_sq]
  exact mul_pos two_pos (pow_pos (norm_pos_iff.2 hu) 2)

end Quadratic

section Flow

variable [TopologicalSpace Eₛ] [TopologicalSpace Eᵤ]
  [AddCommGroup Eₛ] [AddCommGroup Eᵤ] [Module ℝ Eₛ] [Module ℝ Eᵤ]
  [ContinuousSMul ℝ Eₛ] [ContinuousSMul ℝ Eᵤ]

/-- The standard split hyperbolic flow. Its first coordinate contracts in forward time and its
second coordinate contracts in backward time. On real Hilbert spaces it is the negative-gradient
flow of `splitQuadratic`. -/
def splitQuadraticFlow : _root_.Flow ℝ (WithLp 2 (Eₛ × Eᵤ)) where
  toFun t z := WithLp.toLp 2 (Real.exp (-t) • z.fst, Real.exp t • z.snd)
  cont' := by fun_prop
  map_add' t u z :=
    WithLp.prod_ext (by simp [Real.exp_add, mul_smul, mul_comm])
      (by simp [Real.exp_add, mul_smul, mul_comm])
  map_zero' z := WithLp.prod_ext (by simp) (by simp)

/-- Evaluation of the split quadratic flow. -/
@[simp]
theorem splitQuadraticFlow_apply (t : ℝ) (z : WithLp 2 (Eₛ × Eᵤ)) :
    splitQuadraticFlow t z =
      WithLp.toLp 2 (Real.exp (-t) • z.fst, Real.exp t • z.snd) :=
  (rfl)

end Flow

end TauCeti

section GradientFlow

variable [NormedAddCommGroup Eₛ] [NormedAddCommGroup Eᵤ]

/-- Every orbit of the explicit split flow solves the negative-gradient equation for
`TauCeti.splitQuadratic`. -/
theorem Flow.isNegativeGradient_splitQuadraticFlow
    [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    [CompleteSpace Eₛ] [CompleteSpace Eᵤ] :
    Flow.IsNegativeGradient (TauCeti.splitQuadraticFlow (Eₛ := Eₛ) (Eᵤ := Eᵤ))
      (TauCeti.splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) := by
  rw [Flow.isNegativeGradient_iff]
  intro z t
  have hs : HasDerivAt (fun u : ℝ ↦ Real.exp (-u) • z.fst)
      (-Real.exp (-t) • z.fst) t := by
    convert ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).smul_const z.fst using 1 <;>
      simp
  have hu : HasDerivAt (fun u : ℝ ↦ Real.exp u • z.snd) (Real.exp t • z.snd) t :=
    (Real.hasDerivAt_exp t).smul_const z.snd
  have hprod := hs.hasFDerivAt.prodMk hu.hasFDerivAt
  have htoLp :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ Eₛ Eᵤ).symm.hasFDerivAt.comp t hprod
  convert htoLp.hasDerivAt using 1
  · funext u
    simp only [TauCeti.splitQuadraticFlow_apply, Function.comp_apply,
      WithLp.prodContinuousLinearEquiv_symm_apply]
  · -- Expose the vector-field value so the explicit gradient formula rewrites the goal.
    change -∇ TauCeti.splitQuadratic
        (TauCeti.splitQuadraticFlow (Eₛ := Eₛ) (Eᵤ := Eᵤ) t z) = _
    rw [TauCeti.gradient_splitQuadratic]
    exact WithLp.prod_ext (by simp) (by simp)

namespace TauCeti

/-- On the split quadratic model, the negative gradient flow built from a globally Lipschitz
gradient is the explicit hyperbolic flow. -/
theorem negativeGradientFlow_splitQuadratic [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    [CompleteSpace Eₛ] [CompleteSpace Eᵤ] :
    negativeGradientFlow (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ))
        lipschitzWith_gradient_splitQuadratic = splitQuadraticFlow := by
  refine _root_.Flow.ext fun t z ↦ ?_
  have hγ := (Flow.isNegativeGradient_splitQuadraticFlow (Eₛ := Eₛ) (Eᵤ := Eᵤ)).isIntegralCurve z
  have h := eq_negativeGradientFlow (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ))
    lipschitzWith_gradient_splitQuadratic hγ t
  have h0 : splitQuadraticFlow (Eₛ := Eₛ) (Eᵤ := Eᵤ) 0 z = z := _root_.Flow.map_zero_apply _ z
  rw [h0] at h
  exact h.symm

/-- Every negative-gradient trajectory of `splitQuadratic` is a flow line of `splitQuadraticFlow`.
-/
theorem eq_splitQuadraticFlow_of_isIntegralCurve [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    [CompleteSpace Eₛ] [CompleteSpace Eᵤ] {γ : ℝ → WithLp 2 (Eₛ × Eᵤ)}
    (hγ : IsIntegralCurve γ fun _ z ↦ -∇ (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) z) :
    γ = fun t ↦ splitQuadraticFlow t (γ 0) :=
  funext fun t ↦ negativeGradientFlow_splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ) ▸
    eq_negativeGradientFlow _ lipschitzWith_gradient_splitQuadratic hγ t

/-- Any global negative-gradient trajectory of `splitQuadratic` with finite limits at `-∞` and `+∞`
is identically zero, with both limits equal to `0`. -/
theorem eq_zero_of_isIntegralCurve_splitQuadratic [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    [CompleteSpace Eₛ] [CompleteSpace Eᵤ] {ζ : ℝ → WithLp 2 (Eₛ × Eᵤ)}
    (hζ : IsIntegralCurve ζ (fun _ w ↦ -∇ (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) w))
    {p q : WithLp 2 (Eₛ × Eᵤ)} (hbot : Tendsto ζ atBot (𝓝 p)) (htop : Tendsto ζ atTop (𝓝 q)) :
    p = 0 ∧ q = 0 ∧ ζ = 0 := by
  have hflow := eq_splitQuadraticFlow_of_isIntegralCurve hζ
  have hp : p = 0 := (gradient_splitQuadratic_eq_zero_iff p).1
    ((forall_negativeGradientFlow_eq_self_iff _ lipschitzWith_gradient_splitQuadratic p).1
      (negativeGradientFlow_splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ) ▸
        Flow.fixed_of_mem_unstableSet (Flow.mem_unstableSet.2 (hflow ▸ hbot))))
  have hq : q = 0 := (gradient_splitQuadratic_eq_zero_iff q).1
    ((forall_negativeGradientFlow_eq_self_iff _ lipschitzWith_gradient_splitQuadratic q).1
      (negativeGradientFlow_splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ) ▸
        Flow.fixed_of_mem_stableSet (Flow.mem_stableSet.2 (hflow ▸ htop))))
  subst hp hq
  exact ⟨rfl, rfl, hζ.eq_const_of_tendsto (fun t ↦ differentiable_splitQuadratic (ζ t))
    continuous_splitQuadratic.continuousAt hbot htop⟩

end TauCeti

end GradientFlow

section Asymptotics

variable [TopologicalSpace Eₛ] [TopologicalSpace Eᵤ]
  [AddCommGroup Eₛ] [AddCommGroup Eᵤ] [Module ℝ Eₛ] [Module ℝ Eᵤ]
  [ContinuousSMul ℝ Eₛ] [ContinuousSMul ℝ Eᵤ]

namespace TauCeti

/-- A point converges to the origin in forward time exactly when its expanding coordinate
vanishes. -/
theorem tendsto_splitQuadraticFlow_atTop_nhds_zero_iff [T2Space Eᵤ]
    (z : WithLp 2 (Eₛ × Eᵤ)) :
    Tendsto (fun t ↦ splitQuadraticFlow t z) atTop (𝓝 0) ↔ z.snd = 0 := by
  constructor
  · intro h
    have hu : Tendsto (fun t : ℝ ↦ Real.exp t • z.snd) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (WithLp.sndL 2 ℝ Eₛ Eᵤ).continuous.continuousAt.tendsto.comp h
    have hconst : Tendsto (fun _ : ℝ ↦ z.snd) atTop (𝓝 0) := by
      simpa [smul_smul, ← Real.exp_add] using
        Real.tendsto_exp_neg_atTop_nhds_zero.smul hu
    exact tendsto_nhds_unique tendsto_const_nhds hconst
  · intro hz
    have hs : Tendsto (fun t : ℝ ↦ Real.exp (-t) • z.fst) atTop (𝓝 0) := by
      simpa using Real.tendsto_exp_neg_atTop_nhds_zero.smul_const z.fst
    simpa [Function.comp_def, hz, Prod.mk_zero_zero] using
      (WithLp.prod_continuous_toLp 2 Eₛ Eᵤ).continuousAt.tendsto.comp
        (hs.prodMk_nhds (tendsto_const_nhds (x := (0 : Eᵤ))))

/-- A point converges to the origin in backward time exactly when its expanding-backward
coordinate vanishes. -/
theorem tendsto_splitQuadraticFlow_atBot_nhds_zero_iff [T2Space Eₛ]
    (z : WithLp 2 (Eₛ × Eᵤ)) :
    Tendsto (fun t ↦ splitQuadraticFlow t z) atBot (𝓝 0) ↔ z.fst = 0 := by
  constructor
  · intro h
    have hs : Tendsto (fun t : ℝ ↦ Real.exp (-t) • z.fst) atBot (𝓝 0) := by
      simpa [Function.comp_def] using (WithLp.fstL 2 ℝ Eₛ Eᵤ).continuous.continuousAt.tendsto.comp h
    have hconst : Tendsto (fun _ : ℝ ↦ z.fst) atBot (𝓝 0) := by
      simpa [smul_smul, ← Real.exp_add] using Real.tendsto_exp_atBot.smul hs
    exact tendsto_nhds_unique tendsto_const_nhds hconst
  · intro hz
    have hu : Tendsto (fun t : ℝ ↦ Real.exp t • z.snd) atBot (𝓝 0) := by
      simpa using Real.tendsto_exp_atBot.smul_const z.snd
    simpa [Function.comp_def, hz, Prod.mk_zero_zero] using
      (WithLp.prod_continuous_toLp 2 Eₛ Eᵤ).continuousAt.tendsto.comp
        ((tendsto_const_nhds (x := (0 : Eₛ))).prodMk_nhds hu)

end TauCeti

namespace Flow

/-- The stable set of the split quadratic flow at the origin is the first coordinate plane. -/
@[simp]
theorem stableSet_splitQuadraticFlow_zero [T2Space Eᵤ] :
    stableSet (TauCeti.splitQuadraticFlow (Eₛ := Eₛ) (Eᵤ := Eᵤ)) 0 =
      {z : WithLp 2 (Eₛ × Eᵤ) | z.snd = 0} := by
  ext z
  rw [mem_stableSet, TauCeti.tendsto_splitQuadraticFlow_atTop_nhds_zero_iff]
  rfl

/-- The unstable set of the split quadratic flow at the origin is the second coordinate plane. -/
@[simp]
theorem unstableSet_splitQuadraticFlow_zero [T2Space Eₛ] :
    unstableSet (TauCeti.splitQuadraticFlow (Eₛ := Eₛ) (Eᵤ := Eᵤ)) 0 =
      {z : WithLp 2 (Eₛ × Eᵤ) | z.fst = 0} := by
  ext z
  rw [mem_unstableSet, TauCeti.tendsto_splitQuadraticFlow_atBot_nhds_zero_iff]
  rfl

end Flow

end Asymptotics

end
