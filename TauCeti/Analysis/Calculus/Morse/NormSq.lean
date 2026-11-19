/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Analysis.Calculus.Morse.Prod
public import TauCeti.Analysis.InnerProductSpace.SquaredDistance
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# The Hessian of the squared norm

The squared norm `z ↦ ‖z‖ ^ 2` on a real inner product space is the model of a nondegenerate
minimum. Its second derivative is the constant bilinear form `2 ⟪v, w⟫`
(`TauCeti.fderiv_fderiv_norm_sq_apply`), so its Hessian quadratic form is `v ↦ 2 * ‖v‖ ^ 2` at
every point and its Morse index vanishes everywhere.

These are the real inputs for the Levi form and the inertia of the squared norm of a complex inner
product space, the basic strictly plurisubharmonic function.

The origin is the only critical point of the squared norm, and it is nondegenerate in finite
dimensions; the negated squared norm `z ↦ -‖z‖ ^ 2` has Morse index the dimension. On a product
`E × F` of inner product spaces the separated sum `(u, v) ↦ -‖u‖ ^ 2 + ‖v‖ ^ 2` is the model of a
nondegenerate critical point of index `dim E`, in the normalization of a Morse chart with no factor
`1/2`: its only critical point is the origin, which is nondegenerate, its second derivative is
`((u, v), (u', v')) ↦ -2 ⟪u, u'⟫ + 2 ⟪v, v'⟫`, and its Morse index is `dim E` at every point. For
`E = F = ℝ` this is the saddle `-x² + y²` of the plane, with Hessian `diag(-2, 2)` and index `1`.

## Main results

* `TauCeti.hessianQuadraticForm_norm_sq`: its Hessian quadratic form is `2 * ‖v‖ ^ 2`.
* `TauCeti.morseIndex_norm_sq`: its Morse index vanishes at every point.
* `TauCeti.fderiv_norm_sq_eq_zero_iff` and `TauCeti.isNondegenerateCriticalPoint_norm_sq`: the
  origin is its only critical point, and it is nondegenerate.
* `TauCeti.morseIndex_neg_norm_sq`: the negated squared norm has Morse index the dimension.
* `TauCeti.fderiv_neg_norm_sq_add_norm_sq_eq_zero_iff`,
  `TauCeti.isNondegenerateCriticalPoint_neg_norm_sq_add_norm_sq`,
  `TauCeti.fderiv_fderiv_neg_norm_sq_add_norm_sq_apply` and
  `TauCeti.morseIndex_neg_norm_sq_add_norm_sq`: the critical point, second derivative and Morse
  index of the model `(u, v) ↦ -‖u‖ ^ 2 + ‖v‖ ^ 2`.
-/

public section

open RealInnerProductSpace

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The Hessian quadratic form of the squared norm is `v ↦ 2 * ‖v‖ ^ 2`, at every point. -/
theorem hessianQuadraticForm_norm_sq (x v : F) :
    hessianQuadraticForm (fun z ↦ ‖z‖ ^ 2) x v = 2 * ‖v‖ ^ 2 := by
  rw [hessianQuadraticForm_apply, fderiv_fderiv_norm_sq_apply, real_inner_self_eq_norm_sq]

/-- The squared norm has Morse index zero at every point. -/
@[simp]
theorem morseIndex_norm_sq [FiniteDimensional ℝ F] (x : F) :
    morseIndex (fun z ↦ ‖z‖ ^ 2) x = 0 := by
  rw [morseIndex_def, ← QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero]
  intro v
  rw [hessianQuadraticForm_norm_sq]
  positivity

/-- The derivative of the squared norm vanishes exactly at the origin. -/
theorem fderiv_norm_sq_eq_zero_iff {x : F} : fderiv ℝ (fun z : F ↦ ‖z‖ ^ 2) x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have hx := congr($h x)
  simpa [fderiv_norm_sq] using hx

/-- The Hessian quadratic form of the squared norm is nondegenerate at every point. -/
theorem nondegenerate_hessianQuadraticForm_norm_sq [FiniteDimensional ℝ F] (x : F) :
    (hessianQuadraticForm (fun z : F ↦ ‖z‖ ^ 2) x).Nondegenerate := by
  have hpos : (hessianQuadraticForm (fun z : F ↦ ‖z‖ ^ 2) x).PosDef := fun v hv ↦ by
    rw [hessianQuadraticForm_norm_sq]
    positivity
  exact QuadraticMap.nondegenerate_iff_radical_eq_bot.2
    ((QuadraticForm.posDef_iff_sigNeg_eq_zero_and_radical_eq_bot _).1 hpos).2

/-- **The squared norm has a nondegenerate critical point at the origin**, its minimum. -/
theorem isNondegenerateCriticalPoint_norm_sq [FiniteDimensional ℝ F] :
    IsNondegenerateCriticalPoint (fun z : F ↦ ‖z‖ ^ 2) 0 :=
  isNondegenerateCriticalPoint_iff_hessianQuadraticForm_nondegenerate.2
    ⟨(contDiff_norm_sq ℝ).contDiffAt, fderiv_norm_sq_eq_zero_iff.2 rfl,
      nondegenerate_hessianQuadraticForm_norm_sq 0⟩

/-- **The negated squared norm has Morse index the dimension** at every point: its Hessian is
negative definite. -/
@[simp]
theorem morseIndex_neg_norm_sq [FiniteDimensional ℝ F] (x : F) :
    morseIndex (fun z : F ↦ -‖z‖ ^ 2) x = Module.finrank ℝ F := by
  have h := morseIndex_neg_add_morseIndex_eq_finrank (nondegenerate_hessianQuadraticForm_norm_sq x)
  rw [morseIndex_norm_sq, add_zero, Pi.neg_def] at h
  exact h

/-! ### The model of a nondegenerate critical point of index `dim E` -/

section Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] in
/-- The model `(u, v) ↦ -‖u‖ ^ 2 + ‖v‖ ^ 2` as a separated sum. -/
private theorem neg_norm_sq_add_norm_sq_eq_comp :
    (fun p : E × F ↦ -‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) =
      (fun u : E ↦ -‖u‖ ^ 2) ∘ Prod.fst + (fun v : F ↦ ‖v‖ ^ 2) ∘ Prod.snd :=
  rfl

/-- The only critical point of the model `(u, v) ↦ -‖u‖ ^ 2 + ‖v‖ ^ 2` is the origin. -/
theorem fderiv_neg_norm_sq_add_norm_sq_eq_zero_iff {p : E × F} :
    fderiv ℝ (fun p : E × F ↦ -‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) p = 0 ↔ p = 0 := by
  obtain ⟨u, v⟩ := p
  have hu : DifferentiableAt ℝ (fun u : E ↦ -‖u‖ ^ 2) u :=
    ((contDiff_norm_sq ℝ).differentiable one_ne_zero u).neg
  rw [neg_norm_sq_add_norm_sq_eq_comp, fderiv_comp_fst_add_comp_snd_eq_zero_iff hu
    ((contDiff_norm_sq ℝ).differentiable one_ne_zero v), fderiv_fun_neg, neg_eq_zero,
    fderiv_norm_sq_eq_zero_iff, fderiv_norm_sq_eq_zero_iff, Prod.mk_eq_zero]

/-- **The second derivative of the model** `(u, v) ↦ -‖u‖ ^ 2 + ‖v‖ ^ 2` is the constant bilinear
form `((u, v), (u', v')) ↦ -2 ⟪u, u'⟫ + 2 ⟪v, v'⟫`. -/
theorem fderiv_fderiv_neg_norm_sq_add_norm_sq_apply (p v w : E × F) :
    fderiv ℝ (fderiv ℝ (fun p : E × F ↦ -‖p.1‖ ^ 2 + ‖p.2‖ ^ 2)) p v w =
      -2 * ⟪v.1, w.1⟫ + 2 * ⟪v.2, w.2⟫ := by
  have hneg : fderiv ℝ (fun u : E ↦ -‖u‖ ^ 2) = -fderiv ℝ (fun u : E ↦ ‖u‖ ^ 2) := by
    ext u : 1
    exact fderiv_fun_neg
  have hu : ContDiffAt ℝ 2 (fun u : E ↦ -‖u‖ ^ 2) p.1 := (contDiff_norm_sq ℝ).neg.contDiffAt
  rw [neg_norm_sq_add_norm_sq_eq_comp, fderiv_fderiv_comp_fst_add_comp_snd hu
    (contDiff_norm_sq ℝ).contDiffAt, hneg, fderiv_neg]
  simp [ContinuousLinearMap.coprodEquivL_apply_apply, fderiv_fderiv_norm_sq_apply]

/-- **The origin is a nondegenerate critical point of the model**
`(u, v) ↦ -‖u‖ ^ 2 + ‖v‖ ^ 2` in finite dimensions. -/
theorem isNondegenerateCriticalPoint_neg_norm_sq_add_norm_sq [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] :
    IsNondegenerateCriticalPoint (fun p : E × F ↦ -‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) 0 := by
  rw [neg_norm_sq_add_norm_sq_eq_comp, ← Prod.mk_zero_zero]
  exact isNondegenerateCriticalPoint_norm_sq.neg.comp_fst_add_comp_snd
    isNondegenerateCriticalPoint_norm_sq

/-- **The model `(u, v) ↦ -‖u‖ ^ 2 + ‖v‖ ^ 2` has Morse index `dim E`** at every point. -/
@[simp]
theorem morseIndex_neg_norm_sq_add_norm_sq [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (p : E × F) :
    morseIndex (fun p : E × F ↦ -‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) p = Module.finrank ℝ E := by
  rw [neg_norm_sq_add_norm_sq_eq_comp, morseIndex_comp_fst_add_comp_snd
    (contDiff_norm_sq ℝ).neg.contDiffAt (contDiff_norm_sq ℝ).contDiffAt, morseIndex_neg_norm_sq,
    morseIndex_norm_sq, add_zero]

end Model

end TauCeti
