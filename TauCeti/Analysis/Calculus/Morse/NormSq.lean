/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SquaredDistance
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.Morse.Prod
import TauCeti.Analysis.Calculus.Morse.ScalarComposition
import TauCeti.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# The Hessian of the squared norm

The squared norm `z ↦ ‖z‖ ^ 2` on a real inner product space is the model of a nondegenerate
minimum. Its second derivative is the constant bilinear form `2 ⟪v, w⟫`
(`TauCeti.fderiv_fderiv_norm_sq_apply`), so its Hessian quadratic form is `v ↦ 2 * ‖v‖ ^ 2` at
every point and its Morse index vanishes everywhere. The hemisphere height `x ↦ √(a - ‖x‖²)`, a
scalar reparametrization of it, has Hessian `-‖v‖² / √a` at the origin.

These are the real inputs for the Levi form and the inertia of the squared norm of a complex inner
product space, the basic strictly plurisubharmonic function.

Separately, a radial function `z ↦ U ‖z‖` has, at `q ≠ 0` and in the radial direction `q`, the
Hessian `U''(‖q‖) ‖q‖²` of its profile `U` along the ray; this is used for the radial Hessian of
central-force Hamiltonians.

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
* `TauCeti.hessianQuadraticForm_sqrt_sub_norm_sq_zero`: the Hessian quadratic form of the
  hemisphere height `√(a - ‖x‖²)` at the origin is `-‖v‖² / √a`.
* `TauCeti.hessianQuadraticForm_comp_norm_apply_self`: in the radial direction, the Hessian of
  a radial function `z ↦ U ‖z‖` at `q ≠ 0` is `U''(‖q‖) ‖q‖²`.
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

/-- The Hessian quadratic form of the hemisphere height `x ↦ √(a - ‖x‖²)` at the origin is
`v ↦ -‖v‖² / √a`. -/
theorem hessianQuadraticForm_sqrt_sub_norm_sq_zero {a : ℝ} (ha : 0 < a) (v : F) :
    hessianQuadraticForm (fun x : F ↦ √(a - ‖x‖ ^ 2)) 0 v = -(‖v‖ ^ 2 / √a) := by
  have hn : ContDiffAt ℝ 2 (fun y : F ↦ ‖y‖ ^ 2) 0 := (contDiff_norm_sq ℝ).contDiffAt
  have hc : fderiv ℝ (fun y : F ↦ ‖y‖ ^ 2) 0 = 0 := by
    simp
  have h0 : ‖(0 : F)‖ ^ 2 = 0 := by simp
  have ha' : a - 0 ≠ 0 := by simpa using ha.ne'
  have hd : HasDerivAt (fun t : ℝ ↦ √(a - t)) (-(1 / (2 * √a))) (‖(0 : F)‖ ^ 2) := by
    rw [h0]
    convert ((hasDerivAt_id' (0 : ℝ)).const_sub a).sqrt ha' using 1
    rw [sub_zero, neg_div]
  have hs : ContDiffAt ℝ 2 (fun t : ℝ ↦ √(a - t)) (‖(0 : F)‖ ^ 2) := by
    rw [h0]
    exact (Real.contDiffAt_sqrt ha').comp 0 (contDiffAt_const.sub contDiffAt_id)
  -- `√(a - ‖x‖²)` is `t ↦ √(a - t)` after the critical function `‖x‖²`; `change` unfolds the
  -- composition.
  change hessianQuadraticForm ((fun t : ℝ ↦ √(a - t)) ∘ fun y : F ↦ ‖y‖ ^ 2) 0 v = _
  rw [hessianQuadraticForm_scalar_comp (f := fun y ↦ ‖y‖ ^ 2) hs hn hc,
    smul_apply, hd.deriv, hessianQuadraticForm_norm_sq, smul_eq_mul]
  field_simp

/-- **The Hessian of a radial function in the radial direction.** If `U` is `C²` at `‖q‖` and
`q ≠ 0`, the Hessian of `z ↦ U ‖z‖` at `q`, evaluated on `q` itself, is the Hessian of `U` at
`‖q‖` evaluated on `‖q‖`, that is `U''(‖q‖) ‖q‖²`. -/
theorem hessianQuadraticForm_comp_norm_apply_self {U : ℝ → ℝ} {q : F}
    (hU : ContDiffAt ℝ 2 U ‖q‖) (hq : q ≠ 0) :
    hessianQuadraticForm (fun z ↦ U ‖z‖) q q = hessianQuadraticForm U ‖q‖ ‖q‖ := by
  -- Restrict to the line `t ↦ t • q`, along which `‖t • q‖ = t ‖q‖` near `t = 1`.
  let L : ℝ →L[ℝ] F := (ContinuousLinearMap.id ℝ ℝ).smulRight q
  let M : ℝ →L[ℝ] ℝ := ‖q‖ • ContinuousLinearMap.id ℝ ℝ
  have hL : L 1 = q := by simp [L]
  have hM : M 1 = ‖q‖ := by simp [M]
  have heq : (fun z : F ↦ U ‖z‖) ∘ L =ᶠ[nhds 1] U ∘ M := by
    filter_upwards [eventually_gt_nhds one_pos] with t ht
    simp [L, M, norm_smul, abs_of_pos ht, mul_comm]
  have h₁ := congr($(L.hessianQuadraticForm_comp (b := 1)
    (f := fun z : F ↦ U ‖z‖) (by rw [hL]; exact hU.comp q (contDiffAt_norm ℝ hq))) 1)
  have h₂ := congr($(M.hessianQuadraticForm_comp (b := 1) (f := U) (by rwa [hM])) 1)
  rw [hessianQuadraticForm_congr_of_eventuallyEq heq, h₂] at h₁
  simpa [hL, hM] using h₁.symm

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

/-! ### Functions of two squared norms -/

section TwoNormSq

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Hessian quadratic form of `u ↦ a * ‖u‖ ^ 2` is `v ↦ 2 * a * ‖v‖ ^ 2`, at every point. -/
theorem hessianQuadraticForm_const_mul_norm_sq (a : ℝ) (x v : F) :
    hessianQuadraticForm (fun z ↦ a * ‖z‖ ^ 2) x v = 2 * a * ‖v‖ ^ 2 := by
  have h : (fun z : F ↦ a * ‖z‖ ^ 2) = a • fun z ↦ ‖z‖ ^ 2 := rfl
  rw [h, hessianQuadraticForm_smul, _root_.smul_apply, hessianQuadraticForm_norm_sq, smul_eq_mul]
  ring

/-- **The Morse index of `u ↦ a * ‖u‖ ^ 2`** is the dimension when `a < 0` and `0` otherwise, at
every point. -/
theorem morseIndex_const_mul_norm_sq [FiniteDimensional ℝ F] (a : ℝ) (x : F) :
    morseIndex (fun z : F ↦ a * ‖z‖ ^ 2) x = if a < 0 then Module.finrank ℝ F else 0 := by
  have h : (fun z : F ↦ a * ‖z‖ ^ 2) = a • fun z ↦ ‖z‖ ^ 2 := rfl
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [ite_eq_left_iff.2 fun h ↦ absurd ha h, h, morseIndex_def, hessianQuadraticForm_smul,
      QuadraticForm.sigNeg_smul_of_neg _ ha, ← morseIndex_neg_norm_sq x, morseIndex_def,
      show (fun z : F ↦ -‖z‖ ^ 2) = -fun z ↦ ‖z‖ ^ 2 from rfl, hessianQuadraticForm_neg,
      sigNeg_neg]
  · simp
  · rw [ite_eq_right_iff.2 fun h ↦ absurd h ha.not_gt, h, morseIndex_def, hessianQuadraticForm_smul,
      QuadraticForm.sigNeg_smul_of_pos _ ha, ← morseIndex_def, morseIndex_norm_sq]

/-- For `a ≠ 0`, the origin is a nondegenerate critical point of `u ↦ a * ‖u‖ ^ 2`. -/
theorem isNondegenerateCriticalPoint_const_mul_norm_sq [FiniteDimensional ℝ F] {a : ℝ}
    (ha : a ≠ 0) : IsNondegenerateCriticalPoint (fun z : F ↦ a * ‖z‖ ^ 2) 0 := by
  have hφ : ContDiffAt ℝ 2 (fun t : ℝ ↦ a * t) (‖(0 : F)‖ ^ 2) :=
    (contDiff_const.mul contDiff_id).contDiffAt
  exact (isNondegenerateCriticalPoint_norm_sq (F := F)).scalar_comp hφ (by simpa using ha)

variable {g : ℝ × ℝ → ℝ} {a b : ℝ}

/-- The map `(u, v) ↦ (‖u‖ ^ 2, ‖v‖ ^ 2)` has vanishing derivative at the origin. -/
private theorem hasFDerivAt_norm_sq_prod_zero :
    HasFDerivAt (fun p : E × F ↦ (‖p.1‖ ^ 2, ‖p.2‖ ^ 2)) (0 : E × F →L[ℝ] ℝ × ℝ) 0 := by
  have h₁ := (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : E × F))).norm_sq
  have h₂ := (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : E × F))).norm_sq
  convert h₁.prodMk h₂ using 1
  ext <;> simp

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] in
/-- A continuous linear functional of `(‖u‖ ^ 2, ‖v‖ ^ 2)` is a separated sum of multiples of the
two squared norms. -/
private theorem comp_norm_sq_prod_eq (ℓ : ℝ × ℝ →L[ℝ] ℝ) :
    (fun p : E × F ↦ ℓ (‖p.1‖ ^ 2, ‖p.2‖ ^ 2)) =
      (fun u : E ↦ ℓ (1, 0) * ‖u‖ ^ 2) ∘ Prod.fst +
        (fun v : F ↦ ℓ (0, 1) * ‖v‖ ^ 2) ∘ Prod.snd := by
  ext p
  have h : ((‖p.1‖ ^ 2, ‖p.2‖ ^ 2) : ℝ × ℝ) = ‖p.1‖ ^ 2 • (1, 0) + ‖p.2‖ ^ 2 • (0, 1) := by
    ext <;> simp
  simp only [Pi.add_apply, Function.comp_apply, h, map_add, map_smul, smul_eq_mul]
  ring

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] in
/-- The base point of `g` in `(u, v) ↦ g (‖u‖ ^ 2, ‖v‖ ^ 2)` at the origin is the origin. -/
private theorem norm_sq_prod_zero :
    ((‖(0 : E × F).1‖ ^ 2, ‖(0 : E × F).2‖ ^ 2) : ℝ × ℝ) = 0 := by
  ext <;> simp

/-- A function of two squared norms is `C²` at the origin when its profile is `C²` there. -/
private theorem contDiffAt_comp_norm_sq_prod_zero (hg : ContDiffAt ℝ 2 g 0) :
    ContDiffAt ℝ 2 (fun p : E × F ↦ g (‖p.1‖ ^ 2, ‖p.2‖ ^ 2)) 0 :=
  (norm_sq_prod_zero (E := E) (F := F) ▸ hg).comp (0 : E × F)
    (((contDiff_norm_sq ℝ).comp contDiff_fst).prodMk
      ((contDiff_norm_sq ℝ).comp contDiff_snd)).contDiffAt

/-- At the origin, the Hessian of `(u, v) ↦ g (‖u‖ ^ 2, ‖v‖ ^ 2)` is that of the separated sum of
multiples of the squared norms by the partial derivatives of `g`. -/
private theorem hessianQuadraticForm_comp_norm_sq_prod_zero_eq (hg : ContDiffAt ℝ 2 g 0) :
    hessianQuadraticForm (fun p : E × F ↦ g (‖p.1‖ ^ 2, ‖p.2‖ ^ 2)) 0 =
      hessianQuadraticForm ((fun u : E ↦ fderiv ℝ g 0 (1, 0) * ‖u‖ ^ 2) ∘ Prod.fst +
        (fun v : F ↦ fderiv ℝ g 0 (0, 1) * ‖v‖ ^ 2) ∘ Prod.snd) 0 := by
  have hφ : ContDiffAt ℝ 2 (fun p : E × F ↦ (‖p.1‖ ^ 2, ‖p.2‖ ^ 2)) 0 :=
    (((contDiff_norm_sq ℝ).comp contDiff_fst).prodMk
      ((contDiff_norm_sq ℝ).comp contDiff_snd)).contDiffAt
  have hg' : ContDiffAt ℝ 2 g (‖(0 : E × F).1‖ ^ 2, ‖(0 : E × F).2‖ ^ 2) :=
    norm_sq_prod_zero (E := E) (F := F) ▸ hg
  have h := hessianQuadraticForm_comp_eq_fderiv_comp (φ := fun p : E × F ↦ (‖p.1‖ ^ 2, ‖p.2‖ ^ 2))
    hg' hφ hasFDerivAt_norm_sq_prod_zero.fderiv
  simp only [Prod.fst_zero, Prod.snd_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Prod.mk_zero_zero] at h
  rw [show (fun p : E × F ↦ g (‖p.1‖ ^ 2, ‖p.2‖ ^ 2)) =
    g ∘ fun p : E × F ↦ (‖p.1‖ ^ 2, ‖p.2‖ ^ 2) from rfl, h, ← comp_norm_sq_prod_eq]
  rfl

/-- The derivative of `g` at the origin, applied to `(1, 0)` and `(0, 1)`, gives the partial
derivatives of `g`. -/
private theorem fderiv_apply_eq_of_hasDerivAt (hg : DifferentiableAt ℝ g 0)
    (ha : HasDerivAt (fun x ↦ g (x, 0)) a 0) (hb : HasDerivAt (fun y ↦ g (0, y)) b 0) :
    fderiv ℝ g 0 (1, 0) = a ∧ fderiv ℝ g 0 (0, 1) = b := by
  have hγ₁ : HasDerivAt (fun x : ℝ ↦ (x, (0 : ℝ))) (1, 0) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 0)
  have hγ₂ : HasDerivAt (fun y : ℝ ↦ ((0 : ℝ), y)) (0, 1) 0 :=
    (hasDerivAt_const 0 0).prodMk (hasDerivAt_id 0)
  have hg' : HasFDerivAt g (fderiv ℝ g 0) ((0 : ℝ), (0 : ℝ)) := hg.hasFDerivAt
  exact ⟨(HasFDerivAt.comp_hasDerivAt (f := fun x : ℝ ↦ (x, (0 : ℝ))) 0 hg' hγ₁).unique ha,
    (HasFDerivAt.comp_hasDerivAt (f := fun y : ℝ ↦ ((0 : ℝ), y)) 0 hg' hγ₂).unique hb⟩

/-- **A function of two squared norms is critical at the origin.** For `g` differentiable at the
origin of `ℝ × ℝ`, the function `(u, v) ↦ g (‖u‖ ^ 2, ‖v‖ ^ 2)` has vanishing derivative at the
origin of `E × F`. -/
theorem fderiv_comp_norm_sq_prod_zero (hg : DifferentiableAt ℝ g 0) :
    fderiv ℝ (fun p : E × F ↦ g (‖p.1‖ ^ 2, ‖p.2‖ ^ 2)) 0 = 0 := by
  have hg' : HasFDerivAt g (fderiv ℝ g 0) (‖(0 : E × F).1‖ ^ 2, ‖(0 : E × F).2‖ ^ 2) := by
    rw [norm_sq_prod_zero]
    exact hg.hasFDerivAt
  exact (hg'.comp (0 : E × F) hasFDerivAt_norm_sq_prod_zero).fderiv.trans
    (ContinuousLinearMap.comp_zero _)

/-- **The Hessian of a function of two squared norms at the origin.** Let `g` be of class `C²` at
the origin of `ℝ × ℝ`, with partial derivatives `a` and `b` there. The Hessian quadratic form of
`(u, v) ↦ g (‖u‖ ^ 2, ‖v‖ ^ 2)` at the origin of `E × F` is `(u, v) ↦ 2 a ‖u‖ ^ 2 + 2 b ‖v‖ ^ 2`.
Only the first derivative of `g` enters, because the squared norms vanish to second order. -/
theorem hessianQuadraticForm_comp_norm_sq_prod_zero (hg : ContDiffAt ℝ 2 g 0)
    (ha : HasDerivAt (fun x ↦ g (x, 0)) a 0) (hb : HasDerivAt (fun y ↦ g (0, y)) b 0)
    (v : E × F) :
    hessianQuadraticForm (fun p : E × F ↦ g (‖p.1‖ ^ 2, ‖p.2‖ ^ 2)) 0 v =
      2 * a * ‖v.1‖ ^ 2 + 2 * b * ‖v.2‖ ^ 2 := by
  obtain ⟨rfl, rfl⟩ := fderiv_apply_eq_of_hasDerivAt (hg.differentiableAt two_ne_zero) ha hb
  rw [hessianQuadraticForm_comp_norm_sq_prod_zero_eq hg, ← Prod.mk_zero_zero,
    hessianQuadraticForm_comp_fst_add_comp_snd (contDiff_const.mul (contDiff_norm_sq ℝ)).contDiffAt
      (contDiff_const.mul (contDiff_norm_sq ℝ)).contDiffAt, QuadraticMap.prod_apply,
    hessianQuadraticForm_const_mul_norm_sq, hessianQuadraticForm_const_mul_norm_sq]

/-- **The Morse index of a function of two squared norms at the origin.** Let `g` be of class `C²`
at the origin of `ℝ × ℝ`, with partial derivatives `a` and `b` there. The Morse index of
`(u, v) ↦ g (‖u‖ ^ 2, ‖v‖ ^ 2)` at the origin counts `dim E` when `a < 0` and `dim F` when
`b < 0`. -/
theorem morseIndex_comp_norm_sq_prod_zero [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (hg : ContDiffAt ℝ 2 g 0) (ha : HasDerivAt (fun x ↦ g (x, 0)) a 0)
    (hb : HasDerivAt (fun y ↦ g (0, y)) b 0) :
    morseIndex (fun p : E × F ↦ g (‖p.1‖ ^ 2, ‖p.2‖ ^ 2)) 0 =
      (if a < 0 then Module.finrank ℝ E else 0) + (if b < 0 then Module.finrank ℝ F else 0) := by
  obtain ⟨rfl, rfl⟩ := fderiv_apply_eq_of_hasDerivAt (hg.differentiableAt two_ne_zero) ha hb
  rw [morseIndex_def, hessianQuadraticForm_comp_norm_sq_prod_zero_eq hg, ← morseIndex_def,
    ← Prod.mk_zero_zero, morseIndex_comp_fst_add_comp_snd
      (contDiff_const.mul (contDiff_norm_sq ℝ)).contDiffAt
      (contDiff_const.mul (contDiff_norm_sq ℝ)).contDiffAt,
    morseIndex_const_mul_norm_sq, morseIndex_const_mul_norm_sq]

/-- **A function of two squared norms has a nondegenerate critical point at the origin** when
both partial derivatives `a` and `b` of its `C²` profile `g` at the origin are nonzero. -/
theorem isNondegenerateCriticalPoint_comp_norm_sq_prod_zero [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (hg : ContDiffAt ℝ 2 g 0) (ha : HasDerivAt (fun x ↦ g (x, 0)) a 0)
    (hb : HasDerivAt (fun y ↦ g (0, y)) b 0) (ha₀ : a ≠ 0) (hb₀ : b ≠ 0) :
    IsNondegenerateCriticalPoint (fun p : E × F ↦ g (‖p.1‖ ^ 2, ‖p.2‖ ^ 2)) 0 := by
  obtain ⟨rfl, rfl⟩ := fderiv_apply_eq_of_hasDerivAt (hg.differentiableAt two_ne_zero) ha hb
  have hm := (isNondegenerateCriticalPoint_const_mul_norm_sq (F := E) ha₀).comp_fst_add_comp_snd
    (isNondegenerateCriticalPoint_const_mul_norm_sq (F := F) hb₀)
  rw [Prod.mk_zero_zero] at hm
  refine isNondegenerateCriticalPoint_iff_hessianQuadraticForm_nondegenerate.2
    ⟨contDiffAt_comp_norm_sq_prod_zero hg,
      fderiv_comp_norm_sq_prod_zero (hg.differentiableAt two_ne_zero), ?_⟩
  rw [hessianQuadraticForm_comp_norm_sq_prod_zero_eq hg]
  exact hm.hessianQuadraticForm_nondegenerate

end TwoNormSq

end TauCeti
