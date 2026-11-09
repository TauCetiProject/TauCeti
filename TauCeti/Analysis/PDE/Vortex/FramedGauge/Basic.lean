/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import TauCeti.Analysis.PDE.Vortex.Deformation
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Algebra.Group.Action.Basic
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Smooth framed gauge transformations of plane vortex fields

The smooth framed gauge group consists of all smooth circle-valued maps on the plane tending
to one at infinity. There is no condition at a finite base point. Its charge-one action is
`(a, α) ↦ (a - u⁻¹ du, u α)`, in the real coordinates of `Vortex.equation`.

The action is free and preserves the equation, the physical energy density and the end phase
framing. It agrees with the existing real-phase action. The logarithmic derivative is expressed
without choosing a real phase. This permits gauges whose phase tends to zero too slowly to lie in an
unweighted Sobolev space. The smooth group here is not a Banach completion.

A function `g` that is smooth near infinity and tends to one is made positive near infinity by a
smooth framed gauge (`TauCeti.Vortex.exists_framedGaugeGroup_mul_eq_norm`). The gauge is `v / |v|`
for `v = 1 + χ (conj g - 1)`, with `χ` a cutoff equal to one outside a large disc, so no logarithm
of the phase is chosen.

The linear part `gaugeLinearAction` fixes the connection variation and rotates its section
variation. This file provides its composition, inverse, pointwise norm, vanishing and regularity
laws, the affine increment and difference identities, and the derivative of the gauge action in
field directions. The gauge's real and imaginary derivatives and the section-coordinate Leibniz
rules are expressed through `gaugeForm`, for use by the deformation operators in
`FramedGauge.Linearization`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex ComplexConjugate Filter
open scoped Topology ContDiff

/-- Smooth circle-valued gauges tending to one at infinity, with no base-point condition. -/
def framedGaugeGroup : Subgroup (ℂ → Circle) where
  carrier := {u | ContDiff ℝ ∞ (fun z ↦ (u z : ℂ)) ∧ Tendsto u (cocompact ℂ) (𝓝 1)}
  one_mem' := ⟨contDiff_const, tendsto_const_nhds⟩
  mul_mem' := by
    rintro u v ⟨hu, htu⟩ ⟨hv, htv⟩
    exact ⟨hu.mul hv, by simpa only [Pi.mul_def, one_mul] using htu.mul htv⟩
  inv_mem' := by
    rintro u ⟨hu, htu⟩
    refine ⟨?_, by simpa only [Pi.inv_def, inv_one] using htu.inv⟩
    simpa only [Pi.inv_apply, Circle.coe_inv_eq_conj, Function.comp_def,
      Complex.conjCLE_apply] using conjCLE.contDiff.comp hu

/-- Membership in the smooth framed group is precisely smoothness and the end condition. -/
@[simp]
theorem mem_framedGaugeGroup (u : ℂ → Circle) :
    u ∈ framedGaugeGroup ↔
      ContDiff ℝ ∞ (fun z ↦ (u z : ℂ)) ∧ Tendsto u (cocompact ℂ) (𝓝 1) := Iff.rfl

/-- The real one-form `Im(u⁻¹ du)`. Multiplication by `i` recovers the imaginary connection
increment; for a circle-valued map the inverse is complex conjugation. -/
def gaugeForm (u : ℂ → Circle) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  imCLM ∘L (ContinuousLinearMap.mul ℝ ℂ (conj (u z : ℂ))) ∘L
    fderiv ℝ (fun w ↦ (u w : ℂ)) z

@[simp]
theorem gaugeForm_apply (u : ℂ → Circle) (z v : ℂ) :
    gaugeForm u z v = (conj (u z : ℂ) * fderiv ℝ (fun w ↦ (u w : ℂ)) z v).im := (rfl)

/-- The charge-one gauge action on the coordinates `a = i(b₁ ds + b₂ dt)`,
`α = 2(p + i q)`. -/
def gaugeTransform (u : ℂ → Circle) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    EuclideanSpace ℝ (Fin 4) :=
  !₂[x z 0 - gaugeForm u z 1, x z 1 - gaugeForm u z I,
    (u z : ℂ).re * x z 2 - (u z : ℂ).im * x z 3,
    (u z : ℂ).im * x z 2 + (u z : ℂ).re * x z 3]

/-- Coordinate formula for the action, without choosing a logarithm of the gauge. -/
theorem gaugeTransform_apply (u : ℂ → Circle) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeTransform u x z =
      !₂[x z 0 - gaugeForm u z 1, x z 1 - gaugeForm u z I,
        (u z : ℂ).re * x z 2 - (u z : ℂ).im * x z 3,
        (u z : ℂ).im * x z 2 + (u z : ℂ).re * x z 3] := (rfl)

/-- The linear part of a charge-one gauge transformation. On variations it fixes the
connection and rotates the section; on the gauge-fixed target it fixes the two real rows
and rotates the complex row. -/
def gaugeLinearAction (u : ℂ → Circle) :
    Module.End ℝ (ℂ → EuclideanSpace ℝ (Fin 4)) where
  toFun y z := !₂[y z 0, y z 1,
    (u z : ℂ).re * y z 2 - (u z : ℂ).im * y z 3,
    (u z : ℂ).im * y z 2 + (u z : ℂ).re * y z 3]
  map_add' y v := by
    ext z i
    fin_cases i <;> simp <;> ring
  map_smul' c y := by
    ext z i
    fin_cases i <;> simp <;> ring

/-- Coordinate formula for the linear gauge action. -/
theorem gaugeLinearAction_apply (u : ℂ → Circle) (y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeLinearAction u y z = !₂[y z 0, y z 1,
      (u z : ℂ).re * y z 2 - (u z : ℂ).im * y z 3,
      (u z : ℂ).im * y z 2 + (u z : ℂ).re * y z 3] := (rfl)

@[simp]
theorem gaugeLinearAction_one (y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    gaugeLinearAction 1 y = y := by
  ext z i
  fin_cases i <;> simp [gaugeLinearAction_apply]

/-- Successive linear gauge actions multiply their gauges. No regularity is needed. -/
theorem gaugeLinearAction_mul (u v : ℂ → Circle) (y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    gaugeLinearAction (u * v) y = gaugeLinearAction u (gaugeLinearAction v y) := by
  ext z i
  fin_cases i <;> simp [gaugeLinearAction_apply, mul_re, mul_im] <;> ring

/-- The inverse gauge undoes the linear action. -/
@[simp]
theorem gaugeLinearAction_inv_gaugeLinearAction (u : ℂ → Circle)
    (y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    gaugeLinearAction u⁻¹ (gaugeLinearAction u y) = y := by
  rw [← gaugeLinearAction_mul, inv_mul_cancel, gaugeLinearAction_one]

/-- The linear action also undoes the inverse gauge. -/
@[simp]
theorem gaugeLinearAction_gaugeLinearAction_inv (u : ℂ → Circle)
    (y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    gaugeLinearAction u (gaugeLinearAction u⁻¹ y) = y := by
  rw [← gaugeLinearAction_mul, mul_inv_cancel, gaugeLinearAction_one]

/-- The linear gauge action is a pointwise isometry for the coefficient metrics of both
the field variations and the gauge-fixed target. -/
@[simp]
theorem norm_gaugeLinearAction (u : ℂ → Circle) (y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    ‖gaugeLinearAction u y z‖ = ‖y z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hn := Circle.re_sq_add_im_sq (u z)
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four, gaugeLinearAction_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (y z 2 ^ 2 + y z 3 ^ 2) * hn

/-- Pointwise vanishing is preserved in both directions. -/
@[simp]
theorem gaugeLinearAction_eq_zero_iff (u : ℂ → Circle)
    (y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeLinearAction u y z = 0 ↔ y z = 0 := by
  rw [← norm_eq_zero, norm_gaugeLinearAction, norm_eq_zero]

/-- Smooth gauges preserve the regularity of variations, without differentiating a
connection increment. -/
theorem contDiff_gaugeLinearAction {n : WithTop ℕ∞} {u : ℂ → Circle}
    (hu : ContDiff ℝ n (fun z ↦ (u z : ℂ))) {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : ContDiff ℝ n y) : ContDiff ℝ n (gaugeLinearAction u y) := by
  have hr := reCLM.contDiff.comp hu
  have hi := imCLM.contDiff.comp hu
  have hc (i : Fin 4) : ContDiff ℝ n (fun z ↦ y z i) := (contDiff_piLp _).mp hy i
  apply (contDiff_piLp _).mpr
  intro i
  fin_cases i <;> simp only [gaugeLinearAction_apply, PiLp.toLp_apply]
  · exact hc 0
  · exact hc 1
  · exact (hr.mul (hc 2)).sub (hi.mul (hc 3))
  · exact (hi.mul (hc 2)).add (hr.mul (hc 3))

/-- The logarithmic derivative of a product is the sum of the logarithmic derivatives. -/
theorem gaugeForm_mul {u v : ℂ → Circle} {z : ℂ}
    (hu : DifferentiableAt ℝ (fun w ↦ (u w : ℂ)) z)
    (hv : DifferentiableAt ℝ (fun w ↦ (v w : ℂ)) z) :
    gaugeForm (u * v) z = gaugeForm u z + gaugeForm v z := by
  ext a
  have hu1 : conj (u z : ℂ) * (u z : ℂ) = 1 := by
    simp [← Circle.coe_inv_eq_conj]
  have hv1 : conj (v z : ℂ) * (v z : ℂ) = 1 := by
    simp [← Circle.coe_inv_eq_conj]
  simp only [gaugeForm_apply, Pi.mul_apply, Circle.coe_mul, fderiv_fun_mul hu hv,
    add_apply, smul_apply, smul_eq_mul, map_mul]
  have h : conj (u z : ℂ) * conj (v z : ℂ) *
      (fderiv ℝ (fun w ↦ (u w : ℂ)) z a * (v z : ℂ) +
        (u z : ℂ) * fderiv ℝ (fun w ↦ (v w : ℂ)) z a) =
      conj (u z : ℂ) * fderiv ℝ (fun w ↦ (u w : ℂ)) z a +
        conj (v z : ℂ) * fderiv ℝ (fun w ↦ (v w : ℂ)) z a := by
    linear_combination
      (conj (v z : ℂ) * fderiv ℝ (fun w ↦ (v w : ℂ)) z a) * hu1 +
      (conj (u z : ℂ) * fderiv ℝ (fun w ↦ (u w : ℂ)) z a) * hv1
  simpa only [Complex.add_im, mul_comm (v z : ℂ), add_comm] using congrArg Complex.im h

@[simp]
theorem gaugeForm_one (z : ℂ) : gaugeForm 1 z = 0 := by
  ext v
  simp

/-- The logarithmic derivative of the inverse gauge is the negative of the logarithmic
derivative. -/
theorem gaugeForm_inv {u : ℂ → Circle} {z : ℂ}
    (hu : DifferentiableAt ℝ (fun w ↦ (u w : ℂ)) z) :
    gaugeForm u⁻¹ z = -gaugeForm u z := by
  have h := gaugeForm_mul hu (Circle.differentiableAt_coe_inv hu)
  rw [mul_inv_cancel, gaugeForm_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

@[simp]
theorem gaugeTransform_one (x : ℂ → EuclideanSpace ℝ (Fin 4)) : gaugeTransform 1 x = x := by
  ext z i
  fin_cases i <;> simp [gaugeTransform]

/-- Gauge composition is multiplication of the actual circle-valued maps. -/
theorem gaugeTransform_mul {u v : ℂ → Circle}
    (hu : Differentiable ℝ (fun w ↦ (u w : ℂ)))
    (hv : Differentiable ℝ (fun w ↦ (v w : ℂ)))
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    gaugeTransform (u * v) x = gaugeTransform u (gaugeTransform v x) := by
  ext z i
  fin_cases i <;> simp [gaugeTransform, gaugeForm_mul (hu z) (hv z), mul_re, mul_im] <;> ring

/-- Gauge action on differences of fields is its linear action on the difference. -/
theorem gaugeTransform_sub_gaugeTransform (u : ℂ → Circle) (x y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    gaugeTransform u x - gaugeTransform u y = gaugeLinearAction u (x - y) := by
  ext z i
  fin_cases i <;> simp [gaugeTransform_apply, gaugeLinearAction_apply] <;> ring

/-- The affine gauge action transports every increment by its linear part. -/
theorem gaugeTransform_add (u : ℂ → Circle) (x y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    gaugeTransform u (x + y) = gaugeTransform u x + gaugeLinearAction u y := by
  ext z i
  fin_cases i <;> simp [gaugeTransform_apply, gaugeLinearAction_apply] <;> ring

/-- The linear action is the derivative of the actual gauge action in every field direction. -/
theorem hasDerivAt_gaugeTransform_add_smul (u : ℂ → Circle)
    (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    HasDerivAt (fun t : ℝ ↦ gaugeTransform u (x + t • y) z)
      (gaugeLinearAction u y z) 0 := by
  simp_rw [gaugeTransform_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simpa only [id_eq, one_smul] using
    (((hasDerivAt_id (0 : ℝ)).smul_const (gaugeLinearAction u y z)).const_add
      (gaugeTransform u x z))

/-- The smooth framed group acts on fields; the field need not itself be smooth. -/
instance : MulAction framedGaugeGroup (ℂ → EuclideanSpace ℝ (Fin 4)) where
  smul u x := gaugeTransform u.val x
  one_smul := gaugeTransform_one
  mul_smul u v x := gaugeTransform_mul
    (((mem_framedGaugeGroup _).mp u.property).1.differentiable (by simp))
    (((mem_framedGaugeGroup _).mp v.property).1.differentiable (by simp)) x

/-- The bundled action is the charge-one coordinate transformation. -/
@[simp]
theorem framedGaugeGroup_smul (u : framedGaugeGroup) (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    u • x = gaugeTransform u.val x := (rfl)

/-- The differential of a circle-valued map is its imaginary logarithmic derivative times
`i u`. This identity includes all tangent-vector factors. -/
theorem fderiv_coe_eq_mul_gaugeForm {u : ℂ → Circle} {z : ℂ} (v : ℂ) :
    fderiv ℝ (fun w ↦ (u w : ℂ)) z v = (u z : ℂ) * I * gaugeForm u z v := by
  by_cases hu : DifferentiableAt ℝ (fun w ↦ (u w : ℂ)) z
  swap
  · simp [fderiv_zero_of_not_differentiableAt hu]
  have h := congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L v) hu.hasFDerivAt.norm_sq.fderiv
  simp [Circle.norm_coe, Complex.inner, mul_re] at h
  have hn := Circle.re_sq_add_im_sq (u z)
  apply Complex.ext <;> simp [gaugeForm_apply, mul_re, mul_im]
  · linear_combination
      -((fderiv ℝ (fun w ↦ (u w : ℂ)) z) v).re * hn - (u z : ℂ).re / 2 * h
  · linear_combination
      -((fderiv ℝ (fun w ↦ (u w : ℂ)) z) v).im * hn - (u z : ℂ).im / 2 * h

/-- The derivative of the real part of a circle-valued gauge is its imaginary coordinate
multiplied by the negative logarithmic derivative, without choosing a phase. -/
theorem fderiv_re_coe_eq_neg_im_mul_gaugeForm {u : ℂ → Circle} {z : ℂ}
    (hu : DifferentiableAt ℝ (fun w ↦ (u w : ℂ)) z) (v : ℂ) :
    fderiv ℝ (fun w ↦ (u w : ℂ).re) z v = -(u z : ℂ).im * gaugeForm u z v := by
  calc
    _ = (fderiv ℝ (fun w ↦ (u w : ℂ)) z v).re :=
      congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L v)
        (reCLM.hasFDerivAt.comp z hu.hasFDerivAt).fderiv
    _ = _ := by
      rw [fderiv_coe_eq_mul_gaugeForm v]
      simp only [mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
        mul_zero, mul_one, sub_zero, zero_sub, neg_mul]

/-- The derivative of the imaginary part of a circle-valued gauge is its real coordinate
multiplied by the logarithmic derivative, without choosing a phase. -/
theorem fderiv_im_coe_eq_re_mul_gaugeForm {u : ℂ → Circle} {z : ℂ}
    (hu : DifferentiableAt ℝ (fun w ↦ (u w : ℂ)) z) (v : ℂ) :
    fderiv ℝ (fun w ↦ (u w : ℂ).im) z v = (u z : ℂ).re * gaugeForm u z v := by
  calc
    _ = (fderiv ℝ (fun w ↦ (u w : ℂ)) z v).im :=
      congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L v)
        (imCLM.hasFDerivAt.comp z hu.hasFDerivAt).fderiv
    _ = _ := by
      rw [fderiv_coe_eq_mul_gaugeForm v]
      simp only [mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
        mul_zero, mul_one, zero_add, add_zero]

/-- Leibniz rule for the real section coordinate of the linear gauge action. Only the gauge
and the two section coordinates need be differentiable at the point. -/
theorem fderiv_gaugeLinearAction_apply_two {u : ℂ → Circle} {z : ℂ}
    (hu : DifferentiableAt ℝ (fun w ↦ (u w : ℂ)) z)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hp : DifferentiableAt ℝ (fun w ↦ y w 2) z)
    (hq : DifferentiableAt ℝ (fun w ↦ y w 3) z) (v : ℂ) :
    fderiv ℝ (fun w ↦ gaugeLinearAction u y w 2) z v =
      (u z : ℂ).re * fderiv ℝ (fun w ↦ y w 2) z v -
        (u z : ℂ).im * fderiv ℝ (fun w ↦ y w 3) z v -
        gaugeForm u z v * gaugeLinearAction u y z 3 := by
  have hr : DifferentiableAt ℝ (fun w ↦ (u w : ℂ).re) z :=
    reCLM.differentiableAt.comp z hu
  have hi : DifferentiableAt ℝ (fun w ↦ (u w : ℂ).im) z :=
    imCLM.differentiableAt.comp z hu
  simp only [gaugeLinearAction_apply, PiLp.toLp_apply, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [fderiv_fun_sub (hr.fun_mul hp) (hi.fun_mul hq), fderiv_fun_mul hr hp,
    fderiv_fun_mul hi hq]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul,
    fderiv_re_coe_eq_neg_im_mul_gaugeForm hu, fderiv_im_coe_eq_re_mul_gaugeForm hu]
  ring

/-- Leibniz rule for the imaginary section coordinate of the linear gauge action. Only the
gauge and the two section coordinates need be differentiable at the point. -/
theorem fderiv_gaugeLinearAction_apply_three {u : ℂ → Circle} {z : ℂ}
    (hu : DifferentiableAt ℝ (fun w ↦ (u w : ℂ)) z)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hp : DifferentiableAt ℝ (fun w ↦ y w 2) z)
    (hq : DifferentiableAt ℝ (fun w ↦ y w 3) z) (v : ℂ) :
    fderiv ℝ (fun w ↦ gaugeLinearAction u y w 3) z v =
      (u z : ℂ).im * fderiv ℝ (fun w ↦ y w 2) z v +
        (u z : ℂ).re * fderiv ℝ (fun w ↦ y w 3) z v +
        gaugeForm u z v * gaugeLinearAction u y z 2 := by
  have hr : DifferentiableAt ℝ (fun w ↦ (u w : ℂ).re) z :=
    reCLM.differentiableAt.comp z hu
  have hi : DifferentiableAt ℝ (fun w ↦ (u w : ℂ).im) z :=
    imCLM.differentiableAt.comp z hu
  simp only [gaugeLinearAction_apply, PiLp.toLp_apply, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [fderiv_fun_add (hi.fun_mul hp) (hr.fun_mul hq), fderiv_fun_mul hi hp,
    fderiv_fun_mul hr hq]
  simp only [add_apply, smul_apply, smul_eq_mul,
    fderiv_re_coe_eq_neg_im_mul_gaugeForm hu, fderiv_im_coe_eq_re_mul_gaugeForm hu]
  ring

/-- The smooth framed gauge action is free. The connection coordinates suffice; no
nonvanishing, regularity or equation hypothesis on the field is required. -/
instance : IsCancelSMul framedGaugeGroup (ℂ → EuclideanSpace ℝ (Fin 4)) := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro u x hu
  have hup := (mem_framedGaugeGroup _).mp u.property
  have hud : Differentiable ℝ (fun z ↦ (u.val z : ℂ)) :=
    hup.1.differentiable (by simp)
  have hzero (z : ℂ) : fderiv ℝ (fun w ↦ (u.val w : ℂ)) z = 0 := by
    have hg (i : Fin 4) := congrArg (fun v ↦ v z i) hu
    have hg₁ : gaugeForm u.val z 1 = 0 := by
      simpa only [framedGaugeGroup_smul, gaugeTransform_apply, PiLp.toLp_apply,
        Matrix.cons_val_zero, sub_eq_self] using hg 0
    have hgI : gaugeForm u.val z I = 0 := by
      simpa only [framedGaugeGroup_smul, gaugeTransform_apply, PiLp.toLp_apply,
        Matrix.cons_val_one, Matrix.cons_val_zero, sub_eq_self] using hg 1
    have hlin : (gaugeForm u.val z).toLinearMap = 0 := by
      apply Complex.basisOneI.ext
      intro i
      fin_cases i
      · simpa using hg₁
      · simpa using hgI
    have hform : gaugeForm u.val z = 0 := by
      ext v
      exact LinearMap.congr_fun hlin v
    ext v
    simp [fderiv_coe_eq_mul_gaugeForm v, hform]
  have hconst (z : ℂ) : u.val z = u.val 0 := by
    apply Subtype.ext
    exact is_const_of_fderiv_eq_zero hud hzero z 0
  have hend : Tendsto (fun _ : ℂ ↦ u.val 0) (cocompact ℂ) (𝓝 1) :=
    hup.2.congr fun z ↦ hconst z
  have hone : u.val 0 = 1 := tendsto_nhds_unique tendsto_const_nhds hend
  apply Subtype.ext
  funext z
  exact (hconst z).trans hone

/-- The logarithmic derivative of a smooth gauge is smooth as a one-form. -/
theorem contDiff_gaugeForm {u : ℂ → Circle}
    (hu : ContDiff ℝ ∞ (fun w ↦ (u w : ℂ))) : ContDiff ℝ ∞ (gaugeForm u) := by
  exact contDiff_const.clm_comp
    ((ContinuousLinearMap.mul ℝ ℂ).contDiff.comp (conjCLE.contDiff.comp hu) |>.clm_comp
      (hu.fderiv_right (by simp)))

/-- A `C²` gauge has a differentiable logarithmic derivative. -/
theorem differentiableAt_gaugeForm {u : ℂ → Circle} {z : ℂ}
    (hu : ContDiffAt ℝ 2 (fun w ↦ (u w : ℂ)) z) :
    DifferentiableAt ℝ (gaugeForm u) z := by
  have h : ContDiffAt ℝ 1 (gaugeForm u) z :=
    contDiffAt_const.clm_comp
      ((ContinuousLinearMap.mul ℝ ℂ).contDiff.contDiffAt.comp z
        (conjCLE.contDiff.contDiffAt.comp z (hu.of_le (by norm_num))) |>.clm_comp
        (hu.fderiv_right (by norm_num)))
  exact h.differentiableAt one_ne_zero

/-- Smooth gauges preserve smooth fields. -/
theorem contDiff_gaugeTransform {u : ℂ → Circle}
    (hu : ContDiff ℝ ∞ (fun w ↦ (u w : ℂ)))
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x) :
    ContDiff ℝ ∞ (gaugeTransform u x) := by
  have hg := contDiff_gaugeForm hu
  have hr := reCLM.contDiff.comp hu
  have hi := imCLM.contDiff.comp hu
  have hc (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z i) :=
    (contDiff_piLp _).mp hx i
  apply (contDiff_piLp _).mpr
  intro i
  fin_cases i <;> simp only [gaugeTransform, PiLp.toLp_apply]
  · exact (hc 0).sub (hg.clm_apply contDiff_const)
  · exact (hc 1).sub (hg.clm_apply contDiff_const)
  · exact (hr.mul (hc 2)).sub (hi.mul (hc 3))
  · exact (hi.mul (hc 2)).add (hr.mul (hc 3))

/-- The logarithmic derivative of a `C²` circle-valued gauge is closed. -/
theorem fderiv_gaugeForm_symm {u : ℂ → Circle} {z : ℂ}
    (hu : ContDiffAt ℝ 2 (fun w ↦ (u w : ℂ)) z) (a b : ℂ) :
    fderiv ℝ (fun w ↦ gaugeForm u w a) z b =
      fderiv ℝ (fun w ↦ gaugeForm u w b) z a := by
  have hu' := hu.differentiableAt (by norm_num)
  have hd := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hp (v : ℂ) : DifferentiableAt ℝ
      (fun w ↦ fderiv ℝ (fun t ↦ (u t : ℂ)) w v) z :=
    hd.clm_apply (differentiableAt_const _)
  have hpartial (v w : ℂ) :
      fderiv ℝ (fun t ↦ gaugeForm u t v) z w =
        (conj (fderiv ℝ (fun t ↦ (u t : ℂ)) z w) *
            fderiv ℝ (fun t ↦ (u t : ℂ)) z v +
          conj (u z : ℂ) * fderiv ℝ
            (fun t ↦ fderiv ℝ (fun s ↦ (u s : ℂ)) t v) z w).im := by
    have h := imCLM.hasFDerivAt.comp z
      (((conjCLE.hasFDerivAt.comp z hu'.hasFDerivAt).mul (hp v).hasFDerivAt))
    simpa [gaugeForm_apply, Function.comp_def, Pi.mul_apply, mul_comm, add_comm] using
      congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L w) h.fderiv
  have hcomm := (hu.isSymmSndFDerivAt (by norm_num)).eq a b
  have hsecond (v w : ℂ) :
      fderiv ℝ (fun t ↦ fderiv ℝ (fun s ↦ (u s : ℂ)) t v) z w =
        fderiv ℝ (fderiv ℝ (fun s ↦ (u s : ℂ))) z w v := by
    simp [fderiv_clm_apply hd (differentiableAt_const _)]
  rw [hpartial, hpartial, hsecond, hsecond, hcomm]
  have hprod : conj (fderiv ℝ (fun w ↦ (u w : ℂ)) z b) *
      fderiv ℝ (fun w ↦ (u w : ℂ)) z a =
      conj (fderiv ℝ (fun w ↦ (u w : ℂ)) z a) *
        fderiv ℝ (fun w ↦ (u w : ℂ)) z b := by
    rw [fderiv_coe_eq_mul_gaugeForm a, fderiv_coe_eq_mul_gaugeForm b]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hprod]

/-- Off-shell gauge covariance: the curvature defect is unchanged and the complex defect
is multiplied by the same circle element as the section. -/
theorem equation_gaugeTransform {u : ℂ → Circle}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hu : ContDiffAt ℝ 2 (fun w ↦ (u w : ℂ)) z)
    (hx : ∀ i, DifferentiableAt ℝ (fun w ↦ x w i) z) :
    equation (gaugeTransform u x) z =
      !₂[equation x z 0,
        (u z : ℂ).re * equation x z 1 - (u z : ℂ).im * equation x z 2,
        (u z : ℂ).im * equation x z 1 + (u z : ℂ).re * equation x z 2] := by
  have hu' := hu.differentiableAt (by norm_num)
  have hr : DifferentiableAt ℝ (fun w ↦ (u w : ℂ).re) z :=
    reCLM.differentiableAt.comp z hu'
  have hi : DifferentiableAt ℝ (fun w ↦ (u w : ℂ).im) z :=
    imCLM.differentiableAt.comp z hu'
  have hg (v : ℂ) : DifferentiableAt ℝ (fun w ↦ gaugeForm u w v) z :=
    (differentiableAt_gaugeForm hu).clm_apply (differentiableAt_const v)
  have hn := Circle.re_sq_add_im_sq (u z)
  ext i
  fin_cases i <;> simp [gaugeTransform, fderiv_fun_sub, fderiv_fun_add,
    fderiv_fun_mul, hx, hr, hi, hg, fderiv_re_coe_eq_neg_im_mul_gaugeForm hu',
    fderiv_im_coe_eq_re_mul_gaugeForm hu', -gaugeForm_apply]
  · linear_combination (x z 2 ^ 2 + x z 3 ^ 2) / 2 * hn -
      fderiv_gaugeForm_symm hu 1 I
  · ring
  · ring

/-- A gauge transformation preserves the vortex equation in both directions. -/
@[simp]
theorem equation_gaugeTransform_eq_zero_iff {u : ℂ → Circle}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hu : ContDiffAt ℝ 2 (fun w ↦ (u w : ℂ)) z)
    (hx : ∀ i, DifferentiableAt ℝ (fun w ↦ x w i) z) :
    equation (gaugeTransform u x) z = 0 ↔ equation x z = 0 := by
  rw [equation_gaugeTransform hu hx]
  refine ⟨fun h ↦ ?_, fun h ↦ by ext i; fin_cases i <;> simp [h]⟩
  have h₀ := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 0) h
  have h₁ := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 1) h
  have h₂ := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 2) h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, PiLp.zero_apply] at h₀ h₁ h₂
  have hn := Circle.re_sq_add_im_sq (u z)
  ext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  all_goals simp only [PiLp.zero_apply]
  · exact h₀
  · linear_combination (u z : ℂ).re * h₁ + (u z : ℂ).im * h₂ - equation x z 1 * hn
  · linear_combination -(u z : ℂ).im * h₁ + (u z : ℂ).re * h₂ - equation x z 2 * hn

/-- The section transforms by the charge-one representation, not its square. -/
@[simp]
theorem sectionValue_gaugeTransform (u : ℂ → Circle)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    sectionValue (gaugeTransform u x) z = (u z : ℂ) * sectionValue x z := by
  apply Complex.ext <;> simp [sectionValue_apply, gaugeTransform] <;> ring

/-- Covariant derivatives transform by multiplication by the circle-valued gauge. -/
theorem covariantDerivative_gaugeTransform {u : ℂ → Circle} {z : ℂ}
    (hu : DifferentiableAt ℝ (fun w ↦ (u w : ℂ)) z)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z)
    (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z) (v : ℂ) :
    covariantDerivative (gaugeTransform u x) z v =
      (u z : ℂ) * covariantDerivative x z v := by
  have hs := differentiableAt_sectionValue hp hq
  have heq : sectionValue (gaugeTransform u x) =
      fun w ↦ (u w : ℂ) * sectionValue x w := funext (sectionValue_gaugeTransform u x)
  have hg : gaugeForm u z v = v.re * gaugeForm u z 1 + v.im * gaugeForm u z I := by
    calc
      gaugeForm u z v = gaugeForm u z (v.re • (1 : ℂ) + v.im • I) := by
        rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
      _ = _ := by simp only [map_add, map_smul, smul_eq_mul]
  simp only [covariantDerivative_apply, heq, fderiv_fun_mul hu hs, add_apply, smul_apply,
    smul_eq_mul, sectionValue_gaugeTransform, gaugeTransform, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, ofReal_add, ofReal_sub, ofReal_mul,
    fderiv_coe_eq_mul_gaugeForm, hg]
  ring

/-- Curvature is unchanged by `C²` gauge transformations. -/
@[simp]
theorem curvature_gaugeTransform {u : ℂ → Circle}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hu : ContDiffAt ℝ 2 (fun w ↦ (u w : ℂ)) z)
    (hb₀ : DifferentiableAt ℝ (fun w ↦ x w 0) z)
    (hb₁ : DifferentiableAt ℝ (fun w ↦ x w 1) z) :
    curvature (gaugeTransform u x) z = curvature x z := by
  have hg (v : ℂ) : DifferentiableAt ℝ (fun w ↦ gaugeForm u w v) z :=
    (differentiableAt_gaugeForm hu).clm_apply (differentiableAt_const v)
  simp [curvature_apply, gaugeTransform, fderiv_fun_sub, hb₀, hb₁, hg, -gaugeForm_apply]
  linear_combination fderiv_gaugeForm_symm hu 1 I

/-- Gauge invariance of the physical energy density; hence any integral finite-energy
condition is preserved, without decay assumptions on derivatives of the gauge. -/
@[simp]
theorem energyDensity_gaugeTransform {u : ℂ → Circle}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hu : ContDiffAt ℝ 2 (fun w ↦ (u w : ℂ)) z)
    (hx : ∀ i, DifferentiableAt ℝ (fun w ↦ x w i) z) :
    energyDensity (gaugeTransform u x) z = energyDensity x z := by
  simp [energyDensity_apply, curvature_gaugeTransform hu (hx 0) (hx 1),
    covariantDerivative_gaugeTransform (hu.differentiableAt (by norm_num)) (hx 2) (hx 3)]

/-- The end framing `α times an inverse winding phase tends to one` is preserved by framed
gauges. The function `phase` can in particular be `(z / ‖z‖)^(-m)`. -/
theorem tendsto_sectionValue_gaugeTransform {u : ℂ → Circle}
    (hu : Tendsto u (cocompact ℂ) (𝓝 1))
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} {phase : ℂ → ℂ}
    (hx : Tendsto (fun z ↦ sectionValue x z * phase z) (cocompact ℂ) (𝓝 1)) :
    Tendsto (fun z ↦ sectionValue (gaugeTransform u x) z * phase z)
      (cocompact ℂ) (𝓝 1) := by
  have huc : Tendsto (fun z ↦ (u z : ℂ)) (cocompact ℂ) (𝓝 1) := by
    have hc : Continuous (fun w : Circle ↦ (w : ℂ)) := continuous_subtype_val
    simpa only [Function.comp_def, Circle.coe_one] using (hc.tendsto 1).comp hu
  simpa only [sectionValue_gaugeTransform, mul_assoc, one_mul] using huc.mul hx

/-- The phase gauges already used in the deformation complex have logarithmic derivative
`df`, independently of the choice of real lift. -/
theorem gaugeForm_exp {f : ℂ → ℝ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    gaugeForm (fun w ↦ Circle.exp (f w)) z = fderiv ℝ f z := by
  ext v
  have hd := ((ofRealCLM.hasFDerivAt.comp z hf.hasFDerivAt).mul_const I).cexp
  have heq : fderiv ℝ (fun w ↦ ((f w : ℂ) * I).exp) z v =
      ((f z : ℂ) * I).exp * ((fderiv ℝ f z v : ℂ) * I) := by
    simpa [mul_comm I] using congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L v) hd.fderiv
  have hunit : conj ((f z : ℂ) * I).exp * ((f z : ℂ) * I).exp = 1 := by
    rw [← Circle.coe_exp, ← Circle.coe_inv_eq_conj]
    simp
  simp only [gaugeForm_apply, Circle.coe_exp, heq, ← mul_assoc, hunit, one_mul,
    mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_one, zero_mul, add_zero]

/-- The phase-coordinate action agrees with the action of its actual circle-valued gauge. -/
theorem gaugeTransform_exp {f : ℂ → ℝ} (hf : Differentiable ℝ f)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    gaugeTransform (fun w ↦ Circle.exp (f w)) x = phaseGauge x f := by
  ext z i
  fin_cases i <;> simp [gaugeTransform, gaugeForm_exp (hf z), Circle.coe_exp,
    Complex.exp_ofReal_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- A smooth phase tending to zero gives a framed gauge. This is a sufficient end condition,
not a definition of the framed group in terms of a chosen logarithm. -/
theorem exp_mem_framedGaugeGroup {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (ht : Tendsto f (cocompact ℂ) (𝓝 0)) :
    (fun w ↦ Circle.exp (f w)) ∈ framedGaugeGroup := by
  refine (mem_framedGaugeGroup _).mpr ⟨?_, ?_⟩
  · simpa only [Circle.coe_exp, Function.comp_def, Complex.ofRealCLM_apply] using
      ((ofRealCLM.contDiff.comp hf).mul (contDiff_const (c := I))).cexp
  · simpa only [Circle.exp_zero, Function.comp_def] using (Circle.exp.continuous.tendsto 0).comp ht

open Metric in
/-- **A framed gauge making a function positive near infinity.** If `g : ℂ → ℂ` is smooth outside
a compact set and tends to one at infinity, then some smooth framed gauge `u` satisfies
`u g = |g|` outside a compact set. -/
theorem exists_framedGaugeGroup_mul_eq_norm {g : ℂ → ℂ}
    (hg : ∀ᶠ z in cocompact ℂ, ContDiffAt ℝ ∞ g z) (hgt : Tendsto g (cocompact ℂ) (𝓝 1)) :
    ∃ u : framedGaugeGroup, ∀ᶠ z in cocompact ℂ, ((u : ℂ → Circle) z : ℂ) * g z = ‖g z‖ := by
  obtain ⟨R₀, -, hR₀⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸
      hg.and (hgt.eventually (Metric.ball_mem_nhds 1 one_half_pos)))
  set R := max R₀ 0
  have hgR {z : ℂ} (hz : R < ‖z‖) : ContDiffAt ℝ ∞ g z ∧ 1 / 2 < (g z).re := by
    obtain ⟨hc, h⟩ := hR₀ (show R₀ ≤ ‖z‖ from (le_max_left _ _).trans hz.le)
    rw [dist_eq_norm] at h
    have := abs_re_le_norm (g z - 1)
    rw [sub_re, one_re] at this
    exact ⟨hc, by linarith [abs_lt.1 (this.trans_lt h)]⟩
  -- A cutoff `χ` vanishing on the disc of radius `R + 1` and equal to one outside radius `R + 2`.
  let b : ContDiffBump (0 : ℂ) := ⟨R + 1, R + 2, by positivity, by linarith⟩
  set χ : ℂ → ℝ := fun z ↦ 1 - b z
  have hχ0 {z : ℂ} (hz : ‖z‖ ≤ R + 1) : χ z = 0 := by
    simp only [χ, b.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hz), sub_self]
  have hχ1 {z : ℂ} (hz : R + 2 ≤ ‖z‖) : χ z = 1 := by
    simp only [χ, b.zero_of_le_dist (by rwa [dist_zero_right]), sub_zero]
  -- The unnormalized gauge `v = 1 + χ (conj g - 1)` is smooth with positive real part.
  set v : ℂ → ℂ := fun z ↦ 1 + (χ z : ℂ) * (conj (g z) - 1)
  have hv_re (z : ℂ) : 0 < (v z).re := by
    simp only [v, add_re, one_re, re_ofReal_mul, sub_re, conj_re]
    rcases le_or_gt ‖z‖ R with hz | hz
    · rw [hχ0 (by linarith)]
      norm_num
    · nlinarith [(hgR hz).2, sub_nonneg.2 (b.le_one (x := z)), b.nonneg (x := z)]
  have hv0 (z : ℂ) : v z ≠ 0 := fun h ↦ by simpa [h] using hv_re z
  have hv : ContDiff ℝ ∞ v := by
    refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
    rcases lt_or_ge R ‖z‖ with hz | hz
    · exact contDiffAt_const.add ((ofRealCLM.contDiff.comp
        (contDiff_const.sub b.contDiff)).contDiffAt.mul
        ((conjCLE.contDiff.contDiffAt.comp z (hgR hz).1).sub contDiffAt_const))
    · refine (contDiffAt_const (c := (1 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds
        (show ‖z‖ < R + 1 by linarith)] with w hw
      simp [v, hχ0 (le_of_lt hw)]
  -- The gauge `u = v / |v|`, written as `exp (i arg v)` to avoid a membership proof.
  set u : ℂ → Circle := fun z ↦ Circle.exp (arg (v z))
  have hu (z : ℂ) : (u z : ℂ) = v z / (‖v z‖ : ℂ) := by
    simp only [u, Circle.coe_exp, exp_arg_mul_I (hv0 z)]
  have hvt : Tendsto v (cocompact ℂ) (𝓝 1) := by
    have h := ((continuous_conj.tendsto 1).comp hgt)
    rw [map_one] at h
    refine h.congr' ?_
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (R + 2)] with z hz
    simp [v, hχ1 hz]
  have hmem : u ∈ framedGaugeGroup :=
    exp_mem_framedGaugeGroup (contDiff_iff_contDiffAt.2 fun z ↦
        (contDiffAt_arg (mem_slitPlane_iff.2 (Or.inl (hv_re z)))).comp z hv.contDiffAt)
      (by simpa [arg_one, Function.comp_def] using ((continuousAt_arg (by simp)).tendsto).comp hvt)
  refine ⟨⟨u, hmem⟩, ?_⟩
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (R + 2)] with z hz
  have hvz : v z = conj (g z) := by simp [v, hχ1 hz]
  have hgz : g z ≠ 0 := fun h ↦ by
    have := (hgR (show R < ‖z‖ by linarith)).2
    simp [h] at this
    linarith
  rw [hu z, hvz, Complex.norm_conj, div_mul_eq_mul_div, conj_mul',
    div_eq_iff (ofReal_ne_zero.2 (norm_ne_zero_iff.2 hgz))]
  ring

/-- **The framed gauge action is free at a field with nowhere dense zeros.** If the section of
`y` is nonzero on a dense set, then a smooth framed gauge is determined by its action on `y`. -/
theorem framedGaugeGroup_smul_left_injective {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hdense : Dense {z | sectionValue y z ≠ 0}) :
    Function.Injective fun u : framedGaugeGroup ↦ u • y := by
  intro u v huv
  have hc (u : framedGaugeGroup) : Continuous fun z ↦ ((u.val z : Circle) : ℂ) :=
    ((mem_framedGaugeGroup _).mp u.property).1.continuous
  refine Subtype.ext (funext fun z ↦ Circle.ext ?_)
  refine congrFun ((hc u).ext_on hdense (hc v) fun w hw ↦ ?_) z
  have hw' := congrArg (fun x ↦ sectionValue x w) huv
  simp only [framedGaugeGroup_smul, sectionValue_gaugeTransform] at hw'
  exact mul_right_cancel₀ hw hw'

end TauCeti.Vortex
