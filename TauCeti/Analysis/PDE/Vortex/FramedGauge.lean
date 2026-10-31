/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import TauCeti.Analysis.PDE.Vortex.Deformation
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Smooth framed gauge transformations of plane vortex fields

The smooth framed gauge group consists of all smooth circle-valued maps on the plane tending
to one at infinity. There is no condition at a finite base point. Its charge-one action is
`(a, α) ↦ (a - u⁻¹ du, u α)`, in the real coordinates of `Vortex.equation`.

The action preserves the equation, the physical energy density and the end phase framing.
It agrees with the existing real-phase action. The logarithmic derivative is expressed without
choosing a real phase. This permits gauges whose phase tends to zero too slowly to lie in an
unweighted Sobolev space. The smooth group here is not a Banach completion.

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
theorem fderiv_coe_eq_mul_gaugeForm {u : ℂ → Circle} {z : ℂ}
    (hu : DifferentiableAt ℝ (fun w ↦ (u w : ℂ)) z) (v : ℂ) :
    fderiv ℝ (fun w ↦ (u w : ℂ)) z v = (u z : ℂ) * I * gaugeForm u z v := by
  have h := congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L v) hu.hasFDerivAt.norm_sq.fderiv
  simp [Circle.norm_coe, Complex.inner, mul_re] at h
  have hn := Circle.normSq_coe (u z)
  simp only [Complex.normSq_apply] at hn
  apply Complex.ext <;> simp [gaugeForm_apply, mul_re, mul_im]
  · linear_combination
      -((fderiv ℝ (fun w ↦ (u w : ℂ)) z) v).re * hn - (u z : ℂ).re / 2 * h
  · linear_combination
      -((fderiv ℝ (fun w ↦ (u w : ℂ)) z) v).im * hn - (u z : ℂ).im / 2 * h

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
    rw [fderiv_coe_eq_mul_gaugeForm hu' a, fderiv_coe_eq_mul_gaugeForm hu' b]
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
  have hgr (v : ℂ) : fderiv ℝ (fun w ↦ (u w : ℂ).re) z v =
      -(u z : ℂ).im * gaugeForm u z v := by
    have heq : fderiv ℝ (fun w ↦ (u w : ℂ).re) z =
        reCLM ∘L fderiv ℝ (fun w ↦ (u w : ℂ)) z := by
      simpa only [Function.comp_def, Complex.reCLM_apply] using
        (reCLM.hasFDerivAt.comp z hu'.hasFDerivAt).fderiv
    rw [heq]
    simpa using congrArg Complex.re (fderiv_coe_eq_mul_gaugeForm hu' v)
  have hgi (v : ℂ) : fderiv ℝ (fun w ↦ (u w : ℂ).im) z v =
      (u z : ℂ).re * gaugeForm u z v := by
    have heq : fderiv ℝ (fun w ↦ (u w : ℂ).im) z =
        imCLM ∘L fderiv ℝ (fun w ↦ (u w : ℂ)) z := by
      simpa only [Function.comp_def, Complex.imCLM_apply] using
        (imCLM.hasFDerivAt.comp z hu'.hasFDerivAt).fderiv
    rw [heq]
    simpa using congrArg Complex.im (fderiv_coe_eq_mul_gaugeForm hu' v)
  have hn := Circle.normSq_coe (u z)
  simp only [Complex.normSq_apply] at hn
  ext i
  fin_cases i <;> simp [gaugeTransform, fderiv_fun_sub, fderiv_fun_add,
    fderiv_fun_mul, hx, hr, hi, hg, hgr, hgi, -gaugeForm_apply]
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
  have hn := Circle.normSq_coe (u z)
  simp only [Complex.normSq_apply] at hn
  ext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  all_goals simp only [PiLp.zero_apply]
  · exact h₀
  · linear_combination (u z : ℂ).re * h₁ + (u z : ℂ).im * h₂ - equation x z 1 * hn
  · linear_combination -(u z : ℂ).im * h₁ + (u z : ℂ).re * h₂ - equation x z 2 * hn

/-- The actual section `α = 2(p + i q)` represented by a real vortex field. -/
def sectionValue (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : ℂ :=
  2 * ((x z 2 : ℂ) + (x z 3 : ℂ) * I)

/-- The section in the real field coordinates. -/
theorem sectionValue_apply (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    sectionValue x z = 2 * ((x z 2 : ℂ) + (x z 3 : ℂ) * I) := (rfl)

/-- The section transforms by the charge-one representation, not its square. -/
@[simp]
theorem sectionValue_gaugeTransform (u : ℂ → Circle)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    sectionValue (gaugeTransform u x) z = (u z : ℂ) * sectionValue x z := by
  apply Complex.ext <;> simp [sectionValue, gaugeTransform] <;> ring

/-- The covariant derivative `d_a α`, with the charge-one connection `a = i(b₁ ds + b₂ dt)`.
The argument `v` is an actual real tangent vector to the plane. -/
def covariantDerivative (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z v : ℂ) : ℂ :=
  fderiv ℝ (sectionValue x) z v +
    I * ((x z 0 * v.re + x z 1 * v.im : ℝ) : ℂ) * sectionValue x z

/-- Coordinate evaluation of the covariant derivative of the actual section. -/
theorem covariantDerivative_apply (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z v : ℂ) :
    covariantDerivative x z v = fderiv ℝ (sectionValue x) z v +
      I * ((x z 0 * v.re + x z 1 * v.im : ℝ) : ℂ) * sectionValue x z := (rfl)

/-- Covariant derivatives transform by multiplication by the circle-valued gauge. -/
theorem covariantDerivative_gaugeTransform {u : ℂ → Circle} {z : ℂ}
    (hu : DifferentiableAt ℝ (fun w ↦ (u w : ℂ)) z)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z)
    (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z) (v : ℂ) :
    covariantDerivative (gaugeTransform u x) z v =
      (u z : ℂ) * covariantDerivative x z v := by
  have hs : DifferentiableAt ℝ (sectionValue x) z := by
    exact (differentiableAt_const (2 : ℂ)).mul
      ((ofRealCLM.differentiableAt.comp z hp).add
        ((ofRealCLM.differentiableAt.comp z hq).mul_const I))
  have heq : sectionValue (gaugeTransform u x) =
      fun w ↦ (u w : ℂ) * sectionValue x w := funext (sectionValue_gaugeTransform u x)
  have hg : gaugeForm u z v = v.re * gaugeForm u z 1 + v.im * gaugeForm u z I := by
    calc
      gaugeForm u z v = gaugeForm u z (v.re • (1 : ℂ) + v.im • I) := by
        rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
      _ = _ := by simp only [map_add, map_smul, smul_eq_mul]
  simp only [covariantDerivative, heq, fderiv_fun_mul hu hs, add_apply, smul_apply,
    smul_eq_mul, sectionValue_gaugeTransform, gaugeTransform, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, ofReal_add, ofReal_sub, ofReal_mul,
    fderiv_coe_eq_mul_gaugeForm hu, hg]
  ring

/-- The real curvature coefficient: `F_a = i curvature ds ∧ dt`. -/
def curvature (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : ℝ :=
  fderiv ℝ (fun w ↦ x w 1) z 1 - fderiv ℝ (fun w ↦ x w 0) z I

/-- The curvature coefficient in the oriented coordinate frame `(1, i)`. -/
theorem curvature_apply (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    curvature x z = fderiv ℝ (fun w ↦ x w 1) z 1 -
      fderiv ℝ (fun w ↦ x w 0) z I := (rfl)

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
  simp [curvature, gaugeTransform, fderiv_fun_sub, hb₀, hb₁, hg, -gaugeForm_apply]
  linear_combination fderiv_gaugeForm_symm hu 1 I

/-- The physical energy density `|F_a|² + |d_a α|² + (1 - |α|²)²` in the Euclidean plane.
No finite-energy condition is built into a field's type. -/
def energyDensity (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : ℝ :=
  curvature x z ^ 2 + ‖covariantDerivative x z 1‖ ^ 2 +
    ‖covariantDerivative x z I‖ ^ 2 + (1 - ‖sectionValue x z‖ ^ 2) ^ 2

/-- The physical energy density as a sum of curvature, kinetic and potential terms. -/
theorem energyDensity_apply (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    energyDensity x z = curvature x z ^ 2 + ‖covariantDerivative x z 1‖ ^ 2 +
      ‖covariantDerivative x z I‖ ^ 2 + (1 - ‖sectionValue x z‖ ^ 2) ^ 2 := (rfl)

/-- Gauge invariance of the physical energy density; hence any integral finite-energy
condition is preserved, without decay assumptions on derivatives of the gauge. -/
@[simp]
theorem energyDensity_gaugeTransform {u : ℂ → Circle}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hu : ContDiffAt ℝ 2 (fun w ↦ (u w : ℂ)) z)
    (hx : ∀ i, DifferentiableAt ℝ (fun w ↦ x w i) z) :
    energyDensity (gaugeTransform u x) z = energyDensity x z := by
  simp [energyDensity, curvature_gaugeTransform hu (hx 0) (hx 1),
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

end TauCeti.Vortex
