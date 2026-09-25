/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pick.Basic

/-!
# Boundary Cayley coordinates and Nevanlinna measure transport

The boundary Cayley map

`x ↦ (x - i) / (x + i)`

identifies the real line with the unit circle punctured at `1`.  This is the boundary counterpart
of the Cayley coordinate from the upper half-plane to the unit disc.  A finite measure on the
circle consequently splits into its atom at `1`, which produces the linear term in a Nevanlinna
representation, and a finite measure on the real line.

This file gives the explicit boundary homeomorphism and packages the measure transport.  The
integral decomposition is stated for arbitrary continuous functions on the circle, so it can be
applied directly to the Herglotz kernel.  Under the boundary coordinate that kernel becomes the
Nevanlinna kernel `(1 + x * z) / (x - z)`.

## Main declarations

* `TauCeti.boundaryCayleyHomeomorph`: the homeomorphism from `ℝ` to `Circle \ {1}`.
* `MeasureTheory.Measure.cayleyPushforward`: the finite real-line measure obtained from the
  non-atomic-at-`1` part of a circle measure.
* `TauCeti.integral_circle_eq_atom_add_integral_cayleyPushforward`: decomposition of an integral
  over the circle into its atom at `1` and its real-line part.
* `TauCeti.nevanlinnaKernel_im`, `TauCeti.norm_nevanlinnaKernel_le` and
  `TauCeti.integrable_nevanlinnaKernel`: the imaginary part of the kernel, its boundedness on the
  real line, and the resulting integrability against a finite measure.
* `TauCeti.I_mul_herglotzTransform_cayley_eq`: the resulting Nevanlinna-kernel formula for the
  Cayley-coordinate Herglotz transform.
* `TauCeti.nevanlinnaKernel_ofReal`: the kernel is real at a real parameter.
* `TauCeti.exists_isFiniteMeasure_eq_nevanlinnaKernel_add`: the Nevanlinna representation of a
  Pick function by a nonnegative linear coefficient and a finite real-line measure.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*,
  2nd ed., Chapter 6.
-/

public section

noncomputable section

open Complex MeasureTheory Metric Set

namespace TauCeti

/-- The boundary Cayley map from the real line to the unit circle, sending
`x` to `(x - i) / (x + i)`. -/
def boundaryCayley (x : ℝ) : Circle :=
  ⟨((x : ℂ) - I) / ((x : ℂ) + I), by
    refine mem_sphere_zero_iff_norm.2 ?_
    rw [norm_div]
    have hnorm : ‖(x : ℂ) - I‖ = ‖(x : ℂ) + I‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq,
        ← normSq_eq_norm_sq]
      simp [normSq_apply]
    rw [hnorm]
    apply div_self
    rw [norm_ne_zero_iff]
    intro h
    have := congrArg im h
    norm_num at this⟩

/-- The boundary Cayley map as a complex-valued formula. -/
@[simp]
theorem coe_boundaryCayley (x : ℝ) :
    (boundaryCayley x : ℂ) = ((x : ℂ) - I) / ((x : ℂ) + I) :=
  by rw [boundaryCayley]

/-- The boundary Cayley map never takes the omitted value `1`. -/
theorem boundaryCayley_ne_one (x : ℝ) : boundaryCayley x ≠ 1 := by
  intro h
  have h' := congrArg ((↑) : Circle → ℂ) h
  simp only [coe_boundaryCayley, Circle.coe_one] at h'
  have hden : (x : ℂ) + I ≠ 0 := by
    intro hzero
    have := congrArg im hzero
    simp at this
  rw [div_eq_one_iff_eq hden] at h'
  have := congrArg im h'
  norm_num at this

/-- The real coordinate of a point of the circle.  At the omitted point `1` the denominator is
zero and Lean's totalized division assigns the harmless value `0`; the measure transport below
first restricts away from that point. -/
def circleCayleyInv (z : Circle) : ℝ :=
  -(z : ℂ).im / (1 - (z : ℂ).re)

/-- Applying the real boundary coordinate after the boundary Cayley map gives the original real
number. -/
@[simp]
theorem circleCayleyInv_boundaryCayley (x : ℝ) :
    circleCayleyInv (boundaryCayley x) = x := by
  have hden : x ^ 2 + 1 ≠ 0 := by positivity
  simp only [circleCayleyInv, coe_boundaryCayley, div_re, div_im, sub_re, sub_im,
    ofReal_re, ofReal_im, I_re, I_im, add_re, add_im, normSq_apply]
  field_simp
  ring

/-- The real part of a boundary Cayley point. -/
@[simp]
theorem boundaryCayley_re (x : ℝ) :
    (((x : ℂ) - I) / ((x : ℂ) + I)).re = (x ^ 2 - 1) / (x ^ 2 + 1) := by
  rw [div_re]
  simp only [sub_re, sub_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
    normSq_apply]
  ring

/-- The imaginary part of a boundary Cayley point. -/
@[simp]
theorem boundaryCayley_im (x : ℝ) :
    (((x : ℂ) - I) / ((x : ℂ) + I)).im = -(2 * x) / (x ^ 2 + 1) := by
  rw [div_im]
  simp only [sub_re, sub_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
    normSq_apply]
  ring

private theorem one_sub_re_ne_zero_of_ne_one {z : Circle} (hz : z ≠ 1) :
    1 - (z : ℂ).re ≠ 0 := by
  intro h
  have hre : (z : ℂ).re = 1 := by linarith
  have him : (z : ℂ).im = 0 := by
    have hs := Circle.normSq_coe z
    rw [normSq_apply, hre] at hs
    nlinarith [sq_nonneg (z : ℂ).im]
  apply hz
  apply Circle.ext
  apply Complex.ext <;> simp [hre, him]

/-- A non-`1` point of the circle is recovered from its real boundary coordinate. -/
theorem boundaryCayley_circleCayleyInv {z : Circle} (hz : z ≠ 1) :
    boundaryCayley (circleCayleyInv z) = z := by
  apply Circle.ext
  have hden := one_sub_re_ne_zero_of_ne_one hz
  have hcircle := Circle.normSq_coe z
  rw [normSq_apply] at hcircle
  have hquad : (z : ℂ).im ^ 2 + (1 - (z : ℂ).re) ^ 2 =
      2 * (1 - (z : ℂ).re) := by
    nlinarith [hcircle]
  have hquadpos : 0 < (z : ℂ).im ^ 2 + (1 - (z : ℂ).re) ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hden)
  apply Complex.ext
  · rw [coe_boundaryCayley, boundaryCayley_re]
    simp only [circleCayleyInv]
    have hdenom : 0 < (-(z : ℂ).im / (1 - (z : ℂ).re)) ^ 2 + 1 := by positivity
    rw [div_eq_iff hdenom.ne']
    field_simp [hden, hquadpos.ne']
    nlinarith [hquad]
  · rw [coe_boundaryCayley, boundaryCayley_im]
    simp only [circleCayleyInv]
    have hdenom : 0 < (-(z : ℂ).im / (1 - (z : ℂ).re)) ^ 2 + 1 := by positivity
    rw [div_eq_iff hdenom.ne']
    field_simp [hden, hquadpos.ne']
    rw [hquad]
    ring

/-- The boundary Cayley map is continuous. -/
@[fun_prop]
theorem continuous_boundaryCayley : Continuous boundaryCayley := by
  exact continuous_induced_rng.mpr <| Continuous.div (by fun_prop) (by fun_prop) fun x h ↦ by
      have := congrArg im h
      norm_num at this

/-- The inverse boundary coordinate is measurable on the whole circle. -/
@[fun_prop]
theorem measurable_circleCayleyInv : Measurable circleCayleyInv := by
  unfold circleCayleyInv
  fun_prop

/-- The inverse boundary coordinate is continuous away from the omitted point `1`. -/
theorem continuous_circleCayleyInv_restrict :
    Continuous fun z : {z : Circle // z ≠ 1} ↦ circleCayleyInv z := by
  unfold circleCayleyInv
  exact Continuous.div₀ (by fun_prop) (by fun_prop) fun z ↦
    one_sub_re_ne_zero_of_ne_one z.2

/-- The boundary Cayley homeomorphism from the real line onto the circle punctured at `1`. -/
def boundaryCayleyHomeomorph : ℝ ≃ₜ {z : Circle // z ≠ 1} where
  toFun x := ⟨boundaryCayley x, boundaryCayley_ne_one x⟩
  invFun z := circleCayleyInv z
  left_inv := circleCayleyInv_boundaryCayley
  right_inv z := Subtype.ext (boundaryCayley_circleCayleyInv z.2)
  continuous_toFun := continuous_boundaryCayley.subtype_mk _
  continuous_invFun := continuous_circleCayleyInv_restrict

@[simp]
theorem boundaryCayleyHomeomorph_apply (x : ℝ) :
    (boundaryCayleyHomeomorph x : Circle) = boundaryCayley x :=
  by simp [boundaryCayleyHomeomorph]

@[simp]
theorem boundaryCayleyHomeomorph_symm_apply (z : {z : Circle // z ≠ 1}) :
    boundaryCayleyHomeomorph.symm z = circleCayleyInv z :=
  by simp [boundaryCayleyHomeomorph]

/-- The real-line measure obtained by deleting the atom at `1` from a circle measure and pushing
the remainder forward through the inverse boundary Cayley coordinate. -/
def _root_.MeasureTheory.Measure.cayleyPushforward (mu : Measure Circle) : Measure ℝ :=
  (mu.restrict ({1}ᶜ : Set Circle)).map circleCayleyInv

/-- The Cayley pushforward of a finite circle measure is finite. -/
instance _root_.MeasureTheory.Measure.isFiniteMeasure_cayleyPushforward
    (mu : Measure Circle) [IsFiniteMeasure mu] :
    IsFiniteMeasure mu.cayleyPushforward := by
  unfold Measure.cayleyPushforward
  infer_instance

/-- Integration against a finite circle measure splits into the contribution of its atom at `1`
and integration against its real-line Cayley pushforward. -/
theorem integral_circle_eq_atom_add_integral_cayleyPushforward {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (mu : Measure Circle)
    [IsFiniteMeasure mu] (f : Circle → E) (hf : Continuous f) :
    ∫ z, f z ∂mu = mu.real {1} • f 1 + ∫ x, f (boundaryCayley x) ∂mu.cayleyPushforward := by
  have hfi : Integrable f mu :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hsingle : Integrable f (mu.restrict ({1} : Set Circle)) := hfi.restrict
  have hcompl : Integrable f (mu.restrict ({1}ᶜ : Set Circle)) := hfi.restrict
  calc
    ∫ z, f z ∂mu = ∫ z, f z ∂(mu.restrict {1} + mu.restrict ({1}ᶜ : Set Circle)) := by
      rw [Measure.restrict_add_restrict_compl (measurableSet_singleton 1)]
    _ = ∫ z, f z ∂mu.restrict {1} + ∫ z, f z ∂mu.restrict ({1}ᶜ : Set Circle) :=
      integral_add_measure hsingle hcompl
    _ = mu.real {1} • f 1 + ∫ z, f z ∂mu.restrict ({1}ᶜ : Set Circle) := by
      rw [integral_singleton]
    _ = mu.real {1} • f 1 + ∫ x, f (boundaryCayley x) ∂mu.cayleyPushforward := by
      congr 1
      unfold Measure.cayleyPushforward
      -- Expose the composition expected by `integral_map`; the two integrands are definitionally
      -- equal, but its rewrite lemma matches the composition form.
      change ∫ z, f z ∂mu.restrict ({1}ᶜ : Set Circle) =
        ∫ x, (f ∘ boundaryCayley) x ∂Measure.map circleCayleyInv
          (mu.restrict ({1}ᶜ : Set Circle))
      rw [integral_map measurable_circleCayleyInv.aemeasurable
        (hf.comp continuous_boundaryCayley).aestronglyMeasurable]
      refine integral_congr_ae ((ae_restrict_mem (measurableSet_singleton 1).compl).mono ?_)
      intro z hz
      exact congrArg f (boundaryCayley_circleCayleyInv (by simpa using hz)).symm

/-- The Nevanlinna kernel on the upper half-plane. -/
def nevanlinnaKernel (z : ℂ) (x : ℝ) : ℂ :=
  (1 + (x : ℂ) * z) / ((x : ℂ) - z)

/-- The Nevanlinna kernel is the quotient `(1 + x z) / (x - z)`. -/
theorem nevanlinnaKernel_def (z : ℂ) (x : ℝ) :
    nevanlinnaKernel z x = (1 + (x : ℂ) * z) / ((x : ℂ) - z) := by
  rw [nevanlinnaKernel]

/-- The Nevanlinna kernel is measurable in its real variable at every complex parameter. -/
@[fun_prop]
theorem measurable_nevanlinnaKernel (z : ℂ) : Measurable (nevanlinnaKernel z) := by
  unfold nevanlinnaKernel
  exact (measurable_const.add (Complex.measurable_ofReal.mul_const z)).div
    (Complex.measurable_ofReal.sub measurable_const)

/-- Away from its pole, the Nevanlinna kernel separates into its affine part and a resolvent. -/
theorem nevanlinnaKernel_eq_add_div {z : ℂ} {x : ℝ} (h : (x : ℂ) - z ≠ 0) :
    nevanlinnaKernel z x = z + (1 + z ^ 2) / ((x : ℂ) - z) := by
  rw [nevanlinnaKernel]
  field_simp
  ring

/-- The Nevanlinna kernel is continuous in its complex parameter away from its pole. -/
theorem continuousAt_nevanlinnaKernel_left {x : ℝ} {z : ℂ} (h : (x : ℂ) ≠ z) :
    ContinuousAt (fun w => nevanlinnaKernel w x) z := by
  unfold nevanlinnaKernel
  exact (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).div
    (continuousAt_const.sub continuousAt_id) (sub_ne_zero.mpr h)

/-- On the nonpositive real axis, the Nevanlinna kernel is bounded at every parameter with
positive real part. -/
theorem norm_nevanlinnaKernel_le_of_nonpos {z : ℂ} {x : ℝ}
    (hz : 0 < z.re) (hx : x ≤ 0) :
    ‖nevanlinnaKernel z x‖ ≤ ‖z‖ + (1 + ‖z‖ ^ 2) / z.re := by
  have hden : z.re ≤ ‖(x : ℂ) - z‖ := by
    have hre : |x - z.re| ≤ ‖(x : ℂ) - z‖ := by
      simpa only [sub_re, ofReal_re] using abs_re_le_norm ((x : ℂ) - z)
    have hneg : x - z.re < 0 := by linarith
    rw [abs_of_neg hneg] at hre
    linarith
  have hden0 : (x : ℂ) - z ≠ 0 := by
    rw [← norm_pos_iff]
    exact lt_of_lt_of_le hz hden
  have hinv : ‖((x : ℂ) - z)⁻¹‖ ≤ (z.re)⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ hz hden
  rw [nevanlinnaKernel_eq_add_div hden0, div_eq_mul_inv]
  calc
    ‖z + (1 + z ^ 2) * ((x : ℂ) - z)⁻¹‖
        ≤ ‖z‖ + ‖(1 + z ^ 2) * ((x : ℂ) - z)⁻¹‖ := norm_add_le _ _
    _ = ‖z‖ + ‖1 + z ^ 2‖ * ‖((x : ℂ) - z)⁻¹‖ := by rw [norm_mul]
    _ ≤ ‖z‖ + (1 + ‖z‖ ^ 2) / z.re := by
      have hone : ‖1 + z ^ 2‖ ≤ 1 + ‖z‖ ^ 2 := by
        calc
          ‖1 + z ^ 2‖ ≤ 1 + ‖z ^ 2‖ := by
            simpa only [norm_one] using norm_add_le (1 : ℂ) (z ^ 2)
          _ = _ := by rw [norm_pow]
      rw [div_eq_mul_inv]
      gcongr

/-- At a real parameter the Nevanlinna kernel is real. -/
@[simp]
theorem nevanlinnaKernel_ofReal (t x : ℝ) :
    nevanlinnaKernel (t : ℂ) x = (((1 + x * t) / (x - t) : ℝ) : ℂ) := by
  rw [nevanlinnaKernel]
  push_cast
  ring

/-- In boundary Cayley coordinates, the Herglotz kernel becomes the Nevanlinna kernel. -/
theorem I_mul_herglotzKernel_cayley (z : ℂ) (x : ℝ)
    (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    I * (((boundaryCayley x : ℂ) + (z - I) / (z + I)) /
      ((boundaryCayley x : ℂ) - (z - I) / (z + I))) = nevanlinnaKernel z x := by
  have hxi : (x : ℂ) + I ≠ 0 := by
    intro h
    have := congrArg im h
    simp at this
  have hzi : z + I ≠ 0 := by
    have hzpos : 0 < z.im := hz
    intro h
    have := congrArg im h
    simp only [add_im, I_im, zero_im] at this
    linarith
  have hxz : (x : ℂ) - z ≠ 0 := by
    have hzpos : 0 < z.im := hz
    intro h
    have := congrArg im h
    simp only [sub_im, ofReal_im, zero_sub, zero_im] at this
    linarith
  have hdiff : ((x : ℂ) - I) / ((x : ℂ) + I) - (z - I) / (z + I) ≠ 0 := by
    rw [div_sub_div _ _ hxi hzi]
    apply div_ne_zero
    · have heq : ((x : ℂ) - I) * (z + I) - ((x : ℂ) + I) * (z - I) =
          2 * I * ((x : ℂ) - z) := by ring
      rw [heq]
      exact mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hxz
    · exact mul_ne_zero hxi hzi
  simp only [coe_boundaryCayley, nevanlinnaKernel]
  field_simp [hxi, hzi, hxz, hdiff]
  have hsum : ((x : ℂ) - I) * (z + I) + ((x : ℂ) + I) * (z - I) =
      2 * ((x : ℂ) * z + 1) := by
    calc
      _ = 2 * (x : ℂ) * z - 2 * (I * I) := by ring
      _ = _ := by rw [I_mul_I]; ring
  have hsub : ((x : ℂ) - I) * (z + I) - ((x : ℂ) + I) * (z - I) =
      2 * I * ((x : ℂ) - z) := by ring
  rw [hsum, hsub]
  field_simp [hxz, I_ne_zero]
  ring

/-- The imaginary part of the Nevanlinna kernel.  On the upper half-plane it is positive, and the
weight `1 + x ^ 2` appearing in the numerator is what turns a Nevanlinna measure into the measure
of the Stieltjes--Perron inversion formula. -/
@[simp]
theorem nevanlinnaKernel_im (z : ℂ) (x : ℝ) :
    (nevanlinnaKernel z x).im = z.im * (1 + x ^ 2) / normSq ((x : ℂ) - z) := by
  simp only [nevanlinnaKernel, div_im, normSq_apply, add_re, add_im, one_re, one_im, mul_re,
    mul_im, ofReal_re, ofReal_im, sub_re, sub_im]
  ring

/-- The Nevanlinna kernel at a point of the upper half-plane is bounded on the real line, by a
bound depending only on the distance of the point from the boundary in Cayley coordinates. -/
theorem norm_nevanlinnaKernel_le {z : ℂ} (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) (x : ℝ) :
    ‖nevanlinnaKernel z x‖ ≤ (‖z + I‖ + ‖z - I‖) / (‖z + I‖ - ‖z - I‖) := by
  have hzim : 0 < z.im := hz
  have hlt : ‖z - I‖ < ‖z + I‖ := by
    refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
    rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
    simp only [normSq_apply, sub_re, sub_im, add_re, add_im, I_re, I_im]
    nlinarith
  have hDpos : (0 : ℝ) < ‖z + I‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  have hEnonneg : (0 : ℝ) ≤ ‖z - I‖ := norm_nonneg _
  set D := ‖z + I‖ with hD
  set E := ‖z - I‖ with hE
  set W := ‖(z - I) / (z + I)‖ with hW
  have hWeq : D * W = E := by
    rw [hW, norm_div, ← hD, ← hE]
    field_simp
  have hWlt : W < 1 := by nlinarith
  have hWnonneg : (0 : ℝ) ≤ W := norm_nonneg _
  have hzeta : ‖(boundaryCayley x : ℂ)‖ = 1 := Circle.norm_coe _
  have hnum : ‖(boundaryCayley x : ℂ) + (z - I) / (z + I)‖ ≤ 1 + W := by
    calc ‖(boundaryCayley x : ℂ) + (z - I) / (z + I)‖
        ≤ ‖(boundaryCayley x : ℂ)‖ + W := norm_add_le _ _
      _ = 1 + W := by rw [hzeta]
  have hden : 1 - W ≤ ‖(boundaryCayley x : ℂ) - (z - I) / (z + I)‖ := by
    have := norm_sub_norm_le ((boundaryCayley x : ℂ)) ((z - I) / (z + I))
    rwa [hzeta] at this
  have hdenpos : (0 : ℝ) < ‖(boundaryCayley x : ℂ) - (z - I) / (z + I)‖ :=
    lt_of_lt_of_le (by linarith) hden
  rw [← I_mul_herglotzKernel_cayley z x hz, norm_mul, norm_I, one_mul, norm_div,
    div_le_div_iff₀ hdenpos (by nlinarith)]
  nlinarith [mul_le_mul_of_nonneg_right hnum (by nlinarith : (0 : ℝ) ≤ D - E),
    mul_le_mul_of_nonneg_left hden (by nlinarith : (0 : ℝ) ≤ D + E)]

/-- The Nevanlinna kernel at a nonreal point is continuous in the real variable. -/
@[fun_prop]
theorem continuous_nevanlinnaKernel {z : ℂ} (hz : z.im ≠ 0) :
    Continuous (nevanlinnaKernel z) := by
  unfold nevanlinnaKernel
  refine Continuous.div (by fun_prop) (by fun_prop) fun x h ↦ ?_
  have := congrArg im h
  simp only [sub_im, ofReal_im, zero_sub, zero_im, neg_eq_zero] at this
  exact hz this

/-- The Nevanlinna kernel at a point of the upper half-plane is integrable against every finite
measure on the real line, so the Nevanlinna representation is an honest Bochner integral. -/
theorem integrable_nevanlinnaKernel {z : ℂ} (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet)
    (mu : Measure ℝ) [IsFiniteMeasure mu] : Integrable (nevanlinnaKernel z) mu :=
  .of_bound (continuous_nevanlinnaKernel (ne_of_gt hz)).aestronglyMeasurable _
    (.of_forall (norm_nevanlinnaKernel_le hz))

private theorem I_mul_one_add_cayley_div_one_sub (z : ℂ)
    (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    I * ((1 + (z - I) / (z + I)) / (1 - (z - I) / (z + I))) = z := by
  have hzpos : 0 < z.im := hz
  have hzi : z + I ≠ 0 := by
    intro h
    have := congrArg im h
    simp only [add_im, I_im, zero_im] at this
    linarith
  field_simp [hzi, I_mul_I]
  ring

/-- Transporting a Cayley-coordinate Herglotz transform to the real line separates the atom at
`1` as a nonnegative linear coefficient and writes the remaining term with the Nevanlinna kernel.
-/
theorem I_mul_herglotzTransform_cayley_eq (mu : Measure Circle) [IsFiniteMeasure mu]
    {z : ℂ} (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    I * mu.herglotzTransform ((z - I) / (z + I)) =
      (mu.real {1} : ℂ) * z + ∫ x, nevanlinnaKernel z x ∂mu.cayleyPushforward := by
  let w := (z - I) / (z + I)
  have hw : w ∈ ball (0 : ℂ) 1 := by
    let tau : UpperHalfPlane := ⟨z, hz⟩
    let i : UpperHalfPlane := ⟨I, by simp⟩
    have h := UpperHalfPlane.norm_discCoordinate_lt_one i tau
    rw [UpperHalfPlane.discCoordinate_def] at h
    simpa only [tau, i, UpperHalfPlane.coe_mk, map_neg, conj_I, sub_neg_eq_add,
      mem_ball_zero_iff, w] using h
  have hcont : Continuous fun u : Circle ↦ I * (((u : ℂ) + w) / ((u : ℂ) - w)) :=
    continuous_const.mul <| (continuous_subtype_val.add continuous_const).div
      (continuous_subtype_val.sub continuous_const) fun u hu ↦ by
        have hnorm := Circle.norm_coe u
        rw [sub_eq_zero] at hu
        rw [hu] at hnorm
        exact (mem_ball_zero_iff.1 hw).ne hnorm
  rw [Measure.herglotzTransform_def, ← integral_const_mul,
    integral_circle_eq_atom_add_integral_cayleyPushforward mu _ hcont]
  simp only [w, Circle.coe_one, I_mul_herglotzKernel_cayley z _ hz]
  rw [I_mul_one_add_cayley_div_one_sub z hz]
  simp only [real_smul]

/-- **Nevanlinna representation of a Pick function.** A function holomorphic on the upper
half-plane with nonnegative imaginary part is the sum of a real constant, a linear term with
nonnegative coefficient, and the integral of the Nevanlinna kernel against a finite positive
measure on `ℝ`.

The linear coefficient is the mass at the omitted boundary point `1` of the circle measure in the
Cayley-coordinate Herglotz representation. -/
theorem exists_isFiniteMeasure_eq_nevanlinnaKernel_add {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F UpperHalfPlane.upperHalfPlaneSet)
    (him : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ (F z).im) :
    ∃ (rho : Measure ℝ) (b : ℝ), IsFiniteMeasure rho ∧ 0 ≤ b ∧
      ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
        F z = (b : ℂ) * z + ∫ x, nevanlinnaKernel z x ∂rho + (F I).re := by
  obtain ⟨mu, hmu, hrep⟩ :=
    exists_isFiniteMeasure_eq_I_mul_herglotzTransform_cayley_add hF him
  let _ := hmu
  refine ⟨mu.cayleyPushforward, mu.real {1}, inferInstance, measureReal_nonneg, fun z hz ↦ ?_⟩
  rw [hrep z hz, I_mul_herglotzTransform_cayley_eq mu hz]

end TauCeti

end
