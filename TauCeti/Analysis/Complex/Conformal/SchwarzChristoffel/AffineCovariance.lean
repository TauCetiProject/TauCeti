/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Vertex
public import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Affine covariance of the Schwarz--Christoffel map

A positive affine change `x ↦ c * x + d` of the real prevertices extends to an automorphism of
the upper half-plane.  This file computes its effect on the Schwarz--Christoffel integrand and on
the normalized primitive.  If `S = ∑ i, e i`, then the integrand acquires the factor `c ^ S`,
while the primitive acquires `c ^ (S + 1)` because the change of variable contributes one further
factor of `c`.

This covariance removes the translation and positive-scaling redundancy from the prevertex
parameters.

## Main results

* `TauCeti.schwarzChristoffelIntegrand_affine_prevertices` -- covariance of the integrand.
* `TauCeti.schwarzChristoffelPrimitive_affine_prevertices` -- covariance of the normalized
  primitive.
* `TauCeti.schwarzChristoffelPrimitive_affine_prevertices_of_exponent_sum_eq_neg_two` -- under
  the closing condition, the affine change scales the primitive by the inverse scale factor.
* `TauCeti.schwarzChristoffelVertex_affine_prevertices` -- covariance of the boundary values.
* `TauCeti.exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_affine_prevertices` -- a positive
  affine change of all prevertices preserves an affine image of the primitive and its boundary
  values.

## References

* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Filter Finset Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The Schwarz--Christoffel integrand is covariant under a positive affine change of all its
prevertices.  The exponent of the scale factor is the total turning exponent. -/
theorem schwarzChristoffelIntegrand_affine_prevertices (a e : ι → ℝ) {c : ℝ} (hc : 0 < c)
    (d : ℝ) (z : ℂ) :
    schwarzChristoffelIntegrand (fun i ↦ c * a i + d) e ((c : ℂ) * z + (d : ℂ)) =
      (c : ℂ) ^ ((∑ i, e i : ℝ) : ℂ) * schwarzChristoffelIntegrand a e z := by
  rw [schwarzChristoffelIntegrand_def, schwarzChristoffelIntegrand_def]
  have h_affine (i : ι) : (c : ℂ) * z + (d : ℂ) - ((c * a i + d : ℝ) : ℂ) =
      (c : ℂ) * (z - (a i : ℂ)) := by
    push_cast
    ring
  simp_rw [h_affine, TauCeti.ofReal_mul_cpow hc.le, Finset.prod_mul_distrib]
  congr 1
  rw [Complex.ofReal_sum]
  exact (cpow_sum (Complex.ofReal_ne_zero.mpr hc.ne') (fun i ↦ (e i : ℂ)) Finset.univ).symm

/-- The normalized Schwarz--Christoffel primitive is covariant under a simultaneous positive
affine change of its prevertices, base point, and argument.  Its scale exponent is one more than
the total turning exponent. -/
theorem schwarzChristoffelPrimitive_affine_prevertices (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {c : ℝ} (hc : 0 < c) (d : ℝ) {z : ℂ}
    (hz : z ∈ upperHalfPlaneSet) :
    schwarzChristoffelPrimitive (fun i ↦ c * a i + d) e
        (d +ᵥ ((⟨c, hc⟩ : {x : ℝ // 0 < x}) • z₀))
        ((c : ℂ) * z + (d : ℂ)) =
      (c : ℂ) ^ (((∑ i, e i) + 1 : ℝ) : ℂ) *
        schwarzChristoffelPrimitive a e z₀ z := by
  let a' : ι → ℝ := fun i ↦ c * a i + d
  let z₀' : UpperHalfPlane := d +ᵥ ((⟨c, hc⟩ : {x : ℝ // 0 < x}) • z₀)
  let C : ℂ := (c : ℂ) ^ (((∑ i, e i) + 1 : ℝ) : ℂ)
  have hc₀ : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hcoe : (z₀' : ℂ) = (c : ℂ) * (z₀ : ℂ) + (d : ℂ) := by
    simp [z₀', UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_pos_real_smul,
      Complex.real_smul, add_comm]
  have hC : C = (c : ℂ) ^ ((∑ i, e i : ℝ) : ℂ) * (c : ℂ) := by
    dsimp only [C]
    have h_exp : (((∑ i, e i) + 1 : ℝ) : ℂ) = ((∑ i, e i : ℝ) : ℂ) + 1 := by
      push_cast
      ring
    rw [h_exp, Complex.cpow_add _ _ hc₀, Complex.cpow_one]
  have hleft : ∀ w ∈ upperHalfPlaneSet,
      HasDerivAt
        (schwarzChristoffelPrimitive a' e z₀' ∘
          fun ζ : ℂ ↦ (c : ℂ) * ζ + (d : ℂ))
        (C * schwarzChristoffelIntegrand a e w) w := by
    intro w hw
    have hinner : HasDerivAt (fun ζ : ℂ ↦ (c : ℂ) * ζ + (d : ℂ)) (c : ℂ) w := by
      simpa using ((hasDerivAt_id w).const_mul (c : ℂ)).add_const (d : ℂ)
    have hcomp :=
      (hasDerivAt_schwarzChristoffelPrimitive a' e z₀'
        (by simpa [upperHalfPlaneSet, mul_im] using mul_pos hc hw)).comp w hinner
    have hderiv :
        schwarzChristoffelIntegrand a' e
            ((c : ℂ) * w + (d : ℂ)) * (c : ℂ) =
          C * schwarzChristoffelIntegrand a e w := by
      simp only [a']
      rw [schwarzChristoffelIntegrand_affine_prevertices a e hc d w, hC]
      ring
    exact hcomp.congr_deriv hderiv
  have hC₀ : C ≠ 0 := by
    rw [hC]
    exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hc₀)) hc₀
  have hg : ∀ w ∈ upperHalfPlaneSet,
      HasDerivAt
        (fun ζ : ℂ ↦ C⁻¹ * schwarzChristoffelPrimitive a' e z₀'
          ((c : ℂ) * ζ + (d : ℂ)))
        (schwarzChristoffelIntegrand a e w) w := by
    intro w hw
    refine ((hleft w hw).const_mul C⁻¹).congr_deriv ?_
    rw [← mul_assoc, inv_mul_cancel₀ hC₀, one_mul]
  have hg₀ : C⁻¹ * schwarzChristoffelPrimitive a' e z₀'
      ((c : ℂ) * (z₀ : ℂ) + (d : ℂ)) = 0 := by
    rw [← hcoe, schwarzChristoffelPrimitive_apply_base, mul_zero]
  have heq := eqOn_schwarzChristoffelPrimitive a e z₀ hg hg₀ hz
  have hscaled : schwarzChristoffelPrimitive a' e z₀'
      ((c : ℂ) * z + (d : ℂ)) = C * schwarzChristoffelPrimitive a e z₀ z := by
    calc
      _ = C * (C⁻¹ * schwarzChristoffelPrimitive a' e z₀'
          ((c : ℂ) * z + (d : ℂ))) := (mul_inv_cancel_left₀ hC₀ _).symm
      _ = C * schwarzChristoffelPrimitive a e z₀ z := congr_arg (C * ·) heq
  simpa only [a', z₀', C] using hscaled

/-- Under the polygonal closing condition `∑ i, e i = -2`, a positive affine change
`x ↦ c * x + d` of the prevertices, base point, and argument multiplies the normalized
Schwarz--Christoffel primitive by `c⁻¹`. -/
theorem schwarzChristoffelPrimitive_affine_prevertices_of_exponent_sum_eq_neg_two (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {c : ℝ} (hc : 0 < c) (d : ℝ) (hsum : ∑ i, e i = -2)
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    schwarzChristoffelPrimitive (fun i ↦ c * a i + d) e
        (d +ᵥ ((⟨c, hc⟩ : {x : ℝ // 0 < x}) • z₀))
        ((c : ℂ) * z + (d : ℂ)) =
      (c : ℂ)⁻¹ * schwarzChristoffelPrimitive a e z₀ z := by
  rw [schwarzChristoffelPrimitive_affine_prevertices a e z₀ hc d hz, hsum]
  norm_num [Complex.cpow_neg]

/-- A positive affine change of the prevertices scales their Schwarz--Christoffel boundary values
by the same factor as the primitive.  Keeping the original base point introduces the displayed
translation, independent of the chosen prevertex. -/
theorem schwarzChristoffelVertex_affine_prevertices (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {c : ℝ} (hc : 0 < c) (d : ℝ) (j : ι)
    (hj : -1 < ∑ i with a i = a j, e i) :
    schwarzChristoffelVertex (fun i ↦ c * a i + d) e z₀ j =
      (c : ℂ) ^ (((∑ i, e i) + 1 : ℝ) : ℂ) *
        schwarzChristoffelVertex a e z₀ j -
      schwarzChristoffelPrimitive (fun i ↦ c * a i + d) e
        (d +ᵥ ((⟨c, hc⟩ : {x : ℝ // 0 < x}) • z₀)) z₀ := by
  let a' : ι → ℝ := fun i ↦ c * a i + d
  let z₀' : UpperHalfPlane := d +ᵥ ((⟨c, hc⟩ : {x : ℝ // 0 < x}) • z₀)
  let C : ℂ := (c : ℂ) ^ (((∑ i, e i) + 1 : ℝ) : ℂ)
  let φ : ℂ → ℂ := fun z ↦ (c : ℂ) * z + (d : ℂ)
  have hc0 : c ≠ 0 := hc.ne'
  have hj' : -1 < ∑ i with a' i = a' j, e i := by
    have hfiber (i : ι) : a' i = a' j ↔ a i = a j := by
      constructor
      · intro h
        apply mul_left_cancel₀ hc0
        exact add_right_cancel h
      · exact fun h ↦ congrArg (fun x ↦ c * x + d) h
    simpa only [hfiber] using hj
  have hφ_maps : MapsTo φ upperHalfPlaneSet upperHalfPlaneSet := by
    intro z hz
    simpa [upperHalfPlaneSet, φ, mul_im] using mul_pos hc hz
  have hφ_tendsto : Tendsto φ (𝓝[upperHalfPlaneSet] (a j : ℂ))
      (𝓝[upperHalfPlaneSet] (a' j : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hcont : ContinuousAt φ (a j : ℂ) := by fun_prop
      have ht := hcont.tendsto.mono_left
        (@inf_le_left (Filter ℂ) _ (𝓝 (a j : ℂ)) (𝓟 upperHalfPlaneSet))
      have hcenter : ((a' j : ℝ) : ℂ) = φ (a j : ℂ) := by
        dsimp only [a', φ]
        push_cast
        rfl
      rw [hcenter]
      exact ht
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact hφ_maps hz
  have hleft :=
    (tendsto_schwarzChristoffelPrimitive a' e z₀' j hj').comp hφ_tendsto
  have hright : Tendsto (fun z ↦ C * schwarzChristoffelPrimitive a e z₀ z)
      (𝓝[upperHalfPlaneSet] (a j : ℂ))
      (𝓝 (C * schwarzChristoffelVertex a e z₀ j)) :=
    tendsto_const_nhds.mul (tendsto_schwarzChristoffelPrimitive a e z₀ j hj)
  have heq : (fun z ↦ schwarzChristoffelPrimitive a' e z₀' (φ z)) =ᶠ[
      𝓝[upperHalfPlaneSet] (a j : ℂ)]
      (fun z ↦ C * schwarzChristoffelPrimitive a e z₀ z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact schwarzChristoffelPrimitive_affine_prevertices a e z₀ hc d hz
  have := Real.nhdsWithin_upperHalfPlaneSet_neBot (a j)
  have hvertex : schwarzChristoffelVertex a' e z₀' j =
      C * schwarzChristoffelVertex a e z₀ j :=
    tendsto_nhds_unique hleft (hright.congr' heq.symm)
  rw [schwarzChristoffelVertex_change_base a' e z₀ z₀' j hj', hvertex]

/-- A positive affine change of all real prevertices preserves the domain represented by an
affine image of the Schwarz--Christoffel primitive.  The normalization point of the primitive is
kept fixed; its change under reparametrization is absorbed into the additive constant.  At every
integrable prevertex, the adjusted affine images of the old and new boundary values agree. -/
theorem exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_affine_prevertices
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {c : ℝ} (hc : 0 < c) (d : ℝ)
    {A B : ℂ} {U : Set ℂ}
    (hbij : BijOn (fun z ↦ A * schwarzChristoffelPrimitive a e z₀ z + B)
      upperHalfPlaneSet U) :
    ∃ A' : ℂ, A' ≠ 0 ∧ ∃ B' : ℂ,
      BijOn (fun z ↦ A' *
        schwarzChristoffelPrimitive (fun i ↦ c * a i + d) e z₀ z + B')
        upperHalfPlaneSet U ∧
      ∀ j, -1 < ∑ i with a i = a j, e i →
        A' * schwarzChristoffelVertex (fun i ↦ c * a i + d) e z₀ j + B' =
          A * schwarzChristoffelVertex a e z₀ j + B := by
  have hA : A ≠ 0 := ne_zero_of_injOn_const_mul_add hbij.injOn
  let C : ℂ := (c : ℂ) ^ (((∑ i, e i) + 1 : ℝ) : ℂ)
  let z₀' : UpperHalfPlane := d +ᵥ ((⟨c, hc⟩ : {x : ℝ // 0 < x}) • z₀)
  let A' : ℂ := A * C⁻¹
  let B' : ℂ := B + A' *
    schwarzChristoffelPrimitive (fun i ↦ c * a i + d) e z₀' z₀
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hC : C ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hc0)
  have hA' : A' ≠ 0 := mul_ne_zero hA (inv_ne_zero hC)
  let φ : ℂ → ℂ := fun z ↦ (c : ℂ) * z + (d : ℂ)
  let ψ : UpperHalfPlane → UpperHalfPlane := fun z ↦
    d +ᵥ ((⟨c, hc⟩ : {x : ℝ // 0 < x}) • z)
  have hc_unit : IsUnit (⟨c, hc⟩ : {x : ℝ // 0 < x}) := by
    refine ⟨Units.mk ⟨c, hc⟩ ⟨c⁻¹, inv_pos.mpr hc⟩ ?_ ?_, rfl⟩
    · ext
      exact mul_inv_cancel₀ hc.ne'
    · ext
      exact inv_mul_cancel₀ hc.ne'
  have hψ : Function.Bijective ψ :=
    (AddAction.bijective d).comp hc_unit.smul_bijective
  have hsemiconj : Function.Semiconj UpperHalfPlane.coe ψ φ := by
    intro z
    simp only [ψ, φ, UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_pos_real_smul,
      Complex.real_smul]
    ring
  have hφ : BijOn φ upperHalfPlaneSet upperHalfPlaneSet := by
    rw [← UpperHalfPlane.range_coe]
    exact hsemiconj.bijOn_range hψ UpperHalfPlane.coe_injective
  have heq : Set.EqOn
      ((fun w ↦ A' *
        schwarzChristoffelPrimitive (fun i ↦ c * a i + d) e z₀ w + B') ∘ φ)
      (fun z ↦ A * schwarzChristoffelPrimitive a e z₀ z + B)
      upperHalfPlaneSet := by
    intro z hz
    rw [Function.comp_apply,
      schwarzChristoffelPrimitive_change_base (fun i ↦ c * a i + d) e z₀ z₀'
        (hφ.mapsTo hz),
      schwarzChristoffelPrimitive_affine_prevertices a e z₀ hc d hz]
    dsimp only [A', B']
    field_simp
    ring
  refine ⟨A', hA', B', ?_, fun j hj ↦ ?_⟩
  · rw [← hφ.image_eq]
    exact (bijOn_comp_iff hφ.injOn).mp (hbij.congr heq.symm)
  · rw [schwarzChristoffelVertex_affine_prevertices a e z₀ hc d j hj]
    dsimp only [A', B']
    field_simp
    ring

end TauCeti

end
