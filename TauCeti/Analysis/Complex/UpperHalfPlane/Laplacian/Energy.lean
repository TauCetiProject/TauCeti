/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Analysis.Complex.UpperHalfPlane.Laplacian.Basic
import TauCeti.Analysis.Complex.UpperHalfPlane.Measure
import TauCeti.Analysis.InnerProductSpace.Laplacian.Integral

/-!
# The energy of the hyperbolic Laplacian

For functions `f, g : ℍ → ℂ`, with `f` of class `C²` and `g` of class `C¹` with compact support in
`ℍ`, the pairing of the hyperbolic Laplacian `Δ f = -y² (∂ₓ² + ∂ᵧ²) f` with `g` against the
invariant measure `dμ = dx dy / y²` is the Euclidean Dirichlet pairing of their gradients:

`∫_ℍ (Δ f) · conj g dμ = ∫_ℍ (∂ₓ f · conj (∂ₓ g) + ∂ᵧ f · conj (∂ᵧ g)) dx dy`.

The density `y⁻²` of `dμ` cancels the factor `y²` of `Δ`, and an integration by parts in `x` and
in `y` produces the right side, with no boundary terms since `g` has compact support in `ℍ`.
Derivatives are those of `f ∘ ofComplex` and `g ∘ ofComplex` on `ℂ`, viewed as a real vector
space, and the right side is a Lebesgue integral over the open upper half-plane of `ℂ`.

Two consequences are the nonnegativity of `Δ` on compactly supported functions, whose quadratic
form `∫ (Δ f) · conj f dμ` is the Dirichlet energy `∫ (|∂ₓ f|² + |∂ᵧ f|²) dx dy`, and its
symmetry `∫ (Δ f) · conj g dμ = ∫ f · conj (Δ g) dμ` for compactly supported `C²` functions.
These are the identities from which the Laplacian of a quotient `Γ\ℍ` is built as a nonnegative
self-adjoint operator.

## Main results

* `TauCeti.UpperHalfPlane.integral_hyperbolicLaplacian_mul_conj`: the energy identity
  `∫ (Δ f) · conj g dμ = ∫ (∂ₓ f · conj (∂ₓ g) + ∂ᵧ f · conj (∂ᵧ g)) dx dy`.
* `TauCeti.UpperHalfPlane.integral_hyperbolicLaplacian_mul_conj_self`: the quadratic form
  `∫ (Δ f) · conj f dμ` is the real Dirichlet energy `∫ (|∂ₓ f|² + |∂ᵧ f|²) dx dy`.
* `TauCeti.UpperHalfPlane.integral_hyperbolicLaplacian_mul_conj_eq_integral_mul_conj`: the
  symmetry `∫ (Δ f) · conj g dμ = ∫ f · conj (Δ g) dμ`.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set Topology
open UpperHalfPlane hiding I
open scoped ComplexConjugate Laplacian

namespace TauCeti.UpperHalfPlane

variable {f g : ℍ → ℂ}

/-- A function on `ℍ` with compact support that is `C¹` in the coordinates of `ℂ` extends by zero
to a compactly supported `C¹` function on `ℂ`, whose support lies in `ℍ`. -/
private theorem exists_contDiff_hasCompactSupport_eventuallyEq
    (hg : ContDiffOn ℝ 1 (g ∘ ofComplex) upperHalfPlaneSet) (hgc : HasCompactSupport g) :
    ∃ G : ℂ → ℂ, ContDiff ℝ 1 G ∧ HasCompactSupport G ∧ tsupport G ⊆ upperHalfPlaneSet ∧
      ∀ w ∈ upperHalfPlaneSet, G =ᶠ[𝓝 w] g ∘ ofComplex := by
  set K : Set ℂ := (↑) '' tsupport g
  have hK : IsCompact K := hgc.isCompact.image continuous_coe
  have hKU : K ⊆ upperHalfPlaneSet := by
    rintro _ ⟨z, -, rfl⟩
    exact z.im_pos
  set G : ℂ → ℂ := upperHalfPlaneSet.indicator (g ∘ ofComplex) with hG
  have hG0 (w : ℂ) (hw : w ∉ K) : G w = 0 := by
    by_cases hwU : w ∈ upperHalfPlaneSet
    · rw [hG, indicator_of_mem hwU, Function.comp_apply]
      refine image_eq_zero_of_notMem_tsupport fun h ↦ hw ⟨_, h, ?_⟩
      rw [ofComplex_apply_of_im_pos hwU, coe_mk]
    · exact indicator_of_notMem hwU _
  have hGg (w : ℂ) (hw : w ∈ upperHalfPlaneSet) : G =ᶠ[𝓝 w] g ∘ ofComplex := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hw] with x hx using indicator_of_mem hx _
  have hGK : tsupport G ⊆ K := closure_minimal (Function.support_subset_iff'.2 hG0) hK.isClosed
  refine ⟨G, contDiff_iff_contDiffAt.2 fun w ↦ ?_, HasCompactSupport.intro hK hG0,
    hGK.trans hKU, hGg⟩
  by_cases hw : w ∈ upperHalfPlaneSet
  · exact (hg.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hw)).congr_of_eventuallyEq (hGg w hw)
  · refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds fun h ↦ hw (hKU h)] with x hx
    exact hG0 x hx

/-- **The energy identity for the hyperbolic Laplacian.** For `f : ℍ → ℂ` of class `C²` and
`g : ℍ → ℂ` of class `C¹` with compact support in `ℍ`,
`∫_ℍ (Δ f) · conj g dμ = ∫_ℍ (∂ₓ f · conj (∂ₓ g) + ∂ᵧ f · conj (∂ᵧ g)) dx dy`, where
`dμ = dx dy / y²` is the invariant measure and the derivatives are those of `f ∘ ofComplex` and
`g ∘ ofComplex` in the directions `1` and `I`. Nothing is assumed about `f` beyond smoothness. -/
theorem integral_hyperbolicLaplacian_mul_conj
    (hf : ContDiffOn ℝ 2 (f ∘ ofComplex) upperHalfPlaneSet)
    (hg : ContDiffOn ℝ 1 (g ∘ ofComplex) upperHalfPlaneSet) (hgc : HasCompactSupport g) :
    ∫ z, hyperbolicLaplacian f z * conj (g z) =
      ∫ w in upperHalfPlaneSet,
        (fderiv ℝ (f ∘ ofComplex) w 1 * conj (fderiv ℝ (g ∘ ofComplex) w 1) +
          fderiv ℝ (f ∘ ofComplex) w I * conj (fderiv ℝ (g ∘ ofComplex) w I)) := by
  obtain ⟨G, hG, hGc, hGU, hGg⟩ := exists_contDiff_hasCompactSupport_eventuallyEq hg hgc
  -- Green's first identity on `ℂ` for the pairing `(a, b) ↦ a * conj b`, against `G`.
  set B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
    (ContinuousLinearMap.mul ℝ ℂ).bilinearComp (ContinuousLinearMap.id ℝ ℂ)
      conjCLE.toContinuousLinearMap
  have hB (a b : ℂ) : B a b = a * conj b := by simp [B]
  have hgreen := integral_bilinear_laplacian_eq_neg_integral_sum_fderiv (μ := volume)
    orthonormalBasisOneI B (u := f ∘ ofComplex)
    (fun w hw ↦ hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds (hGU hw))) hG hGc
  have hU : MeasurableSet upperHalfPlaneSet := isOpen_upperHalfPlaneSet.measurableSet
  have hG0 (w : ℂ) (hw : w ∉ upperHalfPlaneSet) : w ∉ tsupport G := fun h ↦ hw (hGU h)
  have hfG (w : ℂ) (hw : w ∈ upperHalfPlaneSet) :
      (w.im ^ 2)⁻¹ • (hyperbolicLaplacian f (ofComplex w) * conj (g (ofComplex w))) =
        -B (Δ (f ∘ ofComplex) w) (G w) := by
    have hw' : (w.im : ℂ) ≠ 0 := ofReal_ne_zero.2 (ne_of_gt hw)
    rw [hyperbolicLaplacian_apply, ofComplex_apply_of_im_pos hw, hB, coe_mk, mk_im,
      (hGg w hw).self_of_nhds, Function.comp_apply, ofComplex_apply_of_im_pos hw, real_smul]
    push_cast
    field_simp
  calc ∫ z, hyperbolicLaplacian f z * conj (g z)
      = ∫ w in upperHalfPlaneSet, -B (Δ (f ∘ ofComplex) w) (G w) := by
        rw [integral_eq_setIntegral_inv_im_sq_smul]
        exact setIntegral_congr_fun hU hfG
    _ = ∫ w, -B (Δ (f ∘ ofComplex) w) (G w) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw ↦ by
          simp [image_eq_zero_of_notMem_tsupport (hG0 w hw)]
    _ = ∫ w, ∑ i, B (fderiv ℝ (f ∘ ofComplex) w (orthonormalBasisOneI i))
          (fderiv ℝ G w (orthonormalBasisOneI i)) := by
        rw [integral_neg, hgreen, neg_neg]
    _ = ∫ w in upperHalfPlaneSet, ∑ i, B (fderiv ℝ (f ∘ ofComplex) w (orthonormalBasisOneI i))
          (fderiv ℝ G w (orthonormalBasisOneI i)) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw ↦ by
          simp [fderiv_of_notMem_tsupport ℝ (hG0 w hw)]).symm
    _ = _ := setIntegral_congr_fun hU fun w hw ↦ by
        simp [Fin.sum_univ_two, hB, (hGg w hw).fderiv_eq]

/-- **The Dirichlet energy.** For `f : ℍ → ℂ` of class `C²` with compact support in `ℍ`, the
quadratic form `∫_ℍ (Δ f) · conj f dμ` of the hyperbolic Laplacian is the real number
`∫_ℍ (|∂ₓ f|² + |∂ᵧ f|²) dx dy`, the integral of a nonnegative function. -/
theorem integral_hyperbolicLaplacian_mul_conj_self
    (hf : ContDiffOn ℝ 2 (f ∘ ofComplex) upperHalfPlaneSet) (hfc : HasCompactSupport f) :
    ∫ z, hyperbolicLaplacian f z * conj (f z) =
      ((∫ w in upperHalfPlaneSet,
        (‖fderiv ℝ (f ∘ ofComplex) w 1‖ ^ 2 + ‖fderiv ℝ (f ∘ ofComplex) w I‖ ^ 2) : ℝ) : ℂ) := by
  rw [integral_hyperbolicLaplacian_mul_conj hf (hf.of_le one_le_two) hfc, ← integral_complex_ofReal]
  push_cast
  simp only [mul_conj']

/-- **The hyperbolic Laplacian is symmetric** on compactly supported functions: for `f, g : ℍ → ℂ`
of class `C²` with compact support in `ℍ`, `∫_ℍ (Δ f) · conj g dμ = ∫_ℍ f · conj (Δ g) dμ`. -/
theorem integral_hyperbolicLaplacian_mul_conj_eq_integral_mul_conj
    (hf : ContDiffOn ℝ 2 (f ∘ ofComplex) upperHalfPlaneSet) (hfc : HasCompactSupport f)
    (hg : ContDiffOn ℝ 2 (g ∘ ofComplex) upperHalfPlaneSet) (hgc : HasCompactSupport g) :
    ∫ z, hyperbolicLaplacian f z * conj (g z) = ∫ z, f z * conj (hyperbolicLaplacian g z) := by
  have h : ∫ z, f z * conj (hyperbolicLaplacian g z) =
      conj (∫ z, hyperbolicLaplacian g z * conj (f z)) := by
    rw [← integral_conj]
    simp [mul_comm]
  rw [h, integral_hyperbolicLaplacian_mul_conj hf (hg.of_le one_le_two) hgc,
    integral_hyperbolicLaplacian_mul_conj hg (hf.of_le one_le_two) hfc, ← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun w ↦ ?_)
  simp only [map_add, map_mul, conj_conj]
  ring

end TauCeti.UpperHalfPlane
