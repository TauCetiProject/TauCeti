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
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.Indicator
import TauCeti.Analysis.Calculus.ContDiff.IsOpen
import TauCeti.Analysis.Complex.UpperHalfPlane.Measure
import TauCeti.Analysis.InnerProductSpace.Laplacian.Integral

/-!
# The energy of the hyperbolic Laplacian

For functions `f, g : ℍ → ℂ`, with `g` of class `C¹` with compact support in `ℍ` and `f` of class
`C²` near the support of `g`, the pairing of the hyperbolic Laplacian `Δ f = -y² (∂ₓ² + ∂ᵧ²) f`
with `g` against the invariant measure `dμ = dx dy / y²` is the Euclidean Dirichlet pairing of
their gradients:

`∫_ℍ (Δ f) · conj g dμ = ∫_ℍ (∂ₓ f · conj (∂ₓ g) + ∂ᵧ f · conj (∂ᵧ g)) dx dy`.

The density `y⁻²` of `dμ` cancels the factor `y²` of `Δ`, and an integration by parts in `x` and
in `y` produces the right side, with no boundary terms since `g` has compact support in `ℍ`.
Derivatives are those of `f ∘ ofComplex` and `g ∘ ofComplex` on `ℂ`, viewed as a real vector
space, and the right side is a Lebesgue integral over the open upper half-plane of `ℂ`.

Two consequences are the nonnegativity of `Δ` on compactly supported functions, whose quadratic
form `∫ (Δ f) · conj f dμ` is the Dirichlet energy `∫ (|∂ₓ f|² + |∂ᵧ f|²) dx dy`, and its
symmetry `∫ (Δ f) · conj g dμ = ∫ f · conj (Δ g) dμ` for `g` compactly supported and `C²` and `f`
`C²` near the support of `g`.
These are the identities from which the Laplacian of a quotient `Γ\ℍ` is built as a nonnegative
self-adjoint operator.

## Main results

* `TauCeti.UpperHalfPlane.integral_hyperbolicLaplacian_mul_conj`: the energy identity
  `∫ (Δ f) · conj g dμ = ∫ (∂ₓ f · conj (∂ₓ g) + ∂ᵧ f · conj (∂ᵧ g)) dx dy`.
* `TauCeti.UpperHalfPlane.integral_hyperbolicLaplacian_mul_conj_self`: the quadratic form
  `∫ (Δ f) · conj f dμ` is the real Dirichlet energy `∫ (|∂ₓ f|² + |∂ᵧ f|²) dx dy`.
* `integral_hyperbolicLaplacian_mul_conj_eq_integral_mul_conj_hyperbolicLaplacian` (in
  `TauCeti.UpperHalfPlane`): the symmetry `∫ (Δ f) · conj g dμ = ∫ f · conj (Δ g) dμ`.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set Topology
open UpperHalfPlane hiding I
open scoped ComplexConjugate Laplacian

namespace TauCeti.UpperHalfPlane

variable {f g : ℍ → ℂ}

/-- A function on `ℍ` with compact support that is `C¹` in the coordinates of `ℂ` extends by zero
to a compactly supported `C¹` function on `ℂ`, whose support lies in the image of that of `g`. -/
private theorem exists_contDiff_hasCompactSupport_eventuallyEq
    (hg : ContDiffOn ℝ 1 (g ∘ ofComplex) upperHalfPlaneSet) (hgc : HasCompactSupport g) :
    ∃ G : ℂ → ℂ, ContDiff ℝ 1 G ∧ HasCompactSupport G ∧ tsupport G ⊆ (↑) '' tsupport g ∧
      ∀ w ∈ upperHalfPlaneSet, G =ᶠ[𝓝 w] g ∘ ofComplex := by
  set K : Set ℂ := (↑) '' tsupport g
  have hK : IsCompact K := hgc.isCompact.image continuous_coe
  have hKU : K ⊆ upperHalfPlaneSet := by
    rintro _ ⟨z, -, rfl⟩
    exact z.im_pos
  have hgK : upperHalfPlaneSet ∩ Function.support (g ∘ ofComplex) ⊆ K := fun w ⟨hw, hgw⟩ ↦
    ⟨_, subset_tsupport _ hgw, by rw [ofComplex_apply_of_im_pos hw, coe_mk]⟩
  have hGK : tsupport (upperHalfPlaneSet.indicator (g ∘ ofComplex)) ⊆ K :=
    closure_minimal (support_indicator.trans_subset hgK) hK.isClosed
  refine ⟨_, hg.contDiff_indicator_of_isClosed isOpen_upperHalfPlaneSet hK.isClosed hKU hgK,
    hK.of_isClosed_subset isClosed_closure hGK, hGK, fun w hw ↦ ?_⟩
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hw] with x hx using indicator_of_mem hx _

/-- **The energy identity for the hyperbolic Laplacian.** For `g : ℍ → ℂ` of class `C¹` with
compact support in `ℍ` and `f : ℍ → ℂ` of class `C²` near the support of `g`,
`∫_ℍ (Δ f) · conj g dμ = ∫_ℍ (∂ₓ f · conj (∂ₓ g) + ∂ᵧ f · conj (∂ᵧ g)) dx dy`, where
`dμ = dx dy / y²` is the invariant measure and the derivatives are those of `f ∘ ofComplex` and
`g ∘ ofComplex` in the directions `1` and `I`. Nothing is assumed about `f` beyond smoothness
near the support of `g`. -/
theorem integral_hyperbolicLaplacian_mul_conj
    (hf : ∀ z ∈ tsupport g, ContDiffAt ℝ 2 (f ∘ ofComplex) z)
    (hg : ContDiffOn ℝ 1 (g ∘ ofComplex) upperHalfPlaneSet) (hgc : HasCompactSupport g) :
    ∫ z, hyperbolicLaplacian f z * conj (g z) =
      ∫ w in upperHalfPlaneSet,
        (fderiv ℝ (f ∘ ofComplex) w 1 * conj (fderiv ℝ (g ∘ ofComplex) w 1) +
          fderiv ℝ (f ∘ ofComplex) w I * conj (fderiv ℝ (g ∘ ofComplex) w I)) := by
  obtain ⟨G, hG, hGc, hGK, hGg⟩ := exists_contDiff_hasCompactSupport_eventuallyEq hg hgc
  have hGU : tsupport G ⊆ upperHalfPlaneSet := by
    rintro _ hw
    obtain ⟨z, -, rfl⟩ := hGK hw
    exact z.im_pos
  -- Green's first identity on `ℂ` for the pairing `(a, b) ↦ a * conj b`, against `G`.
  set B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
    (ContinuousLinearMap.mul ℝ ℂ).bilinearComp (ContinuousLinearMap.id ℝ ℂ)
      conjCLE.toContinuousLinearMap
  have hB (a b : ℂ) : B a b = a * conj b := by simp [B]
  have hgreen := integral_bilinear_laplacian_eq_neg_integral_sum_fderiv (μ := volume)
    orthonormalBasisOneI B (u := f ∘ ofComplex)
    (fun w hw ↦ by obtain ⟨z, hz, rfl⟩ := hGK hw; exact hf z hz) hG hGc
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
  have hf' (z : ℍ) (_ : z ∈ tsupport f) : ContDiffAt ℝ 2 (f ∘ ofComplex) z :=
    hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  rw [integral_hyperbolicLaplacian_mul_conj hf' (hf.of_le one_le_two) hfc,
    ← integral_complex_ofReal]
  push_cast
  simp only [mul_conj']

/-- A function on `ℍ` of class `C²` near the compact support of `g` agrees near that support with
a compactly supported function on `ℍ` of class `C²`. -/
private theorem exists_contDiffOn_hasCompactSupport_eventuallyEq
    (hf : ∀ z ∈ tsupport g, ContDiffAt ℝ 2 (f ∘ ofComplex) z) (hgc : HasCompactSupport g) :
    ∃ f₀ : ℍ → ℂ, ContDiffOn ℝ 2 (f₀ ∘ ofComplex) upperHalfPlaneSet ∧ HasCompactSupport f₀ ∧
      ∀ z ∈ tsupport g, f ∘ ofComplex =ᶠ[𝓝 (z : ℂ)] f₀ ∘ ofComplex := by
  set K : Set ℂ := (↑) '' tsupport g
  have hK : IsCompact K := hgc.isCompact.image continuous_coe
  have hfK : ∀ w ∈ K, ContDiffAt ℝ 2 (f ∘ ofComplex) w := by
    rintro _ ⟨z, hz, rfl⟩
    exact hf z hz
  obtain ⟨U, hU, hKU, hfU⟩ := TauCeti.exists_isOpen_superset_contDiffOn (by simp) hfK
  have hKH : K ⊆ upperHalfPlaneSet := by rintro _ ⟨z, -, rfl⟩; exact z.im_pos
  obtain ⟨F, hF, hFc, hFU, -, hFf⟩ :=
    (hfU.mono inter_subset_left).exists_contDiff_eventuallyEq_on_isCompact hK
      (hU.inter isOpen_upperHalfPlaneSet) (subset_inter hKU hKH)
  have hF₀ (w : ℂ) (hw : w ∈ upperHalfPlaneSet) : (F ∘ (↑) : ℍ → ℂ) (ofComplex w) = F w := by
    simp [ofComplex_apply_of_im_pos hw]
  refine ⟨F ∘ (↑), hF.contDiffOn.congr fun w hw ↦ hF₀ w hw,
    (isEmbedding_coe.isInducing.isCompact_preimage' hFc fun w hw ↦ ⟨⟨w, (hFU hw).2⟩, rfl⟩)
      |>.of_isClosed_subset isClosed_closure (tsupport_comp_subset_preimage F continuous_coe),
    fun z hz ↦ ?_⟩
  filter_upwards [hFf _ ⟨z, hz, rfl⟩, isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw hwH
  rw [← hw, Function.comp_apply, hF₀ w hwH]

/-- **The hyperbolic Laplacian is symmetric**: for `g : ℍ → ℂ` of class `C²` with compact support
in `ℍ` and `f : ℍ → ℂ` of class `C²` near the support of `g`,
`∫_ℍ (Δ f) · conj g dμ = ∫_ℍ f · conj (Δ g) dμ`. Both sides only see `f` near the support of `g`,
so `f` is first replaced by a compactly supported `C²` function agreeing with it there. -/
theorem integral_hyperbolicLaplacian_mul_conj_eq_integral_mul_conj_hyperbolicLaplacian
    (hf : ∀ z ∈ tsupport g, ContDiffAt ℝ 2 (f ∘ ofComplex) z)
    (hg : ContDiffOn ℝ 2 (g ∘ ofComplex) upperHalfPlaneSet) (hgc : HasCompactSupport g) :
    ∫ z, hyperbolicLaplacian f z * conj (g z) = ∫ z, f z * conj (hyperbolicLaplacian g z) := by
  obtain ⟨f₀, hf₀, hf₀c, hff₀⟩ := exists_contDiffOn_hasCompactSupport_eventuallyEq hf hgc
  have hf₀' (z : ℍ) (_ : z ∈ tsupport g) : ContDiffAt ℝ 2 (f₀ ∘ ofComplex) z :=
    hf₀.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  have hg' (z : ℍ) (_ : z ∈ tsupport f₀) : ContDiffAt ℝ 2 (g ∘ ofComplex) z :=
    hg.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  calc ∫ z, hyperbolicLaplacian f z * conj (g z)
      = ∫ z, hyperbolicLaplacian f₀ z * conj (g z) := integral_congr_ae <| ae_of_all _ fun z ↦ by
        by_cases hz : z ∈ tsupport g
        · simp only [hyperbolicLaplacian_congr_nhds (hff₀ z hz)]
        · simp [image_eq_zero_of_notMem_tsupport hz]
    _ = conj (∫ z, hyperbolicLaplacian g z * conj (f₀ z)) := by
        rw [integral_hyperbolicLaplacian_mul_conj hf₀' (hg.of_le one_le_two) hgc,
          integral_hyperbolicLaplacian_mul_conj hg' (hf₀.of_le one_le_two) hf₀c, ← integral_conj]
        refine integral_congr_ae (ae_of_all _ fun w ↦ ?_)
        simp only [map_add, map_mul, conj_conj]
        ring
    _ = ∫ z, f₀ z * conj (hyperbolicLaplacian g z) := by
        rw [← integral_conj]
        simp [mul_comm]
    _ = ∫ z, f z * conj (hyperbolicLaplacian g z) := integral_congr_ae <| ae_of_all _ fun z ↦ by
        by_cases hz : z ∈ tsupport g
        · simpa [ofComplex_apply] using congrArg (· * conj (hyperbolicLaplacian g z))
            (hff₀ z hz).self_of_nhds.symm
        · simp [hyperbolicLaplacian_eq_zero_of_notMem_tsupport hz]

end TauCeti.UpperHalfPlane
