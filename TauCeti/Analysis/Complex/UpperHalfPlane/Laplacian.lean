/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.NumberTheory.ModularForms.SlashActions
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Calculus.FDeriv.OfReal
import TauCeti.Analysis.Complex.Conformal.Laplacian
import TauCeti.Analysis.Complex.UpperHalfPlane.SmulDeriv
import TauCeti.Analysis.Complex.Wirtinger.Laplacian
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.NumberTheory.ModularForms.Basic

/-!
# The hyperbolic Laplacian and the weight-`k` Laplacians on the upper half-plane

For `f : ℍ → ℂ` and `z = x + iy ∈ ℍ`, the **hyperbolic Laplacian** is the nonnegative operator

`Δ f = -y² (∂ₓ² + ∂ᵧ²) f`,

and for a real weight `k` the **weight-`k` Laplacian** is

`Δ_k f = -y² (∂ₓ² + ∂ᵧ²) f + i k y (∂ₓ + i ∂ᵧ) f`,

so that `Δ₀ = Δ`. The first-order operator `∂ₓ + i ∂ᵧ` is twice the conjugate Wirtinger
derivative `\bar∂` (`TauCeti.conjWirtingerDeriv`), which is how it enters the definition: it
annihilates holomorphic functions, and after a holomorphic map with derivative `a` it picks up
the factor `conj a`. Derivatives are taken of `f ∘ ofComplex`, the function on `ℂ` obtained through
Mathlib's partial inverse `UpperHalfPlane.ofComplex` of the inclusion `ℍ → ℂ`, with `ℂ` viewed as a
two-dimensional real inner product space; the junk values of `ofComplex` off `ℍ` do not matter,
since all derivatives are taken at points of the open set `ℍ`. This is the sign convention under
which the Laplace eigenvalues of Maass forms are nonnegative; the operator `y² (∂ₓ² + ∂ᵧ²)` of
the opposite convention is `-Δ`.

The main results are:

* the power law `Δ_k y^s = s (1 - k - s) y^s` for every complex `s`, in particular
  `Δ y^s = s (1 - s) y^s`;
* the invariance of `Δ` under every orientation-preserving isometry `τ ↦ g • τ` of `ℍ`,
  `Δ (f ∘ g) = (Δ f) ∘ g` for `g ∈ GL(2, ℝ)` with positive determinant;
* for an integral weight `k` and the same `g`, the commutation of `Δ_k` with the weight-`k`
  slash action `f ↦ f ∣[k] g`.

The commutation follows from the conformal covariance of the planar Laplacian under the
holomorphic map `τ ↦ g • τ`, whose derivative is `det g / (cτ + d)²`, together with
`Im (g • τ) = det g · Im τ / |cτ + d|²` and the product rule for the holomorphic automorphy
factor `(cτ + d)^(-k)`.

## Main declarations

* `TauCeti.UpperHalfPlane.hyperbolicLaplacian`: the hyperbolic Laplacian `Δ`.
* `TauCeti.UpperHalfPlane.weightLaplacian`: the weight-`k` Laplacian `Δ_k`.
* `TauCeti.UpperHalfPlane.weightLaplacian_im_cpow`: `Δ_k y^s = s (1 - k - s) y^s`.
* `TauCeti.UpperHalfPlane.hyperbolicLaplacian_im_cpow`: `Δ y^s = s (1 - s) y^s`.
* `TauCeti.UpperHalfPlane.hyperbolicLaplacian_comp_smul`: `Δ (f ∘ g) = (Δ f) ∘ g` for
  `det g > 0`.
* `TauCeti.UpperHalfPlane.weightLaplacian_slash`: `Δ_k (f ∣[k] g) = (Δ_k f) ∣[k] g` for
  `det g > 0`.

## References

* H. Iwaniec, *Spectral Methods of Automorphic Forms*, second edition, Section 1.2 (the
  Laplacian of the upper half-plane and its invariance).
* J. H. Bruinier and J. Funke, *On two geometric theta lifts*, Duke Math. J. **125** (2004),
  Section 3, equation (3.1) (the weight-`k` Laplacian).
-/

public section

noncomputable section

open Complex Filter InnerProductSpace Laplacian Topology
open UpperHalfPlane hiding I
open scoped ModularForm

namespace TauCeti.UpperHalfPlane

/-- The **hyperbolic Laplacian** `Δ f = -y² (∂ₓ² + ∂ᵧ²) f` of `f : ℍ → ℂ` at `z = x + iy`,
with the sign convention making it a nonnegative operator. The Euclidean Laplacian is that of
`f ∘ ofComplex` on `ℂ`, viewed as a real inner product space. -/
def hyperbolicLaplacian (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  -((z.im : ℂ) ^ 2) * Δ (f ∘ ofComplex) (z : ℂ)

/-- The **weight-`k` Laplacian** `Δ_k f = -y² (∂ₓ² + ∂ᵧ²) f + i k y (∂ₓ + i ∂ᵧ) f` of
`f : ℍ → ℂ` at `z = x + iy`, for a real weight `k`, with `∂ₓ + i ∂ᵧ = 2 \bar∂` written through the
conjugate Wirtinger derivative (`TauCeti.UpperHalfPlane.weightLaplacian_eq_fderiv` gives the
coordinate form). Its weight-`0` case is the hyperbolic Laplacian
(`TauCeti.UpperHalfPlane.weightLaplacian_zero`). -/
def weightLaplacian (k : ℝ) (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  hyperbolicLaplacian f z + 2 * I * k * z.im * conjWirtingerDeriv (f ∘ ofComplex) z 1

/-- The defining formula of the hyperbolic Laplacian. -/
theorem hyperbolicLaplacian_apply (f : ℍ → ℂ) (z : ℍ) :
    hyperbolicLaplacian f z = -((z.im : ℂ) ^ 2) * Δ (f ∘ ofComplex) (z : ℂ) :=
  (rfl)

/-- The defining formula of the weight-`k` Laplacian. -/
theorem weightLaplacian_apply (k : ℝ) (f : ℍ → ℂ) (z : ℍ) :
    weightLaplacian k f z =
      hyperbolicLaplacian f z + 2 * I * k * z.im * conjWirtingerDeriv (f ∘ ofComplex) z 1 :=
  (rfl)

/-- The weight-`k` Laplacian in coordinates:
`Δ_k f = -y² (∂ₓ² + ∂ᵧ²) f + i k y (∂ₓ + i ∂ᵧ) f`. -/
theorem weightLaplacian_eq_fderiv (k : ℝ) (f : ℍ → ℂ) (z : ℍ) :
    weightLaplacian k f z = hyperbolicLaplacian f z +
      I * k * z.im * (fderiv ℝ (f ∘ ofComplex) z 1 + I * fderiv ℝ (f ∘ ofComplex) z I) := by
  have h := fderiv_apply_one_add_I_smul_fderiv_apply_I (f ∘ ofComplex) z
  rw [smul_eq_mul, smul_eq_mul] at h
  rw [weightLaplacian_apply, h]
  ring

/-- The weight-`0` Laplacian is the hyperbolic Laplacian. -/
@[simp]
theorem weightLaplacian_zero (f : ℍ → ℂ) : weightLaplacian 0 f = hyperbolicLaplacian f := by
  ext z
  simp [weightLaplacian_apply]

/-- The hyperbolic Laplacian annihilates constants. -/
@[simp]
theorem hyperbolicLaplacian_const (c : ℂ) : hyperbolicLaplacian (fun _ ↦ c) = 0 := by
  ext z
  simp [hyperbolicLaplacian_apply, Function.comp_def]

/-- The weight-`k` Laplacian annihilates constants. -/
@[simp]
theorem weightLaplacian_const (k : ℝ) (c : ℂ) : weightLaplacian k (fun _ ↦ c) = 0 := by
  ext z
  simp [weightLaplacian_apply, Function.comp_def]

section Linear

variable {f g : ℍ → ℂ} {z : ℍ}

/-- The hyperbolic Laplacian is additive on functions that are `C²` at the point. -/
theorem hyperbolicLaplacian_add (hf : ContDiffAt ℝ 2 (f ∘ ofComplex) z)
    (hg : ContDiffAt ℝ 2 (g ∘ ofComplex) z) :
    hyperbolicLaplacian (f + g) z = hyperbolicLaplacian f z + hyperbolicLaplacian g z := by
  rw [hyperbolicLaplacian_apply, hyperbolicLaplacian_apply, hyperbolicLaplacian_apply,
    Pi.add_comp, hf.laplacian_add hg, mul_add]

/-- The hyperbolic Laplacian commutes with complex scalars on functions that are `C²` at the
point. -/
theorem hyperbolicLaplacian_const_smul (c : ℂ) (hf : ContDiffAt ℝ 2 (f ∘ ofComplex) z) :
    hyperbolicLaplacian (c • f) z = c * hyperbolicLaplacian f z := by
  rw [hyperbolicLaplacian_apply, hyperbolicLaplacian_apply, Pi.smul_comp, laplacian_smul c hf,
    smul_eq_mul]
  ring

/-- The weight-`k` Laplacian is additive on functions that are `C²` at the point. -/
theorem weightLaplacian_add {k : ℝ} (hf : ContDiffAt ℝ 2 (f ∘ ofComplex) z)
    (hg : ContDiffAt ℝ 2 (g ∘ ofComplex) z) :
    weightLaplacian k (f + g) z = weightLaplacian k f z + weightLaplacian k g z := by
  rw [weightLaplacian_apply, weightLaplacian_apply, weightLaplacian_apply,
    hyperbolicLaplacian_add hf hg, Pi.add_comp, conjWirtingerDeriv_add
      (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num)), add_apply]
  ring

/-- The weight-`k` Laplacian commutes with complex scalars on functions that are `C²` at the
point. -/
theorem weightLaplacian_const_smul {k : ℝ} (c : ℂ) (hf : ContDiffAt ℝ 2 (f ∘ ofComplex) z) :
    weightLaplacian k (c • f) z = c * weightLaplacian k f z := by
  rw [weightLaplacian_apply, weightLaplacian_apply, hyperbolicLaplacian_const_smul c hf,
    Pi.smul_comp, conjWirtingerDeriv_const_smul, smul_apply, smul_eq_mul]
  ring

end Linear

section Power

/-- On `ℍ`, the function `τ ↦ (Im τ)^s`, read through `ofComplex`, is `w ↦ (Im w)^s` near every
point of `ℍ`. -/
private theorem im_cpow_comp_ofComplex_eventuallyEq (s : ℂ) (z : ℍ) :
    (fun τ : ℍ ↦ (τ.im : ℂ) ^ s) ∘ ofComplex =ᶠ[𝓝 (z : ℂ)] fun w ↦ (w.im : ℂ) ^ s := by
  rw [← isOpenEmbedding_coe.map_nhds_eq, eventuallyEq_map]
  filter_upwards with τ
  simp [ofComplex_apply]

/-- **The power law for the weight-`k` Laplacian**: `Δ_k y^s = s (1 - k - s) y^s` for every
complex `s`. -/
theorem weightLaplacian_im_cpow (k : ℝ) (s : ℂ) (z : ℍ) :
    weightLaplacian k (fun τ ↦ (τ.im : ℂ) ^ s) z = s * (1 - k - s) * (z.im : ℂ) ^ s := by
  set φ' : ℝ → ℂ := fun t ↦ s * (t : ℂ) ^ (s - 1)
  set G : ℂ → ℂ := fun w ↦ (w.im : ℂ) ^ s
  have hy : (z.im : ℂ) ≠ 0 := ofReal_ne_zero.2 z.im_ne_zero
  -- `G` is a function of `Im w`, with derivative `φ'` in the variable `t = Im w`.
  have hG (w : ℂ) (hw : 0 < w.im) : HasFDerivAt G (imCLM.smulRight (φ' w.im)) w := by
    have h := ((hasDerivAt_id (w.im : ℂ)).cpow_const (c := s)
      (ofReal_mem_slitPlane.2 hw)).comp_ofReal
    simp only [id, mul_one] at h
    exact h.hasFDerivAt_comp_im
  have hφ' : HasDerivAt φ' (s * ((s - 1) * (z.im : ℂ) ^ (s - 1 - 1))) z.im := by
    have h := ((hasDerivAt_id (z.im : ℂ)).cpow_const (c := s - 1)
      (ofReal_mem_slitPlane.2 z.im_pos)).comp_ofReal
    simp only [id, mul_one] at h
    exact h.const_mul s
  have hGev : fderiv ℝ G =ᶠ[𝓝 (z : ℂ)] fun w ↦ imCLM.smulRight (φ' w.im) := by
    have hpos : ∀ᶠ w in 𝓝 (z : ℂ), 0 < w.im :=
      Complex.continuous_im.continuousAt.eventually (lt_mem_nhds z.im_pos)
    filter_upwards [hpos] with w hw
    exact (hG w hw).fderiv
  have hcont : ContDiffAt ℝ 2 G z := by
    have hpow : ContDiffAt ℂ 2 (fun u : ℂ ↦ u ^ s) (z.im : ℂ) :=
      (analyticAt_id.cpow analyticAt_const (ofReal_mem_slitPlane.2 z.im_pos)).contDiffAt
    exact (hpow.restrict_scalars ℝ).comp (z : ℂ) (ofRealCLM.comp imCLM).contDiff.contDiffAt
  have hD1 : (fun w ↦ fderiv ℝ G w 1) =ᶠ[𝓝 (z : ℂ)] fun _ ↦ 0 :=
    hGev.mono fun w hw ↦ by simp [hw]
  have hDI : (fun w ↦ fderiv ℝ G w I) =ᶠ[𝓝 (z : ℂ)] fun w ↦ φ' w.im :=
    hGev.mono fun w hw ↦ by simp [hw]
  have hΔ : Δ G z = s * ((s - 1) * (z.im : ℂ) ^ (s - 1 - 1)) := by
    rw [laplacian_eq_fderiv_fderiv_apply_one_add_fderiv_fderiv_apply_I
      ((hcont.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)),
      hD1.fderiv_eq, hDI.fderiv_eq, hφ'.hasFDerivAt_comp_im.fderiv]
    simp
  have hev := im_cpow_comp_ofComplex_eventuallyEq s z
  rw [weightLaplacian_eq_fderiv, hyperbolicLaplacian_apply,
    (laplacian_congr_nhds hev).self_of_nhds, hev.fderiv_eq, hΔ, hGev.self_of_nhds]
  simp only [ContinuousLinearMap.smulRight_apply, imCLM_apply, one_im, Complex.I_im,
    zero_smul, one_smul, zero_add, coe_im, φ']
  rw [cpow_sub _ _ hy, cpow_sub _ _ hy, cpow_one]
  field_simp
  linear_combination (s * (z.im : ℂ) ^ s * k) * I_sq

/-- **The power law for the hyperbolic Laplacian**: `Δ y^s = s (1 - s) y^s` for every complex
`s`. -/
theorem hyperbolicLaplacian_im_cpow (s : ℂ) (z : ℍ) :
    hyperbolicLaplacian (fun τ ↦ (τ.im : ℂ) ^ s) z = s * (1 - s) * (z.im : ℂ) ^ s := by
  simpa using weightLaplacian_im_cpow 0 s z

end Power

section Slash

variable {g : GL (Fin 2) ℝ}

/-- The Möbius transformation read through `ofComplex` sends a point of `ℍ` to its image. -/
private theorem coe_smul_ofComplex_coe (z : ℍ) :
    ((g • ofComplex (z : ℂ) : ℍ) : ℂ) = ((g • z : ℍ) : ℂ) := by
  rw [ofComplex_apply]

/-- The squared norm of the derivative `det g / (cz + d)²` of the Möbius transformation read
through `ofComplex`. -/
private theorem norm_deriv_coe_smul_ofComplex_sq (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (z : ℍ) :
    ‖deriv (fun w ↦ ((g • ofComplex w : ℍ) : ℂ)) z‖ ^ 2 =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det / normSq (denom g z)) ^ 2 := by
  rw [deriv_smul hg z, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hg.le,
    ← Complex.normSq_eq_norm_sq]

/-- **Möbius invariance of the hyperbolic Laplacian**: for `g ∈ GL(2, ℝ)` with positive
determinant, `Δ (f ∘ g) = (Δ f) ∘ g` at every point where `f` is `C²`. -/
theorem hyperbolicLaplacian_comp_smul (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    {f : ℍ → ℂ} {z : ℍ} (hf : ContDiffAt ℝ 2 (f ∘ ofComplex) (g • z : ℍ)) :
    hyperbolicLaplacian (fun τ ↦ f (g • τ)) z = hyperbolicLaplacian f (g • z) := by
  rw [hyperbolicLaplacian_apply, hyperbolicLaplacian_apply,
    ← comp_ofComplex_comp_coe_smul_ofComplex, laplacian_comp_eq_norm_deriv_sq_smul
      ((coe_smul_ofComplex_coe z).symm ▸ hf) (analyticAt_smul hg z).contDiffAt,
    coe_smul_ofComplex_coe, norm_deriv_coe_smul_ofComplex_sq hg, im_smul_eq_div_normSq,
    abs_of_pos (by simpa using hg)]
  have := denom_ne_zero g z
  rw [Complex.real_smul, Matrix.GeneralLinearGroup.val_det_apply]
  push_cast
  field_simp

/-- The first-order coefficients in `Δ_k (f ∣[k] g)` match those of `(Δ_k f) ∣[k] g`: with
`D = cz + d`, the derivative `det g / D²` of the Möbius transformation and the derivative
`-k c D^(-k - 1)` of the automorphy factor combine through `D - conj D = 2 i c y`. -/
private theorem slash_firstOrder_coeff (k : ℤ) (z : ℍ) :
    -(z.im : ℂ) ^ 2 * 2 * (-(k : ℂ) * (g 1 0 : ℂ) * (denom g z)⁻¹) *
        ((g : Matrix (Fin 2) (Fin 2) ℝ).det / (starRingEnd ℂ) (denom g z) ^ 2) +
      I * k * z.im * ((g : Matrix (Fin 2) (Fin 2) ℝ).det / (starRingEnd ℂ) (denom g z) ^ 2) =
      I * k * ((g : Matrix (Fin 2) (Fin 2) ℝ).det * z.im /
        (denom g z * (starRingEnd ℂ) (denom g z))) := by
  have hD : denom g z ≠ 0 := denom_ne_zero g z
  have hDc : (starRingEnd ℂ) (denom g z) ≠ 0 := (map_ne_zero _).2 hD
  have hy : (z.im : ℂ) ≠ 0 := ofReal_ne_zero.2 z.im_ne_zero
  have hrel : denom g z - (starRingEnd ℂ) (denom g z) = 2 * I * (g 1 0 : ℂ) * z.im := by
    rw [denom, map_add, map_mul, conj_ofReal, conj_ofReal, add_sub_add_right_eq_sub, ← mul_sub,
      sub_conj, coe_im]
    push_cast
    ring
  field_simp
  linear_combination ((k : ℂ) * (g : Matrix (Fin 2) (Fin 2) ℝ).det * I) * hrel +
    (2 * (k : ℂ) * (g : Matrix (Fin 2) (Fin 2) ℝ).det * (g 1 0 : ℂ) * z.im) * I_sq

/-- **The weight-`k` Laplacian commutes with the weight-`k` slash action** of every
`g ∈ GL(2, ℝ)` with positive determinant: for an integral weight `k`,
`Δ_k (f ∣[k] g) = (Δ_k f) ∣[k] g` at every point where `f` is `C²`. -/
theorem weightLaplacian_slash (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det) (k : ℤ)
    {f : ℍ → ℂ} {z : ℍ} (hf : ContDiffAt ℝ 2 (f ∘ ofComplex) (g • z : ℍ)) :
    weightLaplacian k (f ∣[k] g) z = (weightLaplacian k f ∣[k] g) z := by
  set m : ℂ → ℂ := fun w ↦ ((g • ofComplex w : ℍ) : ℂ)
  set J : ℂ → ℂ := fun w ↦ ((|g.det.val| : ℝ) : ℂ) ^ (k - 1) * denom g w ^ (-k)
  -- Both sides are linear in `A = Δ (f ∘ ofComplex)` and `B = \bar∂(f ∘ ofComplex)` at `g • z`.
  set A := Δ (f ∘ ofComplex) ((g • z : ℍ) : ℂ)
  set B := conjWirtingerDeriv (f ∘ ofComplex) ((g • z : ℍ) : ℂ) 1
  have hm : AnalyticAt ℂ m z := analyticAt_smul hg z
  have hmz : m z = ((g • z : ℍ) : ℂ) := coe_smul_ofComplex_coe z
  have hFm : ContDiffAt ℝ 2 (f ∘ ofComplex) (m z) := hmz ▸ hf
  have hJ : ContDiffAt ℂ 2 J z := by
    refine (analyticAt_const.mul (AnalyticAt.zpow ?_ (denom_ne_zero g z))).contDiffAt
    unfold denom
    fun_prop
  have hH : ContDiffAt ℝ 2 ((f ∘ ofComplex) ∘ m) z :=
    hFm.comp _ (hm.contDiffAt.restrict_scalars ℝ)
  have hev := ModularForm.slash_comp_ofComplex_eventuallyEq hg k f z
  -- The left side: the product rule for the holomorphic factor `J`, then the conformal
  -- covariance of `Δ` and `\bar∂` under `m`.
  have hL : weightLaplacian k (f ∣[k] g) z =
      -(z.im : ℂ) ^ 2 * (J z * (‖deriv m z‖ ^ 2 • A) +
        4 * deriv J z * ((starRingEnd ℂ) (deriv m z) * B)) +
      2 * I * ((k : ℝ) : ℂ) * z.im * (J z * ((starRingEnd ℂ) (deriv m z) * B)) := by
    rw [weightLaplacian_apply, hyperbolicLaplacian_apply, (laplacian_congr_nhds hev).self_of_nhds,
      hev.conjWirtingerDeriv_eq, conjWirtingerDeriv_fun_mul
        ((hJ.restrict_scalars ℝ).differentiableAt (by norm_num))
        (hH.differentiableAt (by norm_num)),
      (hJ.differentiableAt (by norm_num)).conjWirtingerDeriv_eq_zero,
      laplacian_fun_mul_eq_mul_laplacian_add_deriv_mul_conjWirtingerDeriv hJ hH,
      conjWirtingerDeriv_comp_eq_conj_smul (hFm.differentiableAt (by norm_num))
        hm.differentiableAt.hasDerivAt,
      laplacian_comp_eq_norm_deriv_sq_smul hFm hm.contDiffAt, hmz]
    simp only [smul_apply, smul_zero, smul_eq_mul, add_zero, A, B]
  -- The right side: the slash of `Δ_k f`, with `Im (g • z) = det g · Im z / |cz + d|²`.
  have hR : (weightLaplacian k f ∣[k] g) z =
      J z * (-(((g • z : ℍ).im : ℂ) ^ 2) * A + 2 * I * ((k : ℝ) : ℂ) * (g • z : ℍ).im * B) := by
    rw [ModularForm.slash_apply, σ_eq_refl_of_det_pos hg, weightLaplacian_apply,
      hyperbolicLaplacian_apply, ContinuousAlgEquiv.refl_apply]
    simp only [J]
    ring
  have hdJ : deriv J z = ((|g.det.val| : ℝ) : ℂ) ^ (k - 1) *
      ((-k : ℤ) * g 1 0 * denom g z ^ (-k - 1)) :=
    ((hasDerivAt_denom_zpow g (-k) z).const_mul _).deriv
  rw [hL, hR, norm_deriv_coe_smul_ofComplex_sq hg, deriv_smul hg z, hdJ, im_smul_eq_div_normSq]
  simp only [Matrix.GeneralLinearGroup.val_det_apply, abs_of_pos hg, J,
    zpow_sub_one₀ (denom_ne_zero g z), map_div₀, map_pow, conj_ofReal, Complex.real_smul]
  push_cast
  rw [← mul_conj]
  linear_combination
    (2 * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 1) * denom g z ^ (-k) * B) *
      slash_firstOrder_coeff (g := g) k z

end Slash

end TauCeti.UpperHalfPlane
