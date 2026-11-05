/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Complex.CauchyKernel

/-!
# The Cauchy transform with parameters

For a compactly supported `C¹` map `f : ℂ → F` into a complex Banach space, the Cauchy transform
`T f w = π⁻¹ ∫ (w - z)⁻¹ • f z` solves the inhomogeneous Cauchy–Riemann equation
`\bar∂ (T f) = f` on the whole plane and is holomorphic off the support of `f`
(`TauCeti.Analysis.Complex.Pompeiu.Basic`). This file studies the transform when `f` depends
on parameters, as needed to solve `\bar∂ u = f` with smooth or holomorphic dependence on
parameters. Normalizing constants play no role in regularity, so the statements are about the
unnormalized integral `∫ (w - z)⁻¹ • f z`.

* Let `g : P → ℂ → F` be jointly `C^n` on `s ×ˢ univ`, for an open set `s` of a real normed space
  `P`, with `g p z = 0` for `p ∈ s` and `z` outside a fixed compact set `k`. The transform
  `(p, w) ↦ ∫ (w - z)⁻¹ • g p z` is jointly `C^n` on `s ×ˢ univ`: this is smoothness of the
  convolution of the locally integrable Cauchy kernel with a compactly supported family, after the
  substitution `ζ = w - z`. Its derivative in `p` is the transform of the derivative of `g` in `p`,
  so every parameter derivative commutes with the transform. By
  `TauCeti.differentiableOn_integral_sub_inv_smul_compl`, for every `p ∈ s` the transform of
  `g p` is holomorphic off `k`, a region that does not depend on `p`.
* When the parameter space `Q` is complex, the conjugate Wirtinger derivative in `q` commutes with
  the transform. In particular, if `g q z` is holomorphic in `q` for every `z`, so is the
  transform of `g q` at every point `w`.
* Cut off a family `f`, jointly `C^n` on `s ×ˢ U` for an open set `U ⊆ ℂ`, by a fixed smooth
  function of the plane variable which equals `1` near a compact set `K ⊆ U`. Its normalized
  transform is a family `u`, jointly `C^n` on `s ×ˢ univ`, with `\bar∂ (u p) = f p` near `K` for
  every parameter `p ∈ s`. The cutoff does not depend on the parameter, so `s` need not be
  shrunk, and `u` is holomorphic in those parameters in which `f` is. This is the one-variable
  step of the `\bar∂`-Poincaré lemma on polydiscs, which solves in one conjugate variable while
  keeping smooth dependence on some of the other variables and holomorphic dependence on the
  rest.

## Main results

* `TauCeti.contDiffOn_integral_sub_inv_smul_with_param`: joint smoothness in the parameter and the
  point.
* `TauCeti.hasFDerivAt_integral_sub_inv_smul_with_param`: parameter derivatives commute with the
  transform.
* `TauCeti.conjWirtingerDeriv_integral_sub_inv_smul_with_param` and
  `TauCeti.differentiableAt_integral_sub_inv_smul_with_param`: the conjugate Wirtinger derivative
  in a complex parameter commutes with the transform, which preserves holomorphy in parameters.
* `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_with_param`: local solutions of
  `\bar∂ u = f` depending smoothly on parameters.
* `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_with_holomorphic_param`: local
  solutions depending smoothly on some parameters and holomorphically on the others.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.2.2.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0,
  §§1–2 (the `\bar∂`-Poincaré lemma in one and in several variables, where the solution depends
  holomorphically on the remaining variables).
-/

public section

open MeasureTheory Complex Set Filter
open scoped Real Topology Convolution

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ### Smooth dependence on parameters -/

section Parameter

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {g : P → ℂ → F} {s : Set P}
  {k : Set ℂ}

/-- **Joint smoothness of the Cauchy transform in parameters.** If `g` is `C^n` on `s ×ˢ univ`
for an open set `s` of parameters, and `g p` vanishes outside a fixed compact set `k` for every
`p ∈ s`, then `(p, w) ↦ ∫ (w - z)⁻¹ • g p z` is `C^n` on `s ×ˢ univ`. -/
theorem contDiffOn_integral_sub_inv_smul_with_param {n : ℕ∞} (hs : IsOpen s) (hk : IsCompact k)
    (hgs : ∀ p x, p ∈ s → x ∉ k → g p x = 0) (hg : ContDiffOn ℝ n ↿g (s ×ˢ univ)) :
    ContDiffOn ℝ n (fun q : P × ℂ ↦ ∫ z, (q.2 - z)⁻¹ • g q.1 z) (s ×ˢ univ) := by
  refine (contDiffOn_convolution_right_with_param (μ := volume)
    (ContinuousLinearMap.lsmul ℝ ℂ) hs hk hgs Complex.locallyIntegrable_inv hg).congr
      fun q _ ↦ ?_
  simp only [convolution_eq_swap, ContinuousLinearMap.lsmul_apply]

/-- The derivative of `g` on `s ×ˢ univ`, multiplied by the Cauchy kernel at `w`, is integrable
in the space variable, for `p ∈ s`. -/
private theorem integrable_sub_inv_smul_fderiv_uncurry (hs : IsOpen s) (hk : IsCompact k)
    (hgs : ∀ p x, p ∈ s → x ∉ k → g p x = 0) (hg : ContDiffOn ℝ 1 ↿g (s ×ˢ univ)) {p : P}
    (hp : p ∈ s) (w : ℂ) :
    Integrable fun z ↦ (w - z)⁻¹ • fderiv ℝ ↿g (p, z) := by
  have hopen : IsOpen (s ×ˢ (univ : Set ℂ)) := hs.prod isOpen_univ
  refine (Complex.locallyIntegrable_sub_inv w).integrable_smul_right_of_hasCompactSupport ?_ ?_
  · exact (hg.continuousOn_fderiv_of_isOpen hopen le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) fun z ↦ ⟨hp, mem_univ z⟩
  · refine HasCompactSupport.intro hk fun z hz ↦ ?_
    -- Near `(p, z)` the family vanishes, since `s ×ˢ kᶜ` is a neighbourhood of `(p, z)`.
    refine (hasFDerivAt_zero_of_eventually_const 0 ?_).fderiv
    filter_upwards [(hs.prod hk.isClosed.isOpen_compl).mem_nhds (mk_mem_prod hp hz)] with q hq
    exact hgs q.1 q.2 hq.1 hq.2

/-- On `s ×ˢ univ`, the derivative of `g` in the parameter is the derivative of `↿g` restricted to
`P × {0}`: `fderiv_slice_left` under the hypotheses of this section. -/
private theorem fderiv_slice_eq_fderiv_uncurry_comp_inl (hs : IsOpen s)
    (hg : ContDiffOn ℝ 1 ↿g (s ×ˢ univ)) {p : P} (hp : p ∈ s) (z : ℂ) :
    fderiv ℝ (fun p ↦ g p z) p = (fderiv ℝ ↿g (p, z)).comp (ContinuousLinearMap.inl ℝ P ℂ) :=
  fderiv_slice_left ((hg.differentiableOn one_ne_zero).differentiableAt
    ((hs.prod isOpen_univ).mem_nhds (mk_mem_prod hp (mem_univ z))))

/-- The derivative of `g` in the parameter, multiplied by the Cauchy kernel at `w`, is integrable
in the space variable, for `p ∈ s`. -/
private theorem integrable_sub_inv_smul_fderiv_slice (hs : IsOpen s) (hk : IsCompact k)
    (hgs : ∀ p x, p ∈ s → x ∉ k → g p x = 0) (hg : ContDiffOn ℝ 1 ↿g (s ×ˢ univ)) {p : P}
    (hp : p ∈ s) (w : ℂ) :
    Integrable fun z ↦ (w - z)⁻¹ • fderiv ℝ (fun p ↦ g p z) p := by
  have h := ((ContinuousLinearMap.compL ℝ P (P × ℂ) F).flip
    (ContinuousLinearMap.inl ℝ P ℂ)).integrable_comp
      (integrable_sub_inv_smul_fderiv_uncurry hs hk hgs hg hp w)
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.smul_comp,
    ← fderiv_slice_eq_fderiv_uncurry_comp_inl hs hg hp] using h

/-- **Parameter derivatives commute with the Cauchy transform.** Under the hypotheses of
`TauCeti.contDiffOn_integral_sub_inv_smul_with_param` with `n = 1`, the derivative in `p ∈ s` of
`∫ (w - z)⁻¹ • g p z` is the transform `∫ (w - z)⁻¹ • D_p g p z` of the derivative of `g` in
`p`. -/
theorem hasFDerivAt_integral_sub_inv_smul_with_param [CompleteSpace F] (hs : IsOpen s)
    (hk : IsCompact k) (hgs : ∀ p x, p ∈ s → x ∉ k → g p x = 0)
    (hg : ContDiffOn ℝ 1 ↿g (s ×ˢ univ)) {p : P} (hp : p ∈ s) (w : ℂ) :
    HasFDerivAt (fun p ↦ ∫ z, (w - z)⁻¹ • g p z)
      (∫ z, (w - z)⁻¹ • fderiv ℝ (fun p ↦ g p z) p) p := by
  -- Mathlib's joint derivative of the convolution, restricted to the slice `w` fixed.
  have hjoint := (hasFDerivAt_convolution_right_with_param (μ := volume)
    (ContinuousLinearMap.lsmul ℝ ℂ) hs hk hgs Complex.locallyIntegrable_inv hg (p, w) hp).comp p
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) p w)
  refine (hjoint.congr_of_eventuallyEq (.of_forall fun p' ↦ ?_)).congr_fderiv ?_
  · simp only [Function.comp_apply, convolution_eq_swap, ContinuousLinearMap.lsmul_apply]
  -- Restriction to `P × {0}` is a continuous linear map, so it commutes with the integral.
  let R : (P × ℂ →L[ℝ] F) →L[ℝ] P →L[ℝ] F :=
    (ContinuousLinearMap.compL ℝ P (P × ℂ) F).flip (ContinuousLinearMap.inl ℝ P ℂ)
  have hR := R.integral_comp_comm (integrable_sub_inv_smul_fderiv_uncurry hs hk hgs hg hp w)
  simp only [R, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply] at hR
  have hL (t : ℂ) : ContinuousLinearMap.precompR (P × ℂ) (ContinuousLinearMap.lsmul ℝ ℂ)
      (w - t)⁻¹ (fderiv ℝ ↿g (p, t)) = (w - t)⁻¹ • fderiv ℝ ↿g (p, t) := by
    ext v <;> simp
  simp only [convolution_eq_swap, hL, ← hR, fderiv_slice_eq_fderiv_uncurry_comp_inl hs hg hp,
    ContinuousLinearMap.smul_comp]

end Parameter

/-! ### Holomorphic dependence on parameters -/

section Holomorphic

variable [CompleteSpace F] {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {g : Q → ℂ → F}
  {s : Set Q} {k : Set ℂ}

/-- **The conjugate Wirtinger derivative in a complex parameter commutes with the Cauchy
transform**: `\bar∂_q ∫ (w - z)⁻¹ • g q z = ∫ (w - z)⁻¹ • \bar∂_q g q z`, under the hypotheses of
`TauCeti.contDiffOn_integral_sub_inv_smul_with_param` with `n = 1`. -/
theorem conjWirtingerDeriv_integral_sub_inv_smul_with_param (hs : IsOpen s) (hk : IsCompact k)
    (hgs : ∀ q x, q ∈ s → x ∉ k → g q x = 0) (hg : ContDiffOn ℝ 1 ↿g (s ×ˢ univ)) {q : Q}
    (hq : q ∈ s) (w : ℂ) (v : Q) :
    conjWirtingerDeriv (fun q ↦ ∫ z, (w - z)⁻¹ • g q z) q v =
      ∫ z, (w - z)⁻¹ • conjWirtingerDeriv (fun q ↦ g q z) q v := by
  have hint := integrable_sub_inv_smul_fderiv_slice hs hk hgs hg hq w
  have hv (u : Q) := hint.apply_continuousLinearMap u
  have hI : Integrable fun z ↦ I • ((w - z)⁻¹ • fderiv ℝ (fun q ↦ g q z) q) (I • v) :=
    (hv _).smul I
  have hz (z : ℂ) : (w - z)⁻¹ • conjWirtingerDeriv (fun q ↦ g q z) q v =
      (2 : ℂ)⁻¹ • (((w - z)⁻¹ • fderiv ℝ (fun q ↦ g q z) q) v +
        I • ((w - z)⁻¹ • fderiv ℝ (fun q ↦ g q z) q) (I • v)) := by
    simp only [conjWirtingerDeriv_apply, FunLike.coe_smul, Pi.smul_apply]
    module
  rw [conjWirtingerDeriv_apply,
    (hasFDerivAt_integral_sub_inv_smul_with_param hs hk hgs hg hq w).fderiv,
    ContinuousLinearMap.integral_apply hint, ContinuousLinearMap.integral_apply hint,
    integral_congr_ae (.of_forall hz), integral_smul, integral_add (hv v) hI,
    integral_smul]

/-- **The Cauchy transform preserves holomorphy in parameters.** Under the hypotheses of
`TauCeti.contDiffOn_integral_sub_inv_smul_with_param` with `n = 1`, if `g q z` is complex
differentiable in `q` at a point `q ∈ s` for every `z`, then so is `∫ (w - z)⁻¹ • g q z`, for every
`w`. -/
theorem differentiableAt_integral_sub_inv_smul_with_param (hs : IsOpen s) (hk : IsCompact k)
    (hgs : ∀ q x, q ∈ s → x ∉ k → g q x = 0) (hg : ContDiffOn ℝ 1 ↿g (s ×ˢ univ)) {q : Q}
    (hq : q ∈ s) (hgq : ∀ z, DifferentiableAt ℂ (fun q ↦ g q z) q) (w : ℂ) :
    DifferentiableAt ℂ (fun q ↦ ∫ z, (w - z)⁻¹ • g q z) q := by
  rw [differentiableAt_iff_conjWirtingerDeriv_eq_zero
    (hasFDerivAt_integral_sub_inv_smul_with_param hs hk hgs hg hq w).differentiableAt]
  ext v
  simp [conjWirtingerDeriv_integral_sub_inv_smul_with_param hs hk hgs hg hq w v,
    (hgq _).conjWirtingerDeriv_eq_zero]

end Holomorphic

/-! ### Local solutions of `\bar∂ u = f` with parameters -/

section LocalSolution

variable {P : Type*} {χ : ℂ → ℝ} {U K : Set ℂ} {n : ℕ∞}

/-- The family `f` cut off by `χ` in the plane variable and divided by `π`, so that its Cauchy
transform `cutoffTransform χ f` solves `\bar∂ u = χ f`. -/
private noncomputable def cutoffFamily (χ : ℂ → ℝ) (f : P → ℂ → F) (p : P) (z : ℂ) : F :=
  ((π : ℂ)⁻¹ * χ z) • f p z

/-- The Cauchy transform `w ↦ ∫ (w - z)⁻¹ • π⁻¹ χ z f p z` of the cut-off family. -/
private noncomputable def cutoffTransform (χ : ℂ → ℝ) (f : P → ℂ → F) (p : P) (w : ℂ) : F :=
  ∫ z, (w - z)⁻¹ • cutoffFamily χ f p z

/-- The cut-off family vanishes off the support of `χ`. -/
private theorem cutoffFamily_eq_zero (f : P → ℂ → F) (p : P) {z : ℂ} (hz : z ∉ tsupport χ) :
    cutoffFamily χ f p z = 0 := by
  simp [cutoffFamily, image_eq_zero_of_notMem_tsupport hz]

variable [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The cut-off family is jointly `Cⁿ` in the parameter and the point, over the whole plane. -/
private theorem contDiffOn_cutoffFamily {f : P → ℂ → F} {s : Set P} (hs : IsOpen s)
    (hU : IsOpen U) (hχ : ContDiff ℝ n χ) (hχU : tsupport χ ⊆ U)
    (hf : ContDiffOn ℝ n ↿f (s ×ˢ U)) :
    ContDiffOn ℝ n ↿(cutoffFamily χ f) (s ×ˢ univ) := by
  rintro ⟨p, z⟩ ⟨hp, -⟩
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases hz : z ∈ tsupport χ
  · have hc : ContDiff ℝ n fun x : P × ℂ ↦ (π : ℂ)⁻¹ * (χ x.2 : ℂ) :=
      contDiff_const.mul (ofRealCLM.contDiff.comp (hχ.comp contDiff_snd))
    exact hc.contDiffAt.smul (hf.contDiffAt ((hs.prod hU).mem_nhds (mk_mem_prod hp (hχU hz))))
  · -- Off the support of `χ`, the family vanishes near `(p, z)`.
    refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_univ.prod (isClosed_tsupport χ).isOpen_compl).mem_nhds
      (mk_mem_prod (mem_univ p) hz)] with x hx
    exact cutoffFamily_eq_zero f x.1 hx.2

/-- The cut-off transform is jointly `Cⁿ` in the parameter and the point. -/
private theorem contDiffOn_cutoffTransform {f : P → ℂ → F} {s : Set P} (hs : IsOpen s)
    (hU : IsOpen U) (hχ : ContDiff ℝ n χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (hf : ContDiffOn ℝ n ↿f (s ×ˢ U)) :
    ContDiffOn ℝ n ↿(cutoffTransform χ f) (s ×ˢ univ) :=
  contDiffOn_integral_sub_inv_smul_with_param hs hχc.isCompact
    (fun p _ _ hz ↦ cutoffFamily_eq_zero f p hz) (contDiffOn_cutoffFamily hs hU hχ hχU hf)

variable [CompleteSpace F]

/-- The cut-off transform solves `\bar∂ u = χ f`. -/
private theorem conjWirtingerDeriv_cutoffTransform {f : P → ℂ → F} {s : Set P} (hn : 1 ≤ n)
    (hs : IsOpen s) (hU : IsOpen U) (hχ : ContDiff ℝ n χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ U) (hf : ContDiffOn ℝ n ↿f (s ×ˢ U)) {p : P} (hp : p ∈ s) (w : ℂ) :
    conjWirtingerDeriv (cutoffTransform χ f p) w 1 = (χ w : ℂ) • f p w := by
  have hg : ContDiff ℝ 1 (cutoffFamily χ f p) :=
    ((contDiffOn_cutoffFamily hs hU hχ hχU hf).comp_contDiff (contDiff_const.prodMk contDiff_id)
      fun z ↦ mk_mem_prod hp (mem_univ z)).of_le (by exact_mod_cast hn)
  have hc : HasCompactSupport (cutoffFamily χ f p) :=
    .intro hχc.isCompact fun z hz ↦ cutoffFamily_eq_zero f p hz
  unfold cutoffTransform
  rw [hc.conjWirtingerDeriv_integral_sub_inv_smul_apply_one hg, cutoffFamily, smul_smul,
    ← mul_assoc, mul_inv_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero), one_mul]

/-- The cut-off transform of a family holomorphic in a complex parameter is holomorphic in that
parameter. -/
private theorem differentiableAt_cutoffTransform {Q : Type*} [NormedAddCommGroup Q]
    [NormedSpace ℂ Q] {f : Q → ℂ → F} {s : Set Q} (hn : 1 ≤ n) (hs : IsOpen s) (hU : IsOpen U)
    (hχ : ContDiff ℝ n χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (hf : ContDiffOn ℝ n ↿f (s ×ˢ U))
    (hfq : ∀ q ∈ s, ∀ z ∈ U, DifferentiableAt ℂ (fun q ↦ f q z) q) {q : Q} (hq : q ∈ s)
    (w : ℂ) :
    DifferentiableAt ℂ (fun q ↦ cutoffTransform χ f q w) q := by
  refine differentiableAt_integral_sub_inv_smul_with_param hs hχc.isCompact
    (fun q _ _ hz ↦ cutoffFamily_eq_zero f q hz)
    ((contDiffOn_cutoffFamily hs hU hχ hχU hf).of_le (by exact_mod_cast hn)) hq (fun z ↦ ?_) w
  by_cases hz : z ∈ tsupport χ
  · exact (hfq q hq z (hχU hz)).const_smul _
  · exact (differentiableAt_const (0 : F)).congr_of_eventuallyEq
      (.of_forall fun q ↦ cutoffFamily_eq_zero f q hz)

/-- **Local solutions of `\bar∂ u = f` with smooth parameters.** Let `f` be a family of maps
`ℂ → F` which is jointly `Cⁿ`, `1 ≤ n`, on `s ×ˢ U` for an open set `s` of parameters and an
open set `U ⊆ ℂ`, and let `K ⊆ U` be compact. Then some family `u`, jointly `Cⁿ` on `s ×ˢ univ`,
satisfies `\bar∂ (u p) = f p` near `K` for every `p ∈ s`, on a neighbourhood of `K` independent
of `p`. No shrinking of the parameter domain is needed. -/
theorem exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_with_param {f : P → ℂ → F}
    {s : Set P} (hn : 1 ≤ n) (hs : IsOpen s) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ n ↿f (s ×ˢ U)) :
    ∃ u : P → ℂ → F, ContDiffOn ℝ n ↿u (s ×ˢ univ) ∧
      ∀ᶠ z in 𝓝ˢ K, ∀ p ∈ s, conjWirtingerDeriv (u p) z 1 = f p z := by
  obtain ⟨χ, hχ, -, hχK, hχc, hχU⟩ := hK.exists_contDiff_cutoff hU hKU
  have hχn : ContDiff ℝ n χ := hχ.of_le (by exact_mod_cast le_top)
  refine ⟨cutoffTransform χ f, contDiffOn_cutoffTransform hs hU hχn hχc hχU hf, ?_⟩
  filter_upwards [isOpen_interior.mem_nhdsSet.mpr hχK] with z hz p hp
  have hz1 : χ z = 1 := interior_subset hz
  simp [conjWirtingerDeriv_cutoffTransform hn hs hU hχn hχc hχU hf hp, hz1]

/-- **Local solutions of `\bar∂ u = f` with smooth and holomorphic parameters.** Let `f` be a
family of maps `ℂ → F` indexed by `P × Q`, for a real normed space `P` and a complex normed space
`Q`, which is jointly `Cⁿ`, `1 ≤ n`, on `s ×ˢ U` for an open set `s ⊆ P × Q` and an open set
`U ⊆ ℂ`, and holomorphic in `q ∈ Q` at every point of `s ×ˢ U`. Let `K ⊆ U` be compact. Then some
family `u`, jointly `Cⁿ` on `s ×ˢ univ`, satisfies `\bar∂ (u x) = f x` near `K` for every `x ∈ s`,
on a neighbourhood of `K` independent of `x`, and is holomorphic in `q` on `s` at every point of
the plane. -/
theorem exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_with_holomorphic_param {Q : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℂ Q] {f : P × Q → ℂ → F} {s : Set (P × Q)} (hn : 1 ≤ n)
    (hs : IsOpen s) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ n ↿f (s ×ˢ U))
    (hfq : ∀ x ∈ s, ∀ z ∈ U, DifferentiableAt ℂ (fun q ↦ f (x.1, q) z) x.2) :
    ∃ u : P × Q → ℂ → F, ContDiffOn ℝ n ↿u (s ×ˢ univ) ∧
      (∀ᶠ z in 𝓝ˢ K, ∀ x ∈ s, conjWirtingerDeriv (u x) z 1 = f x z) ∧
      ∀ x ∈ s, ∀ w, DifferentiableAt ℂ (fun q ↦ u (x.1, q) w) x.2 := by
  obtain ⟨χ, hχ, -, hχK, hχc, hχU⟩ := hK.exists_contDiff_cutoff hU hKU
  have hχn : ContDiff ℝ n χ := hχ.of_le (by exact_mod_cast le_top)
  refine ⟨cutoffTransform χ f, contDiffOn_cutoffTransform hs hU hχn hχc hχU hf, ?_, ?_⟩
  · filter_upwards [isOpen_interior.mem_nhdsSet.mpr hχK] with z hz x hx
    have hz1 : χ z = 1 := interior_subset hz
    simp [conjWirtingerDeriv_cutoffTransform hn hs hU hχn hχc hχU hf hx, hz1]
  · -- Freeze the smooth parameter `p` and apply the holomorphic statement to the slice.
    rintro ⟨p, q⟩ hx w
    have hι : ContDiff ℝ n fun y : Q × ℂ ↦ ((p, y.1), y.2) :=
      (contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd
    exact differentiableAt_cutoffTransform (f := fun q z ↦ f (p, q) z) hn
      (hs.preimage (Continuous.prodMk_right p)) hU hχn hχc hχU
      (hf.comp hι.contDiffOn fun y hy ↦ mk_mem_prod hy.1 hy.2)
      (fun q hq z hz ↦ hfq (p, q) hq z hz) hx w

end LocalSolution

end TauCeti
