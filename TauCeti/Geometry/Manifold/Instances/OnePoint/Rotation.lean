/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Moebius
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.SpecialUnitary
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine
import TauCeti.Topology.FiberBundle.Separation

/-!
# The Möbius transformations preserving the Fubini–Study form

The Möbius transformations `z ↦ (a * z + b) / (c * z + d)` of the Riemann sphere `OnePoint ℂ` are
smooth maps of the underlying real surface. This file determines which of them preserve the
Fubini–Study form `ω_FS` (`OnePoint.fubiniStudyForm`): for `A ∈ SL(2, ℂ)`, the transformation of
`A` pulls `ω_FS` back to itself exactly when `A` is unitary
(`OnePoint.mpullback_smul_fubiniStudyForm_eq_self_iff_mem_unitaryGroup`). Passing to
`PSL(2, ℂ) = SL(2, ℂ) ⧸ {±1}`, the Möbius transformations preserving `ω_FS` are exactly the
elements of the projective special unitary group `PSU(2)`, the range of
`Matrix.specialUnitaryGroup.toPSL`
(`OnePoint.mpullback_smul_fubiniStudyForm_eq_self_iff_mem_range_toPSL`). Classically `PSU(2)` is
the rotation group of the round sphere; the comparison with the round metric is not made here.

In the affine coordinate the transformation of `A = !![a, b; c, d]` has derivative
`det A / (c * z + d) ^ 2` (`OnePoint.mfderiv_smul_coe_apply`). Writing `ρ(z) = 1 / (π (1 + |z|²)²)`
for the density of `ω_FS`, the pullback of `ω_FS` therefore has density
`1 / (π (|a z + b|² + |c z + d|²)²)` when `det A = 1`. It agrees with `ρ` exactly when
`|a z + b|² + |c z + d|² = |z|² + 1` for every `z`, that is, when `A` preserves the Hermitian
norm of the vectors `(z, 1)`. Comparing coefficients, this says that the columns of `A` are
orthonormal. The identity is checked at the finite points that are not sent to `∞`; they are
dense in the sphere, and two smooth forms agreeing on a dense set are equal.

## Main declarations

* `OnePoint.instContMDiffConstSMulGLReal`, `OnePoint.instContMDiffConstSMulPSLReal`: `GL(2, ℂ)`
  and `PSL(2, ℂ)` act on the Riemann sphere by smooth maps of the underlying real surface.
* `OnePoint.mfderiv_smul_coe_apply`: the derivative of a Möbius transformation in the affine
  coordinate.
* `OnePoint.mpullback_smul_fubiniStudyForm_eq_self_iff_mem_unitaryGroup`: an element of
  `SL(2, ℂ)` preserves the Fubini–Study form exactly when it is unitary.
* `OnePoint.mpullback_smul_fubiniStudyForm_eq_self_iff_mem_range_toPSL`: an element of
  `PSL(2, ℂ)` preserves the Fubini–Study form exactly when it lies in `PSU(2)`.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0,
  Section 2 (the Fubini–Study metric and its invariance under the unitary group).
* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer,
  1983, Chapter 4 (complex Möbius transformations and the unitary subgroup).
-/

public section

open Set Filter Function Bundle ComplexConjugate TauCeti
open scoped Manifold Topology TauCeti.ComplexManifold MatrixGroups ContDiff

noncomputable section

namespace OnePoint

/-! ### Möbius transformations as smooth maps of the real surface -/

/-- `GL(2, ℂ)` acts on the Riemann sphere, regarded as a real surface, by smooth (indeed
real-analytic) maps: each Möbius transformation is holomorphic. -/
instance instContMDiffConstSMulGLReal {n : WithTop ℕ∞} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n (GL (Fin 2) ℂ) (OnePoint ℂ) where
  contMDiff_const_smul g := by
    simpa only [modelWithCornersSelf_restrictScalars] using
      ((contMDiff_const_smul (I := 𝓘(ℂ)) (n := ω) g).restrictScalars ℝ).of_le le_top

/-- `PSL(2, ℂ)` acts on the Riemann sphere, regarded as a real surface, by smooth maps. -/
instance instContMDiffConstSMulPSLReal {n : WithTop ℕ∞} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n PSL(2, ℂ) (OnePoint ℂ) where
  contMDiff_const_smul g := by
    induction g using QuotientGroup.induction_on with
    | H A =>
      simpa only [pslMk_smul] using
        contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := n) (A : GL (Fin 2) ℂ)

/-- **The derivative of a Möbius transformation in the affine coordinate.** At a finite point `z`
which `g = !![a, b; c, d]` does not send to `∞`, the derivative of `g` on the Riemann sphere,
read in the affine charts, is multiplication by `det g / (c * z + d) ^ 2`. -/
theorem mfderiv_smul_coe_apply (g : GL (Fin 2) ℂ) {z : ℂ} (hz : g 1 0 * z + g 1 1 ≠ 0)
    (v : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • · : OnePoint ℂ → OnePoint ℂ) z v =
      (g : Matrix (Fin 2) (Fin 2) ℂ).det / (g 1 0 * z + g 1 1) ^ 2 * v := by
  -- Near `z`, the transformation read in the affine charts is `w ↦ (a w + b) / (c w + d)`.
  have hq : ContinuousAt (fun w : ℂ ↦ g 1 0 * w + g 1 1) z := by fun_prop
  have hev : (fun w : ℂ ↦ affineChart (g • (w : OnePoint ℂ)))
      =ᶠ[𝓝 z] fun w ↦ (g 0 0 * w + g 0 1) / (g 1 0 * w + g 1 1) := by
    filter_upwards [hq.eventually_ne hz] with w hw
    simp [smul_some_eq_ite, hw]
  have hd : HasDerivAt (fun w ↦ (g 0 0 * w + g 0 1) / (g 1 0 * w + g 1 1))
      ((g : Matrix (Fin 2) (Fin 2) ℂ).det / (g 1 0 * z + g 1 1) ^ 2) z := by
    refine ((((hasDerivAt_id' z).const_mul (g 0 0)).add_const (g 0 1)).div
      (((hasDerivAt_id' z).const_mul (g 1 0)).add_const (g 1 1)) hz).congr_deriv ?_
    rw [Matrix.det_fin_two]
    ring
  have hF := (hd.hasFDerivAt.restrictScalars ℝ).congr_of_eventuallyEq hev
  have hgz : g • (z : OnePoint ℂ) =
      (((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) : ℂ) : OnePoint ℂ) := by
    simp [smul_some_eq_ite, hz]
  have hmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • · : OnePoint ℂ → OnePoint ℂ) z :=
    (contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := 1) g).mdifferentiableAt one_ne_zero
  rw [hmd.mfderiv]
  simp only [writtenInExtChartAt, hgz, chartAt_coe, extChartAt, OpenPartialHomeomorph.extend,
    modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl,
    OpenPartialHomeomorph.coe_toPartialEquiv_symm, OpenPartialHomeomorph.coe_toPartialEquiv,
    affineChart_symm_apply, affineChart_coe, ModelWithCorners.range_eq_univ, fderivWithin_univ,
    Function.comp_def]
  rw [hF.fderiv]
  -- The casts `tangentSpaceCastModel` between the tangent spaces and `ℂ` are identities, and
  -- `toSpanSingleton ℂ c v = v * c`.
  exact mul_comm v _

/-! ### The pullback of the Fubini–Study form -/

/-- **The Fubini–Study form pulled back by a unimodular Möbius transformation**, at a finite point
`z` not sent to `∞`: it is `Im (conj v * w) / (π (|a z + b|² + |c z + d|²)²)`. -/
private theorem eval₂_mpullback_smul_coe (g : GL (Fin 2) ℂ)
    (hdet : (g : Matrix (Fin 2) (Fin 2) ℂ).det = 1) {z : ℂ} (hz : g 1 0 * z + g 1 1 ≠ 0)
    (v w : ℂ) :
    SmoothBundleForm.eval₂
        (SmoothForm.mpullback (g • ·) (contMDiff_const_smul g) fubiniStudyForm) (z : OnePoint ℂ)
        v w =
      (Real.pi * (‖g 0 0 * z + g 0 1‖ ^ 2 + ‖g 1 0 * z + g 1 1‖ ^ 2) ^ 2)⁻¹ *
        (conj v * w).im := by
  have hgz : g • (z : OnePoint ℂ) =
      (((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) : ℂ) : OnePoint ℂ) := by
    simp [smul_some_eq_ite, hz]
  -- Multiplying both vectors by `c` scales their area `Im (conj v * w)` by `|c|²`.
  have hscale (c v w : ℂ) : (conj (c * v) * (c * w)).im = ‖c‖ ^ 2 * (conj v * w).im := by
    rw [show conj (c * v) * (c * w) = (conj c * c) * (conj v * w) by simp; ring,
      Complex.conj_mul', ← Complex.ofReal_pow, Complex.im_ofReal_mul]
  refine (SmoothForm.eval₂_mpullback _ _ _ _ v w).trans ((eval₂_fubiniStudyForm _ _ _).trans ?_)
  rw [mfderiv_smul_coe_apply g hz, mfderiv_smul_coe_apply g hz, hscale, hgz, chartAt_coe,
    affineChart_coe, hdet, ← mul_assoc]
  congr 1
  -- With `P = |a z + b|` and `Q = |c z + d|`, this is `ρ(P / Q) / Q⁴ = 1 / (π (P² + Q²)²)`.
  rw [fubiniStudyDensity_def, norm_div, norm_div, norm_one, norm_pow]
  have hq : 0 < ‖g 1 0 * z + g 1 1‖ := norm_pos_iff.2 hz
  generalize ‖g 0 0 * z + g 0 1‖ = P
  generalize ‖g 1 0 * z + g 1 1‖ = Q at hq
  have hPQ : P ^ 2 + Q ^ 2 ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg P) (pow_pos hq 2)).ne'
  field_simp
  ring

/-- **Comparing coefficients.** A `2 × 2` complex matrix `!![a, b; c, d]` is unitary exactly when
`|a z + b|² + |c z + d|² = |z|² + 1` for every `z`, that is, when it preserves the Hermitian norm of
every vector `(z, 1)`. -/
private theorem forall_sq_norm_add_sq_norm_eq_iff_mem_unitaryGroup
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (∀ z : ℂ, ‖A 0 0 * z + A 0 1‖ ^ 2 + ‖A 1 0 * z + A 1 1‖ ^ 2 = ‖z‖ ^ 2 + 1) ↔
      A ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  -- Unitarity says that the columns `(a, c)` and `(b, d)` are orthonormal.
  rw [Matrix.mem_unitaryGroup_iff', ← Matrix.ext_iff]
  simp only [Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Complex.star_def, Matrix.one_apply_eq, ne_eq, zero_ne_one, not_false_eq_true,
    Matrix.one_apply_ne, one_ne_zero]
  -- In complex form the identity reads `(conj a conj z + conj b) (a z + b) + ⋯ = conj z z + 1`.
  have key (z : ℂ) : ‖A 0 0 * z + A 0 1‖ ^ 2 + ‖A 1 0 * z + A 1 1‖ ^ 2 = ‖z‖ ^ 2 + 1 ↔
      (conj (A 0 0) * conj z + conj (A 0 1)) * (A 0 0 * z + A 0 1) +
        (conj (A 1 0) * conj z + conj (A 1 1)) * (A 1 0 * z + A 1 1) = conj z * z + 1 := by
    rw [← Complex.ofReal_inj]
    push_cast
    simp only [← Complex.conj_mul', map_add, map_mul]
  simp only [key]
  generalize A 0 0 = a
  generalize A 0 1 = b
  generalize A 1 0 = c
  generalize A 1 1 = d
  constructor
  · -- Evaluate at `z = 0, 1, -1, i` and compare.
    intro h
    have h0 := h 0
    have h1 := h 1
    have hm1 := h (-1)
    have hI := h Complex.I
    simp only [map_zero, map_one, map_neg, Complex.conj_I, mul_zero, zero_add, mul_one,
      mul_neg] at h0 h1 hm1 hI
    have h01 : conj a * b + conj c * d = 0 := by
      linear_combination (h1 - hm1) / 4 + Complex.I / 2 * hI - Complex.I / 4 * (h1 + hm1) +
        ((conj a * b + conj c * d - conj b * a - conj d * c) / 2 +
          Complex.I / 2 * (conj a * a + conj c * c - 1)) * Complex.I_sq
    refine ⟨⟨by linear_combination (h1 + hm1) / 2 - h0, h01⟩, ?_, h0⟩
    simpa [mul_comm] using congrArg conj h01
  · rintro ⟨⟨h00, h01⟩, h10, h11⟩ z
    linear_combination (conj z * z) * h00 + conj z * h01 + z * h10 + h11

/-- The finite points that a Möbius transformation does not send to `∞` are dense in `ℂ`: the
only one it does send to `∞` is `-d / c`. -/
private theorem dense_setOf_add_ne_zero (g : GL (Fin 2) ℂ) :
    Dense {z : ℂ | g 1 0 * z + g 1 1 ≠ 0} := by
  refine (dense_compl_singleton (-(g 1 1 / g 1 0))).mono fun z hz hz' ↦
    mem_compl_singleton_iff.1 hz ?_
  have hc : g 1 0 ≠ 0 := by
    rintro hc
    rw [hc, zero_mul, zero_add] at hz'
    apply g.det_ne_zero
    rw [Matrix.det_fin_two, hc, hz']
    ring
  field_simp
  linear_combination hz'

/-- If a unimodular Möbius transformation preserves the Fubini–Study form, then
`|a z + b|² + |c z + d|² = |z|² + 1` for every `z`. -/
private theorem sq_norm_add_sq_norm_eq_of_mpullback_eq (g : GL (Fin 2) ℂ)
    (hdet : (g : Matrix (Fin 2) (Fin 2) ℂ).det = 1)
    (h : SmoothForm.mpullback (g • ·) (contMDiff_const_smul g) fubiniStudyForm = fubiniStudyForm)
    (z : ℂ) : ‖g 0 0 * z + g 0 1‖ ^ 2 + ‖g 1 0 * z + g 1 1‖ ^ 2 = ‖z‖ ^ 2 + 1 := by
  -- The identity holds at the finite points not sent to `∞`, and so everywhere by continuity.
  refine congrFun ((show Continuous fun z : ℂ ↦ ‖g 0 0 * z + g 0 1‖ ^ 2 +
      ‖g 1 0 * z + g 1 1‖ ^ 2 by fun_prop).ext_on (dense_setOf_add_ne_zero g)
    (show Continuous fun z : ℂ ↦ ‖z‖ ^ 2 + 1 by fun_prop) fun z hz ↦ ?_) z
  -- Compare the two forms on the pair of tangent vectors `1, i`, whose area is `1`.
  have h₁ := congrArg (fun φ : SmoothForm 𝓘(ℝ, ℂ) (OnePoint ℂ) ℝ 2 ↦
    SmoothBundleForm.eval₂ φ (z : OnePoint ℂ) (1 : ℂ) Complex.I) h
  simp only [eval₂_mpullback_smul_coe g hdet hz, eval₂_fubiniStudyForm_coe,
    fubiniStudyDensity_def, map_one, one_mul, Complex.I_im, mul_one, inv_inj] at h₁
  have h₂ := mul_left_cancel₀ Real.pi_ne_zero h₁
  rw [add_comm (1 : ℝ)] at h₂
  exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp h₂

/-- If `|a z + b|² + |c z + d|² = |z|² + 1` for every `z`, then the unimodular Möbius
transformation of `!![a, b; c, d]` preserves the Fubini–Study form. -/
private theorem mpullback_eq_of_sq_norm_add_sq_norm_eq (g : GL (Fin 2) ℂ)
    (hdet : (g : Matrix (Fin 2) (Fin 2) ℂ).det = 1)
    (h : ∀ z : ℂ, ‖g 0 0 * z + g 0 1‖ ^ 2 + ‖g 1 0 * z + g 1 1‖ ^ 2 = ‖z‖ ^ 2 + 1) :
    SmoothForm.mpullback (g • ·) (contMDiff_const_smul g) fubiniStudyForm = fubiniStudyForm := by
  -- The forms agree at the finite points not sent to `∞`, which are dense in the sphere.
  have hdense : Dense (((↑) : ℂ → OnePoint ℂ) '' {z : ℂ | g 1 0 * z + g 1 1 ≠ 0}) :=
    denseRange_coe.dense_image continuous_coe (dense_setOf_add_ne_zero g)
  -- Two smooth forms agreeing on a dense set are equal, since the total space of the bundle of
  -- alternating forms is Hausdorff.
  have hcont (φ : SmoothForm 𝓘(ℝ, ℂ) (OnePoint ℂ) ℝ 2) := φ.contMDiff.continuous
  have heq := (hcont (SmoothForm.mpullback (g • ·) (contMDiff_const_smul g)
    fubiniStudyForm)).ext_on hdense (hcont fubiniStudyForm) ?_
  · exact Subtype.ext (funext fun x ↦ by simpa using congrFun heq x)
  rintro _ ⟨z, hz, rfl⟩
  refine congrArg (TotalSpace.mk' _ _) (ContinuousAlternatingMap.ext fun u ↦ ?_)
  have key (v w : ℂ) : SmoothBundleForm.eval₂
      (SmoothForm.mpullback (g • ·) (contMDiff_const_smul g) fubiniStudyForm) (z : OnePoint ℂ)
      v w = SmoothBundleForm.eval₂ fubiniStudyForm (z : OnePoint ℂ) v w := by
    rw [eval₂_mpullback_smul_coe g hdet hz, eval₂_fubiniStudyForm_coe, fubiniStudyDensity_def,
      h z, add_comm (‖z‖ ^ 2)]
  have hu : u = ![u 0, u 1] := (FinVec.etaExpand_eq u).symm
  rw [hu]
  simpa only [SmoothBundleForm.eval₂_apply] using key (u 0) (u 1)

/-! ### The Möbius transformations preserving the Fubini–Study form -/

/-- **The unimodular Möbius transformations preserving the Fubini–Study form are the unitary
ones.** For `A ∈ SL(2, ℂ)`, the Möbius transformation of `A` pulls the Fubini–Study form of the
Riemann sphere back to itself exactly when `A` is a unitary matrix. -/
theorem mpullback_smul_fubiniStudyForm_eq_self_iff_mem_unitaryGroup (A : SL(2, ℂ)) :
    SmoothForm.mpullback ((A : GL (Fin 2) ℂ) • · : OnePoint ℂ → OnePoint ℂ)
        (contMDiff_const_smul _) fubiniStudyForm = fubiniStudyForm ↔
      (A : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hdet : ((A : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by simp
  rw [← forall_sq_norm_add_sq_norm_eq_iff_mem_unitaryGroup]
  simpa using ⟨sq_norm_add_sq_norm_eq_of_mpullback_eq _ hdet,
    mpullback_eq_of_sq_norm_add_sq_norm_eq _ hdet⟩

/-- **The Fubini–Study form is preserved exactly by `PSU(2)`.** An element of `PSL(2, ℂ)` pulls
the Fubini–Study form of the Riemann sphere back to itself exactly when it lies in the projective
special unitary group `PSU(2)`, the image of `SU(2)`. -/
theorem mpullback_smul_fubiniStudyForm_eq_self_iff_mem_range_toPSL (g : PSL(2, ℂ)) :
    SmoothForm.mpullback (g • · : OnePoint ℂ → OnePoint ℂ) (contMDiff_const_smul g)
        fubiniStudyForm = fubiniStudyForm ↔
      g ∈ (Matrix.specialUnitaryGroup.toPSL :
        Matrix.specialUnitaryGroup (Fin 2) ℂ →* PSL(2, ℂ)).range := by
  induction g using QuotientGroup.induction_on with
  | H A =>
    rw [Matrix.specialUnitaryGroup.mk_mem_range_toPSL_iff,
      ← mpullback_smul_fubiniStudyForm_eq_self_iff_mem_unitaryGroup]
    simp only [pslMk_smul]

end OnePoint
