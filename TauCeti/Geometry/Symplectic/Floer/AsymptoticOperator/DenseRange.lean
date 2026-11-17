/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder
public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Eigenbasis
public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
import TauCeti.Analysis.Distribution.DuBoisReymond
import Mathlib.Analysis.InnerProductSpace.Dual
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Norm
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# The stationary cylinder operator at a nondegenerate orbit has dense range

Let `F` be a finite-dimensional complex inner product space, such as `ℂⁿ`, with its standard
complex structure `J₀ = i`, and let `S` be a loop of real-linear maps of `F` of period one, of
class `C¹`, infinitesimally symplectic for `ω₀ = Im ⟪·, ·⟫` and nondegenerate: the linear equation
`ζ' = S_t ζ` has no nonzero periodic solution. The stationary cylinder operator

`D ξ = ∂s ξ + J₀ (∂t ξ - S_t ξ)`

(`TauCeti.Floer.stationaryCylinderOperator` for the constant structure
`AlmostComplexStructure.ofComplexModule F`) is the linearized Floer operator along the stationary
cylinder over a nondegenerate orbit, written in a unitary trivialization. This file proves that
its image is dense in `L²` of the cylinder: a square integrable section `η` with
`∫ Re ⟪D ξ, η⟫ = 0` for every test section `ξ` vanishes almost everywhere
(`TauCeti.Floer.ae_eq_zero_of_forall_integral_re_inner_stationaryCylinderOperator_eq_zero`).
Together with the a priori estimate of `TauCeti.Geometry.Symplectic.Floer.SpectralGap`, which makes
`D` injective with closed range on the Sobolev completion, this is the surjectivity half of the
invertibility of `D`, the invertible block of a stationary cylinder.

The proof uses the eigenbasis of the asymptotic operator `A = J₀ (d/dt - S_t)`
(`TauCeti.CircleSobolev.exists_hilbertBasis_I_smul_loopOperator_eq_smul`): a Hilbert basis of
`H⁰ = L²(S¹, F)` of eigenfunctions `e` with real eigenvalues `λ ≠ 0`. It does not use any
regularity theory for weak solutions of the adjoint equation.

* **Eigenmodes.** An eigenfunction solves `e' = S_t e - λ J₀ e`, so it is of class `C²` when `S`
  is `C¹`. On the product section `φ(s) e(t)`, `D` acts as the scalar operator
  `(φ' + λ φ) e`.
* **The weak equation of a mode.** Testing against these sections shows that the slice pairing
  `A(s) = ∫₀¹ Re ⟪e, η(s, ·)⟫` is a distributional solution of `A' = λ A`, so `A = c e^{λ s}` on
  every bounded interval, by the du Bois-Reymond lemma
  (`LocallyIntegrableOn.exists_ae_eq_exp_smul_Ioo_of_integral_deriv_add_mul_smul_eq_zero`, in the
  namespace `MeasureTheory`).
  The integrals of `|A|` over unit intervals are bounded by `‖e‖² + ‖η‖²_{L²}`, while those of
  `e^{λ s}` are not, so `c = 0`.
* **All loops.** For a test function `φ`, the functional `ψ ↦ ∫ φ(s) ∫₀¹ Re ⟪ψ, η(s, ·)⟫` on
  continuous loops is bounded by `‖φ‖_{L²} ‖η‖_{L²} ‖ψ‖_{H⁰}`, by Cauchy–Schwarz on the strip and
  Parseval's identity, and vanishes on the eigenfunctions, which span a dense subspace of `H⁰`.
  So the slice pairing of `η` with every continuous loop vanishes almost everywhere.
* **Slices.** By separability of the space of loops, for almost every `s` the slice pairing
  vanishes for all loops at once; testing against loops `g(t) v` with `g` supported in `(0, 1)`
  shows that the slice `η(s, ·)` vanishes, and Fubini's theorem gives `η = 0`.

## Main results

* `TauCeti.Floer.ae_eq_zero_of_forall_integral_re_inner_stationaryCylinderOperator_eq_zero`: a
  square integrable section orthogonal to the image of the test sections under the stationary
  cylinder operator at a nondegenerate orbit vanishes.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2 (the invertibility of `∂s + A` at a nondegenerate orbit via the
  spectral decomposition of `A`).
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc. 27
  (1995), 1–33.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped ContDiff

namespace TauCeti.Floer

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ F] in
/-- On a product section `φ(s) e(t)` whose loop `e` solves `e' = S_t e - λ J₀ e`, the stationary
cylinder operator of `J₀ = i` is `(φ' + λ φ) e`. -/
private theorem stationaryCylinderOperator_smul_of_hasDerivAt {S : ℝ → F →L[ℝ] F}
    {e : ℝ → F} {lam : ℝ} (he : ∀ y, HasDerivAt e (S y (e y) - lam • I • e y) y)
    {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) (z : ℝ × ℝ) :
    stationaryCylinderOperator (fun _ ↦ AlmostComplexStructure.ofComplexModule F) S
        (fun w ↦ φ w.1 • e w.2) z = (deriv φ z.1 + lam * φ z.1) • e z.2 := by
  have h1 : HasFDerivAt (fun w : ℝ × ℝ ↦ φ w.1)
      (deriv φ z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) z :=
    (hφ z.1).hasDerivAt.comp_hasFDerivAt z (hasFDerivAt_fst)
  have h2 := (he z.2).hasFDerivAt.comp z (hasFDerivAt_snd (p := z))
  have h : HasFDerivAt (fun w : ℝ × ℝ ↦ φ w.1 • e w.2) _ z := h1.smul h2
  rw [stationaryCylinderOperator_def, h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.toSpanSingleton_apply, stdComplexLineReal, stdComplexLineImag, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one, mul_zero,
    zero_smul, one_smul, smul_zero, add_zero, zero_add,
    AlmostComplexStructure.ofComplexModule_apply,
    map_smul]
  simp only [smul_sub, smul_comm I (φ z.1), smul_comm I lam, smul_smul I I, I_mul_I, neg_one_smul,
    smul_neg]
  module

omit [FiniteDimensional ℂ F] in
/-- A loop solving `e' = S_t e - λ J₀ e` with `S` of class `C¹` is of class `C²`. -/
private theorem contDiff_two_of_hasDerivAt {S : ℝ → F →L[ℝ] F} (hS : ContDiff ℝ 1 S)
    {e : ℝ → F} {lam : ℝ} (he : ∀ y, HasDerivAt e (S y (e y) - lam • I • e y) y) :
    ContDiff ℝ 2 e := by
  have hd : deriv e = fun y ↦ S y (e y) - lam • I • e y := funext fun y ↦ (he y).deriv
  have hdiff : Differentiable ℝ e := fun y ↦ (he y).differentiableAt
  have h1 : ContDiff ℝ 1 e := contDiff_one_iff_deriv.2 ⟨hdiff, by
    rw [hd]
    exact (hS.continuous.clm_apply hdiff.continuous).sub
      (hdiff.continuous.const_smul I |>.const_smul lam)⟩
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨hdiff, by simp, ?_⟩
  rw [hd]
  exact (hS.clm_apply h1).sub ((h1.const_smul I).const_smul lam)

open CylinderSobolev

omit [FiniteDimensional ℂ F] in
/-- The real part of the pointwise pairing of two square integrable sections is integrable, and
it integrates to the real part of their `L²` inner product. -/
private theorem integral_re_inner_eq_re_inner_toLp {u η : ℝ × ℝ → F}
    (hu : MemLp u 2 stripMeasure) (hη : MemLp η 2 stripMeasure) :
    Integrable (fun z ↦ (inner ℂ (u z) (η z)).re) stripMeasure ∧
      ∫ z, (inner ℂ (u z) (η z)).re ∂stripMeasure =
        RCLike.re (inner ℂ (hu.toLp u) (hη.toLp η)) := by
  have hae : (fun z ↦ RCLike.re (inner ℂ ((hu.toLp u : ℝ × ℝ → F) z) ((hη.toLp η : _) z)))
      =ᵐ[stripMeasure] fun z ↦ (inner ℂ (u z) (η z)).re := by
    filter_upwards [hu.coeFn_toLp, hη.coeFn_toLp] with z h₁ h₂
    rw [h₁, h₂, RCLike.re_to_complex]
  refine ⟨(MemLp.integrable_inner (𝕜 := ℂ) hu hη).re, ?_⟩
  rw [L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
  exact (integral_congr_ae hae).symm

/-- **Parseval's identity on `[0, 1]`.** The squared norm in `H⁰` of a continuous loop of period
one is `∫₀¹ ‖ψ‖²`. -/
private theorem integral_norm_sq_eq_norm_ofContinuousMap_sq (ψ : C(AddCircle (1 : ℝ), F)) :
    ∫ t in Icc (0 : ℝ) 1, ‖ψ t‖ ^ 2 = ‖CircleSobolev.ofContinuousMap 1 ψ‖ ^ 2 := by
  have hhaar : AddCircle.haarAddCircle = (volume : Measure (AddCircle (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
  have h := AddCircle.integral_preimage (T := 1) 0 fun x ↦ ‖ψ x‖ ^ 2
  rw [zero_add] at h
  rw [← real_inner_self_eq_norm_sq, CircleSobolev.real_inner_ofContinuousMap, hhaar,
    integral_Icc_eq_integral_Ioc, h]
  exact integral_congr_ae (ae_of_all _ fun x ↦ (inner_self_eq_norm_sq (𝕜 := ℂ) (ψ x)).symm)

/-- The pairing `s ↦ ∫₀¹ ⟪ψ t, η (s, t)⟫` of a section `η` with a loop `ψ` on the slices
`s = const`. -/
private def sliceInner (η : ℝ × ℝ → F) (ψ : ℝ → F) (s : ℝ) : ℝ :=
  ∫ t in Icc (0 : ℝ) 1, (inner ℂ (ψ t) (η (s, t))).re

omit [FiniteDimensional ℂ F] in
/-- A product section `φ(s) ψ(t)` with `φ` continuous of compact support and `ψ` continuous and
bounded is square integrable on the strip. -/
private theorem memLp_smul_of_hasCompactSupport {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) {ψ : ℝ → F} (hψ : Continuous ψ) {B : ℝ} (hB : ∀ t, ‖ψ t‖ ≤ B) :
    MemLp (fun z : ℝ × ℝ ↦ φ z.1 • ψ z.2) 2 stripMeasure := by
  obtain ⟨Cφ, hCφ⟩ := hφ.bounded_above_of_compact_support hφc
  obtain ⟨R, -, hR⟩ := hφc.exists_pos_le_norm
  refine memLp_stripMeasure_of_continuous (u := fun z : ℝ × ℝ ↦ φ z.1 • ψ z.2)
    ((hφ.comp continuous_fst).smul (hψ.comp continuous_snd)) (C := Cφ * B) (R := R)
    (fun z ↦ ?_) (fun z hz ↦ ?_) 2
  · rw [norm_smul]
    exact mul_le_mul (hCφ _) (hB _) (norm_nonneg _) ((norm_nonneg _).trans (hCφ z.1))
  · rw [hR z.1 (by rw [Real.norm_eq_abs]; exact hz.le), zero_smul]

omit [FiniteDimensional ℂ F] in
/-- **Fubini for product sections.** Pairing `η` with `φ(s) ψ(t)` over the strip integrates `φ`
against the slice pairing of `η` with `ψ`. -/
private theorem integral_inner_smul_eq_integral_mul_sliceInner {η : ℝ × ℝ → F}
    (hη : MemLp η 2 stripMeasure) {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {ψ : ℝ → F} (hψ : Continuous ψ) {B : ℝ} (hB : ∀ t, ‖ψ t‖ ≤ B) :
    ∫ z, (inner ℂ (φ z.1 • ψ z.2) (η z)).re ∂stripMeasure = ∫ s, φ s * sliceInner η ψ s := by
  have hint := (integral_re_inner_eq_re_inner_toLp (memLp_smul_of_hasCompactSupport hφ hφc hψ hB)
    hη).1
  rw [stripMeasure_eq_prod] at hint ⊢
  rw [integral_prod _ hint]
  refine integral_congr_ae (ae_of_all _ fun s ↦ ?_)
  simp only [← Complex.coe_smul, inner_smul_left, conj_ofReal, re_ofReal_mul, sliceInner]
  exact integral_const_mul _ _

omit [FiniteDimensional ℂ F] in
/-- **Growth of the slice pairing.** If `‖ψ‖ ≤ B` and `‖η‖²` is integrable on the strip, the slice
pairing is integrable on `[a, b]`, with
`∫_{[a, b]} |∫₀¹ ⟪ψ, η⟫| ≤ ((b - a) B² + ∫ ‖η‖²) / 2`. -/
private theorem integrableOn_sliceInner_and_integral_abs_le {η : ℝ × ℝ → F}
    (hη : MemLp η 2 stripMeasure) {ψ : ℝ → F} (hψ : Continuous ψ) {B : ℝ}
    (hB : ∀ t, ‖ψ t‖ ≤ B) {a b : ℝ} (hab : a ≤ b) :
    IntegrableOn (sliceInner η ψ) (Icc a b) ∧
      ∫ s in Icc a b, |sliceInner η ψ s| ≤
        ((b - a) * B ^ 2 + ∫ z, ‖η z‖ ^ 2 ∂stripMeasure) / 2 := by
  set μ : Measure (ℝ × ℝ) := (volume.restrict (Icc a b)).prod (volume.restrict (Icc (0 : ℝ) 1))
  have hμ : μ ≤ stripMeasure := by
    rw [stripMeasure_eq_prod]
    exact Measure.prod_mono Measure.restrict_le_self le_rfl
  have hη2 : Integrable (fun z ↦ ‖η z‖ ^ 2) stripMeasure :=
    (memLp_two_iff_integrable_sq_norm hη.aestronglyMeasurable).1 hη
  set G : ℝ × ℝ → ℝ := fun z ↦ (B ^ 2 + ‖η z‖ ^ 2) / 2
  have hG : Integrable G μ :=
    ((integrable_const _).add (hη2.mono_measure hμ)).div_const _
  have hgG (z : ℝ × ℝ) : ‖(inner ℂ (ψ z.2) (η z)).re‖ ≤ G z := by
    have h1 := (abs_re_le_norm (inner ℂ (ψ z.2) (η z))).trans (norm_inner_le_norm (ψ z.2) (η z))
    have h2 : ‖ψ z.2‖ * ‖η z‖ ≤ B * ‖η z‖ := mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
    have h3 := two_mul_le_add_sq B ‖η z‖
    rw [Real.norm_eq_abs]
    simp only [G]
    nlinarith
  have hg : Integrable (fun z : ℝ × ℝ ↦ (inner ℂ (ψ z.2) (η z)).re) μ :=
    hG.mono' ((hψ.comp continuous_snd).aestronglyMeasurable.inner (𝕜 := ℂ)
      (hη.aestronglyMeasurable.mono_measure hμ)).re (ae_of_all _ hgG)
  refine ⟨hg.integral_prod_left, ?_⟩
  calc ∫ s in Icc a b, |sliceInner η ψ s|
      ≤ ∫ s in Icc a b, ∫ t in Icc (0 : ℝ) 1, ‖(inner ℂ (ψ t) (η (s, t))).re‖ :=
        integral_mono hg.integral_prod_left.abs hg.norm.integral_prod_left fun s ↦ by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_integral_norm _
    _ = ∫ z, ‖(inner ℂ (ψ z.2) (η z)).re‖ ∂μ := (integral_prod _ hg.norm).symm
    _ ≤ ∫ z, G z ∂μ := integral_mono hg.norm hG hgG
    _ = ((b - a) * B ^ 2 + ∫ z, ‖η z‖ ^ 2 ∂μ) / 2 := by
        simp only [G]
        rw [integral_div, integral_add (integrable_const _) (hη2.mono_measure hμ),
          integral_const]
        rw [Measure.real, ← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
          Measure.restrict_apply_univ, Real.volume_Icc, Real.volume_Icc, sub_zero,
          ENNReal.ofReal_one, mul_one, ENNReal.toReal_ofReal (sub_nonneg.2 hab), smul_eq_mul]
    _ ≤ ((b - a) * B ^ 2 + ∫ z, ‖η z‖ ^ 2 ∂stripMeasure) / 2 := by
        have := integral_mono_measure hμ (ae_of_all _ fun z ↦ by positivity) hη2
        linarith

omit [FiniteDimensional ℂ F] in
/-- The slice pairing with a continuous loop of period one is locally integrable. -/
private theorem locallyIntegrable_sliceInner {η : ℝ × ℝ → F} (hη : MemLp η 2 stripMeasure)
    (χ : C(AddCircle (1 : ℝ), F)) : LocallyIntegrable (sliceInner η fun t ↦ χ t) := by
  refine locallyIntegrable_iff.2 fun k hk ↦ ?_
  obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall 0
  refine ((integrableOn_sliceInner_and_integral_abs_le hη
    (χ.continuous.comp (AddCircle.continuous_mk' 1)) (fun t ↦ χ.norm_coe_le_norm _)
    (a := -|R|) (b := |R|) (by linarith [abs_nonneg R])).1).mono_set fun x hx ↦ ?_
  have := hR hx
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  exact ⟨by linarith [neg_abs_le x, le_abs_self R], by linarith [le_abs_self x, le_abs_self R]⟩

/-- **Cauchy–Schwarz for product sections.** The pairing of `η` with `φ(s) χ(t)` is bounded by
`‖φ‖_{L²} ‖η‖_{L²} ‖χ‖_{H⁰}`, by Cauchy–Schwarz on the strip and Parseval's identity. -/
private theorem abs_integral_re_inner_smul_le {η : ℝ × ℝ → F} (hη : MemLp η 2 stripMeasure)
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) (χ : C(AddCircle (1 : ℝ), F)) :
    |∫ z, (inner ℂ (φ z.1 • χ z.2) (η z)).re ∂stripMeasure| ≤
      Real.sqrt (∫ s, φ s ^ 2) * ‖hη.toLp η‖ * ‖CircleSobolev.ofContinuousMap 1 χ‖ := by
  have hu := memLp_smul_of_hasCompactSupport hφ hφc (ψ := fun t : ℝ ↦ χ t)
    (χ.continuous.comp (AddCircle.continuous_mk' 1)) fun t ↦ χ.norm_coe_le_norm _
  have hnorm : ‖hu.toLp _‖ = Real.sqrt (∫ s, φ s ^ 2) * ‖CircleSobolev.ofContinuousMap 1 χ‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (hu.toLp _)), MemLp.norm_toLp_sq, stripMeasure_eq_prod,
      ← Real.sqrt_sq (norm_nonneg (CircleSobolev.ofContinuousMap 1 χ)), ← Real.sqrt_mul
        (integral_nonneg fun s ↦ sq_nonneg _), ← integral_norm_sq_eq_norm_ofContinuousMap_sq]
    congr 1
    simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    exact integral_prod_mul (μ := volume) (ν := volume.restrict (Icc (0 : ℝ) 1))
      (fun s ↦ φ s ^ 2) fun t : ℝ ↦ ‖χ t‖ ^ 2
  rw [(integral_re_inner_eq_re_inner_toLp hu hη).2]
  refine ((abs_re_le_norm _).trans (norm_inner_le_norm _ _)).trans (le_of_eq ?_)
  rw [hnorm]
  ring

/-- **Density in `H⁰`.** A real-linear functional on continuous loops bounded by a multiple of the
`H⁰` norm and vanishing on loops forming a Hilbert basis of `H⁰` vanishes. -/
private theorem eq_zero_of_abs_le_of_hilbertBasis (Λ : C(AddCircle (1 : ℝ), F) →ₗ[ℝ] ℝ) {K : ℝ}
    (hK : 0 ≤ K) (hΛ : ∀ χ, |Λ χ| ≤ K * ‖CircleSobolev.ofContinuousMap 1 χ‖) {ι : Type*}
    (b : HilbertBasis ι ℝ (CircleSobolev 0 F)) (e : ι → C(AddCircle (1 : ℝ), F))
    (hb : ∀ i, b i = CircleSobolev.ofContinuousMap 1 (e i)) (he : ∀ i, Λ (e i) = 0)
    (ψ : C(AddCircle (1 : ℝ), F)) : Λ ψ = 0 := by
  -- The loops on which `Λ` vanishes have a dense image in `H⁰`, since it contains the basis.
  set P : Submodule ℝ (CircleSobolev 0 F) := (LinearMap.ker Λ).map
    ((CircleSobolev.ofContinuousMap 1 : C(AddCircle (1 : ℝ), F) →L[ℂ] CircleSobolev 0 F)
      |>.toLinearMap.restrictScalars ℝ)
  have hspan : Submodule.span ℝ (range b) ≤ P :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ⟨e i, he i, (hb i).symm⟩)
  have hmem : CircleSobolev.ofContinuousMap 1 ψ ∈ closure (P : Set (CircleSobolev 0 F)) := by
    have h := Submodule.topologicalClosure_mono hspan
    rw [b.dense_span, top_le_iff] at h
    rw [← Submodule.topologicalClosure_coe, h]
    trivial
  by_contra hne
  have hpos : 0 < |Λ ψ| := abs_pos.2 hne
  obtain ⟨y, ⟨χ, hχ, rfl⟩, hy⟩ := Metric.mem_closure_iff.1 hmem (|Λ ψ| / (K + 1))
    (by positivity)
  have h1 : |Λ ψ| ≤ K * dist (CircleSobolev.ofContinuousMap 1 ψ)
      (CircleSobolev.ofContinuousMap 1 χ) := by
    have := hΛ (ψ - χ)
    rwa [map_sub, LinearMap.mem_ker.1 hχ, sub_zero, map_sub, ← dist_eq_norm] at this
  have h2 := mul_le_mul_of_nonneg_left hy.le hK
  have h3 : K * (|Λ ψ| / (K + 1)) < |Λ ψ| := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  exact (h1.trans h2).not_gt h3

/-- **From a Hilbert basis of loops to all loops.** If `H⁰` has a Hilbert basis of continuous
loops `e i` whose slice pairings with `η` vanish almost everywhere, then the slice pairing of `η`
with every continuous loop vanishes almost everywhere. -/
private theorem sliceInner_ae_eq_zero_of_hilbertBasis {η : ℝ × ℝ → F}
    (hη : MemLp η 2 stripMeasure) {ι : Type*} (b : HilbertBasis ι ℝ (CircleSobolev 0 F))
    (e : ι → C(AddCircle (1 : ℝ), F)) (hb : ∀ i, b i = CircleSobolev.ofContinuousMap 1 (e i))
    (he : ∀ i, sliceInner η (fun t ↦ e i t) =ᵐ[volume] 0) (ψ : C(AddCircle (1 : ℝ), F)) :
    sliceInner η (fun t ↦ ψ t) =ᵐ[volume] 0 := by
  have hcont (χ : C(AddCircle (1 : ℝ), F)) : Continuous fun t : ℝ ↦ χ t :=
    χ.continuous.comp (AddCircle.continuous_mk' 1)
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero (locallyIntegrable_sliceInner hη ψ)
    fun φ hφ hφc ↦ ?_
  have hu (χ : C(AddCircle (1 : ℝ), F)) := memLp_smul_of_hasCompactSupport hφ.continuous hφc
    (hcont χ) fun t ↦ χ.norm_coe_le_norm _
  have hint (χ : C(AddCircle (1 : ℝ), F)) := (integral_re_inner_eq_re_inner_toLp (hu χ) hη).1
  -- The functional `Λ χ = ∫ ⟪φ ⊗ χ, η⟫` on continuous loops is real-linear.
  let Λ : C(AddCircle (1 : ℝ), F) →ₗ[ℝ] ℝ :=
    { toFun := fun χ ↦ ∫ z, (inner ℂ (φ z.1 • χ z.2) (η z)).re ∂stripMeasure
      map_add' := fun χ χ' ↦ by
        simp only [ContinuousMap.add_apply, smul_add, inner_add_left, add_re]
        exact integral_add (hint χ) (hint χ')
      map_smul' := fun c χ ↦ by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
        dsimp only
        rw [smul_comm, ← Complex.coe_smul c, inner_smul_left, conj_ofReal, re_ofReal_mul] }
  have hΛ (χ : C(AddCircle (1 : ℝ), F)) : Λ χ = ∫ s, φ s * sliceInner η (fun t ↦ χ t) s :=
    integral_inner_smul_eq_integral_mul_sliceInner hη hφ.continuous hφc (hcont χ)
      (fun t ↦ χ.norm_coe_le_norm _)
  have h0 := eq_zero_of_abs_le_of_hilbertBasis Λ (by positivity)
    (abs_integral_re_inner_smul_le hη hφ.continuous hφc) b e hb
    (fun i ↦ by rw [hΛ]; exact integral_eq_zero_of_ae ((he i).mono fun s hs ↦ by simp [hs])) ψ
  rw [hΛ] at h0
  simpa [smul_eq_mul] using h0

/-- **A slice orthogonal to all loops vanishes.** A function on `[0, 1]`, integrable there, whose
pairing with every continuous loop of period one vanishes, is zero almost everywhere on `[0, 1]`:
test against the loops `g(t) v` with `g` supported in `(0, 1)` and `v` running over `b j` and
`i b j` for a complex basis `b`. -/
private theorem ae_eq_zero_of_forall_integral_re_inner_eq_zero {f : ℝ → F}
    (hf : IntegrableOn f (Icc (0 : ℝ) 1))
    (h : ∀ ψ : C(AddCircle (1 : ℝ), F), ∫ t in Icc (0 : ℝ) 1, (inner ℂ (ψ t) (f t)).re = 0) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), f t = 0 := by
  have hv (v : F) : ∀ᵐ t, t ∈ Ioo (0 : ℝ) 1 → (inner ℂ v (f t)).re = 0 := by
    refine isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (IntegrableOn.mono_set (t := Icc (0 : ℝ) 1) (hf.const_inner (𝕜 := ℂ) v).re
        Ioo_subset_Icc_self).locallyIntegrableOn
      fun g hg _ hgs ↦ ?_
    have hg0 (t : ℝ) (ht : t ∉ Ioo (0 : ℝ) 1) : g t = 0 :=
      image_eq_zero_of_notMem_tsupport fun h' ↦ ht (hgs h')
    -- The loop `g(t) v`, continuous since `g` vanishes at `0` and `1`.
    let ψ : C(AddCircle (1 : ℝ), F) :=
      ⟨AddCircle.liftIco 1 0 fun t ↦ g t • v, AddCircle.liftIco_continuous
        (by rw [hg0 0 (by simp), hg0 (0 + 1) (by simp)])
        (hg.continuous.smul continuous_const).continuousOn⟩
    have hψ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ψ t = g t • v := by
      -- `ψ` is `AddCircle.liftIco` of `g(t) v`, which is `g(t) v` on `[0, 1)`.
      change AddCircle.liftIco (1 : ℝ) 0 (fun t ↦ g t • v) (t : AddCircle (1 : ℝ)) = _
      rcases eq_or_lt_of_le ht.2 with rfl | ht1
      · rw [show ((1 : ℝ) : AddCircle (1 : ℝ)) = ((0 : ℝ) : AddCircle (1 : ℝ)) by
          rw [AddCircle.coe_period, QuotientAddGroup.mk_zero], AddCircle.liftIco_coe_apply
          (by simp), hg0 0 (by simp), hg0 1 (by simp)]
      · exact AddCircle.liftIco_coe_apply ⟨ht.1, by simpa using ht1⟩
    have h0 := h ψ
    rw [setIntegral_congr_fun measurableSet_Icc fun t ht ↦ by rw [hψ t ht]] at h0
    simp only [← Complex.coe_smul, inner_smul_left, conj_ofReal, re_ofReal_mul] at h0
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦ by
      rw [hg0 t fun h' ↦ ht (Ioo_subset_Icc_self h'), zero_mul]] at h0
    simpa [smul_eq_mul] using h0
  -- Both the real and imaginary parts of `⟪b j, f t⟫` vanish, the latter as `Re ⟪i b j, f t⟫`.
  set b := Module.finBasis ℂ F
  have hall : ∀ᵐ t, ∀ j, t ∈ Ioo (0 : ℝ) 1 →
      (inner ℂ (b j) (f t)).re = 0 ∧ (inner ℂ (I • b j) (f t)).re = 0 :=
    ae_all_iff.2 fun j ↦ by
      filter_upwards [hv (b j), hv (I • b j)] with t h₁ h₂ ht using ⟨h₁ ht, h₂ ht⟩
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
  filter_upwards [hall] with t ht htI
  refine InnerProductSpace.ext_inner_left_basis b fun j ↦ ?_
  obtain ⟨h₁, h₂⟩ := ht j htI
  rw [inner_smul_left, conj_I, neg_mul, neg_re, mul_re, I_re, I_im] at h₂
  rw [inner_zero_right]
  exact Complex.ext (by simpa using h₁) (by simp only [Complex.zero_im]; linarith)

/-- **Vanishing for all loops on almost every slice.** If the slice pairing of `η` with every loop
of a dense set vanishes at `s` and the slice `η(s, ·)` is integrable, then the slice pairing with
every continuous loop vanishes at `s`, since the pairing is continuous in the loop. -/
private theorem sliceInner_eq_zero_of_dense {η : ℝ × ℝ → F} {s : ℝ}
    (hs : IntegrableOn (fun t ↦ η (s, t)) (Icc (0 : ℝ) 1)) {D : Set C(AddCircle (1 : ℝ), F)}
    (hD : Dense D) (hsD : ∀ ψ ∈ D, sliceInner η (fun t ↦ ψ t) s = 0)
    (ψ : C(AddCircle (1 : ℝ), F)) : sliceInner η (fun t ↦ ψ t) s = 0 := by
  have hint (χ : C(AddCircle (1 : ℝ), F)) :
      IntegrableOn (fun t : ℝ ↦ (inner ℂ (χ t) (η (s, t))).re) (Icc (0 : ℝ) 1) :=
    (hs.norm.const_mul ‖χ‖).mono' ((χ.continuous.comp
      (AddCircle.continuous_mk' 1)).aestronglyMeasurable.inner (𝕜 := ℂ)
        hs.aestronglyMeasurable).re
      (ae_of_all _ fun t ↦ (abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (χ.norm_coe_le_norm _) (norm_nonneg _))))
  set L : ℝ := ∫ t in Icc (0 : ℝ) 1, ‖η (s, t)‖
  have hL : 0 ≤ L := integral_nonneg fun _ ↦ norm_nonneg _
  -- `|∫₀¹ Re ⟪ψ, η(s, ·)⟫| ≤ ‖ψ - χ‖ L` for every `χ ∈ D`.
  have key (ε : ℝ) (hε : 0 < ε) : |sliceInner η (fun t ↦ ψ t) s| ≤ ε * L := by
    obtain ⟨χ, hχD, hχ⟩ := hD.exists_dist_lt ψ hε
    rw [← sub_zero (sliceInner η _ s), ← hsD χ hχD, sliceInner, sliceInner,
      ← integral_sub (hint ψ) (hint χ), ← Real.norm_eq_abs, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hs.norm.const_mul ε) (ae_of_all _ fun t ↦ ?_)
    rw [← sub_re, ← inner_sub_left, Real.norm_eq_abs]
    refine (abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)))
    rw [← ContinuousMap.sub_apply]
    exact ((ψ - χ).norm_coe_le_norm _).trans (by rw [← dist_eq_norm]; exact hχ.le)
  by_contra hne
  have hpos : 0 < |sliceInner η (fun t ↦ ψ t) s| := abs_pos.2 hne
  have := key (|sliceInner η (fun t ↦ ψ t) s| / (L + 1)) (div_pos hpos (by linarith))
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)] at this
  nlinarith

/-- **Vanishing slice pairings force vanishing.** If the slice pairing of `η` with every
continuous loop of period one vanishes almost everywhere, then `η` vanishes almost everywhere on
the strip: by separability of the space of loops, for almost every `s` the slice pairing vanishes
for all loops at once, so the slice `η(s, ·)` vanishes, and Fubini's theorem applies. -/
private theorem ae_eq_zero_of_forall_sliceInner_ae_eq_zero {η : ℝ × ℝ → F}
    (hη : MemLp η 2 stripMeasure)
    (h : ∀ ψ : C(AddCircle (1 : ℝ), F), sliceInner η (fun t ↦ ψ t) =ᵐ[volume] 0) :
    η =ᵐ[stripMeasure] 0 := by
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hηp : MemLp η 2 ((volume : Measure ℝ).prod ν) := stripMeasure_eq_prod ▸ hη
  -- Almost every slice is integrable on `[0, 1]`.
  have hslice : ∀ᵐ s, Integrable (fun t ↦ η (s, t)) ν := by
    have h2 := ((memLp_two_iff_integrable_sq_norm hηp.aestronglyMeasurable).1 hηp).prod_right_ae
    filter_upwards [h2, hηp.aestronglyMeasurable.prodMk_left] with s hs hm
    exact ((memLp_two_iff_integrable_sq_norm hm).2 hs).integrable one_le_two
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense C(AddCircle (1 : ℝ), F)
  have hfin : ∀ᵐ s, ∀ᵐ t ∂ν, η (s, t) = 0 := by
    filter_upwards [hslice, (ae_ball_iff hDc).2 fun ψ _ ↦ h ψ] with s hs hsD
    exact ae_eq_zero_of_forall_integral_re_inner_eq_zero hs
      (sliceInner_eq_zero_of_dense hs hD hsD)
  -- Pass to a strongly measurable representative to apply Fubini's theorem to the zero set.
  have hηη' : η =ᵐ[(volume : Measure ℝ).prod ν] hηp.aestronglyMeasurable.mk η :=
    hηp.aestronglyMeasurable.ae_eq_mk
  have h' : ∀ᵐ s, ∀ᵐ t ∂ν, hηp.aestronglyMeasurable.mk η (s, t) = 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod hηη', hfin] with s h1 h2
    filter_upwards [h1, h2] with t ht1 ht2
    rw [← ht1, ht2]
  have hmeas : MeasurableSet {z : ℝ × ℝ | hηp.aestronglyMeasurable.mk η z = 0} :=
    hηp.aestronglyMeasurable.stronglyMeasurable_mk.measurableSet_eq_fun stronglyMeasurable_const
  rw [stripMeasure_eq_prod]
  filter_upwards [hηη', (Measure.ae_prod_mem_iff_ae_ae_mem hmeas).2 h'] with z h1 h2
  rw [h1]
  exact h2

omit [FiniteDimensional ℂ F] in
/-- **The slice pairing with an eigenmode vanishes.** If `e` solves `e' = S_t e - λ J₀ e` with
`λ ≠ 0` and `η` is orthogonal to the image of the test sections under `D`, then the slice pairing
`A(s) = ∫₀¹ Re ⟪e, η(s, ·)⟫` vanishes almost everywhere: on product sections `φ(s) e(t)` the
orthogonality says that `A` solves `A' = λ A` weakly, and `A` has uniformly bounded integrals
over unit intervals. -/
private theorem sliceInner_ae_eq_zero_of_hasDerivAt {S : ℝ → F →L[ℝ] F}
    (hS₁ : ContDiff ℝ 1 S) {e : C(AddCircle (1 : ℝ), F)} {lam : ℝ} (hlam : lam ≠ 0)
    (he : ∀ y : ℝ, HasDerivAt (fun y : ℝ ↦ e y) (S y (e y) - lam • I • e y) y)
    {η : ℝ × ℝ → F} (hη : MemLp η 2 stripMeasure)
    (h : ∀ ξ ∈ testSection F, ∫ z, (inner ℂ (stationaryCylinderOperator
      (fun _ ↦ AlmostComplexStructure.ofComplexModule F) S ξ z) (η z)).re ∂stripMeasure = 0) :
    sliceInner η (fun t ↦ e t) =ᵐ[volume] 0 := by
  have hcont : Continuous fun t : ℝ ↦ e t := e.continuous.comp (AddCircle.continuous_mk' 1)
  have hbd (t : ℝ) : ‖e t‖ ≤ ‖e‖ := e.norm_coe_le_norm _
  refine ae_eq_zero_of_integral_deriv_add_mul_mul_eq_zero hlam
    (fun a b hab ↦ (integrableOn_sliceInner_and_integral_abs_le hη hcont hbd hab).1)
    (M := (‖e‖ ^ 2 + ∫ z, ‖η z‖ ^ 2 ∂stripMeasure) / 2)
    (fun n ↦ by
      simpa using (integrableOn_sliceInner_and_integral_abs_le hη hcont hbd
        (a := n) (b := n + 1) (by linarith)).2)
    fun φ hφ hφc ↦ ?_
  -- Test the orthogonality against the product section `φ(s) e(t)`.
  obtain ⟨R, -, hR⟩ := hφc.exists_pos_le_norm
  have hξ : (fun z : ℝ × ℝ ↦ φ z.1 • e z.2) ∈ testSection F := by
    refine mem_testSection_iff.2 ⟨((hφ.of_le (by simp)).comp contDiff_fst).smul
      ((contDiff_two_of_hasDerivAt hS₁ he).comp contDiff_snd), fun s t ↦ ?_, R,
      fun s t hs ↦ ?_⟩
    · simp only [AddCircle.coe_add_period]
    · simp [hR s (by rwa [Real.norm_eq_abs])]
  have h0 := h _ hξ
  simp_rw [stationaryCylinderOperator_smul_of_hasDerivAt he (hφ.differentiable (by simp))] at h0
  rw [← integral_inner_smul_eq_integral_mul_sliceInner hη (φ := fun s ↦ deriv φ s + lam * φ s)
    ((hφ.continuous_deriv (by simp)).add (continuous_const.mul hφ.continuous))
    (hφc.deriv.add (hφc.smul_left (f := fun _ ↦ lam))) hcont hbd]
  exact h0

/-- **The stationary cylinder operator at a nondegenerate orbit has dense range.** Let `S` be a
loop of real-linear maps of `F`, of class `C¹` and infinitesimally symplectic for
`ω₀ = Im ⟪·, ·⟫`, such that `ζ' = S_t ζ` has no nonzero periodic solution. If a square integrable
section `η` of the cylinder is `L²`-orthogonal to `D ξ = ∂s ξ + J₀ (∂t ξ - S_t ξ)` for every test
section `ξ`, where `J₀ = i`, then `η = 0` almost everywhere. -/
theorem ae_eq_zero_of_forall_integral_re_inner_stationaryCylinderOperator_eq_zero
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)} (hS₁ : ContDiff ℝ 1 fun t : ℝ ↦ S t)
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hnd : ∀ ζ : C(AddCircle (1 : ℝ), F),
      (∀ x : ℝ, HasDerivAt (fun y : ℝ ↦ ζ y) (S x (ζ x)) x) → ζ = 0)
    {η : ℝ × ℝ → F} (hη : MemLp η 2 stripMeasure)
    (h : ∀ ξ ∈ testSection F, ∫ z, (inner ℂ (stationaryCylinderOperator
      (fun _ ↦ AlmostComplexStructure.ofComplexModule F) (fun t ↦ S t) ξ z) (η z)).re
        ∂stripMeasure = 0) :
    η =ᵐ[stripMeasure] 0 := by
  -- The eigenbasis `e i` of the asymptotic operator, with eigenvalues `λ i ≠ 0`.
  obtain ⟨ι, b, a, lam, c, hc, hab⟩ :=
    CircleSobolev.exists_hilbertBasis_I_smul_loopOperator_eq_smul 1 S hS
      ((CircleSobolev.isInvertible_loopOperator_iff 1 S).2 hnd)
  set e : ι → C(AddCircle (1 : ℝ), F) :=
    fun i ↦ CircleSobolev.toContinuousMap 1 (by norm_num) (a i)
  have hb (i : ι) : b i = CircleSobolev.ofContinuousMap 1 (e i) := by
    rw [← (hab i).1, CircleSobolev.ofContinuousMap_toContinuousMap]
  refine ae_eq_zero_of_forall_sliceInner_ae_eq_zero hη
    (sliceInner_ae_eq_zero_of_hilbertBasis hη b e hb fun i ↦ ?_)
  refine sliceInner_ae_eq_zero_of_hasDerivAt hS₁ (fun h0 ↦ ?_)
    ((CircleSobolev.I_smul_loopOperator_eq_smul_iff 1 S (a i) (lam i)).1
      (by rw [(hab i).2.2, (hab i).1])) hη h
  have := (hab i).2.1
  rw [h0, abs_zero] at this
  linarith

end TauCeti.Floer
