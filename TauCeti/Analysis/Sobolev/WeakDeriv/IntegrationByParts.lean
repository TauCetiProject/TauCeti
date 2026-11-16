/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Distribution.TestFunction.Approximation
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Weak integration by parts against `C¹` and operator-valued test fields

`TauCeti.HasWeakLineDerivOn` is defined by testing against smooth scalar test functions
`φ : 𝓓(Ω, ℝ)`. Many test functions built from Taylor remainders, finite-element cutoffs, or
iterated derivatives of `C^m` weights only have finite smoothness `C¹`, and take values in spaces
of continuous linear maps or iterated-gradient duals rather than inner product spaces.

This file extends the weak integration-by-parts identity in three directions, without assuming
translation invariance of the measure or smooth-function density:

* **Finite smoothness (`C¹`).** If `u'` is a weak derivative of `u` in the direction `v` on `Ω`,
  then `∫ fderiv ℝ φ x v • u x ∂μ = -∫ φ x • u' x ∂μ` for every `C¹` compactly supported function
  `φ : E → ℝ` with `tsupport φ ⊆ Ω`
  (`TauCeti.HasWeakLineDerivOn.integral_fderiv_smul_eq_neg_integral_smul`).
  Mollifying `φ` (`ContDiff.exists_testFunction_dist_le_and_dist_fderiv_le`) approximates both `φ`
  and `fderiv ℝ φ` uniformly inside a compact thickening of `tsupport φ` contained in `Ω`, where
  `u` and `u'` are integrable.
* **Bilinear and operator-valued pairings.** Expanding a `C¹` test field `ψ : E → G` with values
  in a finite-dimensional space `G` in a basis transfers the identity through any continuous
  bilinear map `B : G →L[ℝ] F →L[ℝ] H` into any real normed space `H`
  (`TauCeti.HasWeakLineDerivOn.integral_bilin_fderiv_eq_neg`, generalizing
  `TauCeti.HasWeakLineDerivOn.integral_inner_lineDeriv_eq_neg` from inner product spaces to
  arbitrary normed targets).
* **Adjoint Fréchet pairings.** Pairing a weak Fréchet derivative `U : E → E →L[ℝ] F` against a
  `C¹` compactly supported operator functional `Φ : E → (E →L[ℝ] F) →L[ℝ] H` expands along any
  finite basis or orthonormal basis of `E` into directional derivatives of `Φ` evaluated on
  rank-one tensors
  (`TauCeti.HasWeakFDerivOn.integral_clm_apply_eq_neg_sum_fderiv`,
  `TauCeti.HasWeakFDerivOn.integral_clm_apply_eq_neg_sum_fderiv_orthonormalBasis`).

## Main declarations

* `TauCeti.HasWeakLineDerivOn.integral_fderiv_smul_eq_neg_integral_smul` and
  `TauCeti.HasWeakLineDerivOn.setIntegral_fderiv_smul_eq_neg_setIntegral_smul`: integration by
  parts against `C¹` scalar functions compactly supported in `Ω`.
* `TauCeti.hasWeakLineDerivOn_iff_contDiff_one`: characterization of weak directional derivatives
  by `C¹` compactly supported test functions.
* `TauCeti.HasWeakLineDerivOn.integral_bilin_fderiv_eq_neg`,
  `TauCeti.HasWeakLineDerivOn.setIntegral_bilin_fderiv_eq_neg`, and
  `TauCeti.HasWeakLineDerivOn.integral_bilin_lineDeriv_eq_neg`: weak integration by parts through
  a continuous bilinear map.
* `TauCeti.HasWeakLineDerivOn.integral_fderiv_mul_eq_neg` and
  `TauCeti.HasWeakLineDerivOn.integral_fderiv_apply_eq_neg`: scalar and operator-field
  specializations.
* `TauCeti.HasWeakFDerivOn.integral_clm_apply_eq_neg_sum_fderiv` and
  `TauCeti.HasWeakFDerivOn.integral_clm_apply_eq_neg_sum_fderiv_orthonormalBasis`: adjoint
  integration by parts for weak Fréchet derivatives along a basis or orthonormal basis.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2.1.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §3.1.
-/

public section

namespace TauCeti

open _root_.MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions InnerProductSpace

section ScalarC1

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} {Ω : Opens E} {u u' : E → F} {v : E}

/-- **Weak integration by parts against `C¹` functions.** If `u'` is a weak derivative of `u` in
the direction `v` on `Ω`, then `∫ (Dφ(x) v) • u x ∂μ = -∫ φ x • u' x ∂μ` for every `C¹`
compactly supported function `φ : E → ℝ` with `tsupport φ ⊆ Ω`. Neither finite dimensionality of
`E` nor Haar invariance of `μ` is needed. -/
theorem HasWeakLineDerivOn.integral_fderiv_smul_eq_neg_integral_smul
    (h : HasWeakLineDerivOn μ Ω u u' v) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
    ∫ x, fderiv ℝ φ x v • u x ∂μ = -∫ x, φ x • u' x ∂μ := by
  have := h.completeSpace
  by_cases hfd : FiniteDimensional ℝ E
  swap
  · obtain rfl := (hφc.eq_zero_or_finiteDimensional ℝ hφ.continuous).resolve_right hfd; simp
  obtain ⟨δ, hδ, hδΩ⟩ := hφc.isCompact.exists_cthickening_subset_open Ω.isOpen hφs
  set K' := cthickening δ (tsupport φ)
  have hK' : IsCompact K' := hφc.isCompact.cthickening
  have huK : IntegrableOn u K' μ := h.locallyIntegrableOn.integrableOn_compact_subset hδΩ hK'
  have hu'K : IntegrableOn u' K' μ :=
    h.locallyIntegrableOn_deriv.integrableOn_compact_subset hδΩ hK'
  set C := ‖v‖ * (∫ x in K', ‖u x‖ ∂μ) + ∫ x in K', ‖u' x‖ ∂μ
  have hC : 0 ≤ C := add_nonneg
    (mul_nonneg (norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _))
    (integral_nonneg fun _ => norm_nonneg _)
  refine eq_of_forall_dist_le fun ε hε => ?_
  set η := ε / (C + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨ψ, hψK', hψ⟩ := hφ.exists_testFunction_dist_le_and_dist_fderiv_le
    hφc.isCompact subset_rfl hδ hδΩ hη
  have hψ_id : ∫ x, fderiv ℝ (ψ : E → ℝ) x v • u x ∂μ = -∫ x, (ψ : E → ℝ) x • u' x ∂μ := by
    simpa only [(ψ.contDiff.differentiable (by simp) _).lineDeriv_eq_fderiv] using
      h.integral_lineDeriv_smul_eq_neg_integral_smul ψ
  have hφK' : tsupport φ ⊆ K' := self_subset_cthickening _
  have hd_supp : ∀ {g : E → ℝ}, tsupport g ⊆ K' → tsupport (fun x => fderiv ℝ g x v) ⊆ K' :=
    fun hg => (tsupport_fderiv_apply_subset ℝ v).trans hg
  have hb1 := MeasureTheory.norm_integral_smul_sub_le hK' huK
    (f := fun x => fderiv ℝ φ x v) (g := fun x => fderiv ℝ (ψ : E → ℝ) x v)
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    ((ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hd_supp hφK') (hd_supp hψK') fun x _ => by
      rw [dist_eq_norm, ← sub_apply (fderiv ℝ φ x) (fderiv ℝ (ψ : E → ℝ) x) v]
      exact ((fderiv ℝ φ x - fderiv ℝ (ψ : E → ℝ) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (by simpa [dist_comm, dist_eq_norm] using (hψ x).2)
          (norm_nonneg v))
  have hb2 := MeasureTheory.norm_integral_smul_sub_le hK' hu'K hφ.continuous ψ.contDiff.continuous
    hφK' hψK' fun x _ => by simpa [dist_comm] using (hψ x).1
  rw [dist_eq_norm]
  calc ‖(∫ x, fderiv ℝ φ x v • u x ∂μ) - -∫ x, φ x • u' x ∂μ‖
      = ‖((∫ x, fderiv ℝ φ x v • u x ∂μ) - ∫ x, fderiv ℝ (ψ : E → ℝ) x v • u x ∂μ) +
          ((∫ x, φ x • u' x ∂μ) - ∫ x, (ψ : E → ℝ) x • u' x ∂μ)‖ := by rw [hψ_id]; abel_nf
    _ ≤ (η * ‖v‖) * (∫ x in K', ‖u x‖ ∂μ) + η * ∫ x in K', ‖u' x‖ ∂μ :=
        (norm_add_le _ _).trans (add_le_add hb1 hb2)
    _ = η * C := by ring
    _ ≤ ε := by rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith

/-- Set-integral form of `TauCeti.HasWeakLineDerivOn.integral_fderiv_smul_eq_neg_integral_smul`. -/
theorem HasWeakLineDerivOn.setIntegral_fderiv_smul_eq_neg_setIntegral_smul
    (h : HasWeakLineDerivOn μ Ω u u' v) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
    ∫ x in Ω, fderiv ℝ φ x v • u x ∂μ = -∫ x in Ω, φ x • u' x ∂μ := by
  have hd : ∀ x ∉ (Ω : Set E), fderiv ℝ φ x v • u x = 0 := fun x hx => by
    rw [fderiv_of_notMem_tsupport ℝ fun h' => hx (hφs h')]; simp
  have h0 : ∀ x ∉ (Ω : Set E), φ x • u' x = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport fun h' => hx (hφs h'), zero_smul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hd,
    setIntegral_eq_integral_of_forall_compl_eq_zero h0,
    h.integral_fderiv_smul_eq_neg_integral_smul hφ hφc hφs]

/-- Weak directional differentiability is equivalent to the integration-by-parts identity against
all `C¹` functions compactly supported in `Ω`. -/
theorem hasWeakLineDerivOn_iff_contDiff_one [CompleteSpace F] (hu : LocallyIntegrableOn u Ω μ)
    (hu' : LocallyIntegrableOn u' Ω μ) :
    HasWeakLineDerivOn μ Ω u u' v ↔
      ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        ∫ x, fderiv ℝ φ x v • u x ∂μ = -∫ x, φ x • u' x ∂μ := by
  rw [hasWeakLineDerivOn_iff hu hu']
  refine ⟨fun h φ hφ hφc hφs => ((hasWeakLineDerivOn_iff hu hu').2 h
    ).integral_fderiv_smul_eq_neg_integral_smul hφ hφc hφs, fun h φ hφ hφc hφs => ?_⟩
  simpa only [((hφ.of_le (by simp) : ContDiff ℝ 1 φ).differentiable one_ne_zero _
    ).lineDeriv_eq_fderiv] using h φ (hφ.of_le (by simp)) hφc hφs

end ScalarC1

section Bilinear

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {μ : Measure E} {Ω : Opens E} {u u' : E → F} {v : E}

/-- **Bilinear weak integration by parts against `C¹` fields.** If `u'` is a weak derivative of
`u : E → F` in the direction `v` on `Ω` and `B : G →L[ℝ] F →L[ℝ] H` is a continuous bilinear map
with `G` finite-dimensional, then `∫ B (Dψ(x) v) (u x) ∂μ = -∫ B (ψ x) (u' x) ∂μ` for every `C¹`
compactly supported `ψ : E → G` with `tsupport ψ ⊆ Ω`. -/
theorem HasWeakLineDerivOn.integral_bilin_fderiv_eq_neg
    (h : HasWeakLineDerivOn μ Ω u u' v) (B : G →L[ℝ] F →L[ℝ] H) {ψ : E → G}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
    ∫ x, B (fderiv ℝ ψ x v) (u x) ∂μ = -∫ x, B (ψ x) (u' x) ∂μ := by
  by_cases _hH : CompleteSpace H
  swap
  · simp [integral_of_not_completeSpace _hH]
  let b := Module.finBasis ℝ G
  let c : Fin (Module.finrank ℝ G) → G →L[ℝ] ℝ :=
    fun i => LinearMap.toContinuousLinearMap (b.coord i)
  let φ : Fin (Module.finrank ℝ G) → E → ℝ := fun i x => c i (ψ x)
  have hφ : ∀ i, ContDiff ℝ 1 (φ i) := fun i => (c i).contDiff.comp hψ
  have hφc : ∀ i, HasCompactSupport (φ i) := fun i => hψc.comp_left (c i).map_zero
  have hφs : ∀ i, tsupport (φ i) ⊆ Ω := fun i =>
    (tsupport_comp_subset (c i).map_zero ψ).trans hψs
  have hφd : ∀ i x, fderiv ℝ (φ i) x v = c i (fderiv ℝ ψ x v) := fun i x => by
    have hd : HasFDerivAt (φ i) ((c i).comp (fderiv ℝ ψ x)) x :=
      (c i).hasFDerivAt.comp x (hψ.differentiable one_ne_zero x).hasFDerivAt
    rw [hd.fderiv, ContinuousLinearMap.comp_apply]
  have hw : ∀ i, HasWeakLineDerivOn μ Ω (fun x => B (b i) (u x)) (fun x => B (b i) (u' x)) v :=
    fun i => h.clm_comp (B (b i))
  have hrepr : ∀ (g : G) (w : F), B g w = ∑ i, c i g • B (b i) w := fun g w => by
    conv_lhs => rw [← b.sum_repr g, map_sum, FunLike.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [c, Module.Basis.coord_apply]
  calc ∫ x, B (fderiv ℝ ψ x v) (u x) ∂μ
      = ∫ x, ∑ i, fderiv ℝ (φ i) x v • B (b i) (u x) ∂μ := by
        refine integral_congr_ae (.of_forall fun x => ?_)
        dsimp only
        rw [hrepr]
        exact Finset.sum_congr rfl fun i _ => by rw [hφd]
    _ = ∑ i, ∫ x, fderiv ℝ (φ i) x v • B (b i) (u x) ∂μ :=
        integral_finsetSum _ fun i _ =>
          (hw i).locallyIntegrableOn.integrable_smul_left_of_hasCompactSupport
            (((hφ i).continuous_fderiv one_ne_zero).clm_apply continuous_const)
            ((hφc i).fderiv_apply ℝ v)
            ((tsupport_fderiv_apply_subset ℝ v).trans (hφs i))
    _ = ∑ i, -∫ x, φ i x • B (b i) (u' x) ∂μ :=
        Finset.sum_congr rfl fun i _ =>
          (hw i).integral_fderiv_smul_eq_neg_integral_smul (hφ i) (hφc i) (hφs i)
    _ = -∫ x, B (ψ x) (u' x) ∂μ := by
        rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ =>
          (hw i).locallyIntegrableOn_deriv.integrable_smul_left_of_hasCompactSupport
            (hφ i).continuous (hφc i) (hφs i)]
        congr 1
        exact integral_congr_ae (.of_forall fun x => (hrepr (ψ x) (u' x)).symm)

/-- Set-integral form of `TauCeti.HasWeakLineDerivOn.integral_bilin_fderiv_eq_neg`. -/
theorem HasWeakLineDerivOn.setIntegral_bilin_fderiv_eq_neg
    (h : HasWeakLineDerivOn μ Ω u u' v) (B : G →L[ℝ] F →L[ℝ] H) {ψ : E → G}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
    ∫ x in Ω, B (fderiv ℝ ψ x v) (u x) ∂μ = -∫ x in Ω, B (ψ x) (u' x) ∂μ := by
  have hd : ∀ x ∉ (Ω : Set E), B (fderiv ℝ ψ x v) (u x) = 0 := fun x hx => by
    rw [fderiv_of_notMem_tsupport ℝ fun h' => hx (hψs h')]; simp
  have h0 : ∀ x ∉ (Ω : Set E), B (ψ x) (u' x) = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport fun h' => hx (hψs h')]; simp
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hd,
    setIntegral_eq_integral_of_forall_compl_eq_zero h0,
    h.integral_bilin_fderiv_eq_neg B hψ hψc hψs]

/-- Bundled test-function form of `TauCeti.HasWeakLineDerivOn.integral_bilin_fderiv_eq_neg`,
generalizing `TauCeti.HasWeakLineDerivOn.integral_inner_lineDeriv_eq_neg` from inner product
spaces to arbitrary continuous bilinear maps. -/
theorem HasWeakLineDerivOn.integral_bilin_lineDeriv_eq_neg
    (h : HasWeakLineDerivOn μ Ω u u' v) (B : G →L[ℝ] F →L[ℝ] H) (ψ : 𝓓(Ω, G)) :
    ∫ x, B (lineDeriv ℝ (ψ : E → G) x v) (u x) ∂μ =
      -∫ x, B ((ψ : E → G) x) (u' x) ∂μ := by
  simpa only [(ψ.contDiff.differentiable (by simp) _).lineDeriv_eq_fderiv] using
    h.integral_bilin_fderiv_eq_neg B (ψ.contDiff.of_le (by simp)) ψ.hasCompactSupport
      ψ.tsupport_subset

end Bilinear

section Specializations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]
  {μ : Measure E} {Ω : Opens E} {v : E}

private theorem integrable_clm_apply_of_hasCompactSupport [FiniteDimensional ℝ E]
    {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {w : E → F} (hw : LocallyIntegrableOn w Ω μ) {Ψ : E → F →L[ℝ] H}
    (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) (hΨs : tsupport Ψ ⊆ Ω) :
    Integrable (fun x => Ψ x (w x)) μ := by
  have hsupp : Function.support (fun x => Ψ x (w x)) ⊆ tsupport Ψ :=
    fun x hx => by_contra fun hx' => hx (by simp [image_eq_zero_of_notMem_tsupport hx'])
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  exact (hw.continuousOn_clm_apply Ω.isOpen.isLocallyClosed hΨ.continuousOn
    ).integrableOn_compact_subset hΨs hΨc.isCompact

/-- Scalar-multiplication form of weak integration by parts against `C¹` compactly supported
functions. -/
theorem HasWeakLineDerivOn.integral_fderiv_mul_eq_neg {u u' : E → ℝ}
    (h : HasWeakLineDerivOn μ Ω u u' v) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
    ∫ x, fderiv ℝ φ x v * u x ∂μ = -∫ x, φ x * u' x ∂μ := by
  simpa only [smul_eq_mul] using h.integral_fderiv_smul_eq_neg_integral_smul hφ hφc hφs

/-- Set-integral scalar-multiplication form of weak integration by parts against `C¹` compactly
supported functions. -/
theorem HasWeakLineDerivOn.setIntegral_fderiv_mul_eq_neg {u u' : E → ℝ}
    (h : HasWeakLineDerivOn μ Ω u u' v) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
    ∫ x in Ω, fderiv ℝ φ x v * u x ∂μ = -∫ x in Ω, φ x * u' x ∂μ := by
  simpa only [smul_eq_mul] using h.setIntegral_fderiv_smul_eq_neg_setIntegral_smul hφ hφc hφs

/-- **Operator-valued weak integration by parts.** For a finite-dimensional normed space `F` and
any real normed space `H`, if `u'` is a weak derivative of `u : E → F` in the direction `v` on
`Ω`, then `∫ (DΦ(x) v) (u x) ∂μ = -∫ Φ x (u' x) ∂μ` for every `C¹` compactly supported operator
field `Φ : E → F →L[ℝ] H` with `tsupport Φ ⊆ Ω`. -/
theorem HasWeakLineDerivOn.integral_fderiv_apply_eq_neg
    {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {u u' : E → F} (h : HasWeakLineDerivOn μ Ω u u' v) {Φ : E → F →L[ℝ] H}
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) (hΦs : tsupport Φ ⊆ Ω) :
    ∫ x, fderiv ℝ Φ x v (u x) ∂μ = -∫ x, Φ x (u' x) ∂μ := by
  by_cases _hH : CompleteSpace H
  swap
  · simp [integral_of_not_completeSpace _hH]
  by_cases hfd : FiniteDimensional ℝ E
  swap
  · obtain rfl := (hΦc.eq_zero_or_finiteDimensional ℝ hΦ.continuous).resolve_right hfd; simp
  have hint₁ : Integrable (fun x => fderiv ℝ Φ x v (u x)) μ :=
    integrable_clm_apply_of_hasCompactSupport h.locallyIntegrableOn
      ((hΦ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hΦc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hΦs)
  have hint₂ : Integrable (fun x => Φ x (u' x)) μ :=
    integrable_clm_apply_of_hasCompactSupport h.locallyIntegrableOn_deriv
      hΦ.continuous hΦc hΦs
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun l => ?_
  let L : (F →L[ℝ] H) →L[ℝ] F →L[ℝ] ℝ := ContinuousLinearMap.compL ℝ F H ℝ l
  let ψ : E → F →L[ℝ] ℝ := L ∘ Φ
  have hψ : ContDiff ℝ 1 ψ := L.contDiff.comp hΦ
  have hψc : HasCompactSupport ψ := hΦc.comp_left L.map_zero
  have hψs : tsupport ψ ⊆ Ω := (tsupport_comp_subset L.map_zero Φ).trans hΦs
  have hψd : ∀ x, fderiv ℝ ψ x v (u x) = l (fderiv ℝ Φ x v (u x)) := fun x => by
    have hd : HasFDerivAt ψ (L.comp (fderiv ℝ Φ x)) x :=
      L.hasFDerivAt.comp x (hΦ.differentiable one_ne_zero x).hasFDerivAt
    simp [hd.fderiv, L]
  rw [← l.integral_comp_comm hint₁, map_neg, ← l.integral_comp_comm hint₂]
  simpa only [ContinuousLinearMap.id_apply, hψd, ψ, L, Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply] using
    h.integral_bilin_fderiv_eq_neg (.id ℝ (F →L[ℝ] ℝ)) hψ hψc hψs

/-- Set-integral form of `TauCeti.HasWeakLineDerivOn.integral_fderiv_apply_eq_neg`. -/
theorem HasWeakLineDerivOn.setIntegral_fderiv_apply_eq_neg
    {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {u u' : E → F} (h : HasWeakLineDerivOn μ Ω u u' v) {Φ : E → F →L[ℝ] H}
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) (hΦs : tsupport Φ ⊆ Ω) :
    ∫ x in Ω, fderiv ℝ Φ x v (u x) ∂μ = -∫ x in Ω, Φ x (u' x) ∂μ := by
  have hd : ∀ x ∉ (Ω : Set E), fderiv ℝ Φ x v (u x) = 0 := fun x hx => by
    rw [fderiv_of_notMem_tsupport ℝ fun h' => hx (hΦs h')]; simp
  have h0 : ∀ x ∉ (Ω : Set E), Φ x (u' x) = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport fun h' => hx (hΦs h')]; simp
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hd,
    setIntegral_eq_integral_of_forall_compl_eq_zero h0,
    h.integral_fderiv_apply_eq_neg hΦ hΦc hΦs]

end Specializations

section AdjointFDeriv

/-- **Adjoint integration by parts for weak Fréchet derivatives along a basis.** Pairing a weak
Fréchet derivative `U : E → E →L[ℝ] F` against a `C¹` compactly supported operator functional
`Φ : E → (E →L[ℝ] F) →L[ℝ] H` transfers the derivative onto `Φ` along the directions of any finite
basis `b` of `E`. -/
theorem HasWeakFDerivOn.integral_clm_apply_eq_neg_sum_fderiv
    {E F H ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [Fintype ι] (b : Module.Basis ι ℝ E)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {μ : Measure E} {Ω : Opens E} {u : E → F} {U : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn μ Ω u U) {Φ : E → (E →L[ℝ] F) →L[ℝ] H}
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) (hΦs : tsupport Φ ⊆ Ω) :
    ∫ x, Φ x (U x) ∂μ = -∑ i : ι, ∫ x, fderiv ℝ Φ x (b i)
      ((LinearMap.toContinuousLinearMap (b.coord i)).smulRight (u x)) ∂μ := by
  let L : ι → F →L[ℝ] E →L[ℝ] F := fun i =>
    ContinuousLinearMap.smulRightL ℝ E F (LinearMap.toContinuousLinearMap (b.coord i))
  let R : ι → ((E →L[ℝ] F) →L[ℝ] H) →L[ℝ] F →L[ℝ] H := fun i =>
    (ContinuousLinearMap.compL ℝ F (E →L[ℝ] F) H).flip (L i)
  let Ψ : ι → E → F →L[ℝ] H := fun i => R i ∘ Φ
  have hΨ : ∀ i, ContDiff ℝ 1 (Ψ i) := fun i => (R i).contDiff.comp hΦ
  have hΨc : ∀ i, HasCompactSupport (Ψ i) := fun i => hΦc.comp_left (R i).map_zero
  have hΨs : ∀ i, tsupport (Ψ i) ⊆ Ω := fun i =>
    (tsupport_comp_subset (R i).map_zero Φ).trans hΦs
  have hΨd : ∀ i x, fderiv ℝ (Ψ i) x (b i) (u x) =
      fderiv ℝ Φ x (b i) (L i (u x)) := fun i x => by
    have hd : HasFDerivAt (Ψ i) ((R i).comp (fderiv ℝ Φ x)) x :=
      (R i).hasFDerivAt.comp x (hΦ.differentiable one_ne_zero x).hasFDerivAt
    rw [hd.fderiv]
    simp [R]
  have hexp : ∀ x, Φ x (U x) = ∑ i : ι, Ψ i x (U x (b i)) := fun x => by
    have hU : U x = ∑ i : ι, L i (U x (b i)) := by
      ext w
      calc U x w = U x (∑ i : ι, b.repr w i • b i) := by rw [b.sum_repr]
        _ = (∑ i : ι, L i (U x (b i))) w := by
          rw [map_sum, FunLike.coe_sum, Finset.sum_apply]
          simp [L]
    conv_lhs => rw [hU]
    rw [map_sum]
    simp [Ψ, R]
  have hint : ∀ i : ι, Integrable (fun x => Ψ i x (U x (b i))) μ := fun i =>
    integrable_clm_apply_of_hasCompactSupport (h.hasWeakLineDerivOn (b i)).locallyIntegrableOn_deriv
      (hΨ i).continuous (hΨc i) (hΨs i)
  calc ∫ x, Φ x (U x) ∂μ
      = ∑ i : ι, ∫ x, Ψ i x (U x (b i)) ∂μ := by
        simp_rw [hexp]
        exact integral_finsetSum _ fun i _ => hint i
    _ = -∑ i : ι, ∫ x, fderiv ℝ Φ x (b i) (L i (u x)) ∂μ := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← neg_eq_iff_eq_neg,
          ← (h.hasWeakLineDerivOn (b i)).integral_fderiv_apply_eq_neg (hΨ i) (hΨc i) (hΨs i)]
        exact integral_congr_ae (.of_forall fun x => hΨd i x)

/-- Set-integral form of `TauCeti.HasWeakFDerivOn.integral_clm_apply_eq_neg_sum_fderiv`. -/
theorem HasWeakFDerivOn.setIntegral_clm_apply_eq_neg_sum_fderiv
    {E F H ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [Fintype ι] (b : Module.Basis ι ℝ E)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {μ : Measure E} {Ω : Opens E} {u : E → F} {U : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn μ Ω u U) {Φ : E → (E →L[ℝ] F) →L[ℝ] H}
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) (hΦs : tsupport Φ ⊆ Ω) :
    ∫ x in Ω, Φ x (U x) ∂μ = -∑ i : ι, ∫ x in Ω, fderiv ℝ Φ x (b i)
      ((LinearMap.toContinuousLinearMap (b.coord i)).smulRight (u x)) ∂μ := by
  have h0 : ∀ x ∉ (Ω : Set E), Φ x (U x) = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport fun h' => hx (hΦs h')]; simp
  have hd : ∀ i, ∀ x ∉ (Ω : Set E), fderiv ℝ Φ x (b i)
      ((LinearMap.toContinuousLinearMap (b.coord i)).smulRight (u x)) = 0 := fun i x hx => by
    rw [fderiv_of_notMem_tsupport ℝ fun h' => hx (hΦs h')]; simp
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero h0,
    h.integral_clm_apply_eq_neg_sum_fderiv b hΦ hΦc hΦs]
  congr 1
  exact Finset.sum_congr rfl fun i _ =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hd i)).symm

private theorem toContinuousLinearMap_toBasis_coord
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] (b : OrthonormalBasis ι ℝ E) (i : ι) :
    LinearMap.toContinuousLinearMap (b.toBasis.coord i) = innerSL ℝ (b i) := by
  ext w
  simp [Module.Basis.coord_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]

/-- **Adjoint integration by parts for weak Fréchet derivatives along an orthonormal basis.**
Finite dimensionality of `E` is inferred from the finite orthonormal basis `b`. -/
theorem HasWeakFDerivOn.integral_clm_apply_eq_neg_sum_fderiv_orthonormalBasis
    {E F H ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {μ : Measure E} {Ω : Opens E} {u : E → F} {U : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn μ Ω u U) {Φ : E → (E →L[ℝ] F) →L[ℝ] H}
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) (hΦs : tsupport Φ ⊆ Ω) :
    ∫ x, Φ x (U x) ∂μ =
      -∑ i : ι, ∫ x, fderiv ℝ Φ x (b i) ((innerSL ℝ (b i)).smulRight (u x)) ∂μ := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b.toBasis
  simpa only [OrthonormalBasis.coe_toBasis, toContinuousLinearMap_toBasis_coord b] using
    h.integral_clm_apply_eq_neg_sum_fderiv b.toBasis hΦ hΦc hΦs

/-- Set-integral form of
`TauCeti.HasWeakFDerivOn.integral_clm_apply_eq_neg_sum_fderiv_orthonormalBasis`. -/
theorem HasWeakFDerivOn.setIntegral_clm_apply_eq_neg_sum_fderiv_orthonormalBasis
    {E F H ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {μ : Measure E} {Ω : Opens E} {u : E → F} {U : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn μ Ω u U) {Φ : E → (E →L[ℝ] F) →L[ℝ] H}
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) (hΦs : tsupport Φ ⊆ Ω) :
    ∫ x in Ω, Φ x (U x) ∂μ =
      -∑ i : ι, ∫ x in Ω, fderiv ℝ Φ x (b i) ((innerSL ℝ (b i)).smulRight (u x)) ∂μ := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b.toBasis
  simpa only [OrthonormalBasis.coe_toBasis, toContinuousLinearMap_toBasis_coord b] using
    h.setIntegral_clm_apply_eq_neg_sum_fderiv b.toBasis hΦ hΦc hΦs

end AdjointFDeriv

end TauCeti
