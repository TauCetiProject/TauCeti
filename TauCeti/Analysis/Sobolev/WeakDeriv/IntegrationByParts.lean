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
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Coordinates
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Weak integration by parts against `C¹` and operator-valued test fields

Extends weak integration by parts from `𝓓(Ω, ℝ)` to compactly supported `C¹` scalar test functions
(`TauCeti.HasWeakLineDerivOn.integral_fderiv_smul_eq_neg_integral_smul`,
`TauCeti.hasWeakLineDerivOn_iff_contDiff_one`), continuous bilinear pairings
(`TauCeti.HasWeakLineDerivOn.integral_bilin_fderiv_eq_neg`), operator-valued fields
(`TauCeti.HasWeakLineDerivOn.integral_fderiv_apply_eq_neg`), and adjoint weak Fréchet derivatives
(`TauCeti.HasWeakFDerivOn.setIntegral_clm_apply_eq_neg_sum_fderiv_orthonormalBasis`), providing the
single-step weak integration-by-parts identities iterated on `W^{k,p}`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2.1.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §3.1.
-/

public section

namespace TauCeti

open _root_.MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions InnerProductSpace

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} {Ω : Opens E} {u u' : E → F} {v : E}

/-- **Weak integration by parts against `C¹` functions.** -/
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
  have huK := h.locallyIntegrableOn.integrableOn_compact_subset hδΩ hK'
  have hu'K := h.locallyIntegrableOn_deriv.integrableOn_compact_subset hδΩ hK'
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
  have hb1 := MeasureTheory.norm_integral_smul_sub_le hK' huK
    (f := fun x => fderiv ℝ φ x v) (g := fun x => fderiv ℝ (ψ : E → ℝ) x v)
    (((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn)
    (((ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn)
    ((tsupport_fderiv_apply_subset ℝ v).trans hφK') ((tsupport_fderiv_apply_subset ℝ v).trans hψK')
    fun x _ => by
      rw [dist_eq_norm, ← sub_apply (fderiv ℝ φ x) (fderiv ℝ (ψ : E → ℝ) x) v]
      exact ((fderiv ℝ φ x - fderiv ℝ (ψ : E → ℝ) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (by simpa [dist_comm, dist_eq_norm] using (hψ x).2)
          (norm_nonneg v))
  have hb2 := MeasureTheory.norm_integral_smul_sub_le hK' hu'K hφ.continuous.continuousOn
    ψ.contDiff.continuous.continuousOn hφK' hψK' fun x _ => by simpa [dist_comm] using (hψ x).1
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
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hx => by
      rw [fderiv_of_notMem_tsupport ℝ (hx <| hφs ·)]; simp,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hx => by
      rw [image_eq_zero_of_notMem_tsupport (hx <| hφs ·), zero_smul],
    h.integral_fderiv_smul_eq_neg_integral_smul hφ hφc hφs]

/-- Weak directional differentiability is equivalent to integration by parts against all `C¹`
functions compactly supported in `Ω`. -/
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

/-- **Bilinear weak integration by parts against `C¹` fields.** -/
theorem HasWeakLineDerivOn.integral_bilin_fderiv_eq_neg
    {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (h : HasWeakLineDerivOn μ Ω u u' v) (B : G →L[ℝ] F →L[ℝ] H) {ψ : E → G}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
    ∫ x, B (fderiv ℝ ψ x v) (u x) ∂μ = -∫ x, B (ψ x) (u' x) ∂μ := by
  by_cases _hH : CompleteSpace H
  swap
  · simp [integral_of_not_completeSpace _hH]
  let b := Module.finBasis ℝ G
  let c : Fin (Module.finrank ℝ G) → G →L[ℝ] ℝ := fun i => (b.coord i).toContinuousLinearMap
  let φ : Fin (Module.finrank ℝ G) → E → ℝ := fun i => c i ∘ ψ
  have hφ : ∀ i, ContDiff ℝ 1 (φ i) := fun i => (c i).contDiff.comp hψ
  have hφc : ∀ i, HasCompactSupport (φ i) := fun i => hψc.comp_left (c i).map_zero
  have hφs : ∀ i, tsupport (φ i) ⊆ Ω := fun i => (tsupport_comp_subset (c i).map_zero ψ).trans hψs
  have hφd : ∀ i x, fderiv ℝ (φ i) x v = c i (fderiv ℝ ψ x v) := fun i x => by
    rw [((c i).hasFDerivAt.comp x (hψ.differentiable one_ne_zero x).hasFDerivAt).fderiv,
      ContinuousLinearMap.comp_apply]
  have hw : ∀ i, HasWeakLineDerivOn μ Ω (fun x => B (b i) (u x)) (fun x => B (b i) (u' x)) v :=
    fun i => h.clm_comp (B (b i))
  have hrepr : ∀ (g : G) (w : F), B g w = ∑ i, c i g • B (b i) w := fun g w => by
    conv_lhs => rw [← b.sum_repr g, map_sum, FunLike.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun _ _ => by simp [c, Module.Basis.coord_apply]
  calc ∫ x, B (fderiv ℝ ψ x v) (u x) ∂μ
      = ∫ x, ∑ i, fderiv ℝ (φ i) x v • B (b i) (u x) ∂μ :=
        integral_congr_ae (.of_forall fun _ => by
          dsimp only; rw [hrepr]; exact Finset.sum_congr rfl fun i _ => by rw [hφd])
    _ = ∑ i, ∫ x, fderiv ℝ (φ i) x v • B (b i) (u x) ∂μ :=
        integral_finsetSum _ fun i _ =>
          (hw i).locallyIntegrableOn.integrable_smul_left_of_hasCompactSupport
            (((hφ i).continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn
            ((hφc i).fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans (hφs i))
    _ = ∑ i, -∫ x, φ i x • B (b i) (u' x) ∂μ := Finset.sum_congr rfl fun i _ =>
        (hw i).integral_fderiv_smul_eq_neg_integral_smul (hφ i) (hφc i) (hφs i)
    _ = -∫ x, B (ψ x) (u' x) ∂μ := by
        rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ =>
          (hw i).locallyIntegrableOn_deriv.integrable_smul_left_of_hasCompactSupport
            (hφ i).continuous.continuousOn (hφc i) (hφs i)]
        congr 1; exact integral_congr_ae (.of_forall fun x => (hrepr (ψ x) (u' x)).symm)

/-- Set-integral scalar-multiplication form of weak integration by parts against `C¹` functions. -/
theorem HasWeakLineDerivOn.setIntegral_fderiv_mul_eq_neg {u u' : E → ℝ}
    (h : HasWeakLineDerivOn μ Ω u u' v) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
    ∫ x in Ω, fderiv ℝ φ x v * u x ∂μ = -∫ x in Ω, φ x * u' x ∂μ := by
  simpa only [smul_eq_mul] using h.setIntegral_fderiv_smul_eq_neg_setIntegral_smul hφ hφc hφs

/-- **Operator-valued weak integration by parts.** -/
theorem HasWeakLineDerivOn.integral_fderiv_apply_eq_neg [FiniteDimensional ℝ F]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (h : HasWeakLineDerivOn μ Ω u u' v) {Φ : E → F →L[ℝ] H}
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) (hΦs : tsupport Φ ⊆ Ω) :
    ∫ x, fderiv ℝ Φ x v (u x) ∂μ = -∫ x, Φ x (u' x) ∂μ := by
  by_cases _hH : CompleteSpace H
  swap
  · simp [integral_of_not_completeSpace _hH]
  have hint₁ := h.locallyIntegrableOn.integrable_clm_apply_of_hasCompactSupport
    ((hΦ.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn
    (hΦc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hΦs)
  have hint₂ := h.locallyIntegrableOn_deriv.integrable_clm_apply_of_hasCompactSupport
    hΦ.continuous.continuousOn hΦc hΦs
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun l => ?_
  let L := ContinuousLinearMap.compL ℝ F H ℝ l
  have hψd : ∀ x, fderiv ℝ (L ∘ Φ) x v (u x) = l (fderiv ℝ Φ x v (u x)) := fun x => by
    rw [(L.hasFDerivAt.comp x (hΦ.differentiable one_ne_zero x).hasFDerivAt).fderiv]; simp [L]
  rw [← l.integral_comp_comm hint₁, map_neg, ← l.integral_comp_comm hint₂]
  simpa only [ContinuousLinearMap.id_apply, hψd, L, Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply] using
    h.integral_bilin_fderiv_eq_neg (.id ℝ (F →L[ℝ] ℝ)) (L.contDiff.comp hΦ)
      (hΦc.comp_left L.map_zero) ((tsupport_comp_subset L.map_zero Φ).trans hΦs)

/-- Set-integral form of `TauCeti.HasWeakLineDerivOn.integral_fderiv_apply_eq_neg`. -/
theorem HasWeakLineDerivOn.setIntegral_fderiv_apply_eq_neg [FiniteDimensional ℝ F]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (h : HasWeakLineDerivOn μ Ω u u' v) {Φ : E → F →L[ℝ] H}
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) (hΦs : tsupport Φ ⊆ Ω) :
    ∫ x in Ω, fderiv ℝ Φ x v (u x) ∂μ = -∫ x in Ω, Φ x (u' x) ∂μ := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hx => by
      rw [fderiv_of_notMem_tsupport ℝ (hx <| hΦs ·)]; simp,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hx => by
      rw [image_eq_zero_of_notMem_tsupport (hx <| hΦs ·)]; simp,
    h.integral_fderiv_apply_eq_neg hΦ hΦc hΦs]

end

section AdjointFDeriv

variable {E F H ι : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **Adjoint integration by parts for weak Fréchet derivatives along a basis.** -/
theorem HasWeakFDerivOn.integral_clm_apply_eq_neg_sum_fderiv
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (b : Module.Basis ι ℝ E)
    {μ : Measure E} {Ω : Opens E} {u : E → F} {U : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn μ Ω u U) {Φ : E → (E →L[ℝ] F) →L[ℝ] H}
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) (hΦs : tsupport Φ ⊆ Ω) :
    ∫ x, Φ x (U x) ∂μ = -∑ i : ι, ∫ x, fderiv ℝ Φ x (b i)
      ((LinearMap.toContinuousLinearMap (b.coord i)).smulRight (u x)) ∂μ := by
  let L : ι → F →L[ℝ] E →L[ℝ] F := fun i =>
    ContinuousLinearMap.smulRightL ℝ ℝ ℝ E F (b.coord i).toContinuousLinearMap
  let R : ι → ((E →L[ℝ] F) →L[ℝ] H) →L[ℝ] F →L[ℝ] H := fun i =>
    (ContinuousLinearMap.compL ℝ F (E →L[ℝ] F) H).flip (L i)
  let Ψ : ι → E → F →L[ℝ] H := fun i => R i ∘ Φ
  have hΨ : ∀ i, ContDiff ℝ 1 (Ψ i) := fun i => (R i).contDiff.comp hΦ
  have hΨc : ∀ i, HasCompactSupport (Ψ i) := fun i => hΦc.comp_left (R i).map_zero
  have hΨs : ∀ i, tsupport (Ψ i) ⊆ Ω := fun i => (tsupport_comp_subset (R i).map_zero Φ).trans hΦs
  have hΨd : ∀ i x, fderiv ℝ (Ψ i) x (b i) (u x) = fderiv ℝ Φ x (b i) (L i (u x)) := fun i x => by
    rw [((R i).hasFDerivAt.comp x (hΦ.differentiable one_ne_zero x).hasFDerivAt).fderiv]; simp [R]
  have hexp : ∀ x, Φ x (U x) = ∑ i : ι, Ψ i x (U x (b i)) := fun x => by
    have hU : U x = ∑ i : ι, L i (U x (b i)) := by
      ext w
      conv_lhs => rw [← b.sum_repr w, map_sum]
      rw [FunLike.coe_sum, Finset.sum_apply]; simp [L]
    conv_lhs => rw [hU]
    rw [map_sum]; simp [Ψ, R]
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ =>
      ((h.hasWeakLineDerivOn (b i)).locallyIntegrableOn_deriv
        ).integrable_clm_apply_of_hasCompactSupport (hΨ i).continuous.continuousOn (hΨc i) (hΨs i),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← neg_eq_iff_eq_neg,
    ← (h.hasWeakLineDerivOn (b i)).integral_fderiv_apply_eq_neg (hΨ i) (hΨc i) (hΨs i)]
  exact integral_congr_ae (.of_forall fun x => hΨd i x)

/-- Set-integral form of `TauCeti.HasWeakFDerivOn.integral_clm_apply_eq_neg_sum_fderiv`. -/
theorem HasWeakFDerivOn.setIntegral_clm_apply_eq_neg_sum_fderiv
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (b : Module.Basis ι ℝ E)
    {μ : Measure E} {Ω : Opens E} {u : E → F} {U : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn μ Ω u U) {Φ : E → (E →L[ℝ] F) →L[ℝ] H}
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) (hΦs : tsupport Φ ⊆ Ω) :
    ∫ x in Ω, Φ x (U x) ∂μ = -∑ i : ι, ∫ x in Ω, fderiv ℝ Φ x (b i)
      ((LinearMap.toContinuousLinearMap (b.coord i)).smulRight (u x)) ∂μ := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hx => by
      rw [image_eq_zero_of_notMem_tsupport (hx <| hΦs ·)]; simp,
    h.integral_clm_apply_eq_neg_sum_fderiv b hΦ hΦc hΦs]
  congr 1; exact Finset.sum_congr rfl fun _ _ =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hx => by
      rw [fderiv_of_notMem_tsupport ℝ (hx <| hΦs ·)]; simp).symm

/-- **Adjoint integration by parts for weak Fréchet derivatives along an orthonormal basis.** -/
theorem HasWeakFDerivOn.setIntegral_clm_apply_eq_neg_sum_fderiv_orthonormalBasis
    [InnerProductSpace ℝ E] (b : OrthonormalBasis ι ℝ E)
    {μ : Measure E} {Ω : Opens E} {u : E → F} {U : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn μ Ω u U) {Φ : E → (E →L[ℝ] F) →L[ℝ] H}
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) (hΦs : tsupport Φ ⊆ Ω) :
    ∫ x in Ω, Φ x (U x) ∂μ =
      -∑ i : ι, ∫ x in Ω, fderiv ℝ Φ x (b i) ((innerSL ℝ (b i)).smulRight (u x)) ∂μ := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b.toBasis
  simpa only [OrthonormalBasis.coe_toBasis, b.toContinuousLinearMap_toBasis_coord] using
    h.setIntegral_clm_apply_eq_neg_sum_fderiv b.toBasis hΦ hΦc hΦs

end AdjointFDeriv

end TauCeti
