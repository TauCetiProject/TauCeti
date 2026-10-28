/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Strip.Basic
public import TauCeti.Geometry.Symplectic.JHolomorphic.InteriorEstimate
import TauCeti.Analysis.Sobolev.Poincare.TransverseBoundary
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Coercivity of perturbed Cauchy--Riemann operators on the strip

Small uniform perturbations of a constant compatible complex structure preserve the strip
`L²` derivative estimate with linear isotropic boundary conditions. When the two boundary
subspaces are disjoint, the transverse-boundary Poincaré estimate also controls the map itself.
The resulting coercivity constant is independent of the varying principal coefficient.
Sufficiently small zeroth-order terms preserve this full estimate, with uniform constants.

These are estimates on compactly supported smooth maps on the closed strip, in the caller's
inner product. Coefficients are constrained only on the intersection of that strip with the
map's support; they need not themselves be almost complex structures. No Sobolev completion or
Fredholm assertion is made.

The proof uses the vanishing-area identity in
`SymplecticForm.integral_symplecticForm_fderiv_strip_eq_zero` and the absorption estimate
`TauCeti.integral_norm_partialDeriv_sq_le_of_integral_symplecticForm_eq_zero`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix B (linear totally real boundary estimates and perturbation of the principal part).
-/

public section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {u : ℝ × ℝ → V}
  {A : ℝ × ℝ → V →L[ℝ] V} {L₀ L₁ : Submodule ℝ V}

/-- The strip derivative estimate is stable under a principal coefficient within one half
of a fixed compatible complex structure. The isotropic boundary subspaces may intersect. -/
theorem integral_norm_partialDeriv_sq_strip_le_of_close_complexStructure
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hA : ContinuousOn A (tsupport u ∩ (univ ×ˢ Icc (0 : ℝ) 1)))
    (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u)
    (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁)
    (hbottom : ∀ s, u (s, 0) ∈ L₀) (htop : ∀ s, u (s, 1) ∈ L₁)
    (hclose : ∀ z ∈ tsupport u ∩ (univ ×ˢ Icc (0 : ℝ) 1),
      ∀ v, ‖A z v - J v‖ ≤ (1 / 2 : ℝ) * ‖v‖) :
    ∫ z in univ ×ˢ Icc (0 : ℝ) 1,
        (‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ u z stdComplexLineImag‖ ^ 2) ≤
      4 * ∫ z in univ ×ˢ Icc (0 : ℝ) 1,
        ‖fderiv ℝ u z stdComplexLineReal +
          A z (fderiv ℝ u z stdComplexLineImag)‖ ^ 2 := by
  let S : Set (ℝ × ℝ) := univ ×ˢ Icc (0 : ℝ) 1
  let D := fun z ↦ fderiv ℝ u z stdComplexLineReal +
    A z (fderiv ℝ u z stdComplexLineImag)
  have hS : IsClosed S := isClosed_univ.prod isClosed_Icc
  have hdu := hu.continuous_fderiv (by norm_num)
  have hD : ContinuousOn D (tsupport u ∩ S) :=
    (hdu.clm_apply continuous_const).continuousOn.add
      (hA.clm_apply (hdu.clm_apply continuous_const).continuousOn)
  have hDi : IntegrableOn (fun z ↦ ‖D z‖ ^ 2) S := by
    have hi : IntegrableOn (fun z ↦ ‖D z‖ ^ 2) (tsupport u ∩ S) :=
      hD.norm.pow 2 |>.integrableOn_compact (hc.inter_right hS)
    exact hi.of_forall_sdiff_eq_zero hS.measurableSet fun z hz ↦ by
      have hzsupport : z ∉ tsupport u := fun h ↦ hz.2 ⟨h, hz.1⟩
      simp [D, fderiv_of_notMem_tsupport ℝ hzsupport]
  refine integral_norm_partialDeriv_sq_le_of_integral_symplecticForm_eq_zero
    hg (hu.of_le (by norm_num)) hc hDi
    (ω.integral_symplecticForm_fderiv_strip_eq_zero hu hc hL₀ hL₁ hbottom htop) ?_
  filter_upwards [ae_restrict_mem hS.measurableSet] with z hz hzs
  exact hclose z ⟨hzs, hz⟩

/-- Disjoint isotropic boundary subspaces give a uniform full `L²` coercivity estimate for
all principal coefficients within one half of a fixed compatible complex structure. -/
theorem exists_integral_norm_sq_add_partialDeriv_sq_strip_le_mul_of_close_complexStructure
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁) (hL : Disjoint L₀ L₁) :
    ∃ C > 0, ∀ (A : ℝ × ℝ → V →L[ℝ] V) (u : ℝ × ℝ → V),
      ContinuousOn A (tsupport u ∩ (univ ×ˢ Icc (0 : ℝ) 1)) →
      ContDiff ℝ 2 u → HasCompactSupport u →
      (∀ s, u (s, 0) ∈ L₀) → (∀ s, u (s, 1) ∈ L₁) →
      (∀ z ∈ tsupport u ∩ (univ ×ˢ Icc (0 : ℝ) 1),
        ∀ v, ‖A z v - J v‖ ≤ (1 / 2 : ℝ) * ‖v‖) →
      (∫ z in univ ×ˢ Icc (0 : ℝ) 1,
        ‖u z‖ ^ 2 + (‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ u z stdComplexLineImag‖ ^ 2)) ≤
        C * ∫ z in univ ×ˢ Icc (0 : ℝ) 1,
          ‖fderiv ℝ u z stdComplexLineReal +
            A z (fderiv ℝ u z stdComplexLineImag)‖ ^ 2 := by
  obtain ⟨C, hC, hPoincare⟩ :=
    L₀.exists_integral_norm_sq_le_mul_integral_norm_fderiv_sq_of_disjoint L₁ hL
  refine ⟨4 * (C + 1), by positivity, fun A u hA hu hc hbottom htop hclose ↦ ?_⟩
  have hdu := hu.continuous_fderiv (by norm_num)
  have hi := hu.continuous.integrable_norm_sq_of_hasCompactSupport (μ := volume) hc
  have hsi := (hdu.clm_apply continuous_const).integrable_norm_sq_of_hasCompactSupport (μ := volume)
    (hc.fderiv_apply ℝ stdComplexLineReal)
  have hti := (hdu.clm_apply continuous_const).integrable_norm_sq_of_hasCompactSupport (μ := volume)
    (hc.fderiv_apply ℝ stdComplexLineImag)
  have he := hsi.fun_add hti
  have hvalue := hPoincare u (hu.of_le (by norm_num)) hc hbottom htop
  rw [← stdComplexLineImag_eq] at hvalue
  have htbound := integral_mono
    (hti.integrableOn (s := univ ×ˢ Icc (0 : ℝ) 1)) he.integrableOn
    (fun z ↦ le_add_of_nonneg_left (sq_nonneg ‖fderiv ℝ u z stdComplexLineReal‖))
  have henergy := integral_norm_partialDeriv_sq_strip_le_of_close_complexStructure
    hg hA hu hc hL₀ hL₁ hbottom htop hclose
  rw [integral_add hi.integrableOn he.integrableOn]
  calc
    _ ≤ (C + 1) * ∫ z in univ ×ˢ Icc (0 : ℝ) 1,
        ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ u z stdComplexLineImag‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left htbound hC.le]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ C + 1)]

/-- Small zeroth-order terms preserve full strip coercivity. The constants depend only on
the fixed compatible structure and the disjoint isotropic boundary subspaces, uniformly over
both coefficient fields. -/
theorem exists_integral_norm_sq_add_partialDeriv_sq_strip_le_mul_of_small_perturbation
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁) (hL : Disjoint L₀ L₁) :
    ∃ ε > 0, ∃ C > 0, ∀ (A B : ℝ × ℝ → V →L[ℝ] V) (u : ℝ × ℝ → V),
      ContinuousOn A (tsupport u ∩ (univ ×ˢ Icc (0 : ℝ) 1)) →
      ContinuousOn B (tsupport u ∩ (univ ×ˢ Icc (0 : ℝ) 1)) →
      ContDiff ℝ 2 u → HasCompactSupport u →
      (∀ s, u (s, 0) ∈ L₀) → (∀ s, u (s, 1) ∈ L₁) →
      (∀ z ∈ tsupport u ∩ (univ ×ˢ Icc (0 : ℝ) 1),
        ∀ v, ‖A z v - J v‖ ≤ (1 / 2 : ℝ) * ‖v‖) →
      (∀ z ∈ tsupport u ∩ (univ ×ˢ Icc (0 : ℝ) 1), ∀ v, ‖B z v‖ ≤ ε * ‖v‖) →
      (∫ z in univ ×ˢ Icc (0 : ℝ) 1,
        ‖u z‖ ^ 2 + (‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ u z stdComplexLineImag‖ ^ 2)) ≤
        C * ∫ z in univ ×ˢ Icc (0 : ℝ) 1,
          ‖fderiv ℝ u z stdComplexLineReal +
            A z (fderiv ℝ u z stdComplexLineImag) + B z (u z)‖ ^ 2 := by
  obtain ⟨C, hC, hprincipal⟩ :=
    exists_integral_norm_sq_add_partialDeriv_sq_strip_le_mul_of_close_complexStructure
      hg hL₀ hL₁ hL
  let ε := 1 / (4 * (C + 1))
  have hε : 0 < ε := by positivity
  have hεC : 4 * C * ε ^ 2 ≤ 1 := by
    have heq : ε * (4 * (C + 1)) = 1 := by dsimp [ε]; field_simp
    have hε₁ : ε ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ε]
  refine ⟨ε, hε, 4 * C, by positivity, fun A B u hA hB hu hc hbottom htop hclose hsmall ↦ ?_⟩
  let S : Set (ℝ × ℝ) := univ ×ˢ Icc (0 : ℝ) 1
  let D := fun z ↦ fderiv ℝ u z stdComplexLineReal +
    A z (fderiv ℝ u z stdComplexLineImag)
  let F := fun z ↦ D z + B z (u z)
  let E := fun z ↦ ‖u z‖ ^ 2 + (‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 +
    ‖fderiv ℝ u z stdComplexLineImag‖ ^ 2)
  have hS : IsClosed S := isClosed_univ.prod isClosed_Icc
  have hdu := hu.continuous_fderiv (by norm_num)
  have hD : ContinuousOn D (tsupport u ∩ S) :=
    (hdu.clm_apply continuous_const).continuousOn.add
      (hA.clm_apply (hdu.clm_apply continuous_const).continuousOn)
  have hBu : ContinuousOn (fun z ↦ B z (u z)) (tsupport u ∩ S) :=
    hB.clm_apply hu.continuous.continuousOn
  -- All defect terms vanish off the compact support, including the zeroth-order term.
  have hFi : IntegrableOn (fun z ↦ ‖F z‖ ^ 2) S := by
    have hi : IntegrableOn (fun z ↦ ‖F z‖ ^ 2) (tsupport u ∩ S) :=
      (hD.add hBu).norm.pow 2 |>.integrableOn_compact (hc.inter_right hS)
    apply hi.of_forall_sdiff_eq_zero hS.measurableSet
    intro z hz
    have hzsupport : z ∉ tsupport u := fun h ↦ hz.2 ⟨h, hz.1⟩
    simp [F, D, fderiv_of_notMem_tsupport ℝ hzsupport,
      image_eq_zero_of_notMem_tsupport hzsupport]
  have hBi : IntegrableOn (fun z ↦ ‖-B z (u z)‖ ^ 2) S := by
    have hi : IntegrableOn (fun z ↦ ‖-B z (u z)‖ ^ 2) (tsupport u ∩ S) :=
      hBu.neg.norm.pow 2 |>.integrableOn_compact (hc.inter_right hS)
    apply hi.of_forall_sdiff_eq_zero hS.measurableSet
    intro z hz
    have hzsupport : z ∉ tsupport u := fun h ↦ hz.2 ⟨h, hz.1⟩
    simp [image_eq_zero_of_notMem_tsupport hzsupport]
  have hUi := hu.continuous.integrable_norm_sq_of_hasCompactSupport (μ := volume) hc
  have hBbound : (∫ z in S, ‖-B z (u z)‖ ^ 2) ≤ ε ^ 2 * ∫ z in S, ‖u z‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae hBi (hUi.integrableOn.const_mul _)
    filter_upwards [ae_restrict_mem hS.measurableSet] with z hz
    by_cases hzs : z ∈ tsupport u
    · have h := hsmall z ⟨hzs, hz⟩ (u z)
      simpa [norm_neg, mul_pow] using
        pow_le_pow_left₀ (norm_nonneg (B z (u z))) h 2
    · simp [image_eq_zero_of_notMem_tsupport hzs]
  have hdefect : (∫ z in S, ‖D z‖ ^ 2) ≤
      2 * (∫ z in S, ‖F z‖ ^ 2) + 2 * ε ^ 2 * (∫ z in S, ‖u z‖ ^ 2) := by
    have h := TauCeti.MeasureTheory.setIntegral_norm_add_sq_le hFi hBi
    simp only [F, add_neg_cancel_right] at h
    dsimp only [F]
    nlinarith only [h, hBbound]
  have hvalue : (∫ z in S, ‖u z‖ ^ 2) ≤ ∫ z in S, E z := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _) ?_
      (Filter.Eventually.of_forall fun z ↦ le_add_of_nonneg_right
        (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    exact (hUi.fun_add
      (((hdu.clm_apply continuous_const).integrable_norm_sq_of_hasCompactSupport (μ := volume)
        (hc.fderiv_apply ℝ stdComplexLineReal)).fun_add
      ((hdu.clm_apply continuous_const).integrable_norm_sq_of_hasCompactSupport (μ := volume)
        (hc.fderiv_apply ℝ stdComplexLineImag)))).integrableOn
  have hmain := hprincipal A u hA hu hc hbottom htop hclose
  have hEpos : 0 ≤ ∫ z in S, E z := integral_nonneg fun z ↦ by dsimp [E]; positivity
  -- Absorb the small value term into the full energy on the left.
  have hscaled := mul_le_mul_of_nonneg_left hdefect hC.le
  have hsmallvalue := mul_le_mul_of_nonneg_left hvalue (by positivity : 0 ≤ 2 * C * ε ^ 2)
  have habsorb := mul_le_mul_of_nonneg_right hεC hEpos
  dsimp only [S, D, F, E] at hmain hscaled hsmallvalue habsorb ⊢
  nlinarith only [hmain, hscaled, hsmallvalue, habsorb]

end TauCeti
