/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.CompactSupport
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
import TauCeti.Analysis.Sobolev.Poincare.TransverseBoundary
import TauCeti.Analysis.Calculus.FDeriv.Submodule
import TauCeti.Geometry.Symplectic.CompatibleMetric
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.DivergenceTheorem

/-!
# The Cauchy--Riemann energy identity with linear isotropic boundary

The symplectic area of a smooth map on a rectangle vanishes when its vertical sides are zero
and its horizontal boundary curves lie in fixed linear isotropic subspaces. Consequently a
compactly supported smooth map on the strip with these boundary conditions satisfies the same
homogeneous energy identity as a compactly supported map on the plane. In a compatible inner
product this controls both directional derivatives by the Cauchy--Riemann defect, without a
transversality hypothesis on the two boundary subspaces.

When the boundary subspaces are disjoint, a transverse-boundary Poincaré estimate also controls
the map values. The resulting estimate bounds the full value and directional derivative energy
by the defect with a constant independent of the map. This is an estimate on the smooth compactly
supported core; no Sobolev completion or Fredholm assertion is made here.

The boundary calculation uses
`ContinuousLinearMap.integral_bilinear_fderiv_sub_prod_Icc`.

The argument is the energy identity and linear Lagrangian boundary integration by parts of
D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix B.
-/

public section

namespace TauCeti

open MeasureTheory Set Topology
open scoped RealInnerProductSpace

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}
variable {u : ℝ × ℝ → V} {L₀ L₁ : Submodule ℝ V}

omit [FiniteDimensional ℝ V] in
private lemma alternating_pairing_eq_two_mul (v w : V) :
    ω v w - ω w v = 2 * ω v w := by
  rw [← ω.neg_eq v w]
  ring

/-- The area of a rectangle vanishes for a map whose vertical sides are zero and whose two
horizontal boundary curves lie in fixed linear isotropic subspaces. -/
theorem integral_symplecticForm_fderiv_prod_Icc_eq_zero
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hu : ∀ z ∈ Icc a b ×ˢ Icc c d, ContDiffAt ℝ 2 u z)
    (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁)
    (hbottom : ∀ s ∈ Icc a b, u (s, c) ∈ L₀)
    (htop : ∀ s ∈ Icc a b, u (s, d) ∈ L₁)
    (hleft : ∀ t ∈ Icc c d, u (a, t) = 0)
    (hright : ∀ t ∈ Icc c d, u (b, t) = 0) :
    ∫ z in Icc a b ×ˢ Icc c d,
      ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) = 0 := by
  let B := ω.toBilinForm.toContinuousBilinearMap
  have hB (v w : V) : B v w = ω v w := by simp [B]
  -- Along the interior of either horizontal side, differentiating the boundary condition
  -- keeps the tangent vector in the closed isotropic subspace.
  have hhorizontal {e : ℝ} (he : e ∈ Icc c d) {L : Submodule ℝ V}
      (hL : ω.IsIsotropic L) (hline : ∀ s ∈ Icc a b, u (s, e) ∈ L) :
      (∫ s in a..b, B (u (s, e)) (fderiv ℝ u (s, e) stdComplexLineReal)) = 0 := by
    calc
      _ = ∫ _s in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hab
        intro s hs
        have hp : HasDerivAt (fun r : ℝ ↦ ((r, e) : ℝ × ℝ)) stdComplexLineReal s := by
          rw [stdComplexLineReal_eq]
          exact (hasDerivAt_id s).prodMk (hasDerivAt_const s e)
        have hd := ((hu (s, e) ⟨Ioo_subset_Icc_self hs, he⟩).differentiableAt
          (by norm_num)).hasFDerivAt.comp_hasDerivAt s hp
        have htangent : fderiv ℝ u (s, e) stdComplexLineReal ∈ L := by
          have hmem : ∀ᶠ r in 𝓝 s, u (r, e) - u (s, e) ∈ L := by
            filter_upwards [Icc_mem_nhds hs.1 hs.2] with r hr
            exact L.sub_mem (hline r hr) (hline s (Ioo_subset_Icc_self hs))
          simpa using hd.hasFDerivAt.apply_mem_of_eventually_sub_mem
            L.closed_of_finiteDimensional hmem (1 : ℝ)
        simpa only [hB] using
          isIsotropic_iff.mp hL _ (hline s (Ioo_subset_Icc_self hs)) _ htangent
      _ = 0 := intervalIntegral.integral_zero
  have hvertical {s : ℝ} (hline : ∀ t ∈ Icc c d, u (s, t) = 0) :
      (∫ t in c..d, B (u (s, t)) (fderiv ℝ u (s, t) stdComplexLineImag)) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with t ht
    simp [hline t (by simpa [uIcc_of_le hcd] using uIoc_subset_uIcc ht)]
  -- All four boundary terms in Green's formula vanish.
  have hgreen := B.integral_bilinear_fderiv_sub_prod_Icc
    (a := (a, c)) (b := (b, d)) ⟨hab, hcd⟩ (by rw [← Icc_prod_Icc]; exact hu)
  rw [← Icc_prod_Icc, ← stdComplexLineReal_eq, ← stdComplexLineImag_eq,
    hhorizontal ⟨le_rfl, hcd⟩ hL₀ hbottom, hhorizontal ⟨hcd, le_rfl⟩ hL₁ htop,
    hvertical hleft, hvertical hright] at hgreen
  -- Antisymmetry identifies the interior alternating pairing with twice the area density.
  simp only [hB, alternating_pairing_eq_two_mul, integral_const_mul] at hgreen
  linarith

/-- The symplectic area of a compactly supported smooth map on the strip is zero when its
boundary curves lie in fixed linear isotropic subspaces. -/
theorem integral_symplecticForm_fderiv_strip_eq_zero
    (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u)
    (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁)
    (hbottom : ∀ s, u (s, 0) ∈ L₀) (htop : ∀ s, u (s, 1) ∈ L₁) :
    ∫ z in univ ×ˢ Icc (0 : ℝ) 1,
      ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) = 0 := by
  obtain ⟨R, hR, hsupp⟩ := hc.isBounded.subset_ball_lt 0 (0 : ℝ × ℝ)
  have houtside {z : ℝ × ℝ} (hz : R ≤ |z.1|) : z ∉ tsupport u := by
    intro hzmem
    have hnorm : ‖z‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hsupp hzmem
    have hfst : |z.1| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using norm_fst_le z
    linarith
  have hrect : Icc (-R) R ×ˢ Icc (0 : ℝ) 1 ⊆ univ ×ˢ Icc (0 : ℝ) 1 :=
    prod_mono (subset_univ _) Subset.rfl
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (MeasurableSet.univ.prod measurableSet_Icc) hrect]
  · exact integral_symplecticForm_fderiv_prod_Icc_eq_zero (by linarith) zero_le_one
      (fun z _ ↦ hu.contDiffAt) hL₀ hL₁ (fun s _ ↦ hbottom s) (fun s _ ↦ htop s)
      (fun t _ ↦ image_eq_zero_of_notMem_tsupport (houtside (by simp [abs_of_pos hR])))
      (fun t _ ↦ image_eq_zero_of_notMem_tsupport (houtside (by simp [abs_of_pos hR])))
  · intro z hz
    have hfst : z.1 ∉ Icc (-R) R := fun h ↦ hz.2 ⟨h, hz.1.2⟩
    have hlarge : R ≤ |z.1| := by
      simp only [mem_Icc, not_and_or, not_le] at hfst
      rcases hfst with h | h
      · rw [abs_of_neg (by linarith)]
        linarith
      · exact le_trans h.le (le_abs_self _)
    simp [fderiv_of_notMem_tsupport ℝ (houtside hlarge)]

/-- The integrated directional energy on the strip equals the square of the Cauchy--Riemann
defect in the associated bilinear form, for compactly supported smooth maps with linear isotropic
boundary. Only invariance of the symplectic form is needed for this identity. -/
theorem integral_stdComplexLineEnergyDensity_strip_eq_integral_associatedBilinForm
    (hinv : ω.Invariant J) (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u)
    (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁)
    (hbottom : ∀ s, u (s, 0) ∈ L₀) (htop : ∀ s, u (s, 1) ∈ L₁) :
    ∫ z in univ ×ˢ Icc (0 : ℝ) 1,
        ω.stdComplexLineEnergyDensity J (fderiv ℝ u z).toLinearMap =
      ∫ z in univ ×ˢ Icc (0 : ℝ) 1, ω.associatedBilinForm J
        (fderiv ℝ u z stdComplexLineReal + J (fderiv ℝ u z stdComplexLineImag))
        (fderiv ℝ u z stdComplexLineReal + J (fderiv ℝ u z stdComplexLineImag)) :=
  integral_stdComplexLineEnergyDensity_eq_of_integral_symplecticForm_eq_zero
    hinv (hu.of_le (by norm_num)) hc
    (integral_symplecticForm_fderiv_strip_eq_zero hu hc hL₀ hL₁ hbottom htop)

end SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}
variable {u : ℝ × ℝ → V} {L₀ L₁ : Submodule ℝ V}

/-- The homogeneous `L²` Cauchy--Riemann energy identity on the strip with linear isotropic
boundary, in the caller's compatible inner product. It controls both directional derivatives
with constant one, without a transversality assumption on the boundary subspaces. -/
theorem integral_norm_partialDeriv_sq_strip_eq_integral_norm_cauchyRiemann_sq
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u)
    (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁)
    (hbottom : ∀ s, u (s, 0) ∈ L₀) (htop : ∀ s, u (s, 1) ∈ L₁) :
    ∫ z in univ ×ˢ Icc (0 : ℝ) 1,
        (‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ u z stdComplexLineImag‖ ^ 2) =
      ∫ z in univ ×ˢ Icc (0 : ℝ) 1,
        ‖fderiv ℝ u z stdComplexLineReal + J (fderiv ℝ u z stdComplexLineImag)‖ ^ 2 := by
  have h := ω.integral_stdComplexLineEnergyDensity_strip_eq_integral_associatedBilinForm
    (ω.invariant_of_apply_apply_eq_inner hg) hu hc hL₀ hL₁ hbottom htop
  simpa only [SymplecticForm.stdComplexLineEnergyDensity_def,
    SymplecticForm.associatedBilinForm_apply, ContinuousLinearMap.coe_coe,
    hg, real_inner_self_eq_norm_sq] using h

/-- Disjoint linear boundary subspaces allow the directional derivative energy to control
also the value energy on the strip, uniformly over compactly supported `C¹` maps. No isotropy
or choice of complex structure is needed for this Poincaré step. -/
theorem exists_integral_norm_sq_add_partialDeriv_sq_strip_le_mul_integral_partialDeriv_sq
    (hL : Disjoint L₀ L₁) :
    ∃ C > 0, ∀ (u : ℝ × ℝ → V), ContDiff ℝ 1 u → HasCompactSupport u →
      (∀ s, u (s, 0) ∈ L₀) → (∀ s, u (s, 1) ∈ L₁) →
      (∫ z in univ ×ˢ Icc (0 : ℝ) 1,
        ‖u z‖ ^ 2 + (‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ u z stdComplexLineImag‖ ^ 2)) ≤
      C * ∫ z in univ ×ˢ Icc (0 : ℝ) 1,
        ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ u z stdComplexLineImag‖ ^ 2 := by
  obtain ⟨C, hC, hPoincare⟩ :=
    L₀.exists_integral_norm_sq_le_mul_integral_norm_fderiv_sq_of_disjoint L₁ hL
  refine ⟨C + 1, by linarith, ?_⟩
  intro u hu hc hbottom htop
  have hi : Integrable (fun z ↦ ‖u z‖ ^ 2) :=
    hu.continuous.integrable_norm_sq_of_hasCompactSupport hc
  have hdu := hu.continuous_fderiv one_ne_zero
  have hti : Integrable (fun z ↦ ‖fderiv ℝ u z stdComplexLineImag‖ ^ 2) :=
    (hdu.clm_apply continuous_const).integrable_norm_sq_of_hasCompactSupport
      (hc.fderiv_apply ℝ stdComplexLineImag)
  have henergy := (integrable_add_iff_integrable_right' hi).mp
    (hu.integrable_norm_sq_add_partialDeriv_sq hc)
  have hvalue := hPoincare u hu hc hbottom htop
  rw [← stdComplexLineImag_eq] at hvalue
  have htbound := integral_mono
    (hti.integrableOn (s := univ ×ˢ Icc (0 : ℝ) 1)) henergy.integrableOn
    (fun z ↦ le_add_of_nonneg_left (sq_nonneg ‖fderiv ℝ u z stdComplexLineReal‖))
  rw [integral_add hi.integrableOn henergy.integrableOn]
  nlinarith [mul_le_mul_of_nonneg_left htbound hC.le]

/-- With disjoint linear isotropic boundary subspaces, the Cauchy--Riemann defect controls the
full value and directional derivative energy on the strip. The constant is uniform over all
compactly supported `C²` maps satisfying the boundary conditions. -/
theorem exists_integral_norm_sq_add_partialDeriv_sq_strip_le_mul
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁) (hL : Disjoint L₀ L₁) :
    ∃ C > 0, ∀ (u : ℝ × ℝ → V), ContDiff ℝ 2 u → HasCompactSupport u →
      (∀ s, u (s, 0) ∈ L₀) → (∀ s, u (s, 1) ∈ L₁) →
      (∫ z in univ ×ˢ Icc (0 : ℝ) 1,
        ‖u z‖ ^ 2 + (‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ u z stdComplexLineImag‖ ^ 2)) ≤
      C * ∫ z in univ ×ˢ Icc (0 : ℝ) 1,
        ‖fderiv ℝ u z stdComplexLineReal + J (fderiv ℝ u z stdComplexLineImag)‖ ^ 2 := by
  obtain ⟨C, hC, hfull⟩ :=
    exists_integral_norm_sq_add_partialDeriv_sq_strip_le_mul_integral_partialDeriv_sq hL
  refine ⟨C, hC, fun u hu hc hbottom htop ↦ ?_⟩
  have h := hfull u (hu.of_le (by norm_num)) hc hbottom htop
  rwa [integral_norm_partialDeriv_sq_strip_eq_integral_norm_cauchyRiemann_sq
    hg hu hc hL₀ hL₁ hbottom htop] at h

end TauCeti
