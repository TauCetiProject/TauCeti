/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.CompactSupport
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
public import TauCeti.Analysis.Sobolev.Strip
import TauCeti.Analysis.Sobolev.Poincare.TransverseBoundary
import TauCeti.Analysis.Calculus.FDeriv.Submodule
import TauCeti.Geometry.Symplectic.CompatibleMetric
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Norm
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
by the defect with a constant independent of the map.

The estimate passes to the Sobolev completion. The Cauchy--Riemann operator `∂s + J ∂t`
(`TauCeti.StripSobolev.cauchyRiemann`) acts on the Sobolev space `W^{1,2}` of the strip with
boundary values in `L₀` and `L₁` (`TauCeti.StripSobolev.H1`), with values in `L²`. For disjoint
isotropic `L₀` and `L₁`, for instance a transverse pair of Lagrangian subspaces, it is bounded
below (`TauCeti.StripSobolev.exists_norm_le_mul_norm_cauchyRiemann`), hence injective with closed
range (`TauCeti.StripSobolev.ker_cauchyRiemann_eq_bot`,
`TauCeti.StripSobolev.isClosed_range_cauchyRiemann`). This is the linearized operator of the
constant Floer strip at a transverse intersection point of two Lagrangian submanifolds, in a
unitary trivialization. Its surjectivity is not proved here.

The boundary calculation uses
`ContinuousLinearMap.integral_bilinear_fderiv_sub_prod_Icc`. The argument is the energy identity
and linear Lagrangian boundary integration by parts of D. McDuff and D. Salamon,
*J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix B.

## Main results

* `TauCeti.SymplecticForm.integral_symplecticForm_fderiv_strip_eq_zero`: a compactly supported map
  on the strip with isotropic boundary values has zero symplectic area.
* `TauCeti.integral_norm_partialDeriv_sq_strip_eq_integral_norm_cauchyRiemann_sq`: the energy
  identity on the strip.
* `TauCeti.exists_integral_norm_sq_add_partialDeriv_sq_strip_le_mul`: the energy estimate for
  disjoint isotropic boundary subspaces.
* `TauCeti.StripSobolev.exists_norm_le_mul_norm_cauchyRiemann`: on `W^{1,2}`, the Cauchy--Riemann
  operator with disjoint isotropic boundary subspaces is bounded below.
* `TauCeti.StripSobolev.ker_cauchyRiemann_eq_bot` and
  `TauCeti.StripSobolev.isClosed_range_cauchyRiemann`: it is injective with closed range.

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
            L.isClosed_of_finiteDimensional hmem (1 : ℝ)
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
  obtain ⟨C, hC, hPoincare⟩ :=
    L₀.exists_integral_norm_sq_le_mul_integral_norm_fderiv_sq_of_disjoint L₁ hL
  refine ⟨C + 1, by linarith, ?_⟩
  intro u hu hc hbottom htop
  have hdu : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hi : Integrable (fun z ↦ ‖u z‖ ^ 2) :=
    hu.continuous.integrable_norm_sq_of_hasCompactSupport hc
  have hsi : Integrable (fun z ↦ ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2) :=
    (hdu.clm_apply continuous_const).integrable_norm_sq_of_hasCompactSupport
      (hc.fderiv_apply ℝ stdComplexLineReal)
  have hti : Integrable (fun z ↦ ‖fderiv ℝ u z stdComplexLineImag‖ ^ 2) :=
    (hdu.clm_apply continuous_const).integrable_norm_sq_of_hasCompactSupport
      (hc.fderiv_apply ℝ stdComplexLineImag)
  have henergy : Integrable (fun z ↦ ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ u z stdComplexLineImag‖ ^ 2) := hsi.fun_add hti
  have hvalue := hPoincare u (hu.of_le (by norm_num)) hc hbottom htop
  have htbound : (∫ z in univ ×ˢ Icc (0 : ℝ) 1,
      ‖fderiv ℝ u z stdComplexLineImag‖ ^ 2) ≤
      ∫ z in univ ×ˢ Icc (0 : ℝ) 1,
        ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ u z stdComplexLineImag‖ ^ 2 :=
    integral_mono hti.integrableOn henergy.integrableOn
      (fun z ↦ le_add_of_nonneg_left (sq_nonneg _))
  have hidentity := integral_norm_partialDeriv_sq_strip_eq_integral_norm_cauchyRiemann_sq
    hg hu hc hL₀ hL₁ hbottom htop
  rw [integral_add hi.integrableOn henergy.integrableOn, ← hidentity]
  have hscaled := mul_le_mul_of_nonneg_left htbound hC.le
  rw [← stdComplexLineImag_eq] at hvalue
  nlinarith

/-! ### The Cauchy--Riemann operator on `W^{1,2}` of the strip -/

namespace StripSobolev

open CylinderSobolev (stripMeasure jet jet_apply sq_norm_jet_le)

/-- The coefficient `(v, v_s, v_t) ↦ v_s + J v_t` of the Cauchy--Riemann operator `∂s + J ∂t`
on jets. -/
noncomputable def cauchyRiemannJetCoeff (J : AlmostComplexStructure V) : V × V × V →L[ℝ] V :=
  (ContinuousLinearMap.fst ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V)) +
    (LinearMap.toContinuousLinearMap J.toLinearMap).comp
      ((ContinuousLinearMap.snd ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V)))

@[simp]
theorem cauchyRiemannJetCoeff_apply (J : AlmostComplexStructure V) (v : V × V × V) :
    cauchyRiemannJetCoeff J v = v.2.1 + J v.2.2 :=
  (rfl)

/-- On the jet `(ξ, ∂s ξ, ∂t ξ)` of a map, the coefficient gives `∂s ξ + J ∂t ξ`. -/
theorem cauchyRiemannJetCoeff_jet (J : AlmostComplexStructure V) (ξ : ℝ × ℝ → V)
    (z : ℝ × ℝ) :
    cauchyRiemannJetCoeff J (jet ξ z) =
      fderiv ℝ ξ z stdComplexLineReal + J (fderiv ℝ ξ z stdComplexLineImag) := by
  rw [cauchyRiemannJetCoeff_apply, jet_apply, stdComplexLineReal_eq, stdComplexLineImag_eq]

variable (J L₀ L₁) in
/-- The Cauchy--Riemann operator `∂s + J ∂t` from the Sobolev space `W^{1,2}` of the strip with
boundary values in `L₀` and `L₁` (`TauCeti.StripSobolev.H1`) to `L²(ℝ × [0, 1], V)`. -/
noncomputable def cauchyRiemann : H1 L₀ L₁ →L[ℝ] Lp V 2 stripMeasure :=
  ((cauchyRiemannJetCoeff J).compLpL 2 stripMeasure).comp (H1 L₀ L₁).subtypeL

/-- The Cauchy--Riemann operator is the pointwise action of its coefficient on `L²` jets,
restricted to `H1`. -/
theorem cauchyRiemann_apply (x : H1 L₀ L₁) :
    cauchyRiemann J L₀ L₁ x =
      (cauchyRiemannJetCoeff J).compLpL 2 stripMeasure (x : Lp (V × V × V) 2 stripMeasure) :=
  (rfl)

/-- The Cauchy--Riemann operator acts pointwise on `L²` jets: `(v, v_s, v_t) ↦ v_s + J v_t`. -/
theorem coeFn_cauchyRiemann (x : H1 L₀ L₁) :
    cauchyRiemann J L₀ L₁ x =ᵐ[stripMeasure]
      fun z ↦ ((x : Lp (V × V × V) 2 stripMeasure) z).2.1 +
        J ((x : Lp (V × V × V) 2 stripMeasure) z).2.2 :=
  (cauchyRiemannJetCoeff J).coeFn_compLpL _

/-- On the jet of a test section `ξ`, the Cauchy--Riemann operator is `∂s ξ + J ∂t ξ`. -/
theorem cauchyRiemann_jetₗ_ae_eq (ξ : testSection L₀ L₁) :
    cauchyRiemann J L₀ L₁ ⟨jetₗ L₀ L₁ ξ, jetₗ_mem_H1 ξ⟩ =ᵐ[stripMeasure]
      fun z ↦ fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineReal +
        J (fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineImag) := by
  filter_upwards [coeFn_cauchyRiemann (J := J) ⟨jetₗ L₀ L₁ ξ, jetₗ_mem_H1 ξ⟩, coeFn_jetₗ ξ]
    with z h₁ h₂
  rw [h₁, h₂, ← cauchyRiemannJetCoeff_apply, cauchyRiemannJetCoeff_jet]

/-- **The Cauchy--Riemann operator of the strip with transverse isotropic boundary conditions is
bounded below.** Let `J` be compatible with `ω` in the inner product of `V`, and let `L₀`, `L₁` be
isotropic subspaces with `L₀ ∩ L₁ = 0`, for instance a transverse pair of Lagrangian subspaces.
Then `‖x‖ ≤ C ‖(∂s + J ∂t) x‖` for every `x` in the Sobolev space `W^{1,2}` of the strip with
boundary values in `L₀` and `L₁`. -/
theorem exists_norm_le_mul_norm_cauchyRiemann (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁) (hL : Disjoint L₀ L₁) :
    ∃ C, ∀ x : H1 L₀ L₁, ‖x‖ ≤ C * ‖cauchyRiemann J L₀ L₁ x‖ := by
  obtain ⟨C, hC, hest⟩ := exists_integral_norm_sq_add_partialDeriv_sq_strip_le_mul hg hL₀ hL₁ hL
  set D := (cauchyRiemannJetCoeff J).compLpL 2 stripMeasure
  -- The estimate on the jets of test sections.
  have hjet (ξ : testSection L₀ L₁) : ‖jetₗ L₀ L₁ ξ‖ ≤ √C * ‖D (jetₗ L₀ L₁ ξ)‖ := by
    obtain ⟨hξ, hc, h₀, h₁⟩ := mem_testSection_iff.1 ξ.2
    have hD : ‖D (jetₗ L₀ L₁ ξ)‖ ^ 2 = ∫ z in univ ×ˢ Icc (0 : ℝ) 1,
        ‖fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineReal +
          J (fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineImag)‖ ^ 2 := by
      rw [← Lp.integral_norm_sq_eq_norm_sq]
      refine integral_congr_ae ?_
      filter_upwards [cauchyRiemann_jetₗ_ae_eq (J := J) ξ] with z hz
      rw [← hz, cauchyRiemann_apply]
    have hdu : Continuous (fderiv ℝ (ξ : ℝ × ℝ → V)) := hξ.continuous_fderiv (by norm_num)
    have hint : Integrable (fun z ↦ ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 +
        (‖fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineImag‖ ^ 2)) stripMeasure :=
      ((hξ.continuous.integrable_norm_sq_of_hasCompactSupport hc).add
        (((hdu.clm_apply continuous_const).integrable_norm_sq_of_hasCompactSupport
          (hc.fderiv_apply ℝ stdComplexLineReal)).add
        ((hdu.clm_apply continuous_const).integrable_norm_sq_of_hasCompactSupport
          (hc.fderiv_apply ℝ stdComplexLineImag)))).integrableOn
    have hsq : ‖jetₗ L₀ L₁ ξ‖ ^ 2 ≤ (√C * ‖D (jetₗ L₀ L₁ ξ)‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hC.le, hD, sq_norm_jetₗ]
      refine (integral_mono_of_nonneg (.of_forall fun z ↦ by positivity) hint
        (.of_forall fun z ↦ (sq_norm_jet_le _ z).trans_eq ?_)).trans ?_
      · rw [stdComplexLineReal_eq, stdComplexLineImag_eq]
        ring
      exact hest ξ hξ hc h₀ h₁
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  -- It passes to the closure `H1`.
  refine ⟨√C, fun x ↦ ?_⟩
  have hsub := H1_subset_of_isClosed (S := {f | ‖f‖ ≤ √C * ‖D f‖})
    (isClosed_le continuous_norm (continuous_const.mul (continuous_norm.comp D.continuous)))
    (by rintro _ ⟨ξ, rfl⟩; exact hjet ξ)
  exact hsub x.2

/-- With transverse isotropic boundary conditions the Cauchy--Riemann operator on `W^{1,2}` of the
strip is injective. -/
theorem ker_cauchyRiemann_eq_bot (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁) (hL : Disjoint L₀ L₁) :
    (cauchyRiemann J L₀ L₁).ker = ⊥ := by
  obtain ⟨C, hC⟩ := exists_norm_le_mul_norm_cauchyRiemann hg hL₀ hL₁ hL
  refine LinearMap.ker_eq_bot'.2 fun x hx ↦ norm_le_zero_iff.1 ?_
  have hx' : cauchyRiemann J L₀ L₁ x = 0 := hx
  have h := hC x
  rwa [hx', norm_zero, mul_zero] at h

/-- With transverse isotropic boundary conditions the Cauchy--Riemann operator on `W^{1,2}` of the
strip has closed range. -/
theorem isClosed_range_cauchyRiemann (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁) (hL : Disjoint L₀ L₁) :
    IsClosed (Set.range (cauchyRiemann J L₀ L₁)) := by
  obtain ⟨C, hC⟩ := exists_norm_le_mul_norm_cauchyRiemann hg hL₀ hL₁ hL
  refine ((cauchyRiemann J L₀ L₁).antilipschitz_of_bound (K := C.toNNReal) fun x ↦
    (hC x).trans ?_).isClosed_range (cauchyRiemann J L₀ L₁).uniformContinuous
  exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (norm_nonneg _)

end StripSobolev

end TauCeti
