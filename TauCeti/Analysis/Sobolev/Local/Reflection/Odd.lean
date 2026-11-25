/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Reflection
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Odd reflection of half-disc Sobolev maps vanishing on the real axis

For an open `Ω ⊆ ℂ`, let `g` be weakly differentiable on the open upper part `Ω ∩ {0 < im}`, with
`g` continuous on `Ω ∩ {0 ≤ im}` and vanishing on `Ω ∩ ℝ`, and with derivative integrable on
compact subsets of `Ω ∩ {0 ≤ im}`. This file proves that the boundary term of the integration by
parts on the upper half-plane vanishes in every direction, against every smooth compactly supported
test function `χ`, including those that do not vanish on the axis
(`TauCeti.HasWeakLineDerivOn.setIntegral_fderiv_smul_eq_neg_of_continuousOn`):

`∫_{0 < im} ∂_v χ • g = -∫_{0 < im} χ • ∂_v g`.

`TauCeti.HasWeakLineDerivOn.setIntegral_fderiv_smul_eq_neg` proves this when `v` is tangent to the
axis or `χ` vanishes on it; here the vanishing is moved onto `g`. The proof tests the weak
derivative against `ψₙ χ`, where `ψₙ(z) = smoothTransition ((n + 1) im z - 1)` vanishes near the
axis, and lets `n → ∞`. The boundary layer `χ ∂_v ψₙ • g` lives in the strip
`{0 < im ≤ 2 / (n + 1)}`, where `∂_v ψₙ = O(n)` and the area is `O(1/n)`, while `g = o(1)` there
by uniform continuity, since `g` vanishes on the axis.

As consequences:

* `TauCeti.HasWeakLineDerivOn.indicator_setOf_im_nonneg`: the extension of `g` by zero below the
  axis is weakly differentiable on all of `Ω`, with derivative the extension of `∂_v g` by zero.
* `TauCeti.HasWeakFDerivOn.planarReflection_neg_one`: on a conjugation-invariant `Ω`, the odd
  reflection `g(conj z) ↦ -g(z)`, which is `TauCeti.planarReflection` with the single weight
  `-1`, is weakly differentiable on `Ω`, with derivative `TauCeti.planarReflectionFDeriv`. The
  weights of the even reflection sum to one, which is how
  `TauCeti.HasWeakFDerivOn.planarReflection` matches the two one-sided values on the axis; here
  they sum to `-1`, and the boundary condition takes over. The odd reflection is twice the
  extension by zero minus the even reflection.
* `TauCeti.MemWkpLoc.planarReflection_neg_one`: the odd reflection of a continuous map in
  `W^{1,p}_loc(Ω ∩ {0 ≤ im})` vanishing on `Ω ∩ ℝ` is in `W^{1,p}_loc(Ω)`.

Without the boundary condition the odd reflection jumps across the axis, and the conclusions fail.

## References

* L. C. Evans, *Partial Differential Equations*, §5.4 (extension by reflection).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (reflection for totally real boundary conditions).
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology Complex Metric TopologicalSpace
open scoped ContDiff ENNReal ComplexConjugate

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### The boundary-layer cutoff -/

/-- The cutoff `smoothTransition ((n + 1) im z - 1)`: zero where `(n + 1) im z ≤ 1`, one where
`(n + 1) im z ≥ 2`. -/
private def axisCutoff (n : ℕ) (z : ℂ) : ℝ := Real.smoothTransition (((n : ℝ) + 1) * z.im - 1)

private theorem contDiff_axisCutoff (n : ℕ) : ContDiff ℝ ∞ (axisCutoff n) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul imCLM.contDiff).sub contDiff_const)

private theorem hasFDerivAt_axisCutoff (n : ℕ) (z : ℂ) :
    HasFDerivAt (axisCutoff n)
      ((deriv Real.smoothTransition (((n : ℝ) + 1) * z.im - 1) * ((n : ℝ) + 1)) • imCLM) z := by
  have h1 : HasFDerivAt (fun z : ℂ => ((n : ℝ) + 1) * z.im - 1) (((n : ℝ) + 1) • imCLM) z :=
    (imCLM.hasFDerivAt.const_mul ((n : ℝ) + 1)).sub_const 1
  have h2 := ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
    (((n : ℝ) + 1) * z.im - 1)).hasDerivAt.comp_hasFDerivAt z h1
  rw [smul_smul] at h2
  exact h2

/-- The volume of a rectangle `[-ρ, ρ] × [0, δ]` is `2ρδ`. -/
private theorem volume_real_reProdIm_Icc {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) :
    volume.real (Icc (-ρ) ρ ×ℂ Icc 0 δ) = 2 * ρ * δ := by
  have h : volume (Icc (-ρ) ρ ×ℂ Icc 0 δ) = volume (Icc (-ρ) ρ) * volume (Icc (0 : ℝ) δ) := by
    change volume (measurableEquivRealProd ⁻¹' (Icc (-ρ) ρ ×ˢ Icc 0 δ)) = _
    rw [volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet, Measure.volume_eq_prod,
      Measure.prod_prod]
  rw [measureReal_def, h, Real.volume_Icc, Real.volume_Icc, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
  ring

omit [NormedSpace ℝ F] in
/-- A function continuous on `Ω ∩ {0 ≤ im}` and zero on `Ω ∩ ℝ` is uniformly small near the axis
on every compact subset of `Ω ∩ {0 ≤ im}`. -/
private theorem exists_forall_norm_lt_of_im_lt {Ω : Opens ℂ} {g : ℂ → F}
    (hgc : ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (hg0 : ∀ x : ℝ, (x : ℂ) ∈ Ω → g x = 0)
    {T : Set ℂ} (hT : IsCompact T) (hTΩ : T ⊆ Ω) (hT0 : T ⊆ {z | 0 ≤ z.im}) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ z ∈ T, z.im < δ → ‖g z‖ < ε := by
  have hclosed : IsClosed {z : ℂ | 0 ≤ z.im} := Complex.isClosed_setOfPred_le_im 0
  obtain ⟨r, hr, hrΩ⟩ := hT.exists_cthickening_subset_open Ω.isOpen hTΩ
  have hC : IsCompact (cthickening r T ∩ {z : ℂ | 0 ≤ z.im}) := hT.cthickening.inter_right hclosed
  obtain ⟨δ, hδ, hgδ⟩ := Metric.uniformContinuousOn_iff.1 (hC.uniformContinuousOn_of_continuous
    (hgc.mono fun z hz => ⟨hrΩ hz.1, hz.2⟩)) ε hε
  refine ⟨min δ r, lt_min hδ hr, fun z hzT hzδ => ?_⟩
  have hz0 : 0 ≤ z.im := hT0 hzT
  have hdist : dist (z.re : ℂ) z = z.im := by
    rw [Complex.dist_eq_re_im]
    simp [Real.sqrt_sq hz0]
  have hz' : (z.re : ℂ) ∈ cthickening r T ∩ {z : ℂ | 0 ≤ z.im} :=
    ⟨mem_cthickening_of_dist_le _ z r T hzT (by linarith [min_le_right δ r]), by simp⟩
  have h := hgδ z ⟨self_subset_cthickening T hzT, hz0⟩ _ hz'
    (by rw [dist_comm, hdist]; linarith [min_le_left δ r])
  rwa [hg0 _ (hrΩ hz'.1), dist_zero_right] at h

/-- **The boundary layer vanishes in the limit.** For `g` continuous on `Ω ∩ {0 ≤ im}` and zero
on `Ω ∩ ℝ`, and `χ` continuous with compact support meeting `{0 ≤ im}` inside `Ω`, the integral of
`χ (n + 1) smoothTransition'((n + 1) im - 1) • g` over the upper half-plane tends to zero. -/
private theorem tendsto_setIntegral_boundaryLayer {Ω : Opens ℂ} {g : ℂ → F}
    (hgc : ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (hg0 : ∀ x : ℝ, (x : ℂ) ∈ Ω → g x = 0)
    {χ : ℂ → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ∩ {z : ℂ | 0 ≤ z.im} ⊆ Ω) (a : ℝ) :
    Tendsto (fun n : ℕ => ∫ z in {z : ℂ | 0 < z.im},
      (χ z * (deriv Real.smoothTransition (((n : ℝ) + 1) * z.im - 1) * (((n : ℝ) + 1) * a))) •
        g z) atTop (𝓝 0) := by
  have hclosed : IsClosed {z : ℂ | 0 ≤ z.im} := Complex.isClosed_setOfPred_le_im 0
  set T := tsupport χ ∩ {z : ℂ | 0 ≤ z.im}
  have hT : IsCompact T := hχc.isCompact.inter_right hclosed
  obtain ⟨ρ, hρ⟩ := hT.isBounded.subset_closedBall 0
  obtain ⟨B, hB⟩ := (Real.smoothTransition.contDiff.continuous_deriv le_rfl).norm
    |>.bddAbove_range_of_hasCompactSupport Real.smoothTransition.hasCompactSupport_deriv.norm
  obtain ⟨M, hM⟩ := hχ.bounded_above_of_compact_support hχc
  set ρ' := max ρ 0
  set K := 4 * ρ' * (max M 0 * max B 0 * |a|)
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hε₀ : 0 < ε / (K + 1) := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hgδ⟩ := exists_forall_norm_lt_of_im_lt hgc hg0 hT hχΩ inter_subset_right hε₀
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / δ)
  refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right]
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set w := 2 / ((n : ℝ) + 1)
  have hw : w < δ := by
    rw [div_lt_iff₀ hn1]
    rw [div_lt_iff₀ hδ] at hN
    nlinarith [(Nat.cast_le (α := ℝ)).2 hn]
  set f := fun z : ℂ =>
    (χ z * (deriv Real.smoothTransition (((n : ℝ) + 1) * z.im - 1) * (((n : ℝ) + 1) * a))) • g z
  set S := {z : ℂ | 0 < z.im} ∩ (T ∩ {z : ℂ | z.im ≤ w})
  have hK0 : 0 ≤ K := by positivity
  -- Off the strip `S` the integrand vanishes; on it, it is bounded.
  have hoff : ∀ z ∈ {z : ℂ | 0 < z.im} \ S, f z = 0 := by
    rintro z ⟨hz, hzS⟩
    have hz0 : 0 < z.im := hz
    by_cases hzT : z ∈ tsupport χ
    · have hzw : w < z.im := not_le.1 fun h => hzS ⟨hz, ⟨hzT, hz0.le⟩, h⟩
      have h1 : 1 ≤ ((n : ℝ) + 1) * z.im - 1 := by
        rw [div_lt_iff₀ hn1] at hzw
        linarith
      simp [f, Real.smoothTransition.deriv_of_one_le h1]
    · simp [f, image_eq_zero_of_notMem_tsupport hzT]
  have hon : ∀ z ∈ S, ‖f z‖ ≤ max M 0 * (max B 0 * (((n : ℝ) + 1) * |a|)) * (ε / (K + 1)) := by
    rintro z ⟨hz, ⟨hzT, -⟩, hzw⟩
    have hz0 : 0 < z.im := hz
    have hzw' : z.im ≤ w := hzw
    have hgz := hgδ z ⟨hzT, hz0.le⟩ (by linarith)
    have hBz := hB ⟨((n : ℝ) + 1) * z.im - 1, rfl⟩
    simp only [f, norm_smul, norm_mul, Real.norm_eq_abs, abs_of_pos hn1] at hBz ⊢
    have hMz := hM z
    rw [Real.norm_eq_abs] at hMz
    gcongr
    all_goals first
      | exact hMz.trans (le_max_left _ _)
      | exact hBz.trans (le_max_left _ _)
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (measurableSet_lt measurable_const measurable_im) inter_subset_left hoff]
  have hSR : S ⊆ Icc (-ρ') ρ' ×ℂ Icc 0 w := fun z hz => by
    have hzρ := mem_closedBall_zero_iff.1 (hρ hz.2.1)
    refine ⟨abs_le.1 ((abs_re_le_norm z).trans (hzρ.trans (le_max_left _ _))), ?_, hz.2.2⟩
    exact le_of_lt hz.1
  have hRfin : volume (Icc (-ρ') ρ' ×ℂ Icc 0 w) < ⊤ :=
    ((isCompact_Icc.reProdIm isCompact_Icc)).measure_lt_top
  have hvol : volume.real S ≤ 2 * ρ' * w := by
    rw [← volume_real_reProdIm_Icc (le_max_right _ _) (by positivity)]
    exact measureReal_mono hSR hRfin.ne
  calc ‖∫ z in S, f z‖
        ≤ (max M 0 * (max B 0 * (((n : ℝ) + 1) * |a|)) * (ε / (K + 1))) * volume.real S :=
        norm_setIntegral_le_of_norm_le_const ((measure_mono hSR).trans_lt hRfin) hon
    _ ≤ (max M 0 * (max B 0 * (((n : ℝ) + 1) * |a|)) * (ε / (K + 1))) * (2 * ρ' * w) :=
        mul_le_mul_of_nonneg_left hvol (by positivity)
    _ = K * (ε / (K + 1)) := by
        simp only [K, w]
        field_simp
        ring
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [hK0]

/-! ### Integration by parts up to the real axis -/

/-- **Integration by parts up to the real axis for a function vanishing on it.** Let `g'` be a weak
derivative of `g` in the direction `v` on the upper part of `Ω`, with `g` continuous on
`Ω ∩ {0 ≤ im}` and zero on `Ω ∩ ℝ`, and `g'` integrable on compact subsets of `Ω ∩ {0 ≤ im}`.
Then the integration-by-parts identity on the upper half-plane holds, with no boundary term,
against every smooth compactly supported `χ` whose support meets `{0 ≤ im}` inside `Ω`. -/
theorem HasWeakLineDerivOn.setIntegral_fderiv_smul_eq_neg_of_continuousOn {Ω : Opens ℂ}
    {g g' : ℂ → F} {v : ℂ}
    (hgW : HasWeakLineDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) g g' v)
    (hgc : ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (hg0 : ∀ x : ℝ, (x : ℂ) ∈ Ω → g x = 0)
    (hg' : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g')
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ∩ {z : ℂ | 0 ≤ z.im} ⊆ Ω) :
    ∫ z in {z : ℂ | 0 < z.im}, fderiv ℝ χ z v • g z =
      -∫ z in {z : ℂ | 0 < z.im}, χ z • g' z := by
  set H := {z : ℂ | 0 < z.im}
  have hHm : MeasurableSet H := measurableSet_lt measurable_const measurable_im
  have hg : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g := hgc.memLpLoc
  have hint {h : ℂ → F} (hh : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) h) {f : ℂ → ℝ}
      (hf : Continuous f) (hfχ : tsupport f ⊆ tsupport χ) : IntegrableOn (fun z => f z • h z) H :=
    (hh.integrableOn_smul hf (hχc.mono' ((subset_tsupport f).trans hfχ))
      (Complex.isClosed_setOfPred_le_im 0) fun _ hz => ⟨hχΩ ⟨hfχ hz.1, hz.2⟩, hz.2⟩).mono_set
      (ofPred_subset_ofPred.2 fun _ => le_of_lt)
  have hdχ : Continuous fun z => fderiv ℝ χ z v :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdst : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  set D : ℕ → ℂ → ℝ := fun n z => χ z *
    (deriv Real.smoothTransition (((n : ℝ) + 1) * z.im - 1) * (((n : ℝ) + 1) * v.im)) with hD
  -- The weak derivative identity, tested against `ψₙ χ`, which vanishes on the axis.
  have key (n : ℕ) : (∫ z in H, (axisCutoff n z * fderiv ℝ χ z v) • g z) +
      ∫ z in H, D n z • g z = -∫ z in H, (axisCutoff n z * χ z) • g' z := by
    have h0 (x : ℝ) : axisCutoff n x * χ x = 0 := by
      simp [axisCutoff, Real.smoothTransition.zero_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0)]
    have h := hgW.setIntegral_fderiv_smul_eq_neg hg hg' ((contDiff_axisCutoff n).mul hχ)
      hχc.mul_left (fun z hz => hχΩ ⟨tsupport_mul_subset_right hz.1, hz.2⟩) (Or.inr h0)
    have hd (z : ℂ) : fderiv ℝ (fun z => axisCutoff n z * χ z) z v =
        axisCutoff n z * fderiv ℝ χ z v + D n z := by
      have h' :=
        ((hasFDerivAt_axisCutoff n z).mul (hχ.differentiable (by simp) z).hasFDerivAt).fderiv
      rw [show (fun z => axisCutoff n z * χ z) = axisCutoff n * χ from rfl, h']
      simp only [hD, add_apply, smul_apply, smul_eq_mul, imCLM_apply]
      ring
    simp only [hd, add_smul] at h
    rwa [integral_add (hint (f := fun z => axisCutoff n z * fderiv ℝ χ z v) hg
      ((contDiff_axisCutoff n).continuous.mul hdχ)
      (tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ v)))
      (hint (f := D n) hg (hχ.continuous.mul ((hdst.comp ((continuous_const.mul continuous_im).sub
        continuous_const)).mul continuous_const)) tsupport_mul_subset_left)] at h
  -- Pass to the limit `n → ∞`.
  have hlim {f : ℂ → F} (hf : IntegrableOn f H) :
      Tendsto (fun n : ℕ => ∫ z in H, axisCutoff n z • f z) atTop (𝓝 (∫ z in H, f z)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => ‖f z‖)
      (fun n => (contDiff_axisCutoff n).continuous.aestronglyMeasurable.smul
        hf.aestronglyMeasurable) hf.norm (fun n => Eventually.of_forall fun z => ?_)
      ((ae_restrict_iff' hHm).2 (Eventually.of_forall fun z hz => ?_))
    · rw [norm_smul]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [axisCutoff, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    · have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * z.im - 1) atTop atTop :=
        tendsto_atTop_add_const_right _ _
          ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const hz)
      exact tendsto_const_nhds.congr' <| (h.eventually_ge_atTop 1).mono fun n hn => by
        simp [axisCutoff, Real.smoothTransition.one_of_one_le hn]
  have h1 := hlim (hint hg hdχ (tsupport_fderiv_apply_subset ℝ v))
  have h3 := hlim (hint hg' hχ.continuous subset_rfl)
  simp only [smul_smul] at h1 h3
  have h2 := tendsto_setIntegral_boundaryLayer hgc hg0 hχ.continuous hχc hχΩ v.im
  have h := h1.add h2
  rw [add_zero] at h
  exact tendsto_nhds_unique (h.congr key) h3.neg

/-! ### Extension by zero and odd reflection -/

omit [NormedSpace ℝ F] in
/-- The extension by zero of a function locally integrable up to the real axis is locally
integrable on `Ω`. -/
private theorem locallyIntegrableOn_indicator_setOf_im_nonneg {Ω : Opens ℂ} {g : ℂ → F}
    (hg : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g) :
    LocallyIntegrableOn ({z : ℂ | 0 ≤ z.im}.indicator g) Ω := by
  have hH : MeasurableSet {z : ℂ | 0 ≤ z.im} := measurableSet_le measurable_const measurable_im
  refine (memLpLoc_one_iff_locallyIntegrableOn Ω.isOpen.isLocallyClosed).1
    (memLpLoc_iff.2 fun K hKΩ hK => ?_)
  rw [memLp_indicator_iff_restrict hH.nullMeasurableSet, Measure.restrict_restrict hH]
  exact memLpLoc_iff.1 hg _ (fun z hz => ⟨hKΩ hz.2, hz.1⟩)
    (hK.inter_left (Complex.isClosed_setOfPred_le_im 0))

/-- **Extension by zero.** If `g'` is the weak derivative of `g` in the direction `v` on the upper
part of `Ω`, with `g` continuous on `Ω ∩ {0 ≤ im}` and zero on `Ω ∩ ℝ` and `g'` integrable on
compact subsets of `Ω ∩ {0 ≤ im}`, then the extensions by zero below the axis satisfy the same
relation on all of `Ω`. -/
theorem HasWeakLineDerivOn.indicator_setOf_im_nonneg {Ω : Opens ℂ} {g g' : ℂ → F} {v : ℂ}
    (hgW : HasWeakLineDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) g g' v)
    (hgc : ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (hg0 : ∀ x : ℝ, (x : ℂ) ∈ Ω → g x = 0)
    (hg' : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g') :
    HasWeakLineDerivOn volume Ω ({z : ℂ | 0 ≤ z.im}.indicator g)
      ({z : ℂ | 0 ≤ z.im}.indicator g') v := by
  have := hgW.completeSpace
  refine (hasWeakLineDerivOn_iff (locallyIntegrableOn_indicator_setOf_im_nonneg hgc.memLpLoc)
    (locallyIntegrableOn_indicator_setOf_im_nonneg hg')).2 fun φ hφ hφc hφΩ => ?_
  have hH : MeasurableSet {z : ℂ | 0 ≤ z.im} := measurableSet_le measurable_const measurable_im
  have hind (a : ℂ → ℝ) (f : ℂ → F) : (fun z => a z • {z : ℂ | 0 ≤ z.im}.indicator f z) =
      {z : ℂ | 0 ≤ z.im}.indicator fun z => a z • f z :=
    funext fun z => (indicator_smul_apply _ _ _ _).symm
  simp_rw [((hφ.differentiable (by simp)) _).lineDeriv_eq_fderiv]
  rw [hind (fun z => fderiv ℝ φ z v) g, hind φ g', integral_indicator hH, integral_indicator hH,
    setIntegral_congr_set (Complex.setOf_le_im_ae_eq 0),
    setIntegral_congr_set (Complex.setOf_le_im_ae_eq 0)]
  exact hgW.setIntegral_fderiv_smul_eq_neg_of_continuousOn hgc hg0 hg' hφ hφc
    fun z hz => hφΩ hz.1

/-- On a conjugation-invariant set the node dilation of the order-one reflection stays in it. -/
private theorem imDilation_mem_of_mapsTo_conj {Ω : Opens ℂ}
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) :
    ∀ z ∈ Ω, z.im < 0 → ∀ j : Fin 1, imDilation (higherReflectionNode j) z ∈ Ω :=
  fun z hz _ j => by
    rw [imDilation_higherReflectionNode_fin_one]
    exact hΩ hz

/-- **Weak derivative of the odd reflection.** On a conjugation-invariant open set `Ω`, let `Dg`
be the weak derivative of `g` on the upper part of `Ω`, with `g` continuous on `Ω ∩ {0 ≤ im}` and
zero on `Ω ∩ ℝ` and `Dg` integrable on compact subsets of `Ω ∩ {0 ≤ im}`. Then the odd reflection
`planarReflection (fun _ => -1) g`, equal to `-g(conj z)` below the axis, has weak derivative
`planarReflectionFDeriv (fun _ => -1) Dg` on all of `Ω`. -/
theorem HasWeakFDerivOn.planarReflection_neg_one {Ω : Opens ℂ}
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) {g : ℂ → F} {Dg : ℂ → ℂ →L[ℝ] F}
    (hgW : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) g Dg)
    (hgc : ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (hg0 : ∀ x : ℝ, (x : ℂ) ∈ Ω → g x = 0)
    (hDg : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) Dg) :
    HasWeakFDerivOn volume Ω (TauCeti.planarReflection (fun _ : Fin 1 => (-1 : ℝ)) g)
      (planarReflectionFDeriv (fun _ : Fin 1 => (-1 : ℝ)) Dg) := by
  have := hgW.completeSpace
  have hΩ' := imDilation_mem_of_mapsTo_conj hΩ
  have hg := hgc.memLpLoc (p := 1) (μ := volume)
  have hDgI := hDg.clm_comp (ContinuousLinearMap.apply ℝ F I)
  refine basisOneI.hasWeakFDerivOn_of_forall
    ((hg.planarReflection hΩ' _).locallyIntegrableOn le_rfl Ω.isOpen.isLocallyClosed) fun i => ?_
  fin_cases i
  · simpa [planarReflectionFDeriv_apply_one] using (hgW.hasWeakLineDerivOn 1).planarReflection_one
      hΩ' hg (hDg.clm_comp (ContinuousLinearMap.apply ℝ F 1)) _
  -- The odd reflection is twice the extension by zero minus the even reflection.
  have hZ := ((hgW.hasWeakLineDerivOn I).indicator_setOf_im_nonneg hgc hg0 hDgI).const_smul
    (2 : ℝ)
  have hE := (hgW.hasWeakLineDerivOn I).planarReflection_I hΩ' hg hDgI
    (d := fun _ : Fin 1 => (1 : ℝ)) (by simp)
  simp only [Complex.coe_basisOneI, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    planarReflectionFDeriv_apply_I]
  convert hZ.sub hE using 1 <;> funext z <;> by_cases hz : 0 ≤ z.im
  · simp [hz, two_smul]
  · simp [hz, planarReflection_of_neg _ _ (not_le.1 hz)]
  · simp [hz, two_smul]
  · simp [hz, planarReflection_of_neg _ _ (not_le.1 hz)]

/-- **Odd reflection preserves `W^{1,p}`.** On a conjugation-invariant open set `Ω`, the odd
reflection of a map in `W^{1,p}_loc(Ω ∩ {0 ≤ im})`, `1 ≤ p`, that is continuous on
`Ω ∩ {0 ≤ im}` and zero on `Ω ∩ ℝ` is in `W^{1,p}_loc(Ω)`. -/
theorem MemWkpLoc.planarReflection_neg_one {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Opens ℂ}
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) {g : ℂ → F}
    (hg : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 g)
    (hgc : ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (hg0 : ∀ x : ℝ, (x : ℂ) ∈ Ω → g x = 0) :
    MemWkpLoc p Ω 1 (TauCeti.planarReflection (fun _ : Fin 1 => (-1 : ℝ)) g) := by
  have hΩ' := imDilation_mem_of_mapsTo_conj hΩ
  obtain ⟨hgp, Dg, hDg, hDgp⟩ := memWkpLoc_succ_iff.1 hg
  have hDgp' : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) Dg := memWkpLoc_zero_iff.1 hDgp
  refine memWkpLoc_succ_iff_of_isOpen.2 ⟨hgp.planarReflection hΩ' _, _,
    hDg.planarReflection_neg_one hΩ hgc hg0 (hDgp'.mono_exponent hp), ?_⟩
  have h := (((hDgp'.clm_comp (ContinuousLinearMap.apply ℝ F 1)).planarReflection hΩ'
    (fun _ : Fin 1 => (-1 : ℝ))).clm_comp (ContinuousLinearMap.smulRightL ℝ ℝ ℝ ℂ F reCLM)).add
    (((hDgp'.clm_comp (ContinuousLinearMap.apply ℝ F I)).planarReflection hΩ'
      (fun j : Fin 1 => (-1 : ℝ) * higherReflectionNode j)).clm_comp
        (ContinuousLinearMap.smulRightL ℝ ℝ ℝ ℂ F imCLM))
  refine memWkpLoc_zero_iff.2 ?_
  convert h using 1
  funext z
  refine ContinuousLinearMap.coe_injective (basisOneI.ext fun i => ?_)
  fin_cases i <;> simp [planarReflectionFDeriv_apply_one, planarReflectionFDeriv_apply_I]

end TauCeti
