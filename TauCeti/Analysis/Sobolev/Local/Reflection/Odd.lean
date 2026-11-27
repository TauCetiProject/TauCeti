/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Reflection
public import TauCeti.Analysis.Complex.LaplaceReflection
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Odd and twisted reflection of half-disc Sobolev maps

For an open `Ω ⊆ ℂ`, let `g` be weakly differentiable on the open upper part `Ω ∩ {0 < im}`, with
`g` continuous on `Ω ∩ {0 ≤ im}` and vanishing on `Ω ∩ ℝ`, and with derivative integrable on
compact subsets of `Ω ∩ {0 ≤ im}`. This file proves that the boundary term of the integration by
parts on the upper half-plane vanishes in every direction, against every smooth compactly supported
test function `χ` whose support meets `{0 ≤ im}` inside `Ω`, including those that do not vanish on
the axis
(`TauCeti.HasWeakLineDerivOn.setIntegral_fderiv_smul_eq_neg_of_continuousOn`):

`∫_{0 < im} ∂_v χ • g = -∫_{0 < im} χ • ∂_v g`.

`TauCeti.HasWeakLineDerivOn.setIntegral_fderiv_smul_eq_neg` proves this when `v` is tangent to the
axis or `χ` vanishes on it; here the vanishing is moved onto `g`. The proof tests the weak
derivative against `ψₙ χ`, where `ψₙ` is a smooth cutoff vanishing where `(n + 1) im z ≤ 1`,
near the axis, and lets `n → ∞`. The boundary layer `χ ∂_v ψₙ • g`, with
`∂_v ψₙ = TauCeti.imCutoffLayer n v.im`, lives in the strip `{0 < im ≤ 2 / (n + 1)}`, where
`∂_v ψₙ = O(n)` and the area is `O(1/n)`, while `g = o(1)` there by uniform continuity
(`TauCeti.exists_forall_norm_lt_of_im_lt`), since `g` vanishes on the axis. The rest of the
argument is shared with `TauCeti.HasWeakLineDerivOn.setIntegral_fderiv_smul_eq_neg` through
`TauCeti.HasWeakLineDerivOn.setIntegral_fderiv_smul_eq_neg_of_tendsto`.

As consequences:

* `TauCeti.HasWeakLineDerivOn.indicator_setOf_im_nonneg`,
  `TauCeti.HasWeakFDerivOn.indicator_setOf_im_nonneg`: the extension of `g` by zero below the
  axis is weakly differentiable on all of `Ω`, with derivative the extension of `∂_v g` by zero.
* `TauCeti.HasWeakFDerivOn.planarReflection_of_eq_zero`: when the node dilations map the lower
  part of `Ω` into `Ω`, the reflection `TauCeti.planarReflection d g` with any weights `d` is weakly
  differentiable on `Ω`, with derivative `TauCeti.planarReflectionFDeriv d Dg`. The weights of the
  even reflection sum to one, which is how `TauCeti.HasWeakFDerivOn.planarReflection` matches the
  two one-sided values on the axis; for other weights, such as the single weight `-1` of the odd
  reflection, equal to `-g (conj z)` for `im z < 0`, the boundary condition takes over. The
  reflection is the extension by zero plus a combination of reflections with a single weight `1`,
  each minus the extension by zero.
* `TauCeti.MemWkpLoc.planarReflection_of_eq_zero`: such a reflection of a continuous map in
  `W^{1,p}_loc(Ω ∩ {0 ≤ im})` vanishing on `Ω ∩ ℝ` is in `W^{1,p}_loc(Ω)`.
* `TauCeti.HasWeakFDerivOn.twistedReflection`: for a continuous linear map `L` and `g` continuous
  on `Ω ∩ {0 ≤ im}` with `L (g x) = g x` on `Ω ∩ ℝ`, the twisted reflection
  `TauCeti.twistedReflection L g`, equal to `L (g (conj z))` for `im z < 0`, is weakly
  differentiable on `Ω`: it is almost everywhere the even reflection of `L ∘ g` plus the extension
  by zero of `g - L ∘ g`. This is how the leading coefficient of a Cauchy–Riemann equation with a
  totally real boundary condition is reflected.
* `TauCeti.HasWeakFDerivOn.ite_conj`: the same for the reflection that keeps the values of `g` on
  the axis, which agrees with the twisted reflection almost everywhere
  (`TauCeti.ite_conj_ae_eq_twistedReflection`) and is continuous when `g` is.

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

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-! ### The boundary layer -/

/-- An integrand over the upper half-plane that vanishes off the strip `T ∩ {0 < im ≤ w}`, for
`T` in the disc of radius `ρ`, and is bounded by `c` on it, has integral at most `c · 2ρw`. -/
private theorem norm_setIntegral_le_of_strip {f : ℂ → F} {T : Set ℂ} {ρ w c : ℝ}
    (hρ : 0 ≤ ρ) (hw : 0 ≤ w) (hc : 0 ≤ c) (hTρ : T ⊆ closedBall 0 ρ)
    (hoff : ∀ z ∈ {z : ℂ | 0 < z.im} \ ({z : ℂ | 0 < z.im} ∩ (T ∩ {z | z.im ≤ w})), f z = 0)
    (hon : ∀ z ∈ {z : ℂ | 0 < z.im} ∩ (T ∩ {z | z.im ≤ w}), ‖f z‖ ≤ c) :
    ‖∫ z in {z : ℂ | 0 < z.im}, f z‖ ≤ c * (2 * ρ * w) := by
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (measurableSet_lt measurable_const measurable_im) inter_subset_left hoff]
  have hSR : {z : ℂ | 0 < z.im} ∩ (T ∩ {z | z.im ≤ w}) ⊆ Icc (-ρ) ρ ×ℂ Icc 0 w := fun z hz =>
    ⟨abs_le.1 ((abs_re_le_norm z).trans (mem_closedBall_zero_iff.1 (hTρ hz.2.1))),
      le_of_lt hz.1, hz.2.2⟩
  have hRfin : volume (Icc (-ρ) ρ ×ℂ Icc 0 w) < ⊤ :=
    (isCompact_Icc.reProdIm isCompact_Icc).measure_lt_top
  calc _ ≤ c * volume.real ({z : ℂ | 0 < z.im} ∩ (T ∩ {z | z.im ≤ w})) :=
        norm_setIntegral_le_of_norm_le_const ((measure_mono hSR).trans_lt hRfin) hon
    _ ≤ c * (2 * ρ * w) := by
        rw [show 2 * ρ * w = (ρ - -ρ) * (w - 0) by ring,
          ← Complex.volume_real_reProdIm_Icc (by linarith) hw]
        exact mul_le_mul_of_nonneg_left (measureReal_mono hSR hRfin.ne) hc

/-- **The boundary layer vanishes in the limit.** For `g` continuous on `Ω ∩ {0 ≤ im}` and zero
on `Ω ∩ ℝ`, and `χ` continuous with compact support meeting `{0 ≤ im}` inside `Ω`, the integral of
`χ imCutoffLayer n a • g` over the upper half-plane tends to zero. -/
private theorem tendsto_setIntegral_boundaryLayer {Ω : Opens ℂ} {g : ℂ → F}
    (hgc : ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (hg0 : ∀ x : ℝ, (x : ℂ) ∈ Ω → g x = 0)
    {χ : ℂ → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ∩ {z : ℂ | 0 ≤ z.im} ⊆ Ω) (a : ℝ) :
    Tendsto (fun n : ℕ => ∫ z in {z : ℂ | 0 < z.im}, (χ z * imCutoffLayer n a z) • g z) atTop
      (𝓝 0) := by
  have hclosed : IsClosed {z : ℂ | 0 ≤ z.im} := Complex.isClosed_setOfPred_le_im 0
  set T := tsupport χ ∩ {z : ℂ | 0 ≤ z.im}
  have hT : IsCompact T := hχc.isCompact.inter_right hclosed
  obtain ⟨ρ, hρ⟩ := hT.isBounded.subset_closedBall 0
  obtain ⟨B, hB0, hB⟩ := exists_abs_imCutoffLayer_le
  obtain ⟨M, hM⟩ := hχ.bounded_above_of_compact_support hχc
  set ρ' := max ρ 0
  set K := 4 * ρ' * (max M 0 * B * |a|)
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
  set f := fun z : ℂ => (χ z * imCutoffLayer n a z) • g z
  set S := {z : ℂ | 0 < z.im} ∩ (T ∩ {z : ℂ | z.im ≤ w})
  have hK0 : 0 ≤ K := by positivity
  -- Off the strip `S` the integrand vanishes; on it, it is bounded.
  have hoff : ∀ z ∈ {z : ℂ | 0 < z.im} \ S, f z = 0 := by
    rintro z ⟨hz, hzS⟩
    have hz0 : 0 < z.im := hz
    by_cases hzT : z ∈ tsupport χ
    · have hzw : w < z.im := not_le.1 fun h => hzS ⟨hz, ⟨hzT, hz0.le⟩, h⟩
      rw [div_lt_iff₀ hn1] at hzw
      simp [f, imCutoffLayer_of_two_le (by linarith : 2 ≤ ((n : ℝ) + 1) * z.im)]
    · simp [f, image_eq_zero_of_notMem_tsupport hzT]
  have hon : ∀ z ∈ S, ‖f z‖ ≤ max M 0 * (B * (((n : ℝ) + 1) * |a|)) * (ε / (K + 1)) := by
    rintro z ⟨hz, ⟨hzT, -⟩, hzw⟩
    have hgz := hgδ z ⟨hzT, (le_of_lt hz : (0 : ℝ) ≤ z.im)⟩ (lt_of_le_of_lt hzw hw)
    rw [norm_smul, norm_mul, Real.norm_eq_abs]
    gcongr
    · exact (hM z).trans (le_max_left _ _)
    · exact hB n a z
  calc ‖∫ z in {z : ℂ | 0 < z.im}, f z‖
        ≤ (max M 0 * (B * (((n : ℝ) + 1) * |a|)) * (ε / (K + 1))) * (2 * ρ' * w) :=
        norm_setIntegral_le_of_strip (le_max_right _ _) (by positivity) (by positivity)
          (hρ.trans (closedBall_subset_closedBall (le_max_left _ _))) hoff hon
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
      -∫ z in {z : ℂ | 0 < z.im}, χ z • g' z :=
  hgW.setIntegral_fderiv_smul_eq_neg_of_tendsto hgc.memLpLoc hg' hχ hχc hχΩ
    (tendsto_setIntegral_boundaryLayer hgc hg0 hχ.continuous hχc hχΩ v.im)

/-! ### Extension by zero and odd reflection -/

omit [NormedSpace ℝ F] in
/-- The extension by zero of a function locally integrable up to the real axis is locally
integrable on `Ω`. -/
theorem MemLpLoc.locallyIntegrableOn_indicator_setOf_im_nonneg {Ω : Opens ℂ} {g : ℂ → F}
    (hg : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g) :
    LocallyIntegrableOn ({z : ℂ | 0 ≤ z.im}.indicator g) Ω :=
  LocallyIntegrableOn.indicator_of_closure
    (by rw [(Complex.isClosed_setOfPred_le_im 0).closure_eq]
        exact hg.locallyIntegrableOn le_rfl (Ω.isOpen.isLocallyClosed_inter_setOfPred_le_im 0))
    (measurableSet_le measurable_const measurable_im).nullMeasurableSet

/-- **Extension by zero, from integration by parts up to the axis.** If `g` and `g'` are
integrable on compact subsets of `Ω ∩ {0 ≤ im}` and the integration-by-parts identity in the
direction `v` holds on the upper half-plane against every smooth compactly supported test
function on `Ω`, then the extensions by zero below the axis satisfy the weak derivative relation
on all of `Ω`. -/
theorem hasWeakLineDerivOn_indicator_setOf_im_nonneg_of_setIntegral [CompleteSpace F]
    {Ω : Opens ℂ} {g g' : ℂ → F} {v : ℂ} (hg : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g)
    (hg' : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g')
    (hibp : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∫ z in {z : ℂ | 0 < z.im}, fderiv ℝ φ z v • g z = -∫ z in {z : ℂ | 0 < z.im}, φ z • g' z) :
    HasWeakLineDerivOn volume Ω ({z : ℂ | 0 ≤ z.im}.indicator g)
      ({z : ℂ | 0 ≤ z.im}.indicator g') v := by
  refine (hasWeakLineDerivOn_iff hg.locallyIntegrableOn_indicator_setOf_im_nonneg
    hg'.locallyIntegrableOn_indicator_setOf_im_nonneg).2 fun φ hφ hφc hφΩ => ?_
  have hH : MeasurableSet {z : ℂ | 0 ≤ z.im} := measurableSet_le measurable_const measurable_im
  have hind (a : ℂ → ℝ) (f : ℂ → F) : (fun z => a z • {z : ℂ | 0 ≤ z.im}.indicator f z) =
      {z : ℂ | 0 ≤ z.im}.indicator fun z => a z • f z :=
    funext fun z => (indicator_smul_apply _ _ _ _).symm
  simp_rw [((hφ.differentiable (by simp)) _).lineDeriv_eq_fderiv]
  rw [hind (fun z => fderiv ℝ φ z v) g, hind φ g', integral_indicator hH, integral_indicator hH,
    setIntegral_congr_set (Complex.setOf_le_im_ae_eq 0),
    setIntegral_congr_set (Complex.setOf_le_im_ae_eq 0)]
  exact hibp φ hφ hφc hφΩ

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
  refine hasWeakLineDerivOn_indicator_setOf_im_nonneg_of_setIntegral hgc.memLpLoc hg'
    fun φ hφ hφc hφΩ => ?_
  exact hgW.setIntegral_fderiv_smul_eq_neg_of_continuousOn hgc hg0 hg' hφ hφc
    fun z hz => hφΩ hz.1

/-- **Extension by zero, full derivative.** If `Dg` is the weak derivative of `g` on the upper
part of `Ω`, with `g` continuous on `Ω ∩ {0 ≤ im}` and zero on `Ω ∩ ℝ` and `Dg` integrable on
compact subsets of `Ω ∩ {0 ≤ im}`, then the extension of `Dg` by zero below the axis is the weak
derivative of the extension of `g` by zero on all of `Ω`. -/
theorem HasWeakFDerivOn.indicator_setOf_im_nonneg {Ω : Opens ℂ} {g : ℂ → F} {Dg : ℂ → ℂ →L[ℝ] F}
    (hgW : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) g Dg)
    (hgc : ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (hg0 : ∀ x : ℝ, (x : ℂ) ∈ Ω → g x = 0)
    (hDg : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) Dg) :
    HasWeakFDerivOn volume Ω ({z : ℂ | 0 ≤ z.im}.indicator g)
      ({z : ℂ | 0 ≤ z.im}.indicator Dg) := by
  refine hasWeakFDerivOn_iff.2 fun v => ?_
  convert (hasWeakFDerivOn_iff.1 hgW v).indicator_setOf_im_nonneg hgc hg0
    (hDg.clm_comp (ContinuousLinearMap.apply ℝ F v)) using 1
  funext z
  by_cases hz : 0 ≤ z.im <;> simp [hz]

/-- **Weak derivative of a reflection of a map vanishing on the axis.** On an open set `Ω` whose
lower part the node dilations map into `Ω`, let `Dg` be the weak derivative of `g` on the upper part
of `Ω`, with `g` continuous on `Ω ∩ {0 ≤ im}` and zero on `Ω ∩ ℝ` and `Dg` integrable on compact
subsets of `Ω ∩ {0 ≤ im}`. Then for every choice of weights `d`, `planarReflectionFDeriv d Dg` is
the weak derivative of `planarReflection d g` on all of `Ω`. With the single weight `-1` this is the
odd reflection, equal to `-g(conj z)` below the axis.

Unlike `TauCeti.HasWeakFDerivOn.planarReflection`, the weights need not sum to one: the reflection
is the extension by zero plus a combination of reflections with a single weight `1`, minus the
extension by zero. -/
theorem HasWeakFDerivOn.planarReflection_of_eq_zero {Ω : Opens ℂ}
    (hΩ : ∀ z ∈ Ω, z.im < 0 → ∀ j : Fin k, imDilation (higherReflectionNode j) z ∈ Ω)
    {g : ℂ → F} {Dg : ℂ → ℂ →L[ℝ] F}
    (hgW : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) g Dg)
    (hgc : ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (hg0 : ∀ x : ℝ, (x : ℂ) ∈ Ω → g x = 0)
    (hDg : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) Dg) (d : Fin k → ℝ) :
    HasWeakFDerivOn volume Ω (TauCeti.planarReflection d g) (planarReflectionFDeriv d Dg) := by
  have := hgW.completeSpace
  have hZ := hgW.indicator_setOf_im_nonneg hgc hg0 hDg
  have hE (j : Fin k) := hgW.planarReflection hΩ hgc.memLpLoc hDg
    (d := Pi.single j (1 : ℝ)) (by simp)
  have h := hZ.add (HasWeakFDerivOn.sum Finset.univ fun j _ => ((hE j).sub hZ).const_smul (d j))
  convert h using 1 <;> funext z <;> by_cases hz : 0 ≤ z.im
  · simp [hz]
  · simp [hz, planarReflection_of_neg _ _ (not_le.1 hz), Pi.single_apply]
  · simp [hz]
  · simp [hz, planarReflectionFDeriv_of_neg _ _ (not_le.1 hz), Pi.single_apply]

/-- **Reflection of a map vanishing on the axis preserves `W^{1,p}`.** On an open set `Ω` whose
lower part the node dilations map into `Ω`, the reflection with any weights of a map in
`W^{1,p}_loc(Ω ∩ {0 ≤ im})`, `1 ≤ p`, that is continuous on `Ω ∩ {0 ≤ im}` and zero on `Ω ∩ ℝ` is
in `W^{1,p}_loc(Ω)`. With the single weight `-1` this is the odd reflection. -/
theorem MemWkpLoc.planarReflection_of_eq_zero {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Opens ℂ}
    (hΩ : ∀ z ∈ Ω, z.im < 0 → ∀ j : Fin k, imDilation (higherReflectionNode j) z ∈ Ω)
    {g : ℂ → F}
    (hg : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 g)
    (hgc : ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (hg0 : ∀ x : ℝ, (x : ℂ) ∈ Ω → g x = 0)
    (d : Fin k → ℝ) :
    MemWkpLoc p Ω 1 (TauCeti.planarReflection d g) := by
  obtain ⟨hgp, Dg, hDg, hDgp⟩ := memWkpLoc_succ_iff.1 hg
  have hDgp' : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) Dg := memWkpLoc_zero_iff.1 hDgp
  refine memWkpLoc_succ_iff_of_isOpen.2 ⟨hgp.planarReflection hΩ _, _,
    hDg.planarReflection_of_eq_zero hΩ hgc hg0 (hDgp'.mono_exponent hp) d, ?_⟩
  exact memWkpLoc_zero_iff.2 (hDgp'.planarReflectionFDeriv hΩ _)

/-! ### Twisted reflection -/

/-- **Weak derivative of a twisted reflection.** On an open set `Ω` whose lower part conjugation
maps into `Ω`, let `Dg` be the weak derivative of `g` on the upper part of `Ω`, with `g` continuous
on `Ω ∩ {0 ≤ im}` and `Dg` integrable on compact subsets of `Ω ∩ {0 ≤ im}`, and let `L` be a
continuous linear map fixing the values of `g` on `Ω ∩ ℝ`. Then the twisted reflection of `g` by
`L`, equal to `L (g (conj z))` below the axis, has weak derivative on all of `Ω` the twisted
reflection of `Dg` by `D ↦ L ∘ D ∘ conj`.

The twisted reflection is almost everywhere the even reflection of `L ∘ g` plus the extension by
zero of `g - L ∘ g`, which vanishes on the axis. For `L = -1` this is the odd reflection, and for
`L = 1` the even reflection, with no boundary condition. -/
theorem HasWeakFDerivOn.twistedReflection {Ω : Opens ℂ} (hΩ : ∀ z ∈ Ω, z.im < 0 → conj z ∈ Ω)
    (L : F →L[ℝ] F) {g : ℂ → F} {Dg : ℂ → ℂ →L[ℝ] F}
    (hgW : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) g Dg)
    (hgc : ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hg0 : ∀ x : ℝ, (x : ℂ) ∈ Ω → L (g x) = g x)
    (hDg : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) Dg) :
    HasWeakFDerivOn volume Ω (TauCeti.twistedReflection L g)
      (TauCeti.twistedReflection ((ContinuousLinearMap.compL ℝ ℂ F F L).comp
        ((ContinuousLinearMap.compL ℝ ℂ ℂ F).flip (conjCLE : ℂ →L[ℝ] ℂ))) Dg) := by
  have := hgW.completeSpace
  have hΩ' := imDilation_higherReflectionNode_fin_one_mem hΩ
  have hE := (hgW.clm_comp L).planarReflection hΩ' (hgc.memLpLoc.clm_comp L)
    (hDg.clm_comp (ContinuousLinearMap.compL ℝ ℂ F F L)) (d := fun _ : Fin 1 => 1) (by simp)
  have hZ := (hgW.sub (hgW.clm_comp L)).indicator_setOf_im_nonneg
    (hgc.sub (L.continuous.comp_continuousOn hgc)) (fun x hx => sub_eq_zero.2 (hg0 x hx).symm)
    (hDg.sub (hDg.clm_comp (ContinuousLinearMap.compL ℝ ℂ F F L)))
  refine ((hE.add hZ).congr_ae ?_).congr_ae_deriv ?_ <;>
    filter_upwards [ae_restrict_of_ae Complex.ae_im_ne_zero] with z hz <;>
    rcases lt_or_gt_of_ne hz with hz | hz
  · simp [hz, not_le.2 hz, imDilation_higherReflectionNode_fin_one]
  · simp [hz, hz.le]
  · ext v
    simp [hz, not_le.2 hz, imDilation_higherReflectionNode_fin_one_eq_conjCLE]
  · simp [hz, hz.le]

/-- **Weak derivative of the continuous twisted reflection.** Under the hypotheses of
`TauCeti.HasWeakFDerivOn.twistedReflection`, the reflection of `g` twisted by `L` that keeps the
values of `g` on the real axis, equal to `g` on `0 ≤ im` and to `L (g (conj z))` below, has the
same weak derivative on `Ω`. Unlike the twisted reflection, it is continuous when `g` is
continuous up to the axis. -/
theorem HasWeakFDerivOn.ite_conj {Ω : Opens ℂ} (hΩ : ∀ z ∈ Ω, z.im < 0 → conj z ∈ Ω)
    (L : F →L[ℝ] F) {g : ℂ → F} {Dg : ℂ → ℂ →L[ℝ] F}
    (hgW : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) g Dg)
    (hgc : ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hg0 : ∀ x : ℝ, (x : ℂ) ∈ Ω → L (g x) = g x)
    (hDg : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) Dg) :
    HasWeakFDerivOn volume Ω (fun z ↦ if 0 ≤ z.im then g z else L (g (conj z)))
      (TauCeti.twistedReflection ((ContinuousLinearMap.compL ℝ ℂ F F L).comp
        ((ContinuousLinearMap.compL ℝ ℂ ℂ F).flip (conjCLE : ℂ →L[ℝ] ℂ))) Dg) :=
  (hgW.twistedReflection hΩ L hgc hg0 hDg).congr_ae
    (ae_restrict_of_ae (ite_conj_ae_eq_twistedReflection L g).symm)

end TauCeti
