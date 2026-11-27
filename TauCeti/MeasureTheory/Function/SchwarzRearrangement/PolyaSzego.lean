/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.MeasureTheory.Function.SchwarzRearrangement.CriticalValues
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.BoundedVariation.LevelSurface
import TauCeti.Analysis.BoundedVariation.SchwarzRearrangement
import TauCeti.Analysis.Calculus.FDeriv.Clamp
import TauCeti.Analysis.Calculus.FDeriv.Measurable
import TauCeti.Analysis.Calculus.FDeriv.Norm
import TauCeti.Analysis.Convex.Monotone
import TauCeti.MeasureTheory.Function.Coarea.Critical
import TauCeti.MeasureTheory.Function.Monotone
import TauCeti.MeasureTheory.Integral.ReciprocalWeight

/-!
# The Pólya–Szegő inequality for Lipschitz functions

Let `h` be a real Lipschitz function on a finite-dimensional real inner product space `E` equipped
with an additive Haar measure `μ`, and let `h*` be the real Schwarz rearrangement of its positive
part. For every convex `Φ` on `[0, ∞)` with `Φ 0 ≤ 0`,

`∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h* x‖) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) ∂μ`

(`LipschitzWith.lintegral_ofReal_comp_norm_fderiv_toReal_schwarzRearrangement_le`), with no sign,
decay, monotonicity, or positive-dimension restrictions, as extended nonnegative integrals of the
positive part of `Φ`. Gradients are the totalized Fréchet derivatives, which agree almost everywhere
with the Rademacher gradients of these Lipschitz functions. The case `Φ(s) = s` is the `L¹`
comparison of gradients (`LipschitzWith.lintegral_enorm_fderiv_toReal_schwarzRearrangement_le`).
When `Φ` is also nondecreasing with `Φ 0 = 0`, integrability of `x ↦ Φ ‖fderiv ℝ h x‖` under `μ`
transfers to `h*` (`LipschitzWith.integrable_comp_norm_fderiv_toReal_schwarzRearrangement`) with the
corresponding Bochner integral bound
(`LipschitzWith.integral_comp_norm_fderiv_toReal_schwarzRearrangement_le`).

## Strategy

For Lebesgue `volume` in positive dimension when positive superlevel sets `{h > t}` have finite
volume, the coarea formula writes `∫ Φ(‖∇g‖)` as the integral over the levels `t` of the level
contributions `F_g(t) = ∫_{{g = t} ∩ {∇g ≠ 0}} Φ(‖∇g‖) ‖∇g‖⁻¹ dHⁿ⁻¹`
(`ConvexOn.lintegral_ofReal_comp_norm_fderiv_eq_lintegral_setLIntegral`). We compare `F_{h*}(t)`
with `F_h(t)` at almost every level `t > 0`, using the following inputs.

* **Volume.** The level integrals `m_g(t) = ∫_{{g = t} ∩ {∇g ≠ 0}} ‖∇g‖⁻¹ dHⁿ⁻¹` satisfy
  `m_h(t) ≤ -μ'(t) = m_{h*}(t)`, where `μ(t) = |{h > t}|` is the common distribution function.
* **Area.** The regular part of the level surface of `h*` has at most the area of that of `h`:
  the level surfaces carry the perimeters of the superlevel sets, the rearranged superlevel set is
  the ball of the same volume, and the critical part of almost every level surface of `h` is
  Hausdorff-null. The sharp isoperimetric inequality then compares the two perimeters.
* **Radial structure.** The gradient norm of the radially nonincreasing function `h*` is constant
  on the regular part of each level set (`TauCeti.norm_fderiv_eq_of_antitone_norm`).

Write `P_g(t)` for the area of the regular part of the level surface of `g`. A tangent line to
the positive part of `Φ` at the constant gradient norm `c` of `h*` on its level `t` has slope
`k ≥ 0` and intercept `-d ≤ 0` (`ConvexOn.setLIntegral_ofReal_mul_inv_le`). It lies below that
positive part, so `F_h(t) + d m_h(t) ≥ k P_h(t)`, with equality
`F_{h*}(t) + d m_{h*}(t) = k P_{h*}(t)` for `h*`. The volume and area comparisons then give
`F_{h*}(t) ≤ F_h(t)`.

Subtracting the infimum of nonnegative levels of finite superlevel volume removes any decay
assumption on `h`, truncating `Φ` at zero (`ConvexOn.monotoneOn_max_const`) handles non-monotone
convex integrands during that shift, and Haar uniqueness (`Measure.isAddLeftInvariant_eq_smul`)
transfers the inequality from `volume` to any additive Haar measure `μ`.

## Main declarations

* `LipschitzWith.lintegral_ofReal_comp_norm_fderiv_toReal_schwarzRearrangement_le`: extended
  convex-integrand Pólya–Szegő inequality for arbitrary Lipschitz functions and additive Haar
  measures.
* `LipschitzWith.lintegral_enorm_fderiv_toReal_schwarzRearrangement_le`: extended `L¹` gradient
  comparison under rearrangement.
* `LipschitzWith.integrable_comp_norm_fderiv_toReal_schwarzRearrangement` and
  `LipschitzWith.integral_comp_norm_fderiv_toReal_schwarzRearrangement_le`: Bochner integrability
  and integral comparison for convex nondecreasing `Φ` with `Φ 0 = 0`.

## References

* G. Bianchi, R. J. Gardner, P. Gronchi, M. Kiderlen, *The Pólya–Szegő inequality for smoothing
  rearrangements*, J. Funct. Anal. **287** (2024), Theorem 5.8.
* J. E. Brothers, W. P. Ziemer, *Minimal rearrangements of Sobolev functions*, J. Reine Angew.
  Math. **384** (1988), 153–179.
* E. H. Lieb, M. Loss, *Analysis*, 2nd ed., AMS, 2001, Theorem 7.17 and Lemma 7.17.
-/

public section

open MeasureTheory Set Filter Module
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The area comparison.** For a Lipschitz `h` whose positive superlevel sets have finite volume
and its real Schwarz rearrangement `h*`, at almost every level `t > 0` the regular part
`{h* = t} ∩ {∇h* ≠ 0}` of the level surface of `h*` has at most the area `Hⁿ⁻¹` of the regular part
of the level surface of `h`. -/
private theorem ae_euclideanHausdorffMeasure_regularLevel_le [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {K : ℝ≥0} {h : E → ℝ}
    (hh : LipschitzWith K h) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) :
    ∀ᵐ t, 0 < t →
      μHE[finrank ℝ E - 1] ({x | fderiv ℝ (fun z ↦ (schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x ≠ 0} ∩
          (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) ⁻¹' {t})
        ≤ μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) := by
  set f : E → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (h y)
  set w : E → ℝ := fun z ↦ (schwarzRearrangement volume f z).toReal
  have hfS := hh.schwarzRearrangement_ofReal_ne_top volume (hfin 1 one_pos)
  have hcrit := hh.ae_euclideanHausdorffMeasure_setOf_fderiv_eq_zero_inter_preimage_eq_zero
    volume (by simpa using Nat.one_le_iff_ne_zero.2 (finrank_pos (R := ℝ) (M := E)).ne')
  -- Almost every level surface carries the perimeter of its superlevel set.
  filter_upwards [(lipschitzWith_toReal_schwarzRearrangement volume
      hh).locallyLipschitz.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure ⊤,
    hh.locallyLipschitz.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure ⊤, hcrit]
    with t hPw hPh hcrit ht
  rw [finrank_self] at hcrit
  simp only [TopologicalSpace.Opens.coe_top, univ_inter] at hPw hPh
  -- The superlevel sets of `w` are the rearranged superlevel sets of `h`.
  have hset : {x | t < w x} = {x | ENNReal.ofReal t < schwarzRearrangement volume f x} := by
    ext x
    exact (ENNReal.ofReal_lt_iff_lt_toReal ht.le (hfS x)).symm
  have hsource : {x | ENNReal.ofReal t < f x} = {x | t < h x} := by
    ext x
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le
  have hper : perimeter volume ⊤ {x | t < w x} ≤ perimeter volume ⊤ {x | t < h x} := by
    have hs : NullMeasurableSet {x | ENNReal.ofReal t < f x} := nullMeasurableSet_lt
      aemeasurable_const hh.continuous.measurable.ennreal_ofReal.aemeasurable
    rw [hset, ← hsource]
    exact hs.perimeter_setOf_lt_schwarzRearrangement_le
  -- The critical part of the level surface of `h` is null.
  calc _ ≤ μHE[finrank ℝ E - 1] (w ⁻¹' {t}) := measure_mono inter_subset_right
    _ ≤ μHE[finrank ℝ E - 1] (h ⁻¹' {t}) := by rw [← hPw, ← hPh]; exact hper
    _ ≤ μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) +
        μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x = 0} ∩ h ⁻¹' {t}) := by
      refine (measure_mono fun x hx ↦ ?_).trans (measure_union_le _ _)
      by_cases hx0 : fderiv ℝ h x = 0
      · exact Or.inr ⟨hx0, hx⟩
      · exact Or.inl ⟨hx0, hx⟩
    _ = _ := by rw [hcrit, add_zero]

/-- **The level comparison.** For a Lipschitz `h` whose positive superlevel sets have finite volume
and its real Schwarz rearrangement `h*`, at almost every level `t > 0` the contribution
`∫_{{h* = t} ∩ {∇h* ≠ 0}} Φ(‖∇h*‖) ‖∇h*‖⁻¹ dHⁿ⁻¹` of that level to `∫ Φ(‖∇h*‖)` is at most the
corresponding contribution for `h`. -/
private theorem ae_setLIntegral_ofReal_comp_norm_fderiv_toReal_schwarzRearrangement_le
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {K : ℝ≥0}
    {h : E → ℝ} (hh : LipschitzWith K h) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦ0 : Φ 0 ≤ 0) :
    ∀ᵐ t, 0 < t →
      ∫⁻ x in {x | fderiv ℝ (fun z ↦ (schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x ≠ 0} ∩
          (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) ⁻¹' {t},
        ENNReal.ofReal (Φ ‖fderiv ℝ (fun z ↦ (schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) *
        ‖fderiv ℝ (fun z ↦ (schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1] ≤
      ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t},
        ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) * ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1] := by
  have hfS := hh.schwarzRearrangement_ofReal_ne_top volume (hfin 1 one_pos)
  -- The rearrangement is radially nonincreasing, so its gradient norm is constant on each level.
  have hanti (x y : E) (hxy : ‖x‖ ≤ ‖y‖) :
      (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) y).toReal ≤
        (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x).toReal :=
    ENNReal.toReal_mono (hfS x) (schwarzRearrangement_le_of_norm_le volume _ hxy)
  -- The level integrals of `‖∇h‖⁻¹` compare through the distribution function.
  filter_upwards [MeasureTheory.ae_setLIntegral_inv_enorm_fderiv_le_ofReal_neg_deriv hfin,
    hh.ae_setLIntegral_inv_enorm_fderiv_toReal_schwarzRearrangement_eq_ofReal_neg_deriv hfin,
    ae_euclideanHausdorffMeasure_regularLevel_le hh hfin] with t hm hm' hP ht
  have hmeas {g : E → ℝ} : MeasurableSet ({x | fderiv ℝ g x ≠ 0} ∩ g ⁻¹' {t}) := by
    rw [inter_comm]
    exact measurableSet_preimage_inter_setOf_fderiv_ne_zero (measurableSet_singleton t)
  refine hΦ.setLIntegral_ofReal_mul_inv_le hΦ0 hmeas hmeas (measurable_fderiv ℝ h)
    (fun x hx ↦ hx.1) (fun x hx ↦ hx.1) (fun x hx y hy ↦ ?_) (hP ht)
    ((hm ht).trans (hm' ht).ge) ((hm' ht).trans_ne ENNReal.ofReal_ne_top)
  exact norm_fderiv_eq_of_antitone_norm hanti hx.1 hy.1 (hx.2.trans hy.2.symm)

end TauCeti

namespace LipschitzWith

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {K : ℝ≥0} {h : E → ℝ}

/-- Core Lebesgue-`volume` Pólya–Szegő inequality on a nontrivial space when positive superlevel
sets `{h > t}` have finite volume. -/
private theorem lintegral_ofReal_comp_norm_fderiv_volume_le_of_ne_top [Nontrivial E]
    (hh : LipschitzWith K h) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦ0 : Φ 0 ≤ 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ (fun z ↦ (schwarzRearrangement volume
        (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) := by
  rw [hΦ.lintegral_ofReal_comp_norm_fderiv_eq_lintegral_setLIntegral hΦ0,
    hΦ.lintegral_ofReal_comp_norm_fderiv_eq_lintegral_setLIntegral hΦ0]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_setLIntegral_ofReal_comp_norm_fderiv_toReal_schwarzRearrangement_le hh hfin
    hΦ hΦ0, volume.ae_ne (0 : ℝ)] with t ht ht0
  rcases lt_or_gt_of_ne ht0 with htneg | htpos
  · -- The rearrangement is nonnegative, so its negative levels are empty.
    have hempty : (fun z ↦ (schwarzRearrangement volume
        (fun y ↦ ENNReal.ofReal (h y)) z).toReal) ⁻¹' {t} = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ (htneg.trans_le ENNReal.toReal_nonneg).ne' hx
    simp [hempty]
  · exact ht htpos

/-- Nonnegative levels at which the strict superlevel set of `h` has finite Lebesgue volume. -/
private def finiteVolumeLevels (h : E → ℝ) : Set ℝ :=
  {s : ℝ | 0 ≤ s ∧ volume {x | s < h x} ≠ ∞}

/-- `finiteVolumeLevels h` is bounded below by `0`. -/
private theorem bddBelow_finiteVolumeLevels (h : E → ℝ) : BddBelow (finiteVolumeLevels h) :=
  ⟨0, fun _ hs ↦ hs.1⟩

/-- The infimum of `finiteVolumeLevels h` is nonnegative. -/
private theorem sInf_finiteVolumeLevels_nonneg (h : E → ℝ) :
    0 ≤ sInf (finiteVolumeLevels h) :=
  Real.sInf_nonneg fun _ hs ↦ hs.1

/-- Shifting `h` at `c = sInf (finiteVolumeLevels h)` commutes with extended Schwarz rearrangement
up to `+ ENNReal.ofReal c`. -/
private theorem schwarzRearrangement_ofReal_eq_add_sInf [Nontrivial E] (h : E → ℝ) (x : E) :
    schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x =
      schwarzRearrangement volume
        (fun y ↦ ENNReal.ofReal (max (h y - sInf (finiteVolumeLevels h)) 0)) x +
        ENNReal.ofReal (sInf (finiteVolumeLevels h)) := by
  set c := sInf (finiteVolumeLevels h)
  have hc0 : 0 ≤ c := sInf_finiteVolumeLevels_nonneg h
  rw [← congrFun (schwarzRearrangement_add_const volume _ _) x]
  refine eq_of_forall_lt_iff fun t ↦ ?_
  rw [lt_schwarzRearrangement_iff, lt_schwarzRearrangement_iff]
  rcases lt_or_ge t (ENNReal.ofReal c) with htc | hct
  · have ht_fin : t ≠ ∞ := (lt_trans htc ENNReal.ofReal_lt_top).ne
    have htr_not : t.toReal ∉ finiteVolumeLevels h :=
      notMem_of_lt_csInf (ENNReal.toReal_lt_of_lt_ofReal htc) (bddBelow_finiteVolumeLevels h)
    have hvol : volume {y | t < ENNReal.ofReal (h y)} = ∞ := by
      simp_rw [ENNReal.lt_ofReal_iff_toReal_lt ht_fin]
      by_contra hne
      exact htr_not ⟨ENNReal.toReal_nonneg, hne⟩
    have huniv : {y | t < ENNReal.ofReal (max (h y - c) 0) + ENNReal.ofReal c} = univ :=
      eq_univ_of_forall fun _ ↦ htc.trans_le le_add_self
    rw [hvol, huniv, measure_univ_of_isAddLeftInvariant]
  · rcases eq_or_ne t ∞ with rfl | ht_fin
    · simp
    · suffices {y | t < ENNReal.ofReal (h y)} =
          {y | t < ENNReal.ofReal (max (h y - c) 0) + ENNReal.ofReal c} by rw [this]
      ext y
      simp only [mem_ofPred_eq, ← ENNReal.ofReal_add (le_max_right _ _) hc0,
        ENNReal.lt_ofReal_iff_toReal_lt ht_fin]
      have hcs : c ≤ t.toReal := (ENNReal.ofReal_le_iff_le_toReal ht_fin).1 hct
      grind

/-- Removing the finite-superlevel-measure hypothesis for convex nondecreasing `Φ` with `Φ 0 = 0`
by shifting `h` at `sInf (finiteVolumeLevels h)` (or noting `(h⁺)* = ∞`, so `((h⁺)*).toReal = 0`,
when `finiteVolumeLevels h` is empty). -/
private theorem lintegral_ofReal_comp_norm_fderiv_volume_le_of_monotoneOn [Nontrivial E]
    (hh : LipschitzWith K h) {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ)
    (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ (fun z ↦
        (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) := by
  rcases (finiteVolumeLevels h).eq_empty_or_nonempty with hSempty | hSne
  · have htop : ∀ x, schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x = ∞ :=
      schwarzRearrangement_ofReal_eq_top_of_forall_measure_eq_top fun s hs ↦ by
        by_contra hfin
        exact (hSempty ▸ notMem_empty s) ⟨hs, hfin⟩
    simp [htop, hΦ0]
  · set c := sInf (finiteVolumeLevels h)
    let hc_fun : E → ℝ := fun x ↦ max (h x - c) 0
    have hhc_lip : LipschitzWith K hc_fun :=
      (LipschitzWith.of_dist_le_mul fun x y ↦ by
        simpa [dist_sub_right] using hh.dist_le_mul x y).max_const 0
    have hhc_fin (t : ℝ) (ht : 0 < t) : volume {x | t < hc_fun x} ≠ ∞ := by
      obtain ⟨s, hsS, hsc⟩ :=
        (csInf_lt_iff (bddBelow_finiteVolumeLevels h) hSne).1 (lt_add_of_pos_right c ht)
      refine ne_top_of_le_ne_top hsS.2 (measure_mono fun x hx ↦ ?_)
      simp only [hc_fun, mem_ofPred_eq] at hx ⊢
      grind
    have hhc_ne := hhc_lip.schwarzRearrangement_ofReal_ne_top volume (hhc_fin 1 one_pos)
    have hval_eq : (fun z ↦ (schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) z).toReal) =
        fun z ↦ (schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (hc_fun y)) z).toReal + c := by
      ext z
      rw [schwarzRearrangement_ofReal_eq_add_sInf h z,
        ENNReal.toReal_add (hhc_ne z) ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (sInf_finiteVolumeLevels_nonneg h)]
    simp_rw [hval_eq, fderiv_add_const]
    refine (lintegral_ofReal_comp_norm_fderiv_volume_le_of_ne_top hhc_lip hhc_fin hΦ hΦ0.le).trans
      (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (hΦm (norm_nonneg _) (norm_nonneg _) ?_))
    simp only [hc_fun]
    rw [fderiv_max_const_eq_indicator]
    refine (norm_indicator_le_norm_self _ x).trans_eq ?_
    rw [fderiv_sub_const]

/-- Lebesgue-`volume` form of the Lipschitz convex-integrand Pólya–Szegő inequality without
superlevel-finiteness or monotonicity hypotheses. -/
private theorem lintegral_ofReal_comp_norm_fderiv_volume_le (hh : LipschitzWith K h)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦ0 : Φ 0 ≤ 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ (fun z ↦
        (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have hzero (g : E → ℝ) (x : E) : fderiv ℝ g x = 0 :=
      ContinuousLinearMap.ext fun v ↦ by rw [Subsingleton.elim v 0, map_zero, map_zero]
    simp [hzero, ENNReal.ofReal_eq_zero.2 hΦ0]
  let Ψ : ℝ → ℝ := fun s ↦ max (Φ s) 0
  have hΨ_ofReal (r : ℝ) : ENNReal.ofReal (Φ r) = ENNReal.ofReal (Ψ r) := by
    simp [Ψ, ENNReal.ofReal_max]
  have hΨ0 : Ψ 0 = 0 := max_eq_right hΦ0
  have hΨ_conv : ConvexOn ℝ (Ici 0) Ψ := hΦ.sup (convexOn_const 0 (convex_Ici 0))
  have hΨ_mono : MonotoneOn Ψ (Ici 0) := by
    simpa only [inter_self] using hΦ.monotoneOn_max_const (mem_Ici.2 le_rfl) hΦ0
  simp_rw [hΨ_ofReal]
  exact lintegral_ofReal_comp_norm_fderiv_volume_le_of_monotoneOn hh hΨ_conv hΨ_mono hΨ0

/-- **The Pólya–Szegő inequality for Lipschitz functions.** For any additive Haar measure `μ` on
`E`, any `K`-Lipschitz function `h : E → ℝ`, and any `Φ : ℝ → ℝ` convex on `[0, ∞)` with `Φ 0 ≤ 0`,
the real Schwarz rearrangement `h*` of the positive part of `h` satisfies

`∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h* x‖) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) ∂μ`,

where both sides are extended integrals of the positive part of `Φ`, finite or infinite, and the
gradients are the totalized Fréchet derivatives. -/
theorem lintegral_ofReal_comp_norm_fderiv_toReal_schwarzRearrangement_le
    (μ : Measure E) [μ.IsAddHaarMeasure] (hh : LipschitzWith K h)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦ0 : Φ 0 ≤ 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ (fun z ↦
        (schwarzRearrangement μ (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) ∂μ := by
  have hc₀ : (Measure.addHaarScalarFactor μ volume : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume).ne'
  have hrearr : schwarzRearrangement μ (fun y ↦ ENNReal.ofReal (h y)) =
      schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) := by
    rw [Measure.isAddLeftInvariant_eq_smul μ volume, ENNReal.smul_def,
      schwarzRearrangement_smul_measure volume hc₀ ENNReal.coe_ne_top]
  rw [hrearr]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul μ volume, ENNReal.smul_def]
  conv_rhs => rw [Measure.isAddLeftInvariant_eq_smul μ volume, ENNReal.smul_def]
  rw [lintegral_smul_measure, lintegral_smul_measure]
  exact mul_le_mul_right (lintegral_ofReal_comp_norm_fderiv_volume_le hh hΦ hΦ0) _

/-- **`L¹` comparison of gradients under rearrangement.** For any additive Haar measure `μ` on `E`
and any `K`-Lipschitz function `h : E → ℝ`, the real Schwarz rearrangement `h*` of the positive part
of `h` satisfies `∫⁻ x, ‖fderiv ℝ h* x‖ₑ ∂μ ≤ ∫⁻ x, ‖fderiv ℝ h x‖ₑ ∂μ`. -/
theorem lintegral_enorm_fderiv_toReal_schwarzRearrangement_le
    (μ : Measure E) [μ.IsAddHaarMeasure] (hh : LipschitzWith K h) :
    ∫⁻ x, ‖fderiv ℝ (fun z ↦ (schwarzRearrangement μ
        (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖ₑ ∂μ ≤ ∫⁻ x, ‖fderiv ℝ h x‖ₑ ∂μ := by
  simpa only [id, ofReal_norm] using
    hh.lintegral_ofReal_comp_norm_fderiv_toReal_schwarzRearrangement_le μ
      (convexOn_id (convex_Ici 0)) le_rfl

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Nonnegativity of `Φ ‖fderiv ℝ w x‖` for nondecreasing `Φ` on `[0, ∞)` with `Φ 0 = 0`. -/
private theorem ae_comp_norm_fderiv_nonneg {μ : Measure E} {Φ : ℝ → ℝ}
    (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) (w : E → ℝ) :
    0 ≤ᵐ[μ] fun x ↦ Φ ‖fderiv ℝ w x‖ :=
  ae_of_all _ fun _ ↦ by
    simpa [hΦ0] using hΦm (mem_Ici.2 le_rfl) (norm_nonneg _) (norm_nonneg _)

/-- **Integrability in the Lipschitz convex-integrand Pólya–Szegő inequality.** For any additive
Haar measure `μ`, if `h` is `K`-Lipschitz and `Φ` is convex and nondecreasing on `[0, ∞)` with
`Φ 0 = 0`, integrability of `x ↦ Φ ‖fderiv ℝ h x‖` under `μ` implies integrability of
`x ↦ Φ ‖fderiv ℝ h* x‖` under `μ`, where `h*` is the real Schwarz rearrangement of the positive part
of `h`. -/
theorem integrable_comp_norm_fderiv_toReal_schwarzRearrangement
    {μ : Measure E} [μ.IsAddHaarMeasure] (hh : LipschitzWith K h)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ h x‖) μ) :
    Integrable (fun x ↦ Φ ‖fderiv ℝ (fun z ↦
      (schwarzRearrangement μ (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) μ :=
  (lintegral_ofReal_ne_top_iff_integrable
    (hΦm.measurable_comp (measurable_fderiv ℝ _).norm fun _ ↦ norm_nonneg _).aestronglyMeasurable
    (ae_comp_norm_fderiv_nonneg hΦm hΦ0 _)).1 <|
    ne_top_of_le_ne_top hint.lintegral_lt_top.ne
      (hh.lintegral_ofReal_comp_norm_fderiv_toReal_schwarzRearrangement_le μ hΦ hΦ0.le)

/-- **Bochner-integral Pólya–Szegő inequality for Lipschitz functions.** For any additive Haar
measure `μ`, `K`-Lipschitz `h`, and convex nondecreasing `Φ` on `[0, ∞)` with `Φ 0 = 0`, if
`x ↦ Φ ‖fderiv ℝ h x‖` is `μ`-integrable and `h*` denotes the real Schwarz rearrangement of the
positive part of `h`, then `∫ x, Φ ‖fderiv ℝ h* x‖ ∂μ ≤ ∫ x, Φ ‖fderiv ℝ h x‖ ∂μ`. -/
theorem integral_comp_norm_fderiv_toReal_schwarzRearrangement_le
    {μ : Measure E} [μ.IsAddHaarMeasure] (hh : LipschitzWith K h)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ h x‖) μ) :
    ∫ x, Φ ‖fderiv ℝ (fun z ↦
        (schwarzRearrangement μ (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖ ∂μ ≤
      ∫ x, Φ ‖fderiv ℝ h x‖ ∂μ := by
  have hint' := hh.integrable_comp_norm_fderiv_toReal_schwarzRearrangement hΦ hΦm hΦ0 hint
  rw [integral_eq_lintegral_of_nonneg_ae (ae_comp_norm_fderiv_nonneg hΦm hΦ0 _)
      hint'.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_comp_norm_fderiv_nonneg hΦm hΦ0 h)
      hint.aestronglyMeasurable]
  exact ENNReal.toReal_mono hint.lintegral_lt_top.ne
    (hh.lintegral_ofReal_comp_norm_fderiv_toReal_schwarzRearrangement_le μ hΦ hΦ0.le)

end LipschitzWith
