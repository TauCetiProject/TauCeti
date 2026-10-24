/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.Analysis.BoundedVariation.DerivativeMeasure
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Variation and perimeter on the real line

On the real line the variational total variation `|Du|(Ω)` bounds the classical variation of
the Lebesgue values of `u`. If `x₀ ≤ x₁ ≤ ⋯ ≤ xₘ` are Lebesgue points of `u` with values
`v₀, …, vₘ`, in the sense that the mean oscillation `⨍_{B(xᵢ, r)} |u - vᵢ|` tends to zero, and
`[x₀, xₘ] ⊆ Ω`, then

`∑ᵢ |vᵢ₊₁ - vᵢ| ≤ |Du|(Ω)`

(`TauCeti.Real.ofReal_sum_abs_sub_le_totalVariationOn`). The test function is a combination
`∑ᵢ εᵢ (ψ (c (y - xᵢ)) - ψ (c (y - xᵢ₊₁)))` of smooth steps `ψ = Real.smoothTransition`
with signs `εᵢ = sign (vᵢ - vᵢ₊₁)`. Since the steps decrease along the points, the
combination is bounded by the telescoping sum `ψ (c (y - x₀)) - ψ (c (y - xₘ)) ≤ 1`. Its
derivative is a combination of approximate identities concentrating to the right of the
points, so its pairing with `u` converges to `∑ᵢ |vᵢ₊₁ - vᵢ|` as `c → ∞`.

For the indicator of a set `s`, almost every point is a Lebesgue point with value `0` or `1`.
Counting alternations between points of `s` and of its complement gives the sharp
one-dimensional isoperimetric inequality and its rigidity:

* a null-measurable `s ⊆ ℝ` of positive finite measure has perimeter at least `2`
  (`TauCeti.Real.two_le_perimeter`);
* if `s` has finite measure and does not agree almost everywhere with any interval, then it has
  perimeter at least `4` (`TauCeti.Real.four_le_perimeter`);
* a bounded open interval has perimeter `2` (`TauCeti.Real.perimeter_Ioo`), and a set of
  finite measure has perimeter `2` exactly when it agrees almost everywhere with a nonempty such
  interval (`TauCeti.Real.perimeter_eq_two_iff`).

These are the statements about almost every line section that slicing arguments for sets of
finite perimeter in higher dimensions apply: a section of perimeter less than `4` is an interval
up to a null set.

## Main results

* `TauCeti.Real.ofReal_sum_abs_sub_le_totalVariationOn`: the variation of `u` along Lebesgue
  points in `Ω` is at most `|Du|(Ω)`.
* `TauCeti.Real.two_le_perimeter`, `TauCeti.Real.four_le_perimeter`,
  `TauCeti.Real.perimeter_Ioo` and `TauCeti.Real.perimeter_eq_two_iff`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.10 (functions of bounded variation of one variable).
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.2 (pointwise and essential variation in one variable).
-/

public section

open Filter Set MeasureTheory Metric TopologicalSpace TestFunction LineDeriv
open scoped Topology ENNReal Distributions BoundedContinuousFunction

namespace TauCeti.Real

/-- The combination `∑ᵢ εᵢ (ψ (c (y - xᵢ)) - ψ (c (y - xᵢ₊₁)))` of smooth steps at monotone
points, with coefficients of absolute value at most one, is bounded by one. -/
private theorem abs_sum_mul_smoothTransition_sub_le {m : ℕ} {x : Fin (m + 1) → ℝ}
    (hx : Monotone x) {ε : Fin m → ℝ} (hε : ∀ i, |ε i| ≤ 1) {c : ℝ} (hc : 0 ≤ c) (y : ℝ) :
    |∑ i : Fin m, ε i * (Real.smoothTransition (c * (y - x i.castSucc)) -
      Real.smoothTransition (c * (y - x i.succ)))| ≤ 1 := by
  -- The steps decrease along the monotone points and telescope.
  have hd (i : Fin m) : 0 ≤ Real.smoothTransition (c * (y - x i.castSucc)) -
      Real.smoothTransition (c * (y - x i.succ)) :=
    sub_nonneg.2 (Real.smoothTransition.monotone (by gcongr; exact hx (Fin.castSucc_le_succ i)))
  calc _ ≤ ∑ i : Fin m, |ε i * (Real.smoothTransition (c * (y - x i.castSucc)) -
        Real.smoothTransition (c * (y - x i.succ)))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin m, (Real.smoothTransition (c * (y - x i.castSucc)) -
        Real.smoothTransition (c * (y - x i.succ))) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul, abs_of_nonneg (hd i)]
      exact mul_le_of_le_one_left (hd i) (hε i)
    _ = Real.smoothTransition (c * (y - x 0)) -
        Real.smoothTransition (c * (y - x (Fin.last m))) :=
      Fin.sum_univ_castSucc_sub_succ fun i => Real.smoothTransition (c * (y - x i))
    _ ≤ 1 := by
      linarith [Real.smoothTransition.le_one (c * (y - x 0)),
        Real.smoothTransition.nonneg (c * (y - x (Fin.last m)))]

/-- The combination of smooth steps at monotone points `x₀ ≤ ⋯ ≤ xₘ`, each rising on
`[xᵢ, xᵢ + c⁻¹]`, vanishes outside `[x₀, xₘ + c⁻¹]`. -/
private theorem sum_mul_smoothTransition_sub_eq_zero {m : ℕ} {x : Fin (m + 1) → ℝ}
    (hx : Monotone x) (ε : Fin m → ℝ) {c : ℝ} (hc : 0 < c) {y : ℝ}
    (hy : y ∉ Icc (x 0) (x (Fin.last m) + c⁻¹)) :
    ∑ i : Fin m, ε i * (Real.smoothTransition (c * (y - x i.castSucc)) -
      Real.smoothTransition (c * (y - x i.succ))) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases not_and_or.1 hy with hy | hy
  · -- Left of every point all steps are `0`.
    have h (j) : Real.smoothTransition (c * (y - x j)) = 0 :=
      Real.smoothTransition.zero_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos hc.le (by linarith [hx (Fin.zero_le j)]))
    simp [h]
  · -- Right of every transition all steps are `1`.
    have h (j) : Real.smoothTransition (c * (y - x j)) = 1 := by
      refine Real.smoothTransition.one_of_one_le ?_
      calc (1 : ℝ) = c * c⁻¹ := (mul_inv_cancel₀ hc.ne').symm
        _ ≤ c * (y - x j) := by gcongr; linarith [hx (Fin.le_last j)]
    simp [h]

/-- **The variation along Lebesgue points is bounded by the total variation.** Let
`x₀ ≤ x₁ ≤ ⋯ ≤ xₘ` be points with `[x₀, xₘ] ⊆ Ω` at which `u` has Lebesgue values `vᵢ`, that
is, the mean oscillation `⨍_{B(xᵢ, r)} |u - vᵢ|` tends to zero as `r → 0`. Then
`∑ᵢ |vᵢ₊₁ - vᵢ| ≤ |Du|(Ω)`. -/
theorem ofReal_sum_abs_sub_le_totalVariationOn {Ω : Opens ℝ} {u : ℝ → ℝ}
    (hu : LocallyIntegrableOn u Ω) {m : ℕ} {x v : Fin (m + 1) → ℝ} (hx : Monotone x)
    (hΩ : Icc (x 0) (x (Fin.last m)) ⊆ Ω)
    (hv : ∀ i, Tendsto (fun r => ⨍ y in closedBall (x i) r, ‖u y - v i‖) (𝓝[>] 0) (𝓝 0)) :
    ENNReal.ofReal (∑ i : Fin m, |v i.succ - v i.castSucc|) ≤ totalVariationOn volume Ω u := by
  set K := Icc (x 0) (x (Fin.last m))
  have hxK (i) : x i ∈ K := ⟨hx (Fin.zero_le i), hx (Fin.le_last i)⟩
  obtain ⟨δ, hδ, hδΩ⟩ := isCompact_Icc.exists_cthickening_subset_open Ω.isOpen hΩ
  have huL : IntegrableOn u (cthickening δ K) :=
    hu.integrableOn_compact_subset hδΩ isCompact_Icc.cthickening
  -- The signs `ε i` are chosen so that `ε i (v i - v (i + 1)) = |v (i + 1) - v i|`.
  set ε : Fin m → ℝ := fun i => SignType.sign (v i.castSucc - v i.succ)
  have hε (i) : |ε i| ≤ 1 := by
    simp only [ε]
    cases SignType.sign (v i.castSucc - v i.succ) <;> simp
  -- The pairings of `u` with the rescaled kernels `c ψ'(c (y - p))` converge to the values.
  set I : ℝ → ℝ → ℝ := fun c p => ∫ y, c * deriv Real.smoothTransition (c * (y - p)) * u y
  have hlim : Tendsto (fun c => ∑ i : Fin m, ε i * (I c (x i.castSucc) - I c (x i.succ))) atTop
      (𝓝 (∑ i : Fin m, |v i.succ - v i.castSucc|)) := by
    have hI (i) : Tendsto (fun c => I c (x i)) atTop (𝓝 (v i)) :=
      Real.smoothTransition.tendsto_integral_mul_deriv_mul_sub_mul ⟨cthickening δ K,
        mem_of_superset (closedBall_mem_nhds _ hδ) (closedBall_subset_cthickening (hxK i) δ),
        huL⟩ (hv i)
    refine tendsto_finsetSum _ fun i _ => ?_
    rw [abs_sub_comm, ← self_mul_sign, mul_comm]
    exact ((hI _).sub (hI _)).const_mul _
  refine le_of_tendsto (ENNReal.tendsto_ofReal hlim) ?_
  filter_upwards [eventually_gt_atTop δ⁻¹] with c hc
  have hc0 : 0 < c := lt_trans (inv_pos.2 hδ) hc
  have hball (p) (hp : p ∈ K) : closedBall p c⁻¹ ⊆ cthickening δ K :=
    (closedBall_subset_closedBall (inv_lt_of_inv_lt₀ hδ hc).le).trans
      (closedBall_subset_cthickening hp δ)
  have hkint (p) (hp : p ∈ K) :
      Integrable fun y => c * deriv Real.smoothTransition (c * (y - p)) * u y :=
    Real.smoothTransition.integrable_mul_deriv_mul_sub_mul hc0 (huL.mono_set (hball p hp))
  -- The test function: a combination of smooth steps at the points `x i`.
  set g : ℝ → ℝ := fun y => ∑ i : Fin m, ε i * (Real.smoothTransition (c * (y - x i.castSucc)) -
    Real.smoothTransition (c * (y - x i.succ)))
  have hstep (p y : ℝ) : HasDerivAt (fun y => Real.smoothTransition (c * (y - p)))
      (c * deriv Real.smoothTransition (c * (y - p))) y :=
    (((hasDerivAt_id y).sub_const p).const_mul c).smoothTransition.congr_deriv
      (by rw [id, mul_one, mul_comm])
  have hgd (y) : HasDerivAt g (∑ i : Fin m, ε i *
      (c * deriv Real.smoothTransition (c * (y - x i.castSucc)) -
        c * deriv Real.smoothTransition (c * (y - x i.succ)))) y :=
    HasDerivAt.fun_sum fun i _ => ((hstep _ y).sub (hstep _ y)).const_mul (ε i)
  have hgsmooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    have hstep (p : ℝ) : ContDiff ℝ (⊤ : ℕ∞) fun y => Real.smoothTransition (c * (y - p)) :=
      Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
    exact ContDiff.sum fun i _ => contDiff_const.mul ((hstep _).sub (hstep _))
  have hg0 (y) (hy : y ∉ Icc (x 0) (x (Fin.last m) + c⁻¹)) : g y = 0 :=
    sum_mul_smoothTransition_sub_eq_zero hx ε hc0 hy
  have hsupp : Icc (x 0) (x (Fin.last m) + c⁻¹) ⊆ Ω := by
    refine fun y hy => hδΩ ?_
    rcases le_total y (x (Fin.last m)) with h | h
    · exact self_subset_cthickening K ⟨hy.1, h⟩
    · refine hball _ (hxK (Fin.last m)) ?_
      rw [Real.closedBall_eq_Icc]
      exact ⟨by linarith [inv_pos.2 hc0], hy.2⟩
  have hts : tsupport g ⊆ Ω :=
    (isClosed_Icc.closure_subset_iff.2 (Function.support_subset_iff'.2 hg0)).trans hsupp
  let T : 𝓓(Ω, ℝ) := ⟨g, hgsmooth, HasCompactSupport.intro isCompact_Icc hg0, hts⟩
  -- Its derivative pairs with `u` to the combination of the kernel pairings.
  have hpair : ∫ y, ∂_{(1 : ℝ)} T y * u y =
      ∑ i : Fin m, ε i * (I c (x i.castSucc) - I c (x i.succ)) := by
    have hT (y) : ∂_{(1 : ℝ)} T y = ∑ i : Fin m, ε i *
        (c * deriv Real.smoothTransition (c * (y - x i.castSucc)) -
          c * deriv Real.smoothTransition (c * (y - x i.succ))) := by
      rw [lineDerivOp_apply, coe_mk, (hgd y).differentiableAt.lineDeriv_eq_fderiv,
        fderiv_apply_one_eq_deriv, (hgd y).deriv]
    simp_rw [hT, Finset.sum_mul, mul_assoc, sub_mul]
    rw [integral_finsetSum _ fun i _ => ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, integral_sub (hkint _ (hxK _)) (hkint _ (hxK _))]
    · exact ((hkint _ (hxK _)).sub (hkint _ (hxK _))).const_mul _
  have hTnorm : ‖(T : ℝ →ᵇ ℝ)‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 ((BoundedContinuousFunction.norm_le zero_le_one).2
      (abs_sum_mul_smoothTransition_sub_le hx hε hc0.le))
  calc ENNReal.ofReal (∑ i : Fin m, ε i * (I c (x i.castSucc) - I c (x i.succ)))
      ≤ ENNReal.ofReal |∫ y, ∂_{(1 : ℝ)} T y * u y| :=
        ENNReal.ofReal_le_ofReal (hpair ▸ le_abs_self _)
    _ ≤ ‖(1 : ℝ)‖ₑ * ‖(T : ℝ →ᵇ ℝ)‖ₑ * totalVariationOn volume Ω u :=
        ofReal_abs_integral_lineDeriv_mul_le_enorm_mul_enorm_mul_totalVariationOn T 1
    _ ≤ totalVariationOn volume Ω u := by
        rw [enorm_one, one_mul]
        exact mul_le_of_le_one_left zero_le hTnorm

/-- Almost every point is a Lebesgue point of the indicator of a measurable set. -/
private theorem ae_tendsto_average_indicator {s : Set ℝ} (hs : MeasurableSet s) :
    ∀ᵐ x, Tendsto (fun r => ⨍ y in closedBall x r, ‖s.indicator 1 y - s.indicator (1 : ℝ → ℝ) x‖)
      (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume
    ((locallyIntegrable_const (1 : ℝ)).indicator hs) 1] with x hx
  exact hx (fun _ => x) id tendsto_id (eventually_mem_nhdsWithin.mono fun r hr =>
    mem_closedBall_self (by simpa using (le_of_lt hr)))

/-- A set of nonzero measure contains a Lebesgue point of the indicator of a measurable set. -/
private theorem exists_mem_tendsto_average_indicator {s t : Set ℝ} (hs : MeasurableSet s)
    (ht : volume t ≠ 0) : ∃ x ∈ t, Tendsto (fun r => ⨍ y in closedBall x r,
      ‖s.indicator 1 y - s.indicator (1 : ℝ → ℝ) x‖) (𝓝[>] 0) (𝓝 0) := by
  by_contra! h
  exact ht (measure_mono_null (fun x hx => h x hx) (ae_iff.1 (ae_tendsto_average_indicator hs)))

/-- Monotone Lebesgue points of the indicator of a measurable set `s` bound its perimeter from
below by the number of alternations between `s` and its complement. -/
private theorem ofReal_sum_le_perimeter {s : Set ℝ} (hs : MeasurableSet s) {m : ℕ}
    {x : Fin (m + 1) → ℝ} (hx : Monotone x)
    (hxs : ∀ i, Tendsto (fun r => ⨍ y in closedBall (x i) r,
      ‖s.indicator 1 y - s.indicator (1 : ℝ → ℝ) (x i)‖) (𝓝[>] 0) (𝓝 0)) :
    ENNReal.ofReal (∑ i : Fin m,
      |s.indicator 1 (x i.succ) - s.indicator (1 : ℝ → ℝ) (x i.castSucc)|)
      ≤ perimeter volume ⊤ s := by
  have hu : LocallyIntegrableOn (s.indicator (1 : ℝ → ℝ)) ((⊤ : Opens ℝ) : Set ℝ) := by
    rw [Pi.one_def]
    exact ((locallyIntegrable_const 1).indicator hs).locallyIntegrableOn _
  rw [perimeter_def]
  exact ofReal_sum_abs_sub_le_totalVariationOn (v := fun i => s.indicator 1 (x i)) hu hx
    (by simp) hxs

/-- A null-measurable set agrees almost everywhere with a measurable set of the same perimeter
and measure. -/
private theorem exists_measurableSet_ae_eq {s : Set ℝ} (hs : NullMeasurableSet s) :
    ∃ t, MeasurableSet t ∧ s =ᵐ[volume] t ∧ perimeter volume ⊤ s = perimeter volume ⊤ t ∧
      volume s = volume t :=
  ⟨toMeasurable volume s, measurableSet_toMeasurable _ _, hs.toMeasurable_ae_eq.symm,
    perimeter_congr_ae (ae_restrict_of_ae hs.toMeasurable_ae_eq.symm),
    (measure_toMeasurable s).symm⟩

private theorem two_le_perimeter_of_measurableSet {s : Set ℝ} (hs : MeasurableSet s)
    (h0 : volume s ≠ 0) (hfin : volume s ≠ ∞) : 2 ≤ perimeter volume ⊤ s := by
  -- A Lebesgue point of `s`, with Lebesgue points of the complement on either side.
  obtain ⟨b, hbs, hb⟩ := exists_mem_tendsto_average_indicator hs h0
  obtain ⟨a, ⟨hab, has⟩, ha⟩ := exists_mem_tendsto_average_indicator hs (t := Iio b \ s)
    (by rw [measure_sdiff_eq_top Real.volume_Iio hfin]; exact ENNReal.top_ne_zero)
  obtain ⟨c, ⟨hbc, hcs⟩, hc⟩ := exists_mem_tendsto_average_indicator hs (t := Ioi b \ s)
    (by rw [measure_sdiff_eq_top Real.volume_Ioi hfin]; exact ENNReal.top_ne_zero)
  have h := ofReal_sum_le_perimeter hs (x := ![a, b, c])
    (Fin.monotone_iff_le_succ.2 fun i => by
      fin_cases i <;> simp [(mem_Iio.1 hab).le, (mem_Ioi.1 hbc).le])
    (fun i => by fin_cases i <;> assumption)
  simpa [Fin.sum_univ_succ, has, hbs, hcs, one_add_one_eq_two] using h

private theorem four_le_perimeter_of_measurableSet {s : Set ℝ} (hs : MeasurableSet s)
    (hfin : volume s ≠ ∞) (h : ∀ I : Set ℝ, I.OrdConnected → ¬s =ᵐ[volume] I) :
    4 ≤ perimeter volume ⊤ s := by
  set P : ℝ → Prop := fun x => Tendsto (fun r => ⨍ y in closedBall x r,
    ‖s.indicator 1 y - s.indicator (1 : ℝ → ℝ) x‖) (𝓝[>] 0) (𝓝 0)
  have hnull : volume {x | ¬P x} = 0 := ae_iff.1 (ae_tendsto_average_indicator hs)
  -- Two Lebesgue points of `s` separated by a Lebesgue point of its complement.
  obtain ⟨b, z, b', hbz, hzb', hbs, hb, hzs, hz, hb's, hb'⟩ :
      ∃ b z b', b < z ∧ z < b' ∧ b ∈ s ∧ P b ∧ z ∉ s ∧ P z ∧ b' ∈ s ∧ P b' := by
    by_contra! hcon
    -- Otherwise `s` agrees a.e. with the interval spanned by its Lebesgue points.
    set I : Set ℝ := {y | ∃ b ∈ s, P b ∧ ∃ b' ∈ s, P b' ∧ b ≤ y ∧ y ≤ b'}
    have hI : I.OrdConnected := ⟨fun y₁ ⟨b, hbs, hb, _, _, _, hby, _⟩ y₂
      ⟨_, _, _, b', hb's, hb', _, hyb'⟩ y hy =>
        ⟨b, hbs, hb, b', hb's, hb', hby.trans hy.1, hy.2.trans hyb'⟩⟩
    have h₁ : s \ I ⊆ {x | ¬P x} := fun y ⟨hys, hyI⟩ hy =>
      hyI ⟨y, hys, hy, y, hys, hy, le_rfl, le_rfl⟩
    have h₂ : I \ s ⊆ {x | ¬P x} := fun y ⟨⟨b, hbs, hb, b', hb's, hb', hby, hyb'⟩, hys⟩ hy =>
      hcon b y b' (lt_of_le_of_ne hby (ne_of_mem_of_not_mem hbs hys))
        (lt_of_le_of_ne hyb' (ne_of_mem_of_not_mem hb's hys).symm) hbs hb hys hy hb's hb'
    exact h I hI (ae_eq_set.2 ⟨measure_mono_null h₁ hnull, measure_mono_null h₂ hnull⟩)
  -- Lebesgue points of the complement on either side.
  obtain ⟨a, ⟨hab, has⟩, ha⟩ := exists_mem_tendsto_average_indicator hs (t := Iio b \ s)
    (by rw [measure_sdiff_eq_top Real.volume_Iio hfin]; exact ENNReal.top_ne_zero)
  obtain ⟨c, ⟨hb'c, hcs⟩, hc⟩ := exists_mem_tendsto_average_indicator hs (t := Ioi b' \ s)
    (by rw [measure_sdiff_eq_top Real.volume_Ioi hfin]; exact ENNReal.top_ne_zero)
  have h := ofReal_sum_le_perimeter hs (x := ![a, b, z, b', c])
    (Fin.monotone_iff_le_succ.2 fun i => by
      fin_cases i <;> simp [(mem_Iio.1 hab).le, hbz.le, hzb'.le, (mem_Ioi.1 hb'c).le])
    (fun i => by fin_cases i <;> assumption)
  have h4 : (1 + (1 + (1 + 1)) : ℝ) = 4 := by norm_num
  simpa [Fin.sum_univ_succ, has, hbs, hzs, hb's, hcs, h4] using h

/-- **The isoperimetric inequality on the line.** A null-measurable set of positive finite measure
in `ℝ` has perimeter at least two. -/
theorem two_le_perimeter {s : Set ℝ} (hs : NullMeasurableSet s) (h0 : volume s ≠ 0)
    (hfin : volume s ≠ ∞) : 2 ≤ perimeter volume ⊤ s := by
  obtain ⟨t, ht, -, hst, hvol⟩ := exists_measurableSet_ae_eq hs
  rw [hvol] at h0 hfin
  exact hst ▸ two_le_perimeter_of_measurableSet ht h0 hfin

/-- A null-measurable set of finite measure in `ℝ` that does not agree almost everywhere with any
interval has perimeter at least four. -/
theorem four_le_perimeter {s : Set ℝ} (hs : NullMeasurableSet s) (hfin : volume s ≠ ∞)
    (h : ∀ I : Set ℝ, I.OrdConnected → ¬s =ᵐ[volume] I) : 4 ≤ perimeter volume ⊤ s := by
  obtain ⟨t, ht, hst, hP, hvol⟩ := exists_measurableSet_ae_eq hs
  rw [hvol] at hfin
  exact hP ▸ four_le_perimeter_of_measurableSet ht hfin fun I hI hI' => h I hI (hst.trans hI')

/-- A bounded open interval of `ℝ` has perimeter two. -/
theorem perimeter_Ioo {a b : ℝ} (hab : a < b) : perimeter volume ⊤ (Ioo a b) = 2 := by
  refine le_antisymm ?_ (two_le_perimeter measurableSet_Ioo.nullMeasurableSet (by simp [hab])
    (by simp))
  rw [perimeter_def, totalVariationOn_le_iff]
  intro φ hφ
  have hdiff : Differentiable ℝ φ := φ.contDiff.differentiable (by simp)
  -- On the line a test vector field is a test function, whose divergence is its derivative.
  have hd (x : ℝ) : divergenceCLM φ x = deriv φ x := by
    have hφ : postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ)) φ = φ := by
      ext; simp
    have h := congrFun (congrArg DFunLike.coe (divergenceCLM_postcompCLM_toSpanSingleton φ 1)) x
    rw [hφ] at h
    rw [h, lineDerivOp_apply, (hdiff x).lineDeriv_eq_fderiv, fderiv_apply_one_eq_deriv]
  have hint : ∫ x, divergenceCLM φ x * (Ioo a b).indicator 1 x = φ b - φ a := by
    simp_rw [hd, ← indicator_mul_right, Pi.one_apply, mul_one]
    rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_deriv_eq_sub
        (fun x _ => hdiff x) ((φ.contDiff.continuous_deriv (by simp)).intervalIntegrable _ _)]
  rw [hint, ← ENNReal.ofReal_ofNat 2]
  refine ENNReal.ofReal_le_ofReal ?_
  have ha := hφ a
  have hb := hφ b
  rw [Real.norm_eq_abs, abs_le] at ha hb
  linarith

/-- **Equality in the isoperimetric inequality on the line.** A null-measurable set of finite
measure in `ℝ` has perimeter two exactly when it agrees almost everywhere with a nonempty bounded
open interval. -/
theorem perimeter_eq_two_iff {s : Set ℝ} (hs : NullMeasurableSet s) (hfin : volume s ≠ ∞) :
    perimeter volume ⊤ s = 2 ↔ ∃ a b, a < b ∧ s =ᵐ[volume] Ioo a b := by
  refine ⟨fun h2 => ?_, fun ⟨a, b, hab, hsab⟩ => ?_⟩
  · -- A null set has perimeter zero, and otherwise a perimeter below four forces an interval.
    have h0 : volume s ≠ 0 := fun h0 => by
      rw [perimeter_congr_ae (ae_restrict_of_ae (ae_eq_empty.2 h0)), perimeter_empty] at h2
      norm_num at h2
    by_contra! hne
    refine absurd (four_le_perimeter hs hfin fun I hI hsI => ?_) (by rw [h2]; norm_num)
    obtain ⟨a, b, hab, hIab⟩ := hI.exists_ae_eq_Ioo ((measure_congr hsI).symm ▸ h0)
      ((measure_congr hsI).symm ▸ hfin)
    exact hne a b hab (hsI.trans hIab)
  · rw [perimeter_congr_ae (ae_restrict_of_ae hsab), perimeter_Ioo hab]

end TauCeti.Real
