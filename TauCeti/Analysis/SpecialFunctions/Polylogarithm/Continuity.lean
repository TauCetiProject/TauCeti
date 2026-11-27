/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.Complex.UpperLogContinuity
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Holomorphy
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.RadialIntegrand
import TauCeti.MeasureTheory.Function.DeLaValleePoussin

/-!
# Continuity of integer-weight polylogarithms

In weights `n ≥ 2`, the logarithmic radial integral defining `TauCeti.Polylog.polylog n` is
uniformly integrable on `(0, 1]` over bounded complex parameter families. Combining uniform
integrability with almost-everywhere convergence of Mathlib's principal logarithm yields both
unrestricted continuity away from the pole and branch cut (including at `z = 1` when `2 ≤ n` and
hence on the entire closed unit disc) and continuity within the closed lower half-plane.

Specifically:
* Unrestricted continuity (`TauCeti.Polylog.continuousAt_polylog`): `polylog n` is continuous at
  `z` whenever `z ≠ 1 ∨ 2 ≤ n` and `n ≤ 0 ∨ z.im ≠ 0 ∨ z.re ≤ 1`. In particular, continuity at
  `z = 1` holds only for weights `2 ≤ n` (for `n ≤ 1`, `z = 1` is a pole or logarithmic
  singularity): for `n ≤ 0` and `z ≠ 1`, continuity comes from rationality
  (`analyticAt_polylog_neg_nat`); for `n ≥ 1` and `z ≠ 1` off `[1, ∞)` it comes from holomorphy on
  the slit plane (`analyticAt_polylog`); and at `z = 1` in weights `n ≥ 2` every radial argument
  `1 - t` with `t ∈ (0, 1)` lies in the open slit plane. In particular `polylog n` is continuous
  on the closed unit disc (`TauCeti.Polylog.continuousOn_polylog_closedBall`) for `2 ≤ n`.
* Closed lower half-plane continuity (`TauCeti.Polylog.continuousWithinAt_polylog_im_nonpos`):
  within `{w | w.im ≤ 0}`, `polylog n` is continuous at every `z` satisfying `z ≠ 1 ∨ 2 ≤ n`
  (again continuity at `z = 1` requires `2 ≤ n`), since `1 - t z` lies in the closed upper
  half-plane where Mathlib's principal logarithm is continuous away from `0` and `1 - t z` vanishes
  at most once on `(0, 1]`.

## Main declarations

* `TauCeti.Polylog.continuousAt_polylog`: unrestricted continuity of `polylog n` for
  `z ≠ 1 ∨ 2 ≤ n` and `n ≤ 0 ∨ z.im ≠ 0 ∨ z.re ≤ 1`.
* `TauCeti.Polylog.continuousOn_polylog_closedBall`: `polylog n` is continuous on
  `Metric.closedBall 0 1` for `2 ≤ n`.
* `TauCeti.Polylog.continuousWithinAt_polylog_im_nonpos`: continuity of `polylog n` within the
  closed lower half-plane `{w | w.im ≤ 0}` for `z ≠ 1 ∨ 2 ≤ n`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.4, p. 51.
-/

public section

open Filter MeasureTheory Metric Set
open scoped Topology

namespace TauCeti.Polylog

/-- Vitali convergence for the radial integral of `polylog (k + 2)` along a countably generated
filter when `Log (1 - t z)` converges almost everywhere on `(0, 1]`. -/
private lemma tendsto_polylog_nat_add_two_of_ae_tendsto {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (k : ℕ) {z : ι → ℂ} {z₀ : ℂ} (hz : Tendsto z l (𝓝 z₀))
    (hlog : ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 1),
      Tendsto (fun i ↦ Complex.log (1 - (t : ℂ) * z i)) l
        (𝓝 (Complex.log (1 - (t : ℂ) * z₀)))) :
    Tendsto (fun i ↦ polylog (k + 2 : ℕ) (z i)) l (𝓝 (polylog (k + 2 : ℕ) z₀)) := by
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  set w : ℕ → ℂ := z ∘ u
  have hw : Tendsto w atTop (𝓝 z₀) := hz.comp hu
  obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto w hw).exists_norm_le
  obtain ⟨C, hC, hCz⟩ := exists_setLIntegral_norm_radialIntegrand_pow_le 2 k R
  set F : ℕ → ℝ → ℂ := fun m t ↦
    ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * w m)) / t
  set f : ℝ → ℂ := fun t ↦ ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z₀)) / t
  have hF_meas : ∀ m, AEStronglyMeasurable (F m) (volume.restrict (Ioc 0 1)) :=
    fun m ↦ (intervalIntegrable_radialIntegrand k (w m)).1.aestronglyMeasurable
  have hae : ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 1), Tendsto (fun m ↦ F m t) atTop (𝓝 (f t)) := by
    filter_upwards [hlog] with t ht
    exact (tendsto_const_nhds.mul (ht.comp hu).neg).div_const (t : ℂ)
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp [Real.volume_Ioc]⟩
  have hlim : TendstoInMeasure (volume.restrict (Ioc 0 1)) F atTop f :=
    MeasureTheory.tendstoInMeasure_of_tendsto_ae hF_meas hae
  have hΦ : Tendsto (fun t : ℝ ↦ t ^ 2 / t) atTop atTop :=
    tendsto_id.congr' (by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
      exact (mul_div_cancel_right₀ t ht).symm.trans (by rw [sq]))
  have hint := tendsto_const_nhds (x := ((Nat.factorial k : ℂ)⁻¹)).mul
    (TauCeti.tendsto_integral_of_lintegral_ofReal_le (Φ := fun t : ℝ ↦ t ^ 2) hΦ
      (Eventually.of_forall hF_meas) hC
      (Eventually.of_forall fun m ↦ hCz (w m) (hR (w m) (mem_range_self m))) hlim)
  simpa only [Function.comp_def, polylog_nat_add_two, intervalIntegral.integral_of_le zero_le_one,
    F, f, w] using hint

/-- Every integer-weight polylogarithm `polylog n` is continuous at `z` whenever `z ≠ 1 ∨ 2 ≤ n`
and `n ≤ 0 ∨ z.im ≠ 0 ∨ z.re ≤ 1`. Continuity at `z = 1` requires `2 ≤ n`. -/
theorem continuousAt_polylog {n : ℤ} {z : ℂ} (hn : z ≠ 1 ∨ 2 ≤ n)
    (hz : n ≤ 0 ∨ z.im ≠ 0 ∨ z.re ≤ 1) : ContinuousAt (polylog n) z := by
  by_cases hz1 : z = 1
  · subst hz1
    have hn2 : 2 ≤ n := hn.resolve_left (not_not.mpr rfl)
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k + 2 : ℕ) := ⟨(n - 2).toNat, by omega⟩
    refine tendsto_polylog_nat_add_two_of_ae_tendsto k tendsto_id ?_
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hslit : 1 - (t : ℂ) * 1 ∈ Complex.slitPlane := by
      rw [mul_one, Complex.mem_slitPlane_iff]
      exact Or.inl (by simp; linarith [ht.2])
    exact (continuousAt_clog hslit).tendsto.comp
      ((by fun_prop : Continuous fun i : ℂ ↦ 1 - (t : ℂ) * i).tendsto 1)
  · rcases le_or_gt n 0 with hn0 | hn0
    · obtain ⟨r, rfl⟩ := Int.exists_eq_neg_ofNat hn0
      exact (analyticAt_polylog_neg_nat r hz1).continuousAt
    · exact (analyticAt_polylog n (z.one_sub_mem_slitPlane_iff.mpr
        ⟨hz.resolve_left hn0.not_ge, hz1⟩)).continuousAt

/-- For every integer weight `n ≥ 2`, `polylog n` is continuous on the closed unit disc. -/
theorem continuousOn_polylog_closedBall {n : ℤ} (hn : 2 ≤ n) :
    ContinuousOn (polylog n) (closedBall 0 1) :=
  fun z hz ↦ (continuousAt_polylog (Or.inr hn)
    (Or.inr (Or.inr
      ((Complex.re_le_norm z).trans (mem_closedBall_zero_iff.mp hz))))).continuousWithinAt

/-- Every integer-weight polylogarithm is continuous within the closed lower half-plane
`{w | w.im ≤ 0}` at every point `z` with `z ≠ 1 ∨ 2 ≤ n`. Continuity at `z = 1` requires
`2 ≤ n`. -/
theorem continuousWithinAt_polylog_im_nonpos (n : ℤ) {z : ℂ} (hz : z ≠ 1 ∨ 2 ≤ n) :
    ContinuousWithinAt (polylog n) {w : ℂ | w.im ≤ 0} z := by
  rcases le_or_gt n 0 with hn | hn
  · obtain ⟨r, rfl⟩ := Int.exists_eq_neg_ofNat hn
    exact (analyticAt_polylog_neg_nat r
      (hz.resolve_right (by omega))).continuousAt.continuousWithinAt
  · obtain ⟨_ | _ | k, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
    · exact absurd hn (lt_irrefl 0)
    · have hz1 : z ≠ 1 := hz.resolve_right (by omega)
      rw [Nat.cast_one, (funext polylog_one : polylog 1 = fun w ↦ -Complex.log (1 - w))]
      simpa [Pi.neg_def] using (continuousWithinAt_log_one_sub_ofReal_mul_im_nonpos zero_le_one
        (z := z) (by simpa [sub_ne_zero] using hz1.symm)).neg
    · refine tendsto_polylog_nat_add_two_of_ae_tendsto k nhdsWithin_le_nhds ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (ae_one_sub_ofReal_mul_ne_zero z)] with t ht htz
      exact (continuousWithinAt_log_one_sub_ofReal_mul_im_nonpos ht.1.le htz).tendsto

end TauCeti.Polylog
