/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.Complex.UpperLogContinuity
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Holomorphy
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.RadialIntegrand

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
  `1 - t` with `t ∈ (0, 1)` lies in the open slit plane.
* Closed lower half-plane continuity (`TauCeti.Polylog.continuousWithinAt_polylog_im_nonpos`):
  within `{w | w.im ≤ 0}`, `polylog n` is continuous at every `z` satisfying `z ≠ 1 ∨ 2 ≤ n`
  (again continuity at `z = 1` requires `2 ≤ n`), since `1 - t z` lies in the closed upper
  half-plane where Mathlib's principal logarithm is continuous away from `0` and `1 - t z` vanishes
  at most once on `(0, 1]`.

## Main declarations

* `TauCeti.Polylog.continuousAt_polylog`: unrestricted continuity of `polylog n` for
  `z ≠ 1 ∨ 2 ≤ n` and `n ≤ 0 ∨ z.im ≠ 0 ∨ z.re ≤ 1`.
* `TauCeti.Polylog.continuousWithinAt_polylog_im_nonpos`: continuity of `polylog n` within the
  closed lower half-plane `{w | w.im ≤ 0}` for `z ≠ 1 ∨ 2 ≤ n`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.4, p. 51.
-/

public section

open Filter MeasureTheory Set
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
  have hui :=
    (uniformIntegrable_radialIntegrand k (Metric.isBounded_range_of_tendsto w hw)).unifIntegrable
  set F : ℕ → ℝ → ℂ := fun m t ↦
    ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * w m)) / t
  set f : ℝ → ℂ := fun t ↦ ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z₀)) / t
  have hF_int : ∀ m, Integrable (F m) (volume.restrict (Ioc 0 1)) :=
    fun m ↦ (intervalIntegrable_radialIntegrand k (w m)).1
  have hf_mem : MemLp f 1 (volume.restrict (Ioc 0 1)) :=
    memLp_one_iff_integrable.mpr (intervalIntegrable_radialIntegrand k z₀).1
  have hae : ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 1), Tendsto (fun m ↦ F m t) atTop (𝓝 (f t)) := by
    filter_upwards [hlog] with t ht
    exact (tendsto_const_nhds.mul (ht.comp hu).neg).div_const (t : ℂ)
  have hL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
    (fun m ↦ (hF_int m).aestronglyMeasurable) hf_mem hui hae
  have hint := tendsto_const_nhds (x := ((Nat.factorial k : ℂ)⁻¹)).mul
    (tendsto_integral_of_L1' f (Eventually.of_forall hF_int) hL1)
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
      have hne : ∀ᵐ t : ℝ ∂volume, 1 - (t : ℂ) * z ≠ 0 := by
        rw [ae_iff]
        simpa [not_not] using
          (Complex.subsingleton_one_sub_ofReal_mul_eq_zero z).measure_zero volume
      filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hne] with t ht htz
      exact (continuousWithinAt_log_one_sub_ofReal_mul_im_nonpos ht.1.le htz).tendsto

end TauCeti.Polylog
