/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ResolventTransform.Nevanlinna
public import TauCeti.MeasureTheory.Measure.ResolventTransform.WeakConvergence
import TauCeti.Analysis.Convex.SchauderFixedPoint
import TauCeti.MeasureTheory.Measure.ResolventTransform.Expansion
import TauCeti.MeasureTheory.Measure.ResolventTransform.Inversion
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Pastur equation and the Pastur measure semigroup

For a finite Borel measure `ν` on `ℝ`, a variance parameter `t : ℝ≥0`, and a complex number `z` in
the upper half-plane `{z : ℂ | 0 < z.im}`, the **Pastur self-consistent equation**

`w = m_ν(z + t w) = ∫ (x - z - t w)⁻¹ dν(x)`

has a unique solution `w` with `0 ≤ w.im`
(`MeasureTheory.existsUnique_eq_resolventTransform_add_mul`).
Existence follows from Schauder's fixed-point theorem (`TauCeti.schauderFixedPoint_compactConvex`)
on the compact convex half-disc `{w : ℂ | 0 ≤ w.im} ∩ closedBall 0 ((Im z)⁻¹ ν(ℝ))`. Uniqueness
comes from the imaginary-part identity `t ∫ ‖(x - ζ)⁻¹‖² dν(x) = 1 - Im z / Im ζ < 1` at
`ζ = z + t w`, which makes the difference equation strictly contractive by the arithmetic-geometric
mean inequality without assuming `ν` has unit mass.

That same bound implies `‖t m_ν'(ζ)‖ < 1`, so `1 - t m_ν'(ζ) ≠ 0` and the fixed point is complex
differentiable on `{z : ℂ | 0 < z.im}` with derivative `m_ν'(ζ) / (1 - t m_ν'(ζ))`. Along the
positive imaginary axis it satisfies `iy w(iy) → -ν(ℝ)` as `y → ∞`. By the Pick–Nevanlinna
characterization (`MeasureTheory.exists_isFiniteMeasure_resolventTransform_eq_of_tendsto`), there is
a unique finite measure `ν.pastur t` on `ℝ` of total mass `ν(ℝ)` whose resolvent transform solves
the Pastur equation off the real axis. When `ν` is a probability measure, `ν.pastur t` is a
probability measure: it is the additive free convolution `ν ⊞ SC_t` with the centred semicircle law
of variance `t`, defined for arbitrary (possibly heavy-tailed) laws `ν`.

The family `(ν.pastur t)_{t ≥ 0}` forms a semigroup (`(ν.pastur s).pastur t = ν.pastur (s + t)`),
covaries with real affine maps, and depends jointly continuously in the weak topology on
`(ν, t) : ProbabilityMeasure ℝ × ℝ≥0` (`MeasureTheory.ProbabilityMeasure.continuous_pastur`).

We use Mathlib's `MeasureTheory.resolventTransform`, with sign `(x - z)⁻¹`, not `(z - x)⁻¹`.

## Main definitions

* `MeasureTheory.Measure.pastur`: the Pastur measure `ν.pastur t` of a real measure `ν` at
  parameter `t : ℝ≥0` (zero when `ν` is not finite).
* `MeasureTheory.ProbabilityMeasure.pastur`: the bundled Pastur evolution on
  `ProbabilityMeasure ℝ`.

## Main results

* `MeasureTheory.existsUnique_eq_resolventTransform_add_mul`: existence and uniqueness in the
  closed upper half-plane for the Pastur equation `w = m_ν(z + t w)` at `0 < z.im`.
* `MeasureTheory.eq_resolventTransform_pastur_iff`: `m_{ν.pastur t}(z)` is the unique solution with
  `0 ≤ w.im` for `0 < z.im`.
* `MeasureTheory.resolventTransform_pastur_eq`: `m_{ν.pastur t}(z) = m_ν(z + t m_{ν.pastur t}(z))`
  for all `z.im ≠ 0`.
* `MeasureTheory.norm_mul_deriv_resolventTransform_pastur_lt_one` and
  `MeasureTheory.hasDerivAt_resolventTransform_pastur`: strict contraction of `t m_ν'(ζ)` and the
  implicit-derivative formula off the real axis.
* `MeasureTheory.Measure.pastur_zero`, `MeasureTheory.Measure.pastur_pastur`,
  `MeasureTheory.Measure.map_affine_pastur`: identity at `0`, semigroup law, and affine covariance.
* `MeasureTheory.ProbabilityMeasure.continuous_pastur`: joint weak continuity in `(ν, t)`.

## References

* L. A. Pastur, *On the spectrum of random matrices*, Teoret. Mat. Fiz. 10 (1972), 102–112.
* P. Biane, *On the free convolution with a semi-circular distribution*, Indiana Univ. Math. J.
  46 (1997), 705–718, Lemma 2.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §4.3.2 and Theorem 5.4.5.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped ComplexConjugate NNReal Topology ENNReal

namespace MeasureTheory

section PasturFixedPoint

variable {ν : Measure ℝ} [IsFiniteMeasure ν]

/-- **Biane's imaginary-part identity.** If `w = m_ν(z + t w)` with `z.im ≠ 0` and
`0 ≤ z.im * w.im`, then at `ζ = z + t w` we have `t ∫ ‖(x - ζ)⁻¹‖² dν(x) = 1 - z.im / ζ.im < 1`. -/
private lemma mul_integral_norm_resolvent_sq_eq (t : ℝ≥0) {z w : ℂ} (hz : z.im ≠ 0)
    (hzw : 0 ≤ z.im * w.im) (hw : w = resolventTransform ν (z + t * w)) :
    (t : ℝ) * ∫ x, ‖resolvent (z + t * w) x‖ ^ 2 ∂ν = 1 - z.im / (z + t * w).im ∧
      0 < z.im / (z + t * w).im := by
  set ζ := z + t * w
  have hζim : ζ.im = z.im + (t : ℝ) * w.im := by simp [ζ]
  have hprod : 0 < z.im * ζ.im := by
    rw [hζim]
    have hsq : 0 < z.im * z.im := mul_self_pos.2 hz
    nlinarith [t.coe_nonneg, mul_nonneg t.coe_nonneg hzw]
  have hζ0 : ζ.im ≠ 0 := fun h ↦ by simp [h] at hprod
  have hquot : 0 < z.im / ζ.im := div_pos_iff.2 <|
    (mul_pos_iff.1 hprod).imp (fun h ↦ ⟨h.1, h.2⟩) (fun h ↦ ⟨h.1, h.2⟩)
  have hint_im : w.im = ζ.im * ∫ x, ‖resolvent ζ x‖ ^ 2 ∂ν := by
    rw [congrArg im hw, im_resolventTransform, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    dsimp only
    rw [resolvent, Ring.inverse_eq_inv', Complex.coe_algebraMap, norm_inv, inv_pow,
      ← normSq_eq_norm_sq, normSq_apply]
    simp [sq, div_eq_mul_inv]
  refine ⟨?_, hquot⟩
  apply mul_right_cancel₀ hζ0
  calc ((t : ℝ) * ∫ x, ‖resolvent ζ x‖ ^ 2 ∂ν) * ζ.im
      = (t : ℝ) * (ζ.im * ∫ x, ‖resolvent ζ x‖ ^ 2 ∂ν) := by ring
    _ = (t : ℝ) * w.im := by rw [← hint_im]
    _ = ζ.im - z.im := by linarith [hζim]
    _ = (1 - z.im / ζ.im) * ζ.im := by field_simp [hζ0]

/-- Existence of a solution in the closed upper half-plane via Schauder's fixed-point theorem. -/
private lemma exists_eq_resolventTransform_add_mul (t : ℝ≥0) {z : ℂ} (hz : 0 < z.im) :
    ∃ w : ℂ, 0 ≤ w.im ∧ w = resolventTransform ν (z + t * w) := by
  let R : ℝ := (z.im)⁻¹ * ν.real univ
  have hR0 : 0 ≤ R := by positivity
  let K : Set ℂ := {w : ℂ | 0 ≤ w.im} ∩ closedBall 0 R
  have hKcpt : IsCompact K :=
    (isCompact_closedBall 0 R).inter_left (isClosed_le continuous_const continuous_im)
  have hKconv : Convex ℝ K := by
    refine Convex.inter (fun u hu v hv a b ha hb _ ↦ ?_) (convex_closedBall 0 R)
    simp only [mem_ofPred_eq, add_im, real_smul, mul_im, ofReal_re, ofReal_im, zero_mul,
      add_zero] at hu hv ⊢
    positivity
  have hKne : K.Nonempty := ⟨0, by simp, mem_closedBall_self hR0⟩
  have hmaps : MapsTo (fun w : ℂ ↦ resolventTransform ν (z + t * w)) K K := by
    rintro w ⟨hwim, -⟩
    rw [mem_ofPred_eq] at hwim
    have hζ : z.im ≤ (z + t * w).im := by
      simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
      nlinarith [t.coe_nonneg]
    have hζpos : 0 < (z + t * w).im := hz.trans_le hζ
    refine ⟨?_, ?_⟩
    · rw [mem_ofPred_eq, im_resolventTransform]
      exact integral_nonneg fun x ↦ div_nonneg hζpos.le (by positivity)
    · rw [mem_closedBall_zero_iff]
      calc ‖resolventTransform ν (z + t * w)‖
          ≤ |(z + t * w).im|⁻¹ * ν.real univ := norm_resolventTransform_le hζpos.ne'
        _ ≤ (z.im)⁻¹ * ν.real univ := by rw [abs_of_pos hζpos]; gcongr
  have hcont : ContinuousOn (fun w : ℂ ↦ resolventTransform ν (z + t * w)) K := by
    intro w hw
    have hwim : 0 ≤ w.im := hw.1
    have hζpos : 0 < (z + t * w).im := by
      simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
      nlinarith [t.coe_nonneg]
    have hsupp : z + t * w ∉ algebraMap ℝ ℂ '' ν.support := by
      rintro ⟨x, -, hx⟩
      exact hζpos.ne' (by simpa using congrArg im hx.symm)
    exact (ContinuousAt.comp (g := resolventTransform ν) (f := fun u : ℂ ↦ z + t * u)
      (hasDerivAt_resolventTransform (z + t * w) hsupp).continuousAt
      (by fun_prop : Continuous fun u : ℂ ↦ z + t * u).continuousAt).continuousWithinAt
  obtain ⟨⟨w₀, hw₀K⟩, hfix⟩ := TauCeti.schauderFixedPoint_compactConvex hKcpt hKconv hKne
    ⟨hmaps.restrict _ K K, hcont.mapsToRestrict hmaps⟩
  exact ⟨w₀, hw₀K.1, (congrArg Subtype.val hfix).symm⟩

private lemma integrable_norm_resolvent_sq {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    Integrable (fun x : ℝ ↦ ‖resolvent ζ x‖ ^ 2) ν :=
  Integrable.of_bound (by fun_prop) (|ζ.im|⁻¹ ^ 2) (ae_of_all _ fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (Complex.norm_resolvent_real_le ζ x hζ) 2)

/-- Uniqueness in the closed upper half-plane via Biane's contraction estimate and AM-GM. -/
private lemma eq_of_eq_resolventTransform_add_mul (t : ℝ≥0) {z w₁ w₀ : ℂ} (hz : 0 < z.im)
    (hw₁im : 0 ≤ w₁.im) (hw₁eq : w₁ = resolventTransform ν (z + t * w₁))
    (hw₀im : 0 ≤ w₀.im) (hw₀eq : w₀ = resolventTransform ν (z + t * w₀)) :
    w₁ = w₀ := by
  set ζ₁ := z + t * w₁
  set ζ₀ := z + t * w₀
  have hζ₁pos : 0 < ζ₁.im := by
    simp only [ζ₁, add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    nlinarith [t.coe_nonneg]
  have hζ₀pos : 0 < ζ₀.im := by
    simp only [ζ₀, add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    nlinarith [t.coe_nonneg]
  obtain ⟨hb₁, hq₁⟩ := mul_integral_norm_resolvent_sq_eq (ν := ν) t hz.ne'
    (mul_nonneg hz.le hw₁im) hw₁eq
  obtain ⟨hb₀, hq₀⟩ := mul_integral_norm_resolvent_sq_eq (ν := ν) t hz.ne'
    (mul_nonneg hz.le hw₀im) hw₀eq
  have hint_sq (ζ : ℂ) (hζ : ζ.im ≠ 0) := integrable_norm_resolvent_sq (ν := ν) hζ
  have hsub : w₁ - w₀ = ((t : ℂ) * (w₁ - w₀)) * ∫ x, resolvent ζ₁ x * resolvent ζ₀ x ∂ν := by
    have hdiff : ζ₁ - ζ₀ = (t : ℂ) * (w₁ - w₀) := by simp [ζ₁, ζ₀]; ring
    nth_rw 1 [hw₁eq, hw₀eq]
    rw [resolventTransform_apply, resolventTransform_apply,
      ← integral_sub (integrable_resolvent_of_im_ne_zero hζ₁pos.ne')
        (integrable_resolvent_of_im_ne_zero hζ₀pos.ne'), ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    dsimp only; rw [spectrum.resolvent_sub_resolvent (Complex.mem_resolventSet_real hζ₁pos.ne' x)
      (Complex.mem_resolventSet_real hζ₀pos.ne' x), hdiff]; ring
  let r : ℝ := (t : ℝ) * ∫ x, ‖resolvent ζ₁ x * resolvent ζ₀ x‖ ∂ν
  have hr_lt : r < 1 := by
    have hsum_int := ((hint_sq ζ₁ hζ₁pos.ne').add (hint_sq ζ₀ hζ₀pos.ne')).div_const 2
    have hprod_int : Integrable (fun x : ℝ ↦ ‖resolvent ζ₁ x * resolvent ζ₀ x‖) ν :=
      hsum_int.mono' (by fun_prop) (ae_of_all _ fun x ↦ by
        dsimp only [Pi.add_apply]; rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul]
        nlinarith [sq_nonneg (‖resolvent ζ₁ x‖ - ‖resolvent ζ₀ x‖)])
    have hle : ∫ x, ‖resolvent ζ₁ x * resolvent ζ₀ x‖ ∂ν ≤
        (∫ x, ‖resolvent ζ₁ x‖ ^ 2 ∂ν + ∫ x, ‖resolvent ζ₀ x‖ ^ 2 ∂ν) / 2 := by
      rw [← integral_add (hint_sq ζ₁ hζ₁pos.ne') (hint_sq ζ₀ hζ₀pos.ne'), ← integral_div]
      refine integral_mono hprod_int hsum_int fun x ↦ ?_
      dsimp only [Pi.add_apply]; rw [norm_mul]
      nlinarith [sq_nonneg (‖resolvent ζ₁ x‖ - ‖resolvent ζ₀ x‖)]
    have hr_le : r ≤ ((1 - z.im / ζ₁.im) + (1 - z.im / ζ₀.im)) / 2 := by
      calc r ≤ (t : ℝ) * ((∫ x, ‖resolvent ζ₁ x‖ ^ 2 ∂ν + ∫ x, ‖resolvent ζ₀ x‖ ^ 2 ∂ν) / 2) :=
            mul_le_mul_of_nonneg_left hle t.coe_nonneg
        _ = ((1 - z.im / ζ₁.im) + (1 - z.im / ζ₀.im)) / 2 := by
            dsimp only [ζ₁, ζ₀] at *; rw [← hb₁, ← hb₀]; ring
    linarith
  have hnorm_le : ‖w₁ - w₀‖ ≤ ‖w₁ - w₀‖ * r := by
    calc ‖w₁ - w₀‖ = ‖((t : ℂ) * (w₁ - w₀)) * ∫ x, resolvent ζ₁ x * resolvent ζ₀ x ∂ν‖ :=
          congrArg norm hsub
      _ = ‖w₁ - w₀‖ * ((t : ℝ) * ‖∫ x, resolvent ζ₁ x * resolvent ζ₀ x ∂ν‖) := by
          rw [norm_mul, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg t.coe_nonneg]; ring
      _ ≤ ‖w₁ - w₀‖ * r := by dsimp only [r]; gcongr; exact norm_integral_le_integral_norm _
  exact sub_eq_zero.1 (norm_eq_zero.1 (by nlinarith [norm_nonneg (w₁ - w₀)]))

/-- **Existence and uniqueness for the Pastur equation.** For every finite Borel measure `ν` on `ℝ`,
`t : ℝ≥0`, and `z : ℂ` with `0 < z.im`, there is a unique `w : ℂ` with `0 ≤ w.im` solving
`w = resolventTransform ν (z + t * w)`. -/
theorem existsUnique_eq_resolventTransform_add_mul (t : ℝ≥0) {z : ℂ} (hz : 0 < z.im) :
    ∃! w : ℂ, 0 ≤ w.im ∧ w = resolventTransform ν (z + t * w) := by
  obtain ⟨w₀, hw₀im, hw₀eq⟩ := exists_eq_resolventTransform_add_mul (ν := ν) t hz
  exact ⟨w₀, ⟨hw₀im, hw₀eq⟩,
    fun w₁ ⟨hw₁im, hw₁eq⟩ ↦ eq_of_eq_resolventTransform_add_mul t hz hw₁im hw₁eq hw₀im hw₀eq⟩

/-- Auxiliary upper-half-plane Pastur fixed point used to construct `Measure.pastur`. -/
private def pasturAux (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ≥0) (z : ℂ) : ℂ :=
  if hz : 0 < z.im then (existsUnique_eq_resolventTransform_add_mul (ν := ν) t hz).choose else 0

private lemma pasturAux_spec (t : ℝ≥0) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (pasturAux ν t z).im ∧
      pasturAux ν t z = resolventTransform ν (z + t * pasturAux ν t z) := by
  simpa only [pasturAux, dite_eq_left hz] using
    (existsUnique_eq_resolventTransform_add_mul (ν := ν) t hz).choose_spec.1

private lemma eq_pasturAux_iff (t : ℝ≥0) {z w : ℂ} (hz : 0 < z.im) :
    w = pasturAux ν t z ↔ 0 ≤ w.im ∧ w = resolventTransform ν (z + t * w) := by
  refine ⟨fun h ↦ h ▸ pasturAux_spec t hz, fun hw ↦ ?_⟩
  simpa only [pasturAux, dite_eq_left hz] using
    (existsUnique_eq_resolventTransform_add_mul (ν := ν) t hz).choose_spec.2 w hw

private lemma norm_pasturAux_le (t : ℝ≥0) {z : ℂ} (hz : 0 < z.im) :
    ‖pasturAux ν t z‖ ≤ (z.im)⁻¹ * ν.real univ := by
  obtain ⟨hwim, hweq⟩ := pasturAux_spec (ν := ν) t hz
  have hζ : z.im ≤ (z + t * pasturAux ν t z).im := by
    simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    nlinarith [t.coe_nonneg]
  have hζpos : 0 < (z + t * pasturAux ν t z).im := hz.trans_le hζ
  rw [hweq]
  calc ‖resolventTransform ν (z + t * pasturAux ν t z)‖
      ≤ |(z + t * pasturAux ν t z).im|⁻¹ * ν.real univ := norm_resolventTransform_le hζpos.ne'
    _ ≤ (z.im)⁻¹ * ν.real univ := by
        rw [abs_of_pos hζpos]
        gcongr

private lemma continuousAt_pasturAux (t : ℝ≥0) {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt (pasturAux ν t) z := by
  rw [ContinuousAt, tendsto_iff_ultrafilter]
  intro U hU
  let R : ℝ := 2 * (z.im)⁻¹ * ν.real univ
  let K : Set ℂ := {w : ℂ | 0 ≤ w.im} ∩ closedBall 0 R
  have hKcpt : IsCompact K :=
    (isCompact_closedBall 0 R).inter_left (isClosed_le continuous_const continuous_im)
  have hmem : K ∈ U.map (pasturAux ν t) := by
    rw [Ultrafilter.mem_map]
    have hhalf : {u : ℂ | z.im / 2 < u.im} ∈ U :=
      hU ((isOpen_lt continuous_const continuous_im).mem_nhds (by rw [mem_ofPred_eq]; linarith))
    filter_upwards [hhalf] with u hu
    have hupos : 0 < u.im := by linarith
    refine ⟨(pasturAux_spec t hupos).1, mem_closedBall_zero_iff.2 ?_⟩
    calc ‖pasturAux ν t u‖ ≤ (u.im)⁻¹ * ν.real univ := norm_pasturAux_le t hupos
      _ ≤ (z.im / 2)⁻¹ * ν.real univ := by
          gcongr
      _ = R := by dsimp only [R]; ring
  obtain ⟨w, hwK, hwlim⟩ := hKcpt.ultrafilter_le_nhds (U.map (pasturAux ν t))
    (le_principal_iff.2 hmem)
  have hwim : 0 ≤ w.im := hwK.1
  have hζpos : 0 < (z + t * w).im := by
    simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    nlinarith [t.coe_nonneg]
  have hsupp : z + t * w ∉ algebraMap ℝ ℂ '' ν.support := by
    rintro ⟨x, -, hx⟩
    exact hζpos.ne' (by simpa using congrArg im hx.symm)
  have hζlim : Tendsto (fun u : ℂ ↦ u + t * pasturAux ν t u) U (𝓝 (z + t * w)) :=
    (tendsto_id.mono_left hU).add (tendsto_const_nhds.mul hwlim)
  have hrhs : Tendsto (fun u : ℂ ↦ resolventTransform ν (u + t * pasturAux ν t u)) U
      (𝓝 (resolventTransform ν (z + t * w))) :=
    (hasDerivAt_resolventTransform _ hsupp).continuousAt.tendsto.comp hζlim
  have hev : (fun u : ℂ ↦ pasturAux ν t u) =ᶠ[U]
      fun u : ℂ ↦ resolventTransform ν (u + t * pasturAux ν t u) := by
    filter_upwards [hU ((isOpen_lt continuous_const continuous_im).mem_nhds hz)] with u hu
    exact (pasturAux_spec t hu).2
  have hweq : w = pasturAux ν t z :=
    (eq_pasturAux_iff t hz).2 ⟨hwim, tendsto_nhds_unique hwlim (hrhs.congr' hev.symm)⟩
  exact hweq ▸ hwlim

/-- Implicit differentiation helper: if `f` is continuous at `z`, satisfies
`f w = m_ν(w + t * f w)` near `z`, and `1 - t * m_ν'(z + t * f z) ≠ 0`, then `f` has complex
derivative `m_ν'(ζ) / (1 - t * m_ν'(ζ))` at `z`. -/
private lemma hasDerivAt_of_pastur_eq {f : ℂ → ℂ} (t : ℝ≥0) {z : ℂ}
    (hcont : ContinuousAt f z) (heq : ∀ᶠ w in 𝓝 z, f w = resolventTransform ν (w + t * f w))
    (hζ0 : (z + t * f z).im ≠ 0)
    (hjac : 1 - (t : ℂ) * deriv (resolventTransform ν) (z + t * f z) ≠ 0) :
    HasDerivAt f (deriv (resolventTransform ν) (z + t * f z) /
      (1 - (t : ℂ) * deriv (resolventTransform ν) (z + t * f z))) z := by
  let ζ : ℂ → ℂ := fun w ↦ w + t * f w
  let d : ℂ := deriv (resolventTransform ν) (ζ z)
  have hsupp : ζ z ∉ algebraMap ℝ ℂ '' ν.support := by
    rintro ⟨x, -, hx⟩
    exact hζ0 (by simpa [ζ] using congrArg im hx.symm)
  have hm_deriv : HasDerivAt (resolventTransform ν) d (ζ z) := by
    have h := hasDerivAt_resolventTransform (ζ z) hsupp
    dsimp only [d]
    rw [h.deriv]
    exact h
  have hζ_cont : ContinuousAt ζ z := continuousAt_id.add (continuousAt_const.mul hcont)
  have hfz : f z = resolventTransform ν (ζ z) := heq.self_of_nhds
  have hζ_ne : ∀ᶠ w in 𝓝[≠] z, ζ w ≠ ζ z := by
    filter_upwards [nhdsWithin_le_nhds heq, self_mem_nhdsWithin] with w hw hwz hζeq
    have hw' : f w = resolventTransform ν (ζ w) := hw
    have hfw : f w = f z := by rw [hw', hζeq, ← hfz]
    apply hwz
    have : w + t * f z = z + t * f z := by simpa [ζ, hfw] using hζeq
    exact add_right_cancel this
  have hζ_tendsto : Tendsto ζ (𝓝[≠] z) (𝓝[≠] (ζ z)) :=
    tendsto_nhdsWithin_iff.2 ⟨hζ_cont.mono_left nhdsWithin_le_nhds, hζ_ne⟩
  have hslope_m : Tendsto (fun w ↦ slope (resolventTransform ν) (ζ z) (ζ w)) (𝓝[≠] z) (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope.1 hm_deriv).comp hζ_tendsto
  have hden_lim : Tendsto (fun w ↦ 1 - (t : ℂ) * slope (resolventTransform ν) (ζ z) (ζ w))
      (𝓝[≠] z) (𝓝 (1 - (t : ℂ) * d)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hslope_m)
  rw [hasDerivAt_iff_tendsto_slope]
  refine (hslope_m.div hden_lim hjac).congr' ?_
  filter_upwards [nhdsWithin_le_nhds heq, self_mem_nhdsWithin, hζ_ne,
    hden_lim.eventually_ne hjac] with w hw hwz hζne hden
  have hw' : f w = resolventTransform ν (ζ w) := hw
  let q : ℂ := slope (resolventTransform ν) (ζ z) (ζ w)
  have hq_mul : q * (ζ w - ζ z) = f w - f z := by
    dsimp only [q]
    rw [slope_def_field, ← hw', ← hfz, div_mul_cancel₀ _ (sub_ne_zero.2 hζne)]
  have hlin : (1 - (t : ℂ) * q) * (f w - f z) = q * (w - z) := by
    have hζdiff : ζ w - ζ z = (w - z) + (t : ℂ) * (f w - f z) := by simp [ζ]; ring
    linear_combination -hq_mul + q * hζdiff
  have hwz' : w - z ≠ 0 := sub_ne_zero.2 hwz
  rw [Pi.div_apply, slope_def_field f z w, div_eq_div_iff hden hwz']
  linear_combination -hlin

private lemma differentiableOn_pasturAux (t : ℝ≥0) :
    DifferentiableOn ℂ (pasturAux ν t) {z : ℂ | 0 < z.im} := by
  intro z (hz : 0 < z.im)
  obtain ⟨hwim, hweq⟩ := pasturAux_spec (ν := ν) t hz
  set ζ := z + t * pasturAux ν t z
  have hζpos : 0 < ζ.im := by
    simp only [ζ, add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    nlinarith [t.coe_nonneg]
  obtain ⟨hb, hq⟩ := mul_integral_norm_resolvent_sq_eq (ν := ν) t hz.ne'
    (mul_nonneg hz.le hwim) hweq
  have hsupp : ζ ∉ algebraMap ℝ ℂ '' ν.support := by
    rintro ⟨x, -, hx⟩
    exact hζpos.ne' (by simpa using congrArg im hx.symm)
  have hnorm_lt : ‖(t : ℂ) * deriv (resolventTransform ν) ζ‖ < 1 := by
    rw [(hasDerivAt_resolventTransform ζ hsupp).deriv, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg t.coe_nonneg]
    calc (t : ℝ) * ‖∫ x, resolvent ζ x ^ 2 ∂ν‖
        ≤ (t : ℝ) * ∫ x, ‖resolvent ζ x ^ 2‖ ∂ν :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) t.coe_nonneg
      _ = (t : ℝ) * ∫ x, ‖resolvent ζ x‖ ^ 2 ∂ν := by simp_rw [norm_pow]
      _ = 1 - z.im / ζ.im := hb
      _ < 1 := by linarith
  have hjac : 1 - (t : ℂ) * deriv (resolventTransform ν) ζ ≠ 0 := by
    intro h
    have : ‖(t : ℂ) * deriv (resolventTransform ν) ζ‖ = 1 := by
      rw [← sub_eq_zero.1 h, norm_one]
    linarith
  have heq : ∀ᶠ w in 𝓝 z, pasturAux ν t w = resolventTransform ν (w + t * pasturAux ν t w) := by
    filter_upwards [(isOpen_lt continuous_const continuous_im).mem_nhds hz] with w hw
    exact (pasturAux_spec t hw).2
  exact (hasDerivAt_of_pastur_eq t (continuousAt_pasturAux t hz) heq hζpos.ne'
    hjac).differentiableAt.differentiableWithinAt

private lemma tendsto_mul_I_mul_pasturAux (t : ℝ≥0) :
    Tendsto (fun y : ℝ ↦ (y : ℂ) * I * pasturAux ν t (y * I)) atTop
      (𝓝 (-(ν.real univ : ℂ))) := by
  have hdiff : Tendsto (fun y : ℝ ↦
      (y : ℂ) * I * (pasturAux ν t (y * I) - resolventTransform ν (y * I))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    let C : ℝ := (t : ℝ) * ν.real univ ^ 2
    have hbound_lim : Tendsto (fun y : ℝ ↦ C * (y ^ 2)⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := C)).mul
        (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (Nat.succ_ne_zero 1)))
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hbound_lim
    filter_upwards [eventually_gt_atTop 0] with y hy
    have hz : 0 < (y * I : ℂ).im := by simpa using hy
    obtain ⟨hwim, hweq⟩ := pasturAux_spec (ν := ν) t hz
    set w := pasturAux ν t (y * I)
    have hζ : y ≤ (y * I + t * w).im := by
      simp only [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, mul_zero,
        add_zero, zero_mul]
      nlinarith [t.coe_nonneg]
    have hζpos : 0 < (y * I + t * w).im := hy.trans_le hζ
    have hsub := norm_resolventTransform_sub_le (μ := ν) hζpos.ne' hz.ne'
    have hnorm_w : ‖w‖ ≤ y⁻¹ * ν.real univ := by simpa using norm_pasturAux_le (ν := ν) t hz
    rw [hweq, norm_mul, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hy, norm_I, mul_one]
    calc y * ‖resolventTransform ν (y * I + t * w) - resolventTransform ν (y * I)‖
        ≤ y * (‖(y * I + t * w) - y * I‖ / (|(y * I + t * w).im| * |(y * I : ℂ).im|) *
            ν.real univ) := mul_le_mul_of_nonneg_left hsub hy.le
      _ ≤ y * (((t : ℝ) * (y⁻¹ * ν.real univ)) / (y * y) * ν.real univ) := by
          have him1 : |(y * I + t * w).im| = (y * I + t * w).im := abs_of_pos hζpos
          have him2 : |(y * I : ℂ).im| = y := by simp [abs_of_pos hy]
          have hnum : ‖(y * I + t * w) - y * I‖ ≤ (t : ℝ) * (y⁻¹ * ν.real univ) := by
            rw [add_sub_cancel_left, norm_mul, norm_real, Real.norm_eq_abs,
              abs_of_nonneg t.coe_nonneg]
            exact mul_le_mul_of_nonneg_left hnorm_w t.coe_nonneg
          rw [him1, him2]
          gcongr
      _ = C * (y ^ 2)⁻¹ := by
          dsimp only [C]
          field_simp [hy.ne']
  convert hdiff.add (tendsto_mul_I_mul_resolventTransform (μ := ν)) using 1
  · ext y; ring
  · simp

private lemma exists_pasturMeasure (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ≥0) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ.real univ = ν.real univ ∧
      ∀ z : ℂ, 0 < z.im → pasturAux ν t z = resolventTransform μ z :=
  exists_isFiniteMeasure_resolventTransform_eq_of_tendsto
    (differentiableOn_pasturAux t) (fun _ hz ↦ (pasturAux_spec t hz).1)
    (tendsto_mul_I_mul_pasturAux t)

end PasturFixedPoint

namespace Measure

/-- **The Pastur measure** `ν.pastur t` of a Borel measure `ν` on `ℝ` at variance parameter
`t : ℝ≥0`. When `ν` is finite, it is the unique finite measure on `ℝ` whose resolvent transform
solves Pastur's self-consistent equation `m(z) = m_ν(z + t m(z))` off the real axis; for a
probability measure `ν`, this is the free semicircle convolution `ν ⊞ SC_t`. When `ν` is not
finite, `ν.pastur t` is `0`. -/
def pastur (ν : Measure ℝ) (t : ℝ≥0) : Measure ℝ :=
  by
    classical
    exact if h : IsFiniteMeasure ν then (exists_pasturMeasure ν t).choose else 0

/-- `ν.pastur t` is always a finite measure. -/
instance isFiniteMeasure_pastur (ν : Measure ℝ) (t : ℝ≥0) : IsFiniteMeasure (ν.pastur t) := by
  classical
  dsimp only [pastur]
  split_ifs with h
  · exact (exists_pasturMeasure ν t).choose_spec.1
  · infer_instance

/-- The real total mass of `ν.pastur t` agrees with that of `ν` for every measure `ν`. -/
@[simp]
theorem pastur_real_univ (ν : Measure ℝ) (t : ℝ≥0) :
    (ν.pastur t).real univ = ν.real univ := by
  classical
  by_cases h : IsFiniteMeasure ν
  · simpa only [pastur, dite_eq_left h] using (exists_pasturMeasure ν t).choose_spec.2.1
  · have htop : ν univ = ⊤ := by
      by_contra hne
      exact h ⟨lt_top_iff_ne_top.2 hne⟩
    simp [pastur, dite_eq_right h, measureReal_def, htop]

/-- `ν.pastur t` preserves total mass for finite measures. -/
@[simp]
theorem pastur_univ (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ≥0) :
    (ν.pastur t) univ = ν univ := by
  rw [← ofReal_measureReal, pastur_real_univ, ofReal_measureReal]

/-- If `ν` is a probability measure, then `ν.pastur t` is a probability measure. -/
instance isProbabilityMeasure_pastur (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℝ≥0) :
    IsProbabilityMeasure (ν.pastur t) :=
  ⟨by simp⟩

end Measure

section PasturAPI

variable {ν : Measure ℝ} [IsFiniteMeasure ν]

private lemma resolventTransform_pastur_eq_pasturAux (t : ℝ≥0) {z : ℂ} (hz : 0 < z.im) :
    resolventTransform (ν.pastur t) z = pasturAux ν t z := by
  classical
  have h : IsFiniteMeasure ν := inferInstance
  simpa only [Measure.pastur, dite_eq_left h] using
    ((exists_pasturMeasure ν t).choose_spec.2.2 z hz).symm

/-- **Uniqueness in the Stieltjes class for the Pastur equation.** In the upper half-plane,
`resolventTransform (ν.pastur t) z` is the unique complex number `w` with `0 ≤ w.im` solving
`w = resolventTransform ν (z + t * w)`. -/
theorem eq_resolventTransform_pastur_iff (t : ℝ≥0) {z w : ℂ} (hz : 0 < z.im) :
    w = resolventTransform (ν.pastur t) z ↔
      0 ≤ w.im ∧ w = resolventTransform ν (z + t * w) := by
  rw [resolventTransform_pastur_eq_pasturAux t hz, eq_pasturAux_iff t hz]

/-- **The Pastur equation off the real axis.** For every finite measure `ν` on `ℝ`, `t : ℝ≥0`, and
`z : ℂ` with `z.im ≠ 0`, `m_{ν.pastur t}(z) = m_ν(z + t m_{ν.pastur t}(z))`. -/
theorem resolventTransform_pastur_eq (t : ℝ≥0) {z : ℂ} (hz : z.im ≠ 0) :
    resolventTransform (ν.pastur t) z =
      resolventTransform ν (z + t * resolventTransform (ν.pastur t) z) := by
  rcases hz.lt_or_gt with hlt | hgt
  · have hconj : 0 < (conj z).im := by simpa using hlt
    have hupper := ((eq_resolventTransform_pastur_iff (ν := ν) t hconj).1 rfl).2
    have h := congrArg conj hupper
    rw [← Measure.resolventTransform_conj, ← Measure.resolventTransform_conj,
      Measure.resolventTransform_conj] at h
    simpa [map_add, map_mul] using h
  · exact ((eq_resolventTransform_pastur_iff (ν := ν) t hgt).1 rfl).2

omit [IsFiniteMeasure ν] in
/-- Off the real axis, the shifted spectral parameter `z + t m_{ν.pastur t}(z)` stays in the same
open half-plane as `z`. -/
theorem im_mul_im_add_mul_resolventTransform_pastur_pos (t : ℝ≥0) {z : ℂ} (hz : z.im ≠ 0) :
    0 < z.im * (z + t * resolventTransform (ν.pastur t) z).im := by
  have hzw : 0 ≤ z.im * (resolventTransform (ν.pastur t) z).im := by
    rw [im_resolventTransform, ← integral_const_mul]
    exact integral_nonneg fun x ↦ by
      have : z.im * (z.im / ((x - z.re) ^ 2 + z.im ^ 2)) =
          z.im ^ 2 / ((x - z.re) ^ 2 + z.im ^ 2) := by ring
      rw [this]
      positivity
  simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
  have hsq : 0 < z.im * z.im := mul_self_pos.2 hz
  nlinarith [t.coe_nonneg, mul_nonneg t.coe_nonneg hzw]

/-- **Strict contraction of the Pastur Jacobian.** Off the real axis, at
`ζ = z + t m_{ν.pastur t}(z)`, the complex derivative satisfies `‖t m_ν'(ζ)‖ < 1`. -/
theorem norm_mul_deriv_resolventTransform_pastur_lt_one (t : ℝ≥0) {z : ℂ} (hz : z.im ≠ 0) :
    ‖(t : ℂ) * deriv (resolventTransform ν) (z + t * resolventTransform (ν.pastur t) z)‖ < 1 := by
  let w := resolventTransform (ν.pastur t) z
  let ζ := z + t * w
  have hzw : 0 ≤ z.im * w.im := by
    dsimp only [w]
    rw [im_resolventTransform, ← integral_const_mul]
    exact integral_nonneg fun x ↦ by
      have : z.im * (z.im / ((x - z.re) ^ 2 + z.im ^ 2)) =
          z.im ^ 2 / ((x - z.re) ^ 2 + z.im ^ 2) := by ring
      rw [this]
      positivity
  obtain ⟨hb, hq⟩ := mul_integral_norm_resolvent_sq_eq (ν := ν) t hz hzw
    (resolventTransform_pastur_eq t hz)
  have hζ0 : ζ.im ≠ 0 := fun h ↦ by
    dsimp only [ζ] at h
    simp [h] at hq
  have hsupp : ζ ∉ algebraMap ℝ ℂ '' ν.support := by
    rintro ⟨x, -, hx⟩
    exact hζ0 (by simpa using congrArg im hx.symm)
  dsimp only [w, ζ] at hb hq hsupp ⊢
  rw [(hasDerivAt_resolventTransform _ hsupp).deriv, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg t.coe_nonneg]
  calc (t : ℝ) * ‖∫ x, resolvent (z + t * resolventTransform (ν.pastur t) z) x ^ 2 ∂ν‖
      ≤ (t : ℝ) * ∫ x, ‖resolvent (z + t * resolventTransform (ν.pastur t) z) x ^ 2‖ ∂ν :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) t.coe_nonneg
    _ = (t : ℝ) * ∫ x, ‖resolvent (z + t * resolventTransform (ν.pastur t) z) x‖ ^ 2 ∂ν := by
        simp_rw [norm_pow]
    _ = 1 - z.im / (z + t * resolventTransform (ν.pastur t) z).im := hb
    _ < 1 := by linarith

/-- The Pastur Jacobian `1 - t m_ν'(z + t m_{ν.pastur t}(z))` is nonzero off the real axis. -/
theorem one_sub_mul_deriv_resolventTransform_pastur_ne_zero (t : ℝ≥0) {z : ℂ} (hz : z.im ≠ 0) :
    1 - (t : ℂ) * deriv (resolventTransform ν)
      (z + t * resolventTransform (ν.pastur t) z) ≠ 0 := by
  intro h
  have hlt := norm_mul_deriv_resolventTransform_pastur_lt_one (ν := ν) t hz
  rw [← sub_eq_zero.1 h, norm_one] at hlt
  exact lt_irrefl 1 hlt

/-- **Complex derivative of the Pastur resolvent transform.** Off the real axis,
`m_{ν.pastur t}'(z) = m_ν'(ζ) / (1 - t m_ν'(ζ))` where `ζ = z + t m_{ν.pastur t}(z)`. -/
theorem hasDerivAt_resolventTransform_pastur (t : ℝ≥0) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (resolventTransform (ν.pastur t))
      (deriv (resolventTransform ν) (z + t * resolventTransform (ν.pastur t) z) /
        (1 - (t : ℂ) * deriv (resolventTransform ν)
          (z + t * resolventTransform (ν.pastur t) z))) z := by
  have hpos := im_mul_im_add_mul_resolventTransform_pastur_pos (ν := ν) t hz
  have hζ0 : (z + t * resolventTransform (ν.pastur t) z).im ≠ 0 :=
    fun h ↦ by simp [h] at hpos
  have hsupp : z ∉ algebraMap ℝ ℂ '' (ν.pastur t).support := by
    rintro ⟨x, -, hx⟩
    exact hz (by simpa using congrArg im hx.symm)
  have heq : ∀ᶠ w : ℂ in 𝓝 z, resolventTransform (ν.pastur t) w =
      resolventTransform ν (w + t * resolventTransform (ν.pastur t) w) := by
    filter_upwards [(isOpen_compl_singleton.preimage continuous_im).mem_nhds hz] with w hw
    exact resolventTransform_pastur_eq t hw
  exact hasDerivAt_of_pastur_eq t
    (hasDerivAt_resolventTransform z hsupp).continuousAt heq hζ0
    (one_sub_mul_deriv_resolventTransform_pastur_ne_zero t hz)

namespace Measure

/-- The Pastur measure of the zero measure is zero. -/
@[simp]
theorem pastur_zero_measure (t : ℝ≥0) : (0 : Measure ℝ).pastur t = 0 := by
  apply ext_of_resolventTransform fun z hz ↦ ?_
  symm
  rw [eq_resolventTransform_pastur_iff t hz]
  simp

/-- At `t = 0`, the Pastur measure of a finite measure `ν` is `ν` itself. -/
@[simp]
theorem pastur_zero (ν : Measure ℝ) [IsFiniteMeasure ν] : ν.pastur 0 = ν := by
  apply ext_of_resolventTransform fun z hz ↦ ?_
  symm
  rw [eq_resolventTransform_pastur_iff 0 hz]
  refine ⟨?_, by simp⟩
  rw [im_resolventTransform]
  exact integral_nonneg fun x ↦ div_nonneg hz.le (by positivity)

/-- **Semigroup property of the Pastur evolution.** Evolving a finite measure `ν` by `s` and then
by `t` equals evolving `ν` by `s + t`. -/
@[simp]
theorem pastur_pastur (ν : Measure ℝ) [IsFiniteMeasure ν] (s t : ℝ≥0) :
    (ν.pastur s).pastur t = ν.pastur (s + t) := by
  apply ext_of_resolventTransform fun z hz ↦ ?_
  set w := resolventTransform (ν.pastur (s + t)) z
  obtain ⟨hwim, hweq⟩ := (eq_resolventTransform_pastur_iff (ν := ν) (s + t) hz).1 rfl
  have hz' : 0 < (z + t * w).im := by
    simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    nlinarith [t.coe_nonneg]
  have hstep1 : w = resolventTransform (ν.pastur s) (z + t * w) := by
    rw [eq_resolventTransform_pastur_iff s hz']
    refine ⟨hwim, ?_⟩
    convert hweq using 2
    push_cast
    ring
  exact ((eq_resolventTransform_pastur_iff (ν := ν.pastur s) t hz).2 ⟨hwim, hstep1⟩).symm

/-- **Affine covariance of the Pastur evolution.** Pushing `ν.pastur t` forward by `x ↦ a + b * x`
evolves the pushed-forward measure at rescaled time `b² t` (including the degenerate slope `b = 0`).
-/
theorem map_affine_pastur (ν : Measure ℝ) [IsFiniteMeasure ν] (a b : ℝ) (t : ℝ≥0) :
    (ν.pastur t).map (fun x : ℝ ↦ a + b * x) =
      (ν.map (fun x : ℝ ↦ a + b * x)).pastur (Real.toNNReal (b ^ 2) * t) := by
  have : IsFiniteMeasure ((ν.pastur t).map (fun x : ℝ ↦ a + b * x)) :=
    (ν.pastur t).isFiniteMeasure_map (fun x : ℝ ↦ a + b * x)
  have : IsFiniteMeasure (ν.map (fun x : ℝ ↦ a + b * x)) :=
    ν.isFiniteMeasure_map (fun x : ℝ ↦ a + b * x)
  by_cases hb : b = 0
  · subst hb
    have h0 : Real.toNNReal ((0 : ℝ) ^ 2) * t = 0 := by simp
    rw [h0, pastur_zero]
    simp [Measure.map_const]
  · apply ext_of_resolventTransform fun z hz ↦ ?_
    let w := resolventTransform ((ν.pastur t).map (fun x : ℝ ↦ a + b * x)) z
    have hzim : 0 ≤ w.im := by
      dsimp only [w]
      rw [im_resolventTransform]
      exact integral_nonneg fun x ↦ div_nonneg hz.le (by positivity)
    rw [eq_resolventTransform_pastur_iff _ hz]
    refine ⟨hzim, ?_⟩
    have hw_eq : w = (b : ℂ)⁻¹ * resolventTransform (ν.pastur t) ((z - a) / b) :=
      resolventTransform_map_affine a b hb z
    have hz_div : ((z - a) / b).im ≠ 0 := by
      have : ((z - a) / (b : ℂ)).im = z.im / b := by
        rw [div_eq_mul_inv, ← ofReal_inv, mul_comm, im_ofReal_mul]
        simp [div_eq_mul_inv, mul_comm]
      rw [this]
      exact div_ne_zero hz.ne' hb
    have hpastur := resolventTransform_pastur_eq (ν := ν) t hz_div
    calc w = (b : ℂ)⁻¹ * resolventTransform (ν.pastur t) ((z - a) / b) := hw_eq
      _ = (b : ℂ)⁻¹ * resolventTransform ν
            ((z - a) / b + t * resolventTransform (ν.pastur t) ((z - a) / b)) :=
          congrArg ((b : ℂ)⁻¹ * ·) hpastur
      _ = (b : ℂ)⁻¹ * resolventTransform ν
            ((z + (Real.toNNReal (b ^ 2) * t : ℝ≥0) * w - a) / b) := by
          congr 2
          rw [hw_eq]
          simp only [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg b), ofReal_mul, ofReal_pow]
          field_simp [hb]
          ring
      _ = resolventTransform (ν.map (fun x : ℝ ↦ a + b * x))
            (z + (Real.toNNReal (b ^ 2) * t : ℝ≥0) * w) :=
          (resolventTransform_map_affine a b hb _).symm

end Measure

namespace ProbabilityMeasure

/-- **The Pastur evolution on `ProbabilityMeasure ℝ`.** At time `t`, this is the additive free
convolution `ν ⊞ SC_t` with the centred semicircle law of variance `t`. -/
def pastur (ν : ProbabilityMeasure ℝ) (t : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨(ν : Measure ℝ).pastur t, inferInstance⟩

/-- Coercing `ν.pastur t` to `Measure ℝ` commutes with `Measure.pastur`. -/
@[simp, norm_cast]
theorem toMeasure_pastur (ν : ProbabilityMeasure ℝ) (t : ℝ≥0) :
    (ν.pastur t : Measure ℝ) = (ν : Measure ℝ).pastur t :=
  (rfl)

/-- At `t = 0`, the Pastur evolution on `ProbabilityMeasure ℝ` is the identity. -/
@[simp]
theorem pastur_zero (ν : ProbabilityMeasure ℝ) : ν.pastur 0 = ν := by
  ext1
  simp

/-- Semigroup law for the Pastur evolution on `ProbabilityMeasure ℝ`. -/
@[simp]
theorem pastur_pastur (ν : ProbabilityMeasure ℝ) (s t : ℝ≥0) :
    (ν.pastur s).pastur t = ν.pastur (s + t) := by
  ext1
  simp

/-- Uniform comparison bound between `m_{q.1.pastur q.2}(z)` and `m_{p.1}(z + p.2 w)` used to prove
joint weak continuity of `ProbabilityMeasure.pastur`. -/
private lemma norm_resolventTransform_pastur_sub_resolventTransform_le
    (p q : ProbabilityMeasure ℝ × ℝ≥0) {z w : ℂ} (hz : 0 < z.im) (hwim : 0 ≤ w.im) :
    ‖resolventTransform (q.1.pastur q.2 : Measure ℝ) z -
        resolventTransform (p.1 : Measure ℝ) (z + p.2 * w)‖ ≤
      ‖(q.2 : ℂ) * resolventTransform (q.1.pastur q.2 : Measure ℝ) z - (p.2 : ℂ) * w‖ /
          (z.im * (z + p.2 * w).im) +
        ‖resolventTransform (q.1 : Measure ℝ) (z + p.2 * w) -
          resolventTransform (p.1 : Measure ℝ) (z + p.2 * w)‖ := by
  let fq := resolventTransform (q.1.pastur q.2 : Measure ℝ) z
  let ζ₀ := z + p.2 * w
  have hζ₀pos : 0 < ζ₀.im := by
    simp only [ζ₀, add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    nlinarith [p.2.coe_nonneg]
  have hfq_eq : fq = resolventTransform (q.1 : Measure ℝ) (z + q.2 * fq) :=
    resolventTransform_pastur_eq q.2 hz.ne'
  have hfq_im : 0 ≤ fq.im := by
    dsimp only [fq]
    rw [im_resolventTransform]
    exact integral_nonneg fun x ↦ div_nonneg hz.le (by positivity)
  have hζq : z.im ≤ (z + q.2 * fq).im := by
    simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    nlinarith [q.2.coe_nonneg]
  have hζqpos : 0 < (z + q.2 * fq).im := hz.trans_le hζq
  calc ‖fq - resolventTransform (p.1 : Measure ℝ) ζ₀‖
      = ‖resolventTransform (q.1 : Measure ℝ) (z + q.2 * fq) -
          resolventTransform (p.1 : Measure ℝ) ζ₀‖ :=
        congrArg (fun u ↦ ‖u - resolventTransform (p.1 : Measure ℝ) ζ₀‖) hfq_eq
    _ ≤ ‖resolventTransform (q.1 : Measure ℝ) (z + q.2 * fq) -
          resolventTransform (q.1 : Measure ℝ) ζ₀‖ +
        ‖resolventTransform (q.1 : Measure ℝ) ζ₀ -
          resolventTransform (p.1 : Measure ℝ) ζ₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖(q.2 : ℂ) * fq - (p.2 : ℂ) * w‖ / (z.im * ζ₀.im) +
        ‖resolventTransform (q.1 : Measure ℝ) ζ₀ -
          resolventTransform (p.1 : Measure ℝ) ζ₀‖ := by
        gcongr
        have hlip := norm_resolventTransform_sub_le (μ := (q.1 : Measure ℝ))
          hζqpos.ne' hζ₀pos.ne'
        simp only [probReal_univ, mul_one, abs_of_pos hζqpos, abs_of_pos hζ₀pos] at hlip
        refine hlip.trans ?_
        have hsub : z + q.2 * fq - ζ₀ = (q.2 : ℂ) * fq - (p.2 : ℂ) * w := by
          dsimp only [ζ₀]; ring
        rw [hsub]
        gcongr

/-- **Joint weak continuity of the Pastur evolution.** The map `(ν, t) ↦ ν.pastur t` is continuous
on `ProbabilityMeasure ℝ × ℝ≥0`. -/
@[fun_prop]
theorem continuous_pastur : Continuous fun p : ProbabilityMeasure ℝ × ℝ≥0 ↦ p.1.pastur p.2 := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [ContinuousAt, tendsto_iff_tendsto_resolventTransform]
  intro z hz
  rw [tendsto_iff_ultrafilter]
  intro U hU
  let f : ProbabilityMeasure ℝ × ℝ≥0 → ℂ :=
    fun q ↦ resolventTransform (q.1.pastur q.2 : Measure ℝ) z
  let K : Set ℂ := {w : ℂ | 0 ≤ w.im} ∩ closedBall 0 (z.im)⁻¹
  have hKcpt : IsCompact K :=
    (isCompact_closedBall 0 (z.im)⁻¹).inter_left (isClosed_le continuous_const continuous_im)
  have hmem : K ∈ U.map f := Ultrafilter.mem_map.2 <| Eventually.of_forall fun q ↦
    ⟨by rw [mem_ofPred_eq, im_resolventTransform]
        exact integral_nonneg fun x ↦ div_nonneg hz.le (by positivity),
     mem_closedBall_zero_iff.2 <| by
        simpa [f, abs_of_pos hz] using
          norm_resolventTransform_le (μ := (q.1.pastur q.2 : Measure ℝ)) hz.ne'⟩
  obtain ⟨w, hwK, hwlim⟩ := hKcpt.ultrafilter_le_nhds (U.map f) (le_principal_iff.2 hmem)
  have hwim : 0 ≤ w.im := hwK.1
  let ζ₀ : ℂ := z + p.2 * w
  have hζ₀pos : 0 < ζ₀.im := by
    simp only [ζ₀, add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    nlinarith [p.2.coe_nonneg]
  have hq2 : Tendsto (fun q : ProbabilityMeasure ℝ × ℝ≥0 ↦ (q.2 : ℂ)) U (𝓝 (p.2 : ℂ)) :=
    (continuous_ofReal.comp (NNReal.continuous_coe.comp continuous_snd)).tendsto p |>.mono_left hU
  have h1 : Tendsto (fun q : ProbabilityMeasure ℝ × ℝ≥0 ↦
      ‖(q.2 : ℂ) * f q - (p.2 : ℂ) * w‖ / (z.im * ζ₀.im)) U (𝓝 0) := by
    simpa using ((hq2.mul hwlim).sub (tendsto_const_nhds (x := (p.2 : ℂ) * w))).norm.div_const
      (z.im * ζ₀.im)
  have h2 : Tendsto (fun q : ProbabilityMeasure ℝ × ℝ≥0 ↦
      ‖resolventTransform (q.1 : Measure ℝ) ζ₀ - resolventTransform (p.1 : Measure ℝ) ζ₀‖)
      U (𝓝 0) := by
    have hweak := tendsto_resolventTransform_of_tendsto
      (continuous_fst.tendsto p |>.mono_left hU) hζ₀pos.ne'
    simpa using (hweak.sub (tendsto_const_nhds (x := resolventTransform (p.1 : Measure ℝ) ζ₀))).norm
  have hdiff0 : Tendsto (fun q : ProbabilityMeasure ℝ × ℝ≥0 ↦
      f q - resolventTransform (p.1 : Measure ℝ) ζ₀) U (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 <| squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun q ↦ norm_resolventTransform_pastur_sub_resolventTransform_le p q hz hwim)
      (by simpa only [f, ζ₀, add_zero] using h1.add h2)
  have hflim : Tendsto f U (𝓝 (resolventTransform (p.1 : Measure ℝ) ζ₀)) := by
    simpa using hdiff0.add (tendsto_const_nhds (x := resolventTransform (p.1 : Measure ℝ) ζ₀))
  have hweq : w = f p := (eq_resolventTransform_pastur_iff (ν := (p.1 : Measure ℝ)) p.2 hz).2
    ⟨hwim, tendsto_nhds_unique hwlim hflim⟩
  dsimp only [f] at hweq hwlim
  exact hweq ▸ hwlim

end ProbabilityMeasure

end PasturAPI

end MeasureTheory

end
