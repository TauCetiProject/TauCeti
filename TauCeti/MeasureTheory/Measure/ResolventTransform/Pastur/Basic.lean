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
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Convex
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
(`MeasureTheory.existsUnique_im_nonneg_and_eq_resolventTransform_add_mul`).
Existence follows from Schauder's fixed-point theorem (`TauCeti.schauderFixedPoint_compactConvex`)
on the compact convex half-disc `{w : ℂ | 0 ≤ w.im} ∩ closedBall 0 ((Im z)⁻¹ ν(ℝ))`. Uniqueness
comes from the imaginary-part identity `t ∫ ‖(x - ζ)⁻¹‖² dν(x) = 1 - Im z / Im ζ < 1` at
`ζ = z + t w`, which makes the difference equation strictly contractive by the arithmetic-geometric
mean inequality without assuming `ν` has unit mass.

That same bound implies `‖t m_ν'(ζ)‖ < 1`, so `1 - t m_ν'(ζ) ≠ 0` and the fixed point is complex
differentiable on `{z : ℂ | 0 < z.im}` with derivative `m_ν'(ζ) / (1 - t m_ν'(ζ))`. Along the
positive imaginary axis it satisfies `iy w(iy) → -ν(ℝ)` as `y → ∞`. By the Pick–Nevanlinna
characterization
(`MeasureTheory.exists_isFiniteMeasure_measureReal_univ_eq_and_resolventTransform_eq`), there is
a unique finite measure `ν.pastur t` on `ℝ` of total mass `ν(ℝ)` whose resolvent transform solves
the Pastur equation off the real axis. When `ν` is a probability measure, `ν.pastur t` is a
probability measure; by Biane (1997), this corresponds to the additive free convolution with the
centred semicircle law of variance `t` (that identification is not formalized here).

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

* `MeasureTheory.existsUnique_im_nonneg_and_eq_resolventTransform_add_mul`: existence and uniqueness
  in the closed upper half-plane for the Pastur equation `w = m_ν(z + t w)` at `0 < z.im`.
* `MeasureTheory.eq_resolventTransform_pastur_iff` and `MeasureTheory.Measure.eq_pastur_iff`:
  `m_{ν.pastur t}(z)` is the unique solution with `0 ≤ w.im` for `0 < z.im`, characterizing
  `ν.pastur t` among finite measures.
* `MeasureTheory.resolventTransform_pastur_eq`: `m_{ν.pastur t}(z) = m_ν(z + t m_{ν.pastur t}(z))`
  for all `z.im ≠ 0`.
* `MeasureTheory.norm_mul_deriv_resolventTransform_add_mul_resolventTransform_pastur_lt_one` and
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

private lemma le_im_add_nnreal_mul (t : ℝ≥0) (z : ℂ) {w : ℂ} (hw : 0 ≤ w.im) :
    z.im ≤ (z + t * w).im := by
  simpa using mul_nonneg t.coe_nonneg hw

private lemma im_add_nnreal_mul_pos (t : ℝ≥0) {z w : ℂ} (hz : 0 < z.im) (hw : 0 ≤ w.im) :
    0 < (z + t * w).im :=
  hz.trans_le (le_im_add_nnreal_mul t z hw)

private lemma sq_im_le_im_mul_im_add_nnreal_mul (t : ℝ≥0) {z w : ℂ} (hzw : 0 ≤ z.im * w.im) :
    z.im ^ 2 ≤ z.im * (z + t * w).im := by
  have him : (z + t * w).im = z.im + (t : ℝ) * w.im := by simp
  rw [him]
  nlinarith [mul_nonneg t.coe_nonneg hzw]

private lemma im_mul_im_add_nnreal_mul_pos (t : ℝ≥0) {z w : ℂ} (hz : z.im ≠ 0)
    (hzw : 0 ≤ z.im * w.im) : 0 < z.im * (z + t * w).im :=
  (sq_pos_of_ne_zero hz).trans_le (sq_im_le_im_mul_im_add_nnreal_mul t hzw)

private lemma abs_im_le_abs_im_add_nnreal_mul (t : ℝ≥0) {z w : ℂ} (hzw : 0 ≤ z.im * w.im) :
    |z.im| ≤ |(z + t * w).im| := by
  by_cases hz : z.im = 0
  · simpa [hz] using abs_nonneg (z + t * w).im
  · have hle : |z.im| * |z.im| ≤ |z.im| * |(z + t * w).im| := calc
      |z.im| * |z.im| = z.im ^ 2 := by rw [abs_mul_abs_self, sq]
      _ ≤ z.im * (z + t * w).im := sq_im_le_im_mul_im_add_nnreal_mul t hzw
      _ ≤ |z.im * (z + t * w).im| := le_abs_self _
      _ = |z.im| * |(z + t * w).im| := abs_mul _ _
    exact le_of_mul_le_mul_left hle (abs_pos.2 hz)

private lemma isCompact_halfDisc (R : ℝ) :
    IsCompact ({w : ℂ | 0 ≤ w.im} ∩ closedBall 0 R) :=
  (isCompact_closedBall 0 R).inter_left (isClosed_le continuous_const continuous_im)

/-- Bound on the shift increment `‖m_ν(z + t w) - m_ν(z)‖` off the real axis. -/
theorem norm_resolventTransform_add_nnreal_mul_sub_le {ν : Measure ℝ} [IsFiniteMeasure ν]
    {t : ℝ≥0} {z w : ℂ} (hζ : (z + t * w).im ≠ 0) (hz : z.im ≠ 0) :
    ‖resolventTransform ν (z + t * w) - resolventTransform ν z‖ ≤
      (t : ℝ) * ‖w‖ / (|(z + t * w).im| * |z.im|) * ν.real univ := by
  simpa [add_sub_cancel_left, norm_mul, norm_real, Real.norm_of_nonneg t.coe_nonneg] using
    norm_resolventTransform_sub_le (μ := ν) hζ hz

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
  have hprod : 0 < z.im * ζ.im := im_mul_im_add_nnreal_mul_pos t hz hzw
  have hζ0 : ζ.im ≠ 0 := right_ne_zero_of_mul hprod.ne'
  have hquot : 0 < z.im / ζ.im := div_pos_iff.2 (mul_pos_iff.1 hprod)
  have hint_im : w.im = ζ.im * ∫ x, ‖resolvent ζ x‖ ^ 2 ∂ν := by
    rw [congrArg im hw, im_resolventTransform, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    dsimp only
    rw [Complex.resolvent_real_eq_inv, norm_inv, inv_pow, ← normSq_eq_norm_sq, normSq_apply]
    simp [sq, div_eq_mul_inv]
  refine ⟨?_, hquot⟩
  apply mul_right_cancel₀ hζ0
  calc ((t : ℝ) * ∫ x, ‖resolvent ζ x‖ ^ 2 ∂ν) * ζ.im
      = (t : ℝ) * (ζ.im * ∫ x, ‖resolvent ζ x‖ ^ 2 ∂ν) := by ring
    _ = (t : ℝ) * w.im := by rw [← hint_im]
    _ = ζ.im - z.im := by linarith [hζim]
    _ = (1 - z.im / ζ.im) * ζ.im := by field_simp [hζ0]

/-- Uniform bound on `m_ν(z + t w)` for `0 < z.im` and `0 ≤ w.im`. -/
private lemma norm_resolventTransform_add_nnreal_mul_le (t : ℝ≥0) {z w : ℂ} (hz : 0 < z.im)
    (hw : 0 ≤ w.im) :
    ‖resolventTransform ν (z + t * w)‖ ≤ (z.im)⁻¹ * ν.real univ := by
  have hζ : z.im ≤ (z + t * w).im := le_im_add_nnreal_mul t z hw
  have hζpos : 0 < (z + t * w).im := hz.trans_le hζ
  calc ‖resolventTransform ν (z + t * w)‖
      ≤ |(z + t * w).im|⁻¹ * ν.real univ := norm_resolventTransform_le hζpos.ne'
    _ ≤ (z.im)⁻¹ * ν.real univ := by rw [abs_of_pos hζpos]; gcongr

/-- Existence of a solution in the closed upper half-plane via Schauder's fixed-point theorem. -/
private lemma exists_eq_resolventTransform_add_mul (t : ℝ≥0) {z : ℂ} (hz : 0 < z.im) :
    ∃ w : ℂ, 0 ≤ w.im ∧ w = resolventTransform ν (z + t * w) := by
  let R : ℝ := (z.im)⁻¹ * ν.real univ
  have hR0 : 0 ≤ R := by positivity
  let K : Set ℂ := {w : ℂ | 0 ≤ w.im} ∩ closedBall 0 R
  have hKconv : Convex ℝ K := (convex_halfSpace_im_ge 0).inter (convex_closedBall 0 R)
  have hKne : K.Nonempty := ⟨0, by simp, mem_closedBall_self hR0⟩
  have hmaps : MapsTo (fun w : ℂ ↦ resolventTransform ν (z + t * w)) K K := by
    rintro w ⟨hwim, -⟩
    exact ⟨im_resolventTransform_nonneg (im_add_nnreal_mul_pos t hz hwim).le,
      mem_closedBall_zero_iff.2 (norm_resolventTransform_add_nnreal_mul_le t hz hwim)⟩
  have hcont : ContinuousOn (fun w : ℂ ↦ resolventTransform ν (z + t * w)) K := by
    intro w hw
    have hζpos : 0 < (z + t * w).im := im_add_nnreal_mul_pos t hz hw.1
    exact (ContinuousAt.comp (g := resolventTransform ν) (f := fun u : ℂ ↦ z + t * u)
      (hasDerivAt_resolventTransform_of_im_ne_zero hζpos.ne').continuousAt
      (by fun_prop : Continuous fun u : ℂ ↦ z + t * u).continuousAt).continuousWithinAt
  obtain ⟨⟨w₀, hw₀K⟩, hfix⟩ := TauCeti.schauderFixedPoint_compactConvex (isCompact_halfDisc R)
    hKconv hKne ⟨hmaps.restrict _ K K, hcont.mapsToRestrict hmaps⟩
  exact ⟨w₀, hw₀K.1, (congrArg Subtype.val hfix).symm⟩

/-- Uniqueness in the closed upper half-plane via Biane's contraction estimate and AM-GM. -/
private lemma eq_of_eq_resolventTransform_add_mul (t : ℝ≥0) {z w₁ w₀ : ℂ} (hz : 0 < z.im)
    (hw₁im : 0 ≤ w₁.im) (hw₁eq : w₁ = resolventTransform ν (z + t * w₁))
    (hw₀im : 0 ≤ w₀.im) (hw₀eq : w₀ = resolventTransform ν (z + t * w₀)) :
    w₁ = w₀ := by
  set ζ₁ := z + t * w₁ with hζ₁
  set ζ₀ := z + t * w₀ with hζ₀
  have hζ₁pos : 0 < ζ₁.im := im_add_nnreal_mul_pos t hz hw₁im
  have hζ₀pos : 0 < ζ₀.im := im_add_nnreal_mul_pos t hz hw₀im
  obtain ⟨hb₁, hq₁⟩ := mul_integral_norm_resolvent_sq_eq (ν := ν) t hz.ne'
    (mul_nonneg hz.le hw₁im) hw₁eq
  obtain ⟨hb₀, hq₀⟩ := mul_integral_norm_resolvent_sq_eq (ν := ν) t hz.ne'
    (mul_nonneg hz.le hw₀im) hw₀eq
  rw [← hζ₁] at hb₁ hq₁
  rw [← hζ₀] at hb₀ hq₀
  have hsub : w₁ - w₀ = ((t : ℂ) * (w₁ - w₀)) * ∫ x, resolvent ζ₁ x * resolvent ζ₀ x ∂ν := by
    nth_rw 1 [hw₁eq, hw₀eq]
    rw [resolventTransform_sub_resolventTransform hζ₁pos.ne' hζ₀pos.ne']
    simp only [hζ₁, hζ₀]; ring
  have hamgm (x : ℝ) : ‖resolvent ζ₁ x * resolvent ζ₀ x‖ ≤
      (‖resolvent ζ₁ x‖ ^ 2 + ‖resolvent ζ₀ x‖ ^ 2) / 2 := by
    rw [norm_mul]
    nlinarith [sq_nonneg (‖resolvent ζ₁ x‖ - ‖resolvent ζ₀ x‖)]
  let r : ℝ := (t : ℝ) * ∫ x, ‖resolvent ζ₁ x * resolvent ζ₀ x‖ ∂ν
  have hr_lt : r < 1 := by
    have h₁ := integrable_norm_resolvent_sq (μ := ν) hζ₁pos.ne'
    have h₀ := integrable_norm_resolvent_sq (μ := ν) hζ₀pos.ne'
    have hsum_int := (h₁.add h₀).div_const 2
    have hprod_int : Integrable (fun x : ℝ ↦ ‖resolvent ζ₁ x * resolvent ζ₀ x‖) ν :=
      hsum_int.mono' (by fun_prop) (ae_of_all _ fun x ↦ by
        simpa only [Pi.add_apply, Real.norm_of_nonneg (norm_nonneg _)] using hamgm x)
    have hle : ∫ x, ‖resolvent ζ₁ x * resolvent ζ₀ x‖ ∂ν ≤
        (∫ x, ‖resolvent ζ₁ x‖ ^ 2 ∂ν + ∫ x, ‖resolvent ζ₀ x‖ ^ 2 ∂ν) / 2 := by
      rw [← integral_add h₁ h₀, ← integral_div]
      exact integral_mono hprod_int hsum_int hamgm
    have hr_le : r ≤ ((1 - z.im / ζ₁.im) + (1 - z.im / ζ₀.im)) / 2 :=
      (mul_le_mul_of_nonneg_left hle t.coe_nonneg).trans_eq (by rw [← hb₁, ← hb₀]; ring)
    linarith
  have hnorm_le : ‖w₁ - w₀‖ ≤ ‖w₁ - w₀‖ * r := by
    calc ‖w₁ - w₀‖ = ‖((t : ℂ) * (w₁ - w₀)) * ∫ x, resolvent ζ₁ x * resolvent ζ₀ x ∂ν‖ :=
          congrArg norm hsub
      _ = ‖w₁ - w₀‖ * ((t : ℝ) * ‖∫ x, resolvent ζ₁ x * resolvent ζ₀ x ∂ν‖) := by
          rw [norm_mul, norm_mul, norm_real, Real.norm_of_nonneg t.coe_nonneg]; ring
      _ ≤ ‖w₁ - w₀‖ * r := by dsimp only [r]; gcongr; exact norm_integral_le_integral_norm _
  exact sub_eq_zero.1 (norm_eq_zero.1 (by nlinarith [norm_nonneg (w₁ - w₀)]))

/-- **Existence and uniqueness for the Pastur equation.** For every finite Borel measure `ν` on `ℝ`,
`t : ℝ≥0`, and `z : ℂ` with `0 < z.im`, there is a unique `w : ℂ` with `0 ≤ w.im` solving
`w = resolventTransform ν (z + t * w)`. -/
theorem existsUnique_im_nonneg_and_eq_resolventTransform_add_mul (t : ℝ≥0) {z : ℂ}
    (hz : 0 < z.im) :
    ∃! w : ℂ, 0 ≤ w.im ∧ w = resolventTransform ν (z + t * w) := by
  obtain ⟨w₀, hw₀im, hw₀eq⟩ := exists_eq_resolventTransform_add_mul (ν := ν) t hz
  exact ⟨w₀, ⟨hw₀im, hw₀eq⟩,
    fun w₁ ⟨hw₁im, hw₁eq⟩ ↦ eq_of_eq_resolventTransform_add_mul t hz hw₁im hw₁eq hw₀im hw₀eq⟩

/-- Auxiliary upper-half-plane Pastur fixed point used to construct `Measure.pastur`. -/
private def pasturAux (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ≥0) (z : ℂ) : ℂ :=
  if hz : 0 < z.im then
    (existsUnique_im_nonneg_and_eq_resolventTransform_add_mul (ν := ν) t hz).choose
  else 0

private lemma pasturAux_spec (t : ℝ≥0) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (pasturAux ν t z).im ∧
      pasturAux ν t z = resolventTransform ν (z + t * pasturAux ν t z) := by
  simpa only [pasturAux, dite_eq_left hz] using
    (existsUnique_im_nonneg_and_eq_resolventTransform_add_mul (ν := ν) t hz).choose_spec.1

private lemma eq_pasturAux_iff (t : ℝ≥0) {z w : ℂ} (hz : 0 < z.im) :
    w = pasturAux ν t z ↔ 0 ≤ w.im ∧ w = resolventTransform ν (z + t * w) := by
  refine ⟨fun h ↦ h ▸ pasturAux_spec t hz, fun hw ↦ ?_⟩
  simpa only [pasturAux, dite_eq_left hz] using
    (existsUnique_im_nonneg_and_eq_resolventTransform_add_mul (ν := ν) t hz).choose_spec.2 w hw

private lemma norm_pasturAux_le (t : ℝ≥0) {z : ℂ} (hz : 0 < z.im) :
    ‖pasturAux ν t z‖ ≤ (z.im)⁻¹ * ν.real univ := by
  obtain ⟨hwim, hweq⟩ := pasturAux_spec (ν := ν) t hz
  rw [hweq]
  exact norm_resolventTransform_add_nnreal_mul_le t hz hwim

/-- Compactness-plus-uniqueness criterion for convergence to `pasturAux ν t z`: if `f` eventually
lies in the compact half-disc `{w | 0 ≤ w.im} ∩ closedBall 0 R` along `l` and every ultrafilter
limit point solves the Pastur equation, then `Tendsto f l (𝓝 (pasturAux ν t z))`. -/
private lemma tendsto_pasturAux_of_ultrafilter {α : Type*} {l : Filter α} {f : α → ℂ} {R : ℝ}
    (t : ℝ≥0) {z : ℂ} (hz : 0 < z.im)
    (hmem : ∀ᶠ a in l, 0 ≤ (f a).im ∧ ‖f a‖ ≤ R)
    (hlim : ∀ (U : Ultrafilter α), ↑U ≤ l → ∀ w : ℂ, 0 ≤ w.im → Tendsto f U (𝓝 w) →
      w = resolventTransform ν (z + t * w)) :
    Tendsto f l (𝓝 (pasturAux ν t z)) := by
  refine (isCompact_halfDisc R).tendsto_nhds_of_unique_mapClusterPt
    (hmem.mono fun a ha ↦ ⟨ha.1, mem_closedBall_zero_iff.2 ha.2⟩) fun w hwK hcl ↦ ?_
  obtain ⟨U, hU, hwlim⟩ := mapClusterPt_iff_ultrafilter.1 hcl
  exact (eq_pasturAux_iff t hz).2 ⟨hwK.1, hlim U hU w hwK.1 hwlim⟩

private lemma continuousAt_pasturAux (t : ℝ≥0) {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt (pasturAux ν t) z := by
  refine tendsto_pasturAux_of_ultrafilter t hz (R := 2 * (z.im)⁻¹ * ν.real univ) ?_ ?_
  · have hhalf : {u : ℂ | z.im / 2 < u.im} ∈ 𝓝 z :=
      (isOpen_lt continuous_const continuous_im).mem_nhds (by rw [mem_ofPred_eq]; linarith)
    filter_upwards [hhalf] with u hu
    have hupos : 0 < u.im := by linarith
    refine ⟨(pasturAux_spec t hupos).1, ?_⟩
    calc ‖pasturAux ν t u‖ ≤ (u.im)⁻¹ * ν.real univ := norm_pasturAux_le t hupos
      _ ≤ (z.im / 2)⁻¹ * ν.real univ := by gcongr
      _ = 2 * (z.im)⁻¹ * ν.real univ := by ring
  · intro U hU w hwim hwlim
    have hζpos : 0 < (z + t * w).im := im_add_nnreal_mul_pos t hz hwim
    have hζlim : Tendsto (fun u : ℂ ↦ u + t * pasturAux ν t u) U (𝓝 (z + t * w)) :=
      (tendsto_id.mono_left hU).add (tendsto_const_nhds.mul hwlim)
    have hrhs : Tendsto (fun u : ℂ ↦ resolventTransform ν (u + t * pasturAux ν t u)) U
        (𝓝 (resolventTransform ν (z + t * w))) :=
      (hasDerivAt_resolventTransform_of_im_ne_zero hζpos.ne').continuousAt.tendsto.comp hζlim
    have hev : (fun u : ℂ ↦ pasturAux ν t u) =ᶠ[U]
        fun u : ℂ ↦ resolventTransform ν (u + t * pasturAux ν t u) := by
      filter_upwards [hU ((isOpen_lt continuous_const continuous_im).mem_nhds hz)] with u hu
      exact (pasturAux_spec t hu).2
    exact tendsto_nhds_unique hwlim (hrhs.congr' hev.symm)

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
  have hm_deriv : HasDerivAt (resolventTransform ν) d (ζ z) :=
    (hasDerivAt_resolventTransform_of_im_ne_zero (μ := ν) hζ0).differentiableAt.hasDerivAt
  let Φ : ℂ → ℂ := fun u ↦ u - (t : ℂ) * resolventTransform ν u
  have hΦ_deriv : HasDerivAt Φ (1 - (t : ℂ) * d) (ζ z) :=
    (hasDerivAt_id (ζ z)).sub (hm_deriv.const_mul (t : ℂ))
  have hζ_cont : ContinuousAt ζ z := continuousAt_id.add (continuousAt_const.mul hcont)
  have hinv : ∀ᶠ w in 𝓝 z, Φ (ζ w) = w :=
    heq.mono fun w hw ↦ by dsimp only [Φ, ζ]; rw [← hw]; ring
  have hζ_deriv : HasDerivAt ζ (1 - (t : ℂ) * d)⁻¹ z :=
    hΦ_deriv.of_local_left_inverse hζ_cont hjac hinv
  rw [div_eq_mul_inv]
  exact (hm_deriv.comp z hζ_deriv).congr_of_eventuallyEq heq

private lemma norm_mul_deriv_resolventTransform_lt_one_of_eq (t : ℝ≥0) {z w : ℂ}
    (hz : z.im ≠ 0) (hzw : 0 ≤ z.im * w.im)
    (hw : w = resolventTransform ν (z + t * w)) :
    ‖(t : ℂ) * deriv (resolventTransform ν) (z + t * w)‖ < 1 := by
  obtain ⟨hb, hq⟩ := mul_integral_norm_resolvent_sq_eq (ν := ν) t hz hzw hw
  have hζ0 : (z + t * w).im ≠ 0 := fun h ↦ by simp [h] at hq
  rw [(hasDerivAt_resolventTransform_of_im_ne_zero hζ0).deriv, norm_mul, norm_real,
    Real.norm_eq_abs, abs_of_nonneg t.coe_nonneg]
  calc (t : ℝ) * ‖∫ x, resolvent (z + t * w) x ^ 2 ∂ν‖
      ≤ (t : ℝ) * ∫ x, ‖resolvent (z + t * w) x ^ 2‖ ∂ν :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) t.coe_nonneg
    _ = (t : ℝ) * ∫ x, ‖resolvent (z + t * w) x‖ ^ 2 ∂ν := by simp_rw [norm_pow]
    _ = 1 - z.im / (z + t * w).im := hb
    _ < 1 := by linarith

private lemma one_sub_mul_deriv_ne_zero_of_eq (t : ℝ≥0) {z w : ℂ}
    (hz : z.im ≠ 0) (hzw : 0 ≤ z.im * w.im)
    (hw : w = resolventTransform ν (z + t * w)) :
    1 - (t : ℂ) * deriv (resolventTransform ν) (z + t * w) ≠ 0 := by
  refine sub_ne_zero.2 fun h ↦ ?_
  have hlt := norm_mul_deriv_resolventTransform_lt_one_of_eq t hz hzw hw
  rw [← h, norm_one] at hlt
  exact lt_irrefl 1 hlt

private lemma differentiableOn_pasturAux (t : ℝ≥0) :
    DifferentiableOn ℂ (pasturAux ν t) {z : ℂ | 0 < z.im} := by
  intro z (hz : 0 < z.im)
  obtain ⟨hwim, hweq⟩ := pasturAux_spec (ν := ν) t hz
  have hζpos : 0 < (z + t * pasturAux ν t z).im := im_add_nnreal_mul_pos t hz hwim
  have hjac := one_sub_mul_deriv_ne_zero_of_eq t hz.ne' (mul_nonneg hz.le hwim) hweq
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
    have hζ : y ≤ (y * I + t * w).im := by simpa using le_im_add_nnreal_mul t (y * I) hwim
    have hζpos : 0 < (y * I + t * w).im := hy.trans_le hζ
    have hsub := norm_resolventTransform_add_nnreal_mul_sub_le (ν := ν) hζpos.ne' hz.ne'
    have hnorm_w : ‖w‖ ≤ y⁻¹ * ν.real univ := by simpa using norm_pasturAux_le (ν := ν) t hz
    rw [hweq, norm_mul, norm_mul, norm_real, Real.norm_of_nonneg hy.le, norm_I, mul_one]
    calc y * ‖resolventTransform ν (y * I + t * w) - resolventTransform ν (y * I)‖
        ≤ y * ((t : ℝ) * ‖w‖ / (|(y * I + t * w).im| * |(y * I : ℂ).im|) * ν.real univ) :=
          mul_le_mul_of_nonneg_left hsub hy.le
      _ ≤ y * ((t : ℝ) * (y⁻¹ * ν.real univ) / (y * y) * ν.real univ) := by
          have him1 : |(y * I + t * w).im| = (y * I + t * w).im := abs_of_pos hζpos
          have him2 : |(y * I : ℂ).im| = y := by simp [abs_of_pos hy]
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
  exists_isFiniteMeasure_measureReal_univ_eq_and_resolventTransform_eq
    (differentiableOn_pasturAux t) (fun _ hz ↦ (pasturAux_spec t hz).1)
    (tendsto_mul_I_mul_pasturAux t)

end PasturFixedPoint

namespace Measure

open Classical in
/-- **The Pastur measure** `ν.pastur t` of a Borel measure `ν` on `ℝ` at variance parameter
`t : ℝ≥0`. When `ν` is finite, it is the unique finite measure on `ℝ` whose resolvent transform
solves Pastur's self-consistent equation `m(z) = m_ν(z + t m(z))` off the real axis (by Biane
(1997), for a probability measure `ν` this corresponds to the additive free convolution with the
centred semicircle law of variance `t`; that identification is not formalized here). When `ν` is
not finite, `ν.pastur t` is `0`. -/
def pastur (ν : Measure ℝ) (t : ℝ≥0) : Measure ℝ :=
  if _ : IsFiniteMeasure ν then (exists_pasturMeasure ν t).choose else 0

open Classical in
private lemma pastur_spec (ν : Measure ℝ) [h : IsFiniteMeasure ν] (t : ℝ≥0) :
    IsFiniteMeasure (ν.pastur t) ∧ (ν.pastur t).real univ = ν.real univ ∧
      ∀ z : ℂ, 0 < z.im → pasturAux ν t z = resolventTransform (ν.pastur t) z := by
  simpa only [pastur, dite_eq_left h] using (exists_pasturMeasure ν t).choose_spec

open Classical in
/-- When `ν` is not a finite measure, `ν.pastur t` is `0`. -/
theorem pastur_of_not_isFiniteMeasure {ν : Measure ℝ} (hν : ¬ IsFiniteMeasure ν) (t : ℝ≥0) :
    ν.pastur t = 0 :=
  dite_eq_right hν

/-- `ν.pastur t` is always a finite measure. -/
instance isFiniteMeasure_pastur (ν : Measure ℝ) (t : ℝ≥0) : IsFiniteMeasure (ν.pastur t) := by
  by_cases h : IsFiniteMeasure ν
  · exact (pastur_spec ν t).1
  · rw [pastur_of_not_isFiniteMeasure h]
    infer_instance

/-- The real total mass of `ν.pastur t` agrees with that of `ν` for every measure `ν`. -/
@[simp]
theorem pastur_real_univ (ν : Measure ℝ) (t : ℝ≥0) :
    (ν.pastur t).real univ = ν.real univ := by
  by_cases h : IsFiniteMeasure ν
  · exact (pastur_spec ν t).2.1
  · simp [pastur_of_not_isFiniteMeasure h, measureReal_def, not_isFiniteMeasure_iff.mp h]

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
    resolventTransform (ν.pastur t) z = pasturAux ν t z :=
  ((Measure.pastur_spec ν t).2.2 z hz).symm

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
    0 < z.im * (z + t * resolventTransform (ν.pastur t) z).im :=
  im_mul_im_add_nnreal_mul_pos t hz (im_mul_im_resolventTransform_nonneg (ν.pastur t) z)

omit [IsFiniteMeasure ν] in
/-- Off the real axis, the shifted spectral parameter `z + t m_{ν.pastur t}(z)` stays off the real
axis. -/
theorem im_add_mul_resolventTransform_pastur_ne_zero (t : ℝ≥0) {z : ℂ} (hz : z.im ≠ 0) :
    (z + t * resolventTransform (ν.pastur t) z).im ≠ 0 :=
  right_ne_zero_of_mul (im_mul_im_add_mul_resolventTransform_pastur_pos (ν := ν) t hz).ne'

omit [IsFiniteMeasure ν] in
/-- The shifted spectral parameter `z + t m_{ν.pastur t}(z)` has imaginary part of magnitude at
least `|z.im|`. -/
theorem abs_im_le_abs_im_add_mul_resolventTransform_pastur (t : ℝ≥0) (z : ℂ) :
    |z.im| ≤ |(z + t * resolventTransform (ν.pastur t) z).im| :=
  abs_im_le_abs_im_add_nnreal_mul t (im_mul_im_resolventTransform_nonneg (ν.pastur t) z)

/-- **Strict contraction of the Pastur fixed-point derivative.** Off the real axis, at
`ζ = z + t m_{ν.pastur t}(z)`, the complex derivative satisfies `‖t m_ν'(ζ)‖ < 1`. -/
theorem norm_mul_deriv_resolventTransform_add_mul_resolventTransform_pastur_lt_one (t : ℝ≥0)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖(t : ℂ) * deriv (resolventTransform ν) (z + t * resolventTransform (ν.pastur t) z)‖ < 1 :=
  norm_mul_deriv_resolventTransform_lt_one_of_eq t hz
    (im_mul_im_resolventTransform_nonneg (ν.pastur t) z) (resolventTransform_pastur_eq t hz)

/-- The Pastur Jacobian `1 - t m_ν'(z + t m_{ν.pastur t}(z))` is nonzero off the real axis. -/
theorem one_sub_mul_deriv_resolventTransform_add_mul_resolventTransform_pastur_ne_zero (t : ℝ≥0)
    {z : ℂ} (hz : z.im ≠ 0) :
    1 - (t : ℂ) * deriv (resolventTransform ν)
      (z + t * resolventTransform (ν.pastur t) z) ≠ 0 :=
  one_sub_mul_deriv_ne_zero_of_eq t hz
    (im_mul_im_resolventTransform_nonneg (ν.pastur t) z) (resolventTransform_pastur_eq t hz)

/-- **Complex derivative of the Pastur resolvent transform.** Off the real axis,
`m_{ν.pastur t}'(z) = m_ν'(ζ) / (1 - t m_ν'(ζ))` where `ζ = z + t m_{ν.pastur t}(z)`. -/
theorem hasDerivAt_resolventTransform_pastur (t : ℝ≥0) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (resolventTransform (ν.pastur t))
      (deriv (resolventTransform ν) (z + t * resolventTransform (ν.pastur t) z) /
        (1 - (t : ℂ) * deriv (resolventTransform ν)
          (z + t * resolventTransform (ν.pastur t) z))) z := by
  have heq : ∀ᶠ w : ℂ in 𝓝 z, resolventTransform (ν.pastur t) w =
      resolventTransform ν (w + t * resolventTransform (ν.pastur t) w) := by
    filter_upwards [(isOpen_compl_singleton.preimage continuous_im).mem_nhds hz] with w hw
    exact resolventTransform_pastur_eq t hw
  exact hasDerivAt_of_pastur_eq t
    (hasDerivAt_resolventTransform_of_im_ne_zero hz).continuousAt heq
    (im_add_mul_resolventTransform_pastur_ne_zero t hz)
    (one_sub_mul_deriv_resolventTransform_add_mul_resolventTransform_pastur_ne_zero t hz)

end PasturAPI

namespace Measure

/-- **Measure-level characterization of the Pastur evolution.** Among finite measures on `ℝ`,
`ν.pastur t` is uniquely characterized by the Pastur self-consistent equation on the upper
half-plane. -/
theorem eq_pastur_iff {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {t : ℝ≥0} :
    μ = ν.pastur t ↔
      ∀ z : ℂ, 0 < z.im →
        resolventTransform μ z = resolventTransform ν (z + t * resolventTransform μ z) := by
  refine ⟨fun h z hz ↦ h ▸ resolventTransform_pastur_eq t hz.ne', fun h ↦ ?_⟩
  exact ext_of_resolventTransform fun z hz ↦
    (eq_resolventTransform_pastur_iff t hz).2 ⟨im_resolventTransform_nonneg hz.le, h z hz⟩

/-- The Pastur measure of the zero measure is zero. -/
@[simp]
theorem zero_pastur (t : ℝ≥0) : (0 : Measure ℝ).pastur t = 0 :=
  (eq_pastur_iff.2 fun _ _ ↦ by simp).symm

/-- At `t = 0`, the Pastur measure of a finite measure `ν` is `ν` itself. -/
@[simp]
theorem pastur_zero (ν : Measure ℝ) [IsFiniteMeasure ν] : ν.pastur 0 = ν :=
  (eq_pastur_iff.2 fun _ _ ↦ by simp).symm

/-- **Semigroup property of the Pastur evolution.** Evolving a measure `ν` by `s` and then by `t`
equals evolving `ν` by `s + t`. -/
@[simp]
theorem pastur_pastur (ν : Measure ℝ) (s t : ℝ≥0) :
    (ν.pastur s).pastur t = ν.pastur (s + t) := by
  by_cases hν : IsFiniteMeasure ν
  · apply ext_of_resolventTransform fun z hz ↦ ?_
    set w := resolventTransform (ν.pastur (s + t)) z
    obtain ⟨hwim, hweq⟩ := (eq_resolventTransform_pastur_iff (ν := ν) (s + t) hz).1 rfl
    have hz' : 0 < (z + t * w).im := im_add_nnreal_mul_pos t hz hwim
    have hstep1 : w = resolventTransform (ν.pastur s) (z + t * w) := by
      rw [eq_resolventTransform_pastur_iff s hz']
      refine ⟨hwim, ?_⟩
      convert hweq using 2
      push_cast
      ring
    exact ((eq_resolventTransform_pastur_iff (ν := ν.pastur s) t hz).2 ⟨hwim, hstep1⟩).symm
  · rw [pastur_of_not_isFiniteMeasure hν, pastur_of_not_isFiniteMeasure hν, zero_pastur]

/-- **Affine covariance of the Pastur evolution.** Pushing `ν.pastur t` forward by `x ↦ a + b * x`
evolves the pushed-forward measure at rescaled time `b² t` (including the degenerate slope `b = 0`).
-/
theorem map_affine_pastur (ν : Measure ℝ) (a b : ℝ) (t : ℝ≥0) :
    (ν.pastur t).map (fun x : ℝ ↦ a + b * x) =
      (ν.map (fun x : ℝ ↦ a + b * x)).pastur (Real.toNNReal (b ^ 2) * t) := by
  by_cases hν : IsFiniteMeasure ν
  · have : IsFiniteMeasure ((ν.pastur t).map (fun x : ℝ ↦ a + b * x)) :=
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
      rw [eq_resolventTransform_pastur_iff _ hz]
      refine ⟨im_resolventTransform_nonneg hz.le, ?_⟩
      have hw_eq : w = (b : ℂ)⁻¹ * resolventTransform (ν.pastur t) ((z - a) / b) :=
        resolventTransform_map_affine a b hb z
      have hz_div : ((z - a) / b).im ≠ 0 := by
        simpa [Complex.div_ofReal_im] using div_ne_zero hz.ne' hb
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
  · have hmap : ¬ IsFiniteMeasure (ν.map (fun x : ℝ ↦ a + b * x)) := by
      rw [not_isFiniteMeasure_iff, Measure.map_apply (by fun_prop) MeasurableSet.univ,
        preimage_univ]
      exact not_isFiniteMeasure_iff.mp hν
    simp [pastur_of_not_isFiniteMeasure hν, pastur_of_not_isFiniteMeasure hmap]

end Measure

namespace ProbabilityMeasure

/-- **The Pastur evolution on `ProbabilityMeasure ℝ`.** At parameter `t : ℝ≥0`, this bundles
`(ν : Measure ℝ).pastur t` as a probability measure (by Biane (1997), this corresponds to the
additive free convolution with the centred semicircle law of variance `t`; that identification is
not formalized here). -/
def pastur (ν : ProbabilityMeasure ℝ) (t : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨(ν : Measure ℝ).pastur t, inferInstance⟩

/-- Coercing `ν.pastur t` to `Measure ℝ` commutes with `Measure.pastur`. -/
@[simp, norm_cast]
theorem toMeasure_pastur (ν : ProbabilityMeasure ℝ) (t : ℝ≥0) :
    (ν.pastur t : Measure ℝ) = (ν : Measure ℝ).pastur t :=
  (rfl)

/-- Bundling a probability measure with `Measure.toProbabilityMeasure` commutes with `pastur`. -/
@[simp]
theorem pastur_toProbabilityMeasure (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℝ≥0) :
    ν.toProbabilityMeasure.pastur t = (ν.pastur t).toProbabilityMeasure :=
  toMeasure_injective (by simp)

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

/-- Affine covariance of the Pastur evolution on `ProbabilityMeasure ℝ`. -/
theorem map_affine_pastur (ν : ProbabilityMeasure ℝ) (a b : ℝ) (t : ℝ≥0) :
    (ν.pastur t).map (fun x : ℝ ↦ a + b * x) =
      (ν.map (fun x : ℝ ↦ a + b * x)).pastur (Real.toNNReal (b ^ 2) * t) :=
  toMeasure_injective (by simpa using Measure.map_affine_pastur (ν : Measure ℝ) a b t)

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
  have hζ₀pos : 0 < ζ₀.im := im_add_nnreal_mul_pos p.2 hz hwim
  have hfq_eq : fq = resolventTransform (q.1 : Measure ℝ) (z + q.2 * fq) :=
    resolventTransform_pastur_eq q.2 hz.ne'
  have hfq_im : 0 ≤ fq.im := im_resolventTransform_nonneg hz.le
  have hζq : z.im ≤ (z + q.2 * fq).im := le_im_add_nnreal_mul q.2 z hfq_im
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
  rw [toMeasure_pastur, resolventTransform_pastur_eq_pasturAux (ν := (p.1 : Measure ℝ)) p.2 hz]
  let f : ProbabilityMeasure ℝ × ℝ≥0 → ℂ :=
    fun q ↦ resolventTransform (q.1.pastur q.2 : Measure ℝ) z
  refine tendsto_pasturAux_of_ultrafilter (ν := (p.1 : Measure ℝ)) (f := f) p.2 hz
    (R := (z.im)⁻¹) ?_ ?_
  · -- Uniform half-disc bound for resolvent transforms of probability measures
    exact Eventually.of_forall fun q ↦
      ⟨im_resolventTransform_nonneg hz.le, by
        simpa [f, abs_of_pos hz] using
          norm_resolventTransform_le (μ := (q.1.pastur q.2 : Measure ℝ)) hz.ne'⟩
  · -- Every ultrafilter limit point solves the Pastur equation at `p`
    intro U hU w hwim hwlim
    let ζ₀ : ℂ := z + p.2 * w
    have hζ₀pos : 0 < ζ₀.im := im_add_nnreal_mul_pos p.2 hz hwim
    have hq2 : Tendsto (fun q : ProbabilityMeasure ℝ × ℝ≥0 ↦ (q.2 : ℂ)) U (𝓝 (p.2 : ℂ)) :=
      (continuous_ofReal.comp (NNReal.continuous_coe.comp continuous_snd)).tendsto p
        |>.mono_left hU
    -- Bound the Pastur residual using Lipschitz continuity in `ζ` and weak continuity in `ν`
    have h1 : Tendsto (fun q : ProbabilityMeasure ℝ × ℝ≥0 ↦
        ‖(q.2 : ℂ) * f q - (p.2 : ℂ) * w‖ / (z.im * ζ₀.im)) U (𝓝 0) := by
      simpa using ((hq2.mul hwlim).sub (tendsto_const_nhds (x := (p.2 : ℂ) * w))).norm.div_const
        (z.im * ζ₀.im)
    have h2 : Tendsto (fun q : ProbabilityMeasure ℝ × ℝ≥0 ↦
        ‖resolventTransform (q.1 : Measure ℝ) ζ₀ - resolventTransform (p.1 : Measure ℝ) ζ₀‖)
        U (𝓝 0) := by
      have hweak := tendsto_resolventTransform_of_tendsto
        (continuous_fst.tendsto p |>.mono_left hU) hζ₀pos.ne'
      simpa using
        (hweak.sub (tendsto_const_nhds (x := resolventTransform (p.1 : Measure ℝ) ζ₀))).norm
    have hdiff0 : Tendsto (fun q : ProbabilityMeasure ℝ × ℝ≥0 ↦
        f q - resolventTransform (p.1 : Measure ℝ) ζ₀) U (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.2 <| squeeze_zero (fun _ ↦ norm_nonneg _)
        (fun q ↦ norm_resolventTransform_pastur_sub_resolventTransform_le p q hz hwim)
        (by simpa only [f, ζ₀, add_zero] using h1.add h2)
    have hflim : Tendsto f U (𝓝 (resolventTransform (p.1 : Measure ℝ) ζ₀)) := by
      simpa using hdiff0.add (tendsto_const_nhds (x := resolventTransform (p.1 : Measure ℝ) ζ₀))
    exact tendsto_nhds_unique hwlim hflim

end ProbabilityMeasure

end MeasureTheory

end
