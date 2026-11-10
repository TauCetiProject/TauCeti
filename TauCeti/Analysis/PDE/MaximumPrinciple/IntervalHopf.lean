/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
public import TauCeti.Analysis.Sobolev.W1p.Zero
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import TauCeti.Analysis.Sobolev.W1p.VanishingBoundary

/-!
# Hopf's boundary-point lemma for weak supersolutions on an interval

On an interval `(x₀, x₁)` consider the divergence-form operator

`L u = (a u' + b u)' + c u' + d u`

in the sign convention of Gilbarg–Trudinger, Chapter 8: `u ∈ W^{1,2}(x₀, x₁)` is a *weak
supersolution*, `L u ≤ 0`, when

`∫ ((a u' + b u) w' - (c u' + d u) w) ≥ 0` for every `w ∈ W^{1,2}_0(x₀, x₁)` with `w ≥ 0`.

The coefficients are only assumed to satisfy `λ ≤ a ≤ Λ` with `λ > 0`, `|b| ≤ β`, `a` and `b`
measurable, `c ∈ L²` and `d ∈ L¹`. **Hopf's lemma**
(`TauCeti.PDE.exists_pos_mul_le_intervalRepresentativeL_of_integral_nonneg`) says that if the
continuous representative of such a `u` vanishes at `x₀` and is positive on `(x₀, x₁)`, then it
leaves `x₀` at a positive linear rate: `ε h ≤ u (x₀ + h)` for some `ε > 0` and all small `h > 0`.
In particular a right derivative of `u` at `x₀`, if it exists, is positive
(`TauCeti.PDE.pos_of_hasDerivWithinAt_intervalRepresentativeL_of_integral_nonneg`). No sign
condition is imposed on `b`, `c` or `d`. In contrast with the divergence-form Hopf lemma in higher
dimensions, which needs Hölder continuous `a` and `b`, no continuity of the coefficients is
needed: in one dimension the weighted flux is monotone up to an integrable error.

## The argument

Let `q = c / a` and let `m = exp (∫ q)` be the integrating factor. Testing the supersolution
inequality with `m φ` cancels the first-order term: for the weighted flux `Φ = m (a u' + b u)`
and `k = m (d - q b) u`,

`∫ k φ ≤ ∫ Φ φ'` for every absolutely continuous `φ ≥ 0` vanishing at `x₀` and `x₁`.

Taking for `φ` the difference of two ramps of width `δ` and letting `δ → 0` at two Lebesgue
points `s < t` of `Φ` gives `Φ t ≤ Φ s + ∫ y in s..t, |k y|`. So either `Φ s` exceeds the mass of
`|k|` on `(x₀, s)` at some Lebesgue point `s`, and then the flux, hence `u'`, is bounded below by
a positive constant near `x₀`; or `Φ y ≤ ∫ z in x₀..y, |k z|` almost everywhere. In the second case
`k` is controlled by `u`, so `u' ≤ C max_{[x₀, x₀ + h]} u` on `(x₀, x₀ + h)`, and integrating from
`x₀`, where `u` vanishes, forces `u = 0` on a short interval, contradicting its positivity.

## Main declarations

* `TauCeti.PDE.exists_pos_mul_le_intervalRepresentativeL_of_integral_nonneg`: **Hopf's lemma** for
  weak supersolutions on an interval, in difference-quotient form.
* `TauCeti.PDE.pos_of_hasDerivWithinAt_intervalRepresentativeL_of_integral_nonneg`: the derivative
  form.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 8.1 (weak supersolutions) and Lemma 3.4 (the classical Hopf lemma).
* D. Rosales, *Generalizing Hopf's boundary point lemma*, arXiv:1806.07003 (the divergence-form
  Hopf lemma for weak supersolutions).
-/

public section

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology

namespace TauCeti.PDE

variable {x₀ x₁ s t δ x : ℝ} {a b c d q Φ k : ℝ → ℝ}

/-- The integrating factor `t ↦ exp (∫ s in x₀..t, q s)`. -/
private noncomputable def integratingFactor (x₀ : ℝ) (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (∫ s in x₀..t, q s)

private theorem integratingFactor_pos (t : ℝ) : 0 < integratingFactor x₀ q t :=
  Real.exp_pos _

private theorem abs_intervalIntegral_le_integral_abs (hq : Integrable q) (t : ℝ) :
    |∫ s in x₀..t, q s| ≤ ∫ s, |q s| := by
  refine (intervalIntegral.norm_integral_le_integral_norm_uIoc (f := q)).trans ?_
  exact setIntegral_le_integral hq.norm (.of_forall fun _ ↦ norm_nonneg _)

private theorem integratingFactor_le (hq : Integrable q) (t : ℝ) :
    integratingFactor x₀ q t ≤ Real.exp (∫ s, |q s|) :=
  Real.exp_le_exp.2 (le_of_abs_le (abs_intervalIntegral_le_integral_abs hq t))

private theorem exp_neg_le_integratingFactor (hq : Integrable q) (t : ℝ) :
    Real.exp (-∫ s, |q s|) ≤ integratingFactor x₀ q t :=
  Real.exp_le_exp.2 (neg_le_of_abs_le (abs_intervalIntegral_le_integral_abs hq t))

private theorem continuous_integratingFactor (hq : Integrable q) :
    Continuous (integratingFactor x₀ q) :=
  Real.continuous_exp.comp
    (intervalIntegral.continuous_primitive (fun _ _ ↦ hq.intervalIntegrable) x₀)

private theorem ae_hasDerivAt_integratingFactor (hq : Integrable q) :
    ∀ᵐ t, HasDerivAt (integratingFactor x₀ q) (integratingFactor x₀ q t * q t) t := by
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hq.locallyIntegrable] with t ht
  exact (ht x₀).exp

private theorem absolutelyContinuousOnInterval_integratingFactor (hq : Integrable q)
    (x₁ : ℝ) : AbsolutelyContinuousOnInterval (integratingFactor x₀ q) x₀ x₁ := by
  set L := ∫ s, |q s|
  have hlip : LipschitzOnWith (Real.toNNReal (Real.exp L)) Real.exp (Icc (-L) L) := by
    refine (convex_Icc _ _).lipschitzOnWith_of_nnnorm_deriv_le
      (fun x _ ↦ Real.differentiableAt_exp) fun x hx ↦ ?_
    rw [Real.deriv_exp, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos x), Real.coe_toNNReal _ (Real.exp_pos L).le]
    exact Real.exp_le_exp.2 hx.2
  exact hlip.comp_absolutelyContinuousOnInterval
    (fun t _ ↦ abs_le.1 (abs_intervalIntegral_le_integral_abs hq t))
    (hq.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)

/-- Multiplying by the bounded integrating factor preserves `Lᵖ`. -/
private theorem memLp_integratingFactor_mul (hq : Integrable q) {μ : Measure ℝ}
    {p : ENNReal} {f : ℝ → ℝ} (hf : MemLp f p μ) :
    MemLp (fun y ↦ integratingFactor x₀ q y * f y) p μ := by
  refine hf.of_le_mul (c := Real.exp (∫ s, |q s|))
    ((continuous_integratingFactor hq).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (.of_forall fun y ↦ ?_)
  rw [norm_mul, Real.norm_eq_abs (integratingFactor x₀ q y),
    abs_of_pos (integratingFactor_pos y)]
  gcongr
  exact integratingFactor_le hq y

/-- A lower bound `σ > 0` for `m y F` gives the lower bound `σ exp (-∫ |q|)` for `F`. -/
private theorem mul_exp_neg_le_of_le_integratingFactor_mul (hq : Integrable q) {y σ F : ℝ}
    (hσ : 0 < σ) (h : σ ≤ integratingFactor x₀ q y * F) :
    σ * Real.exp (-∫ s, |q s|) ≤ F := by
  have hF : 0 < F := pos_of_mul_pos_right (hσ.trans_le h) (integratingFactor_pos y).le
  calc σ * Real.exp (-∫ s, |q s|) ≤ Real.exp (∫ s, |q s|) * F * Real.exp (-∫ s, |q s|) := by
        gcongr
        exact h.trans (mul_le_mul_of_nonneg_right (integratingFactor_le hq y) hF.le)
    _ = F := by rw [mul_comm, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- An upper bound `K ≥ 0` for `m y F` gives the upper bound `exp (∫ |q|) K` for `F`. -/
private theorem le_exp_mul_of_integratingFactor_mul_le (hq : Integrable q) {y K F : ℝ}
    (hK : 0 ≤ K) (h : integratingFactor x₀ q y * F ≤ K) :
    F ≤ Real.exp (∫ s, |q s|) * K := by
  rcases le_or_gt F 0 with hF | hF
  · exact hF.trans (by positivity)
  calc F = Real.exp (∫ s, |q s|) * (Real.exp (-∫ s, |q s|) * F) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (∫ s, |q s|) * K := by
        gcongr
        exact (mul_le_mul_of_nonneg_right (exp_neg_le_integratingFactor hq y) hF.le).trans h

/-- The ramp rising linearly from `0` at `s` to `1` at `s + δ`: the projection of `(x - s) / δ`
onto `[0, 1]`. -/
private noncomputable def ramp (s δ x : ℝ) : ℝ := projIcc 0 1 zero_le_one ((x - s) / δ)

private theorem ramp_nonneg : 0 ≤ ramp s δ x := (projIcc 0 1 zero_le_one _).2.1

private theorem ramp_le_one : ramp s δ x ≤ 1 := (projIcc 0 1 zero_le_one _).2.2

private theorem ramp_of_le (hδ : 0 < δ) (h : x ≤ s) : ramp s δ x = 0 := by
  rw [ramp, projIcc_of_le_left _ (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)]

private theorem ramp_of_ge (hδ : 0 < δ) (h : s + δ ≤ x) : ramp s δ x = 1 := by
  rw [ramp, projIcc_of_right_le _ (by rw [le_div_iff₀ hδ]; linarith)]

private theorem ramp_le_ramp (hδ : 0 < δ) (h : s ≤ t) : ramp t δ x ≤ ramp s δ x :=
  monotone_projIcc _ (div_le_div_of_nonneg_right (by linarith) hδ.le)

private theorem lipschitzWith_ramp (hδ : 0 < δ) :
    LipschitzWith (Real.toNNReal δ⁻¹) (ramp s δ) := by
  have hlin : LipschitzWith (Real.toNNReal δ⁻¹) fun x : ℝ ↦ (x - s) / δ :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.2 hδ.le), ← sub_div,
        sub_sub_sub_cancel_right, abs_div, abs_of_pos hδ, div_eq_inv_mul]
  have h := (LipschitzWith.subtype_val _).comp ((LipschitzWith.projIcc zero_le_one).comp hlin)
  rwa [one_mul, one_mul] at h

/-- Away from its two corners the ramp has derivative `δ⁻¹` on `(s, s + δ)` and `0` elsewhere. -/
private theorem hasDerivAt_ramp (hδ : 0 < δ) (hs : x ≠ s) (hsδ : x ≠ s + δ) :
    HasDerivAt (ramp s δ) ((Ioo s (s + δ)).indicator (fun _ ↦ δ⁻¹) x) x := by
  rcases lt_or_gt_of_ne hs with hxs | hxs
  · have hx : x ∉ Ioo s (s + δ) := fun h ↦ (lt_asymm hxs h.1).elim
    rw [indicator_of_notMem hx]
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hxs] with y hy using ramp_of_le hδ (le_of_lt hy)
  rcases lt_or_gt_of_ne hsδ with hxsδ | hxsδ
  · have hx : x ∈ Ioo s (s + δ) := ⟨hxs, hxsδ⟩
    rw [indicator_of_mem hx]
    have hlin : HasDerivAt (fun y ↦ (y - s) / δ) δ⁻¹ x := by
      simpa [one_div] using ((hasDerivAt_id x).sub_const s).div_const δ
    refine hlin.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hxs hxsδ] with y hy
    rw [ramp, projIcc_of_mem _ ⟨div_nonneg (by linarith [hy.1]) hδ.le,
      by rw [div_le_iff₀ hδ]; linarith [hy.2]⟩]
  · have hx : x ∉ Ioo s (s + δ) := fun h ↦ (lt_asymm hxsδ h.2).elim
    rw [indicator_of_notMem hx]
    refine (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hxsδ] with y hy using ramp_of_ge hδ (le_of_lt hy)

/-- Integrating against a constant multiple of the indicator of a subinterval. -/
private theorem setIntegral_mul_indicator_Ioo (hsub : Ioo s t ⊆ Ioo x₀ x₁) (r : ℝ) :
    ∫ y in Ioo x₀ x₁, Φ y * (Ioo s t).indicator (fun _ ↦ r) y = r * ∫ y in Ioo s t, Φ y := by
  have h : (fun y ↦ Φ y * (Ioo s t).indicator (fun _ ↦ r) y) =
      (Ioo s t).indicator (fun y ↦ r * Φ y) := by
    ext y
    by_cases hy : y ∈ Ioo s t <;> simp [hy, mul_comm]
  rw [h, integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.2 hsub, integral_const_mul]

private theorem ramp_sub_mem_Icc (hδ : 0 < δ) (h : s ≤ t) :
    (ramp s δ - ramp t δ) x ∈ Icc 0 1 := by
  have h1 : ramp s δ x ≤ 1 := ramp_le_one
  have h0 : 0 ≤ ramp t δ x := ramp_nonneg
  simp only [Pi.sub_apply, mem_Icc, sub_nonneg]
  exact ⟨ramp_le_ramp hδ h, by linarith⟩

private theorem ramp_sub_eq_zero (hδ : 0 < δ) (h : s ≤ t) (hx : x ∉ Ioo s (t + δ)) :
    (ramp s δ - ramp t δ) x = 0 := by
  rw [Pi.sub_apply, sub_eq_zero]
  rcases le_or_gt x s with hxs | hxs
  · rw [ramp_of_le hδ hxs, ramp_of_le hδ (hxs.trans h)]
  · have htx : t + δ ≤ x := not_lt.1 fun h' ↦ hx ⟨hxs, h'⟩
    rw [ramp_of_ge hδ (by linarith), ramp_of_ge hδ htx]

/-- The derivative of a difference of two ramps is the difference of two normalized indicators,
away from the four corners. -/
private theorem deriv_ramp_sub_ae (hδ : 0 < δ) :
    deriv (ramp s δ - ramp t δ) =ᵐ[volume] fun y ↦
      (Ioo s (s + δ)).indicator (fun _ ↦ δ⁻¹) y - (Ioo t (t + δ)).indicator (fun _ ↦ δ⁻¹) y := by
  have hne : ∀ z : ℝ, ∀ᵐ y : ℝ, y ≠ z := fun z ↦ by simp [ae_iff, measure_singleton]
  filter_upwards [hne s, hne (s + δ), hne t, hne (t + δ)] with y h1 h2 h3 h4
  exact ((hasDerivAt_ramp hδ h1 h2).sub (hasDerivAt_ramp hδ h3 h4)).deriv

private theorem memLp_deriv_ramp_sub (hδ : 0 < δ) :
    MemLp (deriv (ramp s δ - ramp t δ)) 2 (volume.restrict (Ioo x₀ x₁)) := by
  refine MemLp.ae_eq (EventuallyEq.symm (ae_restrict_of_ae (deriv_ramp_sub_ae hδ)))
    (MemLp.of_bound (((measurable_const.indicator measurableSet_Ioo).sub
      (measurable_const.indicator measurableSet_Ioo)).aestronglyMeasurable) (δ⁻¹ + δ⁻¹)
      (.of_forall fun y ↦ (norm_sub_le _ _).trans (add_le_add ?_ ?_))) <;>
  exact (norm_indicator_le_norm_self _ _).trans (by simp [abs_of_pos hδ])

/-- Testing `Φ` against the derivative of a difference of two ramps gives the difference of its
averages over `(s, s + δ)` and `(t, t + δ)`. -/
private theorem integral_mul_deriv_ramp_sub (hΦ : IntegrableOn Φ (Ioo x₀ x₁))
    (hs : x₀ ≤ s) (hδ : 0 < δ) (hst : s + δ ≤ t) (ht : t + δ ≤ x₁) :
    ∫ y in Ioo x₀ x₁, Φ y * deriv (ramp s δ - ramp t δ) y =
      (δ⁻¹ * ∫ y in Ioo s (s + δ), Φ y) - δ⁻¹ * ∫ y in Ioo t (t + δ), Φ y := by
  have hint : ∀ z, IntegrableOn (fun y ↦ Φ y * (Ioo z (z + δ)).indicator (fun _ ↦ δ⁻¹) y)
      (Ioo x₀ x₁) := fun z ↦ hΦ.mul_bdd
    ((measurable_const.indicator measurableSet_Ioo).aestronglyMeasurable) (c := δ⁻¹)
    (.of_forall fun y ↦ (norm_indicator_le_norm_self _ _).trans (by simp [abs_of_pos hδ]))
  calc ∫ y in Ioo x₀ x₁, Φ y * deriv (ramp s δ - ramp t δ) y
      = ∫ y in Ioo x₀ x₁, (Φ y * (Ioo s (s + δ)).indicator (fun _ ↦ δ⁻¹) y -
          Φ y * (Ioo t (t + δ)).indicator (fun _ ↦ δ⁻¹) y) :=
        integral_congr_ae ((ae_restrict_of_ae (deriv_ramp_sub_ae (s := s) (t := t) hδ)).mono
          fun y hy ↦ by simp only [hy, mul_sub])
    _ = (δ⁻¹ * ∫ y in Ioo s (s + δ), Φ y) - δ⁻¹ * ∫ y in Ioo t (t + δ), Φ y := by
        rw [integral_sub (hint s) (hint t),
          setIntegral_mul_indicator_Ioo (Ioo_subset_Ioo hs (by linarith)),
          setIntegral_mul_indicator_Ioo (Ioo_subset_Ioo (by linarith) ht)]

/-- Since `0 ≤ ramp s δ - ramp t δ ≤ 1` vanishes off `(s, t + δ)`, testing `k` against it costs
at most the mass of `|k|` there. -/
private theorem neg_setIntegral_abs_le_integral_mul_ramp_sub (hk : IntegrableOn k (Ioo x₀ x₁))
    (hs : x₀ ≤ s) (hδ : 0 < δ) (hst : s ≤ t) (ht : t + δ ≤ x₁) :
    -∫ y in Ioo s (t + δ), |k y| ≤ ∫ y in Ioo x₀ x₁, k y * (ramp s δ - ramp t δ) y := by
  have hsub : Ioo s (t + δ) ⊆ Ioo x₀ x₁ := Ioo_subset_Ioo hs ht
  have hneg : ∫ y in Ioo x₀ x₁, -(Ioo s (t + δ)).indicator (fun y ↦ |k y|) y =
      -∫ y in Ioo s (t + δ), |k y| := by
    rw [integral_neg, integral_indicator measurableSet_Ioo,
      Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2 hsub]
  rw [← hneg]
  refine integral_mono ((IntegrableOn.integrable_indicator (f := fun y ↦ |k y|)
    (hk.mono_set hsub).abs measurableSet_Ioo).integrableOn.neg)
    (hk.mul_bdd (((lipschitzWith_ramp hδ).continuous.sub
      (lipschitzWith_ramp hδ).continuous).aestronglyMeasurable) (c := 1)
      (.of_forall fun y ↦ by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [(ramp_sub_mem_Icc (x := y) hδ hst).1],
          (ramp_sub_mem_Icc (x := y) hδ hst).2⟩)) fun y ↦ ?_
  have h01 := ramp_sub_mem_Icc (x := y) hδ hst
  by_cases hy : y ∈ Ioo s (t + δ)
  · rw [indicator_of_mem hy]
    nlinarith [mul_le_mul_of_nonneg_right (neg_abs_le (k y)) h01.1,
      mul_le_mul_of_nonneg_left h01.2 (abs_nonneg (k y))]
  · rw [indicator_of_notMem hy, neg_zero, ramp_sub_eq_zero hδ hst hy, mul_zero]

/-- The test inequality for the difference of two ramps: averages of `Φ` over `(t, t + δ)`
exceed those over `(s, s + δ)` by at most the mass of `|k|` in between. -/
private theorem ramp_average_le
    (hΦ : IntegrableOn Φ (Ioo x₀ x₁)) (hk : IntegrableOn k (Ioo x₀ x₁))
    (hKI : ∀ φ : ℝ → ℝ, AbsolutelyContinuousOnInterval φ x₀ x₁ →
      MemLp (deriv φ) 2 (volume.restrict (Ioo x₀ x₁)) → φ x₀ = 0 → φ x₁ = 0 →
      (∀ y ∈ Ioo x₀ x₁, 0 ≤ φ y) →
      ∫ y in Ioo x₀ x₁, k y * φ y ≤ ∫ y in Ioo x₀ x₁, Φ y * deriv φ y)
    (hs : x₀ ≤ s) (hδ : 0 < δ) (hst : s + δ ≤ t) (ht : t + δ ≤ x₁) :
    δ⁻¹ * ∫ y in Ioo t (t + δ), Φ y ≤
      (δ⁻¹ * ∫ y in Ioo s (s + δ), Φ y) + ∫ y in Ioo s (t + δ), |k y| := by
  have hst' : s ≤ t := by linarith
  have h := hKI (ramp s δ - ramp t δ)
    (((lipschitzWith_ramp hδ).lipschitzOnWith.absolutelyContinuousOnInterval).sub
      ((lipschitzWith_ramp hδ).lipschitzOnWith.absolutelyContinuousOnInterval))
    (memLp_deriv_ramp_sub hδ) (ramp_sub_eq_zero hδ hst' fun h ↦ (not_lt.2 hs) h.1)
    (ramp_sub_eq_zero hδ hst' fun h ↦ (not_lt.2 ht) h.2) fun y _ ↦ (ramp_sub_mem_Icc hδ hst').1
  rw [integral_mul_deriv_ramp_sub hΦ hs hδ hst ht] at h
  linarith [neg_setIntegral_abs_le_integral_mul_ramp_sub hk hs hδ hst' ht]

/-- A set integral over a subinterval as a difference of primitives based at `x₀`. -/
private theorem setIntegral_Ioo_eq_sub {f : ℝ → ℝ} (hf : IntegrableOn f (Ioo x₀ x₁))
    {y₁ y₂ : ℝ} (h₀ : x₀ ≤ y₁) (h₁₂ : y₁ ≤ y₂) (h₂ : y₂ ≤ x₁) :
    ∫ z in Ioo y₁ y₂, f z = (∫ z in x₀..y₂, f z) - ∫ z in x₀..y₁, f z := by
  have hi : ∀ y, x₀ ≤ y → y ≤ x₁ → IntervalIntegrable f volume x₀ y := fun y hy hy' ↦
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hy).2 (hf.mono_set (Ioo_subset_Ioo_right hy'))
  rw [intervalIntegral.integral_interval_sub_left (hi y₂ (h₀.trans h₁₂) h₂)
    (hi y₁ h₀ (h₁₂.trans h₂)), intervalIntegral.integral_of_le h₁₂, integral_Ioc_eq_integral_Ioo]

/-- **The flux is almost decreasing.** At two Lebesgue points `s < t` of `Φ`, the inequality of
`ramp_average_le` passes to the limit: `Φ t ≤ Φ s + ∫ y in s..t, |k y|`. -/
private theorem le_add_intervalIntegral_abs
    (hΦ : IntegrableOn Φ (Ioo x₀ x₁)) (hk : IntegrableOn k (Ioo x₀ x₁))
    (hKI : ∀ φ : ℝ → ℝ, AbsolutelyContinuousOnInterval φ x₀ x₁ →
      MemLp (deriv φ) 2 (volume.restrict (Ioo x₀ x₁)) → φ x₀ = 0 → φ x₁ = 0 →
      (∀ y ∈ Ioo x₀ x₁, 0 ≤ φ y) →
      ∫ y in Ioo x₀ x₁, k y * φ y ≤ ∫ y in Ioo x₀ x₁, Φ y * deriv φ y)
    (hs : s ∈ Ioo x₀ x₁) (ht : t ∈ Ioo x₀ x₁) (hst : s < t)
    (hPs : HasDerivAt (fun y ↦ ∫ z in x₀..y, Φ z) (Φ s) s)
    (hPt : HasDerivAt (fun y ↦ ∫ z in x₀..y, Φ z) (Φ t) t) :
    Φ t ≤ Φ s + ∫ y in s..t, |k y| := by
  set P : ℝ → ℝ := fun y ↦ ∫ z in x₀..y, Φ z
  set K : ℝ → ℝ := fun y ↦ ∫ z in x₀..y, |k z|
  have hka : IntegrableOn (fun y ↦ |k y|) (Ioo x₀ x₁) := hk.abs
  have hx : x₀ < x₁ := hs.1.trans hs.2
  have hKon : ContinuousOn K (Icc x₀ x₁) := by
    have h := intervalIntegral.continuousOn_primitive_interval (a := x₀) (b := x₁)
      (f := fun y ↦ |k y|) (μ := volume) (by
        rw [uIcc_of_le hx.le, integrableOn_Icc_iff_integrableOn_Ioo]
        exact hka)
    rwa [uIcc_of_le hx.le] at h
  have hKcont : ContinuousAt K t := hKon.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hev : ∀ᶠ δ in 𝓝[>] 0,
      δ⁻¹ * (P (t + δ) - P t) ≤ δ⁻¹ * (P (s + δ) - P s) + (K (t + δ) - K s) := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min (sub_pos.2 hst) (sub_pos.2 ht.2))] with δ hδ
    have hδst : s + δ ≤ t := by linarith [hδ.2.trans_le (min_le_left _ _)]
    have hδt : t + δ ≤ x₁ := by linarith [hδ.2.trans_le (min_le_right _ _)]
    have h := ramp_average_le hΦ hk hKI hs.1.le hδ.1 hδst hδt
    rwa [setIntegral_Ioo_eq_sub hΦ (hs.1.trans hst).le (by linarith [hδ.1]) hδt,
      setIntegral_Ioo_eq_sub hΦ hs.1.le (by linarith [hδ.1]) (by linarith),
      setIntegral_Ioo_eq_sub hka hs.1.le (by linarith [hδ.1]) hδt] at h
  have hlimL : Tendsto (fun δ ↦ δ⁻¹ * (P (t + δ) - P t)) (𝓝[>] 0) (𝓝 (Φ t)) := by
    simpa only [smul_eq_mul] using hPt.tendsto_slope_zero_right
  have hlimR : Tendsto (fun δ ↦ δ⁻¹ * (P (s + δ) - P s) + (K (t + δ) - K s)) (𝓝[>] 0)
      (𝓝 (Φ s + (K t - K s))) := by
    have hs' : Tendsto (fun δ ↦ δ⁻¹ * (P (s + δ) - P s)) (𝓝[>] 0) (𝓝 (Φ s)) := by
      simpa only [smul_eq_mul] using hPs.tendsto_slope_zero_right
    refine hs'.add ((hKcont.tendsto.comp ?_).sub_const _)
    have : Tendsto (fun δ : ℝ ↦ t + δ) (𝓝 0) (𝓝 t) := by
      simpa using (continuous_const_add t).tendsto 0
    exact this.mono_left nhdsWithin_le_nhds
  have h := le_of_tendsto_of_tendsto hlimL hlimR hev
  have hKst : K t - K s = ∫ y in s..t, |k y| := by
    rw [intervalIntegral.integral_of_le hst.le, integral_Ioc_eq_integral_Ioo,
      setIntegral_Ioo_eq_sub hka hs.1.le hst.le ht.2.le]
  linarith

/-- Below a Lebesgue point `s` of `Φ`, the function `Φ` stays almost everywhere above
`Φ s - ∫ y in x₀..s, |k y|`. -/
private theorem ae_sub_le_of_hasDerivAt
    (hΦ : IntegrableOn Φ (Ioo x₀ x₁)) (hk : IntegrableOn k (Ioo x₀ x₁))
    (hKI : ∀ φ : ℝ → ℝ, AbsolutelyContinuousOnInterval φ x₀ x₁ →
      MemLp (deriv φ) 2 (volume.restrict (Ioo x₀ x₁)) → φ x₀ = 0 → φ x₁ = 0 →
      (∀ y ∈ Ioo x₀ x₁, 0 ≤ φ y) →
      ∫ y in Ioo x₀ x₁, k y * φ y ≤ ∫ y in Ioo x₀ x₁, Φ y * deriv φ y)
    (hE : ∀ᵐ y, y ∈ Ioo x₀ x₁ → HasDerivAt (fun y ↦ ∫ z in x₀..y, Φ z) (Φ y) y)
    (hs : s ∈ Ioo x₀ x₁) (hPs : HasDerivAt (fun y ↦ ∫ z in x₀..y, Φ z) (Φ s) s) :
    ∀ᵐ y, y ∈ Ioo x₀ s → Φ s - ∫ z in x₀..s, |k z| ≤ Φ y := by
  filter_upwards [hE] with y hy hys
  have hyI : y ∈ Ioo x₀ x₁ := ⟨hys.1, hys.2.trans hs.2⟩
  have h := le_add_intervalIntegral_abs hΦ hk hKI hyI hs hys.2 (hy hyI) hPs
  have hmono : ∫ z in y..s, |k z| ≤ ∫ z in x₀..s, |k z| :=
    intervalIntegral.integral_mono_interval hys.1.le hys.2.le le_rfl
      (.of_forall fun _ ↦ abs_nonneg _)
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hs.1.le).2
        ((hk.mono_set (Ioo_subset_Ioo_right hs.2.le)).abs))
  linarith

/-- An absolutely continuous `ψ ≥ 0` vanishing at both endpoints, with derivative in `L²`,
is an admissible test function in the weak supersolution inequality. -/
private theorem integral_nonneg_of_absolutelyContinuousOnInterval (hx : x₀ < x₁)
    {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2}
    (hsuper : ∀ w : W1p0 volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2,
      (∀ᵐ x ∂volume.restrict (Ioo x₀ x₁),
        0 ≤ W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) x) →
      0 ≤ ∫ x in Ioo x₀ x₁, ((a x * W1p.gradient u x + b x * W1p.value u x) *
          W1p.gradient (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) x -
        (c x * W1p.gradient u x + d x * W1p.value u x) *
          W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) x))
    {ψ : ℝ → ℝ} (hψ : AbsolutelyContinuousOnInterval ψ x₀ x₁)
    (hdψ : MemLp (deriv ψ) 2 (volume.restrict (Ioo x₀ x₁))) (hψ₀ : ψ x₀ = 0) (hψ₁ : ψ x₁ = 0)
    (hψnn : ∀ t ∈ Ioo x₀ x₁, 0 ≤ ψ t) :
    0 ≤ ∫ x in Ioo x₀ x₁,
      ((a x * W1p.gradient u x + b x * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le x)) *
          deriv ψ x -
        (c x * W1p.gradient u x + d x * W1p.intervalRepresentativeL hx u
          (projIcc x₀ x₁ hx.le x)) * ψ x) := by
  obtain ⟨w, hwv, hwg⟩ := hψ.exists_w1p_value_gradient_ae_eq hdψ
  have hw0 : w ∈ w1p0Submodule volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2 := by
    refine W1p.mem_w1p0Submodule_of_continuousOn_closure (by norm_num)
      (by simpa using Metric.isBounded_Ioo x₀ x₁) ?_ ?_ hwv
    · simpa [closure_Ioo hx.ne, uIcc_of_le hx.le] using hψ.continuousOn
    · intro t ht
      simp only [Opens.coe_mk, frontier_Ioo hx, mem_insert_iff, mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      exacts [hψ₀, hψ₁]
  have h := hsuper ⟨w, hw0⟩ (by
    filter_upwards [hwv, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    simpa [ht] using hψnn t hmem)
  refine h.trans_eq (integral_congr_ae ?_)
  filter_upwards [hwv, hwg, W1p.value_ae_eq_intervalRepresentativeL hx u] with t h1 h2 h3
  rw [h1, h2, h3]

/-- The product rule for the integrating factor times an absolutely continuous function. -/
private theorem deriv_integratingFactor_mul_ae (hx : x₀ < x₁) (hq : Integrable q) {φ : ℝ → ℝ}
    (hφ : AbsolutelyContinuousOnInterval φ x₀ x₁) :
    deriv (integratingFactor x₀ q * φ) =ᵐ[volume.restrict (Ioo x₀ x₁)] fun y ↦
      integratingFactor x₀ q y * q y * φ y + integratingFactor x₀ q y * deriv φ y := by
  filter_upwards [ae_restrict_of_ae (ae_hasDerivAt_integratingFactor (x₀ := x₀) hq),
    ae_restrict_of_ae hφ.ae_differentiableAt, ae_restrict_mem measurableSet_Ioo] with y hm hd hy
  have hd' := (hd (by rw [uIcc_of_le hx.le]; exact Ioo_subset_Icc_self hy)).hasDerivAt
  rw [(hm.mul hd').deriv]

/-- The integrating factor times an absolutely continuous function with `L²` derivative again
has `L²` derivative, given `q ∈ L²`. -/
private theorem memLp_deriv_integratingFactor_mul (hx : x₀ < x₁) (hq : Integrable q)
    (hq2 : MemLp q 2 (volume.restrict (Ioo x₀ x₁))) {φ : ℝ → ℝ}
    (hφ : AbsolutelyContinuousOnInterval φ x₀ x₁)
    (hdφ : MemLp (deriv φ) 2 (volume.restrict (Ioo x₀ x₁))) :
    MemLp (deriv (integratingFactor x₀ q * φ)) 2 (volume.restrict (Ioo x₀ x₁)) := by
  have hφc : ContinuousOn φ (Icc x₀ x₁) := by
    simpa [uIcc_of_le hx.le] using hφ.continuousOn
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hφc
  have h1 : MemLp (fun y ↦ q y * φ y) 2 (volume.restrict (Ioo x₀ x₁)) := by
    refine hq2.of_le_mul (c := B) (hq2.aestronglyMeasurable.mul
      ((hφc.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo))
      ((ae_restrict_mem measurableSet_Ioo).mono fun y hy ↦ ?_)
    rw [norm_mul, mul_comm]
    gcongr
    exact hB y (Ioo_subset_Icc_self hy)
  refine ((memLp_integratingFactor_mul (x₀ := x₀) hq h1).add
    (memLp_integratingFactor_mul (x₀ := x₀) hq hdφ)).ae_eq ?_
  filter_upwards [deriv_integratingFactor_mul_ae hx hq hφ] with y hy
  rw [hy, Pi.add_apply, mul_assoc]

/-- **Testing with the integrating factor.** Write `F = a u' + b u` for the flux and
`m = exp (∫ q)` with `q a = c` on the interval. Testing the supersolution inequality with `m φ`
removes the first-order term: `∫ m (d - q b) u φ ≤ ∫ m F φ'` for every admissible `φ ≥ 0`. -/
private theorem integral_mul_le_integral_mul_deriv (hx : x₀ < x₁)
    {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2}
    (hsuper : ∀ w : W1p0 volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2,
      (∀ᵐ x ∂volume.restrict (Ioo x₀ x₁),
        0 ≤ W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) x) →
      0 ≤ ∫ x in Ioo x₀ x₁, ((a x * W1p.gradient u x + b x * W1p.value u x) *
          W1p.gradient (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) x -
        (c x * W1p.gradient u x + d x * W1p.value u x) *
          W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) x))
    (hq : Integrable q) (hq2 : MemLp q 2 (volume.restrict (Ioo x₀ x₁)))
    (hqa : ∀ y ∈ Ioo x₀ x₁, q y * a y = c y)
    (hF : MemLp (fun y ↦ a y * W1p.gradient u y +
      b y * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)) 2
      (volume.restrict (Ioo x₀ x₁)))
    (hk : Integrable (fun y ↦ (d y - q y * b y) *
      W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)) (volume.restrict (Ioo x₀ x₁)))
    {φ : ℝ → ℝ} (hφ : AbsolutelyContinuousOnInterval φ x₀ x₁)
    (hdφ : MemLp (deriv φ) 2 (volume.restrict (Ioo x₀ x₁))) (hφ₀ : φ x₀ = 0) (hφ₁ : φ x₁ = 0)
    (hφnn : ∀ y ∈ Ioo x₀ x₁, 0 ≤ φ y) :
    ∫ y in Ioo x₀ x₁, integratingFactor x₀ q y * ((d y - q y * b y) *
        W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)) * φ y ≤
      ∫ y in Ioo x₀ x₁, integratingFactor x₀ q y * (a y * W1p.gradient u y +
        b y * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)) * deriv φ y := by
  set m := integratingFactor x₀ q
  set v : ℝ → ℝ := fun y ↦ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)
  have hφc : ContinuousOn φ (Icc x₀ x₁) := by
    simpa [uIcc_of_le hx.le] using hφ.continuousOn
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hφc
  have hφm : AEStronglyMeasurable φ (volume.restrict (Ioo x₀ x₁)) :=
    (hφc.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  set ψ : ℝ → ℝ := m * φ
  have hdψ := deriv_integratingFactor_mul_ae hx hq hφ
  have h := integral_nonneg_of_absolutelyContinuousOnInterval hx hsuper
    ((absolutelyContinuousOnInterval_integratingFactor hq x₁).mul hφ)
    (memLp_deriv_integratingFactor_mul hx hq hq2 hφ hdφ)
    (by simp [hφ₀]) (by simp [hφ₁])
    (fun y hy ↦ mul_nonneg (integratingFactor_pos y).le (hφnn y hy))
  have hcongr : (fun y ↦ (a y * W1p.gradient u y + b y * v y) * deriv ψ y -
      (c y * W1p.gradient u y + d y * v y) * ψ y) =ᵐ[volume.restrict (Ioo x₀ x₁)]
      fun y ↦ m y * (a y * W1p.gradient u y + b y * v y) * deriv φ y -
        m y * ((d y - q y * b y) * v y) * φ y := by
    filter_upwards [hdψ, ae_restrict_mem measurableSet_Ioo] with y hd hy
    rw [hd, ← hqa y hy]
    simp only [ψ, Pi.mul_apply]
    ring
  have hmF : MemLp (fun y ↦ m y * (a y * W1p.gradient u y + b y * v y)) 2
      (volume.restrict (Ioo x₀ x₁)) := memLp_integratingFactor_mul hq hF
  have i1 : Integrable (fun y ↦ m y * (a y * W1p.gradient u y + b y * v y) * deriv φ y)
      (volume.restrict (Ioo x₀ x₁)) := hmF.integrable_mul hdφ
  have i2 : Integrable (fun y ↦ m y * ((d y - q y * b y) * v y) * φ y)
      (volume.restrict (Ioo x₀ x₁)) :=
    ((memLp_integratingFactor_mul hq (memLp_one_iff_integrable.2 hk)).integrable le_rfl).mul_bdd
      hφm ((ae_restrict_mem measurableSet_Ioo).mono fun y hy ↦ hB y (Ioo_subset_Icc_self hy))
  rw [integral_congr_ae hcongr, integral_sub i1 i2] at h
  linarith

/-- The fundamental theorem of calculus for the continuous representative, read from `x₀`. -/
private theorem intervalRepresentativeL_eq_integral (hx : x₀ < x₁)
    (u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) {y : ℝ} (hy : y ∈ Icc x₀ x₁) :
    W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y) =
      W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le x₀) +
        ∫ r in x₀..y, W1p.gradient u r := by
  rw [W1p.integral_gradient_eq_intervalRepresentativeL_sub hx u ⟨x₀, left_mem_Icc.2 hx.le⟩
    ⟨y, hy⟩, projIcc_of_mem hx.le hy, projIcc_of_mem hx.le (left_mem_Icc.2 hx.le)]
  ring

private theorem intervalIntegrable_gradient
    (u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) {y : ℝ} (hy : y ∈ Icc x₀ x₁) :
    IntervalIntegrable (fun r ↦ W1p.gradient u r) volume x₀ y := by
  have : IsFiniteMeasure (volume.restrict ((⟨Ioo x₀ x₁, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) :=
    Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  have hg : IntegrableOn (fun r ↦ W1p.gradient u r) (Ioo x₀ x₁) :=
    (Lp.memLp (W1p.gradient u)).integrable (by norm_num)
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hy.1).2
    (hg.mono_set (Ioo_subset_Ioo_right hy.2))

/-- **Positive flux gives linear growth.** If the flux `a u' + b u` is bounded below by `σ > 0`
near `x₀`, where `u` vanishes and `a ≤ Λ`, then `u` grows at least linearly from `x₀`. -/
private theorem exists_pos_mul_le_of_le_flux (hx : x₀ < x₁)
    (u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) {Λ β σ s : ℝ}
    (ha : ∀ y ∈ Ioo x₀ x₁, 0 < a y) (haΛ : ∀ y ∈ Ioo x₀ x₁, a y ≤ Λ)
    (hb : ∀ y ∈ Ioo x₀ x₁, |b y| ≤ β) (hσ : 0 < σ) (hs : s ∈ Ioo x₀ x₁)
    (hu₀ : W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le x₀) = 0)
    (hlow : ∀ᵐ y, y ∈ Ioo x₀ s →
      σ ≤ a y * W1p.gradient u y + b y * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)) :
    ∃ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo 0 δ,
      ε * h ≤ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le (x₀ + h)) := by
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hb s hs)
  have hΛ : 0 < Λ := (ha s hs).trans_le (haΛ s hs)
  have hvc : Continuous fun y ↦ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y) :=
    (W1p.intervalRepresentativeL hx u).continuous.comp continuous_projIcc
  -- Near `x₀` the term `b u` is at most `σ / 2`.
  obtain ⟨η, hη, hvη⟩ := Metric.continuousAt_iff.1 hvc.continuousAt (σ / (2 * (β + 1)))
    (by positivity)
  refine ⟨σ / (2 * Λ), by positivity, min (s - x₀) η, lt_min (sub_pos.2 hs.1) hη,
    fun h hh ↦ ?_⟩
  have hhs : x₀ + h < s := by linarith [hh.2.trans_le (min_le_left _ _)]
  have hgrad : ∀ᵐ y, y ∈ Ioo x₀ (x₀ + h) → σ / (2 * Λ) ≤ W1p.gradient u y := by
    filter_upwards [hlow] with y hy hyI
    have hyI' : y ∈ Ioo x₀ x₁ := ⟨hyI.1, hyI.2.trans (hhs.trans hs.2)⟩
    have hvy : |W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)| <
        σ / (2 * (β + 1)) := by
      have := hvη (x := y) (by
        rw [Real.dist_eq, abs_of_pos (sub_pos.2 hyI.1)]
        linarith [hyI.2, hh.2.trans_le (min_le_right _ _)])
      rwa [Real.dist_eq, hu₀, sub_zero] at this
    have hbv : |b y * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)| ≤ σ / 2 := by
      rw [abs_mul]
      calc |b y| * |W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)| ≤
          β * (σ / (2 * (β + 1))) :=
            mul_le_mul (hb y hyI') hvy.le (abs_nonneg _) hβ
        _ ≤ σ / 2 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    have hag : σ / 2 ≤ a y * W1p.gradient u y := by
      have := hy ⟨hyI.1, hyI.2.trans hhs⟩
      linarith [le_abs_self (b y * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y))]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [haΛ y hyI', ha y hyI']
  have hmem : x₀ + h ∈ Icc x₀ x₁ := ⟨by linarith [hh.1], by linarith [hs.2]⟩
  rw [intervalRepresentativeL_eq_integral hx u hmem, hu₀, zero_add]
  have hle := intervalIntegral.integral_mono_ae_restrict (le_add_of_nonneg_right hh.1.le)
    intervalIntegrable_const (intervalIntegrable_gradient u hmem)
    (f := fun _ ↦ σ / (2 * Λ)) (by
      have hne : ∀ᵐ y : ℝ, y ≠ x₀ := by simp [ae_iff, measure_singleton]
      have hne' : ∀ᵐ y : ℝ, y ≠ x₀ + h := by simp [ae_iff, measure_singleton]
      filter_upwards [ae_restrict_of_ae hgrad, ae_restrict_of_ae hne, ae_restrict_of_ae hne',
        ae_restrict_mem measurableSet_Icc] with y hy h1 h2 h3
      exact hy ⟨lt_of_le_of_ne h3.1 (Ne.symm h1), lt_of_le_of_ne h3.2 h2⟩)
  rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at hle
  linarith

/-- **A flux controlled by the solution forces it to vanish.** Suppose that `u` vanishes at `x₀`,
that `a ≥ λ > 0` and `|b| ≤ β`, and that on each short interval `(x₀, x₀ + h)` the flux
`a u' + b u` is at most `C U` for every bound `U ≥ 0` of `u` on `[x₀, x₀ + h]`. Then `u` cannot
be positive on the whole interval. -/
private theorem not_forall_pos_of_flux_le (hx : x₀ < x₁)
    (u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) {lam β C : ℝ} (hlam : 0 < lam)
    (ha : ∀ y ∈ Ioo x₀ x₁, lam ≤ a y) (hb : ∀ y ∈ Ioo x₀ x₁, |b y| ≤ β) (hC : 0 ≤ C)
    (hu₀ : W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le x₀) = 0)
    (hup : ∀ h, 0 < h → h < x₁ - x₀ → ∀ U, 0 ≤ U →
      (∀ y ∈ Icc x₀ (x₀ + h), W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y) ≤ U) →
      ∀ᵐ y, y ∈ Ioo x₀ (x₀ + h) →
        a y * W1p.gradient u y + b y * W1p.intervalRepresentativeL hx u
          (projIcc x₀ x₁ hx.le y) ≤ C * U) :
    ¬∀ t ∈ Ioo x₀ x₁, 0 < W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t) := by
  intro hpos
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hb ((x₀ + x₁) / 2) ⟨by linarith, by linarith⟩)
  have hvc : Continuous fun y ↦ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y) :=
    (W1p.intervalRepresentativeL hx u).continuous.comp continuous_projIcc
  -- A short interval on which the growth allowed by the flux bound is at most one half.
  set h := min ((x₁ - x₀) / 2) (lam / (2 * (C + β + 1)))
  have hh : 0 < h := lt_min (by linarith) (by positivity)
  have hh₁ : h < x₁ - x₀ := (min_le_left _ _).trans_lt (by linarith)
  have hhC : h * ((C + β) / lam) ≤ 1 / 2 := by
    have : h ≤ lam / (2 * (C + β + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    rw [mul_div_assoc', div_le_iff₀ hlam]
    nlinarith
  -- `U` is the maximum of `u` on `[x₀, x₀ + h]`, attained at `τ`.
  obtain ⟨τ, hτ, hτmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (by linarith))
    (hvc.continuousOn (s := Icc x₀ (x₀ + h)))
  set U := W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le τ)
  have hUpos : 0 < U :=
    (hpos (x₀ + h) ⟨by linarith, by linarith⟩).trans_le (hτmax ⟨by linarith, le_rfl⟩)
  have hgrad : ∀ᵐ y, y ∈ Ioo x₀ (x₀ + h) → W1p.gradient u y ≤ (C + β) * U / lam := by
    filter_upwards [hup h hh hh₁ U hUpos.le fun y hy ↦ hτmax hy] with y hy hyI
    have hyI' : y ∈ Ioo x₀ x₁ := ⟨hyI.1, hyI.2.trans (by linarith)⟩
    have hvy := hpos y hyI'
    have hvU : W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y) ≤ U :=
      hτmax (Ioo_subset_Icc_self hyI)
    have hbv : -(β * U) ≤ b y * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y) := by
      have := abs_le.1 (hb y hyI')
      nlinarith
    have hag := hy hyI
    rw [le_div_iff₀ hlam]
    rcases le_or_gt (W1p.gradient u y) 0 with hg | hg
    · nlinarith
    · nlinarith [mul_le_mul_of_nonneg_left (ha y hyI') hg.le]
  have hmem : τ ∈ Icc x₀ x₁ := ⟨hτ.1, hτ.2.trans (by linarith)⟩
  have hU := intervalRepresentativeL_eq_integral hx u hmem
  rw [hu₀, zero_add] at hU
  have hle := intervalIntegral.integral_mono_ae_restrict hτ.1
    (intervalIntegrable_gradient u hmem) intervalIntegrable_const
    (g := fun _ ↦ (C + β) * U / lam) (by
      have hne : ∀ᵐ y : ℝ, y ≠ x₀ := by simp [ae_iff, measure_singleton]
      have hne' : ∀ᵐ y : ℝ, y ≠ τ := by simp [ae_iff, measure_singleton]
      filter_upwards [ae_restrict_of_ae hgrad, ae_restrict_of_ae hne, ae_restrict_of_ae hne',
        ae_restrict_mem measurableSet_Icc] with y hy h1 h2 h3
      exact hy ⟨lt_of_le_of_ne h3.1 (Ne.symm h1), (lt_of_le_of_ne h3.2 h2).trans_le hτ.2⟩)
  rw [intervalIntegral.integral_const, smul_eq_mul, ← hU] at hle
  have : (τ - x₀) * ((C + β) * U / lam) ≤ U / 2 := by
    calc (τ - x₀) * ((C + β) * U / lam) ≤ h * ((C + β) * U / lam) := by
          gcongr
          linarith [hτ.2]
      _ = h * ((C + β) / lam) * U := by ring
      _ ≤ 1 / 2 * U := by gcongr
      _ = U / 2 := by ring
  linarith

/-- The mass of `|m (d - q b) u|` on `(x₀, y)` is at most `exp L · U · ∫ |d - q b|` when
`0 ≤ u ≤ U` there. -/
private theorem intervalIntegral_abs_le (hx : x₀ < x₁)
    (u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) (hq : Integrable q)
    (he : IntegrableOn (fun y ↦ d y - q y * b y) (Ioo x₀ x₁)) {y U : ℝ}
    (hy : y ∈ Ioo x₀ x₁)
    (hU : ∀ z ∈ Icc x₀ y, |W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le z)| ≤ U) :
    ∫ z in x₀..y, |integratingFactor x₀ q z * ((d z - q z * b z) *
        W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le z))| ≤
      Real.exp (∫ s, |q s|) * U * ∫ z in Ioo x₀ x₁, |d z - q z * b z| := by
  set L := ∫ s, |q s|
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU x₀ (left_mem_Icc.2 hy.1.le))
  have hey : IntervalIntegrable (fun z ↦ |d z - q z * b z|) volume x₀ y :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hy.1.le).2
      ((he.mono_set (Ioo_subset_Ioo_right hy.2.le)).abs)
  have hpt : ∀ z ∈ Icc x₀ y, |integratingFactor x₀ q z * ((d z - q z * b z) *
      W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le z))| ≤
        Real.exp L * U * |d z - q z * b z| := fun z hz ↦ by
    rw [abs_mul, abs_mul, abs_of_pos (integratingFactor_pos z)]
    calc integratingFactor x₀ q z * (|d z - q z * b z| *
          |W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le z)|)
        ≤ Real.exp L * (|d z - q z * b z| * U) := by
          gcongr
          exacts [integratingFactor_le hq z, hU z hz]
      _ = Real.exp L * U * |d z - q z * b z| := by ring
  have hmeas : AEStronglyMeasurable (fun z ↦ integratingFactor x₀ q z * ((d z - q z * b z) *
      W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le z))) (volume.restrict (Ioc x₀ y)) :=
    (continuous_integratingFactor hq).aestronglyMeasurable.mul
      ((he.mono_set (Ioc_subset_Ioo_right hy.2)).aestronglyMeasurable.mul
        ((W1p.intervalRepresentativeL hx u).continuous.comp
          continuous_projIcc).aestronglyMeasurable)
  have hki : IntervalIntegrable (fun z ↦ |integratingFactor x₀ q z * ((d z - q z * b z) *
      W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le z))|) volume x₀ y := by
    refine (hey.const_mul (Real.exp L * U)).mono_fun' ?_ ?_
    · rw [uIoc_of_le hy.1.le]
      exact hmeas.norm
    · rw [uIoc_of_le hy.1.le]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
      rw [Real.norm_eq_abs, abs_abs]
      exact hpt z (Ioc_subset_Icc_self hz)
  calc ∫ z in x₀..y, |integratingFactor x₀ q z * ((d z - q z * b z) *
        W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le z))|
      ≤ ∫ z in x₀..y, Real.exp L * U * |d z - q z * b z| :=
        intervalIntegral.integral_mono_on hy.1.le hki (hey.const_mul _) hpt
    _ = Real.exp L * U * ∫ z in Ioc x₀ y, |d z - q z * b z| := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hy.1.le]
    _ ≤ Real.exp L * U * ∫ z in Ioo x₀ x₁, |d z - q z * b z| :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_set he.abs
          (.of_forall fun _ ↦ abs_nonneg _) (Ioc_subset_Ioo_right hy.2).eventuallyLE)
          (by positivity)

/-- The Hopf lemma for a weak supersolution, given an integrating factor `q` with `q a = c`. -/
private theorem exists_pos_mul_le_of_integratingFactor (hx : x₀ < x₁)
    (u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) {lam Λ β : ℝ} (hlam : 0 < lam)
    (ha : ∀ y ∈ Ioo x₀ x₁, lam ≤ a y) (haΛ : ∀ y ∈ Ioo x₀ x₁, a y ≤ Λ)
    (hb : ∀ y ∈ Ioo x₀ x₁, |b y| ≤ β)
    (hsuper : ∀ w : W1p0 volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2,
      (∀ᵐ x ∂volume.restrict (Ioo x₀ x₁),
        0 ≤ W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) x) →
      0 ≤ ∫ x in Ioo x₀ x₁, ((a x * W1p.gradient u x + b x * W1p.value u x) *
          W1p.gradient (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) x -
        (c x * W1p.gradient u x + d x * W1p.value u x) *
          W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) x))
    (hq : Integrable q) (hq2 : MemLp q 2 (volume.restrict (Ioo x₀ x₁)))
    (hqa : ∀ y ∈ Ioo x₀ x₁, q y * a y = c y)
    (hF : MemLp (fun y ↦ a y * W1p.gradient u y +
      b y * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)) 2
      (volume.restrict (Ioo x₀ x₁)))
    (he : IntegrableOn (fun y ↦ d y - q y * b y) (Ioo x₀ x₁))
    (hu₀ : W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le x₀) = 0)
    (hpos : ∀ t ∈ Ioo x₀ x₁, 0 < W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) :
    ∃ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo 0 δ,
      ε * h ≤ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le (x₀ + h)) := by
  set L := ∫ s, |q s|
  -- The weighted flux `Φ = m (a u' + b u)` and the weighted zeroth-order term `k`.
  set Φ : ℝ → ℝ := fun y ↦ integratingFactor x₀ q y * (a y * W1p.gradient u y +
    b y * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)) with hΦ
  set k : ℝ → ℝ := fun y ↦ integratingFactor x₀ q y * ((d y - q y * b y) *
    W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)) with hk
  have hvb : ∀ y, ‖W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)‖ ≤
      ‖W1p.intervalRepresentativeL hx u‖ := fun y ↦
    (W1p.intervalRepresentativeL hx u).norm_coe_le_norm _
  have hk1 : Integrable (fun y ↦ (d y - q y * b y) *
      W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)) (volume.restrict (Ioo x₀ x₁)) :=
    he.mul_bdd ((W1p.intervalRepresentativeL hx u).continuous.comp
      continuous_projIcc).aestronglyMeasurable (.of_forall hvb)
  have hΦi : IntegrableOn Φ (Ioo x₀ x₁) :=
    (memLp_integratingFactor_mul hq hF).integrable (by norm_num)
  have hki : IntegrableOn k (Ioo x₀ x₁) :=
    (memLp_integratingFactor_mul hq (memLp_one_iff_integrable.2 hk1)).integrable le_rfl
  have hKI := fun φ (h₁ : AbsolutelyContinuousOnInterval φ x₀ x₁) h₂ h₃ h₄ h₅ ↦
    integral_mul_le_integral_mul_deriv hx hsuper hq hq2 hqa hF hk1 h₁ h₂ h₃ h₄ h₅
  have hE : ∀ᵐ y, y ∈ Ioo x₀ x₁ → HasDerivAt (fun y ↦ ∫ z in x₀..y, Φ z) (Φ y) y := by
    filter_upwards [((intervalIntegrable_iff_integrableOn_Ioo_of_le hx.le).2
      hΦi).ae_hasDerivAt_integral] with y hy hyI
    exact hy (by rw [uIcc_of_le hx.le]; exact Ioo_subset_Icc_self hyI) x₀ left_mem_uIcc
  by_cases hA : ∃ s ∈ Ioo x₀ x₁,
      HasDerivAt (fun y ↦ ∫ z in x₀..y, Φ z) (Φ s) s ∧ ∫ z in x₀..s, |k z| < Φ s
  · -- The flux has a positive limit at `x₀`: `u` grows linearly.
    obtain ⟨s, hs, hPs, hlt⟩ := hA
    refine exists_pos_mul_le_of_le_flux hx u (fun y hy ↦ hlam.trans_le (ha y hy)) haΛ hb
      (σ := (Φ s - ∫ z in x₀..s, |k z|) * Real.exp (-L))
      (mul_pos (sub_pos.2 hlt) (Real.exp_pos _)) hs hu₀ ?_
    filter_upwards [ae_sub_le_of_hasDerivAt hΦi hki hKI hE hs hPs] with y hy hys
    exact mul_exp_neg_le_of_le_integratingFactor_mul hq (sub_pos.2 hlt) (hy hys)
  · -- The flux has a nonpositive limit at `x₀`: `u` vanishes near `x₀`.
    push Not at hA
    refine absurd hpos (not_forall_pos_of_flux_le hx u hlam ha hb
      (C := Real.exp L * Real.exp L * ∫ z in Ioo x₀ x₁, |d z - q z * b z|)
      (by positivity) hu₀ fun h hh hh₁ U hU hvU ↦ ?_)
    filter_upwards [hE] with y hy hyh
    have hyI : y ∈ Ioo x₀ x₁ := ⟨hyh.1, hyh.2.trans (by linarith)⟩
    have hKU := intervalIntegral_abs_le hx u hq he hyI (U := U) fun z hz ↦ by
      have hz0 : 0 ≤ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le z) := by
        rcases eq_or_lt_of_le hz.1 with rfl | hz'
        · exact hu₀.ge
        · exact (hpos z ⟨hz', hz.2.trans_lt hyI.2⟩).le
      rw [abs_of_nonneg hz0]
      exact hvU z ⟨hz.1, hz.2.trans hyh.2.le⟩
    have hD : 0 ≤ ∫ z in Ioo x₀ x₁, |d z - q z * b z| :=
      setIntegral_nonneg measurableSet_Ioo fun _ _ ↦ abs_nonneg _
    exact (le_exp_mul_of_integratingFactor_mul_le hq (by positivity)
      ((hA y hyI (hy hyI)).trans hKU)).trans_eq (by ring)

/-- **Hopf's boundary-point lemma for weak supersolutions on an interval.** Let
`L u = (a u' + b u)' + c u' + d u` on `(x₀, x₁)` with `λ ≤ a ≤ Λ`, `λ > 0`, `|b| ≤ β`, `a` and `b`
measurable, `c ∈ L²` and `d ∈ L¹`, and let `u ∈ W^{1,2}(x₀, x₁)` be a weak supersolution,
`L u ≤ 0`: `∫ ((a u' + b u) w' - (c u' + d u) w) ≥ 0` for every `w ∈ W^{1,2}_0(x₀, x₁)` with
`w ≥ 0`. If the continuous representative of `u` vanishes at `x₀` and is positive on `(x₀, x₁)`,
then it leaves `x₀` at a positive linear rate: `ε h ≤ u (x₀ + h)` for some `ε > 0` and all small
`h > 0`. No sign condition is imposed on `b`, `c` or `d`, and no continuity on `a` or `b`. -/
theorem exists_pos_mul_le_intervalRepresentativeL_of_integral_nonneg (hx : x₀ < x₁)
    (u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) {lam Λ β : ℝ} (hlam : 0 < lam)
    (ha : ∀ y ∈ Ioo x₀ x₁, lam ≤ a y) (haΛ : ∀ y ∈ Ioo x₀ x₁, a y ≤ Λ)
    (ham : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hb : ∀ y ∈ Ioo x₀ x₁, |b y| ≤ β) (hbm : AEStronglyMeasurable b (volume.restrict (Ioo x₀ x₁)))
    (hc : MemLp c 2 (volume.restrict (Ioo x₀ x₁))) (hd : IntegrableOn d (Ioo x₀ x₁))
    (hsuper : ∀ w : W1p0 volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2,
      (∀ᵐ y ∂volume.restrict (Ioo x₀ x₁),
        0 ≤ W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y) →
      0 ≤ ∫ y in Ioo x₀ x₁, ((a y * W1p.gradient u y + b y * W1p.value u y) *
          W1p.gradient (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y -
        (c y * W1p.gradient u y + d y * W1p.value u y) *
          W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y))
    (hu₀ : W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le x₀) = 0)
    (hpos : ∀ t ∈ Ioo x₀ x₁, 0 < W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) :
    ∃ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo 0 δ,
      ε * h ≤ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le (x₀ + h)) := by
  have hIoo : ∀ᵐ y ∂volume.restrict (Ioo x₀ x₁), y ∈ Ioo x₀ x₁ :=
    ae_restrict_mem measurableSet_Ioo
  -- The integrating factor is built from `q = c / a`, extended by zero off the interval.
  have hca : MemLp (fun y ↦ c y / a y) 2 (volume.restrict (Ioo x₀ x₁)) := by
    refine hc.of_le_mul (c := lam⁻¹)
      (hc.aestronglyMeasurable.div₀ ham)
      (hIoo.mono fun y hy ↦ ?_)
    rw [norm_div, Real.norm_of_nonneg (hlam.le.trans (ha y hy)), div_eq_inv_mul]
    gcongr
    exact ha y hy
  have hq2 : MemLp ((Ioo x₀ x₁).indicator fun y ↦ c y / a y) 2 (volume.restrict (Ioo x₀ x₁)) :=
    hca.ae_eq (indicator_ae_eq_restrict measurableSet_Ioo.nullMeasurableSet).symm
  have hgrad : MemLp (fun y ↦ a y * W1p.gradient u y) 2 (volume.restrict (Ioo x₀ x₁)) := by
    refine (Lp.memLp (W1p.gradient u)).of_le_mul (c := Λ)
      (ham.mul (Lp.memLp (W1p.gradient u)).aestronglyMeasurable) (hIoo.mono fun y hy ↦ ?_)
    rw [norm_mul, Real.norm_of_nonneg (hlam.le.trans (ha y hy))]
    gcongr
    exact haΛ y hy
  have hbv : MemLp (fun y ↦ b y * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)) 2
      (volume.restrict (Ioo x₀ x₁)) := by
    refine MemLp.of_bound (hbm.mul ((W1p.intervalRepresentativeL hx u).continuous.comp
      continuous_projIcc).aestronglyMeasurable) (β * ‖W1p.intervalRepresentativeL hx u‖)
      (hIoo.mono fun y hy ↦ ?_)
    rw [norm_mul]
    exact mul_le_mul (hb y hy) ((W1p.intervalRepresentativeL hx u).norm_coe_le_norm _)
      (norm_nonneg _) ((abs_nonneg _).trans (hb y hy))
  refine exists_pos_mul_le_of_integratingFactor hx u hlam ha haΛ hb hsuper
    ((integrable_indicator_iff measurableSet_Ioo).2 (hca.integrable (by norm_num))) hq2
    (fun y hy ↦ ?_) (hgrad.add hbv) (hd.sub ?_) hu₀ hpos
  · rw [indicator_of_mem hy, div_mul_cancel₀ _ (hlam.trans_le (ha y hy)).ne']
  · exact (hq2.integrable (by norm_num)).mul_bdd hbm (hIoo.mono fun y hy ↦ hb y hy)

/-- **Hopf's boundary-point lemma for weak supersolutions on an interval**, derivative form: under
the hypotheses of `exists_pos_mul_le_intervalRepresentativeL_of_integral_nonneg`, a right
derivative of the continuous representative at `x₀`, if it exists, is positive. -/
theorem pos_of_hasDerivWithinAt_intervalRepresentativeL_of_integral_nonneg (hx : x₀ < x₁)
    (u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) {lam Λ β : ℝ} (hlam : 0 < lam)
    (ha : ∀ y ∈ Ioo x₀ x₁, lam ≤ a y) (haΛ : ∀ y ∈ Ioo x₀ x₁, a y ≤ Λ)
    (ham : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hb : ∀ y ∈ Ioo x₀ x₁, |b y| ≤ β) (hbm : AEStronglyMeasurable b (volume.restrict (Ioo x₀ x₁)))
    (hc : MemLp c 2 (volume.restrict (Ioo x₀ x₁))) (hd : IntegrableOn d (Ioo x₀ x₁))
    (hsuper : ∀ w : W1p0 volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2,
      (∀ᵐ y ∂volume.restrict (Ioo x₀ x₁),
        0 ≤ W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y) →
      0 ≤ ∫ y in Ioo x₀ x₁, ((a y * W1p.gradient u y + b y * W1p.value u y) *
          W1p.gradient (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y -
        (c y * W1p.gradient u y + d y * W1p.value u y) *
          W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y))
    (hu₀ : W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le x₀) = 0)
    (hpos : ∀ t ∈ Ioo x₀ x₁, 0 < W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t))
    {u' : ℝ}
    (hd' : HasDerivWithinAt (fun t ↦ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t))
      u' (Ici x₀) x₀) :
    0 < u' := by
  obtain ⟨ε, hε, δ, hδ, h⟩ := exists_pos_mul_le_intervalRepresentativeL_of_integral_nonneg hx u
    hlam ha haΛ ham hb hbm hc hd hsuper hu₀ hpos
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x₀)).mp
    (hasDerivWithinAt_Ioi_iff_Ici.mpr hd')
  refine hε.trans_le (ge_of_tendsto hslope ?_)
  filter_upwards [Ioo_mem_nhdsGT (lt_add_of_pos_right x₀ hδ)] with t ht
  have h' := h (t - x₀) ⟨sub_pos.2 ht.1, by linarith [ht.2]⟩
  rw [add_sub_cancel] at h'
  rw [slope_def_field, hu₀, sub_zero, le_div_iff₀ (sub_pos.2 ht.1)]
  exact h'

end TauCeti.PDE
