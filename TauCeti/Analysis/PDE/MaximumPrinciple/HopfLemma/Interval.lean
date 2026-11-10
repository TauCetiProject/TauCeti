/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# Hopf's boundary-point lemma for weak supersolutions on an interval

Let `x₀ < x₁` and consider on the interval `(x₀, x₁)` the one-dimensional divergence-form operator

`L u = -(a u' + b u)' + c u' + d u`

with measurable coefficients, `0 < λ ≤ a ≤ Λ`, `|b|, |c| ≤ M` and `d` integrable. A function
`u` with integrable weak derivative `u'` is a **weak supersolution**, `L u ≥ 0`, if

`0 ≤ ∫ ((a u' + b u) ψ' + (c u' + d u) ψ)`

for every nonnegative test function `ψ` on `(x₀, x₁)`. This file proves **Hopf's boundary-point
lemma** for such `u`: if `u` is continuous on `[x₀, x₁)`, vanishes at `x₀` and is positive on
`(x₀, x₁)`, then it leaves `x₀` at a positive linear rate, `κ h ≤ u (x₀ + h)` for some `κ > 0` and
all small `h > 0`
(`TauCeti.PDE.exists_pos_mul_le_of_integral_mul_deriv_add_mul_nonneg`). In particular a right
derivative of `u` at `x₀`, if it exists, is positive
(`TauCeti.PDE.pos_of_hasDerivWithinAt_of_integral_mul_deriv_add_mul_nonneg`).

No regularity of the coefficients beyond boundedness is needed, and no sign condition on `b`,
`c` or `d`: since the boundary value is `0` and `u ≥ 0`, the lower-order terms only contribute
quantities that are small near `x₀`. The direction of the inequality matters: `u = (x - x₀)²`
satisfies `L u = -2 ≤ 0` for `a = 1`, `b = c = d = 0`, is positive on `(x₀, x₁)` and vanishes at
`x₀`, but `u (x₀ + h) / h = h → 0`.

## Proof

Write `F = a u' + b u` for the flux and `g = c u' + d u`. The supersolution inequality says that
`F' ≤ g` in the sense of distributions, so `Φ = F - ∫ t in x₀..·, g t` agrees almost everywhere
with an antitone function
(`MeasureTheory.LocallyIntegrableOn.exists_ae_antitoneOn_sub_integral_of_integral_nonneg`).

* If `Φ z = η > 0` at some point `z`, then `Φ ≥ η` before `z`, while `b u` and the primitive of
  `g` tend to `0` at `x₀`. So `a u' ≥ η / 2` near `x₀`, hence `u' ≥ η / (2 Λ)`, and integrating
  gives the linear lower bound.
* Otherwise `Φ ≤ 0` almost everywhere, that is `a u' ≤ -b u + ∫ g`. Let
  `W x = ∫ t in x₀..x, max (u' t) 0`. Since `u ≥ 0` and `u x₀ = 0`, both `u` and
  `∫ t in x₀..x, |u' t| = 2 W x - u x` are controlled by `W x`, so `max u' 0 ≤ C W x / λ` on
  `(x₀, x)` and `W x ≤ (x - x₀) C W x / λ`. For `x` close to `x₀` this forces `W x = 0`, hence
  `u x ≤ 0`, contradicting positivity.

## Main declarations

* `TauCeti.PDE.exists_pos_mul_le_of_integral_mul_deriv_add_mul_nonneg`: **Hopf's lemma for weak
  supersolutions on an interval**, the difference quotients `u (x₀ + h) / h` are bounded below
  by a positive constant for small `h > 0`.
* `TauCeti.PDE.pos_of_hasDerivWithinAt_of_integral_mul_deriv_add_mul_nonneg`: the derivative
  form, a right derivative of `u` at `x₀` is positive.

## References

* L. Rosales, *Generalizing Hopf's boundary point lemma*, Canad. Math. Bull. 62 (2019),
  arXiv:1806.07003 (the divergence-form lemma for weak supersolutions in dimension `n ≥ 2`).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 3.4 (the classical lemma) and Section 8.1 (weak supersolutions).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Section 8.2
  (Sobolev functions of one variable).
-/

public section

open MeasureTheory Set Filter Topology intervalIntegral
open scoped ContDiff

namespace TauCeti.PDE

variable {x₀ x₁ y lam Λ M : ℝ} {a b c d u u' : ℝ → ℝ}

/-- If `u x = ∫ t in x₀..x, u' t` on `[x₀, y]` and `κ ≤ u'` almost everywhere on
`(x₀, x₀ + δ)`, then `κ h ≤ u (x₀ + h)` for `0 < h < δ`. -/
private lemma mul_le_of_ae_le_deriv {δ κ : ℝ} (hδy : x₀ + δ ≤ y)
    (hu'i : IntegrableOn u' (Ioo x₀ y)) (hftc : ∀ x ∈ Icc x₀ y, ∫ t in x₀..x, u' t = u x)
    (hκ : ∀ᵐ x, x ∈ Ioo x₀ (x₀ + δ) → κ ≤ u' x) {h : ℝ} (hh : h ∈ Ioo 0 δ) :
    κ * h ≤ u (x₀ + h) := by
  rw [← hftc (x₀ + h) ⟨by linarith [hh.1], by linarith [hh.2]⟩]
  have hint : IntervalIntegrable u' volume x₀ (x₀ + h) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [hh.1])).2
      (hu'i.mono_set (Ioo_subset_Ioo_right (by linarith [hh.2])))
  calc κ * h = ∫ _ in x₀..x₀ + h, κ := by simp [mul_comm]
    _ ≤ ∫ t in x₀..x₀ + h, u' t := by
      refine integral_mono_ae_restrict (by linarith [hh.1]) intervalIntegrable_const hint
        ((ae_restrict_iff' measurableSet_Icc).2 ?_)
      filter_upwards [hκ, volume.ae_ne x₀] with t ht htx₀ htI
      exact ht ⟨htI.1.lt_of_ne' htx₀, by linarith [htI.2, hh.2]⟩

/-- Let `u x = ∫ t in x₀..x, u' t` on `[x₀, x]` with `u x ≥ 0`, and let
`W = ∫ t in x₀..x, max (u' t) 0`. Then `u ≤ W` on `[x₀, x]` and `∫ t in x₀..x, |u' t| ≤ 2 W`. -/
private lemma le_integral_max_zero_and_integral_abs_le (hx : x₀ ≤ x₁)
    (hu'i : IntegrableOn u' (Icc x₀ x₁)) (hftc : ∀ t ∈ Icc x₀ x₁, ∫ s in x₀..t, u' s = u t)
    (hu0 : 0 ≤ u x₁) :
    (∀ t ∈ Icc x₀ x₁, u t ≤ ∫ s in x₀..x₁, max (u' s) 0) ∧
      ∫ s in x₀..x₁, |u' s| ≤ 2 * ∫ s in x₀..x₁, max (u' s) 0 := by
  have hint : ∀ {f : ℝ → ℝ}, IntegrableOn f (Icc x₀ x₁) → ∀ t ∈ Icc x₀ x₁,
      IntervalIntegrable f volume x₀ t := fun hf t ht ↦
    (hf.mono_set (uIcc_of_le ht.1 ▸ Icc_subset_Icc_right ht.2)).intervalIntegrable
  have hx₁ : x₁ ∈ Icc x₀ x₁ := right_mem_Icc.2 hx
  refine ⟨fun t ht ↦ ?_, ?_⟩
  · -- `u t = ∫ u' ≤ ∫ max u' 0` over `[x₀, t]`, and the latter grows with `t`.
    rw [← hftc t ht]
    exact (integral_mono_on ht.1 (hint hu'i t ht) (hint hu'i.pos_part t ht)
      fun s _ ↦ le_max_left _ _).trans (integral_mono_interval le_rfl ht.1 ht.2
        (Eventually.of_forall fun s ↦ le_max_right _ _) (hint hu'i.pos_part x₁ hx₁))
  · -- `|u'| = 2 max u' 0 - u'` and `∫ u' = u x₁ ≥ 0`.
    rw [integral_congr (g := fun t ↦ 2 * max (u' t) 0 - u' t) fun t _ ↦ by
        dsimp only
        rcases le_total 0 (u' t) with h | h
        · rw [abs_of_nonneg h, max_eq_left h]; ring
        · rw [abs_of_nonpos h, max_eq_right h]; ring,
      intervalIntegral.integral_sub ((hint hu'i.pos_part x₁ hx₁).const_mul 2) (hint hu'i x₁ hx₁),
      intervalIntegral.integral_const_mul, hftc x₁ hx₁]
    linarith

/-- The lower-order terms in the Gronwall step. If `0 ≤ u ≤ W` on `[x₀, x]` and
`∫ s in x₀..x, |u' s| ≤ 2 W`, then for `t ∈ [x₀, x]`,
`∫ s in x₀..t, (K |u' s| + |d s| u s) ≤ (2 K + ∫ s in x₀..x, |d s|) W`. -/
private lemma integral_mul_abs_add_le {K W : ℝ} (hx : x₀ ≤ x₁) (hK : 0 ≤ K)
    (hu'i : IntegrableOn u' (Icc x₀ x₁)) (hd : IntegrableOn d (Icc x₀ x₁))
    (huc : ContinuousOn u (Icc x₀ x₁)) (hu0 : ∀ t ∈ Icc x₀ x₁, 0 ≤ u t)
    (huW : ∀ t ∈ Icc x₀ x₁, u t ≤ W) (habs : ∫ s in x₀..x₁, |u' s| ≤ 2 * W) {t : ℝ}
    (ht : t ∈ Icc x₀ x₁) :
    ∫ s in x₀..t, (K * |u' s| + |d s| * u s) ≤ (2 * K + ∫ s in x₀..x₁, |d s|) * W := by
  have hint : ∀ {f : ℝ → ℝ}, IntegrableOn f (Icc x₀ x₁) → IntervalIntegrable f volume x₀ x₁ :=
    fun hf ↦ (hf.mono_set (uIcc_of_le hx).subset).intervalIntegrable
  have hdu : IntegrableOn (fun s ↦ |d s| * u s) (Icc x₀ x₁) :=
    IntegrableOn.mul_continuousOn hd.abs huc isCompact_Icc
  have hW : 0 ≤ W := (hu0 x₀ (left_mem_Icc.2 hx)).trans (huW x₀ (left_mem_Icc.2 hx))
  calc ∫ s in x₀..t, (K * |u' s| + |d s| * u s)
      ≤ ∫ s in x₀..x₁, (K * |u' s| + |d s| * u s) :=
        integral_mono_interval le_rfl ht.1 ht.2
          ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs ↦
            add_nonneg (mul_nonneg hK (abs_nonneg _))
              (mul_nonneg (abs_nonneg _) (hu0 s (Ioc_subset_Icc_self hs)))))
          (hint ((hu'i.abs.const_mul K).add hdu))
    _ = K * (∫ s in x₀..x₁, |u' s|) + ∫ s in x₀..x₁, |d s| * u s := by
        rw [intervalIntegral.integral_add ((hint hu'i.abs).const_mul K) (hint hdu),
          intervalIntegral.integral_const_mul]
    _ ≤ K * (2 * W) + ∫ s in x₀..x₁, |d s| * W := by
        gcongr ?_ + ?_
        · exact mul_le_mul_of_nonneg_left habs hK
        · exact integral_mono_on hx (hint hdu) ((hint hd.abs).mul_const W)
            fun s hs ↦ mul_le_mul_of_nonneg_left (huW s hs) (abs_nonneg _)
    _ = (2 * K + ∫ s in x₀..x₁, |d s|) * W := by
        rw [intervalIntegral.integral_mul_const]
        ring

/-- The Gronwall step of the Hopf lemma. Let `u ≥ 0` on `[x₀, y]` with `u x = ∫ t in x₀..x, u' t`,
and suppose that almost everywhere on `(x₀, y)`, wherever `u' t > 0`,
`λ u' t ≤ K u t + ∫ s in x₀..t, (K |u' s| + |d s| u s)`. Then `u` is not positive on `(x₀, y)`. -/
private lemma exists_mem_Ioo_nonpos_of_mul_deriv_le (hy : x₀ < y) (hlam : 0 < lam) {K : ℝ}
    (hK : 0 ≤ K) (hu'i : IntegrableOn u' (Ioo x₀ y)) (hd : IntegrableOn d (Ioo x₀ y))
    (huc : ContinuousOn u (Icc x₀ y)) (hftc : ∀ x ∈ Icc x₀ y, ∫ t in x₀..x, u' t = u x)
    (hu0 : ∀ x ∈ Icc x₀ y, 0 ≤ u x)
    (hle : ∀ᵐ t, t ∈ Ioo x₀ y → 0 < u' t →
      lam * u' t ≤ K * u t + ∫ s in x₀..t, (K * |u' s| + |d s| * u s)) :
    ∃ x ∈ Ioo x₀ y, u x ≤ 0 := by
  set D := ∫ t in Ioo x₀ y, |d t|
  have hD : 0 ≤ D := integral_nonneg fun _ ↦ abs_nonneg _
  set L := 3 * K + D
  -- A point `x = x₀ + r` so close to `x₀` that `r L ≤ λ / 2`.
  set r := min ((y - x₀) / 2) (lam / (2 * (L + 1)))
  have hr : 0 < r := lt_min (by linarith) (by positivity)
  have hrL : r * L ≤ lam / 2 := by
    have h₁ : r * (2 * (L + 1)) ≤ lam := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
    nlinarith
  set x := x₀ + r
  have hxy : x < y := by linarith [min_le_left ((y - x₀) / 2) (lam / (2 * (L + 1)))]
  have hx : x₀ ≤ x := by linarith
  have hsub : Icc x₀ x ⊆ Icc x₀ y := Icc_subset_Icc_right hxy.le
  have hIcc : IntegrableOn u' (Icc x₀ x) :=
    ((integrableOn_Icc_iff_integrableOn_Ioo (f := u') (a := x₀) (b := y)).2 hu'i).mono_set hsub
  have hdIcc : IntegrableOn d (Icc x₀ x) :=
    ((integrableOn_Icc_iff_integrableOn_Ioo (f := d) (a := x₀) (b := y)).2 hd).mono_set hsub
  -- With `W = ∫ t in x₀..x, max (u' t) 0`, the hypothesis gives `max u' 0 ≤ L W / λ`.
  set W := ∫ t in x₀..x, max (u' t) 0
  obtain ⟨huW, habs⟩ := le_integral_max_zero_and_integral_abs_le hx hIcc
    (fun t ht ↦ hftc t (hsub ht)) (hu0 x (hsub (right_mem_Icc.2 hx)))
  have hW : 0 ≤ W := (hu0 x₀ (left_mem_Icc.2 hy.le)).trans (huW x₀ (left_mem_Icc.2 hx))
  have hdD : ∫ s in x₀..x, |d s| ≤ D := by
    rw [integral_of_le hx]
    exact setIntegral_mono_set hd.abs (Eventually.of_forall fun _ ↦ abs_nonneg _)
      (Ioc_subset_Ioo_right hxy).eventuallyLE
  have hW_le : W ≤ r * (L * W / lam) := by
    calc W ≤ ∫ _ in x₀..x, L * W / lam := by
          refine integral_mono_ae_restrict hx
            (IntegrableOn.mono_set hIcc.pos_part (uIcc_of_le hx).subset).intervalIntegrable
            intervalIntegrable_const ((ae_restrict_iff' measurableSet_Icc).2 ?_)
          filter_upwards [hle, volume.ae_ne x₀] with t ht htx₀ htI
          rcases le_or_gt (u' t) 0 with hneg | hpos
          · rw [max_eq_right hneg]
            positivity
          rw [max_eq_left hpos.le, le_div_iff₀ hlam]
          have h₁ := ht ⟨htI.1.lt_of_ne' htx₀, htI.2.trans_lt hxy⟩ hpos
          have h₂ := integral_mul_abs_add_le hx hK hIcc hdIcc (huc.mono hsub)
            (fun s hs ↦ hu0 s (hsub hs)) huW habs htI
          have h₃ := huW t htI
          nlinarith
      _ = r * (L * W / lam) := by
          simp only [intervalIntegral.integral_const, smul_eq_mul, x, add_sub_cancel_left]
  -- `r L ≤ λ / 2` turns this into `W ≤ W / 2`, so `u x ≤ W ≤ 0`.
  have hhalf : r * (L * W / lam) ≤ W / 2 := by
    rw [← mul_div_assoc, div_le_div_iff₀ hlam two_pos]
    nlinarith
  exact ⟨x, ⟨by linarith, hxy⟩, (huW x (right_mem_Icc.2 hx)).trans (by linarith)⟩

/-- The case of a positive flux in the Hopf lemma. Suppose that, almost everywhere on `(x₀, z)`,
the flux `a u' + b u` exceeds `η + ∫ t in x₀..x, g t` for some `η > 0`, with `0 < a ≤ Λ` and
`b u ≤ K u`. Since the primitive of `g` and `u` tend to `0` at `x₀`, the derivative `u'` is at
least `η / (2 Λ)` near `x₀`, so `u` grows at least linearly from `x₀`. -/
private lemma exists_pos_mul_le_of_le_flux {z η K : ℝ} {g : ℝ → ℝ} (hxz : x₀ < z) (hzy : z ≤ y)
    (hη : 0 < η) (hΛ : 0 < Λ) (huc : ContinuousOn u (Icc x₀ y)) (hu₀ : u x₀ = 0)
    (hu'i : IntegrableOn u' (Ioo x₀ y)) (hftc : ∀ x ∈ Icc x₀ y, ∫ t in x₀..x, u' t = u x)
    (hg : IntegrableOn g (Ioo x₀ y))
    (hflux : ∀ᵐ x, x ∈ Ioo x₀ z → η ≤ a x * u' x + b x * u x - ∫ t in x₀..x, g t)
    (ha : ∀ᵐ x, x ∈ Ioo x₀ z → 0 < a x ∧ a x ≤ Λ)
    (hb : ∀ᵐ x, x ∈ Ioo x₀ z → b x * u x ≤ K * u x) :
    ∃ κ > 0, ∃ δ > 0, ∀ h ∈ Ioo 0 δ, κ * h ≤ u (x₀ + h) := by
  have hy : x₀ ∈ Icc x₀ y := left_mem_Icc.2 (hxz.le.trans hzy)
  -- Near `x₀`, both `|∫ t in x₀..x, g t|` and `K u x` are below `η / 4`.
  have hP : Tendsto (fun x ↦ |∫ t in x₀..x, g t|) (𝓝[Icc x₀ y] x₀) (𝓝 0) := by
    simpa using (TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo
      hg hy x₀ hy).tendsto.abs
  have hu : Tendsto (fun x ↦ K * u x) (𝓝[Icc x₀ y] x₀) (𝓝 0) := by
    simpa [hu₀] using ((huc x₀ hy).tendsto.const_mul K)
  obtain ⟨ε, hε, hsmall⟩ := Metric.mem_nhdsWithin_iff.1
    ((hP.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < η / 4))).and
      (hu.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < η / 4))))
  set δ := min ε (z - x₀)
  have hδ : 0 < δ := lt_min hε (sub_pos.2 hxz)
  have hδz : x₀ + δ ≤ z := by linarith [min_le_right ε (z - x₀)]
  refine ⟨η / (2 * Λ), by positivity, δ, hδ, fun h hh ↦ mul_le_of_ae_le_deriv
    (hδz.trans hzy) hu'i hftc ?_ hh⟩
  filter_upwards [hflux, ha, hb] with x hxf hxa hxb hxδ
  have hxz' : x ∈ Ioo x₀ z := ⟨hxδ.1, hxδ.2.trans_le hδz⟩
  obtain ⟨hPx, hux⟩ : |∫ t in x₀..x, g t| < η / 4 ∧ K * u x < η / 4 := hsmall ⟨by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.2 hxδ.1)]
    linarith [hxδ.2, min_le_left ε (z - x₀)], hxδ.1.le, hxz'.2.le.trans hzy⟩
  have h₁ := hxf hxz'
  obtain ⟨ha₀, haΛ⟩ := hxa hxz'
  have h₂ := hxb hxz'
  have h₃ := neg_abs_le (∫ t in x₀..x, g t)
  -- `a u' > η / 2 > 0`, so `u' > 0` and `Λ u' ≥ a u' > η / 2`.
  have hau : η / 2 < a x * u' x := by linarith
  have hu' : 0 < u' x := by
    by_contra hneg
    nlinarith [not_lt.1 hneg]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right haΛ hu'.le]

/-- The lower-order part of the flux. If `|c| ≤ K` almost everywhere and `u ≥ 0` on `[x₀, y]`,
then `∫ s in x₀..t, (c u' + d u) ≤ ∫ s in x₀..t, (K |u'| + |d| u)` for `t ∈ [x₀, y]`. -/
private lemma integral_mul_add_mul_le {t K : ℝ} (ht : t ∈ Icc x₀ y)
    (hc : ∀ᵐ s, s ∈ Ioo x₀ y → |c s| ≤ K) (hu0 : ∀ x ∈ Icc x₀ y, 0 ≤ u x)
    (hg : IntegrableOn (fun s ↦ c s * u' s + d s * u s) (Ioo x₀ y))
    (hG : IntegrableOn (fun s ↦ K * |u' s| + |d s| * u s) (Ioo x₀ y)) :
    ∫ s in x₀..t, (c s * u' s + d s * u s) ≤ ∫ s in x₀..t, (K * |u' s| + |d s| * u s) := by
  have hint : ∀ {f : ℝ → ℝ}, IntegrableOn f (Ioo x₀ y) → IntervalIntegrable f volume x₀ t :=
    fun hf ↦ (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).2
      (hf.mono_set (Ioo_subset_Ioo_right ht.2))
  refine integral_mono_ae_restrict ht.1 (hint hg) (hint hG)
    ((ae_restrict_iff' measurableSet_Icc).2 ?_)
  filter_upwards [hc, volume.ae_ne x₀, volume.ae_ne t] with s hs hsx₀ hst hsI
  have hsJ : s ∈ Ioo x₀ y := ⟨hsI.1.lt_of_ne' hsx₀, (hsI.2.lt_of_ne hst).trans_le ht.2⟩
  have hus := hu0 s (Ioo_subset_Icc_self hsJ)
  have h₁ : c s * u' s ≤ K * |u' s| :=
    (le_abs_self _).trans (abs_mul (c s) (u' s) ▸
      mul_le_mul_of_nonneg_right (hs hsJ) (abs_nonneg _))
  have h₂ : d s * u s ≤ |d s| * u s := mul_le_mul_of_nonneg_right (le_abs_self _) hus
  linarith

/-- On a subinterval `(x₀, y)` of `(x₀, x₁)` on whose closure `u` is continuous, the flux
`a u' + b u`, the lower-order term `c u' + d u` and its majorant `M |u'| + |d| u` are integrable. -/
private lemma integrableOn_flux (hJ : Ioo x₀ y ⊆ Ioo x₀ x₁) (hlam : 0 < lam)
    (huc : ContinuousOn u (Icc x₀ y)) (hu'i : IntegrableOn u' (Ioo x₀ x₁))
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haΛ : ∀ᵐ x ∂volume.restrict (Ioo x₀ x₁), lam ≤ a x ∧ a x ≤ Λ)
    (hb : AEStronglyMeasurable b (volume.restrict (Ioo x₀ x₁)))
    (hbM : ∀ᵐ x ∂volume.restrict (Ioo x₀ x₁), |b x| ≤ M)
    (hc : AEStronglyMeasurable c (volume.restrict (Ioo x₀ x₁)))
    (hcM : ∀ᵐ x ∂volume.restrict (Ioo x₀ x₁), |c x| ≤ M) (hd : IntegrableOn d (Ioo x₀ x₁)) :
    IntegrableOn (fun x ↦ a x * u' x + b x * u x) (Ioo x₀ y) ∧
      IntegrableOn (fun x ↦ c x * u' x + d x * u x) (Ioo x₀ y) ∧
      IntegrableOn (fun x ↦ |M| * |u' x| + |d x| * u x) (Ioo x₀ y) := by
  obtain ⟨U, hU⟩ := isCompact_Icc.exists_bound_of_continuousOn huc
  have hu'J : IntegrableOn u' (Ioo x₀ y) := hu'i.mono_set hJ
  have huJ : AEStronglyMeasurable u (volume.restrict (Ioo x₀ y)) :=
    (huc.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hUJ : ∀ᵐ x ∂volume.restrict (Ioo x₀ y), ‖u x‖ ≤ U :=
    (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hxJ ↦
      hU x (Ioo_subset_Icc_self hxJ))
  have haJ : ∀ᵐ x ∂volume.restrict (Ioo x₀ y), ‖a x‖ ≤ Λ :=
    (ae_restrict_of_ae_restrict_of_subset hJ haΛ).mono fun x hxa ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (hlam.trans_le hxa.1)]
      exact hxa.2
  refine ⟨(hu'J.bdd_mul (ha.mono_set hJ) haJ).add (((huc.integrableOn_compact
    isCompact_Icc).mono_set Ioo_subset_Icc_self).bdd_mul (hb.mono_set hJ)
      (ae_restrict_of_ae_restrict_of_subset hJ hbM)),
    (hu'J.bdd_mul (hc.mono_set hJ) (ae_restrict_of_ae_restrict_of_subset hJ hcM)).add
      ((hd.mono_set hJ).mul_bdd huJ hUJ),
    (hu'J.abs.const_mul _).add ((hd.mono_set hJ).abs.mul_bdd huJ hUJ)⟩

/-- **Hopf's boundary-point lemma for weak supersolutions on an interval.** Let `u` be continuous
on `[x₀, x₁)` with `u x₀ = 0` and `u > 0` on `(x₀, x₁)`, with integrable weak derivative `u'` on
`(x₀, x₁)`. Let `a, b, c` be measurable with `0 < λ ≤ a ≤ Λ`, `|b| ≤ M` and `|c| ≤ M`, and let
`d` be integrable on `(x₀, x₁)`. If `u` is a weak supersolution of
`-(a u' + b u)' + c u' + d u ≥ 0`, that is,
`0 ≤ ∫ ((a u' + b u) ψ' + (c u' + d u) ψ)` for every nonnegative test function `ψ` on
`(x₀, x₁)`, then `u` leaves `x₀` at a positive linear rate: `κ h ≤ u (x₀ + h)` for some `κ > 0`
and all `0 < h < δ`. -/
theorem exists_pos_mul_le_of_integral_mul_deriv_add_mul_nonneg (hx : x₀ < x₁) (hlam : 0 < lam)
    (hu : ContinuousOn u (Ico x₀ x₁)) (hu₀ : u x₀ = 0) (hpos : ∀ x ∈ Ioo x₀ x₁, 0 < u x)
    (hu' : HasWeakLineDerivOn volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ u u' 1)
    (hu'i : IntegrableOn u' (Ioo x₀ x₁))
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haΛ : ∀ᵐ x ∂volume.restrict (Ioo x₀ x₁), lam ≤ a x ∧ a x ≤ Λ)
    (hb : AEStronglyMeasurable b (volume.restrict (Ioo x₀ x₁)))
    (hbM : ∀ᵐ x ∂volume.restrict (Ioo x₀ x₁), |b x| ≤ M)
    (hc : AEStronglyMeasurable c (volume.restrict (Ioo x₀ x₁)))
    (hcM : ∀ᵐ x ∂volume.restrict (Ioo x₀ x₁), |c x| ≤ M) (hd : IntegrableOn d (Ioo x₀ x₁))
    (hsuper : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo x₀ x₁ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, ((a x * u' x + b x * u x) * deriv ψ x + (c x * u' x + d x * u x) * ψ x)) :
    ∃ κ > 0, ∃ δ > 0, ∀ h ∈ Ioo 0 δ, κ * h ≤ u (x₀ + h) := by
  -- Work on `J = (x₀, y)`, `y` the midpoint, where `u` is bounded and all products are integrable.
  set y := (x₀ + x₁) / 2 with hy_def
  have hy : x₀ < y := by linarith
  have hyx : y < x₁ := by linarith
  have hJ : Ioo x₀ y ⊆ Ioo x₀ x₁ := Ioo_subset_Ioo_right hyx.le
  have huc : ContinuousOn u (Icc x₀ y) := hu.mono (Icc_subset_Ico_right hyx)
  have hu0 : ∀ x ∈ Icc x₀ y, 0 ≤ u x := fun x hxy ↦ by
    rcases hxy.1.eq_or_lt with rfl | h
    · exact hu₀.ge
    · exact (hpos x ⟨h, hxy.2.trans_lt hyx⟩).le
  have hu'J : IntegrableOn u' (Ioo x₀ y) := hu'i.mono_set hJ
  obtain ⟨hF, hg, hG⟩ := integrableOn_flux hJ hlam huc hu'i ha haΛ hb hbM hc hcM hd
  have hftc : ∀ x ∈ Icc x₀ y, ∫ t in x₀..x, u' t = u x := fun x hxy ↦ by
    rw [(hu'.mono (Ω' := ⟨Ioo x₀ y, isOpen_Ioo⟩) hJ).integral_eq_sub hu'J huc EventuallyEq.rfl
      (left_mem_Icc.2 hy.le) hxy, hu₀, sub_zero]
  -- The flux minus the primitive of `g` is antitone off a null set.
  obtain ⟨s, hs, hanti⟩ :=
    hF.locallyIntegrableOn.exists_ae_antitoneOn_sub_integral_of_integral_nonneg hg
      fun ψ hψ hψs hψnn ↦ hsuper ψ hψ (hψs.trans hJ) hψnn
  set P : ℝ → ℝ := fun x ↦ ∫ t in x₀..x, (c t * u' t + d t * u t)
  have haΛ' := (ae_restrict_iff' measurableSet_Ioo).1 haΛ
  have hbu : ∀ᵐ t, t ∈ Ioo x₀ y → |b t * u t| ≤ |M| * u t := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hbM] with t htb htJ
    have hut := hu0 t (Ioo_subset_Icc_self htJ)
    rw [abs_mul, abs_of_nonneg hut]
    exact mul_le_mul_of_nonneg_right ((htb (hJ htJ)).trans (le_abs_self M)) hut
  by_cases hcase : ∃ z ∈ Ioo x₀ y ∩ s, 0 < a z * u' z + b z * u z - P z
  · -- A positive value of the antitone function `Φ = a u' + b u - P` bounds it below near `x₀`.
    obtain ⟨z, ⟨hzJ, hzs⟩, hη⟩ := hcase
    have hΛ : 0 < Λ := by
      have : (ae (volume.restrict (Ioo x₀ x₁))).NeBot := ae_restrict_neBot.2 (by simp [hx])
      obtain ⟨x, hxa⟩ := haΛ.exists
      exact hlam.trans_le (hxa.1.trans hxa.2)
    have hzy : Ioo x₀ z ⊆ Ioo x₀ y := Ioo_subset_Ioo_right hzJ.2.le
    refine exists_pos_mul_le_of_le_flux (a := a) (b := b) (K := |M|) hzJ.1 hzJ.2.le hη hΛ huc hu₀
      hu'J hftc hg ?_ ?_ ?_
    · filter_upwards [hs] with x hxs hxz
      exact hanti ⟨hzy hxz, hxs⟩ ⟨hzJ, hzs⟩ hxz.2.le
    · filter_upwards [haΛ'] with x hxa hxz
      exact ⟨hlam.trans_le (hxa (hJ (hzy hxz))).1, (hxa (hJ (hzy hxz))).2⟩
    · filter_upwards [hbu] with x hxb hxz using (le_abs_self _).trans (hxb (hzy hxz))
  · -- Otherwise `a u' ≤ -b u + P` almost everywhere, and the Gronwall step makes `u` vanish.
    simp only [not_exists, not_and, not_lt] at hcase
    have hcM' : ∀ᵐ t, t ∈ Ioo x₀ y → |c t| ≤ |M| := by
      filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hcM] with t htc htJ
      exact (htc (hJ htJ)).trans (le_abs_self M)
    obtain ⟨x, hxJ, hux⟩ := exists_mem_Ioo_nonpos_of_mul_deriv_le hy hlam (abs_nonneg M) hu'J
      (hd.mono_set hJ) huc hftc hu0 (by
        filter_upwards [hs, haΛ', hbu] with t hts hta htb htJ hu't
        have h₁ := hcase t ⟨htJ, hts⟩
        have h₂ := integral_mul_add_mul_le (Ioo_subset_Icc_self htJ) hcM' hu0 hg hG
        have h₃ := mul_le_mul_of_nonneg_right (hta (hJ htJ)).1 hu't.le
        have h₄ : P t = ∫ s in x₀..t, (c s * u' s + d s * u s) := rfl
        linarith [neg_abs_le (b t * u t), htb htJ])
    exact absurd hux (hpos x (hJ hxJ)).not_ge

/-- **Hopf's boundary-point lemma for weak supersolutions on an interval, derivative form.**
Under the hypotheses of `TauCeti.PDE.exists_pos_mul_le_of_integral_mul_deriv_add_mul_nonneg`, a
right derivative of `u` at `x₀`, if it exists, is positive. -/
theorem pos_of_hasDerivWithinAt_of_integral_mul_deriv_add_mul_nonneg (hx : x₀ < x₁)
    (hlam : 0 < lam) (hu : ContinuousOn u (Ico x₀ x₁)) (hu₀ : u x₀ = 0)
    (hpos : ∀ x ∈ Ioo x₀ x₁, 0 < u x)
    (hu' : HasWeakLineDerivOn volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ u u' 1)
    (hu'i : IntegrableOn u' (Ioo x₀ x₁))
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haΛ : ∀ᵐ x ∂volume.restrict (Ioo x₀ x₁), lam ≤ a x ∧ a x ≤ Λ)
    (hb : AEStronglyMeasurable b (volume.restrict (Ioo x₀ x₁)))
    (hbM : ∀ᵐ x ∂volume.restrict (Ioo x₀ x₁), |b x| ≤ M)
    (hc : AEStronglyMeasurable c (volume.restrict (Ioo x₀ x₁)))
    (hcM : ∀ᵐ x ∂volume.restrict (Ioo x₀ x₁), |c x| ≤ M) (hd : IntegrableOn d (Ioo x₀ x₁))
    (hsuper : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo x₀ x₁ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, ((a x * u' x + b x * u x) * deriv ψ x + (c x * u' x + d x * u x) * ψ x))
    {u₀' : ℝ} (hderiv : HasDerivWithinAt u u₀' (Ici x₀) x₀) : 0 < u₀' := by
  obtain ⟨κ, hκ, δ, hδ, h⟩ := exists_pos_mul_le_of_integral_mul_deriv_add_mul_nonneg hx hlam hu
    hu₀ hpos hu' hu'i ha haΛ hb hbM hc hcM hd hsuper
  have hslope := hasDerivWithinAt_iff_tendsto_slope.mp hderiv
  rw [Ici_sdiff_left] at hslope
  refine hκ.trans_le (ge_of_tendsto hslope ?_)
  -- For `x₀ < t < x₀ + δ` the slope at `x₀` is the difference quotient `u t / (t - x₀)`.
  filter_upwards [Ioo_mem_nhdsGT (lt_add_of_pos_right x₀ hδ)] with t ht
  have h' := h (t - x₀) ⟨sub_pos.2 ht.1, by linarith [ht.2]⟩
  rw [add_sub_cancel] at h'
  rwa [slope_def_field, hu₀, sub_zero, le_div_iff₀ (sub_pos.2 ht.1)]

end TauCeti.PDE
