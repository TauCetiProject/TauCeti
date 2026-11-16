/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HalfPlane

/-!
# Meromorphy of the totalized Dirichlet series

`LSeries a` is zero where its defining series is not summable. Consequently, it cannot be
meromorphic on its finite abscissa of absolute convergence: a meromorphic germ there would
propagate the zero values on the left into the convergence half-plane on the right, forcing
all coefficients away from zero to vanish. In particular, local meromorphy of the totalized
series implies analyticity, and half-plane meromorphy bounds any non-top abscissa.

These statements concern the totalized series, not an arbitrary meromorphic continuation.
-/

public section

open Complex Filter LSeries Set Topology

variable {a : ℕ → ℂ} {s : ℂ}

private theorem TauCeti.LSeries.zero_germ_at_abscissa (hm : MeromorphicAt (LSeries a) s)
    (hσ : abscissaOfAbsConv a = (s.re : EReal)) : LSeries a =ᶠ[𝓝[≠] s] 0 := by
  -- The zero values to the left exclude a nonvanishing meromorphic germ at the boundary.
  rcases hm.eventually_eq_zero_or_eventually_ne_zero with hz | hn
  · exact hz
  · obtain ⟨ε, hε, hn⟩ := Metric.mem_nhdsWithin_iff.mp hn
    have hd : dist (s - (ε / 2 : ℝ)) s < ε := by
      simp only [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_real,
        Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      linarith
    have hne : s - (ε / 2 : ℝ) ≠ s := by
      intro h
      have := congrArg Complex.re h
      simp only [sub_re, ofReal_re] at this
      linarith
    exfalso
    apply hn ⟨hd, hne⟩
    exact eq_zero_of_not_LSeriesSummable a _ fun hsum ↦ by
      have := hsum.abscissaOfAbsConv_le
      rw [hσ] at this
      have := EReal.coe_le_coe_iff.mp this
      simp only [sub_re, ofReal_re] at this
      linarith

/-- The totalized Dirichlet series is not meromorphic on its finite abscissa of absolute
convergence. -/
theorem MeromorphicAt.abscissaOfAbsConv_ne_re (hm : MeromorphicAt (LSeries a) s) :
    abscissaOfAbsConv a ≠ (s.re : EReal) := by
  intro hσ
  -- Propagate the zero germ through the convergence half-plane and use series injectivity.
  obtain ⟨ε, hε, hz⟩ := Metric.mem_nhdsWithin_iff.mp
    (TauCeti.LSeries.zero_germ_at_abscissa hm hσ)
  let t : ℂ := s + (ε / 2 : ℝ)
  have ht : s.re < t.re := by
    simp only [t, add_re, ofReal_re]
    linarith
  have hdt : dist t s < ε := by
    simp only [t, dist_eq_norm, add_sub_cancel_left, norm_real,
      Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hne : t ≠ s := fun h ↦ (ne_of_gt ht) (congrArg Complex.re h)
  have heq : LSeries a =ᶠ[𝓝 t] 0 :=
    eventuallyEq_of_mem ((Metric.isOpen_ball.inter isClosed_singleton.isOpen_compl).mem_nhds
      ⟨hdt, hne⟩) fun z hz' ↦ hz hz'
  have hzero : EqOn (LSeries a) 0 {z : ℂ | s.re < z.re} :=
    ((LSeries_analyticOnNhd a).mono (fun z hz ↦ by simpa only [hσ,
      EReal.coe_lt_coe_iff] using hz)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_halfSpace_re_gt s.re).isPreconnected ht heq
  have hev : (fun x : ℝ ↦ LSeries a x) =ᶠ[atTop] 0 :=
    (eventually_gt_atTop s.re).mono fun x hx ↦
      hzero (by simpa only [mem_ofPred_eq, ofReal_re] using hx)
  have ha := (LSeries_eventually_eq_zero_iff'.mp hev).resolve_right
    (by simp only [hσ, EReal.coe_ne_top, not_false_eq_true])
  have hsum : LSeriesSummable a (s.re - 1 : ℝ) := by
    exact (LSeriesSummable_congr (f := 0) _ (fun {n} hn ↦ (ha n hn).symm)).mp
      LSeriesSummable_zero
  have := hsum.abscissaOfAbsConv_le
  rw [hσ] at this
  have := EReal.coe_le_coe_iff.mp this
  simp only [ofReal_re] at this
  linarith

/-- Local meromorphy of the totalized Dirichlet series implies analyticity, including its
zero values to the left of the convergence half-plane. -/
theorem MeromorphicAt.analyticAt_LSeries (hm : MeromorphicAt (LSeries a) s) :
    AnalyticAt ℂ (LSeries a) s := by
  rcases lt_or_gt_of_ne hm.abscissaOfAbsConv_ne_re with hs | hs
  · exact LSeries_analyticOnNhd a s hs
  · apply (analyticAt_const (v := (0 : ℂ))).congr
    filter_upwards [((Complex.isOpen_re_lt_EReal _).mem_nhds hs)] with z hz
    exact (eq_zero_of_not_LSeriesSummable a z fun hsum ↦
      (not_le_of_gt hz) hsum.abscissaOfAbsConv_le).symm

/-- Meromorphy of the totalized series on a right half-plane bounds its abscissa of absolute
convergence, unless the abscissa is `⊤` and the series is identically zero. -/
theorem MeromorphicOn.abscissaOfAbsConv_le {c : ℝ}
    (hm : MeromorphicOn (LSeries a) {z | c < z.re}) (htop : abscissaOfAbsConv a ≠ ⊤) :
    abscissaOfAbsConv a ≤ c := by
  by_contra hc
  have hr := EReal.coe_toReal htop (ne_bot_of_gt (lt_of_not_ge hc))
  let r := (abscissaOfAbsConv a).toReal
  have hcr : c < r := EReal.coe_lt_coe_iff.mp (hr.symm ▸ lt_of_not_ge hc)
  exact (hm r (by simpa using hcr)).abscissaOfAbsConv_ne_re hr.symm
