/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Injectivity
public import TauCeti.NumberTheory.LSeries.EntireExtension

/-!
# Analytic continuations of an L-series to a connected open set

An L-series `LSeries a s = ∑ a n / n ^ s` is guaranteed to be a holomorphic function on its open
half-plane of absolute convergence `abscissaOfAbsConv a < re s`. A statement about its value or its
order of vanishing at a point where convergence of the series is not established has to name a
continuation. Merely asking for a function analytic near the point says nothing, since any germ
would do; the continuation must be tied to the series. `LSeries.IsContinuationOn a F U` says that
`F` is analytic on a connected open set `U` that meets the half-plane of absolute convergence, and
that `F` agrees with the series on the part of `U` lying in that half-plane.

By the identity theorem such a continuation is determined by `a` on its domain, and agrees there
with any continuation to a larger domain, in particular with an entire extension
(`LSeries.IsContinuationOn.eqOn_of_subset`). When some coefficient `a n` with `n ≠ 0` is nonzero it
vanishes to finite order at every point of its domain
(`LSeries.IsContinuationOn.analyticOrderAt_ne_top`), so its order of vanishing there is a natural
number.

## Main definitions

* `LSeries.IsContinuationOn a F U`: `F` is an analytic continuation of `LSeries a` to `U`.

## Main results

* `LSeries.isContinuationOn_LSeries`: the series itself, on its half-plane of absolute
  convergence.
* `LSeries.HasEntireExtension.exists_isContinuationOn_univ`: an entire extension gives a
  continuation to all of `ℂ`.
* `LSeries.IsContinuationOn.eqOn_of_subset`: a continuation to `U` agrees on `U` with every
  continuation to a larger set.
* `LSeries.IsContinuationOn.analyticOrderAt_ne_top`: a continuation of a nonzero series vanishes
  to finite order at each point of its domain.
-/

public section

namespace LSeries

open Filter Topology

/-- `F` is an **analytic continuation of the L-series** `LSeries a` to `U`: the set `U` is open
and connected and meets the open half-plane of absolute convergence of `a`, `F` is analytic on
`U`, and `F` agrees with `LSeries a` on the part of `U` in that half-plane. -/
structure IsContinuationOn (a : ℕ → ℂ) (F : ℂ → ℂ) (U : Set ℂ) : Prop where
  /-- The domain of the continuation is open. -/
  isOpen : IsOpen U
  /-- The domain of the continuation is connected. -/
  isPreconnected : IsPreconnected U
  /-- The continuation is analytic on its domain. -/
  analyticOnNhd : AnalyticOnNhd ℂ F U
  /-- The domain meets the half-plane of absolute convergence. -/
  exists_mem_abscissaOfAbsConv_lt_re : ∃ s ∈ U, abscissaOfAbsConv a < s.re
  /-- The continuation agrees with the series on the half-plane of absolute convergence. -/
  eq_LSeries : ∀ ⦃s⦄, s ∈ U → abscissaOfAbsConv a < s.re → F s = LSeries a s

variable {a : ℕ → ℂ} {F G : ℂ → ℂ} {U V : Set ℂ}

/-- **The series is a continuation of itself** on its half-plane of absolute convergence, when
that half-plane is nonempty. -/
theorem isContinuationOn_LSeries (ha : abscissaOfAbsConv a < ⊤) :
    IsContinuationOn a (LSeries a) {s | abscissaOfAbsConv a < s.re} := by
  obtain ⟨σ, hσ, -⟩ := EReal.exists_between_coe_real ha
  refine ⟨Complex.isOpen_re_gt_EReal _, ?_, LSeries_analyticOnNhd a,
    ⟨(σ : ℂ), by simpa using hσ, by simpa using hσ⟩, fun _ _ _ ↦ rfl⟩
  induction h : abscissaOfAbsConv a with
  | bot => simpa using isPreconnected_univ
  | coe r => simpa using (convex_halfSpace_re_gt r).isPreconnected
  | top => exact absurd h ha.ne

/-- **An entire extension is a continuation to all of `ℂ`.** -/
theorem HasEntireExtension.exists_isContinuationOn_univ (h : HasEntireExtension a) :
    ∃ F, IsContinuationOn a F Set.univ := by
  obtain ⟨F, hF, hFa⟩ := h.exists_extension
  obtain ⟨σ, hσ, -⟩ := EReal.exists_between_coe_real h.abscissa_lt_top
  exact ⟨F, isOpen_univ, isPreconnected_univ, Complex.analyticOnNhd_univ_iff_differentiable.mpr hF,
    ⟨σ, Set.mem_univ _, by simpa using hσ⟩, fun s _ hs ↦ hFa hs⟩

namespace IsContinuationOn

/-- The half-plane of absolute convergence of a series with a continuation is nonempty. -/
theorem abscissaOfAbsConv_lt_top (h : IsContinuationOn a F U) : abscissaOfAbsConv a < ⊤ := by
  obtain ⟨s, -, hs⟩ := h.exists_mem_abscissaOfAbsConv_lt_re
  exact hs.trans (EReal.coe_lt_top _)

/-- Near a point of its domain in the half-plane of absolute convergence, a continuation agrees
with the series. -/
theorem eventuallyEq_LSeries (h : IsContinuationOn a F U) {s : ℂ} (hs : s ∈ U)
    (hsa : abscissaOfAbsConv a < s.re) : F =ᶠ[𝓝 s] LSeries a :=
  Filter.eventuallyEq_of_mem ((h.isOpen.inter (Complex.isOpen_re_gt_EReal _)).mem_nhds ⟨hs, hsa⟩)
    fun _ hz ↦ h.eq_LSeries hz.1 hz.2

/-- **Uniqueness of continuations**: a continuation of `LSeries a` to `U` agrees on `U` with any
continuation of `LSeries a` to a set containing `U`. -/
theorem eqOn_of_subset (hF : IsContinuationOn a F U) (hG : IsContinuationOn a G V) (hUV : U ⊆ V) :
    Set.EqOn F G U := by
  obtain ⟨s, hs, hsa⟩ := hF.exists_mem_abscissaOfAbsConv_lt_re
  exact hF.analyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd.mono hUV)
    hF.isPreconnected hs
    ((hF.eventuallyEq_LSeries hs hsa).trans (hG.eventuallyEq_LSeries (hUV hs) hsa).symm)

/-- **A continuation of a nonzero series vanishes to finite order** at every point of its domain,
when some coefficient `a n` with `n ≠ 0` is nonzero. -/
theorem analyticOrderAt_ne_top (h : IsContinuationOn a F U) (ha : ∃ n ≠ 0, a n ≠ 0) {s : ℂ}
    (hs : s ∈ U) : analyticOrderAt F s ≠ ⊤ := by
  -- If `F` vanished identically near a point of the connected set `U`, the series would vanish on
  -- an open subset of its half-plane of absolute convergence, hence on a right half-plane, which
  -- forces every coefficient `a n` with `n ≠ 0` to vanish.
  obtain ⟨s₀, hs₀, hs₀a⟩ := h.exists_mem_abscissaOfAbsConv_lt_re
  refine h.analyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected h.isPreconnected hs₀ hs ?_
  intro htop
  obtain ⟨σ, hσ, hσs₀⟩ := EReal.exists_between_coe_real hs₀a
  -- The series vanishes near `s₀`, hence on the right half-plane `σ < re z`.
  have hsub : {z : ℂ | σ < z.re} ⊆ {z | abscissaOfAbsConv a < z.re} :=
    fun z (hz : σ < z.re) ↦ hσ.trans (by exact_mod_cast hz)
  have hzero : Set.EqOn (LSeries a) 0 {z : ℂ | σ < z.re} :=
    ((LSeries_analyticOnNhd a).mono hsub).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_halfSpace_re_gt σ).isPreconnected (by exact_mod_cast hσs₀)
      ((h.eventuallyEq_LSeries hs₀ hs₀a).symm.trans (analyticOrderAt_eq_top.mp htop))
  have hev : (fun x : ℝ ↦ LSeries a x) =ᶠ[atTop] 0 :=
    (eventually_gt_atTop σ).mono fun x hx ↦ hzero (by simpa using hx)
  obtain ⟨n, hn, han⟩ := ha
  exact (LSeries_eventually_eq_zero_iff'.mp hev).elim (fun h ↦ han (h n hn))
    h.abscissaOfAbsConv_lt_top.ne

end IsContinuationOn

end LSeries
