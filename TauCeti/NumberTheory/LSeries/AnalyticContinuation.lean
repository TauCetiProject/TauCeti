/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.Convex.Topology
import Mathlib.NumberTheory.LSeries.Deriv
public import TauCeti.NumberTheory.LSeries.EntireExtension

/-!
# Analytic continuations of an L-series to a connected open set

An L-series `LSeries a` is analytic on its half-plane of absolute convergence
`{s | abscissaOfAbsConv a < s.re}`. A statement about the behaviour of `LSeries a` at a point
outside that half-plane, such as its order of vanishing at `s = 1`, needs an analytic function
on a larger region that agrees with the series where the series converges.
`LSeries.IsAnalyticContinuation a f U` says that `f` is such a function on the connected open set
`U`: it is analytic on `U`, `U` meets the half-plane, and `f` agrees with `LSeries a` on the part
of the half-plane inside `U`.

Merely asking for a function analytic near a point says nothing about the series, since any germ
qualifies; asking for a connected domain that meets the half-plane is what ties the continuation
to the actual Dirichlet series. Indeed two continuations on the same `U` coincide on `U`, so the
germ of a continuation at each point of `U`, and hence its order of vanishing and Taylor
coefficients there, depend only on `U` and the coefficients `a`.

This is weaker than `LSeries.HasEntireExtension`, which asks for an entire function: an entire
extension continues the series to every connected open set meeting the half-plane.

## Main definitions

* `LSeries.IsAnalyticContinuation a f U`: `f` is an analytic continuation of `LSeries a` to the
  connected open set `U`.

## Main results

* `LSeries.IsAnalyticContinuation.eqOn`: two continuations to the same set agree on it.
* `LSeries.IsAnalyticContinuation.eventuallyEq`: hence they have the same germ at each point
  of the set.
* `LSeries.IsAnalyticContinuation.mono`: a continuation restricts to every connected open subset
  still meeting the half-plane.
* `LSeries.isAnalyticContinuation_LSeries`: the L-series continues itself to every connected open
  subset of its half-plane of absolute convergence.
* `LSeries.HasEntireExtension.exists_isAnalyticContinuation_univ`: a series with an entire
  extension has a continuation to all of `ℂ`.
-/

public section

namespace LSeries

open Filter Set Topology

/-- `f` is an **analytic continuation** of the L-series `LSeries a` to the set `U`: `U` is open
and preconnected, `f` is analytic on `U`, `U` meets the half-plane of absolute convergence
`{s | abscissaOfAbsConv a < s.re}`, and `f` agrees with `LSeries a` on the part of that
half-plane inside `U`. -/
structure IsAnalyticContinuation (a : ℕ → ℂ) (f : ℂ → ℂ) (U : Set ℂ) : Prop where
  /-- The domain of the continuation is open. -/
  isOpen : IsOpen U
  /-- The domain of the continuation is preconnected. -/
  isPreconnected : IsPreconnected U
  /-- The continuation is analytic on its domain. -/
  analyticOnNhd : AnalyticOnNhd ℂ f U
  /-- The domain meets the half-plane of absolute convergence. -/
  nonempty_inter : (U ∩ {s : ℂ | abscissaOfAbsConv a < s.re}).Nonempty
  /-- The continuation agrees with the L-series where both are defined. -/
  eqOn_LSeries : EqOn f (LSeries a) (U ∩ {s : ℂ | abscissaOfAbsConv a < s.re})

/-- The half-plane of absolute convergence of an L-series is open. -/
theorem isOpen_setOf_abscissaOfAbsConv_lt_re (a : ℕ → ℂ) :
    IsOpen {s : ℂ | abscissaOfAbsConv a < s.re} :=
  isOpen_lt continuous_const (continuous_coe_real_ereal.comp Complex.continuous_re)

/-- **The L-series continues itself** to every nonempty connected open subset of its half-plane
of absolute convergence. -/
theorem isAnalyticContinuation_LSeries {a : ℕ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hU' : IsPreconnected U) (hne : U.Nonempty)
    (hsub : U ⊆ {s : ℂ | abscissaOfAbsConv a < s.re}) :
    IsAnalyticContinuation a (LSeries a) U where
  isOpen := hU
  isPreconnected := hU'
  analyticOnNhd := (LSeries_analyticOnNhd a).mono hsub
  nonempty_inter := by rwa [inter_eq_left.mpr hsub]
  eqOn_LSeries := eqOn_refl _ _

namespace IsAnalyticContinuation

variable {a : ℕ → ℂ} {f g : ℂ → ℂ} {U V : Set ℂ}

/-- **Uniqueness of analytic continuation**: two continuations of the same L-series to the same
connected open set agree on it. -/
theorem eqOn (hf : IsAnalyticContinuation a f U) (hg : IsAnalyticContinuation a g U) :
    EqOn f g U := by
  obtain ⟨z₀, hz₀⟩ := hf.nonempty_inter
  have hfg : f =ᶠ[𝓝 z₀] g :=
    eventuallyEq_iff_exists_mem.mpr ⟨_, (hf.isOpen.inter
      (isOpen_setOf_abscissaOfAbsConv_lt_re a)).mem_nhds hz₀,
        fun z hz ↦ (hf.eqOn_LSeries hz).trans (hg.eqOn_LSeries hz).symm⟩
  exact hf.analyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hg.analyticOnNhd hf.isPreconnected
    hz₀.1 hfg

/-- Two continuations of the same L-series to the same set have the same germ at every point of
that set, so they have the same order of vanishing and the same Taylor coefficients there. -/
theorem eventuallyEq (hf : IsAnalyticContinuation a f U) (hg : IsAnalyticContinuation a g U)
    {s : ℂ} (hs : s ∈ U) : f =ᶠ[𝓝 s] g :=
  eventuallyEq_iff_exists_mem.mpr ⟨U, hf.isOpen.mem_nhds hs, hf.eqOn hg⟩

/-- A continuation restricts to every connected open subset of its domain that still meets the
half-plane of absolute convergence. -/
theorem mono (hf : IsAnalyticContinuation a f U) (hVU : V ⊆ U) (hV : IsOpen V)
    (hV' : IsPreconnected V) (hne : (V ∩ {s : ℂ | abscissaOfAbsConv a < s.re}).Nonempty) :
    IsAnalyticContinuation a f V where
  isOpen := hV
  isPreconnected := hV'
  analyticOnNhd := hf.analyticOnNhd.mono hVU
  nonempty_inter := hne
  eqOn_LSeries := hf.eqOn_LSeries.mono (inter_subset_inter_left _ hVU)

/-- A continuation is analytic at every point of its domain. -/
theorem analyticAt (hf : IsAnalyticContinuation a f U) {s : ℂ} (hs : s ∈ U) :
    AnalyticAt ℂ f s :=
  hf.analyticOnNhd s hs

end IsAnalyticContinuation

/-- An entire function extending `LSeries a` on its half-plane of absolute convergence is an
analytic continuation of the series to every connected open set meeting that half-plane. -/
theorem isAnalyticContinuation_of_differentiable {a : ℕ → ℂ} {F : ℂ → ℂ} {U : Set ℂ}
    (hF : Differentiable ℂ F) (hFa : ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → F s = LSeries a s)
    (hU : IsOpen U) (hU' : IsPreconnected U)
    (hne : (U ∩ {s : ℂ | abscissaOfAbsConv a < s.re}).Nonempty) :
    IsAnalyticContinuation a F U where
  isOpen := hU
  isPreconnected := hU'
  analyticOnNhd := (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF).mono (subset_univ U)
  nonempty_inter := hne
  eqOn_LSeries := fun _ hs ↦ hFa hs.2

/-- A series with an entire extension has an analytic continuation to all of `ℂ`. -/
theorem HasEntireExtension.exists_isAnalyticContinuation_univ {a : ℕ → ℂ}
    (h : HasEntireExtension a) : ∃ F : ℂ → ℂ, IsAnalyticContinuation a F univ := by
  obtain ⟨F, hF, hFa⟩ := h.exists_extension
  obtain ⟨σ, hσ, -⟩ := EReal.exists_between_coe_real h.abscissa_lt_top
  refine ⟨F, isAnalyticContinuation_of_differentiable hF hFa isOpen_univ
    isPreconnected_univ ⟨((σ + 1 : ℝ) : ℂ), mem_univ _, ?_⟩⟩
  simp only [mem_ofPred_eq, Complex.ofReal_re]
  exact hσ.trans (by exact_mod_cast lt_add_one σ)

end LSeries
