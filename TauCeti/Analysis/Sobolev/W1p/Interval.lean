/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Zero
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Analysis.Sobolev.W1p.Extension
import TauCeti.Analysis.Sobolev.W1p.VanishingBoundary
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# `W^{1,p}_0` on a bounded interval

On an interval `(a, b)` of the real line, a function `u ∈ W^{1,p}(a, b)` with weak derivative `u'`
lies in `W^{1,p}_0(a, b)` exactly when it is the primitive of `u'` from the left endpoint and
`u'` has integral zero:

`u t = ∫ s in a..t, u' s` for almost every `t ∈ (a, b)`, and `∫ s in a..b, u' s = 0`.

So the continuous representative `t ↦ ∫ s in a..t, u' s` of `u` vanishes at both endpoints: on
the line, the closure of the test functions is cut out by the two classical boundary conditions
`u a = 0` and `u b = 0`. The forward direction holds for every `1 ≤ p ≤ ∞`; the converse needs
`p < ∞`, since for `p = ∞` the closure of the test functions is smaller.

This is the form of the zero boundary condition used for the one-dimensional Dirichlet problem,
whose solutions are written down by integrating twice.

## The argument

The zero-extension `u₀` of `u ∈ W^{1,p}_0(a, b)` is weakly differentiable on all of `ℝ`, with weak
derivative the zero-extension of `u'` (`TauCeti.W1p0.hasWeakFDerivOn_indicator`), so by the
fundamental theorem of calculus for weak derivatives `u₀ t = c + ∫ s in a..t, u₀' s` almost
everywhere on `ℝ`. To the left of `a` both `u₀` and the integral vanish, which forces `c = 0`.
The integral of `u'` vanishes by `TauCeti.W1p0.setIntegral_inner_gradient_eq_zero`. Conversely
the primitive is continuous on `[a, b]` and vanishes at `a` and `b`, so
`TauCeti.W1p.mem_w1p0Submodule_of_continuousOn_closure` applies.

## Main declarations

* `TauCeti.W1p.value_ae_eq_intervalIntegral_gradient_of_mem_w1p0Submodule`: a function of
  `W^{1,p}_0(a, b)` is the primitive from `a` of its weak derivative.
* `TauCeti.W1p.intervalIntegral_gradient_eq_zero_of_mem_w1p0Submodule`: the weak derivative of a
  function of `W^{1,p}_0(a, b)` has integral zero.
* `TauCeti.W1p.mem_w1p0Submodule_Ioo_iff`: for `p < ∞`, these two properties characterize
  `W^{1,p}_0(a, b)`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 8.12.
-/

public section

open MeasureTheory Set Filter TopologicalSpace intervalIntegral

namespace TauCeti

variable {a b : ℝ} {p : ENNReal} [Fact (1 ≤ p)]

/-- **A function of `W^{1,p}_0(a, b)` is the primitive of its weak derivative from `a`.** If
`u ∈ W^{1,p}_0(a, b)`, then `u t = ∫ s in a..t, u' s` for almost every `t ∈ (a, b)`, where `u'`
is the weak derivative `TauCeti.W1p.gradient u`. -/
theorem W1p.value_ae_eq_intervalIntegral_gradient_of_mem_w1p0Submodule
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p}
    (hu : u ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    W1p.value u =ᵐ[volume.restrict (Ioo a b)] fun t => ∫ s in a..t, W1p.gradient u s := by
  -- The zero-extension is weakly differentiable on the whole line.
  have hv : HasWeakLineDerivOn volume ⊤ ((Ioo a b).indicator (W1p.value u))
      ((Ioo a b).indicator (W1p.gradient u)) 1 := by
    simpa using
      (W1p0.hasWeakFDerivOn_indicator (Omega' := ⊤) le_top ⟨u, hu⟩).hasWeakLineDerivOn 1
  obtain ⟨c, hc⟩ := hv.exists_ae_eq_add_intervalIntegral_top a
  -- To the left of `a`, both the extension and its primitive from `a` vanish, so `c = 0`.
  have hleft : ∀ t ≤ a, ∫ s in a..t, (Ioo a b).indicator (W1p.gradient u) s = 0 := fun t ht => by
    refine (integral_congr fun s hs => ?_).trans integral_zero
    rw [uIcc_of_ge ht] at hs
    exact indicator_of_notMem (fun h : s ∈ Ioo a b => h.1.not_ge hs.2) _
  have hc0 : c = 0 := by
    have : (ae (volume.restrict (Ioo (a - 1) a))).NeBot := ae_restrict_neBot.2 (by simp)
    obtain ⟨t, ht, htI⟩ := ((ae_restrict_of_ae (s := Ioo (a - 1) a) hc).and
      (ae_restrict_mem (μ := volume) measurableSet_Ioo)).exists
    dsimp only at ht
    rw [hleft t htI.2.le, add_zero,
      indicator_of_notMem (fun h : t ∈ Ioo a b => h.1.not_gt htI.2)] at ht
    exact ht.symm
  filter_upwards [ae_restrict_of_ae hc, ae_restrict_mem measurableSet_Ioo] with t ht htI
  rw [indicator_of_mem htI, hc0, zero_add] at ht
  rw [ht]
  refine integral_congr_ae (ae_of_all _ fun s hs => ?_)
  rw [uIoc_of_le htI.1.le] at hs
  exact indicator_of_mem (⟨hs.1, hs.2.trans_lt htI.2⟩ : s ∈ Ioo a b) _

/-- **The weak derivative of a function of `W^{1,p}_0(a, b)` has integral zero.** -/
theorem W1p.intervalIntegral_gradient_eq_zero_of_mem_w1p0Submodule (hab : a ≤ b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p}
    (hu : u ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    ∫ s in a..b, W1p.gradient u s = 0 := by
  have h := W1p0.setIntegral_inner_gradient_eq_zero (Omega := ⟨Ioo a b, isOpen_Ioo⟩)
    (by simpa using Metric.isBounded_Ioo a b) ⟨u, hu⟩ 1
  rw [integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  simpa using h

/-- **`W^{1,p}_0` on an interval.** For `a < b` and `p < ∞`, a function `u ∈ W^{1,p}(a, b)` with
weak derivative `u'` lies in `W^{1,p}_0(a, b)` exactly when `u t = ∫ s in a..t, u' s` for almost
every `t ∈ (a, b)` and `∫ s in a..b, u' s = 0`: its continuous representative vanishes at both
endpoints. -/
theorem W1p.mem_w1p0Submodule_Ioo_iff (hp : p ≠ ⊤) (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    u ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p ↔
      (W1p.value u =ᵐ[volume.restrict (Ioo a b)] fun t => ∫ s in a..t, W1p.gradient u s) ∧
        ∫ s in a..b, W1p.gradient u s = 0 := by
  refine ⟨fun hu => ⟨W1p.value_ae_eq_intervalIntegral_gradient_of_mem_w1p0Submodule hu,
    W1p.intervalIntegral_gradient_eq_zero_of_mem_w1p0Submodule hab.le hu⟩, fun ⟨hv, h0⟩ => ?_⟩
  have : IsFiniteMeasure (volume.restrict ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) :=
    Real.isFiniteMeasure_restrict_Ioo a b
  have hint : IntegrableOn (W1p.gradient u) (Ioo a b) :=
    (Lp.memLp (W1p.gradient u)).integrable Fact.out
  refine W1p.mem_w1p0Submodule_of_continuousOn_closure hp (by simpa using Metric.isBounded_Ioo a b)
    (g := fun t => ∫ s in a..t, W1p.gradient u s) ?_ ?_ (by simpa using hv)
  · simpa [closure_Ioo hab.ne] using
      TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hint
        (left_mem_Icc.2 hab.le)
  · intro t ht
    simp only [Opens.coe_mk, frontier_Ioo hab, mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact integral_same
    · exact h0

end TauCeti
