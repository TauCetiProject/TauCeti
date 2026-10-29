/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Conjugation of complex divided differences

Local conjugation symmetry at a real centre passes to the divided difference, including
its derivative value at the centre. A complex normalization constant is allowed: this is
useful when a holomorphic regular factor carries a fixed complex phase.
-/

public section

open Complex Filter Topology
open scoped ComplexConjugate

namespace TauCeti

/-- Dividing a function by a constant and taking its divided difference at a real centre
preserves local conjugation symmetry. No differentiability assumption is needed: at the
centre, conjugation also respects the convention that the derivative is zero when absent. -/
theorem eventually_dslope_div_const_conj {f : ℂ → ℂ} (p : ℝ) (c : ℂ)
    (hf : ∀ᶠ z in 𝓝 (p : ℂ), f (conj z) / c = conj (f z / c)) :
    ∀ᶠ z in 𝓝 (p : ℂ),
      dslope f (p : ℂ) (conj z) / c = conj (dslope f (p : ℂ) z / c) := by
  by_cases hc : c = 0
  · simp [hc]
  have hp : f p / c = conj (f p / c) := by
    simpa only [conj_ofReal] using hf.self_of_nhds
  have hevent : (fun z => conj (f (conj z) / c)) =ᶠ[𝓝 (p : ℂ)]
      (fun z => f z / c) := hf.mono fun z hz => by
        simpa only [conj_conj] using congrArg conj hz
  have hd := hevent.deriv_eq
  rw [deriv_div_const] at hd
  have hdconj := congrFun (deriv_conj_conj (f := fun z => f z / c)) (p : ℂ)
  have hdreal : deriv f (p : ℂ) / c = conj (deriv f (p : ℂ) / c) :=
    hd.symm.trans (by simpa only [Function.comp_def, conj_ofReal, deriv_div_const]
      using hdconj)
  filter_upwards [hf] with z hz
  rcases eq_or_ne z (p : ℂ) with rfl | hzp
  · simpa only [conj_ofReal, dslope_same] using hdreal
  · have hczp : conj z ≠ (p : ℂ) := by
      intro h
      exact hzp (by simpa only [conj_conj, conj_ofReal] using congrArg conj h)
    simp only [dslope_of_ne _ hzp, dslope_of_ne _ hczp, slope_def_field]
    calc
      (f (conj z) - f p) / (conj z - (p : ℂ)) / c =
          (f (conj z) / c - f p / c) / (conj z - (p : ℂ)) := by field_simp
      _ = (conj (f z / c) - conj (f p / c)) / (conj z - (p : ℂ)) :=
        congrArg₂ (fun x y : ℂ => (x - y) / (conj z - (p : ℂ))) hz hp
      _ = conj ((f z / c - f p / c) / (z - (p : ℂ))) := by simp
      _ = conj ((f z - f p) / (z - (p : ℂ)) / c) := by congr 1; field_simp

end TauCeti
