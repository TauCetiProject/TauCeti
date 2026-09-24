/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import TauCeti.Analysis.Calculus.TaylorIntegral

/-!
# Necessary second-derivative tests

This file records necessary versions of Mathlib's sufficient second-derivative tests. At a local
maximum of a continuous real-valued function, the value `deriv (deriv g) t₀` is nonpositive; at a
local minimum it is nonnegative. On a real normed space the same holds for every diagonal entry
`fderiv ℝ (fderiv ℝ f) x w w` of the Hessian of a `C²` function at a local extremum.

## Main declarations

* `TauCeti.deriv_deriv_nonpos_of_isLocalMax`: the local-maximum version.
* `TauCeti.deriv_deriv_nonneg_of_isLocalMin`: the local-minimum version.
* `TauCeti.fderiv_fderiv_self_nonpos_of_isLocalMax` /
  `TauCeti.fderiv_fderiv_self_nonneg_of_isLocalMin`: the Hessian is negative (resp. positive)
  semidefinite on the diagonal at a local maximum (resp. minimum).
-/

public section

namespace TauCeti

open Topology

/-- **Necessary second-derivative test.** At a local maximum of a continuous function
`g : ℝ → ℝ`, the value `deriv (deriv g) t₀` is nonpositive. -/
theorem deriv_deriv_nonpos_of_isLocalMax {g : ℝ → ℝ} {t₀ : ℝ}
    (hg : ContinuousAt g t₀) (hmax : IsLocalMax g t₀) :
    deriv (deriv g) t₀ ≤ 0 := by
  by_contra h
  rw [not_le] at h
  have hd : deriv g t₀ = 0 := hmax.deriv_eq_zero
  have hmin : IsLocalMin g t₀ := isLocalMin_of_deriv_deriv_pos h hd hg
  -- Being both a local minimum and a local maximum, `g` is eventually constant near `t₀`.
  have hconst : g =ᶠ[𝓝 t₀] fun _ => g t₀ := by
    filter_upwards [hmax, hmin] with y hy hy' using le_antisymm hy hy'
  have hderiv : deriv g =ᶠ[𝓝 t₀] fun _ => (0 : ℝ) := by
    filter_upwards [hconst.deriv] with y hy
    simpa using hy
  have hzero : deriv (deriv g) t₀ = 0 := by
    rw [hderiv.deriv_eq]; simp
  linarith

/-- **Necessary second-derivative test, minimum version.** At a local minimum of a continuous
function `g : ℝ → ℝ`, the value `deriv (deriv g) t₀` is nonnegative. -/
theorem deriv_deriv_nonneg_of_isLocalMin {g : ℝ → ℝ} {t₀ : ℝ}
    (hg : ContinuousAt g t₀) (hmin : IsLocalMin g t₀) :
    0 ≤ deriv (deriv g) t₀ := by
  have := deriv_deriv_nonpos_of_isLocalMax (g := -g) hg.neg hmin.neg
  simpa using this

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}

/-- At a local maximum of a `C²` function `f : E → ℝ`, every diagonal Hessian entry is
nonpositive. -/
theorem fderiv_fderiv_self_nonpos_of_isLocalMax (hf : ContDiffAt ℝ 2 f x) (hmax : IsLocalMax f x)
    (w : E) : fderiv ℝ (fderiv ℝ f) x w w ≤ 0 := by
  have hf' : ContDiffAt ℝ 2 f (x + (0 : ℝ) • w) := by simpa using hf
  have hline : ContinuousAt (fun t : ℝ => x + t • w) 0 := by fun_prop
  have h := deriv_deriv_nonpos_of_isLocalMax
    (hf'.continuousAt.comp (f := fun t : ℝ => x + t • w) hline)
    ((by simpa using hmax : IsLocalMax f (x + (0 : ℝ) • w)).comp_continuous
      (g := fun t : ℝ => x + t • w) hline)
  rwa [Function.comp_def, hf'.deriv_deriv_comp_add_smul, zero_smul, add_zero] at h

/-- At a local minimum of a `C²` function `f : E → ℝ`, every diagonal Hessian entry is
nonnegative. -/
theorem fderiv_fderiv_self_nonneg_of_isLocalMin (hf : ContDiffAt ℝ 2 f x) (hmin : IsLocalMin f x)
    (w : E) : 0 ≤ fderiv ℝ (fderiv ℝ f) x w w := by
  have hf' : ContDiffAt ℝ 2 f (x + (0 : ℝ) • w) := by simpa using hf
  have hline : ContinuousAt (fun t : ℝ => x + t • w) 0 := by fun_prop
  have h := deriv_deriv_nonneg_of_isLocalMin
    (hf'.continuousAt.comp (f := fun t : ℝ => x + t • w) hline)
    ((by simpa using hmin : IsLocalMin f (x + (0 : ℝ) • w)).comp_continuous
      (g := fun t : ℝ => x + t • w) hline)
  rwa [Function.comp_def, hf'.deriv_deriv_comp_add_smul, zero_smul, add_zero] at h

end NormedSpace

end TauCeti
