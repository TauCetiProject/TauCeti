/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import TauCeti.Analysis.Calculus.TaylorIntegral

import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Necessary and strict derivative tests

This file records necessary versions of Mathlib's sufficient second-derivative tests. At a local
maximum of a continuous real-valued function, the value `deriv (deriv g) t₀` is nonpositive; at a
local minimum it is nonnegative. On a real normed space the same holds for every diagonal entry
`fderiv ℝ (fderiv ℝ f) x w w` of the Hessian of a `C²` function at a local extremum.

It also strengthens the conclusion of Mathlib's sufficient second-derivative test: at a critical
point `x₀` with `deriv (deriv f) x₀ > 0` the function has a *strict* local minimum,
`f x₀ < f x` for `x ≠ x₀` near `x₀`, and dually for `deriv (deriv f) x₀ < 0`. Strictness is what
the stability of an equilibrium at a minimum of the energy needs. This goes through a strict
version of Mathlib's first-derivative test `isLocalMin_of_sign_deriv`.

It also records the one-sided first-derivative tests at an endpoint: a function with a local
maximum on `Iic a` at `a` (a maximum *from the left*) has nonnegative left derivative there, and
dually for minima and for maxima and minima from the right on `Ici a`. The maximum from the left
is the time-direction step of the parabolic maximum principle, where the maximum may sit on the
top of the space-time cylinder.

## Main declarations

* `IsLocalMaxOn.hasDerivWithinAt_Iic_nonneg`: the left derivative at a maximum from the left is
  nonnegative.
* `IsLocalMinOn.hasDerivWithinAt_Iic_nonpos`, `IsLocalMaxOn.hasDerivWithinAt_Ici_nonpos`,
  `IsLocalMinOn.hasDerivWithinAt_Ici_nonneg`: the dual endpoint tests.
* `TauCeti.eventually_lt_of_sign_deriv`: the strict first-derivative test.
* `TauCeti.eventually_nhdsGT_lt_of_deriv_pos`: its right-hand half, for a function with positive
  derivative just to the right of `x₀`.
* `TauCeti.eventually_lt_of_deriv_deriv_pos`, `TauCeti.eventually_gt_of_deriv_deriv_neg`: the
  strict second-derivative tests.
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

/-- **One-sided first-derivative test.** If `f : ℝ → ℝ` has a local maximum on `Iic a` at `a`,
that is a maximum from the left, then its left derivative at `a` is nonnegative. -/
theorem _root_.IsLocalMaxOn.hasDerivWithinAt_Iic_nonneg {f : ℝ → ℝ} {f' a : ℝ}
    (h : IsLocalMaxOn f (Set.Iic a) a) (hf : HasDerivWithinAt f f' (Set.Iic a) a) : 0 ≤ f' := by
  have hy : (-1 : ℝ) ∈ posTangentConeAt (Set.Iic a) a :=
    mem_posTangentConeAt_of_segment_subset <| by
      rw [segment_symm, segment_eq_Icc (by linarith)]
      exact Set.Icc_subset_Iic_self
  simpa using h.hasFDerivWithinAt_nonpos hf.hasFDerivWithinAt hy

/-- **One-sided first-derivative test, minimum version.** If `f : ℝ → ℝ` has a local minimum on
`Iic a` at `a`, then its left derivative at `a` is nonpositive. -/
theorem _root_.IsLocalMinOn.hasDerivWithinAt_Iic_nonpos {f : ℝ → ℝ} {f' a : ℝ}
    (h : IsLocalMinOn f (Set.Iic a) a) (hf : HasDerivWithinAt f f' (Set.Iic a) a) : f' ≤ 0 := by
  simpa using h.neg.hasDerivWithinAt_Iic_nonneg hf.neg

/-- **One-sided first-derivative test on the right.** If `f : ℝ → ℝ` has a local maximum on
`Ici a` at `a`, that is a maximum from the right, then its right derivative at `a` is
nonpositive. -/
theorem _root_.IsLocalMaxOn.hasDerivWithinAt_Ici_nonpos {f : ℝ → ℝ} {f' a : ℝ}
    (h : IsLocalMaxOn f (Set.Ici a) a) (hf : HasDerivWithinAt f f' (Set.Ici a) a) : f' ≤ 0 := by
  have hy : (1 : ℝ) ∈ posTangentConeAt (Set.Ici a) a :=
    mem_posTangentConeAt_of_segment_subset <| by
      rw [segment_eq_Icc (by linarith)]
      exact Set.Icc_subset_Ici_self
  simpa using h.hasFDerivWithinAt_nonpos hf.hasFDerivWithinAt hy

/-- **One-sided first-derivative test on the right, minimum version.** If `f : ℝ → ℝ` has a
local minimum on `Ici a` at `a`, then its right derivative at `a` is nonnegative. -/
theorem _root_.IsLocalMinOn.hasDerivWithinAt_Ici_nonneg {f : ℝ → ℝ} {f' a : ℝ}
    (h : IsLocalMinOn f (Set.Ici a) a) (hf : HasDerivWithinAt f f' (Set.Ici a) a) : 0 ≤ f' := by
  simpa using h.neg.hasDerivWithinAt_Ici_nonpos hf.neg

/-- **Strict first-derivative test, right-hand half.** If `f : ℝ → ℝ` is continuous at `x₀`
and has positive derivative just to the right of `x₀`, then `f x₀ < f x` just to the right of
`x₀`. -/
theorem eventually_nhdsGT_lt_of_deriv_pos {f : ℝ → ℝ} {x₀ : ℝ} (hc : ContinuousAt f x₀)
    (hf : ∀ᶠ x in 𝓝[>] x₀, 0 < deriv f x) : ∀ᶠ x in 𝓝[>] x₀, f x₀ < f x := by
  obtain ⟨b, hb, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hf
  -- `f` is strictly increasing on `[x₀, b)`: continuous there, with positive derivative inside.
  have hmono : StrictMonoOn f (Set.Ico x₀ b) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico _ _) (fun x hx ↦ ?_) fun x hx ↦ ?_
    · rcases hx.1.eq_or_lt with rfl | hlt
      · exact hc.continuousWithinAt
      · exact (differentiableAt_of_deriv_ne_zero (hsub ⟨hlt, hx.2⟩).ne').continuousAt
          |>.continuousWithinAt
    · rw [interior_Ico] at hx
      exact hsub hx
  filter_upwards [Ioo_mem_nhdsGT hb] with x hx
  exact hmono ⟨le_rfl, hb⟩ ⟨hx.1.le, hx.2⟩ hx.1

/-- **Strict first-derivative test.** If `f : ℝ → ℝ` is continuous at `x₀` and, near `x₀`, the
derivative of `f` has the sign of `x - x₀`, then `x₀` is a strict local minimum of `f`:
`f x₀ < f x` for every `x ≠ x₀` close to `x₀`. This strengthens Mathlib's
`isLocalMin_of_sign_deriv`. -/
theorem eventually_lt_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ} (hc : ContinuousAt f x₀)
    (hf : ∀ᶠ x in 𝓝[≠] x₀, SignType.sign (deriv f x) = SignType.sign (x - x₀)) :
    ∀ᶠ x in 𝓝[≠] x₀, f x₀ < f x := by
  rw [← nhdsLT_sup_nhdsGT, Filter.eventually_sup]
  refine ⟨?_, eventually_nhdsGT_lt_of_deriv_pos hc (deriv_pos_right_of_sign_deriv hf)⟩
  -- To the left of `x₀`, apply the right-hand half to the reflection `x ↦ f (-x)` at `-x₀`.
  have hderiv : ∀ᶠ x in 𝓝[>] (-x₀), 0 < deriv (fun x ↦ f (-x)) x := by
    filter_upwards [tendsto_neg_nhdsGT_neg.eventually (deriv_neg_left_of_sign_deriv hf)]
      with x hx
    rw [deriv_comp_neg]
    exact neg_pos.2 hx
  have hc' : ContinuousAt (fun x ↦ f (-x)) (-x₀) :=
    (by rwa [neg_neg] : ContinuousAt f (-(-x₀))).comp continuousAt_neg
  filter_upwards [tendsto_neg_nhdsLT.eventually (eventually_nhdsGT_lt_of_deriv_pos hc' hderiv)]
    with x hx
  simpa using hx

/-- **Strict second-derivative test.** If `deriv f x₀ = 0` and `deriv (deriv f) x₀ > 0` for a
function `f : ℝ → ℝ` continuous at `x₀`, then `x₀` is a strict local minimum of `f`:
`f x₀ < f x` for every `x ≠ x₀` close to `x₀`. -/
theorem eventually_lt_of_deriv_deriv_pos {f : ℝ → ℝ} {x₀ : ℝ} (hf : 0 < deriv (deriv f) x₀)
    (hd : deriv f x₀ = 0) (hc : ContinuousAt f x₀) : ∀ᶠ x in 𝓝[≠] x₀, f x₀ < f x :=
  eventually_lt_of_sign_deriv hc <| nhdsWithin_le_nhds <|
    eventually_nhdsWithin_sign_eq_of_deriv_pos hf hd

/-- **Strict second-derivative test, maximum version.** If `deriv f x₀ = 0` and
`deriv (deriv f) x₀ < 0` for a function `f : ℝ → ℝ` continuous at `x₀`, then `x₀` is a strict
local maximum of `f`. -/
theorem eventually_gt_of_deriv_deriv_neg {f : ℝ → ℝ} {x₀ : ℝ} (hf : deriv (deriv f) x₀ < 0)
    (hd : deriv f x₀ = 0) (hc : ContinuousAt f x₀) : ∀ᶠ x in 𝓝[≠] x₀, f x < f x₀ := by
  simpa using eventually_lt_of_deriv_deriv_pos (f := (-f ·)) (by simpa) (by simpa) hc.neg

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
