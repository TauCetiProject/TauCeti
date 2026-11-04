/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import TauCeti.Analysis.Calculus.TaylorIntegral

/-!
# Necessary and strict derivative tests

This file records necessary versions of Mathlib's sufficient second-derivative tests. At a local
maximum of a continuous real-valued function, the value `deriv (deriv g) t₀` is nonpositive; at a
local minimum it is nonnegative. On a real normed space the same holds for every diagonal entry
`fderiv ℝ (fderiv ℝ f) x w w` of the Hessian of a `C²` function at a local extremum.

It also strengthens the conclusion of Mathlib's sufficient second-derivative test: at a critical
point `x₀` with `deriv (deriv f) x₀ > 0` the function has a *strict* local minimum,
`f x₀ < f x` for `x ≠ x₀` near `x₀`, and dually for `deriv (deriv f) x₀ < 0`. Strictness is what
the stability of an equilibrium at a minimum of the energy needs.

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

/-- **Strict second-derivative test.** If `deriv f x₀ = 0` and `deriv (deriv f) x₀ > 0` for a
function `f : ℝ → ℝ` continuous at `x₀`, then `x₀` is a strict local minimum of `f`:
`f x₀ < f x` for every `x ≠ x₀` close to `x₀`. -/
theorem eventually_lt_of_deriv_deriv_pos {f : ℝ → ℝ} {x₀ : ℝ} (hf : 0 < deriv (deriv f) x₀)
    (hd : deriv f x₀ = 0) (hc : ContinuousAt f x₀) : ∀ᶠ x in 𝓝[≠] x₀, f x₀ < f x := by
  -- Near `x₀`, the derivative of `f` has the sign of `x - x₀`.
  obtain ⟨ε, hε, hsign⟩ :=
    Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_sign_eq_of_deriv_pos hf hd)
  have hderiv {x : ℝ} (hx : |x - x₀| < ε) (hne : x ≠ x₀) : deriv f x ≠ 0 := by
    intro h
    have := hsign (y := x) (by rwa [Real.dist_eq])
    rw [h, sign_zero, eq_comm, sign_eq_zero_iff, sub_eq_zero] at this
    exact hne this
  have hcont {D : Set ℝ} (hD : ∀ x ∈ D, |x - x₀| < ε) : ContinuousOn f D := fun x hx ↦ by
    rcases eq_or_ne x x₀ with rfl | hne
    · exact hc.continuousWithinAt
    · exact (differentiableAt_of_deriv_ne_zero (hderiv (hD x hx) hne)).continuousAt
        |>.continuousWithinAt
  -- So `f` is strictly decreasing on `(x₀ - ε, x₀]` and strictly increasing on `[x₀, x₀ + ε)`.
  have hanti : StrictAntiOn f (Set.Ioc (x₀ - ε) x₀) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioc _ _)
      (hcont fun x hx ↦ abs_sub_lt_iff.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩) fun x hx ↦ ?_
    rw [interior_Ioc] at hx
    have h := hsign (y := x) (by
      rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith [hx.1, hx.2])
    rwa [sign_neg (sub_neg.2 hx.2), sign_eq_neg_one_iff] at h
  have hmono : StrictMonoOn f (Set.Ico x₀ (x₀ + ε)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico _ _)
      (hcont fun x hx ↦ abs_sub_lt_iff.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩) fun x hx ↦ ?_
    rw [interior_Ico] at hx
    have h := hsign (y := x) (by
      rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith [hx.1, hx.2])
    rwa [sign_pos (sub_pos.2 hx.1), sign_eq_one_iff] at h
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds x₀ hε), self_mem_nhdsWithin]
    with x hx hne
  rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hx
  rcases lt_or_gt_of_ne (Set.mem_compl_singleton_iff.1 hne) with hlt | hgt
  · exact hanti ⟨by linarith, hlt.le⟩ ⟨by linarith, le_rfl⟩ hlt
  · exact hmono ⟨le_rfl, by linarith⟩ ⟨hgt.le, by linarith⟩ hgt

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
