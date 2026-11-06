/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import TauCeti.Analysis.Calculus.TaylorIntegral

/-!
# Necessary derivative tests

This file records necessary versions of Mathlib's sufficient second-derivative tests. At a local
maximum of a continuous real-valued function, the value `deriv (deriv g) t₀` is nonpositive; at a
local minimum it is nonnegative. On a real normed space the same holds for every diagonal entry
`fderiv ℝ (fderiv ℝ f) x w w` of the Hessian of a `C²` function at a local extremum.

It also records the one-sided first-derivative tests at an endpoint: a function with a local
maximum on `Iic a` at `a` (a maximum *from the left*) has nonnegative left derivative there, and
dually for minima and for maxima and minima from the right on `Ici a`. The maximum from the left
is the time-direction step of the parabolic maximum principle, where the maximum may sit on the
top of the space-time cylinder. The same test along the inward ray `t ↦ x - t • e` turns a lower
bound on difference quotients into a lower bound on a directional derivative, which is the last
step of Hopf's boundary-point lemma.

## Main declarations

* `IsLocalMaxOn.hasDerivWithinAt_Iic_nonneg`: the left derivative at a maximum from the left is
  nonnegative.
* `IsLocalMinOn.hasDerivWithinAt_Iic_nonpos`, `IsLocalMaxOn.hasDerivWithinAt_Ici_nonpos`,
  `IsLocalMinOn.hasDerivWithinAt_Ici_nonneg`: the dual endpoint tests.
* `TauCeti.deriv_deriv_nonpos_of_isLocalMax`: the local-maximum version.
* `TauCeti.deriv_deriv_nonneg_of_isLocalMin`: the local-minimum version.
* `TauCeti.fderiv_fderiv_self_nonpos_of_isLocalMax` /
  `TauCeti.fderiv_fderiv_self_nonneg_of_isLocalMin`: the Hessian is negative (resp. positive)
  semidefinite on the diagonal at a local maximum (resp. minimum).
* `TauCeti.le_fderiv_of_le_sub`, `TauCeti.le_fderiv_of_mul_le_sub`: a lower bound on the
  difference quotients `(f x - f (x - t • e)) / t` for small `t > 0` bounds the directional
  derivative `fderiv ℝ f x e` below.
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

/-- **Difference quotients bound the directional derivative.** Let `f` be differentiable at `x`,
and let `g` vanish at `0` and have right derivative `κ` there. If `g t ≤ f x - f (x - t • e)` for
`0 < t ≤ δ`, then `κ ≤ fderiv ℝ f x e`. -/
theorem le_fderiv_of_le_sub {g : ℝ → ℝ} {e : E} {κ δ : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableAt ℝ f x) (hg : HasDerivWithinAt g κ (Set.Ici 0) 0) (hg0 : g 0 = 0)
    (hle : ∀ t ∈ Set.Ioc 0 δ, g t ≤ f x - f (x - t • e)) :
    κ ≤ fderiv ℝ f x e := by
  have hline : HasDerivAt (fun t : ℝ ↦ x - t • e) (-e) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_sub x
  have hray : HasDerivAt (fun t : ℝ ↦ f (x - t • e)) (-fderiv ℝ f x e) 0 := by
    have h := hf.hasFDerivAt.comp_hasDerivAt_of_eq (x := 0) hline (by simp)
    rwa [map_neg] at h
  -- The difference `f x - f (x - t • e) - g t` has a minimum from the right at `t = 0`.
  have hmin : IsLocalMinOn (fun t ↦ f x - f (x - t • e) - g t) (Set.Ici 0) 0 := by
    filter_upwards [Icc_mem_nhdsGE hδ] with t ht
    rcases ht.1.eq_or_lt with rfl | ht0
    · exact le_rfl
    · simp only [zero_smul, sub_zero, sub_self, hg0]
      linarith [hle t ⟨ht0, ht.2⟩]
  have h := hmin.hasDerivWithinAt_Ici_nonneg ((hray.const_sub (f x)).hasDerivWithinAt.sub hg)
  linarith

/-- **A linear lower bound on difference quotients bounds the directional derivative.** If `f` is
differentiable at `x` and `κ t ≤ f x - f (x - t • e)` for `0 < t ≤ δ`, then
`κ ≤ fderiv ℝ f x e`. -/
theorem le_fderiv_of_mul_le_sub {e : E} {κ δ : ℝ} (hδ : 0 < δ) (hf : DifferentiableAt ℝ f x)
    (hκ : ∀ t ∈ Set.Ioc 0 δ, κ * t ≤ f x - f (x - t • e)) :
    κ ≤ fderiv ℝ f x e :=
  le_fderiv_of_le_sub (g := fun t ↦ κ * t) hδ hf
    (by simpa using (hasDerivWithinAt_id (0 : ℝ) (Set.Ici 0)).const_mul κ) (mul_zero κ) hκ

end NormedSpace

end TauCeti
