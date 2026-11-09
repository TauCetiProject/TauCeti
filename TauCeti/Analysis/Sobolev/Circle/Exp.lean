/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Nemytskii
import TauCeti.Analysis.Complex.ContinuousLog.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The exponential Nemytskii map on the circle Sobolev spaces

For `s > 1/2`, the holomorphic Nemytskii map of the complex exponential sends `F ∈ H^s` to the
element `e^F = nemytskii exp F` of `H^s`. This file records its algebraic properties and the
regularity of logarithms in `H^s`.

The hard result is that a continuous logarithm `L` of an element `u` of `H^s` lies itself in `H^s`
(`TauCeti.CircleSobolev.exists_toContinuousMap_eq_of_forall_exp_eq`). To see it, approximate `L`
uniformly within `π` by a trigonometric polynomial `r`. Then `u e^{-r} = e^{L - r}` lies in `H^s`
and takes values in the slit plane, so `L - r = log (u e^{-r})` lies in `H^s` by the holomorphic
Nemytskii map of the principal logarithm.

## Main statements

* `TauCeti.CircleSobolev.exists_toContinuousMap_eq_of_forall_exp_eq`: a continuous logarithm of an
  element of `H^s` is the continuous representative of an element of `H^s`.
* `TauCeti.CircleSobolev.nemytskii_exp_add`,
  `TauCeti.CircleSobolev.nemytskii_exp_mul_nemytskii_exp_neg`: `F ↦ e^F` turns sums into
  products, and `e^F` is a unit with inverse `e^{-F}`.
* `TauCeti.CircleSobolev.nemytskii_exp_eq_nemytskii_exp_iff`: `e^F = e^G` exactly when `G - F` is
  a constant in `2πiℤ`.
-/

public section

noncomputable section

open Complex Set

open scoped Real

namespace TauCeti

namespace CircleSobolev

variable {s : ℝ} [hs : Fact (1 / 2 < s)]

variable (T : ℝ) [Fact (0 < T)]

/-- The continuous representative of `e^F` is the exponential of that of `F`. -/
@[simp]
theorem toContinuousMap_nemytskii_exp (F : CircleSobolev s ℂ) (x : AddCircle T) :
    toContinuousMap T hs.out (nemytskii exp F) x = exp (toContinuousMap T hs.out F x) :=
  toContinuousMap_nemytskii T isOpen_univ differentiable_exp.differentiableOn
    (fun _ ↦ mem_univ _) x

variable {T}

/-- **Continuous logarithms of `H^s` functions lie in `H^s`.** For `s > 1/2`, if the continuous
function `L` on the circle is a logarithm of the continuous representative of `u ∈ H^s`, then `L`
is itself the continuous representative of an element of `H^s`. -/
theorem exists_toContinuousMap_eq_of_forall_exp_eq {u : CircleSobolev s ℂ}
    {L : C(AddCircle T, ℂ)} (h : ∀ x, exp (L x) = toContinuousMap T hs.out u x) :
    ∃ F : CircleSobolev s ℂ, toContinuousMap T hs.out F = L := by
  -- The trigonometric polynomials are uniformly dense, so `L` is within `π` of the continuous
  -- representative of some `r ∈ H^s`.
  have hdense : DenseRange (toContinuousMap T hs.out : CircleSobolev s ℂ →L[ℂ] _) := by
    have hle : Submodule.span ℂ (range (fourier (T := T))) ≤
        LinearMap.range ((toContinuousMap T hs.out : CircleSobolev s ℂ →L[ℂ] C(AddCircle T, ℂ)) :
          CircleSobolev s ℂ →ₗ[ℂ] C(AddCircle T, ℂ)) :=
      Submodule.span_le.2 <| by
        rintro _ ⟨n, rfl⟩
        exact ⟨single n 1, by ext; simp⟩
    have := Submodule.topologicalClosure_mono hle
    rw [span_fourier_closure_eq_top, top_le_iff] at this
    exact Submodule.dense_iff_topologicalClosure_eq_top.2 this
  obtain ⟨r, hr⟩ := Metric.denseRange_iff.1 hdense L π Real.pi_pos
  set w : C(AddCircle T, ℂ) := L - toContinuousMap T hs.out r
  have hw (x : AddCircle T) : |(w x).im| < π :=
    calc |(w x).im| ≤ ‖w x‖ := abs_im_le_norm _
      _ = dist (L x) (toContinuousMap T hs.out r x) := by
        simp only [w, ContinuousMap.sub_apply, dist_eq_norm]
      _ ≤ dist L (toContinuousMap T hs.out r) := ContinuousMap.dist_apply_le_dist x
      _ < π := hr
  have hlog (x : AddCircle T) : log (exp (w x)) = w x :=
    log_exp (abs_lt.1 (hw x)).1 (abs_lt.1 (hw x)).2.le
  -- `u e^{-r} = e^w` takes values in the slit plane, where `log` is holomorphic.
  have hv (x : AddCircle T) :
      toContinuousMap T hs.out (u * nemytskii exp (-r)) x = exp (w x) := by
    simp [w, ← h x, ← exp_add, sub_eq_add_neg]
  have hslit (x : AddCircle T) :
      toContinuousMap T hs.out (u * nemytskii exp (-r)) x ∈ slitPlane := by
    rw [hv, mem_slitPlane_iff_arg, ← log_im, hlog]
    exact ⟨(abs_lt.1 (hw x)).2.ne, exp_ne_zero _⟩
  refine ⟨r + nemytskii log (u * nemytskii exp (-r)), ContinuousMap.ext fun x ↦ ?_⟩
  rw [map_add, ContinuousMap.add_apply, toContinuousMap_nemytskii T isOpen_slitPlane
    (fun z hz ↦ (differentiableAt_log hz).differentiableWithinAt) hslit, hv, hlog]
  simp [w]

/-- `F ↦ e^F` turns sums into products. -/
theorem nemytskii_exp_add (F G : CircleSobolev s ℂ) :
    nemytskii exp (F + G) = nemytskii exp F * nemytskii exp G := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  exact toContinuousMap_injective 1 hs.out (ContinuousMap.ext fun x ↦ by simp [exp_add])

/-- The exponential `e^F` of an element of `H^s` is a unit, with inverse `e^{-F}`. -/
@[simp]
theorem nemytskii_exp_mul_nemytskii_exp_neg (F : CircleSobolev s ℂ) :
    nemytskii exp F * nemytskii exp (-F) = 1 := by
  rw [← nemytskii_exp_add, add_neg_cancel, nemytskii_zero, exp_zero, one_def]

/-- **Logarithms in `H^s` are unique up to `2πiℤ`.** Two elements of `H^s` have the same
exponential exactly when they differ by a constant in `2πiℤ`. -/
theorem nemytskii_exp_eq_nemytskii_exp_iff {F G : CircleSobolev s ℂ} :
    nemytskii exp F = nemytskii exp G ↔ ∃ k : ℤ, G = F + single 0 (k * (2 * π * I)) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_int_forall_eq_add_of_exp_eq (toContinuousMap 1 hs.out F).continuous
      (toContinuousMap 1 hs.out G).continuous fun x ↦ by
        rw [← toContinuousMap_nemytskii_exp, h, toContinuousMap_nemytskii_exp]
    exact ⟨k, toContinuousMap_injective 1 hs.out (ContinuousMap.ext fun x ↦ by simp [hk x])⟩
  · rintro ⟨k, rfl⟩
    exact toContinuousMap_injective 1 hs.out (ContinuousMap.ext fun x ↦ by
      simp [exp_add, exp_int_mul_two_pi_mul_I])

end CircleSobolev

end TauCeti
