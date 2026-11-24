/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.Holder.Normed
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Complex.Beltrami.HigherHolder
import TauCeti.Analysis.Holder.LowOrder

/-!
# The Beltrami equation with small Hölder coefficient

Let `0 < α < 1` and let `μ` be a bounded `α`-Hölder function on `ℂ` vanishing off the closed disc
`closedBall c r`. This file solves the Beltrami equation `\bar∂ψ = μ ∂ψ` when the Hölder norm
`‖μ‖ = ‖μ‖_∞ + [μ]_α` is small, with a solution `C¹`-close to the identity on the disc.

The solution is `ψ = z + T h`, where `T h(w) = π⁻¹ ∫ (w - z)⁻¹ h(z) dz` is the Cauchy transform
of a source `h` supported in the disc, and `h` is the fixed point of `h = μ (1 + B h)` for the
Beurling operator `B = ∂ T`. This is the case `k = 0` of the `C^{k,α}` solver
`TauCeti.exists_ckHolder_conjWirtingerDeriv_eq_mul_wirtingerDeriv`, transported from
`CkHolderSpace 0 α ℂ ℂ` to the bounded Hölder space `HolderSpace α ℂ ℂ` along the isometry
`TauCeti.CkHolderSpace.equivHolderSpace`. The derivative of `ψ` at each point of the disc is
invertible, so `ψ` is a local diffeomorphism there by the inverse function theorem
(`HasStrictFDerivAt.toOpenPartialHomeomorph`).

This is the contraction step in the construction of isothermal coordinates for a Hölder almost
complex structure on a surface, after the Beltrami coefficient has been made small by rescaling.

## Main results

* `TauCeti.exists_conjWirtingerDeriv_eq_mul_wirtingerDeriv`: for `‖μ‖` below a threshold
  depending only on `α`, `c` and `r`, there is a source `h` supported in the disc with
  `‖h‖ ≤ 2 ‖μ‖` such that `ψ = z + T h` is `C¹` on `ball c (r + 1)`, solves `\bar∂ψ = μ ∂ψ` there,
  has derivative within `C ‖μ‖` of the identity at every point of the disc, with `α`-Hölder
  constant at most `C ‖μ‖` there, and has an invertible strict derivative at every point of the
  disc.

## References

* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, 2nd ed., AMS University Lecture Series
  **38**, 2006, Chapter V (the Beltrami equation solved by a fixed point of `h = μ (1 + B h)`).
* I. N. Vekua, *Generalized Analytic Functions*, Pergamon, 1962, Chapters I–II (the Cauchy and
  Beurling operators on Hölder spaces).
-/

public noncomputable section

open Complex Metric
open scoped NNReal

namespace TauCeti

variable {α : ℝ≥0}

/-- **The Beltrami equation with small Hölder coefficient.** Let `0 < α < 1`. There are `δ > 0`
and `C` such that every bounded `α`-Hölder function `μ` vanishing off `closedBall c r` with
`‖μ‖ < δ` admits a source `h`, vanishing off the disc with `‖h‖ ≤ 2 ‖μ‖`, for which
`ψ(w) = w + π⁻¹ ∫ (w - z)⁻¹ h(z) dz`

* is `C¹` on `ball c (r + 1)`, with `\bar∂ψ = h` there;
* solves the Beltrami equation `\bar∂ψ = μ ∂ψ` on `ball c (r + 1)`;
* has real derivative within `C ‖μ‖` of the identity at every point of the disc, with
  `α`-Hölder constant at most `C ‖μ‖` there;
* has an invertible strict derivative at every point of the disc, so it is a local
  diffeomorphism near each such point. -/
theorem exists_conjWirtingerDeriv_eq_mul_wirtingerDeriv (hα : 0 < α) (hα1 : α < 1) (c : ℂ)
    (r : ℝ) :
    ∃ δ > 0, ∃ C : ℝ≥0, ∀ μ ∈ supportedHolderSubmodule (Y := ℂ) α (closedBall c r), ‖μ‖ < δ →
      ∃ h ∈ supportedHolderSubmodule (Y := ℂ) α (closedBall c r), ‖h‖ ≤ 2 * ‖μ‖ ∧
        let ψ : ℂ → ℂ := fun w ↦ w + (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • h z
        ContDiffOn ℝ 1 ψ (ball c (r + 1)) ∧
        (∀ z ∈ ball c (r + 1), conjWirtingerDeriv ψ z 1 = h z) ∧
        (∀ z ∈ ball c (r + 1), conjWirtingerDeriv ψ z 1 = μ z * wirtingerDeriv ψ z 1) ∧
        (∀ z ∈ closedBall c r, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ C * ‖μ‖) ∧
        HolderOnWith (C * ‖μ‖₊) α (fderiv ℝ ψ) (closedBall c r) ∧
        ∀ z ∈ closedBall c r, ∃ L : ℂ ≃L[ℝ] ℂ, HasStrictFDerivAt ψ (L : ℂ →L[ℝ] ℂ) z := by
  obtain ⟨δ, hδ, C, hsol⟩ := exists_ckHolder_conjWirtingerDeriv_eq_mul_wirtingerDeriv 0 hα hα1 c r
  refine ⟨δ, hδ, C, fun μ hμ hμδ ↦ ?_⟩
  set e := CkHolderSpace.equivHolderSpace (α := α) (E := ℂ) (F := ℂ)
  have hμ' : e.symm μ ∈ supportedCkHolderSubmodule (E := ℂ) (F := ℂ) 0 α (closedBall c r) :=
    mem_supportedCkHolderSubmodule_iff.mpr fun z hz ↦ by
      rw [CkHolderSpace.coe_equivHolderSpace_symm]
      exact mem_supportedHolderSubmodule_iff.mp hμ z hz
  have hμn : ‖e.symm μ‖ = ‖μ‖ := e.symm.norm_map μ
  obtain ⟨h, hh, hnorm, hψ, hbar, hbel, -, hfd, hH, hinv⟩ := hsol (e.symm μ) hμ' (hμn ▸ hμδ)
  have he (z : ℂ) : e h z = h z := CkHolderSpace.equivHolderSpace_apply h z
  have hψ' : (fun w ↦ w + (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • e h z) =
      fun w ↦ w + cauchyTransform h w := by
    funext w
    simp only [he, cauchyTransform_apply]
  have hμz (z : ℂ) : e.symm μ z = μ z := by rw [CkHolderSpace.coe_equivHolderSpace_symm]
  have hμnn : ‖e.symm μ‖₊ = ‖μ‖₊ := Subtype.ext hμn
  refine ⟨e h, mem_supportedHolderSubmodule_iff.mpr fun z hz ↦ by
      rw [he]
      exact mem_supportedCkHolderSubmodule_iff.mp hh z hz,
    by rwa [e.norm_map, ← hμn], ?_⟩
  rw [hψ']
  refine ⟨by simpa using hψ.contDiffOn, fun z _ ↦ (hbar z).trans (he z).symm,
    fun z _ ↦ by rw [hbel z, hμz],
    fun z hz ↦ hμn ▸ hfd z hz, ?_, hinv⟩
  rw [fderiv_eq_continuousMultilinearCurryFin1_comp, ← hμnn]
  intro x hx y hy
  simpa only [Function.comp_apply, LinearIsometryEquiv.edist_map] using hH x hx y hy

end TauCeti
