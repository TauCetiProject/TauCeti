/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Complex.DividedDifference.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import TauCeti.Analysis.Calculus.DSlope.Analytic
import TauCeti.Analysis.Calculus.DSlope.Basic
import TauCeti.Analysis.Calculus.DSlope.Integral
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.IteratedDeriv

/-!
# Analyticity and partial-derivative properties of coordinate divided differences

For an entire function `f : (ι → ℂ) → E` (with `ι` finite and `E` complete), the coordinate
divided difference `TauCeti.partialDslope i f ζ` is entire (`TauCeti.differentiable_partialDslope`,
via `TauCeti.analyticAt_dslope_update`) and admits the integral representation
`g z = ∫₀¹ ∂ᵢ f (update z i (ζ + t (z i - ζ))) dt` (`TauCeti.partialDslope_eq_integral`). It also
commutes with `partialDeriv j` for `j ≠ i` and lowers iterated `partialDeriv i` order by one.

## Main results

* `TauCeti.partialDslope_eq_integral`: integral representation of `partialDslope i f ζ` for
  entire `f`.
* `TauCeti.differentiable_partialDslope`: `partialDslope i f ζ` is entire when `f` is.
* `TauCeti.partialDeriv_partialDslope_of_ne`, `TauCeti.iterate_partialDeriv_partialDslope_of_ne`:
  `∂ⱼ` commutes with `f ↦ partialDslope i f ζ` on entire functions for `j ≠ i`.
* `TauCeti.iterate_partialDeriv_partialDslope_eq_zero`: `partialDslope i f ζ` has lower
  `partialDeriv i`-order than `f` for entire `f`.
-/

public section

open Function Set

namespace TauCeti

variable {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [CompleteSpace E]

/-- **Integral representation of the divided difference.** For an entire `f`,
`partialDslope i f ζ z = ∫₀¹ ∂ᵢ f (update z i (ζ + t (z i - ζ))) dt`. -/
theorem partialDslope_eq_integral [Finite ι] {f : (ι → ℂ) → E} (hf : Differentiable ℂ f)
    (i : ι) (ζ : ℂ) (z : ι → ℂ) :
    partialDslope i f ζ z =
      ∫ t in (0 : ℝ)..1, partialDeriv i f (update z i (ζ + t * (z i - ζ))) := by
  rw [partialDslope_apply, dslope_eq_integral_deriv isOpen_univ
    (differentiable_comp_update hf z i).contDiff.contDiffOn (subset_univ _)]
  congr 1 with t
  rw [Complex.real_smul, (hasDerivAt_comp_update (hf _)).deriv]

/-- **The divided difference of an entire function is entire.** -/
theorem differentiable_partialDslope [Finite ι] {f : (ι → ℂ) → E} (hf : Differentiable ℂ f)
    (i : ι) (ζ : ℂ) : Differentiable ℂ (partialDslope i f ζ) := by
  have := Fintype.ofFinite ι
  intro z
  have hfz := hf.differentiableOn.analyticAt_of_finiteDimensional Filter.univ_mem (z := z)
  have hfζ :=
    hf.differentiableOn.analyticAt_of_finiteDimensional Filter.univ_mem (z := update z i ζ)
  rw [partialDslope_def]
  exact (TauCeti.analyticAt_dslope_update i ζ hfz hfζ).differentiableAt

section PartialDeriv

variable [Finite ι] {f : (ι → ℂ) → E}

/-- On entire functions (with finite coordinates and a complete target), the partial derivative `∂ⱼ`
in another variable `j ≠ i` commutes with the divided difference in the `i`-th variable. -/
theorem partialDeriv_partialDslope_of_ne (hf : Differentiable ℂ f) {i j : ι} (hji : j ≠ i)
    (ζ : ℂ) : partialDeriv j (partialDslope i f ζ) = partialDslope i (partialDeriv j f) ζ := by
  ext z
  rw [partialDeriv_eq_deriv_update (differentiable_partialDslope hf i ζ z)]
  have hupd (s : ℂ) : update z j s i = z i := update_of_ne hji.symm _ _
  by_cases h : z i = ζ
  · -- On the hyperplane `z i = ζ` the divided difference is `∂ᵢ f`, and partial derivatives
    -- commute.
    have hline : (fun s ↦ partialDslope i f ζ (update z j s)) =
        fun s ↦ partialDeriv i f (update z j s) :=
      funext fun s ↦ partialDslope_of_eq (hf _) ((hupd s).trans h)
    rw [hline, ← partialDeriv_eq_deriv_update (differentiable_partialDeriv hf i z),
      partialDslope_of_eq (differentiable_partialDeriv hf j z) h, partialDeriv_comm hf]
  · -- Off the hyperplane, differentiate the difference quotient.
    have hline : (fun s ↦ partialDslope i f ζ (update z j s)) =
        fun s ↦ (z i - ζ)⁻¹ • (f (update z j s) - f (update (update z i ζ) j s)) := by
      funext s
      rw [partialDslope_of_ne ((hupd s).trans_ne h), hupd, update_comm hji]
    have hz : update (update z i ζ) j (z j) = update z i ζ := by
      rw [← update_of_ne hji ζ z, update_eq_self]
    rw [hline, partialDslope_of_ne h]
    refine (((hasDerivAt_comp_update (hf _)).sub (hasDerivAt_comp_update (hf _))).const_smul
      (z i - ζ)⁻¹).deriv.trans ?_
    rw [update_eq_self, hz]

/-- On entire functions (with finite coordinates and a complete target), the iterated partial
derivatives `∂ⱼ^m` in another variable `j ≠ i` commute with the divided difference in the `i`-th
variable. In particular, if `f` is a polynomial of degree at most `e` in `zⱼ`, in the sense that
`∂ⱼ^(e+1) f = 0`, then so is `partialDslope i f ζ`. -/
theorem iterate_partialDeriv_partialDslope_of_ne (hf : Differentiable ℂ f) {i j : ι}
    (hji : j ≠ i) (ζ : ℂ) (m : ℕ) :
    (partialDeriv j)^[m] (partialDslope i f ζ) = partialDslope i ((partialDeriv j)^[m] f) ζ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih,
      partialDeriv_partialDslope_of_ne (differentiable_iterate_partialDeriv hf j m) hji]

/-- **Dividing by `zᵢ - ζ` lowers the degree in `zᵢ`.** If `f` is entire and a polynomial of
degree at most `e` in `zᵢ`, in the sense that `∂ᵢ^(e+1) f = 0`, then `partialDslope i f ζ` is a
polynomial of degree less than `e` in `zᵢ`: `∂ᵢ^e (partialDslope i f ζ) = 0`. -/
theorem iterate_partialDeriv_partialDslope_eq_zero (hf : Differentiable ℂ f) {e : ℕ}
    (he : (partialDeriv i)^[e + 1] f = 0) (ζ : ℂ) :
    (partialDeriv i)^[e] (partialDslope i f ζ) = 0 := by
  ext z
  have hline := congrFun (iteratedDeriv_comp_update (differentiable_partialDslope hf i ζ) i z e)
    (z i)
  rw [update_eq_self] at hline
  rw [Pi.zero_apply, ← hline]
  simp only [partialDslope_update]
  refine congrFun
    (Differentiable.iteratedDeriv_dslope_eq_zero (differentiable_comp_update hf z i) ?_ ζ) (z i)
  rw [iteratedDeriv_comp_update hf, he]
  funext _
  simp

end PartialDeriv

end TauCeti
