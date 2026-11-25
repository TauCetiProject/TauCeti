/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import TauCeti.NumberTheory.Padics.AnnularRing.Eval.Basic

/-!
# Joint injectivity of `ℂ_[p]`-evaluations on the open annulus

Over `ℂ_[p]`, the family of annulus evaluations `TauCeti.AnnularRing.evalAt t` and
`TauCeti.AnnularRing.localizedEvalAt t` at all `t : ℂ_[p]` with `p⁻¹ < ‖t‖ < 1` is jointly
injective on both `H = TauCeti.AnnularRing p` and `H[1/T]`.

## Main results

* `TauCeti.AnnularRing.eq_zero_of_forall_evalAt_padicComplex_eq_zero`,
  `TauCeti.AnnularRing.eq_of_forall_evalAt_padicComplex_eq`: joint injectivity on `H`, derived
  from `TauCeti.AnnularRing.eq_zero_of_forall_eval_eq_zero`.
* `TauCeti.AnnularRing.eq_zero_of_forall_localizedEvalAt_padicComplex_eq_zero`,
  `TauCeti.AnnularRing.eq_of_forall_localizedEvalAt_padicComplex_eq`: joint injectivity on `H[1/T]`.

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §§2–3.
-/

public noncomputable section

namespace TauCeti.AnnularRing

variable {p : ℕ} [Fact p.Prime]

/-- **Joint injectivity on `H`**: an element of `AnnularRing p` that vanishes at every point
`t ∈ ℂ_[p]` of the open annulus `p⁻¹ < ‖t‖ < 1` is zero. -/
theorem eq_zero_of_forall_evalAt_padicComplex_eq_zero {x : AnnularRing p}
    (hx : ∀ (t : ℂ_[p]) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1), evalAt t ht₀ ht₁ x = 0) :
    x = 0 :=
  eq_zero_of_forall_eval_eq_zero (K := ℂ_[p]) fun t ht₀ ht₁ ↦ by
    simpa only [← evalAt_eq_eval] using hx t ht₀ ht₁

/-- Two elements of `AnnularRing p` that agree at every point `t ∈ ℂ_[p]` of the open annulus
`p⁻¹ < ‖t‖ < 1` are equal. -/
theorem eq_of_forall_evalAt_padicComplex_eq {x y : AnnularRing p}
    (hxy : ∀ (t : ℂ_[p]) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1),
      evalAt t ht₀ ht₁ x = evalAt t ht₀ ht₁ y) : x = y :=
  sub_eq_zero.mp <| eq_zero_of_forall_evalAt_padicComplex_eq_zero fun t ht₀ ht₁ ↦ by
    rw [map_sub, hxy t ht₀ ht₁, sub_self]

/-- **Joint injectivity on `H[1/T]`**: an element of `H[1/T]` that vanishes at every point
`t ∈ ℂ_[p]` of the open annulus `p⁻¹ < ‖t‖ < 1` is zero. -/
theorem eq_zero_of_forall_localizedEvalAt_padicComplex_eq_zero {A : Type*} [CommRing A]
    [Algebra (AnnularRing p) A] [IsLocalization.Away (T : AnnularRing p) A] {x : A}
    (hx : ∀ (t : ℂ_[p]) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1),
      localizedEvalAt t ht₀ ht₁ x = 0) : x = 0 := by
  obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj (T : AnnularRing p) x
  have ha0 : a = 0 := eq_zero_of_forall_evalAt_padicComplex_eq_zero fun t ht₀ ht₁ ↦ by
    rw [← localizedEvalAt_algebraMap (A := A), ← ha, map_mul, hx t ht₀ ht₁, zero_mul]
  rw [ha0, map_zero] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).pow k).mul_left_eq_zero.mp ha

/-- Two elements of `H[1/T]` that agree at every point `t ∈ ℂ_[p]` of the open annulus
`p⁻¹ < ‖t‖ < 1` are equal. -/
theorem eq_of_forall_localizedEvalAt_padicComplex_eq {A : Type*} [CommRing A]
    [Algebra (AnnularRing p) A] [IsLocalization.Away (T : AnnularRing p) A] {x y : A}
    (hxy : ∀ (t : ℂ_[p]) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1),
      localizedEvalAt t ht₀ ht₁ x = localizedEvalAt t ht₀ ht₁ y) : x = y :=
  sub_eq_zero.mp <| eq_zero_of_forall_localizedEvalAt_padicComplex_eq_zero fun t ht₀ ht₁ ↦ by
    rw [map_sub, hxy t ht₀ ht₁, sub_self]

end TauCeti.AnnularRing
