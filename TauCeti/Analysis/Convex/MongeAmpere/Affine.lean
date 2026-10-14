/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.MongeAmpere.Basic

/-!
# Affine renormalization of the Monge–Ampère measure

Adding the affine function `x ↦ ⟪x, q⟫ + c` to a convex function translates every
subdifferential by `q`. Consequently, it translates subgradient images without changing their
additive Haar measure, so the Aleksandrov Monge–Ampère measure is unchanged.

This invariance permits the standard normalization of a convex function by subtracting a
supporting plane before studying its sections.

## Main statements

* `TauCeti.mem_subdifferential_ite_add_inner_add_iff` identifies the translated
  subdifferential;
* `TauCeti.subgradientImage_ite_add_inner_add` identifies the translated subgradient image;
* `TauCeti.mongeAmpereMeasure_ite_add_inner_add` proves invariance of the Aleksandrov
  Monge–Ampère measure under addition of an affine function.

## References

* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §1.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Measure Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {Ω s : Set E} [DecidablePred (· ∈ Ω)] {u : E → ℝ} {q x y : E} {c : ℝ}

/-- Adding `x ↦ ⟪x, q⟫ + c` to a function on `Ω` translates its relative subdifferential
by `q`. -/
theorem mem_subdifferential_ite_add_inner_add_iff (hx : x ∈ Ω) :
    y ∈ subdifferential (innerₗ E)
        (fun z ↦ if z ∈ Ω then ((u z + inner ℝ z q + c : ℝ) : EReal) else ⊤) x ↔
      y - q ∈ subdifferential (innerₗ E)
        (fun z ↦ if z ∈ Ω then (u z : EReal) else ⊤) x := by
  rw [mem_subdifferential_ite_iff (innerₗ E) hx,
    mem_subdifferential_ite_iff (innerₗ E) hx]
  constructor
  · intro hy z hz
    have h := hy z hz
    simp only [innerₗ_apply_apply, inner_sub_left, inner_sub_right] at h ⊢
    linarith
  · intro hy z hz
    have h := hy z hz
    simp only [innerₗ_apply_apply, inner_sub_left, inner_sub_right] at h ⊢
    linarith

/-- On a subset of `Ω`, adding `x ↦ ⟪x, q⟫ + c` translates the subgradient image by `q`.
The right-hand side is written as a preimage so Haar invariance applies directly. -/
theorem subgradientImage_ite_add_inner_add (hs : s ⊆ Ω) :
    subgradientImage (innerₗ E)
        (fun z ↦ if z ∈ Ω then ((u z + inner ℝ z q + c : ℝ) : EReal) else ⊤) s =
      (fun y ↦ y - q) ⁻¹' subgradientImage (innerₗ E)
        (fun z ↦ if z ∈ Ω then (u z : EReal) else ⊤) s := by
  ext y
  simp only [mem_subgradientImage_iff, mem_preimage]
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨x, hx, (mem_subdifferential_ite_add_inner_add_iff (hs hx)).1 hy⟩
  · rintro ⟨x, hx, hy⟩
    exact ⟨x, hx, (mem_subdifferential_ite_add_inner_add_iff (hs hx)).2 hy⟩

section Measure

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Affine invariance of the Aleksandrov Monge–Ampère measure.** Adding an affine function
`x ↦ ⟪x, q⟫ + c` to a convex function on an open convex domain does not change its
Monge–Ampère measure. -/
theorem mongeAmpereMeasure_ite_add_inner_add (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    mongeAmpereMeasure μ
        (fun x ↦ if x ∈ Ω then ((u x + inner ℝ x q + c : ℝ) : EReal) else ⊤) =
      mongeAmpereMeasure μ (fun x ↦ if x ∈ Ω then (u x : EReal) else ⊤) := by
  have hconv : ConvexOn ℝ Ω (fun x ↦ u x + inner ℝ x q + c) := by
    convert (hu.add ((innerₗ E).flip q |>.convexOn hu.1)).add_const c using 1
    ext z
    simp [Pi.add_apply, innerₗ_apply_apply, real_inner_comm]
  ext s hs
  rw [mongeAmpereMeasure_apply μ (convex_epigraph_ite hconv) ite_ne_bot
      AbsolutelyContinuous.rfl hs,
    mongeAmpereMeasure_apply μ (convex_epigraph_ite hu) ite_ne_bot
      AbsolutelyContinuous.rfl hs,
    setOf_ite_ne_top, hΩ.interior_eq, setOf_ite_ne_top, hΩ.interior_eq,
    subgradientImage_ite_add_inner_add inter_subset_right]
  simpa only [sub_eq_add_neg, add_comm] using
    measure_preimage_add μ (-q)
      (subgradientImage (innerₗ E)
        (fun x ↦ if x ∈ Ω then (u x : EReal) else ⊤) (s ∩ Ω))

end Measure

end TauCeti
