/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Points of `ℍ ∪ ∂ℍ` as complex numbers

Points of `ℍ ∪ ∂ℍ` are modelled as `ℍ ⊕ OnePoint ℝ`: a point of `ℍ` (`Sum.inl`) or an ideal
point (`Sum.inr`). Every such point other than `∞` is a complex number of nonnegative imaginary
part, `toComplex p`, and `toComplex` is injective away from `∞` (`toComplex_injOn`).

## Main declarations

* `TauCeti.UpperHalfPlane.toComplex`: a point of `ℍ ⊕ OnePoint ℝ` as a complex number, with
  `im_toComplex_nonneg` and `toComplex_injOn`.

## Source

Walkden, *Hyperbolic geometry* (MATH32051 lecture notes, Manchester 2019), §7.1 (the closure
`ℍ ∪ ∂ℍ` of the upper half-plane, with `∂ℍ = ℝ ∪ {∞}`).
-/

public section

noncomputable section

open UpperHalfPlane
open scoped OnePoint

namespace TauCeti.UpperHalfPlane

/-- A point of `ℍ ∪ ∂ℍ` other than `∞`, as a complex number of nonnegative imaginary part: a
point of `ℍ` is itself and a real ideal point `x` is `x`. The value at `∞` is `0`
(`toComplex_inr_infty`), and carries no meaning. -/
def toComplex : ℍ ⊕ OnePoint ℝ → ℂ :=
  Sum.elim (↑) fun ξ ↦ ((OnePoint.elim ξ 0 id : ℝ) : ℂ)

@[simp]
theorem toComplex_inl (z : ℍ) : toComplex (.inl z) = z :=
  (rfl)

@[simp]
theorem toComplex_inr_coe (x : ℝ) : toComplex (.inr (x : OnePoint ℝ)) = x :=
  (rfl)

/-- The junk value of `toComplex` at `∞`. -/
@[simp]
theorem toComplex_inr_infty : toComplex (.inr ∞) = 0 :=
  Complex.ofReal_zero

/-- The imaginary part of a point of `ℍ ∪ ∂ℍ` is nonnegative. -/
theorem im_toComplex_nonneg (p : ℍ ⊕ OnePoint ℝ) : 0 ≤ (toComplex p).im := by
  rcases p with z | ξ
  · exact z.im_pos.le
  · induction ξ using OnePoint.rec <;> simp

/-- Two points of `ℍ ∪ ∂ℍ` other than `∞` with the same complex value are equal. -/
theorem toComplex_injOn : Set.InjOn toComplex {p | p ≠ .inr ∞} := by
  rintro (z | ξ) hp (w | η) hq h
  · exact congrArg _ (UpperHalfPlane.coe_injective h)
  · obtain ⟨y, rfl⟩ := OnePoint.ne_infty_iff_exists.1 fun hη ↦ hq (congrArg _ hη)
    have him := congrArg Complex.im h
    rw [toComplex_inl, toComplex_inr_coe, Complex.ofReal_im] at him
    exact absurd him z.im_pos.ne'
  · obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.1 fun hξ ↦ hp (congrArg _ hξ)
    have him := congrArg Complex.im h
    rw [toComplex_inl, toComplex_inr_coe, Complex.ofReal_im] at him
    exact absurd him.symm w.im_pos.ne'
  · obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.1 fun hξ ↦ hp (congrArg _ hξ)
    obtain ⟨y, rfl⟩ := OnePoint.ne_infty_iff_exists.1 fun hη ↦ hq (congrArg _ hη)
    rw [toComplex_inr_coe, toComplex_inr_coe, Complex.ofReal_inj] at h
    rw [h]

end TauCeti.UpperHalfPlane
