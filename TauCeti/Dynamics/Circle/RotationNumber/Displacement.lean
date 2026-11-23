/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
import Mathlib.Topology.Order.IntermediateValue

/-!
# Displacement signs of circle lifts and their translation numbers

A lift `f : ℝ → ℝ` of an orientation-preserving homeomorphism of the circle `ℝ / ℤ`, with
`f (x + 1) = f x + 1`, moves each point `x` by its **displacement** `f x - x`, a continuous
`1`-periodic function of `x`. This file compares the sign of the displacement with the sign of the
translation number `τ f` (`CircleDeg1Lift.translationNumber`), the rotation number of the circle
map read through the chosen lift.

* A continuous injective map `f : ℝ → ℝ` with `f (x + 1) = f x + 1` is strictly increasing
  (`Continuous.strictMono_of_injective_of_map_add_one`), so it is a `CircleDeg1Lift`
  (`CircleDeg1Lift.ofInjective`), and an invertible one
  (`CircleDeg1Lift.isUnit_ofInjective`). The restriction of a homeomorphism of the closed annulus
  strip `ℝ × [0, 1]` commuting with `(x, y) ↦ (x + 1, y)` to a boundary line is of this kind,
  with no orientation hypothesis: a strictly decreasing map cannot commute with `x ↦ x + 1`.
* For a continuous lift the displacement attains its minimum and its maximum
  (`CircleDeg1Lift.exists_isMinOn_map_sub`, `CircleDeg1Lift.exists_isMaxOn_map_sub`), by
  periodicity and compactness of
  `[0, 1]`. Hence a strict displacement bound `x + z < f x` for every `x` holds with a uniform
  margin (`CircleDeg1Lift.exists_gt_forall_add_le_of_forall_add_lt`,
  `CircleDeg1Lift.exists_lt_forall_le_add_of_forall_lt_add`).
* For a continuous lift and an integer `n`, `n < τ f` exactly when `x + n < f x` for every `x`,
  and `τ f < n` exactly when `f x < x + n` for every `x`
  (`CircleDeg1Lift.int_lt_translationNumber_iff`, `CircleDeg1Lift.translationNumber_lt_int_iff`).
  In particular the translation number is positive exactly when every point moves to the right,
  negative exactly when every point moves to the left, and zero exactly when the lift has a fixed
  point (`CircleDeg1Lift.translationNumber_pos_iff`, `CircleDeg1Lift.translationNumber_neg_iff`,
  `CircleDeg1Lift.translationNumber_eq_zero_iff`). For a non-integer `z` the displacement of a
  lift with `z < τ f` may still drop below `z` at some points, so the integer hypothesis cannot be
  dropped.
* An invertible lift moves `x` to the right exactly when its inverse moves `x` to the left
  (`CircleDeg1Lift.lt_units_inv_apply_iff`, `CircleDeg1Lift.units_inv_apply_lt_iff`).

These are the forms in which the boundary twist condition of the Poincaré–Birkhoff theorem is
stated. That condition is a hypothesis, not a property of every area-preserving map of the
annulus: it asks that the two boundary lifts of such a map have strict displacements of opposite
signs, equivalently translation numbers of opposite signs. Passing to the inverse map exchanges
the two signs.

## References

* É. Ghys, *Groups acting on the circle*, L'Enseignement Mathématique 47 (2001), 329–407,
  Section 5.
* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49. This motivates the downstream fixed-point
  application to twist maps of the annulus; it is not a source for the results proved here.
-/

public section

open Function

/-- A continuous injective map of the line commuting with the translation `x ↦ x + 1` is
strictly increasing. -/
theorem Continuous.strictMono_of_injective_of_map_add_one {f : ℝ → ℝ} (hf : Continuous f)
    (hinj : Injective f) (h : ∀ x, f (x + 1) = f x + 1) : StrictMono f := by
  refine (hf.strictMono_of_inj hinj).resolve_right fun hanti ↦ ?_
  have := hanti (lt_add_one (0 : ℝ))
  rw [h] at this
  linarith

namespace CircleDeg1Lift

local notation "τ" => translationNumber

/-- The circle lift given by a continuous injective map of the line commuting with
`x ↦ x + 1`. -/
noncomputable def ofInjective (f : ℝ → ℝ) (hf : Continuous f) (hinj : Injective f)
    (h : ∀ x, f (x + 1) = f x + 1) : CircleDeg1Lift where
  toFun := f
  monotone' := (hf.strictMono_of_injective_of_map_add_one hinj h).monotone
  map_add_one' := h

@[simp]
theorem coe_ofInjective {f : ℝ → ℝ} (hf : Continuous f) (hinj : Injective f)
    (h : ∀ x, f (x + 1) = f x + 1) : ⇑(ofInjective f hf hinj h) = f :=
  (rfl)

theorem continuous_ofInjective {f : ℝ → ℝ} (hf : Continuous f) (hinj : Injective f)
    (h : ∀ x, f (x + 1) = f x + 1) : Continuous (ofInjective f hf hinj h) := by
  rwa [coe_ofInjective]

/-- The lift given by a continuous injective map is invertible. -/
theorem isUnit_ofInjective {f : ℝ → ℝ} (hf : Continuous f) (hinj : Injective f)
    (h : ∀ x, f (x + 1) = f x + 1) : IsUnit (ofInjective f hf hinj h) :=
  isUnit_iff_bijective.2 ⟨by rwa [coe_ofInjective],
    (ofInjective f hf hinj h).continuous_iff_surjective.1 (continuous_ofInjective hf hinj h)⟩

variable (f : CircleDeg1Lift)

/-- The displacement `x ↦ f x - x` of a continuous lift attains its minimum. -/
theorem exists_isMinOn_map_sub (hf : Continuous f) :
    ∃ x₀, IsMinOn (fun x ↦ f x - x) Set.univ x₀ := by
  obtain ⟨x₀, -, hx₀⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 zero_le_one)
    (hf.sub continuous_id).continuousOn
  exact ⟨x₀, isMinOn_univ_iff.2 <| f.forall_map_sub_of_Icc (f x₀ - x₀ ≤ ·) fun y hy ↦ hx₀ hy⟩

/-- The displacement `x ↦ f x - x` of a continuous lift attains its maximum. -/
theorem exists_isMaxOn_map_sub (hf : Continuous f) :
    ∃ x₀, IsMaxOn (fun x ↦ f x - x) Set.univ x₀ := by
  obtain ⟨x₀, -, hx₀⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 zero_le_one)
    (hf.sub continuous_id).continuousOn
  exact ⟨x₀, isMaxOn_univ_iff.2 <| f.forall_map_sub_of_Icc (· ≤ f x₀ - x₀) fun y hy ↦ hx₀ hy⟩

/-- **Uniform margin.** If a continuous lift moves every point `x` strictly beyond `x + z`, then
it moves every point at least to `x + z'` for a single `z' > z`. -/
theorem exists_gt_forall_add_le_of_forall_add_lt (hf : Continuous f) {z : ℝ}
    (hz : ∀ x, x + z < f x) : ∃ z' > z, ∀ x, x + z' ≤ f x := by
  obtain ⟨x₀, hx₀⟩ := f.exists_isMinOn_map_sub hf
  exact ⟨f x₀ - x₀, by linarith [hz x₀], fun x ↦ by linarith [isMinOn_univ_iff.1 hx₀ x]⟩

/-- **Uniform margin.** If a continuous lift moves every point `x` strictly below `x + z`, then
it moves every point at most to `x + z'` for a single `z' < z`. -/
theorem exists_lt_forall_le_add_of_forall_lt_add (hf : Continuous f) {z : ℝ}
    (hz : ∀ x, f x < x + z) : ∃ z' < z, ∀ x, f x ≤ x + z' := by
  obtain ⟨x₀, hx₀⟩ := f.exists_isMaxOn_map_sub hf
  exact ⟨f x₀ - x₀, by linarith [hz x₀], fun x ↦ by linarith [isMaxOn_univ_iff.1 hx₀ x]⟩

/-- For a continuous lift and an integer `n`, the translation number exceeds `n` exactly when
every point `x` is moved strictly beyond `x + n`. -/
theorem int_lt_translationNumber_iff (hf : Continuous f) {n : ℤ} :
    (n : ℝ) < τ f ↔ ∀ x, x + n < f x :=
  ⟨fun h ↦ f.lt_map_of_int_lt_translationNumber h, f.lt_translationNumber_of_forall_add_lt hf⟩

/-- For a continuous lift and an integer `n`, the translation number is less than `n` exactly
when every point `x` is moved strictly below `x + n`. -/
theorem translationNumber_lt_int_iff (hf : Continuous f) {n : ℤ} :
    τ f < n ↔ ∀ x, f x < x + n :=
  ⟨fun h ↦ f.map_lt_of_translationNumber_lt_int h, f.translationNumber_lt_of_forall_lt_add hf⟩

/-- A continuous lift has positive translation number exactly when it moves every point to the
right. -/
theorem translationNumber_pos_iff (hf : Continuous f) : 0 < τ f ↔ ∀ x, x < f x := by
  simpa using f.int_lt_translationNumber_iff hf (n := 0)

/-- A continuous lift has negative translation number exactly when it moves every point to the
left. -/
theorem translationNumber_neg_iff (hf : Continuous f) : τ f < 0 ↔ ∀ x, f x < x := by
  simpa using f.translationNumber_lt_int_iff hf (n := 0)

/-- A continuous lift has translation number zero exactly when it has a fixed point. -/
theorem translationNumber_eq_zero_iff (hf : Continuous f) : τ f = 0 ↔ ∃ x, f x = x := by
  simpa using f.translationNumber_eq_int_iff hf (m := 0)

/-- A point lies below the image of `y` under the inverse of an invertible lift exactly when its
image lies below `y`. -/
theorem lt_units_inv_apply_iff (f : CircleDeg1Liftˣ) {x y : ℝ} :
    x < (f⁻¹ : CircleDeg1Liftˣ) y ↔ f x < y := by
  rw [← coe_toOrderIso_symm, ← coe_toOrderIso, OrderIso.lt_symm_apply]

/-- The image of `y` under the inverse of an invertible lift lies below a point exactly when `y`
lies below the image of that point. -/
theorem units_inv_apply_lt_iff (f : CircleDeg1Liftˣ) {x y : ℝ} :
    (f⁻¹ : CircleDeg1Liftˣ) y < x ↔ y < f x := by
  rw [← coe_toOrderIso_symm, ← coe_toOrderIso, OrderIso.symm_apply_lt]

end CircleDeg1Lift
