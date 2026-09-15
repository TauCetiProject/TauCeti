/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.SMul
public import TauCeti.AlgebraicGeometry.WeilDivisor.Order

/-!
# Monoid and group actions on Weil divisors

A monoid `G` acting on a type of points `X` acts on the formal divisors `WeilDivisor X` by
pushing point coefficients forward: `g • ∑ n_x [x] = ∑ n_x [g • x]`. This file registers
that action and records how it interacts with the divisor vocabulary — coefficients, point
divisors, the order, effectivity, and the (weighted) degree.

The underlying scalar multiplication is Mathlib's `Finsupp.comapSMul`, the action on the domain
of a finitely supported function; Mathlib keeps it out of the instance graph because on a
general `α →₀ M` it competes with the action on the values `M`. The same overlap exists here
whenever `G` also acts on `ℤ` (for instance `ℕ` acting on `WeilDivisor ℕ`), so the domain action
is only a scoped instance, available after `open scoped TauCeti.AlgebraicGeometry.WeilDivisor`;
`TauCeti.AlgebraicGeometry.WeilDivisor.smul_def` identifies it with the formal pushforward.
Concrete settings where no competing action exists, such as automorphisms of a function field
acting on its divisors, register it globally.

## Main results

* `TauCeti.AlgebraicGeometry.WeilDivisor.degree_smul` and
  `TauCeti.AlgebraicGeometry.WeilDivisor.weightedDegree_smul`: an action preserves the
  unweighted degree, and transports a weighted degree to the weight composed with the action;
* `TauCeti.AlgebraicGeometry.WeilDivisor.isEffective_smul` and
  `TauCeti.AlgebraicGeometry.WeilDivisor.smul_le_smul_iff`: the action preserves effectivity and
  the coefficientwise order.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {G X : Type*}

section Monoid

variable [Monoid G] [MulAction G X]

/-- **A monoid acting on the points acts on the divisors** by pushing point coefficients
forward. This is Mathlib's `Finsupp.comapSMul`, the action on the domain of a finitely supported
function. It is scoped because it overlaps with the coefficientwise action whenever `G` also
acts on `ℤ`. -/
noncomputable scoped instance instDistribMulAction : DistribMulAction G (WeilDivisor X) :=
  Finsupp.comapDistribMulAction

/-- The action is the formal pushforward along the action on points. -/
theorem smul_def (g : G) (D : WeilDivisor X) : g • D = pushforward (g • ·) D := rfl

/-- The action carries the point divisor at `x` to the point divisor at `g • x`. -/
@[simp]
theorem smul_ofPoint (g : G) (x : X) : g • ofPoint x = ofPoint (g • x) := by
  rw [smul_def, pushforward_ofPoint]

/-- A monoid action on the points preserves the unweighted degree. -/
@[simp]
theorem degree_smul (g : G) (D : WeilDivisor X) : degree (g • D) = degree D := by
  rw [smul_def, degree_pushforward]

/-- A monoid action on the points transports a weighted degree into the weighted degree against
the weight composed with the action. -/
@[simp]
theorem weightedDegree_smul (g : G) (w : X → ℤ) (D : WeilDivisor X) :
    weightedDegree w (g • D) = weightedDegree (fun x ↦ w (g • x)) D := by
  rw [smul_def, weightedDegree_pushforward]
  -- `weightedDegree_pushforward` produces `w ∘ (g • ·)`, which is the stated weight unfolded.
  rfl

end Monoid

section Group

variable [Group G] [MulAction G X] (g : G)

/-- The coefficient of `x` in `g • D` is the coefficient of `g⁻¹ • x` in `D`. -/
@[simp]
theorem coeff_smul (D : WeilDivisor X) (x : X) : coeff (g • D) x = coeff D (g⁻¹ • x) := by
  exact Finsupp.comapSMul_apply g D x

/-- The action preserves the coefficientwise order on Weil divisors. -/
@[simp]
theorem smul_le_smul_iff {D E : WeilDivisor X} : g • D ≤ g • E ↔ D ≤ E := by
  simp only [le_iff, coeff_smul]
  exact ⟨fun h x ↦ by simpa using h (g • x), fun h x ↦ h _⟩

/-- The action preserves effectivity of Weil divisors. -/
@[simp]
theorem isEffective_smul {D : WeilDivisor X} : IsEffective (g • D) ↔ IsEffective D := by
  simp only [isEffective_iff, coeff_smul]
  exact ⟨fun h x ↦ by simpa using h (g • x), fun h x ↦ h _⟩

end Group

end WeilDivisor

end AlgebraicGeometry

end TauCeti
