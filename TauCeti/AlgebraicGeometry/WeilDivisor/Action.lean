/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.SMul
public import TauCeti.AlgebraicGeometry.WeilDivisor.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Order

/-!
# The action of a group of symmetries on Weil divisors

A group `G` acting on a type of points `X` acts on the formal divisors `WeilDivisor X` by
permuting the points: `g • ∑ n_x [x] = ∑ n_x [g • x]`. This file registers that action and
records how it interacts with the divisor vocabulary — coefficients, point divisors, the
order, effectivity, and the (weighted) degree.

The underlying scalar multiplication is Mathlib's `Finsupp.comapSMul`, the action on the domain
of a finitely supported function; Mathlib keeps it out of the instance graph because on a
general `α →₀ M` it competes with the action on the values `M`. Here the values are the
integers and are not acted on, so the domain action is the intended one and is registered as an
instance, with `TauCeti.AlgebraicGeometry.WeilDivisor.smul_def` identifying it with the formal
pushforward.

## Main results

* `TauCeti.AlgebraicGeometry.WeilDivisor.coeff_smul`: the coefficient of `g • D` at a point is
  the coefficient of `D` at its preimage;
* `TauCeti.AlgebraicGeometry.WeilDivisor.degree_smul` and
  `TauCeti.AlgebraicGeometry.WeilDivisor.weightedDegree_smul`: a symmetry preserves the
  unweighted degree, and transports a weighted degree to the weight composed with the symmetry;
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

/-- **A group of symmetries of the points acts on the divisors** by permuting the points. This
is Mathlib's `Finsupp.comapSMul`, the action on the domain of a finitely supported function,
which is the intended action here because the coefficient group `ℤ` carries no `G`-action. -/
noncomputable instance instDistribMulAction : DistribMulAction G (WeilDivisor X) :=
  Finsupp.comapDistribMulAction

/-- The action is the formal pushforward along the symmetry. -/
theorem smul_def (g : G) (D : WeilDivisor X) : g • D = pushforward (g • ·) D := rfl

@[simp]
theorem smul_ofPoint (g : G) (x : X) : g • ofPoint x = ofPoint (g • x) := by
  rw [smul_def, pushforward_ofPoint]

end Monoid

section Group

variable [Group G] [MulAction G X] (g : G)

/-- The coefficient of `g • D` at a point is the coefficient of `D` at the point it came
from. -/
@[simp]
theorem coeff_smul (D : WeilDivisor X) (x : X) : coeff (g • D) x = coeff D (g⁻¹ • x) :=
  Finsupp.comapSMul_apply g D x

/-- The coefficient of `g • D` at a translated point is the coefficient of `D` at the point. -/
theorem coeff_smul_smul (D : WeilDivisor X) (x : X) : coeff (g • D) (g • x) = coeff D x := by
  simp

@[simp]
theorem smul_le_smul_iff {D E : WeilDivisor X} : g • D ≤ g • E ↔ D ≤ E := by
  simp only [le_iff, coeff_smul]
  exact ⟨fun h x ↦ by simpa using h (g • x), fun h x ↦ h _⟩

@[simp]
theorem isEffective_smul {D : WeilDivisor X} : IsEffective (g • D) ↔ IsEffective D := by
  simp only [isEffective_iff, coeff_smul]
  exact ⟨fun h x ↦ by simpa using h (g • x), fun h x ↦ h _⟩

/-- A symmetry of the points preserves the unweighted degree. -/
@[simp]
theorem degree_smul (D : WeilDivisor X) : degree (g • D) = degree D := by
  rw [smul_def, degree_pushforward]

/-- A symmetry of the points transports a weighted degree into the weighted degree against the
weight composed with the symmetry. -/
theorem weightedDegree_smul (w : X → ℤ) (D : WeilDivisor X) :
    weightedDegree w (g • D) = weightedDegree (fun x ↦ w (g • x)) D := by
  rw [smul_def, weightedDegree_pushforward]
  -- `weightedDegree_pushforward` produces `w ∘ (g • ·)`, which is the stated weight unfolded.
  rfl

end Group

end WeilDivisor

end AlgebraicGeometry

end TauCeti
