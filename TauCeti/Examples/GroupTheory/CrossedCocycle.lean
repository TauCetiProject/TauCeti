/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.CrossedCocycle.Splitting
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Conventions for crossed cocycles and gauge

These computations pin the side and the inverse in the gauge formula
`(h • c) γ = h * c γ * (α γ h)⁻¹` of `TauCeti.CrossedCocycle`, and the conventions of the
splitting `γ ↦ (c γ, γ)` of the semidirect product.

* Let `ℤ` (written multiplicatively) act on `ℚˣ` with the generator acting by inversion. Gauge of
  the unit crossed cocycle by `2` takes the value `2 * (2⁻¹)⁻¹ = 4` at the generator; the
  conventions `h⁻¹ * c γ * α γ h` or `h * c γ * α γ h` would give `1/4` or `1`.
* For the same action, the inverse of the splitting value `(4, 1)` is `(4, -1)`, whereas for the
  trivial action the inverse of `(4, 1)` is `(1/4, -1)`: the action enters the first coordinate.
* A group acting on itself by conjugation has the crossed cocycle `γ ↦ γ⁻¹`
  (`TauCeti.CrossedCocycle.conjInv`), which is not a homomorphism for the symmetric group `S₃`;
  so crossed cocycles of a nontrivial action are not in general homomorphisms.
-/

public section

namespace TauCeti.Examples.CrossedCocycle

open TauCeti.CrossedCocycle Multiplicative SemidirectProduct

/-- The action of `ℤ`, written multiplicatively, on `ℚˣ` in which the generator acts by
inversion. -/
def inversion : Multiplicative ℤ →* MulAut ℚˣ :=
  zpowersHom _ (MulEquiv.inv ℚˣ)

/-- The unit `2` of `ℚ`. -/
def two : ℚˣ :=
  Units.mk0 2 two_ne_zero

/-- Gauge of the unit crossed cocycle by `2`, for the inversion action, takes the value `4` at
the generator. -/
theorem gauge_two_one_ofAdd_one :
    (((two • (1 : TauCeti.CrossedCocycle inversion)) (ofAdd 1) : ℚˣ) : ℚ) = 4 := by
  simp only [CrossedCocycle.smul_apply, CrossedCocycle.one_apply]
  simp [inversion, two]
  norm_num

/-- For the inversion action, the inverse of the splitting value `(4, 1)` is `(4, -1)`. -/
theorem inv_toSplitting_gauge_two :
    ((two • (1 : TauCeti.CrossedCocycle inversion)).toSplitting (ofAdd 1))⁻¹ =
      ⟨two * two, ofAdd (-1)⟩ := by
  ext
  · simp only [inv_left, left_toSplitting, right_splitting, CrossedCocycle.smul_apply,
      CrossedCocycle.one_apply]
    simp [inversion, two]
  · simp

/-- For the trivial action, the inverse of the splitting value `(4, 1)` is `(1/4, -1)`. -/
theorem inv_toSplitting_trivial :
    ((equivMonoidHom.symm (zpowersHom ℚˣ (two * two)) :
      TauCeti.CrossedCocycle (1 : Multiplicative ℤ →* MulAut ℚˣ)).toSplitting (ofAdd 1))⁻¹ =
      ⟨(two * two)⁻¹, ofAdd (-1)⟩ := by
  ext
  · simp
  · simp

/-- The crossed cocycle `γ ↦ γ⁻¹` of `S₃` for the conjugation action is not a homomorphism. -/
theorem not_forall_conjInv_mul :
    ¬ ∀ γ δ : Equiv.Perm (Fin 3),
      conjInv (Equiv.Perm (Fin 3)) (γ * δ) =
        conjInv (Equiv.Perm (Fin 3)) γ * conjInv (Equiv.Perm (Fin 3)) δ := by
  intro h
  have := h (Equiv.swap 0 1) (Equiv.swap 1 2)
  rw [conjInv_apply, conjInv_apply, conjInv_apply] at this
  revert this
  decide

end TauCeti.Examples.CrossedCocycle
