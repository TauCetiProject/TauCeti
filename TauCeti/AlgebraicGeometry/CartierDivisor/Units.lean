/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Principal

/-!
# Units on an open subset and boundary Cartier divisors

A unit on a nonempty open subset of an integral scheme determines a rational function,
and hence a principal Cartier divisor on the whole scheme. That divisor restricts to zero
on the open subset. Its vanishing is equivalent to extension of the unit to the whole scheme.
Conversely, a Cartier divisor restricting to zero on the open subset has trivial line-bundle
class exactly when it arises this way from a unit.

These are the two left-hand exactness statements of the units--divisors--Picard sequence,
expressed using Cartier divisors supported on the complement. No regularity, dimension or
Noetherian hypothesis is required.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Proposition 6.5.
* The Stacks Project, *Divisors*, Section 31.27, *The Weil divisor class associated to an
  invertible module*.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

open TauCeti.AlgebraicGeometry.Scheme

universe u

noncomputable section

variable (X : Scheme.{u}) [IsIntegral X]

/-- The principal Cartier divisor on `X` of a unit on a nonempty open subset `U`. -/
def unitDivisor (U : X.Opens) [Nonempty U] :
    Additive Γ(X, U)ˣ →+ CartierDivisor X :=
  (principalCartierDivisorAddHom X).comp (regularUnitToFunctionField X U).toAdditive

/-- The divisor of an open-subset unit is the principal divisor of its rational function. -/
@[simp]
theorem unitDivisor_apply (U : X.Opens) [Nonempty U] (f : Γ(X, U)ˣ) :
    unitDivisor X U (Additive.ofMul f) =
      principalCartierDivisor X (regularUnitToFunctionField X U f) := by
  simp [unitDivisor]

/-- Restricting a unit to a smaller nonempty open preserves its divisor on `X`. -/
theorem unitDivisor_map {U V : X.Opens} [Nonempty U] [Nonempty V]
    (h : V ≤ U) (f : Γ(X, U)ˣ) :
    unitDivisor X V (Additive.ofMul
        (Units.map (X.presheaf.map (homOfLE h).op).hom f)) =
      unitDivisor X U (Additive.ofMul f) := by
  simp only [unitDivisor_apply, regularUnitToFunctionField_map]

/-- The divisor of a unit on `U` restricts to zero on `U`. -/
@[simp]
theorem unitDivisor_restrict_eq_zero (U : X.Opens) [Nonempty U] (f : Additive Γ(X, U)ˣ) :
    unitDivisor X U f |_ U = 0 := by
  rw [← ofMul_toMul f, unitDivisor_apply, principalCartierDivisor_restrict,
    regularUnitToFunctionField_apply]
  exact rationalUnitClass_germToFunctionField_eq_zero X U f.toMul

/-- A unit on `U` has zero boundary divisor exactly when it is the restriction of a global
unit on `X`. -/
theorem unitDivisor_eq_zero_iff (U : X.Opens) [Nonempty U] (f : Γ(X, U)ˣ) :
    unitDivisor X U (Additive.ofMul f) = 0 ↔
      ∃ g : Γ(X, ⊤)ˣ,
        Units.map (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom g = f := by
  constructor
  · intro hf
    rw [unitDivisor_apply, principalCartierDivisor_eq_rationalUnitClass] at hf
    obtain ⟨g, hg⟩ := (rationalUnitClass_eq_zero_iff X ⊤
      (regularUnitToFunctionField X U f)).mp hf
    refine ⟨g, ?_⟩
    apply Units.map_injective (X.germToFunctionField_injective U)
    have hfield : regularUnitToFunctionField X U
        (Units.map (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom g) =
        regularUnitToFunctionField X U f :=
      (X.regularUnitToFunctionField_map (le_top : U ≤ ⊤) g).trans
        hg
    simpa only [regularUnitToFunctionField_apply] using hfield
  · rintro ⟨g, rfl⟩
    rw [unitDivisor_apply, regularUnitToFunctionField_map]
    rw [regularUnitToFunctionField_apply]
    exact principalCartierDivisor_regularUnitToFunctionField X g

end

end AlgebraicGeometry.Scheme

namespace TauCeti.AlgebraicGeometry.Scheme

open _root_.AlgebraicGeometry.Scheme

universe u

noncomputable section

variable (X : Scheme.{u}) [IsIntegral X]

/-- A Cartier divisor supported on the complement of `U` has trivial line-bundle class exactly
when it is the divisor of a unit on `U`. -/
theorem CartierDivisor.toLineBundleClass_eq_one_iff_exists_unitDivisor
    (U : X.Opens) [Nonempty U] (D : CartierDivisor X) (hD : D |_ U = 0) :
    D.toLineBundleClass = 1 ↔ ∃ f : Γ(X, U)ˣ, unitDivisor X U (Additive.ofMul f) = D := by
  rw [CartierDivisor.toLineBundleClass_eq_one_iff]
  constructor
  · rintro ⟨g, rfl⟩
    rw [principalCartierDivisor_restrict] at hD
    obtain ⟨f, hf⟩ := (rationalUnitClass_eq_zero_iff X U g).mp hD
    refine ⟨f, ?_⟩
    rw [unitDivisor_apply, hf]
  · rintro ⟨f, rfl⟩
    exact ⟨regularUnitToFunctionField X U f, (unitDivisor_apply X U f).symm⟩

end

end TauCeti.AlgebraicGeometry.Scheme
