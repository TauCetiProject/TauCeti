/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.UnitProOrder
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup

/-!
# Invertible pro-order for the `p`-adic integers

The additive group of the `p`-adic integers `ℤ_[p]`, written multiplicatively as
`Multiplicative ℤ_[p]`, is a nontrivial compact non-discrete pro-`p` group. Consequently both
`TauCeti.HasUnitProOrder A (Multiplicative ℤ_[p])` and
`TauCeti.HasCofinalUnitProOrder A (Multiplicative ℤ_[p])` hold if and only if `(p : A)` is a unit
in the semiring `A`; in particular both fail over `ZMod p`. The same equivalences hold for any
nonempty power `Multiplicative (X → ℤ_[p])`.

## Main results

* `TauCeti.hasUnitProOrder_multiplicative_padicInt_iff`: `HasUnitProOrder A (Multiplicative ℤ_[p])`
  holds if and only if `IsUnit (p : A)`.
* `TauCeti.hasCofinalUnitProOrder_multiplicative_padicInt_iff`:
  `HasCofinalUnitProOrder A (Multiplicative ℤ_[p])` holds if and only if `IsUnit (p : A)`.
* `TauCeti.hasUnitProOrder_multiplicative_pi_padicInt_iff`,
  `TauCeti.hasCofinalUnitProOrder_multiplicative_pi_padicInt_iff`: the same criteria for nonempty
  powers `Multiplicative (X → ℤ_[p])`.
* `TauCeti.not_hasUnitProOrder_zmod_multiplicative_padicInt`,
  `TauCeti.not_hasCofinalUnitProOrder_zmod_multiplicative_padicInt`: failure over `ZMod p`.

## References

* J. Bernstein, *Second adjointness for representations of reductive p-adic groups*, Section 1.3.
* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 2.2 and 2.3.
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime]

/-- The additive group of `ℤ_[p]` has invertible pro-order in a semiring `A` if and only if
`(p : A)` is a unit. -/
@[simp]
theorem hasUnitProOrder_multiplicative_padicInt_iff (A : Type*) [Semiring A] :
    HasUnitProOrder A (Multiplicative ℤ_[p]) ↔ IsUnit (p : A) :=
  (isProP_multiplicative_padicInt p).hasUnitProOrder_iff

/-- The additive group of `ℤ_[p]` has cofinal invertible pro-order in a semiring `A` if and only if
`(p : A)` is a unit. -/
@[simp]
theorem hasCofinalUnitProOrder_multiplicative_padicInt_iff (A : Type*) [Semiring A] :
    HasCofinalUnitProOrder A (Multiplicative ℤ_[p]) ↔ IsUnit (p : A) := by
  have hnd : ¬ DiscreteTopology (Multiplicative ℤ_[p]) := fun hd ↦ by
    have : Infinite ℤ_[p] := Infinite.of_injective (Nat.cast : ℕ → ℤ_[p]) Nat.cast_injective
    have : Finite (Multiplicative ℤ_[p]) :=
      Finite.of_finite_univ isCompact_univ.finite_of_discrete
    have : Finite ℤ_[p] := Finite.of_equiv _ Multiplicative.toAdd
    exact not_finite ℤ_[p]
  exact hasCofinalUnitProOrder_iff_isUnit_of_isProP hnd
    (U₀ := (⊤ : OpenSubgroup (Multiplicative ℤ_[p]))) isCompact_univ
    ((isProP_multiplicative_padicInt p).subgroup ⊤)

/-- A nonempty power `ℤ_[p] ^ X` has invertible pro-order in `A` if and only if `(p : A)` is a
unit. -/
@[simp]
theorem hasUnitProOrder_multiplicative_pi_padicInt_iff (X : Type*) [Nonempty X]
    (A : Type*) [Semiring A] :
    HasUnitProOrder A (Multiplicative (X → ℤ_[p])) ↔ IsUnit (p : A) :=
  (isProP_multiplicative_pi_padicInt p X).hasUnitProOrder_iff

/-- A nonempty power `ℤ_[p] ^ X` has cofinal invertible pro-order in `A` if and only if `(p : A)` is
a unit. -/
@[simp]
theorem hasCofinalUnitProOrder_multiplicative_pi_padicInt_iff (X : Type*) [Nonempty X]
    (A : Type*) [Semiring A] :
    HasCofinalUnitProOrder A (Multiplicative (X → ℤ_[p])) ↔ IsUnit (p : A) := by
  have hnd : ¬ DiscreteTopology (Multiplicative (X → ℤ_[p])) := fun hd ↦ by
    have : Infinite ℤ_[p] := Infinite.of_injective (Nat.cast : ℕ → ℤ_[p]) Nat.cast_injective
    have : Finite (Multiplicative (X → ℤ_[p])) :=
      Finite.of_finite_univ isCompact_univ.finite_of_discrete
    have : Finite (X → ℤ_[p]) := Finite.of_equiv _ Multiplicative.toAdd
    exact not_finite (X → ℤ_[p])
  exact hasCofinalUnitProOrder_iff_isUnit_of_isProP hnd
    (U₀ := (⊤ : OpenSubgroup (Multiplicative (X → ℤ_[p])))) isCompact_univ
    ((isProP_multiplicative_pi_padicInt p X).subgroup ⊤)

/-- The additive group of `ℤ_[p]` does not have invertible pro-order in `ZMod p`. -/
theorem not_hasUnitProOrder_zmod_multiplicative_padicInt :
    ¬ HasUnitProOrder (ZMod p) (Multiplicative ℤ_[p]) := by
  have : Nontrivial (ZMod p) := ZMod.nontrivial_iff.mpr (Fact.out : p.Prime).ne_one
  rw [hasUnitProOrder_multiplicative_padicInt_iff, ZMod.natCast_self]
  exact not_isUnit_zero

/-- The additive group of `ℤ_[p]` does not have cofinal invertible pro-order in `ZMod p`: its
levels `p ^ m ℤ_[p]` have non-invertible pro-order in `ZMod p`, while its trivial subgroup is not
open. -/
theorem not_hasCofinalUnitProOrder_zmod_multiplicative_padicInt :
    ¬ HasCofinalUnitProOrder (ZMod p) (Multiplicative ℤ_[p]) := by
  have : Nontrivial (ZMod p) := ZMod.nontrivial_iff.mpr (Fact.out : p.Prime).ne_one
  rw [hasCofinalUnitProOrder_multiplicative_padicInt_iff, ZMod.natCast_self]
  exact not_isUnit_zero

end TauCeti
