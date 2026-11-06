/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.LinearAlgebra.Matrix.PosSemidef

/-!
# The Haagerup property of discrete groups

A discrete group `G` has the **Haagerup property** (is *a-T-menable*) when the constant function
`1` is a pointwise limit of normalized positive-definite functions vanishing at infinity. We use
the net form of Anantharaman–Popa, Definition 16.1.1: for every finite set `F ⊆ G` and every
`ε > 0` there is a positive-definite `φ : G → ℂ` with `φ 1 = 1`, tending to `0` along the cofinite
filter, and with `‖φ g - 1‖ < ε` for `g ∈ F`.

A function `φ` is positive definite when `∑ᵢ ∑ⱼ conj (cᵢ) cⱼ φ (gᵢ⁻¹ gⱼ) ≥ 0` for all finite
families; we state this as positive semidefiniteness, in Mathlib's sense for arbitrary index
types, of the kernel `(g, h) ↦ φ (g⁻¹ * h)`. Over `ℂ` the Hermitian symmetry that
`Matrix.PosSemidef` also records is implied by the nonnegativity of the quadratic forms.

The Haagerup property is the approximation property opposite to property (T): it passes to
subgroups, and finite groups have it. Free groups have it by Haagerup's theorem, proved in
`TauCeti.GroupTheory.HaagerupProperty.FreeGroup`.

## Main declarations

* `TauCeti.HasHaagerupProperty`: the Haagerup property of a discrete group, unfolded by
  `TauCeti.hasHaagerupProperty_iff`.
* `TauCeti.hasHaagerupProperty_of_finite`: finite groups have the Haagerup property.
* `TauCeti.HasHaagerupProperty.of_injective` and `TauCeti.HasHaagerupProperty.subgroup`: the
  Haagerup property passes along injective homomorphisms, in particular to subgroups.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Definition 16.1.1.
* P.-A. Cherix, M. Cowling, P. Jolissaint, P. Julg and A. Valette, *Groups with the Haagerup
  property*, Progress in Mathematics 197, Birkhäuser (2001), §1.1.
-/

public section

open Filter Topology
open scoped ComplexOrder

namespace TauCeti

/-- A discrete group `G` has the **Haagerup property** when for every finite set `F ⊆ G` and every
`ε > 0` there is a function `φ : G → ℂ` that is positive definite (the kernel
`(g, h) ↦ φ (g⁻¹ * h)` is positive semidefinite), normalized by `φ 1 = 1`, vanishes at infinity
(tends to `0` along the cofinite filter), and satisfies `‖φ g - 1‖ < ε` for every `g ∈ F`. -/
def HasHaagerupProperty (G : Type*) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε → ∃ φ : G → ℂ,
    (Matrix.of fun g h => φ (g⁻¹ * h)).PosSemidef ∧ φ 1 = 1 ∧ Tendsto φ cofinite (𝓝 0) ∧
      ∀ g ∈ F, ‖φ g - 1‖ < ε

variable {G H : Type*} [Group G] [Group H]

theorem hasHaagerupProperty_iff : HasHaagerupProperty G ↔
    ∀ (F : Finset G) (ε : ℝ), 0 < ε → ∃ φ : G → ℂ,
      (Matrix.of fun g h => φ (g⁻¹ * h)).PosSemidef ∧ φ 1 = 1 ∧ Tendsto φ cofinite (𝓝 0) ∧
        ∀ g ∈ F, ‖φ g - 1‖ < ε :=
  Iff.rfl

/-- A finite group has the Haagerup property, witnessed by the constant function `1`: along the
cofinite filter of a finite type every function vanishes at infinity. -/
theorem hasHaagerupProperty_of_finite [Finite G] : HasHaagerupProperty G :=
  fun _ ε hε => ⟨fun _ => 1, posSemidef_const_one, rfl, by simp [cofinite_eq_bot],
    fun _ _ => by simpa using hε⟩

/-- The Haagerup property passes along injective group homomorphisms: restrict the approximating
positive-definite functions. -/
theorem HasHaagerupProperty.of_injective (hG : HasHaagerupProperty G) (f : H →* G)
    (hf : Function.Injective f) : HasHaagerupProperty H := by
  classical
  intro F ε hε
  obtain ⟨φ, hpd, h1, hlim, hF⟩ := hG (F.image f) ε hε
  refine ⟨φ ∘ f, ?_, by simpa using h1, hlim.comp hf.tendsto_cofinite,
    fun g hg => hF _ (Finset.mem_image_of_mem f hg)⟩
  convert hpd.submatrix f using 1
  ext g h
  simp

/-- Subgroups of a group with the Haagerup property have the Haagerup property. -/
theorem HasHaagerupProperty.subgroup (hG : HasHaagerupProperty G) (K : Subgroup G) :
    HasHaagerupProperty K :=
  hG.of_injective K.subtype K.subtype_injective

end TauCeti
