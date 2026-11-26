/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RepresentationTheory.Character
public import TauCeti.RepresentationTheory.BaseChange.BrauerNesbitt
import TauCeti.LinearAlgebra.Charpoly.FinrankTwo

/-!
# The trace form of Brauer–Nesbitt in dimension two

The characteristic polynomial of an endomorphism `f` of a two-dimensional space is
`X ^ 2 - tr(f) X + det(f)`, and `tr(f²) = tr(f)² - 2 det(f)`. So for two-dimensional
representations of a monoid, the characters determine the characteristic polynomials at every
element as soon as `2` is invertible, and Brauer–Nesbitt
(`Representation.nonempty_equiv_of_charpoly_eq_of_perfectField`) turns equal characters into an
equivalence of semisimple representations. This is the case `d = 2` of the trace form of
Brauer–Nesbitt in characteristic `p > d`.

Over `𝔽₂` the trace of `f²` does not recover `det f`, but for a group the determinant of `ρ g` is a
unit of `𝔽₂`, hence `1`: two-dimensional semisimple representations of a group over `𝔽₂` with equal
characters are again equivalent.

## Main results

* `Representation.charpoly_eq_of_character_eq_of_finrank_eq_two`: two-dimensional representations
  with equal characters have equal characteristic polynomials when `2 ≠ 0`.
* `Representation.nonempty_equiv_of_character_eq_of_finrank_eq_two`: over a perfect field with
  `2 ≠ 0`, two-dimensional semisimple representations with equal characters are equivalent.
* `Representation.det_apply_eq_one_zmod_two`: over `𝔽₂` every group element acts with
  determinant `1`.
* `Representation.nonempty_equiv_of_character_eq_of_finrank_eq_two_zmod_two`: the same for
  representations of a group over `𝔽₂`.
-/

public section

open Polynomial Module

namespace Representation

variable {k G V W : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

section Monoid

variable [Monoid G] {ρ : Representation k G V} {σ : Representation k G W}

/-- **Characters determine characteristic polynomials in dimension two** when `2 ≠ 0`: the
determinant of `ρ g` is `(tr(ρ g)² - tr(ρ (g * g))) / 2`. -/
theorem charpoly_eq_of_character_eq_of_finrank_eq_two [FiniteDimensional k V]
    [FiniteDimensional k W] (hk : (2 : k) ≠ 0)
    (hV : finrank k V = 2) (hW : finrank k W = 2) (h : ∀ g, ρ.character g = σ.character g)
    (g : G) : (ρ g).charpoly = (σ g).charpoly := by
  have hdet : LinearMap.det (ρ g) = LinearMap.det (σ g) := by
    have hρ := LinearMap.trace_mul_self_of_finrank_eq_two hV (ρ g)
    have hσ := LinearMap.trace_mul_self_of_finrank_eq_two hW (σ g)
    rw [← map_mul] at hρ hσ
    have h₁ := h g
    have h₂ := h (g * g)
    simp only [character] at h₁ h₂
    refine mul_left_cancel₀ hk ?_
    linear_combination hρ - hσ - h₂ + (LinearMap.trace k V (ρ g) +
      LinearMap.trace k W (σ g)) * h₁
  have htr : LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g) := h g
  rw [LinearMap.charpoly_of_finrank_eq_two hV, LinearMap.charpoly_of_finrank_eq_two hW, htr, hdet]

/-- **Brauer–Nesbitt in dimension two, trace form**: over a perfect field in which `2 ≠ 0`, two
semisimple two-dimensional representations of a monoid with the same character are equivalent. -/
theorem nonempty_equiv_of_character_eq_of_finrank_eq_two [PerfectField k] (hk : (2 : k) ≠ 0)
    (ρ : Representation k G V) (σ : Representation k G W) [ρ.IsSemisimpleRepresentation]
    [σ.IsSemisimpleRepresentation] (hV : finrank k V = 2) (hW : finrank k W = 2)
    (h : ∀ g, ρ.character g = σ.character g) : Nonempty (ρ.Equiv σ) :=
  have := Module.finite_of_finrank_eq_succ hV
  have := Module.finite_of_finrank_eq_succ hW
  nonempty_equiv_of_charpoly_eq_of_perfectField ρ σ
    (charpoly_eq_of_character_eq_of_finrank_eq_two hk hV hW h)

end Monoid

section ZModTwo

variable [Group G]

/-- Over `𝔽₂`, every element of a group acts with determinant `1`: the determinant is a unit
of `𝔽₂`. -/
theorem det_apply_eq_one_zmod_two {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (τ : Representation (ZMod 2) G U) (g : G) : LinearMap.det (τ g) = 1 := by
  have hu : LinearMap.det (τ g) * LinearMap.det (τ g⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
  generalize LinearMap.det (τ g) = x at hu
  generalize LinearMap.det (τ g⁻¹) = y at hu
  revert x y
  decide

/-- **Brauer–Nesbitt in dimension two over `𝔽₂`, trace form**: two semisimple two-dimensional
representations of a group over `𝔽₂` with the same character are equivalent. The determinant of
`ρ g` is a unit of `𝔽₂`, hence `1`, so the characteristic polynomials agree. -/
theorem nonempty_equiv_of_character_eq_of_finrank_eq_two_zmod_two {V W : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G W) [ρ.IsSemisimpleRepresentation]
    [σ.IsSemisimpleRepresentation] (hV : finrank (ZMod 2) V = 2) (hW : finrank (ZMod 2) W = 2)
    (h : ∀ g, ρ.character g = σ.character g) : Nonempty (ρ.Equiv σ) := by
  have := Module.finite_of_finrank_eq_succ hV
  have := Module.finite_of_finrank_eq_succ hW
  refine nonempty_equiv_of_charpoly_eq_of_perfectField ρ σ fun g => ?_
  rw [LinearMap.charpoly_of_finrank_eq_two hV, LinearMap.charpoly_of_finrank_eq_two hW,
    det_apply_eq_one_zmod_two, det_apply_eq_one_zmod_two]
  have htr : LinearMap.trace (ZMod 2) V (ρ g) = LinearMap.trace (ZMod 2) W (σ g) := h g
  rw [htr]

end ZModTwo

end Representation
