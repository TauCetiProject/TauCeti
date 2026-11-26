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
`X ^ 2 - tr(f) X + det(f)`, and `tr(f²) = tr(f)² - 2 det(f)`. Over a perfect field with `2 ≠ 0`,
the resulting statement for two-dimensional representations is the case `d = 2` of the trace
form of Brauer–Nesbitt (`Representation.nonempty_equiv_of_character_eq_of_factorial_ne_zero`).

Over `𝔽₂` the trace of `f²` does not recover `det f`, but for a group the determinant of `ρ g` is a
unit of `𝔽₂`, hence `1` (`Representation.det_apply_eq_one`). So the characteristic polynomials
agree, and Brauer–Nesbitt (`Representation.nonempty_equiv_of_charpoly_eq_of_perfectField`) shows
that two-dimensional semisimple representations of a group over `𝔽₂` with equal characters are
again equivalent.

## Main results

* `Representation.nonempty_equiv_of_character_eq_of_finrank_eq_two_zmod_two`: two-dimensional
  semisimple representations of a group over `𝔽₂` with equal characters are equivalent.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, Proposition 2.6, the trace form
  of Brauer–Nesbitt in characteristic `p > d` and its case `k = 𝔽₂`, `d = 2` for groups.
* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. ENS 7 (1974), proof of
  Lemme 6.13.
* C. W. Curtis and I. Reiner, *Representation theory of finite groups and associative algebras*,
  Theorem 30.16 (Brauer–Nesbitt).
-/

public section

open Polynomial Module

namespace Representation

variable {G : Type*} [Group G]

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
  have htr := h g
  simp only [character] at htr
  rw [LinearMap.charpoly_of_finrank_eq_two hV, LinearMap.charpoly_of_finrank_eq_two hW,
    det_apply_eq_one, det_apply_eq_one, htr]

end Representation
