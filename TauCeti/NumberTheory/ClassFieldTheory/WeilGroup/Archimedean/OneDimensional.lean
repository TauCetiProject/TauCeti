/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Unique
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Archimedean.Character
public import TauCeti.RepresentationTheory.LineCharacter

/-!
# The one-dimensional representations of the archimedean Weil groups

The irreducible finite-dimensional complex representations of `W_ℂ = ℂˣ` are one-dimensional, and
a continuous one-dimensional representation of `W_ℂ` is multiplication by a character
`z ↦ |z| ^ s * (z / |z|) ^ k` (`TauCeti.complexUnitsCharacter s k`). The one-dimensional
continuous representations of `W_ℝ` are multiplication by the characters through the norm,
`TauCeti.ClassFieldTheory.WeilGroupReal.character s ε`. This is the one-dimensional half of the
classification of the irreducible continuous representations of the archimedean Weil groups; the
irreducible representations of `W_ℝ` of dimension two are the inductions of characters of `ℂˣ`.

Continuity of a representation `ρ` on a finite-dimensional space is continuity of its matrix
coefficients `w ↦ f (ρ w v)`. Both statements are also given for parameters `G →* GL_n(ℂ)` with
`n` a singleton index type, which are then the scalar matrices of a character.

## Main results

* `TauCeti.ClassFieldTheory.WeilGroupComplex.exists_eq_complexUnitsCharacter_smul`: a continuous
  one-dimensional representation of `W_ℂ` is multiplication by `complexUnitsCharacter s k`.
* `TauCeti.ClassFieldTheory.WeilGroupComplex.exists_eq_complexUnitsCharacter_smul_of_isIrreducible`:
  the same for every continuous irreducible finite-dimensional representation of `W_ℂ`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.exists_eq_character_smul`: a continuous one-dimensional
  representation of `W_ℝ` is multiplication by `character s ε`.
* `TauCeti.ClassFieldTheory.WeilGroupComplex.exists_eq_scalar_complexUnitsCharacter`,
  `TauCeti.ClassFieldTheory.WeilGroupReal.exists_eq_scalar_character`: the same for continuous
  one-dimensional parameters.

## References

* A. W. Knapp, *Local Langlands correspondence: the archimedean case*, §3, pp.401–403.
-/

public section

namespace TauCeti.ClassFieldTheory

open Matrix Module

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

namespace WeilGroupComplex

/-- **The continuous one-dimensional representations of `W_ℂ`**: `ℂˣ` acts by a character
`z ↦ |z| ^ s * (z / |z|) ^ k`. -/
theorem exists_eq_complexUnitsCharacter_smul (ρ : Representation ℂ WeilGroupComplex V)
    (h : finrank ℂ V = 1) (hρ : ∀ (v : V) (f : Dual ℂ V), Continuous fun z ↦ f (ρ z v)) :
    ∃ (s : ℂ) (k : ℤ), ∀ z v, ρ z v = (complexUnitsCharacter s k z : ℂ) • v := by
  obtain ⟨s, k, hsk⟩ :=
    exists_eq_complexUnitsCharacter ⟨ρ.lineCharacter h, ρ.continuous_lineCharacter h hρ⟩
  refine ⟨s, k, fun z v ↦ ?_⟩
  rw [ρ.lineCharacter_smul h, ← hsk]
  rfl

/-- **The continuous irreducible representations of `W_ℂ`** are one-dimensional, and `ℂˣ` acts on
them by a character `z ↦ |z| ^ s * (z / |z|) ^ k`. -/
theorem exists_eq_complexUnitsCharacter_smul_of_isIrreducible [FiniteDimensional ℂ V]
    (ρ : Representation ℂ WeilGroupComplex V) [ρ.IsIrreducible]
    (hρ : ∀ (v : V) (f : Dual ℂ V), Continuous fun z ↦ f (ρ z v)) :
    finrank ℂ V = 1 ∧ ∃ (s : ℂ) (k : ℤ), ∀ z v, ρ z v = (complexUnitsCharacter s k z : ℂ) • v :=
  have h := Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ
  ⟨h, exists_eq_complexUnitsCharacter_smul ρ h hρ⟩

/-- **The continuous one-dimensional parameters of `W_ℂ`** are the scalar matrices of the
characters `z ↦ |z| ^ s * (z / |z|) ^ k`. -/
theorem exists_eq_scalar_complexUnitsCharacter {n : Type*} [Fintype n] [DecidableEq n] [Unique n]
    (r : WeilGroupComplex →* GL n ℂ) (hr : Continuous r) :
    ∃ (s : ℂ) (k : ℤ), ∀ z, r z = GeneralLinearGroup.scalar n (complexUnitsCharacter s k z) := by
  obtain ⟨s, k, hsk⟩ := exists_eq_complexUnitsCharacter
    ⟨GeneralLinearGroup.det.comp r, GeneralLinearGroup.continuous_det.comp hr⟩
  refine ⟨s, k, fun z ↦ ?_⟩
  rw [GeneralLinearGroup.eq_scalar_det (r z), ← hsk]
  rfl

end WeilGroupComplex

namespace WeilGroupReal

/-- **The continuous one-dimensional representations of `W_ℝ`**: `W_ℝ` acts by a character
through the norm, `character s ε`, which is `|z| ^ (2 * s)` on `z ∈ ℂˣ` and `(-1) ^ ε` at
`j`. -/
theorem exists_eq_character_smul (ρ : Representation ℂ WeilGroupReal V) (h : finrank ℂ V = 1)
    (hρ : ∀ (v : V) (f : Dual ℂ V), Continuous fun w ↦ f (ρ w v)) :
    ∃ (s : ℂ) (ε : ZMod 2), ∀ w v, ρ w v = (character s ε w : ℂ) • v := by
  obtain ⟨s, ε, hsε⟩ := exists_eq_character ⟨ρ.lineCharacter h, ρ.continuous_lineCharacter h hρ⟩
  refine ⟨s, ε, fun w v ↦ ?_⟩
  rw [ρ.lineCharacter_smul h, ← hsε]
  rfl

/-- **The continuous one-dimensional parameters of `W_ℝ`** are the scalar matrices of the
characters `character s ε` through the norm. -/
theorem exists_eq_scalar_character {n : Type*} [Fintype n] [DecidableEq n] [Unique n]
    (r : WeilGroupReal →* GL n ℂ) (hr : Continuous r) :
    ∃ (s : ℂ) (ε : ZMod 2), ∀ w, r w = GeneralLinearGroup.scalar n (character s ε w) := by
  obtain ⟨s, ε, hsε⟩ := exists_eq_character
    ⟨GeneralLinearGroup.det.comp r, GeneralLinearGroup.continuous_det.comp hr⟩
  refine ⟨s, ε, fun w ↦ ?_⟩
  rw [GeneralLinearGroup.eq_scalar_det (r w), ← hsε]
  rfl

end WeilGroupReal

end TauCeti.ClassFieldTheory
