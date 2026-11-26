/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.LinearAlgebra.Determinant.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Unique
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Archimedean.Character
public import TauCeti.RepresentationTheory.Continuous.Determinant.Basic

/-!
# The one-dimensional representations of the archimedean Weil groups

The irreducible finite-dimensional complex representations of `W_ℂ = ℂˣ` are one-dimensional, and
a continuous one-dimensional representation of `W_ℂ` is multiplication by a character
`z ↦ |z| ^ s * (z / |z|) ^ k` (`TauCeti.complexUnitsCharacter s k`). The one-dimensional
continuous representations of `W_ℝ` are multiplication by the characters through the norm,
`TauCeti.ClassFieldTheory.WeilGroupReal.character s ε`. This is the one-dimensional half of the
classification of the irreducible continuous representations of the archimedean Weil groups; the
irreducible representations of `W_ℝ` of dimension two are the inductions of characters of `ℂˣ`.

The representations are continuous representations `TauCeti.ContinuousRep` on a space with its
module topology; on a line, `ρ w` is multiplication by its determinant
(`LinearMap.apply_eq_det_smul_of_finrank_eq_one`), so `W` acts by the determinant character
`ContinuousRep.det`, which is continuous. Both statements are also given for parameters
`G →* GL_n(ℂ)` with `n` a singleton index type, which are then the scalar matrices of a character.

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

open Matrix Module

namespace TauCeti.ClassFieldTheory

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [IsModuleTopology ℂ V]

namespace WeilGroupComplex

/-- **The continuous one-dimensional representations of `W_ℂ`**: `ℂˣ` acts by a character
`z ↦ |z| ^ s * (z / |z|) ^ k`. -/
theorem exists_eq_complexUnitsCharacter_smul (ρ : ContinuousRep WeilGroupComplex ℂ V)
    (h : finrank ℂ V = 1) :
    ∃ (s : ℂ) (k : ℤ), ∀ z v, ρ z v = (complexUnitsCharacter s k z : ℂ) • v := by
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_eq_succ h
  obtain ⟨s, k, hsk⟩ := exists_eq_complexUnitsCharacter ρ.continuousDet
  refine ⟨s, k, fun z v ↦ ?_⟩
  have hz : ρ.continuousDet z = complexUnitsCharacter s k z := DFunLike.congr_fun hsk z
  rw [LinearMap.apply_eq_det_smul_of_finrank_eq_one h, ← ρ.coe_det_apply_eq_linearMap_det,
    ← ContinuousRep.coe_continuousDet, hz]

/-- **The continuous irreducible finite-dimensional representations of `W_ℂ`** are
one-dimensional, and `ℂˣ` acts on them by a character `z ↦ |z| ^ s * (z / |z|) ^ k`. -/
theorem exists_eq_complexUnitsCharacter_smul_of_isIrreducible [FiniteDimensional ℂ V]
    (ρ : ContinuousRep WeilGroupComplex ℂ V) [ρ.toRepresentation.IsIrreducible] :
    finrank ℂ V = 1 ∧ ∃ (s : ℂ) (k : ℤ), ∀ z v, ρ z v = (complexUnitsCharacter s k z : ℂ) • v :=
  have h := Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ.toRepresentation
  ⟨h, exists_eq_complexUnitsCharacter_smul ρ h⟩

/-- **The continuous one-dimensional parameters of `W_ℂ`** are the scalar matrices of the
characters `z ↦ |z| ^ s * (z / |z|) ^ k`. -/
theorem exists_eq_scalar_complexUnitsCharacter {n : Type*} [Fintype n] [DecidableEq n] [Unique n]
    (r : WeilGroupComplex →* GL n ℂ) (hr : Continuous r) :
    ∃ (s : ℂ) (k : ℤ), ∀ z, r z = GeneralLinearGroup.scalar n (complexUnitsCharacter s k z) := by
  obtain ⟨s, k, hsk⟩ := exists_eq_complexUnitsCharacter
    ⟨GeneralLinearGroup.det.comp r, GeneralLinearGroup.continuous_det.comp hr⟩
  refine ⟨s, k, fun z ↦ ?_⟩
  have hz : (r z).det = complexUnitsCharacter s k z := DFunLike.congr_fun hsk z
  rw [GeneralLinearGroup.eq_scalar_det (r z), hz]

end WeilGroupComplex

namespace WeilGroupReal

/-- **The continuous one-dimensional representations of `W_ℝ`**: `W_ℝ` acts by a character
through the norm, `character s ε`, which is `|z| ^ (2 * s)` on `z ∈ ℂˣ` and `(-1) ^ ε` at
`j`. -/
theorem exists_eq_character_smul (ρ : ContinuousRep WeilGroupReal ℂ V) (h : finrank ℂ V = 1) :
    ∃ (s : ℂ) (ε : ZMod 2), ∀ w v, ρ w v = (character s ε w : ℂ) • v := by
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_eq_succ h
  obtain ⟨s, ε, hsε⟩ := exists_eq_character ρ.continuousDet
  refine ⟨s, ε, fun w v ↦ ?_⟩
  have hw : ρ.continuousDet w = character s ε w := DFunLike.congr_fun hsε w
  rw [LinearMap.apply_eq_det_smul_of_finrank_eq_one h, ← ρ.coe_det_apply_eq_linearMap_det,
    ← ContinuousRep.coe_continuousDet, hw]

/-- **The continuous one-dimensional parameters of `W_ℝ`** are the scalar matrices of the
characters `character s ε` through the norm. -/
theorem exists_eq_scalar_character {n : Type*} [Fintype n] [DecidableEq n] [Unique n]
    (r : WeilGroupReal →* GL n ℂ) (hr : Continuous r) :
    ∃ (s : ℂ) (ε : ZMod 2), ∀ w, r w = GeneralLinearGroup.scalar n (character s ε w) := by
  obtain ⟨s, ε, hsε⟩ := exists_eq_character
    ⟨GeneralLinearGroup.det.comp r, GeneralLinearGroup.continuous_det.comp hr⟩
  refine ⟨s, ε, fun w ↦ ?_⟩
  have hw : (r w).det = character s ε w := DFunLike.congr_fun hsε w
  rw [GeneralLinearGroup.eq_scalar_det (r w), hw]

end WeilGroupReal

end TauCeti.ClassFieldTheory
