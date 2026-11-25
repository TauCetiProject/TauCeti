/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.GaloisRepresentation.Unramified.Basic
import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Cyclotomic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Checks for unramified local Galois representations and Frobenius polynomials

For a nonarchimedean local field `K` with residue field of `q` elements and a prime `ℓ` different
from the residue characteristic, the Tate module `ℤ_ℓ(1)` (the line of the `ℓ`-adic cyclotomic
character) is unramified with Frobenius polynomial `X - q`; its geometric polynomial is
`X - q⁻¹`. The trivial representation of rank `n` has Frobenius polynomial `(X - 1)^n`, and a
representation whose Frobenius acts by a unipotent matrix `!![1, a; 0, 1]` has the Frobenius
polynomial of the trivial representation of rank two, as for its semisimplification.
-/

open Polynomial TauCeti TauCeti.ContinuousRep ValuativeRel

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

-- `ℤ_ℓ(1)` is unramified with Frobenius polynomial `X - q`, not `X - q⁻¹` ...
example (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ.Coprime (ringChar (𝓀[K]))) :
    (ofCharacter (continuousLocalCyclotomicCharacter ℓ K)).IsUnramified ∧
      (ofCharacter (continuousLocalCyclotomicCharacter ℓ K)).frobCharpoly =
        X - C (Nat.card (𝓀[K]) : ℤ_[ℓ]) := by
  refine ⟨(isUnramified_ofCharacter_iff _).2 fun σ hσ ↦ ?_, ?_⟩
  · simpa using localCyclotomicCharacter_eq_one_of_mem_inertiaSubgroup ℓ hℓ hσ
  · rw [frobCharpoly_ofCharacter, continuousLocalCyclotomicCharacter_apply,
      (isArithFrobeniusLift_arithFrobLift K).coe_localCyclotomicCharacter ℓ hℓ]

-- ... while its geometric Frobenius polynomial is `X - q⁻¹`.
example (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ.Coprime (ringChar (𝓀[K]))) :
    ∃ u : ℤ_[ℓ]ˣ, (u : ℤ_[ℓ]) = Nat.card (𝓀[K]) ∧
      (ofCharacter (continuousLocalCyclotomicCharacter ℓ K)).frobCharpolyGeom =
        X - C ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by
  refine ⟨localCyclotomicCharacter ℓ K (arithFrobLift K),
    (isArithFrobeniusLift_arithFrobLift K).coe_localCyclotomicCharacter ℓ hℓ, ?_⟩
  rw [frobCharpolyGeom_ofCharacter, continuousLocalCyclotomicCharacter_apply]

-- The trivial representation of rank `n` has Frobenius polynomial `(X - 1)^n`.
example (A : Type*) [CommRing A] [TopologicalSpace A] [Nontrivial A] (n : ℕ) :
    (ContinuousRep.trivial (Field.absoluteGaloisGroup K) A (Fin n → A)).frobCharpoly =
      (X - 1) ^ n := by
  simp

-- A unipotent Frobenius `!![1, a; 0, 1]` has the Frobenius polynomial of the trivial
-- representation of rank two.
example {A M : Type*} [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M]
    [TopologicalSpace M] [Module.Free A M] [Module.Finite A M]
    (ρ : ContinuousRep (Field.absoluteGaloisGroup K) A M) (b : Module.Basis (Fin 2) A M) (a : A)
    (h : LinearMap.toMatrix b b (ρ (arithFrobLift K)) = !![1, a; 0, 1]) :
    ρ.frobCharpoly = (ContinuousRep.trivial (Field.absoluteGaloisGroup K) A M).frobCharpoly := by
  rw [frobCharpoly_trivial, Module.finrank_eq_card_basis b, frobCharpoly_def,
    ← LinearMap.charpoly_toMatrix _ b, h, Matrix.charpoly_fin_two]
  simp [Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  ring
