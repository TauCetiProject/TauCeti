/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.GaloisRepresentation.Unramified.Basic
import TauCeti.NumberTheory.GaloisRepresentation.Unramified.Operations
import TauCeti.NumberTheory.GaloisRepresentation.Unramified.Restriction
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
polynomial of the trivial representation of rank two, as for its semisimplification; more
generally an extension of trivial representations has the Frobenius polynomial of a trivial
representation. Restricted to a finite extension `L/K` of residue degree `f`, the Tate module
`ℤ_ℓ(1)` has Frobenius polynomial `X - q^f`, where `q^f` is the cardinality of the residue field
of `L`.
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

-- An extension of trivial representations has the Frobenius polynomial of a trivial
-- representation: the Frobenius polynomial does not see the extension.
example {A M : Type*} [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M]
    [TopologicalSpace M] [ContinuousAdd M] [Module.Free A M] [Module.Finite A M]
    (ρ : ContinuousRep (Field.absoluteGaloisGroup K) A M) (W : Submodule A M)
    (hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W) [Module.Free A W] [Module.Finite A W]
    [Module.Free A (M ⧸ W)] [Module.Finite A (M ⧸ W)]
    (h₁ : ρ.subrepresentation W hW = ContinuousRep.trivial _ A W)
    (h₂ : ρ.quotient W hW = ContinuousRep.trivial _ A (M ⧸ W)) :
    ρ.frobCharpoly = (X - 1) ^ (Module.finrank A W + Module.finrank A (M ⧸ W)) := by
  rw [frobCharpoly_eq_subrepresentation_mul_quotient ρ W hW, h₁, h₂, frobCharpoly_trivial,
    frobCharpoly_trivial, pow_add]

-- Restricted to `G_L` for a finite extension `L/K`, the Tate module `ℤ_ℓ(1)` has Frobenius
-- polynomial `X - q_L`, where `q_L = q^f` is the cardinality of the residue field of `L`.
example (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ.Coprime (ringChar (𝓀[K]))) {L : Type*} [Field L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [ValuativeExtension K L] [FiniteDimensional K L] (ι : L →ₐ[K] SeparableClosure K) :
    ((ofCharacter (continuousLocalCyclotomicCharacter ℓ K)).res
      (continuousAbsoluteGaloisGroupExtend K L ι)).frobCharpoly =
        X - C (Nat.card (𝓀[L]) : ℤ_[ℓ]) := by
  have h : (ofCharacter (continuousLocalCyclotomicCharacter ℓ K)).IsUnramified :=
    (isUnramified_ofCharacter_iff _).2 fun σ hσ ↦ by
      simpa using localCyclotomicCharacter_eq_one_of_mem_inertiaSubgroup ℓ hℓ hσ
  rw [h.frobCharpoly_res_continuousAbsoluteGaloisGroupExtend, ← map_pow,
    charpoly_ofCharacter_apply, map_pow, Units.val_pow_eq_pow_val,
    continuousLocalCyclotomicCharacter_apply,
    (isArithFrobeniusLift_arithFrobLift K).coe_localCyclotomicCharacter ℓ hℓ,
    natCard_residueField K L, Nat.cast_pow]
