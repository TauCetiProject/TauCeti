/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Algebra.Pi
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Reindex
import TauCeti.LinearAlgebra.Matrix.Trace.Basic

/-!
# Realizing an integral tracial form by matrices

A tracial linear form on a finite product of matrix algebras over a commutative ring of
characteristic zero is the trace of a matrix representation if its values on a diagonal matrix
unit in each block are natural numbers. Its value at one is the dimension of the representation.
This includes dimension zero. The matrix representation repeats each Wedderburn block with
the multiplicity prescribed by the form.

## Provenance

`LinearMap.exists_algHom_trace_eq_pi_matrix` adapts the repeated-block construction
of `New.exists_rep_of_trace` in `src/Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean`
in grh-lean (https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC). The algebra-homomorphism formulation over commutative rings
is new here.

## References

* R. Rouquier, *Caractérisation des caractères et pseudo-caractères*, J. Algebra 180 (1996),
  571–586. https://www.math.ucla.edu/~rouquier/papers.html
-/

public section

noncomputable section

open Matrix Fintype Finset LinearMap

attribute [local ext] Matrix.ext_linearMap

namespace LinearMap

variable {k : Type*} [CommRing k]

private lemma trace_eq_sum_blocks {m : ℕ} {d : Fin m → ℕ} [∀ i, NeZero (d i)]
    (τ : (Π i, Matrix (Fin (d i)) (Fin (d i)) k) →ₗ[k] k)
    (hcomm : ∀ x y, τ (x * y) = τ (y * x))
    (c : Fin m → ℕ) (hc : ∀ i, τ (Pi.single i (Matrix.single 0 0 1)) = c i)
    (z : Π i, Matrix (Fin (d i)) (Fin (d i)) k) :
    τ z = ∑ i, c i * (z i).trace := by
  classical
  have hunit (i : Fin m) (a b : Fin (d i)) :
      τ (Pi.single i (Matrix.single a b 1)) = if a = b then (c i : k) else 0 := by
    have h := hcomm (Pi.single i (Matrix.single a 0 1))
      (Pi.single i (Matrix.single 0 b 1))
    split_ifs with hab
    · simpa [hab, hc, ← Pi.single_mul] using h
    · simpa [Ne.symm hab, ← Pi.single_mul] using h
  have hτ : τ = lsum k _ k fun i : Fin m ↦ c i • traceLinearMap (Fin (d i)) k k := by
    ext i a b
    have ht : (Matrix.single a b (1 : k)).trace = if a = b then 1 else 0 := by
      split_ifs with hab <;> simp [hab]
    simpa [-lsum_apply, lsum_piSingle, ht] using hunit i a b
  simp [hτ]

/-- A tracial form on a finite product of matrix algebras is the trace of an algebra
homomorphism if its values on one diagonal matrix unit in each block are natural numbers.
The matrix size is its value at one; it may be zero. -/
theorem exists_algHom_trace_eq_pi_matrix [CharZero k] {m : ℕ} {d : Fin m → ℕ} [∀ i, NeZero (d i)]
    (τ : (Π i, Matrix (Fin (d i)) (Fin (d i)) k) →ₗ[k] k)
    (hcomm : ∀ x y, τ (x * y) = τ (y * x))
    (hnat : ∀ i, ∃ c : ℕ, τ (Pi.single i (Matrix.single 0 0 1)) = c) {n : ℕ}
    (hone : τ 1 = n) :
    ∃ φ : (Π i, Matrix (Fin (d i)) (Fin (d i)) k) →ₐ[k] Matrix (Fin n) (Fin n) k,
      ∀ z, (φ z).trace = τ z := by
  classical
  choose c hc using hnat
  let ι := Σ p : Σ i : Fin m, Fin (c i), Fin (d p.1)
  let diag : (Π p : Σ i : Fin m, Fin (c i), Matrix (Fin (d p.1)) (Fin (d p.1)) k) →ₐ[k]
      Matrix ι ι k := AlgHom.mk' (blockDiagonal'RingHom _ k) (fun c x ↦ blockDiagonal'_smul c x)
  let blocks : (Π i, Matrix (Fin (d i)) (Fin (d i)) k) →ₐ[k] Matrix ι ι k :=
    diag.comp (AlgHom.pi fun p ↦ Pi.evalAlgHom k _ p.1)
  have htrace (z : Π i, Matrix (Fin (d i)) (Fin (d i)) k) : (blocks z).trace = τ z := by
    simp +instances [blocks, diag, AlgHom.mk', ι, trace_blockDiagonal',
      trace_eq_sum_blocks τ hcomm c hc, Fintype.sum_sigma]
  have hcard : Fintype.card ι = n := by
    apply Nat.cast_injective (R := k)
    rw [← hone, ← htrace, map_one, Matrix.trace_one]
  let φ := (reindexAlgEquiv k k (Fintype.equivFinOfCardEq hcard)).toAlgHom.comp blocks
  exact ⟨φ, fun z ↦ (trace_reindex_self (Fintype.equivFinOfCardEq hcard) (blocks z)).trans
    (htrace z)⟩

end LinearMap
