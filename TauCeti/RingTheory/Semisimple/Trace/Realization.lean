/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Matrix.Reindex
import TauCeti.LinearAlgebra.Matrix.Trace.Basic
import TauCeti.LinearAlgebra.Matrix.Trace.Pi

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

namespace LinearMap

variable {k : Type*} [CommRing k]

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
  have hτ (z : Π i, Matrix (Fin (d i)) (Fin (d i)) k) :
      τ z = ∑ i, c i * (z i).trace := by
    simpa only [hc] using τ.apply_eq_sum_mul_trace_of_map_mul_comm hcomm (fun _ ↦ 0) z
  have hdiag (w : Π p : Σ i : Fin m, Fin (c i), Matrix (Fin (d p.1)) (Fin (d p.1)) k) :
      diag w = blockDiagonal' w := by
    exact (congrFun (AlgHom.coe_mk' (R := k)
      (blockDiagonal'RingHom (fun p : Σ i : Fin m, Fin (c i) ↦ Fin (d p.1)) k)
      (fun c x ↦ blockDiagonal'_smul c x)) w).trans (blockDiagonal'RingHom_apply _ _ _)
  have hblocks (z : Π i, Matrix (Fin (d i)) (Fin (d i)) k) :
      blocks z = blockDiagonal' (fun p : Σ i : Fin m, Fin (c i) ↦ z p.1) := by
    rw [AlgHom.comp_apply, hdiag]
    exact congrArg blockDiagonal' (funext fun p ↦
      (AlgHom.pi_apply _ _ p).trans (Pi.evalAlgHom_apply _ _ _ _))
  have htrace (z : Π i, Matrix (Fin (d i)) (Fin (d i)) k) : (blocks z).trace = τ z := by
    rw [hblocks, trace_blockDiagonal', hτ]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    exact (Finset.sum_const _).trans
      ((congrArg (fun a : ℕ ↦ a • (z i).trace)
        (Finset.card_univ.trans (Fintype.card_fin _))).trans (nsmul_eq_mul _ _))
  have hcard : Fintype.card ι = n := by
    apply Nat.cast_injective (R := k)
    rw [← hone, ← htrace, map_one, Matrix.trace_one]
  let φ := (reindexAlgEquiv k k (Fintype.equivFinOfCardEq hcard)).toAlgHom.comp blocks
  exact ⟨φ, fun z ↦ (trace_reindex_self (Fintype.equivFinOfCardEq hcard) (blocks z)).trans
    (htrace z)⟩

end LinearMap
