/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Trace.Pi
import TauCeti.Data.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.Trace.Basic

/-!
# Realizing an integral tracial form by matrices

A tracial linear form on a finite product of matrix algebras over a commutative semiring of
characteristic zero is the trace of a matrix representation if its values on every diagonal matrix
unit are natural numbers. Empty blocks are allowed. Its value at one is the dimension of the
representation.
This includes dimension zero. The matrix representation repeats each Wedderburn block with
the multiplicity prescribed by the form. Both the input blocks and the output matrices may use
arbitrary finite index types.

## Main results

* `LinearMap.exists_algHom_trace_eq_pi_matrix` realizes the form by matrices indexed by any
  finite type whose cardinality is its value at one.

## Provenance

`LinearMap.exists_algHom_trace_eq_pi_matrix` adapts the repeated-block construction
of `New.exists_rep_of_trace` in `src/Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean`
in grh-lean (https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC). The algebra-homomorphism formulation over commutative semirings
is new here.

## References

* R. Rouquier, *Caractérisation des caractères et pseudo-caractères*, J. Algebra 180 (1996),
  571–586. https://www.math.ucla.edu/~rouquier/papers.html
-/

public section

noncomputable section

open Matrix Fintype Finset LinearMap

namespace LinearMap

variable {k : Type*} [CommSemiring k]

/-- A tracial form on a finite product of matrix algebras is the trace of an algebra
homomorphism if its values on diagonal matrix units are natural numbers. Empty blocks are allowed.
The matrix size is its value at one; it may be zero. -/
theorem exists_algHom_trace_eq_pi_matrix [CharZero k]
    {ι : Type*} [Finite ι] [DecidableEq ι]
    {n : ι → Type*} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (τ : (Π i, Matrix (n i) (n i) k) →ₗ[k] k)
    (hcomm : ∀ x y, τ (x * y) = τ (y * x))
    (hnat : ∀ i (b : n i), ∃ c : ℕ, τ (Pi.single i (Matrix.single b b 1)) = c)
    {N : Type*} [Fintype N] [DecidableEq N] (hone : τ 1 = Fintype.card N) :
    ∃ φ : (Π i, Matrix (n i) (n i) k) →ₐ[k] Matrix N N k,
      ∀ z, (φ z).trace = τ z := by
  classical
  let _ := Fintype.ofFinite ι
  let c (i : ι) := if h : Nonempty (n i) then (hnat i (Classical.choice h)).choose else 0
  obtain ⟨w, hw, hτw⟩ := τ.exists_apply_eq_sum_mul_trace_of_map_mul_comm hcomm
  let κ := Σ p : Σ i : ι, Fin (c i), n p.1
  let blocks : (Π i, Matrix (n i) (n i) k) →ₐ[k] Matrix κ κ k :=
    (blockDiagonal'AlgHom _ k k).comp (AlgHom.pi fun p ↦ Pi.evalAlgHom k _ p.1)
  have hτ (z : Π i, Matrix (n i) (n i) k) :
      τ z = ∑ i, c i * (z i).trace := by
    rw [hτw]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : Nonempty (n i)
    · rw [← hw i (Classical.choice hi), (hnat i (Classical.choice hi)).choose_spec]
      simp only [c, dite_eq_left hi]
    · have : IsEmpty (n i) := not_nonempty_iff.mp hi
      simp [Matrix.trace, Matrix.diag]
  have htrace (z : Π i, Matrix (n i) (n i) k) : (blocks z).trace = τ z := by
    simp only [blocks, AlgHom.comp_apply, blockDiagonal'AlgHom_apply]
    rw [trace_blockDiagonal', hτ, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    simp only [AlgHom.pi_apply, Pi.evalAlgHom_apply]
    simpa only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      (Finset.sum_const (s := Finset.univ (α := Fin (c i))) (z i).trace)
  have hcard : Fintype.card κ = Fintype.card N := by
    apply Nat.cast_injective (R := k)
    rw [← hone, ← htrace, map_one, Matrix.trace_one]
  let φ := (reindexAlgEquiv k k (Fintype.equivOfCardEq hcard)).toAlgHom.comp blocks
  refine ⟨φ, fun z ↦ ?_⟩
  simpa only [φ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    coe_reindexAlgEquiv, trace_reindex_self] using htrace z

end LinearMap
