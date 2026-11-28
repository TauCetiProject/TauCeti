/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Tracial forms on products of matrix algebras

A cyclic linear form on a finite product of matrix algebras is a linear combination of the
traces of its blocks. Its coefficient in each block is its value on any diagonal matrix unit
of that block. The coefficients can be arbitrary scalars in a commutative semiring.

## Provenance

`LinearMap.exists_apply_eq_sum_mul_trace_of_map_mul_comm` adapts the matrix-unit calculation in
`New.exists_rep_of_trace` in `src/Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean`
in grh-lean (https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC). Arbitrary finite index types and semiring scalars are new here.

## References

* R. Rouquier, *Caractérisation des caractères et pseudo-caractères*, J. Algebra 180 (1996),
  571–586. https://www.math.ucla.edu/~rouquier/papers.html
-/

public section

open Matrix Fintype Finset

namespace LinearMap

attribute [local ext] Matrix.ext_linearMap

/-- A cyclic linear form on a finite product of matrix algebras is the sum of the block traces
weighted by coefficients agreeing with every diagonal matrix unit in their block.
Empty blocks are allowed. -/
theorem exists_apply_eq_sum_mul_trace_of_map_mul_comm
    {k ι : Type*} [CommSemiring k] [Fintype ι] [DecidableEq ι]
    {n : ι → Type*} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (τ : (Π i, Matrix (n i) (n i) k) →ₗ[k] k)
    (hcomm : ∀ x y, τ (x * y) = τ (y * x)) :
    ∃ c : ι → k,
      (∀ i (b : n i), τ (Pi.single i (Matrix.single b b 1)) = c i) ∧
      ∀ z, τ z = ∑ i, c i * (z i).trace := by
  classical
  let c (i : ι) := if h : Nonempty (n i) then
    τ (Pi.single i (Matrix.single (Classical.choice h) (Classical.choice h) 1)) else 0
  have hunit (i : ι) (b e : n i) :
      τ (Pi.single i (Matrix.single b e 1)) = if b = e then c i else 0 := by
    let a : n i := Classical.choice ⟨b⟩
    have h := hcomm (Pi.single i (Matrix.single b a 1))
      (Pi.single i (Matrix.single a e 1))
    split_ifs with hbe
    · simpa [hbe, c, dite_eq_left (Nonempty.intro b), a, ← Pi.single_mul] using h
    · simpa [Ne.symm hbe, ← Pi.single_mul] using h
  have hτ : τ = lsum k _ k fun i ↦ c i • traceLinearMap (n i) k k := by
    ext i b e
    have ht : (Matrix.single b e (1 : k)).trace = if b = e then 1 else 0 := by
      split_ifs with hbe <;> simp [hbe]
    simpa [-lsum_apply, lsum_piSingle, ht] using hunit i b e
  refine ⟨c, fun i b ↦ by simpa using hunit i b b, fun z ↦ ?_⟩
  simpa only [lsum_apply, LinearMap.sum_apply, comp_apply, proj_apply, LinearMap.smul_apply,
    traceLinearMap_apply, smul_eq_mul] using
    DFunLike.congr_fun hτ z

end LinearMap
