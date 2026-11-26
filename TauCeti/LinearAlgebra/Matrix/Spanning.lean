/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import TauCeti.LinearAlgebra.Eigenspace.ConjugatePow

/-!
# Families of matrices spanning the matrix algebra

A family `v : ι → Matrix n n R` **spans** the matrix algebra when the `R`-span of its range is
everything. This file records three general consequences of spanning, and a criterion for it over
a local ring.

* A matrix commuting with a spanning family commutes with every matrix unit, so it is scalar.
* Spanning survives every ring homomorphism `f : R →+* S`: the entrywise images span `M_n(S)`,
  because the image of `M_n(R)` contains the matrix units.
* Over a local ring `R`, spanning can be checked modulo the maximal ideal: if the reductions
  span `M_n(k)` over the residue field `k`, the family spans `M_n(R)`. This is Nakayama's lemma
  (`IsLocalRing.map_mkQ_eq_top`), applied to the finite module `M_n(R)`.

Combined with `Matrix.span_range_pow_mul_pow_eq_top_of_mul_eq_mul_pow` over the residue field,
the last point lifts the spanning criterion for a matrix conjugate to a power of itself to local
rings: if `A * B = B * A ^ q` with `B` invertible, and the reduction of `A` has an eigenvalue `μ`
whose powers `μ ^ q ^ i`, `i < n`, are pairwise distinct in the residue field, then the
`B ^ a * A ^ b`, `a, b < n`, span `M_n(R)`.

## Main results

* `Matrix.mem_range_scalar_of_commute_of_span_eq_top`: a matrix commuting with a spanning family
  is scalar.
* `Matrix.span_range_map_eq_top`: the image of a spanning family under a ring homomorphism spans.
* `IsLocalRing.span_range_eq_top_of_span_range_map_residue_eq_top`: over a local ring, a family
  whose reductions span the matrix algebra over the residue field spans.
* `IsLocalRing.span_range_pow_mul_pow_eq_top_of_mul_eq_mul_pow`: the spanning criterion for a
  matrix conjugate to a power of itself, over a local ring.

## Provenance

Adapted from `New.Selmer.IsLatticeIn.span_range_eq_top_of_map_pow_eq_map_conj`,
`New.Selmer.eq_bot_or_eq_top_of_span_eq_top` and the private
`Matrix.exists_eq_smul_one_of_commute_of_span_eq_top` in
`src/Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). There the
lift from the residue field is a determinant computation in a basis of matrix units; here it is
Nakayama's lemma, which needs no counting and applies to families of any size.
-/

public section

open Function Submodule

namespace Matrix

variable {R ι n : Type*}

/-- **A matrix commuting with a spanning family is scalar.** If the `v i` span `M_n(R)` and every
`v i` commutes with `M`, then `M` commutes with every matrix, in particular with the matrix units,
so `M` is a scalar matrix. -/
theorem mem_range_scalar_of_commute_of_span_eq_top [Fintype n] [DecidableEq n] [CommSemiring R]
    {v : ι → Matrix n n R} (hv : span R (Set.range v) = ⊤) {M : Matrix n n R}
    (h : ∀ i, Commute (v i) M) :
    M ∈ Set.range (scalar n) :=
  mem_range_scalar_of_commute_single fun _ _ _ ↦
    Commute.span_left (Set.forall_mem_range.mpr h) _ (hv ▸ mem_top)

/-- **Spanning survives a change of rings.** If the `v i` span `M_n(R)` and `f : R →+* S` is a
ring homomorphism, the matrices `(v i).map f` span `M_n(S)`: the `S`-span of their range contains
the image of the `R`-span of the `v i`, hence the matrix units. -/
theorem span_range_map_eq_top [Finite n] {S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) {v : ι → Matrix n n R} (hv : span R (Set.range v) = ⊤) :
    span S (Set.range fun i ↦ (v i).map f) = ⊤ := by
  have := Fintype.ofFinite n
  classical
  set P := span S (Set.range fun i ↦ (v i).map f)
  have hmap (x : Matrix n n R) : x.map f ∈ P := by
    induction (hv ▸ mem_top : x ∈ span R (Set.range v)) using span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact subset_span ⟨i, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => simpa [Matrix.map_add f (map_add f)] using P.add_mem hx hy
    | smul c x _ hx => simpa [Matrix.map_smul'] using P.smul_mem (f c) hx
  refine eq_top_iff'.mpr fun y ↦ ?_
  rw [matrix_eq_sum_single y]
  refine sum_mem fun i _ ↦ sum_mem fun j _ ↦ ?_
  simpa [map_single, smul_single] using P.smul_mem (y i j) (hmap (single i j 1))

end Matrix

namespace IsLocalRing

variable {R ι n : Type*} [CommRing R] [IsLocalRing R]

/-- A matrix over a local ring whose reduction vanishes lies in `𝔪 • M_n(R)`: it is the sum of its
entries, all in the maximal ideal `𝔪`, times the matrix units. -/
private theorem mem_maximalIdeal_smul_top_of_map_residue_eq_zero [Finite n]
    {x : Matrix n n R} (hx : x.map (residue R) = 0) :
    x ∈ maximalIdeal R • (⊤ : Submodule R (Matrix n n R)) := by
  have := Fintype.ofFinite n
  classical
  rw [Matrix.matrix_eq_sum_single x]
  refine sum_mem fun i _ ↦ sum_mem fun j _ ↦ ?_
  rw [show Matrix.single i j (x i j) = x i j • Matrix.single i j 1 by simp [Matrix.smul_single]]
  exact smul_mem_smul ((residue_eq_zero_iff _).mp (by simpa using congrFun₂ hx i j)) mem_top

/-- **Nakayama's lemma for spanning families of matrices.** Over a local ring `R`, a family of
matrices whose reductions span the matrix algebra over the residue field spans `M_n(R)`. -/
theorem span_range_eq_top_of_span_range_map_residue_eq_top [Finite n] {v : ι → Matrix n n R}
    (hv : span (ResidueField R) (Set.range fun i ↦ (v i).map (residue R)) = ⊤) :
    span R (Set.range v) = ⊤ := by
  have := Fintype.ofFinite n
  classical
  rw [← map_mkQ_eq_top, eq_top_iff']
  intro z
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (hv ▸ mem_top : x.map (residue R) ∈ span (ResidueField R) _)
  -- Lift the coefficients of `x.map (residue R)` to `R`.
  let lift := surjInv (residue_surjective (R := R))
  refine ⟨c.sum fun i a ↦ lift a • v i,
    sum_mem fun i _ ↦ smul_mem _ _ (subset_span ⟨i, rfl⟩), ?_⟩
  rw [mkQ_apply, Submodule.Quotient.eq]
  refine mem_maximalIdeal_smul_top_of_map_residue_eq_zero ?_
  ext i j
  have := congrFun₂ hc i j
  simp only [Finsupp.sum, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul] at this
  simp [Finsupp.sum, Matrix.sum_apply, map_sum, lift, surjInv_eq, this]

/-- **A matrix conjugate to a power of itself, over a local ring.** Let `A * B = B * A ^ q` in
`M_n(R)` with `B` invertible, and let the reduction of `A` have an eigenvalue `μ` in the residue
field whose powers `μ ^ q ^ i`, `i < n`, are pairwise distinct. Then the matrices `B ^ a * A ^ b`,
`a, b < n`, span `M_n(R)`: their reductions span over the residue field
(`Matrix.span_range_pow_mul_pow_eq_top_of_mul_eq_mul_pow`), and Nakayama's lemma lifts this. -/
theorem span_range_pow_mul_pow_eq_top_of_mul_eq_mul_pow [Fintype n] [DecidableEq n]
    {A B : Matrix n n R} {q : ℕ} (hAB : A * B = B * A ^ q) (hB : IsUnit B) {μ : ResidueField R}
    (hμ : (A.map (residue R)).charpoly.IsRoot μ)
    (hdist : Injective fun i : Fin (Fintype.card n) ↦ μ ^ q ^ (i : ℕ)) :
    span R (Set.range fun p : Fin (Fintype.card n) × Fin (Fintype.card n) ↦
      B ^ (p.1 : ℕ) * A ^ (p.2 : ℕ)) = ⊤ := by
  let f := (residue R).mapMatrix (m := n)
  have hAB' : f A * f B = f B * f A ^ q := by rw [← map_mul, ← map_pow, ← map_mul, hAB]
  refine span_range_eq_top_of_span_range_map_residue_eq_top ?_
  convert Matrix.span_range_pow_mul_pow_eq_top_of_mul_eq_mul_pow hAB' (hB.map f) hμ hdist
    using 3 with p
  simp [f, ← RingHom.mapMatrix_apply]

end IsLocalRing
