/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# Families of matrices spanning the matrix algebra

A family `v : ι → Matrix n n R` **spans** the matrix algebra when the `R`-span of its range is
everything. This file records two general consequences of spanning, and a criterion for it over
a local ring.

* A matrix commuting with a spanning family commutes with every matrix unit, so it is scalar.
* Spanning survives every ring homomorphism `f : R →+* S`: the entrywise images span `M_n(S)`,
  because the image of `M_n(R)` contains the matrix units.
* Over a local ring `R`, spanning can be checked modulo the maximal ideal: if the reductions
  span `M_n(k)` over the residue field `k`, the family spans `M_n(R)`. This is Nakayama's lemma
  (`IsLocalRing.map_mkQ_eq_top`), applied to the finite module `M_n(R)`.

The kernel of the reduction `M_n(R) → M_n(k)` is `𝔪 • M_n(R)`, the matrices with all entries in
the maximal ideal `𝔪`.

## Main results

* `Matrix.mem_range_scalar_of_commute_of_span_eq_top`: a matrix commuting with a spanning family
  is scalar.
* `Matrix.span_range_map_eq_top`: the image of a spanning family under a ring homomorphism spans.
* `Matrix.mem_ideal_smul_top_iff`: a matrix lies in `I • M_n(R)` exactly when its entries lie
  in the ideal `I`.
* `IsLocalRing.mem_maximalIdeal_smul_top_iff_map_residue_eq_zero`: so a matrix over a local ring
  lies in `𝔪 • M_n(R)` exactly when its reduction vanishes.
* `IsLocalRing.span_range_eq_top_of_span_range_map_residue_eq_top`: over a local ring, a family
  whose reductions span the matrix algebra over the residue field spans.

## Provenance

Adapted from `New.Selmer.IsLatticeIn.span_range_eq_top_of_map_pow_eq_map_conj` and the private
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

/-- A matrix lies in `I • M_n(R)` exactly when all its entries lie in the ideal `I`. -/
theorem mem_ideal_smul_top_iff [CommSemiring R] [Finite n] (I : Ideal R) {x : Matrix n n R} :
    x ∈ I • (⊤ : Submodule R (Matrix n n R)) ↔ ∀ i j, x i j ∈ I := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · refine smul_induction_on hx (fun r hr m _ i j ↦ ?_) fun y z hy hz i j ↦ ?_
    · simpa using I.mul_mem_right (m i j) hr
    · simpa using I.add_mem (hy i j) (hz i j)
  -- Otherwise `x` is the sum of its entries, all in `I`, times the matrix units.
  have := Fintype.ofFinite n
  classical
  rw [matrix_eq_sum_single x]
  refine sum_mem fun i _ ↦ sum_mem fun j _ ↦ ?_
  rw [show single i j (x i j) = x i j • single i j 1 by simp [smul_single]]
  exact smul_mem_smul (hx i j) mem_top

end Matrix

namespace IsLocalRing

variable {R ι n : Type*} [CommRing R] [IsLocalRing R]

/-- A matrix over a local ring lies in `𝔪 • M_n(R)` exactly when its reduction vanishes, that is
when all its entries lie in the maximal ideal `𝔪`. -/
theorem mem_maximalIdeal_smul_top_iff_map_residue_eq_zero [Finite n] {x : Matrix n n R} :
    x ∈ maximalIdeal R • (⊤ : Submodule R (Matrix n n R)) ↔ x.map (residue R) = 0 := by
  simp [Matrix.mem_ideal_smul_top_iff, ← Matrix.ext_iff, residue_eq_zero_iff]

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
  refine mem_maximalIdeal_smul_top_iff_map_residue_eq_zero.mpr ?_
  ext i j
  have := congrFun₂ hc i j
  simp only [Finsupp.sum, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul] at this
  simp [Finsupp.sum, Matrix.sum_apply, map_sum, lift, surjInv_eq, this]

end IsLocalRing
