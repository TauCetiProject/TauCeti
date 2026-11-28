/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import TauCeti.Algebra.Regular.NatCast
import TauCeti.LinearAlgebra.Matrix.Charpoly.Newton

/-!
# Characteristic polynomial from additive trace-power identities

Over a commutative ring `R` without additive torsion (`[IsAddTorsionFree R]`), if the traces of
the powers of a square matrix `A` satisfy

```text
(A ^ m).trace = (B ^ m).trace + ∑ e ∈ S, α e ^ m
```

for all `m ≤ Fintype.card n`, then `A.charpoly = B.charpoly * ∏ e ∈ S, (X - C (α e))`
(`Matrix.charpoly_eq_mul_of_trace_pow_add`). The proof compares `A` with the block diagonal matrix
`Matrix.fromBlocks B 0 0 (Matrix.diagonal (fun e : S ↦ α e.val))` via Newton's identities
(`Matrix.charpoly_eq_of_trace_pow_eq`).

The corresponding statement for endomorphisms of finite free `R`-modules is
`LinearMap.charpoly_eq_mul_of_trace_pow_add`.

## Main results

* `Matrix.charpoly_eq_mul_of_trace_pow_add`: matrix version of the characteristic polynomial
  factorisation from additive trace-power identities.
* `LinearMap.charpoly_eq_mul_of_trace_pow_add`: endomorphism version on finite free modules.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
72fead102f663d5c7a407964a13dc0cf9d977207, Apache 2.0, Copyright 2026 Anthropic, PBC), file
src/Lib/General/LinearAlgebra/Eigenvalues.lean (`charpoly_eq_mul_of_trace_pow_add`).
-/

public section

open Polynomial

namespace Matrix

private lemma fromBlocks_zero₁₂_zero₂₁_pow {R m n : Type*} [CommRing R]
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (B : Matrix m m R) (D : Matrix n n R) (k : ℕ) :
    (fromBlocks B 0 0 D) ^ k = fromBlocks (B ^ k) 0 0 (D ^ k) := by
  induction k with
  | zero => simp [fromBlocks_one]
  | succ k ih => simp [pow_succ, ih, fromBlocks_multiply]

/-- Over a commutative ring without additive torsion, if `(A ^ m).trace` equals
`(B ^ m).trace + ∑ e ∈ S, α e ^ m` for every `m ≤ Fintype.card n`, then the characteristic
polynomial of `A` is `B.charpoly * ∏ e ∈ S, (X - C (α e))`. -/
theorem charpoly_eq_mul_of_trace_pow_add {R n r ι : Type*} [CommRing R] [IsAddTorsionFree R]
    [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]
    {A : Matrix n n R} {B : Matrix r r R} (S : Finset ι) (α : ι → R)
    (h_trace : ∀ m ≤ Fintype.card n,
      (A ^ m).trace = (B ^ m).trace + ∑ e ∈ S, α e ^ m) :
    A.charpoly = B.charpoly * ∏ e ∈ S, (X - C (α e)) := by
  nontriviality R
  classical
  let D : Matrix S S R := diagonal fun e ↦ α e.val
  let M : Matrix (r ⊕ S) (r ⊕ S) R := fromBlocks B 0 0 D
  have hcard : Fintype.card n = Fintype.card (r ⊕ S) := by
    have h0 := h_trace 0 (Nat.zero_le _)
    simp only [pow_zero, trace_one, Finset.sum_const, nsmul_eq_mul, mul_one] at h0
    rw [Fintype.card_sum, Fintype.card_coe]
    have hsub {a b : ℕ} (h : (a : R) = (b : R)) (hlt : a < b) : False :=
      one_ne_zero ((TauCeti.isRegular_natCast_of_ne_zero (S := R) (Nat.sub_ne_zero_of_lt hlt)).left
        (by dsimp only; rw [mul_one, mul_zero, Nat.cast_sub hlt.le, h, sub_self]))
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hsub (by simpa [Nat.cast_add] using h0) hlt
    · exact hsub (by simpa [Nat.cast_add] using h0.symm) hlt
  have hM : A.charpoly = M.charpoly := by
    refine charpoly_eq_of_trace_pow_eq hcard fun j _ hjn ↦ ?_
    rw [h_trace j hjn]
    simpa [M, D, fromBlocks_zero₁₂_zero₂₁_pow, trace_fromBlocks, diagonal_pow, trace_diagonal]
      using (Finset.sum_attach S fun e ↦ α e ^ j).symm
  rw [hM, charpoly_fromBlocks_zero₁₂, charpoly_diagonal]
  simp only [Finset.univ_eq_attach]
  rw [Finset.prod_attach S fun e ↦ X - C (α e)]

end Matrix

namespace LinearMap

/-- Over a commutative ring without additive torsion, if `trace R M (f ^ m)` equals
`trace R N (g ^ m) + ∑ e ∈ S, α e ^ m` for every `m ≤ Module.finrank R M`, then
`f.charpoly = g.charpoly * ∏ e ∈ S, (X - C (α e))`. -/
theorem charpoly_eq_mul_of_trace_pow_add {R M N ι : Type*} [CommRing R] [IsAddTorsionFree R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    {f : Module.End R M} {g : Module.End R N} (S : Finset ι) (α : ι → R)
    (h_trace : ∀ m ≤ Module.finrank R M,
      trace R M (f ^ m) = trace R N (g ^ m) + ∑ e ∈ S, α e ^ m) :
    f.charpoly = g.charpoly * ∏ e ∈ S, (X - C (α e)) := by
  nontriviality R
  classical
  let bM := Module.Free.chooseBasis R M
  let bN := Module.Free.chooseBasis R N
  rw [charpoly_def, charpoly_def]
  refine Matrix.charpoly_eq_mul_of_trace_pow_add S α fun m hm ↦ ?_
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R M) = Module.finrank R M :=
    (Module.finrank_eq_card_basis bM).symm
  simpa only [trace_eq_matrix_trace R bM, trace_eq_matrix_trace R bN, ← LinearMap.toMatrix_pow]
    using h_trace m (hcard ▸ hm)

end LinearMap
