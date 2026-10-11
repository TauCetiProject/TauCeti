/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.LinearAlgebra.Matrix.BlockSucc
public import TauCeti.LinearAlgebra.Pi

/-!
# The upper-left block embedding of an orthogonal group in the next one

An orthogonal matrix of size `n` becomes one of size `n + 1` by placing it in the upper-left block
and filling the last row and column with those of the identity matrix.  That map on matrices is
`Matrix.blockSucc`, from `TauCeti/LinearAlgebra/Matrix/BlockSucc.lean`; it commutes with the
transpose and is multiplicative and unital, so it carries orthogonal matrices to orthogonal
matrices -- and, being injective, only orthogonal ones to orthogonal ones
(`Matrix.blockSucc_mem_orthogonalGroup_iff`).  The induced **block inclusion**
`TauCeti.orthogonalBlockSucc : O(n, k) →* O(n + 1, k)` is the step of the chain
`O(1, k) ⊂ O(2, k) ⊂ ⋯` along which the orthogonal groups of the coordinate dot product are
restricted; it is the orthogonal counterpart of `TauCeti.glBlockSucc`.

The image of the inclusion is exactly the stabilizer of the last basis vector
(`TauCeti.exists_orthogonalBlockSucc_eq_iff_mulVec_single`), and this is a place where orthogonality
is doing real work: fixing the last basis vector says only that the last *column* of the matrix is
that vector, and it takes `Mᵀ * M = 1` to read off that the last *row* is too.  The corresponding
statement for `TauCeti.glBlockSucc` is false, the stabilizer of the last basis vector in
`GL (Fin (n + 1)) k` being the much larger group of matrices with arbitrary last row.

## Main definitions

* `TauCeti.orthogonalBlockSucc`: the induced group homomorphism
  `Matrix.orthogonalGroup (Fin n) k →* Matrix.orthogonalGroup (Fin (n + 1)) k`.

## Main results

* `Matrix.blockSucc_mem_orthogonalGroup_iff`: the extension of a matrix is orthogonal exactly when
  the matrix is.
* `TauCeti.orthogonalBlockSucc_injective`: the block inclusion is injective.
* `TauCeti.exists_orthogonalBlockSucc_eq_iff_mulVec_single`: an orthogonal matrix of size `n + 1` is
  an extension exactly when it fixes the last basis vector.
-/

public section

universe u

namespace Matrix

variable {k : Type u} [CommRing k] {n : ℕ}

attribute [local instance] starRingOfComm

/-- **The extension of a matrix is orthogonal exactly when the matrix is.**  Extending commutes
with the transpose (`Matrix.transpose_blockSucc`) and with products (`Matrix.blockSucc_mul`) and
takes the identity matrix to the identity matrix, so `Matrix.blockSucc M * (Matrix.blockSucc M)ᵀ`
is the extension of `M * Mᵀ`; the reverse implication is the injectivity of the extension. -/
@[simp]
theorem blockSucc_mem_orthogonalGroup_iff {M : Matrix (Fin n) (Fin n) k} :
    blockSucc M ∈ orthogonalGroup (Fin (n + 1)) k ↔ M ∈ orthogonalGroup (Fin n) k := by
  rw [mem_orthogonalGroup_iff, mem_orthogonalGroup_iff, transpose_blockSucc, ← blockSucc_mul,
    ← blockSucc_one]
  exact blockSucc_injective.eq_iff

end Matrix

namespace TauCeti

open Matrix

variable (k : Type u) [CommRing k] (n : ℕ)

attribute [local instance] starRingOfComm

/-- **The orthogonal block inclusion** `O(n, k) →* O(n + 1, k)`: an orthogonal matrix is placed in
the upper-left block and the last basis vector is fixed.  This is the step of the chain
`O(1, k) ⊂ O(2, k) ⊂ ⋯` along which representations of the orthogonal groups are restricted, the
orthogonal counterpart of `TauCeti.glBlockSucc`. -/
def orthogonalBlockSucc :
    Matrix.orthogonalGroup (Fin n) k →* Matrix.orthogonalGroup (Fin (n + 1)) k where
  toFun g := ⟨blockSucc (g : Matrix (Fin n) (Fin n) k),
    blockSucc_mem_orthogonalGroup_iff.mpr g.property⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp [blockSucc_mul])

/-- The orthogonal block inclusion has the extended matrix as its underlying matrix. -/
@[simp]
theorem coe_orthogonalBlockSucc (g : Matrix.orthogonalGroup (Fin n) k) :
    (orthogonalBlockSucc k n g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      blockSucc (g : Matrix (Fin n) (Fin n) k) :=
  (rfl)

/-- The orthogonal block inclusion is injective, so it really embeds `O(n, k)` in `O(n + 1, k)` and
the chain `O(1, k) ⊂ O(2, k) ⊂ ⋯` is a chain of subgroups. -/
theorem orthogonalBlockSucc_injective : Function.Injective (orthogonalBlockSucc k n) := by
  intro g h hgh
  refine Subtype.ext (blockSucc_injective ?_)
  rw [← coe_orthogonalBlockSucc k n, ← coe_orthogonalBlockSucc k n]
  exact congrArg
    (fun x : Matrix.orthogonalGroup (Fin (n + 1)) k =>
      (x : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) hgh

/-! ### The image of the inclusion -/

/-- **The image of the orthogonal block inclusion is the stabilizer of the last basis vector.**  An
extended matrix clearly fixes the last basis vector.  Conversely, fixing it says that the last
*column* is the last basis vector, and for an **orthogonal** matrix that already forces the last
*row* to be the last basis vector as well — the last row is read off `Mᵀ * M = 1` once the last
column is known — so the matrix is the extension of its upper-left block.

This is where orthogonality is doing the work: the subgroup of `GL (Fin (n + 1)) k` fixing the last
basis vector is much larger than the image of `TauCeti.glBlockSucc`, since nothing there constrains
the last row. -/
theorem exists_orthogonalBlockSucc_eq_iff_mulVec_single
    (g : Matrix.orthogonalGroup (Fin (n + 1)) k) :
    (∃ h : Matrix.orthogonalGroup (Fin n) k, orthogonalBlockSucc k n h = g) ↔
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ Pi.single (Fin.last n) 1 =
        Pi.single (Fin.last n) 1 := by
  constructor
  · rintro ⟨h, rfl⟩
    rw [coe_orthogonalBlockSucc, ← Fin.snoc_zero_eq_single, blockSucc_mulVec, Fin.init_snoc,
      Fin.snoc_last, mulVec_zero]
  · intro hfix
    have hgmem : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∈ orthogonalGroup (Fin (n + 1)) k :=
      g.property
    set M := (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    -- Fixing the last basis vector says the last column of `M` is that basis vector.
    have hcol : ∀ i, M i (Fin.last n) = (Pi.single (Fin.last n) 1 : Fin (n + 1) → k) i := by
      intro i
      have hi := congrFun hfix i
      rwa [mulVec_single_one, Matrix.col_apply] at hi
    -- Orthogonality then reads the last row off `Mᵀ * M = 1`.
    have hrow : ∀ i,
        M (Fin.last n) i = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) i := fun i => by
      have h1 := congrFun (congrFun
        ((mem_orthogonalGroup_iff' (Fin (n + 1)) k).mp hgmem) (Fin.last n)) i
      rw [Matrix.mul_apply] at h1
      rw [← h1, Finset.sum_eq_single (Fin.last n)
        (fun j _ hj => by rw [transpose_apply, hcol j, Pi.single_eq_of_ne hj, zero_mul])
        (fun h => absurd (Finset.mem_univ _) h), transpose_apply, hcol (Fin.last n),
        Pi.single_eq_same, one_mul]
    -- So `M` is the extension of its upper-left block.
    have hblock : blockSucc (Matrix.of fun i j => M i.castSucc j.castSucc) = M := by
      ext i j
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => rw [blockSucc_last_last, hrow, Matrix.one_apply_eq]
        | cast j =>
          rw [blockSucc_last_castSucc, hrow, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne']
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          rw [blockSucc_castSucc_last, hcol, Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne]
        | cast j => rw [blockSucc_castSucc_castSucc, Matrix.of_apply]
    refine ⟨⟨Matrix.of fun i j => M i.castSucc j.castSucc,
      blockSucc_mem_orthogonalGroup_iff.mp ?_⟩, Subtype.ext ?_⟩
    · rw [hblock]
      exact hgmem
    · rw [coe_orthogonalBlockSucc, hblock]

end TauCeti
