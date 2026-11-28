/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Block-edgewise Kronecker operators and pairing maps

Given a finite set `Ed` of edges, a finite index set `H`, and a finite index set `L`, a vector
indexed by `(H × Ed) × L` represents a function on edges with values in `O ^ H ⊗ O ^ L`. For a
family of matrices `u : Ed → Matrix H H O` and a matrix `A : Matrix L L O`, the Kronecker product
`blockDiagonal u ⊗ₖ A` acts edgewise by `u e ⊗ A`.

## Main definitions and results

* `TauCeti.edgewise`: the matrix `blockDiagonal u ⊗ₖ A` on `(H × Ed) × L`.
* `TauCeti.edgewise_mul`: multiplicativity `edgewise u A * edgewise u' A' =
  edgewise (fun e ↦ u e * u' e) (A * A')`.
* `TauCeti.edgewise_mulVec`: fiberwise evaluation of `edgewise u A *ᵥ ψ` at `(h', e) : H × Ed`.
* `TauCeti.pairingMap`, `TauCeti.nearInverse`: the pairing matrix `Q'ᵀ * edgewise u (diagonal b)`
  and its opposite-direction near inverse `edgewise u⁻¹ (Av * diagonal b') * R'ᵀ`.
* `TauCeti.pairingMap_mul_nearInverse_apply`: explicit entry formula for
  `(pairingMap u b Q' * nearInverse u Av b' R') i j` as a sum of weighted pairings over `H × Ed`.

## References

* Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`),
  `src/New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean`
  (`New.edgewise`, `New.edgewise_mul`, `New.edgewise_mulVec`, `New.pairingMap`, `New.nearInverse`,
  `New.pairingMap_mul_nearInverse_apply`).
-/

public section

namespace TauCeti

open Matrix
open scoped Kronecker

/-- The matrix on `(H × Ed) × L` that acts on the value at edge `e` by `u e ⊗ A`. -/
def edgewise {O H Ed L : Type*} [CommRing O] [DecidableEq Ed] (u : Ed → Matrix H H O)
    (A : Matrix L L O) : Matrix ((H × Ed) × L) ((H × Ed) × L) O :=
  blockDiagonal u ⊗ₖ A

/-- Multiplying two edgewise operators multiplies their edge matrices and their `L`-factors. -/
theorem edgewise_mul {O H Ed L : Type*} [CommRing O] [DecidableEq Ed] [Fintype H] [Fintype Ed]
    [Fintype L] (u u' : Ed → Matrix H H O) (A A' : Matrix L L O) :
    edgewise u A * edgewise u' A' = edgewise (fun e : Ed ↦ u e * u' e) (A * A') := by
  simp only [edgewise, ← mul_kronecker_mul, ← blockDiagonal_mul]

/-- The value of `edgewise u A *ᵥ ψ` at `x = (h', e)` is `A` applied to the linear combination of
`ψ ((h, e), ·)` with coefficients `u e h' h`. -/
theorem edgewise_mulVec {O H Ed L : Type*} [CommRing O] [DecidableEq Ed] [Fintype H] [Fintype Ed]
    [Fintype L] (u : Ed → Matrix H H O) (A : Matrix L L O) (ψ : (H × Ed) × L → O)
    (x : H × Ed) :
    (fun l : L ↦ (edgewise u A *ᵥ ψ) (x, l)) =
      A *ᵥ ∑ h : H, u x.snd x.fst h • fun l : L ↦ ψ ((h, x.snd), l) := by
  ext l
  simp [edgewise, mulVec, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply, Finset.mul_sum,
    Finset.sum_comm (γ := L), mul_left_comm, mul_assoc]

/-- The pairing matrix `Q'ᵀ * edgewise (fun e ↦ (u e).val) (diagonal b)` sending functions on edges
to their pairings with the columns of `Q'`. -/
def pairingMap {O H Ed L E : Type*} [CommRing O] [DecidableEq Ed] [Fintype H] [DecidableEq H]
    [Fintype Ed] [Fintype L] [DecidableEq L] (u : Ed → GL H O) (b : L → O)
    (Q' : Matrix ((H × Ed) × L) E O) : Matrix E ((H × Ed) × L) O :=
  Q'ᵀ * edgewise (fun e : Ed ↦ (u e).val) (diagonal b)

/-- The opposite-direction near-inverse matrix
`edgewise (fun e ↦ (u e)⁻¹.val) (Av * diagonal b') * R'ᵀ`. -/
def nearInverse {O H Ed L E : Type*} [CommRing O] [DecidableEq Ed] [Fintype H] [DecidableEq H]
    [Fintype Ed] [Fintype L] [DecidableEq L] (u : Ed → GL H O) (Av : Matrix L L O) (b' : L → O)
    (R' : Matrix E ((H × Ed) × L) O) : Matrix ((H × Ed) × L) E O :=
  edgewise (fun e : Ed ↦ (u e)⁻¹.val) (Av * diagonal b') * R'ᵀ

/-- The `(i, j)` entry of `pairingMap u b Q' * nearInverse u Av b' R'` is the sum over
`x : H × Ed` of the `b`-weighted pairing between column `i` of `Q'` at `x` and `Av` applied to
`b'` times row `j` of `R'` at `x`. -/
theorem pairingMap_mul_nearInverse_apply {O H Ed L E : Type*} [CommRing O] [DecidableEq Ed]
    [Fintype H] [Fintype Ed] [Fintype L] [DecidableEq H] [DecidableEq L] (u : Ed → GL H O)
    (Av : Matrix L L O) (b b' : L → O) (Q' : Matrix ((H × Ed) × L) E O)
    (R' : Matrix E ((H × Ed) × L) O) (i j : E) :
    (pairingMap u b Q' * nearInverse u Av b' R') i j =
      ∑ x : H × Ed, (fun l : L ↦ Q' (x, l) i) ⬝ᵥ (b * Av *ᵥ (b' * fun l : L ↦ R' j (x, l))) := by
  let B : Matrix L L O := diagonal b * (Av * diagonal b')
  have h_cancel : edgewise (fun e : Ed ↦ (u e).val) (diagonal b) *
      edgewise (fun e : Ed ↦ (u e)⁻¹.val) (Av * diagonal b') =
        (1 : Matrix (H × Ed) (H × Ed) O) ⊗ₖ B := by
    have h_units : (fun e : Ed ↦ (u e).val * (u e)⁻¹.val) = 1 := funext fun e ↦ (u e).mul_inv
    rw [edgewise_mul, h_units, edgewise, blockDiagonal_one]
  have h_product : pairingMap u b Q' * nearInverse u Av b' R' =
      Q'ᵀ * ((1 : Matrix (H × Ed) (H × Ed) O) ⊗ₖ B * R'ᵀ) := by
    simp only [pairingMap, nearInverse, ← h_cancel, Matrix.mul_assoc]
  have hB (v : L → O) : B *ᵥ v = b * Av *ᵥ (b' * v) := by
    have h_diagonal (d w : L → O) : diagonal d *ᵥ w = d * w := funext (mulVec_diagonal d w)
    simp only [B, ← mulVec_mulVec, h_diagonal]
  calc (pairingMap u b Q' * nearInverse u Av b' R') i j
      = ∑ x : H × Ed, (fun l : L ↦ Q' (x, l) i) ⬝ᵥ (B *ᵥ fun l : L ↦ R' j (x, l)) := by
        rw [h_product]
        simp [Matrix.mul_apply, Fintype.sum_prod_type (α₁ := H × Ed), Matrix.one_apply, dotProduct,
          mulVec]
    _ = _ := by simp only [hB]

end TauCeti
