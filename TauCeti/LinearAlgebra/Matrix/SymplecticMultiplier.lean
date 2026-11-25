/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.SymplecticGroup
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Matrices scaling the symplectic form: similitude factors and the rank-two determinant

`Matrix.J l R` is the standard symplectic form on `l ⊕ l`, and `Matrix.symplecticGroup` collects
the matrices preserving it, `Aᵀ * J * A = J`. This file records what happens one step out, when
`A` merely *scales* the form. In every rank it collects the basic facts about the scaling factor
(the similitude factor); in the rank-two case — `l` a singleton — the scaling factor is forced to
be the determinant.

    Aᵀ * J l R * A = A.det • J l R,     and hence     Aᵀ * J l R * A = d • J l R ↔ A.det = d.

The second form, read left to right, is the useful one. A pairing on a rank-two module known to
scale by some quantity under a given endomorphism identifies that quantity as the determinant,
without computing it — and, since only the one endomorphism appears, without any additivity in it.

For larger `l` the corresponding conclusion is `A.det = d ^ Fintype.card l`. When `A` is
invertible and `d` is a unit, it holds in every rank without any Pfaffian: this is
`TauCeti.GSp.det_eq_multiplier_pow`, which factors a similitude through the Siegel cocharacter
and Mathlib's `Matrix.SymplecticGroup.det_eq_one`. For arbitrary `A` and `d` the usual proof goes
through the Pfaffian; there is none in this Mathlib, and the cheap determinant argument yields
only `A.det ^ 2 = (d ^ Fintype.card l) ^ 2`, which is strictly weaker over a general commutative
ring. This file proves the determinant identity for arbitrary `A` only in the rank-two case.

In every rank, the factor `c` in `M J Mᵀ = c • J` is unique when `l` is nonempty, multiplies
under products, and for invertible `M` is also the factor in `Mᵀ J M = c • J`; the block-diagonal
matrix `diag(1, c • 1)` scales `J` by `c`. These are the facts behind the multiplier of the
symplectic similitude group.

## Main results

* `Matrix.smul_J_injective` and `Matrix.eq_of_mul_J_mul_transpose_eq`: for nonempty `l`, the
  factor by which a matrix scales `J` is unique.
* `Matrix.mul_mul_J_mul_transpose_eq_mul_smul`: the scaling factors multiply under products.
* `Matrix.map_mul_J_mul_transpose_map_eq_smul`: a ring morphism carries a matrix scaling `J` by
  `c` to one scaling `J` by the image of `c`.
* `Matrix.fromBlocks_one_smul_one_mul_J_mul_transpose`: `diag(1, c • 1)` scales `J` by `c`.
* `Matrix.transpose_mul_J_mul_of_mul_J_mul_transpose` and
  `Matrix.GeneralLinearGroup.mul_J_mul_transpose_eq_smul_iff`: for an invertible matrix,
  `M J Mᵀ = c • J` and `Mᵀ J M = c • J` are equivalent.
* `Matrix.transpose_mul_J_mul_eq_det_smul`: `Aᵀ J A = det A • J`.
* `Matrix.transpose_mul_J_mul_eq_smul_iff`: the multiplier is the determinant.
* `Matrix.det_eq_of_symplectic_adjoint_of_mul_eq_smul_one`: the same, from an adjoint `B` with
  `Aᵀ J = J B` and `B A = d • 1`.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/WeilPairing/PairingDet.lean`, theorems `transpose_mul_symJ_mul`,
`det_eq_of_symplectic_adjoint` and `det_eq_of_symplectic_scaling`. The last is an implication in
the source and is stated here as an equivalence, the converse being immediate.

The source states them for a matrix of its own,
`symJ : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0]`. That definition is **replaced** by Mathlib's
canonical `Matrix.J`, which the statements here are about, so nothing standing for `symJ` is
added. The two differ by a sign: `Matrix.J l R` is
`fromBlocks 0 (-1) 1 0`, which in rank two reads `!![0, -1; 1, 0]`. The identities are insensitive
to it, both sides being linear in the form.
The source's elliptic-curve reading — the scaling being the Weil pairing's
`e (A S) (A T) = e S T ^ deg A`, and the conclusion `det = deg` — is likewise not reproduced, no
curve occurring in any statement here.
-/

public section

namespace Matrix

section Similitude

variable {l R : Type*} [DecidableEq l] [CommRing R]

/-- For nonempty `l`, the scalar multiples of `J` determine the scalar. -/
theorem smul_J_injective [Nonempty l] : Function.Injective fun c : R ↦ c • J l R := by
  intro c d h
  obtain ⟨i⟩ := ‹Nonempty l›
  simpa [Matrix.J] using congrFun (congrFun h (Sum.inr i)) (Sum.inl i)

variable [Fintype l]

/-- **The similitude factor is unique**: two scalars by which a matrix scales `J` agree. -/
theorem eq_of_mul_J_mul_transpose_eq [Nonempty l] {M : Matrix (l ⊕ l) (l ⊕ l) R} {c d : R}
    (hc : M * J l R * Mᵀ = c • J l R) (hd : M * J l R * Mᵀ = d • J l R) : c = d :=
  smul_J_injective (hc.symm.trans hd)

/-- **Similitudes compose**: if `M` scales `J` by `a` and `N` scales `J` by `b`, then `M * N`
scales `J` by `a * b`. -/
theorem mul_mul_J_mul_transpose_eq_mul_smul {M N : Matrix (l ⊕ l) (l ⊕ l) R} {a b : R}
    (hM : M * J l R * Mᵀ = a • J l R) (hN : N * J l R * Nᵀ = b • J l R) :
    M * N * J l R * (M * N)ᵀ = (a * b) • J l R := by
  calc M * N * J l R * (M * N)ᵀ = M * (N * J l R * Nᵀ) * Mᵀ := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = (a * b) • J l R := by
        rw [hN, Matrix.mul_smul, Matrix.smul_mul, hM, smul_smul, mul_comm]

/-- **Similitudes map to similitudes**: if `M` scales `J` by `c`, then its entrywise image under a
ring morphism `f` scales `J` by `f c`. -/
theorem map_mul_J_mul_transpose_map_eq_smul {S : Type*} [CommRing S] (f : R →+* S)
    {M : Matrix (l ⊕ l) (l ⊕ l) R} {c : R} (h : M * J l R * Mᵀ = c • J l R) :
    M.map f * J l S * (M.map f)ᵀ = f c • J l S := by
  simpa [Matrix.map_mul, Matrix.transpose_map, Matrix.map_smul', map_J] using
    congrArg (Matrix.map · f) h

/-- The block-diagonal matrix `diag(1, c • 1)` scales `J` by `c`. -/
theorem fromBlocks_one_smul_one_mul_J_mul_transpose (c : R) :
    fromBlocks (1 : Matrix l l R) 0 0 (c • 1) * J l R *
        (fromBlocks (1 : Matrix l l R) 0 0 (c • 1))ᵀ = c • J l R := by
  simp [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_smul]

/-- If `N` is a left inverse of `M` and `M J Mᵀ = c • J`, then also `Mᵀ J M = c • J`. -/
theorem transpose_mul_J_mul_of_mul_J_mul_transpose {M N : Matrix (l ⊕ l) (l ⊕ l) R}
    (hNM : N * M = 1) {c : R} (h : M * J l R * Mᵀ = c • J l R) :
    Mᵀ * J l R * M = c • J l R := by
  have h₁ : J l R * Mᵀ = c • (N * J l R) := by
    calc J l R * Mᵀ = N * (M * J l R * Mᵀ) := by
          simp only [← Matrix.mul_assoc, hNM, Matrix.one_mul]
      _ = c • (N * J l R) := by rw [h, Matrix.mul_smul]
  calc Mᵀ * J l R * M = -(J l R * J l R) * Mᵀ * J l R * M := by
        rw [J_squared, neg_neg, Matrix.one_mul]
    _ = -(J l R * (J l R * Mᵀ) * J l R * M) := by
        simp only [Matrix.neg_mul, Matrix.mul_assoc]
    _ = c • (J l R * N * (-(J l R * J l R)) * M) := by
        rw [h₁]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, smul_neg,
          Matrix.mul_assoc]
    _ = c • J l R := by
        rw [J_squared, neg_neg, Matrix.mul_one, Matrix.mul_assoc, hNM, Matrix.mul_one]

/-- For an invertible matrix, `M J Mᵀ = c • J` and `Mᵀ J M = c • J` are equivalent, for every
scalar `c`. -/
theorem GeneralLinearGroup.mul_J_mul_transpose_eq_smul_iff (M : GL (l ⊕ l) R) (c : R) :
    (M : Matrix (l ⊕ l) (l ⊕ l) R) * J l R * (M : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ = c • J l R ↔
      (M : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ * J l R * (M : Matrix (l ⊕ l) (l ⊕ l) R) = c • J l R := by
  refine ⟨transpose_mul_J_mul_of_mul_J_mul_transpose (Units.inv_mul M), fun h ↦ ?_⟩
  have hT : ((M⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ *
      (M : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ = 1 := by
    rw [← transpose_mul, Units.mul_inv, transpose_one]
  simpa only [transpose_transpose] using
    transpose_mul_J_mul_of_mul_J_mul_transpose hT (by simpa only [transpose_transpose] using h)

end Similitude

variable {l R : Type*} [DecidableEq l] [Fintype l] [Unique l] [CommRing R]

/-- **A rank-two matrix scales the standard symplectic form by its determinant.** -/
@[simp]
theorem transpose_mul_J_mul_eq_det_smul (A : Matrix (l ⊕ l) (l ⊕ l) R) :
    Aᵀ * J l R * A = A.det • J l R := by
  ext (i | i) (j | j) <;>
    simp [det_sum_unique A, J, Matrix.mul_apply, Unique.eq_default i, Unique.eq_default j] <;> ring

/-- **The symplectic multiplier of a rank-two matrix is its determinant.** `A` scales the standard
symplectic form by `d` exactly when `A.det = d`. Only `A` appears: no adjoint, and no additivity
in `A`. -/
theorem transpose_mul_J_mul_eq_smul_iff {A : Matrix (l ⊕ l) (l ⊕ l) R} {d : R} :
    Aᵀ * J l R * A = d • J l R ↔ A.det = d := by
  rw [transpose_mul_J_mul_eq_det_smul]
  refine ⟨fun h => ?_, by rintro rfl; rfl⟩
  simpa [J] using congrFun₂ h (Sum.inr default) (Sum.inl default)

/-- **The determinant from a symplectic adjoint.** If `B` is adjoint to `A` for the form, meaning
`Aᵀ J = J B`, and `B A = d • 1`, then `det A = d`. -/
theorem det_eq_of_symplectic_adjoint_of_mul_eq_smul_one {A B : Matrix (l ⊕ l) (l ⊕ l) R} {d : R}
    (hadj : Aᵀ * J l R = J l R * B) (hBA : B * A = d • (1 : Matrix (l ⊕ l) (l ⊕ l) R)) :
    A.det = d :=
  transpose_mul_J_mul_eq_smul_iff.1 <| by rw [hadj, mul_assoc, hBA, Matrix.mul_smul, mul_one]

end Matrix
