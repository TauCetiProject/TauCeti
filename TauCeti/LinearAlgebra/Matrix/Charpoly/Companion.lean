/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Algebra.leftMulMatrix`, `Matrix.charpoly` and `charpoly_leftMulMatrix`.
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
-- `Module.End.hasEigenvalue_iff_isRoot_charpoly` and `Matrix.charpoly_toLin'`.
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
-- `spectrum` of a matrix and `Matrix.mem_spectrum_iff_not_isUnit_eval_charpoly`.
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
-- `AdjoinRoot.powerBasis'` occurs in the statements below.
public import Mathlib.RingTheory.AdjoinRoot
-- `AdjoinRoot.minpoly_root_of_monic`: a monic `p` is the minimal polynomial of its root.
import TauCeti.RingTheory.AdjoinRoot.Minpoly

/-!
# The companion matrix of a polynomial

For a polynomial `p` of natural degree `d` over a ring `R`, the companion matrix
`Polynomial.companion p` is the `d × d` matrix, indexed by `Fin p.natDegree`, with `1` on the
subdiagonal, `-p.coeff i` in row `i` of the last column, and `0` elsewhere:

```
⎛ 0  0  ⋯  0  -c₀   ⎞
⎜ 1  0  ⋯  0  -c₁   ⎟
⎜ 0  1  ⋯  0  -c₂   ⎟
⎜ ⋮  ⋮  ⋱  ⋮   ⋮    ⎟
⎝ 0  0  ⋯  1  -cₙ₋₁ ⎠
```

with `cᵢ = p.coeff i` and `n = d`.

For monic `p` it is the matrix of multiplication by `X` on `R[X] ⧸ (p)` in the basis
`1, X, …, X ^ (d - 1)`, that is, of multiplication by the root of `AdjoinRoot p` in the power basis
`AdjoinRoot.powerBasis'` (`Polynomial.leftMulMatrix_root_eq_companion`). This identification gives
the characteristic polynomial, the determinant, the minimal polynomial and the spectrum of the
companion matrix of a monic polynomial, over any commutative ring and without extending scalars,
and its eigenvalues over a domain.
The companion matrix of `1` is the empty matrix.

The orientation is the one of `TauCeti.companionFinTwo` in size two: ones below the diagonal and
the coefficients in the last column. The transpose, with the coefficients in the last row, is the
state-transition matrix of the linear recurrence with characteristic polynomial `p`.

Companion matrices are the normal form of cyclic endomorphisms, and in a suitable basis the local
monodromies `h_∞` and `h_0⁻¹` of a hypergeometric differential equation are companion matrices
(Levelt's theorem; Beukers–Heckman, Theorem 3.5).

## Main definitions

* `Polynomial.companion`: the companion matrix of a polynomial.

## Main results

* `Polynomial.leftMulMatrix_root_eq_companion`: for monic `p`, the matrix of multiplication by the
  root of `AdjoinRoot p` in the power basis `1, root p, …` is the companion matrix.
* `Polynomial.charpoly_companion`: for monic `p` over any commutative ring, the characteristic
  polynomial of the companion matrix is `p`.
* `Polynomial.det_companion`: its determinant is `(-1) ^ d * p.coeff 0`.
* `Polynomial.minpoly_companion`: its minimal polynomial is `p`, so a companion matrix is
  non-derogatory.
* `Polynomial.mem_spectrum_companion_iff`, `Polynomial.hasEigenvalue_toLin'_companion_iff`: its
  spectrum consists of the `μ` at which `p` takes a non-unit value; over a domain its eigenvalues
  are the roots of `p` in the coefficient ring.

## References

* J. Hefferon, *Linear Algebra*, fourth edition, Topic: Linear Recurrences.
* F. Beukers and G. Heckman, *Monodromy for the hypergeometric function `ₙFₙ₋₁`*, Invent. Math. 95
  (1989), 325–354, §3, for companion matrices in Levelt's theorem.
-/

public section

open Matrix

namespace Polynomial

section Ring

variable {R : Type*} [Ring R]

/-- **The companion matrix** of a polynomial `p` of natural degree `d`: the `d × d` matrix with `1`
on the subdiagonal, `-p.coeff i` in row `i` of the last column, and `0` elsewhere. For monic `p`
it is the matrix of multiplication by `X` on `R[X] ⧸ (p)` in the basis `1, X, …, X ^ (d - 1)`
(`Polynomial.leftMulMatrix_root_eq_companion`). The definition does not need `p` to be monic, but
the results about it do. -/
def companion (p : R[X]) : Matrix (Fin p.natDegree) (Fin p.natDegree) R :=
  Matrix.of fun i j ↦
    if (i : ℕ) = j + 1 then 1 else if (j : ℕ) + 1 = p.natDegree then -p.coeff i else 0

/-- The entries of the companion matrix: `1` on the subdiagonal, `-p.coeff i` in the last column,
`0` elsewhere. The comparisons are between natural numbers, so no index wraps around. -/
@[simp]
theorem companion_apply (p : R[X]) (i j : Fin p.natDegree) :
    p.companion i j =
      if (i : ℕ) = j + 1 then 1 else if (j : ℕ) + 1 = p.natDegree then -p.coeff i else 0 :=
  (rfl)

end Ring

section CommRing

variable {R : Type*} [CommRing R] {p : R[X]}

/-- For a monic polynomial `p`, the matrix of multiplication by the root of `AdjoinRoot p` in the
power basis `1, root p, …, root p ^ (d - 1)` is the companion matrix of `p`. -/
theorem leftMulMatrix_root_eq_companion (hp : p.Monic) :
    Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hp).basis (AdjoinRoot.root p) = p.companion := by
  have h := (AdjoinRoot.powerBasis' hp).leftMulMatrix
  rw [PowerBasis.minpolyGen_eq, AdjoinRoot.powerBasis'_gen, AdjoinRoot.minpoly_root_of_monic hp]
    at h
  rw [h]
  -- Both sides are `Matrix.of` of a function of the two indices; the index types
  -- `Fin (powerBasis' hp).dim` and `Fin p.natDegree` agree only after unfolding `powerBasis'`, so
  -- the entries are compared through the natural values of the indices.
  refine congrArg Matrix.of (funext₂ fun ⟨i, hi⟩ ⟨j, hj⟩ ↦ ?_)
  have hd : (AdjoinRoot.powerBasis' hp).dim = p.natDegree := AdjoinRoot.powerBasis'_dim hp
  dsimp only
  split_ifs <;> first | rfl | omega

/-- **The characteristic polynomial of the companion matrix** of a monic polynomial `p`, over any
commutative ring, is `p`. -/
@[simp]
theorem charpoly_companion (hp : p.Monic) : p.companion.charpoly = p := by
  rw [← leftMulMatrix_root_eq_companion hp]
  exact (charpoly_leftMulMatrix (AdjoinRoot.powerBasis' hp)).trans
    (AdjoinRoot.minpoly_root_of_monic hp)

/-- The determinant of the companion matrix of a monic polynomial `p` of natural degree `d` is
`(-1) ^ d * p.coeff 0`. -/
@[simp]
theorem det_companion (hp : p.Monic) : p.companion.det = (-1) ^ p.natDegree * p.coeff 0 := by
  rw [det_eq_sign_charpoly_coeff, charpoly_companion hp, Fintype.card_fin]

/-- **The minimal polynomial of the companion matrix** of a monic polynomial `p`, over any
commutative ring, is `p`: it equals the characteristic polynomial, so a companion matrix is
non-derogatory. -/
@[simp]
theorem minpoly_companion (hp : p.Monic) : minpoly R p.companion = p := by
  rw [← leftMulMatrix_root_eq_companion hp]
  exact (minpoly.algHom_eq _ (Algebra.leftMulMatrix_injective _) _).trans
    (AdjoinRoot.minpoly_root_of_monic hp)

/-- The spectrum of the companion matrix of a monic polynomial `p` consists of the `μ` at which
`p` takes a non-unit value. -/
theorem mem_spectrum_companion_iff (hp : p.Monic) {μ : R} :
    μ ∈ spectrum R p.companion ↔ ¬IsUnit (p.eval μ) := by
  rw [mem_spectrum_iff_not_isUnit_eval_charpoly, charpoly_companion hp]

/-- Over a domain, the eigenvalues of the companion matrix of a monic polynomial `p` are the roots
of `p` in the coefficient ring: no extension of scalars is needed. -/
theorem hasEigenvalue_toLin'_companion_iff [IsDomain R] (hp : p.Monic) {μ : R} :
    Module.End.HasEigenvalue (toLin' p.companion) μ ↔ p.IsRoot μ := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin',
    charpoly_companion hp]

end CommRing

end Polynomial
