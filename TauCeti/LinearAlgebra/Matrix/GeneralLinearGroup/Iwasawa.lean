/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cholesky.Topology
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Positive
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Unitary
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Algebra.Group.Units

/-!
# The Iwasawa decomposition of `GL n ℝ`

Every invertible real matrix factors uniquely as `g = k a u`, with `k` orthogonal, `a` diagonal
with positive diagonal entries, and `u` upper unitriangular, and the three factors depend
continuously on `g`. This is the Iwasawa decomposition `G = K A N` of the real reductive group
`G = GL n ℝ`, with maximal compact subgroup `K = O(n)`, `A` the positive diagonal matrices, and
`N` the unipotent radical of the upper triangular Borel subgroup. In matrix
language it is the Gram-Schmidt process, or the `QR` factorization of an invertible matrix with
the triangular factor `R = a u` normalized to have a positive diagonal.

The three factors are the subgroups `unitarySubgroup (GL (Fin n) ℝ)` (the orthogonal matrices,
the star of a real matrix being its transpose), `TauCeti.posDiagonalSubgroup (Fin n) ℝ` and
`TauCeti.upperUnitriangularGroup (Fin n) ℝ`, and `TauCeti.iwasawaHomeomorph n` is the
homeomorphism `K × A × N ≃ₜ GL n ℝ` given by multiplication. The statement is topological: that
the factors also depend smoothly on `g`, making the decomposition a diffeomorphism, is not proved
here.

## The construction

The factorization is read off the Cholesky factorization of the Gram matrix `gᵀ g`. If
`g = k a u`, then `gᵀ g = (a u)ᵀ (a u)`, and `(a u)ᵀ` is lower triangular with positive diagonal,
so it is the Cholesky factor `L` of `gᵀ g` (`TauCeti.eq_cholesky_of_mul_transpose_self_eq`). This
proves uniqueness and dictates the inverse map: `a` is the diagonal of `L`, `k = (g⁻¹)ᵀ L` is
orthogonal because `L Lᵀ = gᵀ g`, and `u = a⁻¹ k⁻¹ g = a⁻¹ Lᵀ`. Continuity of the inverse map is
the continuity of the Cholesky factorization, `TauCeti.continuous_cholesky`.

## Main definitions

* `TauCeti.iwasawaHomeomorph n`: the Iwasawa decomposition, the homeomorphism
  `O(n) × A × N ≃ₜ GL n ℝ` sending `(k, a, u)` to `k a u`.

## Main results

* `TauCeti.iwasawaHomeomorph_apply`: the decomposition multiplies the three factors.
* `TauCeti.existsUnique_iwasawa`: every invertible real matrix is uniquely `k a u`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Birkhäuser, 2002,
  Section VI.4 (the Iwasawa decomposition).
* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Section 2.1 (the `QR` factorization).
-/

public section

noncomputable section

open Matrix

namespace TauCeti

variable {n : ℕ}

/-- The Gram matrix `gᵀ g` of an invertible real matrix, as a positive-definite matrix. -/
private def gramPosDefMatrix (g : GL (Fin n) ℝ) : PosDefMatrix n := by
  refine ⟨⟨(g : Matrix (Fin n) (Fin n) ℝ)ᵀ * g, ?_⟩, ?_⟩
  · have h := isHermitian_conjTranspose_mul_self (g : Matrix (Fin n) (Fin n) ℝ)
    rw [conjTranspose_eq_transpose_of_trivial] at h
    exact isHermitian_iff_isSelfAdjoint.mp h
  · simpa [conjTranspose_eq_transpose_of_trivial] using
      PosDef.conjTranspose_mul_self (g : Matrix (Fin n) (Fin n) ℝ)
        (mulVec_injective_of_isUnit g.isUnit)

private theorem coe_gramPosDefMatrix (g : GL (Fin n) ℝ) :
    ((gramPosDefMatrix g).1 : Matrix (Fin n) (Fin n) ℝ) =
      (g : Matrix (Fin n) (Fin n) ℝ)ᵀ * (g : Matrix (Fin n) (Fin n) ℝ) :=
  (rfl)

/-- The lower-triangular Cholesky factor `L` of the Gram matrix `gᵀ g`, so that
`L Lᵀ = gᵀ g`. -/
private def gramCholesky (g : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (cholesky (gramPosDefMatrix g)).1

private theorem gramCholesky_mul_transpose (g : GL (Fin n) ℝ) :
    gramCholesky g * (gramCholesky g)ᵀ =
      (g : Matrix (Fin n) (Fin n) ℝ)ᵀ * (g : Matrix (Fin n) (Fin n) ℝ) :=
  (cholesky_mul_transpose (gramPosDefMatrix g)).trans (coe_gramPosDefMatrix g)

private theorem gramCholesky_isLowerTriangular (g : GL (Fin n) ℝ) :
    (gramCholesky g).IsLowerTriangular :=
  (cholesky (gramPosDefMatrix g)).2.1

private theorem gramCholesky_diag_pos (g : GL (Fin n) ℝ) (i : Fin n) :
    0 < gramCholesky g i i :=
  (cholesky (gramPosDefMatrix g)).2.2 i

private theorem continuous_gramCholesky : Continuous (gramCholesky (n := n)) := by
  have hgram : Continuous (gramPosDefMatrix (n := n)) :=
    continuous_induced_rng.2 <| continuous_induced_rng.2 <|
      Units.continuous_val.matrix_transpose.matrix_mul Units.continuous_val
  exact continuous_subtype_val.comp (continuous_cholesky.comp hgram)

/-- The matrix `(g⁻¹)ᵀ L` has right inverse its transpose `Lᵀ g⁻¹`, because the Cholesky factor
`L` of `gᵀ g` satisfies `L Lᵀ = gᵀ g`. -/
private theorem gramCholesky_orthogonal (g : GL (Fin n) ℝ) :
    ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * gramCholesky g *
        ((gramCholesky g)ᵀ * ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) = 1 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (gramCholesky g), gramCholesky_mul_transpose]
  simp [← transpose_mul]

/-- The orthogonal factor `(g⁻¹)ᵀ L` of the Iwasawa decomposition of `g`, as an element of
`GL n ℝ` with inverse its transpose. -/
private def iwasawaOrthogonal (g : GL (Fin n) ℝ) : GL (Fin n) ℝ where
  val := ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * gramCholesky g
  inv := (gramCholesky g)ᵀ * ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
  val_inv := gramCholesky_orthogonal g
  inv_val := mul_eq_one_comm.1 (gramCholesky_orthogonal g)

private theorem coe_iwasawaOrthogonal (g : GL (Fin n) ℝ) :
    (iwasawaOrthogonal g : Matrix (Fin n) (Fin n) ℝ) =
      ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * gramCholesky g :=
  (rfl)

private theorem coe_inv_iwasawaOrthogonal (g : GL (Fin n) ℝ) :
    (((iwasawaOrthogonal g)⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      (gramCholesky g)ᵀ * ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) :=
  (rfl)

private theorem iwasawaOrthogonal_mem (g : GL (Fin n) ℝ) :
    iwasawaOrthogonal g ∈ unitarySubgroup (GL (Fin n) ℝ) := by
  rw [mem_unitarySubgroup_GL_iff, coe_iwasawaOrthogonal, transpose_mul, transpose_transpose]
  exact gramCholesky_orthogonal g

/-- The positive diagonal factor of the Iwasawa decomposition of `g`: the diagonal of the
Cholesky factor of `gᵀ g`. -/
private def iwasawaDiagonal (g : GL (Fin n) ℝ) : GL (Fin n) ℝ :=
  diagGL fun i => Units.mk0 (gramCholesky g i i) (gramCholesky_diag_pos g i).ne'

private theorem coe_iwasawaDiagonal (g : GL (Fin n) ℝ) :
    (iwasawaDiagonal g : Matrix (Fin n) (Fin n) ℝ) = diagonal fun i => gramCholesky g i i := by
  simp [iwasawaDiagonal]

private theorem coe_inv_iwasawaDiagonal (g : GL (Fin n) ℝ) :
    (((iwasawaDiagonal g)⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      diagonal fun i => (gramCholesky g i i)⁻¹ :=
  coe_inv_of_coe_eq_diagonal (fun i => (gramCholesky_diag_pos g i).ne') (coe_iwasawaDiagonal g)

private theorem iwasawaDiagonal_mem (g : GL (Fin n) ℝ) :
    iwasawaDiagonal g ∈ posDiagonalSubgroup (Fin n) ℝ :=
  mem_posDiagonalSubgroup_iff.2 ⟨_, gramCholesky_diag_pos g, coe_iwasawaDiagonal g⟩

/-- The upper unitriangular factor `a⁻¹ k⁻¹ g` of the Iwasawa decomposition of `g`. Its matrix is
`a⁻¹ Lᵀ`. -/
private def iwasawaUnitriangular (g : GL (Fin n) ℝ) : GL (Fin n) ℝ :=
  (iwasawaDiagonal g)⁻¹ * (iwasawaOrthogonal g)⁻¹ * g

private theorem coe_iwasawaUnitriangular (g : GL (Fin n) ℝ) :
    (iwasawaUnitriangular g : Matrix (Fin n) (Fin n) ℝ) =
      (diagonal fun i => (gramCholesky g i i)⁻¹) * (gramCholesky g)ᵀ := by
  simp only [iwasawaUnitriangular, Units.val_mul, coe_inv_iwasawaOrthogonal,
    coe_inv_iwasawaDiagonal, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

private theorem iwasawaUnitriangular_mem (g : GL (Fin n) ℝ) :
    iwasawaUnitriangular g ∈ upperUnitriangularGroup (Fin n) ℝ := by
  rw [UpperUnitriangularGroup.mem_iff, coe_iwasawaUnitriangular, isUpperUnitriangular_def]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [diagonal_mul, transpose_apply, gramCholesky_isLowerTriangular g hji, mul_zero]
  · rw [diagonal_mul, transpose_apply, inv_mul_cancel₀ (gramCholesky_diag_pos g i).ne']

/-- The Gram matrix of `k a u` has Cholesky factor `(a u)ᵀ`: this is what makes the Iwasawa
factors of `g` unique. -/
private theorem gramCholesky_mul_mul {k a u : GL (Fin n) ℝ}
    (hk : k ∈ unitarySubgroup (GL (Fin n) ℝ)) (ha : a ∈ posDiagonalSubgroup (Fin n) ℝ)
    (hu : u ∈ upperUnitriangularGroup (Fin n) ℝ) :
    gramCholesky (k * a * u) = ((a * u : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
  obtain ⟨d, hd, had⟩ := mem_posDiagonalSubgroup_iff.1 ha
  have hu' := UpperUnitriangularGroup.mem_iff.1 hu
  have hentry : ∀ i j, ((a * u : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ i j =
      d j * (u : Matrix (Fin n) (Fin n) ℝ) j i := fun i j => by
    simp [had, diagonal_mul]
  let L : PosDiagLowerTriangular n :=
    ⟨((a * u : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ,
      fun i j hij => by
        rw [hentry, hu'.isUpperTriangular (OrderDual.toDual_lt_toDual.1 hij), mul_zero],
      fun i => by rw [hentry, hu'.apply_diag, mul_one]; exact hd i⟩
  have hL : L.1 * L.1ᵀ = ((gramPosDefMatrix (k * a * u)).1 : Matrix (Fin n) (Fin n) ℝ) := by
    simp [L, coe_gramPosDefMatrix, transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (k : Matrix (Fin n) (Fin n) ℝ)ᵀ,
      transpose_mul_self_of_mem_unitarySubgroup hk]
  exact congrArg Subtype.val (eq_cholesky_of_mul_transpose_self_eq _ L hL).symm

private theorem iwasawaOrthogonal_mul_mul {k a u : GL (Fin n) ℝ}
    (hk : k ∈ unitarySubgroup (GL (Fin n) ℝ)) (ha : a ∈ posDiagonalSubgroup (Fin n) ℝ)
    (hu : u ∈ upperUnitriangularGroup (Fin n) ℝ) :
    iwasawaOrthogonal (k * a * u) = k := by
  have hinv : a * u * (k * a * u)⁻¹ = k⁻¹ := by group
  refine Units.ext ?_
  -- `(g⁻¹)ᵀ (a u)ᵀ = (a u g⁻¹)ᵀ = (k⁻¹)ᵀ`, the transpose of the transpose of `k`
  rw [coe_iwasawaOrthogonal, gramCholesky_mul_mul hk ha hu, ← transpose_mul, ← Units.val_mul, hinv]
  simp [coe_inv_eq_transpose_of_mem_unitarySubgroup hk]

private theorem iwasawaDiagonal_mul_mul {k a u : GL (Fin n) ℝ}
    (hk : k ∈ unitarySubgroup (GL (Fin n) ℝ)) (ha : a ∈ posDiagonalSubgroup (Fin n) ℝ)
    (hu : u ∈ upperUnitriangularGroup (Fin n) ℝ) :
    iwasawaDiagonal (k * a * u) = a := by
  obtain ⟨d, -, had⟩ := mem_posDiagonalSubgroup_iff.1 ha
  refine Units.ext ?_
  rw [coe_iwasawaDiagonal, gramCholesky_mul_mul hk ha hu, had]
  refine congrArg diagonal (funext fun i => ?_)
  simp [had, diagonal_mul, (UpperUnitriangularGroup.mem_iff.1 hu).apply_diag]

variable (n) in
/-- **The Iwasawa decomposition of `GL n ℝ`.** Multiplication `(k, a, u) ↦ k a u` is a
homeomorphism from the product of the orthogonal group, the positive diagonal subgroup and the
upper unitriangular group onto `GL n ℝ`. -/
def iwasawaHomeomorph :
    unitarySubgroup (GL (Fin n) ℝ) × posDiagonalSubgroup (Fin n) ℝ ×
        upperUnitriangularGroup (Fin n) ℝ ≃ₜ GL (Fin n) ℝ where
  toFun x := x.1 * x.2.1 * x.2.2
  invFun g := (⟨iwasawaOrthogonal g, iwasawaOrthogonal_mem g⟩,
    ⟨iwasawaDiagonal g, iwasawaDiagonal_mem g⟩,
    ⟨iwasawaUnitriangular g, iwasawaUnitriangular_mem g⟩)
  left_inv := by
    rintro ⟨⟨k, hk⟩, ⟨a, ha⟩, ⟨u, hu⟩⟩
    have hK := iwasawaOrthogonal_mul_mul hk ha hu
    have hA := iwasawaDiagonal_mul_mul hk ha hu
    have hU : iwasawaUnitriangular (k * a * u) = u := by
      rw [iwasawaUnitriangular, hK, hA]
      group
    -- `invFun` produces the three factors of its argument, here `k * a * u`
    exact Prod.ext (Subtype.ext hK) (Prod.ext (Subtype.ext hA) (Subtype.ext hU))
  right_inv g := by
    have h : iwasawaOrthogonal g * iwasawaDiagonal g * iwasawaUnitriangular g = g := by
      rw [iwasawaUnitriangular]
      group
    -- `toFun` multiplies the three factors that `invFun` produces, as elements of `GL n ℝ`
    exact h
  continuous_toFun := by fun_prop
  continuous_invFun := by
    have hL := continuous_gramCholesky (n := n)
    have hK : Continuous (iwasawaOrthogonal (n := n)) :=
      Units.continuous_iff.2
        ⟨Units.continuous_coe_inv.matrix_transpose.matrix_mul hL,
          hL.matrix_transpose.matrix_mul Units.continuous_coe_inv⟩
    have hA : Continuous (iwasawaDiagonal (n := n)) :=
      Units.continuous_iff.2
        ⟨((continuous_pi fun i => hL.matrix_elem i i).matrix_diagonal).congr
            fun g => (coe_iwasawaDiagonal g).symm,
          ((continuous_pi fun i => (hL.matrix_elem i i).inv₀
            fun g => (gramCholesky_diag_pos g i).ne').matrix_diagonal).congr
            fun g => (coe_inv_iwasawaDiagonal g).symm⟩
    have hU : Continuous (iwasawaUnitriangular (n := n)) :=
      (hA.inv.mul hK.inv).mul continuous_id
    exact (hK.subtype_mk _).prodMk ((hA.subtype_mk _).prodMk (hU.subtype_mk _))

/-- The Iwasawa decomposition multiplies its three factors. -/
@[simp]
theorem iwasawaHomeomorph_apply
    (x : unitarySubgroup (GL (Fin n) ℝ) × posDiagonalSubgroup (Fin n) ℝ ×
      upperUnitriangularGroup (Fin n) ℝ) :
    iwasawaHomeomorph n x = x.1 * x.2.1 * x.2.2 :=
  (rfl)

/-- **Every invertible real matrix is uniquely `k a u`**, with `k` orthogonal, `a` diagonal with
positive diagonal entries and `u` upper unitriangular. -/
theorem existsUnique_iwasawa (g : GL (Fin n) ℝ) :
    ∃! x : unitarySubgroup (GL (Fin n) ℝ) × posDiagonalSubgroup (Fin n) ℝ ×
        upperUnitriangularGroup (Fin n) ℝ,
      (x.1 : GL (Fin n) ℝ) * x.2.1 * x.2.2 = g :=
  (iwasawaHomeomorph n).bijective.existsUnique g

end TauCeti
