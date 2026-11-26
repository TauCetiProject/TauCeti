/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Unitary
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Unitary

/-!
# Reindexing the symplectic, orthogonal and complex-linear groups

Mathlib's standard alternating matrix `Matrix.J l R` and symplectic group
`Matrix.symplecticGroup l R`, and Tau Ceti's realification `Matrix.realify`, all use the index type
`l ⊕ l`. Matrix models of Lie groups, such as subgroups of `GL(2n, ℝ)`, use `Fin (2 * n)` instead.
This file transports these objects along an arbitrary equivalence `e : l ⊕ l ≃ p`.

The transported alternating form is `reindex e e (J l R)`. It still squares to `-1` and is
antisymmetric. A matrix `M` indexed by `p` preserves it exactly when `reindex e.symm e.symm M` is
symplectic. It commutes with `M` exactly when `M` is the reindexed realification of a complex
matrix. Orthogonality is invariant under reindexing already in Mathlib
(`Matrix.submatrix_equiv_mem_unitary`).

In the general linear group, the images under `Equiv.reindexGL e` are as follows.
* The image of `TauCeti.GLSymplectic l R` is the stabilizer of the transported form.
* The image of the realified general linear group `(Matrix.GeneralLinearGroup.realify l ℂ).range`
  is the centralizer of the transported form.
* The orthogonal (unitary) subgroup maps onto the orthogonal subgroup
  (`Equiv.map_reindexGL_unitarySubgroup`).
The first two images are closed under transposition. All three pairwise intersections of the
images are the reindexed realification of `U(n)`.

For the index `Fin n`, the standard equivalence is `TauCeti.finSumFinEquivTwoMul n`. It is
`finSumFinEquiv` followed by `finCongr (two_mul n).symm`. Its first step is the `Fin (n + n)`
presentation `TauCeti.JFin`, `TauCeti.GLSymplecticFin`, and the second step carries that
presentation to `Fin (2 * n)` (`TauCeti.reindex_finCongr_JFin`,
`TauCeti.map_reindexGL_finCongr_GLSymplecticFin`).

## Main results

* `Matrix.reindex_J_mul_reindex_J`, `Matrix.transpose_reindex_J`: the transported alternating form
  squares to `-1` and is antisymmetric.
* `Matrix.mul_reindex_J_mul_transpose_eq_iff`, `Matrix.transpose_mul_reindex_J_mul_eq_iff`: the
  symplectic condition against the transported form.
* `Matrix.commute_reindex_J_iff_exists_realify_eq`: the real matrices commuting with the
  transported form are the reindexed realifications.
* `TauCeti.GLSymplectic.mem_map_reindexGL_iff`,
  `Matrix.GeneralLinearGroup.mem_map_reindexGL_range_realify_iff`: membership in the reindexed
  symplectic and complex-linear subgroups.
* `TauCeti.GLSymplectic.map_reindexGL_inf_unitarySubgroup`,
  `TauCeti.GLSymplectic.map_reindexGL_inf_map_reindexGL_range_realify` and
  `Matrix.GeneralLinearGroup.unitarySubgroup_inf_map_reindexGL_range_realify`: the three pairwise
  intersections after reindexing.
* `TauCeti.finSumFinEquivTwoMul`: the equivalence `Fin n ⊕ Fin n ≃ Fin (2 * n)`.
* `TauCeti.GLSymplecticFin_eq_map_reindexGL`, `TauCeti.map_reindexGL_finCongr_GLSymplecticFin`:
  the `Fin (n + n)` symplectic subgroup is the reindexed one, and casting it gives the
  `Fin (2 * n)` one.
-/

public section

open Matrix

namespace Matrix

variable {l p : Type*} [Fintype l] [DecidableEq l] [Fintype p] [DecidableEq p]
  (e : l ⊕ l ≃ p) {R : Type*} [CommRing R]

omit [Fintype l] in
/-- The transported alternating form squares to `-1`. -/
theorem reindex_J_mul_reindex_J : reindex e e (J l R) * reindex e e (J l R) = -1 := by
  -- Only `p` is assumed finite; `l` is finite as a summand of `l ⊕ l ≃ p`.
  have : Fintype l := @Fintype.sumLeft l l (Fintype.ofEquiv p e.symm)
  rw [← coe_reindexAlgEquiv R R e, ← map_mul, J_squared, map_neg, map_one]

omit [Fintype l] [Fintype p] [DecidableEq p] in
/-- The transported alternating form is antisymmetric. -/
theorem transpose_reindex_J : (reindex e e (J l R))ᵀ = -reindex e e (J l R) := by
  rw [transpose_reindex, J_transpose, reindex_apply, reindex_apply, submatrix_neg, Pi.neg_apply,
    Pi.neg_apply]

variable {e}

omit [DecidableEq p] in
/-- **The transported symplectic condition**: a matrix preserves the transported alternating
form exactly when reindexing it back gives a symplectic matrix. -/
theorem mul_reindex_J_mul_transpose_eq_iff {M : Matrix p p R} :
    M * reindex e e (J l R) * Mᵀ = reindex e e (J l R) ↔
      reindex e.symm e.symm M ∈ symplecticGroup l R := by
  classical
  obtain ⟨N, rfl⟩ := (reindex e e).surjective M
  rw [← reindex_symm, Equiv.symm_apply_apply, transpose_reindex, SymplecticGroup.mem_iff,
    ← coe_reindexAlgEquiv R R e, ← map_mul, ← map_mul, (reindexAlgEquiv R R e).injective.eq_iff]

omit [DecidableEq p] in
/-- The transported symplectic condition in the transposed form `Mᵀ J M = J`. -/
theorem transpose_mul_reindex_J_mul_eq_iff {M : Matrix p p R} :
    Mᵀ * reindex e e (J l R) * M = reindex e e (J l R) ↔
      reindex e.symm e.symm M ∈ symplecticGroup l R := by
  classical
  obtain ⟨N, rfl⟩ := (reindex e e).surjective M
  rw [← reindex_symm, Equiv.symm_apply_apply, transpose_reindex, SymplecticGroup.mem_iff',
    ← coe_reindexAlgEquiv R R e, ← map_mul, ← map_mul, (reindexAlgEquiv R R e).injective.eq_iff]

omit [DecidableEq p] in
/-- A matrix commutes with the transported alternating form exactly when reindexing it back gives
a matrix commuting with `J`. -/
theorem commute_reindex_J_iff {M : Matrix p p R} :
    Commute (reindex e e (J l R)) M ↔ Commute (J l R) (reindex e.symm e.symm M) := by
  classical
  obtain ⟨N, rfl⟩ := (reindex e e).surjective M
  rw [← reindex_symm, Equiv.symm_apply_apply, ← coe_reindexAlgEquiv R R e,
    commute_map_iff (reindexAlgEquiv R R e).injective]

omit [Fintype l] [DecidableEq p] in
/-- **The reindexed complex-linear real matrices**: a real matrix commutes with the transported
alternating form exactly when it is the reindexed realification of a complex matrix. -/
theorem commute_reindex_J_iff_exists_realify_eq {M : Matrix p p ℝ} :
    Commute (reindex e e (J l ℝ)) M ↔ ∃ A : Matrix l l ℂ, reindex e e A.realify = M := by
  -- Only `p` is assumed finite; `l` is finite as a summand of `l ⊕ l ≃ p`.
  have : Fintype l := @Fintype.sumLeft l l (Fintype.ofEquiv p e.symm)
  rw [commute_reindex_J_iff, commute_J_iff_exists_realify_eq]
  exact exists_congr fun A ↦ by rw [← reindex_symm, Equiv.eq_symm_apply]

end Matrix

namespace TauCeti.GLSymplectic

variable {l p : Type*} [Fintype l] [DecidableEq l] [Fintype p] [DecidableEq p]
  {e : l ⊕ l ≃ p} {R : Type*} [CommRing R]

/-- **The reindexed symplectic subgroup** is the stabilizer of the transported alternating
form. -/
theorem mem_map_reindexGL_iff {M : GL p R} :
    M ∈ (GLSymplectic l R).map (e.reindexGL R) ↔
      (M : Matrix p p R) * reindex e e (J l R) * (M : Matrix p p R)ᵀ = reindex e e (J l R) := by
  rw [← MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_map_equiv, mem_iff_mem_symplecticGroup,
    mul_reindex_J_mul_transpose_eq_iff, Equiv.reindexGL_symm, Equiv.coe_reindexGL, reindex_apply,
    Equiv.symm_symm]

/-- Membership in the reindexed symplectic subgroup, in the transposed form `Mᵀ J M = J`. -/
theorem mem_map_reindexGL_iff' {M : GL p R} :
    M ∈ (GLSymplectic l R).map (e.reindexGL R) ↔
      (M : Matrix p p R)ᵀ * reindex e e (J l R) * (M : Matrix p p R) = reindex e e (J l R) := by
  rw [← MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_map_equiv, mem_iff_mem_symplecticGroup,
    transpose_mul_reindex_J_mul_eq_iff, Equiv.reindexGL_symm, Equiv.coe_reindexGL, reindex_apply,
    Equiv.symm_symm]

/-- **The reindexed symplectic subgroup is closed under transposition.** -/
theorem star_mem_map_reindexGL [StarRing R] [TrivialStar R] {M : GL p R}
    (hM : M ∈ (GLSymplectic l R).map (e.reindexGL R)) :
    star M ∈ (GLSymplectic l R).map (e.reindexGL R) := by
  rw [mem_map_reindexGL_iff] at hM
  rw [mem_map_reindexGL_iff', Units.coe_star, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial, transpose_transpose, hM]

end TauCeti.GLSymplectic

namespace Matrix.GeneralLinearGroup

variable {l p : Type*} [Fintype l] [DecidableEq l] [Fintype p] [DecidableEq p] {e : l ⊕ l ≃ p}

/-- **The reindexed realified general linear group is the centralizer of the transported
alternating form**. -/
theorem mem_map_reindexGL_range_realify_iff {M : GL p ℝ} :
    M ∈ (realify l ℂ).range.map (e.reindexGL ℝ) ↔
      Commute (Matrix.reindex e e (J l ℝ)) (M : Matrix p p ℝ) := by
  rw [← MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_map_equiv, mem_range_realify_iff,
    commute_reindex_J_iff, Equiv.reindexGL_symm, Equiv.coe_reindexGL, Matrix.reindex_apply,
    Equiv.symm_symm]

/-- **The reindexed realified general linear group is closed under transposition.** -/
theorem star_mem_map_reindexGL_range_realify {M : GL p ℝ}
    (hM : M ∈ (realify l ℂ).range.map (e.reindexGL ℝ)) :
    star M ∈ (realify l ℂ).range.map (e.reindexGL ℝ) := by
  obtain ⟨N, hN, rfl⟩ := hM
  exact ⟨star N, star_mem_range_realify hN, (Equiv.star_reindexGL e ℝ N).symm⟩

/-- **`O(2n) ∩ GL(n, ℂ) = U(n)` after reindexing**: the orthogonal elements of the reindexed
realified general linear group are the reindexed realified unitary matrices. -/
theorem unitarySubgroup_inf_map_reindexGL_range_realify :
    unitarySubgroup (GL p ℝ) ⊓ (realify l ℂ).range.map (e.reindexGL ℝ) =
      ((unitarySubgroup (GL l ℂ)).map (realify l ℂ)).map (e.reindexGL ℝ) := by
  rw [← Equiv.map_reindexGL_unitarySubgroup e ℝ,
    ← Subgroup.map_inf _ _ _ (e.reindexGL ℝ).injective, unitarySubgroup_inf_range_realify]

end Matrix.GeneralLinearGroup

namespace TauCeti.GLSymplectic

open Matrix.GeneralLinearGroup

variable {l p : Type*} [Fintype l] [DecidableEq l] [Fintype p] [DecidableEq p] {e : l ⊕ l ≃ p}

/-- **`Sp(2n, ℝ) ∩ O(2n) = U(n)` after reindexing**: the orthogonal elements of the reindexed
symplectic subgroup are the reindexed realified unitary matrices. -/
theorem map_reindexGL_inf_unitarySubgroup :
    (GLSymplectic l ℝ).map (e.reindexGL ℝ) ⊓ unitarySubgroup (GL p ℝ) =
      ((unitarySubgroup (GL l ℂ)).map (realify l ℂ)).map (e.reindexGL ℝ) := by
  rw [← Equiv.map_reindexGL_unitarySubgroup e ℝ,
    ← Subgroup.map_inf _ _ _ (e.reindexGL ℝ).injective, inf_unitarySubgroup]

/-- **`Sp(2n, ℝ) ∩ GL(n, ℂ) = U(n)` after reindexing**: the symplectic elements of the reindexed
realified general linear group are the reindexed realified unitary matrices. -/
theorem map_reindexGL_inf_map_reindexGL_range_realify :
    (GLSymplectic l ℝ).map (e.reindexGL ℝ : GL (l ⊕ l) ℝ →* GL p ℝ) ⊓
        (realify l ℂ).range.map (e.reindexGL ℝ) =
      ((unitarySubgroup (GL l ℂ)).map (realify l ℂ)).map (e.reindexGL ℝ) := by
  rw [← Subgroup.map_inf _ _ _ (e.reindexGL ℝ).injective, inf_range_realify]

end TauCeti.GLSymplectic

namespace TauCeti

variable (n : ℕ)

/-- The equivalence `Fin n ⊕ Fin n ≃ Fin (2 * n)`: `finSumFinEquiv` followed by the cast
`Fin (n + n) ≃ Fin (2 * n)`. The left summand goes to the first `n` indices and the right summand
to the last `n`, so `Matrix.J` becomes the block matrix `!![0, -1; 1, 0]` in `Fin (2 * n)`
coordinates. -/
def finSumFinEquivTwoMul : Fin n ⊕ Fin n ≃ Fin (2 * n) :=
  finSumFinEquiv.trans (finCongr (two_mul n).symm)

variable {n}

/-- The left summand of `Fin n ⊕ Fin n` goes to the first `n` indices of `Fin (2 * n)`. -/
@[simp]
theorem finSumFinEquivTwoMul_inl (i : Fin n) :
    finSumFinEquivTwoMul n (.inl i) = ⟨i, by omega⟩ :=
  (rfl)

/-- The right summand of `Fin n ⊕ Fin n` goes to the last `n` indices of `Fin (2 * n)`. -/
@[simp]
theorem finSumFinEquivTwoMul_inr (i : Fin n) :
    finSumFinEquivTwoMul n (.inr i) = ⟨n + i, by omega⟩ :=
  (rfl)

variable (n) (R : Type*) [CommRing R]

/-- For `n = 1` the reindexed alternating form is the rotation by a quarter turn,
`!![0, -1; 1, 0]`, matching `TauCeti.JFin_one_eq`. -/
theorem reindex_finSumFinEquivTwoMul_J_one :
    reindex (finSumFinEquivTwoMul 1) (finSumFinEquivTwoMul 1) (J (Fin 1) R) = !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J, finSumFinEquivTwoMul, finSumFinEquiv, Fin.addCases, fromBlocks]

/-- The `Fin (n + n)` symplectic subgroup `TauCeti.GLSymplecticFin` is the symplectic subgroup
reindexed along `finSumFinEquiv`. -/
theorem GLSymplecticFin_eq_map_reindexGL :
    GLSymplecticFin n R =
      (GLSymplectic (Fin n) R).map
        ((finSumFinEquiv (m := n) (n := n)).reindexGL R :
          GL (Fin n ⊕ Fin n) R →* GL (Fin (n + n)) R) := by
  ext M
  rw [GLSymplecticFin.mem_iff, GLSymplectic.mem_map_reindexGL_iff, reindex_apply,
    ← JFin_eq_submatrix]

/-- The `Fin (n + n)` alternating form `TauCeti.JFin`, cast to `Fin (2 * n)`, is `Matrix.J`
reindexed along `TauCeti.finSumFinEquivTwoMul`. -/
theorem reindex_finCongr_JFin :
    reindex (finCongr (two_mul n).symm) (finCongr (two_mul n).symm) (JFin n R) =
      reindex (finSumFinEquivTwoMul n) (finSumFinEquivTwoMul n) (J (Fin n) R) := by
  rw [JFin_eq_submatrix, ← reindex_apply, ← Equiv.trans_apply, reindex_trans,
    finSumFinEquivTwoMul]

/-- The `Fin (n + n)` symplectic subgroup `TauCeti.GLSymplecticFin`, cast to `Fin (2 * n)`, is
the symplectic subgroup reindexed along `TauCeti.finSumFinEquivTwoMul`. -/
theorem map_reindexGL_finCongr_GLSymplecticFin :
    (GLSymplecticFin n R).map ((finCongr (two_mul n).symm).reindexGL R) =
      (GLSymplectic (Fin n) R).map
        ((finSumFinEquivTwoMul n).reindexGL R : GL (Fin n ⊕ Fin n) R →* GL (Fin (2 * n)) R) := by
  rw [GLSymplecticFin_eq_map_reindexGL, Subgroup.map_map]
  congr 1
  ext M i j
  simp [finSumFinEquivTwoMul]

end TauCeti
