/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic
public import TauCeti.LinearAlgebra.Matrix.Realify

/-!
# The unitary group as the intersection of the symplectic, orthogonal and complex groups

Identify `ℂⁿ` with `ℝⁿ ⊕ ℝⁿ` by `x + i y ↦ (x, y)`. Multiplication by `i` becomes the standard
alternating matrix `J = !![0, -1; 1, 0]` (`Matrix.realify_I_smul_one`), and a complex matrix `A`
becomes its realification `Matrix.realify A`. The real matrices commuting with `J` are exactly the
realifications (`Matrix.commute_J_iff_exists_realify_eq`), so inside the real matrices of size
`2n` three groups are in play: the symplectic group `Sp(2n, ℝ)` of `Matrix.symplecticGroup`, the
orthogonal group `O(2n)` of `Matrix.orthogonalGroup`, and the complex-linear group, the commutant of
`J`. Any two of the conditions defining them imply the third, and the matrices satisfying all
three are the realified unitary matrices. So each of the three pairwise intersections is the
realification of `U(n)`.

This is proved twice: for the matrix submonoids, and for the corresponding subgroups of
`GL (n ⊕ n) ℝ`, namely `TauCeti.GLSymplectic n ℝ`, the unitary subgroup for the transpose, and the
range of `Matrix.GeneralLinearGroup.realify n ℂ`. In the general linear group the complex-linear
group is this range, which is the centralizer of `J`
(`Matrix.GeneralLinearGroup.mem_range_realify_iff`).

## Main results

* `Matrix.realify_I_smul_one`: multiplication by `i` realifies to `J`.
* `Matrix.commute_J_iff_exists_realify_eq`: a real matrix commutes with `J` exactly when it is the
  realification of a complex matrix.
* `Matrix.symplecticGroup_inf_orthogonalGroup`, `Matrix.symplecticGroup_inf_centralizer_J` and
  `Matrix.orthogonalGroup_inf_centralizer_J`: each pairwise intersection of the matrix submonoids
  is the realification of the unitary group.
* `Matrix.GeneralLinearGroup.mem_range_realify_iff`: the realified general linear group is the
  centralizer of `J` in `GL (n ⊕ n) ℝ`.
* `TauCeti.GLSymplectic.inf_unitarySubgroup`, `TauCeti.GLSymplectic.inf_range_realify` and
  `Matrix.GeneralLinearGroup.unitarySubgroup_inf_range_realify`: the same three identities for
  subgroups of `GL (n ⊕ n) ℝ`.
* `Matrix.GeneralLinearGroup.range_realify_comp_toUnits`: realifying the unitary group itself
  gives the orthogonal elements of the symplectic subgroup.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Section 2.2 (the identities `Sp(2n) ∩ O(2n) = Sp(2n) ∩ GL(n, ℂ) =
  O(2n) ∩ GL(n, ℂ) = U(n)`).
-/

public section

open Matrix

namespace Matrix

variable {n : Type*} [DecidableEq n]

/-- Multiplication by `i` realifies to the standard alternating matrix `J`. -/
theorem realify_I_smul_one : (Complex.I • (1 : Matrix n n ℂ)).realify = J n ℝ := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> by_cases h : i = j <;> simp [J, h]

variable [Fintype n]

/-- **The complex-linear real matrices**: a real matrix commutes with `J` exactly when it is the
realification of a complex matrix. -/
theorem commute_J_iff_exists_realify_eq {M : Matrix (n ⊕ n) (n ⊕ n) ℝ} :
    Commute (J n ℝ) M ↔ ∃ A : Matrix n n ℂ, A.realify = M := by
  refine ⟨fun h ↦ ?_, fun ⟨A, hA⟩ ↦ hA ▸ commute_J_realify A⟩
  -- In blocks, `J * M = M * J` says that `M = !![P, -R; R, P]`, the realification of `P + i R`.
  rw [← fromBlocks_toBlocks M] at h ⊢
  simp only [Commute, SemiconjBy, J, fromBlocks_multiply, fromBlocks_inj] at h
  refine ⟨Matrix.of fun i j ↦ ⟨M.toBlocks₁₁ i j, M.toBlocks₂₁ i j⟩, ?_⟩
  ext p q
  rcases p with i | i <;> rcases q with j | j
  · simp
  · simpa using congr_fun₂ h.1 i j
  · simp
  · simpa using (congr_fun₂ h.2.1 i j).symm

/-- A real matrix is a realified unitary matrix exactly when it commutes with `J` and is
orthogonal. -/
theorem mem_map_realifyAlgHom_unitaryGroup_iff {M : Matrix (n ⊕ n) (n ⊕ n) ℝ} :
    M ∈ (unitaryGroup n ℂ).map (realifyAlgHom n ℂ) ↔
      Commute (J n ℝ) M ∧ M ∈ orthogonalGroup (n ⊕ n) ℝ := by
  refine ⟨?_, fun ⟨h, hM⟩ ↦ ?_⟩
  · rintro ⟨A, hA, rfl⟩
    rw [realifyAlgHom_apply]
    exact ⟨commute_J_realify A, realify_mem_orthogonalGroup_iff.2 hA⟩
  · obtain ⟨A, rfl⟩ := commute_J_iff_exists_realify_eq.1 h
    exact ⟨A, realify_mem_orthogonalGroup_iff.1 hM, realifyAlgHom_apply A⟩

/-- **`Sp(2n, ℝ) ∩ O(2n) = U(n)`**: the orthogonal symplectic matrices are the realified unitary
matrices. -/
theorem symplecticGroup_inf_orthogonalGroup :
    symplecticGroup n ℝ ⊓ orthogonalGroup (n ⊕ n) ℝ =
      (unitaryGroup n ℂ).map (realifyAlgHom n ℂ) := by
  ext M
  rw [Submonoid.mem_inf, mem_map_realifyAlgHom_unitaryGroup_iff]
  exact ⟨fun ⟨hS, hO⟩ ↦ ⟨SymplecticGroup.commute_J_of_mem_orthogonalGroup hS hO, hO⟩,
    fun ⟨h, hO⟩ ↦ ⟨(SymplecticGroup.mem_iff_mem_orthogonalGroup_of_commute h).2 hO, hO⟩⟩

/-- **`Sp(2n, ℝ) ∩ GL(n, ℂ) = U(n)`**: the symplectic matrices commuting with `J` are the
realified unitary matrices. -/
theorem symplecticGroup_inf_centralizer_J :
    symplecticGroup n ℝ ⊓ Submonoid.centralizer {J n ℝ} =
      (unitaryGroup n ℂ).map (realifyAlgHom n ℂ) := by
  ext M
  rw [Submonoid.mem_inf, Submonoid.mem_centralizer_iff, mem_map_realifyAlgHom_unitaryGroup_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  exact ⟨fun ⟨hS, h⟩ ↦ ⟨h, (SymplecticGroup.mem_iff_mem_orthogonalGroup_of_commute h).1 hS⟩,
    fun ⟨h, hO⟩ ↦ ⟨(SymplecticGroup.mem_iff_mem_orthogonalGroup_of_commute h).2 hO, h⟩⟩

/-- **`O(2n) ∩ GL(n, ℂ) = U(n)`**: the orthogonal matrices commuting with `J` are the realified
unitary matrices. -/
theorem orthogonalGroup_inf_centralizer_J :
    orthogonalGroup (n ⊕ n) ℝ ⊓ Submonoid.centralizer {J n ℝ} =
      (unitaryGroup n ℂ).map (realifyAlgHom n ℂ) := by
  ext M
  rw [Submonoid.mem_inf, Submonoid.mem_centralizer_iff, mem_map_realifyAlgHom_unitaryGroup_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  exact and_comm

namespace GeneralLinearGroup

/-- For a trivial star operation, the unitary elements of `GL n R` are the orthogonal matrices. -/
theorem mem_unitarySubgroup_iff_mem_orthogonalGroup {m R : Type*} [Fintype m] [DecidableEq m]
    [CommRing R] [StarRing R] [TrivialStar R] {M : GL m R} :
    M ∈ unitarySubgroup (GL m R) ↔ (M : Matrix m m R) ∈ orthogonalGroup m R := by
  rw [mem_orthogonalGroup_iff, ← conjTranspose_eq_transpose_of_trivial]
  simp [Units.unitary_eq, mem_unitaryGroup_iff, star_eq_conjTranspose]

/-- **The realified general linear group is the centralizer of `J`**: an invertible real matrix is
the realification of an invertible complex matrix exactly when it commutes with `J`. -/
theorem mem_range_realify_iff {M : GL (n ⊕ n) ℝ} :
    M ∈ (realify n ℂ).range ↔ Commute (J n ℝ) (M : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨A, rfl⟩
    rw [coe_realify]
    exact commute_J_realify _
  -- The inverse of `M` also commutes with `J`, so both are realifications; their preimages are
  -- inverse to each other because realification is injective and multiplicative.
  obtain ⟨A, hA⟩ := commute_J_iff_exists_realify_eq.1 h
  obtain ⟨B, hB⟩ := commute_J_iff_exists_realify_eq.1 (h.units_inv_right (u := M))
  refine ⟨⟨A, B, ?_, ?_⟩, Units.ext ?_⟩
  · simp [← realify_inj, hA, hB]
  · simp [← realify_inj, hA, hB]
  · simpa using hA

/-- An invertible real matrix is a realified unitary matrix exactly when it commutes with `J` and
is orthogonal. -/
theorem mem_map_realify_unitarySubgroup_iff {M : GL (n ⊕ n) ℝ} :
    M ∈ (unitarySubgroup (GL n ℂ)).map (realify n ℂ) ↔
      Commute (J n ℝ) (M : Matrix (n ⊕ n) (n ⊕ n) ℝ) ∧ M ∈ unitarySubgroup (GL (n ⊕ n) ℝ) := by
  rw [mem_unitarySubgroup_iff_mem_orthogonalGroup, ← mem_map_realifyAlgHom_unitaryGroup_iff]
  refine ⟨?_, fun ⟨A, hA, hAM⟩ ↦ ?_⟩
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, by simpa [Units.unitary_eq] using hA, by simp⟩
  · refine ⟨Unitary.toUnits ⟨A, by simpa using hA⟩, by simpa [Units.unitary_eq] using hA,
      Units.ext ?_⟩
    simpa using hAM

/-- **`O(2n) ∩ GL(n, ℂ) = U(n)` in `GL (n ⊕ n) ℝ`**: the orthogonal elements of the realified
general linear group are the realified unitary matrices. -/
theorem unitarySubgroup_inf_range_realify :
    unitarySubgroup (GL (n ⊕ n) ℝ) ⊓ (realify n ℂ).range =
      (unitarySubgroup (GL n ℂ)).map (realify n ℂ) := by
  ext M
  rw [Subgroup.mem_inf, mem_range_realify_iff, mem_map_realify_unitarySubgroup_iff]
  exact and_comm

end GeneralLinearGroup

end Matrix

namespace TauCeti.GLSymplectic

open Matrix Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **`Sp(2n, ℝ) ∩ O(2n) = U(n)` in `GL (n ⊕ n) ℝ`**: the orthogonal elements of the symplectic
subgroup are the realified unitary matrices. -/
theorem inf_unitarySubgroup :
    GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ) =
      (unitarySubgroup (GL n ℂ)).map (realify n ℂ) := by
  ext M
  rw [Subgroup.mem_inf, mem_map_realify_unitarySubgroup_iff, mem_iff_mem_symplecticGroup,
    mem_unitarySubgroup_iff_mem_orthogonalGroup]
  exact ⟨fun ⟨hS, hO⟩ ↦ ⟨SymplecticGroup.commute_J_of_mem_orthogonalGroup hS hO, hO⟩,
    fun ⟨h, hO⟩ ↦ ⟨(SymplecticGroup.mem_iff_mem_orthogonalGroup_of_commute h).2 hO, hO⟩⟩

/-- **`Sp(2n, ℝ) ∩ GL(n, ℂ) = U(n)` in `GL (n ⊕ n) ℝ`**: the symplectic elements of the realified
general linear group are the realified unitary matrices. -/
theorem inf_range_realify :
    GLSymplectic n ℝ ⊓ (realify n ℂ).range = (unitarySubgroup (GL n ℂ)).map (realify n ℂ) := by
  ext M
  rw [Subgroup.mem_inf, mem_range_realify_iff, mem_map_realify_unitarySubgroup_iff,
    mem_iff_mem_symplecticGroup, mem_unitarySubgroup_iff_mem_orthogonalGroup]
  exact ⟨fun ⟨hS, h⟩ ↦ ⟨h, (SymplecticGroup.mem_iff_mem_orthogonalGroup_of_commute h).1 hS⟩,
    fun ⟨h, hO⟩ ↦ ⟨(SymplecticGroup.mem_iff_mem_orthogonalGroup_of_commute h).2 hO, h⟩⟩

end TauCeti.GLSymplectic

namespace Matrix.GeneralLinearGroup

open TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The realifications of the unitary matrices, seen in `GL (n ⊕ n) ℝ`, are the orthogonal
elements of the symplectic subgroup. -/
theorem range_realify_comp_toUnits :
    ((realify n ℂ).comp Unitary.toUnits : unitaryGroup n ℂ →* GL (n ⊕ n) ℝ).range =
      GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ) := by
  rw [MonoidHom.range_comp, GLSymplectic.inf_unitarySubgroup]
  congr 1
  ext u
  refine ⟨?_, fun hu ↦ ⟨⟨u, by simpa [Units.unitary_eq] using hu⟩, Units.ext rfl⟩⟩
  rintro ⟨U, rfl⟩
  simp [Units.unitary_eq]

end Matrix.GeneralLinearGroup
