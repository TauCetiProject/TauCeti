/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.RCLike.Units
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Positive
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic

/-!
# The positive upper-triangular group

The invertible upper-triangular matrices with positive real diagonal entries form a subgroup
of the real or complex general linear group. The diagonal homomorphism of the upper-triangular
group takes values in families of positive real scalar units. Zero imaginary part and
nonnegative real part give an equivalent characterization inside the general linear group.

## Main definitions and results

* `TauCeti.posUpperTriangularGroup`: the positive real diagonal upper-triangular subgroup.
* `TauCeti.PosUpperTriangularGroup.mem_iff`: membership by triangularity and positive diagonal.
* `TauCeti.PosUpperTriangularGroup.mem_iff_nonneg`: membership with nonnegative real diagonal.
* `TauCeti.posUpperTriangularGroup_le_upperTriangularGroup`: inclusion in the upper-triangular
  group.
* `TauCeti.upperUnitriangularGroup_le_posUpperTriangularGroup`: inclusion of the unipotent
  subgroup.
* `TauCeti.posDiagonalSubgroup_map_le_posUpperTriangularGroup`: inclusion of positive real
  diagonal matrices after scalar extension.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition, Birkhäuser (1996), §VI.4,
  Example, pp.311–312, for the positive upper-triangular factor in matrix Iwasawa decomposition.
* Mathlib and Tau Ceti, the upper-triangular diagonal homomorphism and positive real units.
-/

public noncomputable section

open Matrix
open scoped ComplexOrder

namespace TauCeti

variable (ι : Type*) [Fintype ι] [LinearOrder ι] (𝕜 : Type*) [RCLike 𝕜]

/-- The subgroup of upper-triangular invertible matrices with positive real diagonal entries. -/
def posUpperTriangularGroup : Subgroup (GL ι 𝕜) :=
  ((Subgroup.pi Set.univ fun _ : ι ↦ Units.posRealSubgroup 𝕜).comap
    (UpperTriangularGroup.diag (m := ι) (R := 𝕜))).map
      (upperTriangularGroup ι 𝕜).subtype

variable {ι 𝕜}

namespace PosUpperTriangularGroup

/-- An invertible matrix belongs to the positive upper-triangular group exactly when it is
upper triangular with positive real diagonal entries. -/
@[simp]
theorem mem_iff {g : GL ι 𝕜} :
    g ∈ posUpperTriangularGroup ι 𝕜 ↔ (g : Matrix ι ι 𝕜).IsUpperTriangular ∧
      ∀ i, 0 < g i i := by
  rw [posUpperTriangularGroup, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨UpperTriangularGroup.isUpperTriangular x, fun i ↦ ?_⟩
    have hi := ((Subgroup.mem_pi Set.univ).mp (Subgroup.mem_comap.mp hx)) i (Set.mem_univ i)
    simpa only [UpperTriangularGroup.diag_apply_val, Subgroup.subtype_apply] using
      Units.mem_posRealSubgroup.mp hi
  · rintro ⟨htri, hpos⟩
    refine ⟨⟨g, UpperTriangularGroup.mem_iff.mpr htri⟩, ?_, rfl⟩
    apply Subgroup.mem_comap.mpr
    apply (Subgroup.mem_pi Set.univ).mpr
    intro i _
    apply Units.mem_posRealSubgroup.mpr
    simpa only [UpperTriangularGroup.diag_apply_val] using hpos i

/-- An invertible matrix belongs to the positive upper-triangular group exactly when it is
upper triangular with nonnegative real diagonal entries. -/
theorem mem_iff_nonneg {g : GL ι 𝕜} :
    g ∈ posUpperTriangularGroup ι 𝕜 ↔ (g : Matrix ι ι 𝕜).IsUpperTriangular ∧
      ∀ i, 0 ≤ g i i := by
  rw [mem_iff]
  constructor
  · exact fun h ↦ ⟨h.1, fun i ↦ (h.2 i).le⟩
  · rintro ⟨htri, hpos⟩
    let x : upperTriangularGroup ι 𝕜 := ⟨g, UpperTriangularGroup.mem_iff.mpr htri⟩
    refine ⟨htri, fun i ↦ (hpos i).lt_of_ne ?_⟩
    simpa only [UpperTriangularGroup.diag_apply_val] using
      (Units.ne_zero (UpperTriangularGroup.diag x i)).symm

end PosUpperTriangularGroup

/-- Every positive upper-triangular matrix is upper triangular. -/
theorem posUpperTriangularGroup_le_upperTriangularGroup :
    posUpperTriangularGroup ι 𝕜 ≤ upperTriangularGroup ι 𝕜 :=
  fun _ hg ↦ UpperTriangularGroup.mem_iff.mpr (PosUpperTriangularGroup.mem_iff.mp hg).1

/-- Every upper-unitriangular matrix has positive real diagonal. -/
theorem upperUnitriangularGroup_le_posUpperTriangularGroup :
    upperUnitriangularGroup ι 𝕜 ≤ posUpperTriangularGroup ι 𝕜 := by
  intro g hg
  have h := UpperUnitriangularGroup.mem_iff.mp hg
  exact PosUpperTriangularGroup.mem_iff.mpr
    ⟨h.isUpperTriangular, fun i ↦ by rw [h.apply_diag]; exact one_pos⟩

/-- Positive real diagonal matrices remain positive upper triangular after scalar extension. -/
theorem posDiagonalSubgroup_map_le_posUpperTriangularGroup :
    (posDiagonalSubgroup ι ℝ).map (GeneralLinearGroup.map (algebraMap ℝ 𝕜)) ≤
      posUpperTriangularGroup ι 𝕜 := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
  obtain ⟨d, hd, had⟩ := mem_posDiagonalSubgroup_iff.mp ha
  apply PosUpperTriangularGroup.mem_iff.mpr
  rw [GeneralLinearGroup.val_map_apply, had, diagonal_map (map_zero _)]
  exact ⟨blockTriangular_diagonal _, fun i ↦ by
    simpa only [diagonal_apply_eq, RCLike.ofReal_pos] using hd i⟩

end TauCeti
