/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Basic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# Cofiniteness of the projective congruence subgroup `Γ₀(N)`

For nonzero `N`, the image of `Γ₀(N)` in `PSL(2, ℝ)` is a finite-index subgroup of the
effective level-one modular group. Since the latter is cofinite, the projective image is
cofinite as well. This provides the analytic finiteness input for constructing the modular
curve of level `Γ₀(N)`.

The proof uses the finite index of `Γ₀(N)` in `SL(2, ℤ)`, passes through the surjection from
`SL(2, ℤ)` onto the image of `PSL(2, ℤ)` in `PSL(2, ℝ)`, and then applies the finite-index
inheritance theorem for cofiniteness.

## Main result

* `CongruenceSubgroup.Gamma0_psl2zToPSL2RRange_isCofinite`: for nonzero `N`, the effective
  image of `Γ₀(N)` is cofinite in `PSL(2, ℝ)`.

## References

* Diamond and Shurman, *A First Course in Modular Forms*, §2.3.
-/

public section

open CongruenceSubgroup
open scoped MatrixGroups

namespace CongruenceSubgroup

/-- For nonzero `N`, the image of `Γ₀(N)` in `PSL(2, ℝ)` is cofinite. It has finite index
in the effective level-one modular group, which is cofinite by its standard fundamental domain. -/
theorem Gamma0_psl2zToPSL2RRange_isCofinite (N : ℕ) [NeZero N] :
    ((Gamma0 N).map sl2zToPSL2R).IsCofinite := by
  let p : SL(2, ℤ) →* PSL(2, ℤ) := QuotientGroup.mk' (Subgroup.center SL(2, ℤ))
  let G : Subgroup PSL(2, ℤ) := (Gamma0 N).map p
  have hG : G.FiniteIndex := by
    dsimp [G, p]
    exact Subgroup.FiniteIndex.map_of_surjective (Gamma0 N)
      (QuotientGroup.mk'_surjective _)
  let q : PSL(2, ℤ) →* psl2zToPSL2R.range :=
    MonoidHom.rangeRestrict psl2zToPSL2R
  let H : Subgroup psl2zToPSL2R.range := G.map q
  have hH : H.FiniteIndex := by
    dsimp [H, q]
    exact Subgroup.FiniteIndex.map_of_surjective G
      (MonoidHom.rangeRestrict_surjective psl2zToPSL2R)
  have hrel : ((H.map psl2zToPSL2R.range.subtype).subgroupOf psl2zToPSL2R.range).FiniteIndex := by
    have hsub : (H.map psl2zToPSL2R.range.subtype).subgroupOf psl2zToPSL2R.range = H := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [hsub]
    exact hH
  have hcof := (Subgroup.isCofinite_iff_isCofinite_and_finiteIndex
      (Subgroup.map_subtype_le H)).2
    ⟨TauCeti.ModularGroup.isCofinite_psl2zToPSL2RRange, hrel⟩
  have hmap : H.map psl2zToPSL2R.range.subtype = (Gamma0 N).map sl2zToPSL2R := by
    dsimp [H, G]
    rw [Subgroup.map_map]
    rw [Subgroup.map_map]
    have hcomp : (psl2zToPSL2R.range.subtype.comp q).comp p = sl2zToPSL2R := by
      ext g
      simp [q, p, psl2zToPSL2R_mk, sl2zToPSL2R_apply]
    rw [← hcomp]
  rw [← hmap]
  exact hcof

end CongruenceSubgroup
