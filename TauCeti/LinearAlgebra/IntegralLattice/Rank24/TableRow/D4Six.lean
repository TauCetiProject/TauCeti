/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.D4Six.CodeAutomorphism
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Glue.IdentifiedRows

/-!
# The table row `D₄⁶` is the hexacode overlattice of `(D₄)⁶`

The row `D₄⁶` of the rootful rank-24 table, `TauCeti.RootfulNiemeierType.d4Sixth`, glues the
orthogonal sum of its six `D₄` components along the subgroup `d4Sixth.glueSubgroup` generated
`𝔽₄`-linearly by the decoded Conway--Sloane patterns `[111111]` and `[0(02332)]`. The same Niemeier
lattice is constructed over the constant family `D₄` on `Fin 6` as `TauCeti.d4SixLattice`, and
identified in `TauCeti.LinearAlgebra.IntegralLattice.Rank24.D4Six.Lattice` with the overlattice of
the coordinate power `(D₄)⁶` of `TauCeti.IntegralLattice.checkerboardLattice 4` glued along the
hexacode.

This file connects the uniform table lattice `d4Sixth.lattice` to both models:

* Using `TauCeti.RootfulNiemeierType.map_glueSubgroup_d4Sixth`, a glue word of the row lies in
  `d4Sixth.glueSubgroup` exactly when its hexacode coordinates lie in `TauCeti.Hexacode.code ω`
  (`TauCeti.RootfulNiemeierType.mem_glueSubgroup_d4Sixth_iff_hexacode`).
* Naturality of gluing under equal families of components gives the coordinate-preserving isometry
  `TauCeti.RootfulNiemeierType.d4SixthLatticeIsometry` from `d4Sixth.lattice` onto
  `TauCeti.d4SixLattice`.
* Composing with `TauCeti.d4SixHexacodeOverlatticeIsometry` yields
  `TauCeti.RootfulNiemeierType.d4SixthLatticeHexacodeOverlatticeIsometry`, identifying
  `d4Sixth.lattice` with the hexacode gluing of `(D₄)⁶`, and transports monomial automorphisms of
  the hexacode to self-isometries `TauCeti.RootfulNiemeierType.d4SixthLatticeHexacodeAutIsometry`
  of the table lattice.
* Specializing the general gluing theorems to `d4Sixth` records unimodularity, preservation of all
  norm shells below `4`, and recovery of the root sublattice `d4Sixth.rootLattice` directly for
  `d4Sixth.lattice`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4,
  §§3 and 7, Chapter 7, §§8--9, and Chapter 16, §1, Table 16.1.
-/

public section

namespace TauCeti

namespace RootfulNiemeierType

open DynkinType IntegralLattice

/-! ### Hexacode characterization of the table glue subgroup -/

/-- A glue word of the row `D₄⁶` lies in the table glue subgroup `d4Sixth.glueSubgroup` exactly
when its image under `d4SixthGlueModuleIsometry` lies in `d4SixGlueSubgroup`. -/
theorem d4SixthGlueModuleIsometry_mem_d4SixGlueSubgroup_iff (w : d4Sixth.glueModule) :
    d4SixthGlueModuleIsometry w ∈ d4SixGlueSubgroup ↔ w ∈ d4Sixth.glueSubgroup := by
  rw [← map_glueSubgroup_d4Sixth]
  exact AddSubgroup.mem_map_iff_mem d4SixthGlueModuleIsometry.injective

/-- **The table glue subgroup of `D₄⁶` is the hexacode**: a glue word of the row lies in
`d4Sixth.glueSubgroup` exactly when its image under `d4SixthGlueModuleIsometry` and
`d4SixHexacodeIsometry` belongs to `Hexacode.code ω`. -/
theorem mem_glueSubgroup_d4Sixth_iff_hexacode {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (w : d4Sixth.glueModule) :
    w ∈ d4Sixth.glueSubgroup ↔
      d4SixHexacodeIsometry hF hω (d4SixthGlueModuleIsometry w) ∈ Hexacode.code ω := by
  rw [← d4SixthGlueModuleIsometry_mem_d4SixGlueSubgroup_iff, mem_d4SixGlueSubgroup_iff hF hω]

/-! ### Unimodularity and root sublattice of `d4Sixth.lattice` -/

/-- **The table lattice `d4Sixth.lattice` is unimodular.** -/
theorem isUnimodular_lattice_d4Sixth : d4Sixth.lattice.IsUnimodular :=
  (isUnimodular_lattice_iff d4Sixth).mpr natCard_glueSubgroup_d4Sixth

/-- **Gluing along the table subgroup of `D₄⁶` adds no vectors of norm less than `4`**, compared
in the common ambient space. -/
theorem image_vectorsOfNorm_lattice_d4Sixth_eq {n : ℚ} (hn : n < 4) :
    (fun x : d4Sixth.lattice ↦ (x : ∀ i, Fin (d4Sixth.componentType i).rank → ℚ)) ''
        d4Sixth.lattice.vectorsOfNorm n =
      (fun x : d4Sixth.rootLattice ↦ (x : ∀ i, Fin (d4Sixth.componentType i).rank → ℚ)) ''
        d4Sixth.rootLattice.vectorsOfNorm n := by
  rw [lattice_def]
  exact DynkinType.image_vectorsOfNorm_gluedLattice_eq _ _ d4Sixth.valid_componentType _ _
    (fun _ hw hw0 ↦ four_le_sum_glueMinimum_of_mem_glueSubgroup_d4Sixth hw hw0) hn

/-- **The root sublattice of `d4Sixth.lattice` is `d4Sixth.rootLattice`**: the norm-`2` vectors of
the table lattice span the orthogonal sum of its six `D₄` root lattices. -/
theorem span_vectorsOfNorm_two_lattice_d4Sixth :
    Submodule.span ℤ
      ((fun x : d4Sixth.lattice ↦ (x : ∀ i, Fin (d4Sixth.componentType i).rank → ℚ)) ''
        d4Sixth.lattice.vectorsOfNorm 2) = d4Sixth.rootLattice.carrier := by
  rw [lattice_def]
  exact DynkinType.span_vectorsOfNorm_two_gluedLattice _ _ d4Sixth.valid_componentType _ _
    (fun _ hw hw0 ↦ four_le_sum_glueMinimum_of_mem_glueSubgroup_d4Sixth hw hw0) (by norm_num)

/-! ### Comparison of the table lattice with `d4SixLattice` and `(D₄)⁶` -/

/-- Reindexing glue words of `d4Sixth` by `piGlueAlphabetCongr` agrees with
`d4SixthGlueModuleIsometry`, since both preserve every Conway--Sloane digit. -/
private theorem piGlueAlphabetCongr_eq_d4SixthGlueModuleIsometry (w : d4Sixth.glueModule) :
    piGlueAlphabetCongr d4Sixth.componentType d4Sixth.isSimplyLaced_componentType
        (finCongr (rfl : 6 = d4Sixth.components.length)) (fun _ ↦ componentType_d4Sixth _) w =
      d4SixthGlueModuleIsometry w :=
  encodeGlueWord_injective _ _ <|
    (encodeGlueWord_piGlueAlphabetCongr _ _ _ _ _ w).trans
      (encodeGlueWord_glueModuleIsometry _ _ _ _ w).symm

private theorem piGlueAlphabetCongr_mem_d4SixGlueSubgroup_iff (w : d4Sixth.glueModule) :
    piGlueAlphabetCongr d4Sixth.componentType d4Sixth.isSimplyLaced_componentType
        (finCongr (rfl : 6 = d4Sixth.components.length)) (fun _ ↦ componentType_d4Sixth _) w ∈
      d4SixGlueSubgroup ↔ w ∈ d4Sixth.glueSubgroup := by
  rw [piGlueAlphabetCongr_eq_d4SixthGlueModuleIsometry,
    d4SixthGlueModuleIsometry_mem_d4SixGlueSubgroup_iff]

/-- **The table lattice of `D₄⁶` is `TauCeti.d4SixLattice`**, by the coordinate-preserving
isometry identifying the six `D₄` components of the row with the constant family on `Fin 6`. -/
noncomputable def d4SixthLatticeIsometry : Isometry d4Sixth.lattice d4SixLattice :=
  (Isometry.ofEq (lattice_def _)).trans <|
    (gluedLatticeIsometryOfEq _ _ _ _ _ _ _ _ _
      piGlueAlphabetCongr_mem_d4SixGlueSubgroup_iff).trans
    (Isometry.ofEq d4SixLattice_def.symm)

/-- `d4SixthLatticeIsometry` keeps every Bourbaki simple-root coordinate, up to the identification
of the component Dynkin type with `D₄`. -/
-- Not `@[simp]`: `simp` rewrites `(D 4).rank` inside the argument `j` by `rank_D`.
theorem d4SixthLatticeIsometry_apply
    (x : ∀ i, Fin (d4Sixth.componentType i).rank → ℚ) (k : Fin 6) (j : Fin (D 4).rank) :
    d4SixthLatticeIsometry x k j =
      x k (Fin.cast (congrArg rank (componentType_d4Sixth k)).symm j) := by
  rw [d4SixthLatticeIsometry, Isometry.trans_apply, Isometry.trans_apply, Isometry.ofEq_apply,
    Isometry.ofEq_apply]
  exact gluedLatticeIsometryOfEq_apply (s := fun _ ↦ D 4) _ _ _ _ _ _ _ _ _ _ x k j

/-- The inverse of `d4SixthLatticeIsometry` keeps every Bourbaki simple-root coordinate, up to the
identification of the component Dynkin type with `D₄`. -/
-- Not `@[simp]`: `simp` rewrites `d4Sixth.componentType k` inside the argument `j` by
-- `componentType_d4Sixth`.
theorem d4SixthLatticeIsometry_symm_apply
    (y : Fin 6 → Fin (D 4).rank → ℚ) (k : Fin d4Sixth.components.length)
    (j : Fin (d4Sixth.componentType k).rank) :
    d4SixthLatticeIsometry.symm y k j =
      y k (Fin.cast (congrArg rank (componentType_d4Sixth k)) j) := by
  have h := d4SixthLatticeIsometry_apply (d4SixthLatticeIsometry.symm y) k
    (Fin.cast (congrArg rank (componentType_d4Sixth k)) j)
  rw [Isometry.apply_symm_apply, Fin.cast_cast, Fin.cast_refl] at h
  exact h.symm

section HexacodeOverlattice

variable {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)

/-- **The table lattice of `D₄⁶` is the hexacode gluing of `(D₄)⁶`**: composing
`d4SixthLatticeIsometry` with `d4SixHexacodeOverlatticeIsometry` identifies `d4Sixth.lattice` with
the overlattice of `(D₄)⁶` glued along `codeInTypeD4CoordinatePowerDiscriminant` of
`Hexacode.code ω`. -/
noncomputable def d4SixthLatticeHexacodeOverlatticeIsometry :
    Isometry d4Sixth.lattice
      (((checkerboardLattice 4).coordinatePower (Fin 6)).ofIsotropicSubgroup
        ((isEven_checkerboardLattice 4).coordinatePower (Fin 6))
        (codeInTypeD4CoordinatePowerDiscriminant hF hω (Hexacode.code ω).toAddSubgroup)
        (Hexacode.isLagrangian_codeInTypeD4CoordinatePowerDiscriminant hF hω hω).isIsotropic) :=
  d4SixthLatticeIsometry.trans (d4SixHexacodeOverlatticeIsometry hF hω)

/-- In coordinate `j : Fin 6`, `d4SixthLatticeHexacodeOverlatticeIsometry` passes the `j`-th
component of `x` to the checkerboard lattice `D₄` and applies the power of triality realizing the
`j`-th hexacode coordinate scaling. -/
@[simp]
theorem d4SixthLatticeHexacodeOverlatticeIsometry_apply
    (x : ∀ i, Fin (d4Sixth.componentType i).rank → ℚ) (j : Fin 6) :
    d4SixthLatticeHexacodeOverlatticeIsometry hF hω x j =
      checkerboardScalarIsometry hF hω (d4SixHexacodeScaling hω j)
        (rootLatticeIsometryCheckerboard 4 le_rfl (isSimplyLaced_D 4)
          fun i ↦ x j (Fin.cast (congrArg rank (componentType_d4Sixth j)).symm i)) := by
  rw [d4SixthLatticeHexacodeOverlatticeIsometry, Isometry.trans_apply,
    d4SixHexacodeOverlatticeIsometry_apply]
  exact congrArg _ (congrArg _ (funext (d4SixthLatticeIsometry_apply x j)))

/-- The inverse of `d4SixthLatticeHexacodeOverlatticeIsometry` undoes the `k`-th hexacode triality
scaling in checkerboard coordinates and passes back to the Bourbaki simple-root coordinates of the
`k`-th table component. -/
-- Not `@[simp]`: `simp` rewrites `d4Sixth.componentType k` inside the argument `j` by
-- `componentType_d4Sixth`.
theorem d4SixthLatticeHexacodeOverlatticeIsometry_symm_apply
    (y : Fin 6 → Fin 4 → ℚ) (k : Fin d4Sixth.components.length)
    (j : Fin (d4Sixth.componentType k).rank) :
    (d4SixthLatticeHexacodeOverlatticeIsometry hF hω).symm y k j =
      (rootLatticeIsometryCheckerboard 4 le_rfl (isSimplyLaced_D 4)).symm
        (checkerboardScalarIsometry hF hω (d4SixHexacodeScaling hω k)⁻¹ (y k))
        (Fin.cast (congrArg rank (componentType_d4Sixth k)) j) := by
  rw [d4SixthLatticeHexacodeOverlatticeIsometry, Isometry.symm_trans, Isometry.trans_apply,
    d4SixthLatticeIsometry_symm_apply]
  exact congrFun (d4SixHexacodeOverlatticeIsometry_symm_apply hF hω y k) _

/-- **Every monomial automorphism of the hexacode induces a self-isometry of the table lattice
`d4Sixth.lattice`**, obtained by conjugating `d4SixHexacodeAutIsometry` along
`d4SixthLatticeIsometry`. -/
noncomputable def d4SixthLatticeHexacodeAutIsometry (u : Fin 6 → Fˣ) (σ : Equiv.Perm (Fin 6))
    (he : monomialEquiv u σ ∈ monomialAut (Hexacode.code ω)) :
    Isometry d4Sixth.lattice d4Sixth.lattice :=
  d4SixthLatticeIsometry.symm.conjMulEquiv (d4SixHexacodeAutIsometry hF hω u σ he)

/-- Pointwise coordinate formula for `d4SixthLatticeHexacodeAutIsometry` on the `k`-th `D₄`
component of the table lattice. -/
-- Not `@[simp]`: `simp` rewrites `d4Sixth.componentType k` inside the argument `i` by
-- `componentType_d4Sixth`.
theorem d4SixthLatticeHexacodeAutIsometry_apply
    (u : Fin 6 → Fˣ) (σ : Equiv.Perm (Fin 6))
    (he : monomialEquiv u σ ∈ monomialAut (Hexacode.code ω))
    (x : ∀ m, Fin (d4Sixth.componentType m).rank → ℚ)
    (k : Fin d4Sixth.components.length) (i : Fin (d4Sixth.componentType k).rank) :
    d4SixthLatticeHexacodeAutIsometry hF hω u σ he x k i =
      typeD4ScalarIsometry (isSimplyLaced_D 4) hF hω
        ((d4SixHexacodeScaling hω k)⁻¹ * u (σ.symm k) * d4SixHexacodeScaling hω (σ.symm k))
        (fun m ↦ x (σ.symm k) (Fin.cast (congrArg rank (componentType_d4Sixth (σ.symm k))).symm m))
        (Fin.cast (congrArg rank (componentType_d4Sixth k)) i) := by
  rw [d4SixthLatticeHexacodeAutIsometry, Isometry.conjMulEquiv_apply, Isometry.symm_symm,
    d4SixthLatticeIsometry_symm_apply]
  exact congrFun ((d4SixHexacodeAutIsometry_apply hF hω u σ he _ k).trans
    (congrArg _ (funext (d4SixthLatticeIsometry_apply x (σ.symm k))))) _

/-- `d4SixthLatticeIsometry` intertwines `d4SixthLatticeHexacodeAutIsometry` with
`d4SixHexacodeAutIsometry`. -/
-- Not `@[simp]`: `simp` rewrites `(D 4).rank` inside the `DFunLike.coe` motive by `rank_D`.
theorem d4SixthLatticeIsometry_d4SixthLatticeHexacodeAutIsometry_apply
    (u : Fin 6 → Fˣ) (σ : Equiv.Perm (Fin 6))
    (he : monomialEquiv u σ ∈ monomialAut (Hexacode.code ω))
    (x : ∀ i, Fin (d4Sixth.componentType i).rank → ℚ) :
    d4SixthLatticeIsometry (d4SixthLatticeHexacodeAutIsometry hF hω u σ he x) =
      d4SixHexacodeAutIsometry hF hω u σ he (d4SixthLatticeIsometry x) := by
  rw [d4SixthLatticeHexacodeAutIsometry, Isometry.conjMulEquiv_apply, Isometry.symm_symm,
    Isometry.apply_symm_apply]

/-- `d4SixthLatticeHexacodeOverlatticeIsometry` intertwines `d4SixthLatticeHexacodeAutIsometry`
with the direct monomial action `d4SixCheckerboardHexacodeAutIsometry` on the hexacode gluing of
`(D₄)⁶`. -/
@[simp]
theorem
    d4SixthLatticeHexacodeOverlatticeIsometry_d4SixthLatticeHexacodeAutIsometry_apply
    (u : Fin 6 → Fˣ) (σ : Equiv.Perm (Fin 6))
    (he : monomialEquiv u σ ∈ monomialAut (Hexacode.code ω))
    (x : ∀ i, Fin (d4Sixth.componentType i).rank → ℚ) :
    d4SixthLatticeHexacodeOverlatticeIsometry hF hω
        (d4SixthLatticeHexacodeAutIsometry hF hω u σ he x) =
      d4SixCheckerboardHexacodeAutIsometry hF hω u σ he
        (d4SixthLatticeHexacodeOverlatticeIsometry hF hω x) := by
  rw [d4SixthLatticeHexacodeOverlatticeIsometry, Isometry.trans_apply, Isometry.trans_apply,
    d4SixthLatticeIsometry_d4SixthLatticeHexacodeAutIsometry_apply,
    d4SixHexacodeOverlatticeIsometry_d4SixHexacodeAutIsometry_apply]

end HexacodeOverlattice

end RootfulNiemeierType

end TauCeti
