/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Code.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.A1TwentyFour
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeA.ConstructionA

/-!
# The `A₁²⁴` glue lattice and Golay Construction A

Doubling simple-root coordinates and applying the Conway--Sloane-to-Golay permutation
identifies the base root lattice with the zero-code Construction A lattice. On discriminant
modules this is exactly `a1TableToGolayIsometry`, which carries the checked glue subgroup
onto the extended binary Golay code. Naturality of isotropic gluing therefore gives an
explicit isometry of the two overlattices. This is the rootful Golay Construction A lattice,
not the rootless Leech lattice.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*,
  Chapter 4 §3, Chapter 7 §6 and Chapter 16 §1.
-/

public section

namespace TauCeti

open IntegralLattice DynkinType

/-- The base-lattice isometry from `A₁²⁴` in table order to the zero-code binary
Construction A lattice in Golay order: double and permute the simple-root coordinates. -/
noncomputable def a1TableRootToZeroIsometry :
    IntegralLattice.Isometry a1TwentyFourthRootLattice (ConstructionA.zeroLattice 2 (Fin 24)) :=
  (Isometry.piCongrLeft (fun _ : Fin 24 ↦ (A 1).rootLattice (isSimplyLaced_A 1))
    a1TableToGolayPerm.symm).trans (a1ZeroLatticeIsometry (Fin 24))

/-- The destination coordinate `j` reads table coordinate `a1TableToGolayPerm j`, doubled. -/
-- Not a simp lemma: `rank_A` first normalizes the ambient index type.
theorem a1TableRootToZeroIsometry_apply (x : Fin 24 → Fin 1 → ℚ) (j : Fin 24) :
    a1TableRootToZeroIsometry x j = 2 * x (a1TableToGolayPerm j) 0 := by
  erw [a1TableRootToZeroIsometry, Isometry.trans_apply, a1ZeroLatticeIsometry_apply]
  have h := Isometry.piCongrLeft_apply_apply
    (fun _ : Fin 24 ↦ (A 1).rootLattice (isSimplyLaced_A 1))
    a1TableToGolayPerm.symm x (a1TableToGolayPerm j)
  exact congrArg (fun z : Fin 1 → ℚ ↦ 2 * z 0) (by simpa using h)

/-- The discriminant map of the base-lattice isometry is the prescribed quadratic
isometry from table glue words to binary Golay coordinates. -/
-- As with `finrank_a1TwentyFourthLattice`, `rank_A` simplifies the left-hand side's type.
theorem discriminantEquiv_a1TableRootToZeroIsometry_glueWordIsometry
    (w : a1TwentyFourGlueModule) :
    ConstructionA.discriminantEquiv 2 (Fin 24)
      (a1TableRootToZeroIsometry.discriminantGroupEquiv
        (glueWordIsometry (fun _ : Fin 24 ↦ A 1) (fun _ ↦ isSimplyLaced_A 1)
          (fun _ ↦ valid_A.mpr le_rfl) w)) = a1TableToGolayIsometry w := by
  have hn := discriminantQuadraticIsometry_piCongrLeft_glueWordIsometry
    (fun _ : Fin 24 ↦ A 1) (fun _ ↦ isSimplyLaced_A 1)
    (fun _ ↦ valid_A.mpr le_rfl) a1TableToGolayPerm.symm w
  erw [Isometry.discriminantQuadraticIsometry_apply] at hn
  -- Normalize the discriminant-module carrier before rewriting the underlying group maps.
  dsimp only [discriminantQuadraticModule, discriminantBilinearModule,
    a1TwentyFourthRootLattice] at hn ⊢
  rw [a1TableRootToZeroIsometry, Isometry.discriminantGroupEquiv_trans,
    LinearEquiv.trans_apply, hn]
  refine (discriminantEquiv_a1ZeroLatticeIsometry_glueWordIsometry (Fin 24) _).trans ?_
  funext j
  rw [a1TableToGolayIsometry_apply, typeA1GlueAlphabetZModStandardIsometry_apply]
  have h := Equiv.piCongrLeft_apply_apply
    (fun _ : Fin 24 ↦ ((A 1).glueAlphabet (isSimplyLaced_A 1)).carrier)
    a1TableToGolayPerm.symm w (a1TableToGolayPerm j)
  simpa using h

private theorem map_a1TableDiscriminantSubgroup :
    (a1TwentyFourGlueSubgroup.map
      (glueWordIsometry (fun _ : Fin 24 ↦ A 1) (fun _ ↦ isSimplyLaced_A 1)
        (fun _ ↦ valid_A.mpr le_rfl)).toAddEquiv.toAddMonoidHom).map
      a1TableRootToZeroIsometry.discriminantGroupEquiv.toAddEquiv.toAddMonoidHom =
        ConstructionA.codeInZeroLatticeDiscriminantGroup 2 (Fin 24)
          BinaryGolay.code.toAddSubgroup := by
  let f := (glueWordIsometry (fun _ : Fin 24 ↦ A 1) (fun _ ↦ isSimplyLaced_A 1)
    (fun _ ↦ valid_A.mpr le_rfl)).toAddEquiv.toAddMonoidHom
  let g := a1TableRootToZeroIsometry.discriminantGroupEquiv.toAddEquiv.toAddMonoidHom
  let d := (ConstructionA.discriminantEquiv 2 (Fin 24)).toAddEquiv.toAddMonoidHom
  have hc : d.comp (g.comp f) = a1TableToGolayIsometry.toAddEquiv.toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro w
    exact discriminantEquiv_a1TableRootToZeroIsometry_glueWordIsometry w
  apply AddSubgroup.map_injective (f := d)
    (ConstructionA.discriminantEquiv 2 (Fin 24)).injective
  calc
    ((a1TwentyFourGlueSubgroup.map f).map g).map d =
        a1TwentyFourGlueSubgroup.map (d.comp (g.comp f)) :=
      (congrArg (AddSubgroup.map d) (AddSubgroup.map_map _ g f)).trans
        (AddSubgroup.map_map _ d (g.comp f))
    _ = a1TwentyFourGlueSubgroup.map a1TableToGolayIsometry.toAddEquiv.toAddMonoidHom :=
      congrArg (fun h ↦ a1TwentyFourGlueSubgroup.map h) hc
    _ = BinaryGolay.code.toAddSubgroup := map_a1TwentyFourGlueSubgroup_a1TableToGolayIsometry
    _ = _ := (ConstructionA.map_codeInZeroLatticeDiscriminantGroup 2 (Fin 24) _).symm

/-- The `A₁²⁴` glue lattice is explicitly isometric to binary Golay Construction A.
The ambient map doubles and permutes simple-root coordinates. -/
noncomputable def a1TwentyFourthConstructionAIsometry :
    IntegralLattice.Isometry a1TwentyFourthLattice BinaryGolay.constructionALattice := by
  let hC := BinaryGolay.isIsotropic_code
  let hD := (ConstructionA.isIsotropic_codeInZeroLatticeDiscriminantQuadraticModule_iff
    2 (Fin 24) even_two BinaryGolay.code.toAddSubgroup).mpr hC
  let e := a1TableRootToZeroIsometry.ofIsotropicSubgroups
    (isEven_pi_rootLattice (fun _ : Fin 24 ↦ A 1) (fun _ ↦ isSimplyLaced_A 1))
    (ConstructionA.isEven_zeroLattice 2 (Fin 24) even_two)
    (((glueWordIsometry (fun _ : Fin 24 ↦ A 1) (fun _ ↦ isSimplyLaced_A 1)
      (fun _ ↦ valid_A.mpr le_rfl)).isIsotropic_map_iff _ _).mpr
        isLagrangian_a1TwentyFourGlueSubgroup.isIsotropic)
    hD map_a1TableDiscriminantSubgroup
  exact (Isometry.ofEq (a1TwentyFourthLattice_def.trans
    (gluedLattice_def _ _ _ _ _))).trans
    (e.trans (Isometry.ofEq
      ((ConstructionA.ofIsotropicSubgroup_codeInZeroLatticeDiscriminantGroup_eq_integralLattice
        2 (Fin 24) even_two BinaryGolay.code.toAddSubgroup hC).trans
          BinaryGolay.constructionALattice_eq_integralLattice.symm)))

/-- The isometry to Golay Construction A doubles table coordinate `p[j]` in destination
coordinate `j`, where `p = a1TableToGolayPerm`. -/
-- Not a simp lemma: `rank_A` first normalizes the ambient index type.
theorem a1TwentyFourthConstructionAIsometry_apply
    (x : Fin 24 → Fin (A 1).rank → ℚ) (j : Fin 24) :
    a1TwentyFourthConstructionAIsometry x j =
      2 * x (a1TableToGolayPerm j) ⟨0, by decide⟩ := by
  -- Evaluate each factor separately: rewriting the whole composite would require unfolding
  -- the quadratic-module carriers inside its dependent isotropy proofs.
  unfold a1TwentyFourthConstructionAIsometry
  refine (congrArg (fun y : Fin 24 → ℚ ↦ y j) (Isometry.trans_apply _ _ x)).trans ?_
  refine (congrArg (fun y ↦ (_ : (Fin 24 → Fin (A 1).rank → ℚ) → Fin 24 → ℚ) y j)
    (Isometry.ofEq_apply _ x)).trans ?_
  refine (congrArg (fun y : Fin 24 → ℚ ↦ y j) (Isometry.trans_apply _ _ x)).trans ?_
  refine (congrArg (fun y : Fin 24 → ℚ ↦ y j) (Isometry.ofEq_apply _ _)).trans ?_
  refine (congrArg (fun y : Fin 24 → ℚ ↦ y j)
    (Isometry.ofIsotropicSubgroups_apply _ _ _ _ _ _ x)).trans ?_
  exact a1TableRootToZeroIsometry_apply x j

end TauCeti
