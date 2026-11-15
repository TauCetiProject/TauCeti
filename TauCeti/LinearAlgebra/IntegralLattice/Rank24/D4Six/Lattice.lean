/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.RootDiscriminant
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.D4Six.Glue
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.Roots
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Triality

/-!
# The Niemeier lattice with root system `D₄⁶`

`TauCeti.d4SixLattice` is the even overlattice of six orthogonal `D₄` root lattices obtained
by gluing along the hexacode in the Conway--Sloane label coordinates. It is positive definite,
unimodular and of rank `24`. Its carrier is the inverse image of the actual hexacode under the
dual-class map and the previously constructed discriminant isometry.

Every nonzero glue word has coset minimum at least `4`. Consequently gluing preserves all
norm shells below `4`, and the integral span of the norm-`2` vectors is literally the original
orthogonal sum of six `D₄` root lattices. This identifies the root sublattice rather than merely
counting roots. The named construction also provides the lattice on which hexacode symmetries
can act through component isometries.

Identifying each `D₄` component with the checkerboard lattice `D₄ ⊂ ℚ⁴` and applying the power of
triality realizing the hexacode coordinate scaling `[ω, ω, 1, ω², ω², 1]` gives the root-lattice
comparison `TauCeti.d4SixRootIsometry` onto `(D₄)⁶`. On discriminant groups it acts by
`TauCeti.d4SixHexacodeIsometry`, so it restricts to `TauCeti.d4SixHexacodeOverlatticeIsometry`,
identifying `d4SixLattice` with the overlattice of `(D₄)⁶` glued directly along the hexacode via
`TauCeti.codeInTypeD4CoordinatePowerDiscriminant`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed.,
  Chapter 4 §§3 and 6, Chapter 7 §§8--9, and Chapter 16 §1, Table 16.1.
-/

public section

namespace TauCeti

open DynkinType IntegralLattice

/-- The orthogonal sum of six `D₄` root lattices, in Bourbaki simple-root coordinates. -/
noncomputable abbrev d4SixRootLattice : IntegralLattice (Fin 6 → Fin (D 4).rank → ℚ) :=
  pi fun _ : Fin 6 ↦ (D 4).rootLattice (isSimplyLaced_D 4)

/-- The Niemeier lattice with root system `D₄⁶`, glued along the hexacode subgroup generated
`F₄`-linearly by the Conway--Sloane words `[111111]` and `[0(02332)]`. -/
noncomputable def d4SixLattice : IntegralLattice (Fin 6 → Fin (D 4).rank → ℚ) :=
  gluedLattice (fun _ : Fin 6 ↦ D 4) (fun _ ↦ isSimplyLaced_D 4) (fun _ ↦ valid_D.mpr le_rfl)
    d4SixGlueSubgroup isLagrangian_d4SixGlueSubgroup.isIsotropic

/-- The defining presentation of `D₄⁶` by the general isotropic gluing construction. -/
theorem d4SixLattice_def :
    d4SixLattice = gluedLattice (fun _ : Fin 6 ↦ D 4) (fun _ ↦ isSimplyLaced_D 4)
      (fun _ ↦ valid_D.mpr le_rfl) d4SixGlueSubgroup
      isLagrangian_d4SixGlueSubgroup.isIsotropic :=
  (rfl)

/-- A vector lies in `D₄⁶` exactly when it lies in the dual of the orthogonal root lattice
and its discriminant class, read in glue-word coordinates, lies in the hexacode glue subgroup. -/
theorem mem_d4SixLattice_carrier_iff (x : Fin 6 → Fin (D 4).rank → ℚ) :
    x ∈ d4SixLattice.carrier ↔ ∃ hx : x ∈ d4SixRootLattice.dualCarrier,
      (glueWordIsometry (fun _ : Fin 6 ↦ D 4) (fun _ ↦ isSimplyLaced_D 4)
        (fun _ ↦ valid_D.mpr le_rfl)).toAddEquiv.symm (Submodule.Quotient.mk ⟨x, hx⟩) ∈
          d4SixGlueSubgroup :=
  mem_gluedLattice_carrier_iff _ _ _ _ _ x

/-- The carrier condition in the coordinates of the actual hexacode over any field of four
elements with chosen primitive cube root `ω`. The coordinate scalings are those of
`d4SixHexacodeIsometry`. -/
theorem mem_d4SixLattice_carrier_iff_hexacode {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
    (x : Fin 6 → Fin (D 4).rank → ℚ) :
    x ∈ d4SixLattice.carrier ↔ ∃ hx : x ∈ d4SixRootLattice.dualCarrier,
      d4SixHexacodeIsometry hF hω
        ((glueWordIsometry (fun _ : Fin 6 ↦ D 4) (fun _ ↦ isSimplyLaced_D 4)
          (fun _ ↦ valid_D.mpr le_rfl)).toAddEquiv.symm (Submodule.Quotient.mk ⟨x, hx⟩)) ∈
            Hexacode.code ω :=
  (mem_d4SixLattice_carrier_iff x).trans
    (exists_congr fun _ ↦ mem_d4SixGlueSubgroup_iff hF hω)

/-- The root lattice `D₄⁶` is a sublattice of its hexacode overlattice. -/
theorem d4SixRootLattice_carrier_le_d4SixLattice_carrier :
    d4SixRootLattice.carrier ≤ d4SixLattice.carrier :=
  carrier_le_gluedLattice_carrier _ _ _ _ _

/-- The root lattice has index `64` in the hexacode overlattice. -/
theorem relIndex_d4SixRootLattice_d4SixLattice :
    d4SixRootLattice.carrier.toAddSubgroup.relIndex d4SixLattice.carrier.toAddSubgroup = 64 :=
  (relIndex_gluedLattice _ _ _ _ _).trans natCard_d4SixGlueSubgroup

/-- Gluing keeps the rational bilinear form of the orthogonal sum of six `D₄` root lattices. -/
@[simp]
theorem d4SixLattice_form : d4SixLattice.form = d4SixRootLattice.form :=
  gluedLattice_form _ _ _ _ _

/-- The hexacode overlattice is nondegenerate. -/
instance instIsNondegenerateD4SixLattice : d4SixLattice.IsNondegenerate :=
  isNondegenerate_gluedLattice _ _ _ _ _

/-- The hexacode overlattice is even. -/
theorem isEven_d4SixLattice : d4SixLattice.IsEven :=
  isEven_gluedLattice _ _ _ _ _

/-- The hexacode overlattice is unimodular because its glue subgroup is Lagrangian. -/
theorem isUnimodular_d4SixLattice : d4SixLattice.IsUnimodular :=
  (isUnimodular_gluedLattice_iff _ _ _ _ _).mpr isLagrangian_d4SixGlueSubgroup

/-- The hexacode overlattice is positive definite. -/
theorem isPosDef_d4SixLattice : d4SixLattice.IsPosDef :=
  isPosDef_gluedLattice _ _ _ _ _

/-- The hexacode overlattice has rank `24`. -/
-- Not a simp lemma: `rank_D` rewrites the ambient type in its left-hand side.
theorem finrank_d4SixLattice : Module.finrank ℤ d4SixLattice = 24 := by
  rw [d4SixLattice_def, finrank_gluedLattice]
  simp

/-- Gluing along the hexacode adds no vectors of norm less than `4`, compared in the common
rational ambient space. In particular the norm-`2` vectors are exactly the old roots. -/
theorem image_vectorsOfNorm_d4SixLattice_eq {n : ℚ} (hn : n < 4) :
    (fun x : d4SixLattice ↦ (x : Fin 6 → Fin (D 4).rank → ℚ)) ''
        d4SixLattice.vectorsOfNorm n =
      (fun x : d4SixRootLattice ↦ (x : Fin 6 → Fin (D 4).rank → ℚ)) ''
        d4SixRootLattice.vectorsOfNorm n :=
  image_vectorsOfNorm_gluedLattice_eq _ _ _ _ _
    (fun _ hw hw0 ↦ four_le_sum_glueMinimum_of_mem_d4SixGlueSubgroup hw hw0) hn

/-- The root sublattice of the hexacode overlattice is exactly the embedded orthogonal sum
of six `D₄` root lattices: its roots span that carrier, and gluing introduces no new roots. -/
theorem span_vectorsOfNorm_two_d4SixLattice :
    Submodule.span ℤ ((fun x : d4SixLattice ↦ (x : Fin 6 → Fin (D 4).rank → ℚ)) ''
      d4SixLattice.vectorsOfNorm 2) = d4SixRootLattice.carrier := by
  rw [image_vectorsOfNorm_d4SixLattice_eq (by norm_num : (2 : ℚ) < 4)]
  exact span_vectorsOfNorm_two_pi_rootLattice _ _

/-! ### Comparison with the hexacode gluing of `(D₄)⁶` -/

section HexacodeOverlattice

variable {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)

/-- **The `D₄⁶` comparison on root lattices.** The isometry from the orthogonal sum of six `D₄`
root lattices in Bourbaki simple-root coordinates to the coordinate power `(D₄)⁶` of the
checkerboard lattice `D₄ ⊂ ℚ⁴` that identifies each component with `D₄` and applies the power of
triality realizing the hexacode coordinate scaling `d4SixHexacodeScaling hω j` from
`[ω, ω, 1, ω², ω², 1]`. -/
noncomputable def d4SixRootIsometry :
    Isometry d4SixRootLattice ((checkerboardLattice 4).coordinatePower (Fin 6)) :=
  Isometry.pi fun j ↦
    (rootLatticeIsometryCheckerboard 4 le_rfl (isSimplyLaced_D 4)).trans
      (checkerboardScalarIsometry hF hω (d4SixHexacodeScaling hω j))

/-- The `j`-th coordinate of the image of `x` under `d4SixRootIsometry` is obtained by passing to
checkerboard coordinates and applying `checkerboardScalarIsometry` for the `j`-th hexacode
scaling. -/
-- Not `@[simp]`: `simp` rewrites `(D 4).rank` inside the left-hand side by `rank_D`.
theorem d4SixRootIsometry_apply (x : Fin 6 → Fin (D 4).rank → ℚ) (j : Fin 6) :
    d4SixRootIsometry hF hω x j =
      checkerboardScalarIsometry hF hω (d4SixHexacodeScaling hω j)
        (rootLatticeIsometryCheckerboard 4 le_rfl (isSimplyLaced_D 4) (x j)) := by
  rw [d4SixRootIsometry, Isometry.pi_apply, Isometry.trans_apply]

/-- The inverse of `d4SixRootIsometry` undoes the `j`-th hexacode triality scaling in checkerboard
coordinates and passes back to Bourbaki simple-root coordinates. -/
-- Not `@[simp]`: `simp` rewrites `(D 4).rank` inside the ambient codomain type on the left-hand
-- side by `rank_D`.
theorem d4SixRootIsometry_symm_apply (y : Fin 6 → Fin 4 → ℚ) (j : Fin 6) :
    (d4SixRootIsometry hF hω).symm y j =
      (rootLatticeIsometryCheckerboard 4 le_rfl (isSimplyLaced_D 4)).symm
        (checkerboardScalarIsometry hF hω (d4SixHexacodeScaling hω j)⁻¹ (y j)) := by
  rw [d4SixRootIsometry, Isometry.pi_symm, Isometry.pi_apply, Isometry.symm_trans,
    Isometry.trans_apply, ← Isometry.inv_apply, ← checkerboardScalarIsometry_inv]

/-- On the discriminant class of a `D₄` glue label `x`, passing to the checkerboard lattice and
applying the `j`-th hexacode triality scaling multiplies its quaternary coordinate by the `j`-th
hexacode scaling. -/
private theorem discriminantGroupEquiv_rootLatticeIsometryCheckerboard_trans_d4SixHexacodeScaling
    (j : Fin 6) (x : (D 4).glueAlphabet (isSimplyLaced_D 4)) :
    ((rootLatticeIsometryCheckerboard 4 le_rfl (isSimplyLaced_D 4)).trans
        (checkerboardScalarIsometry hF hω (d4SixHexacodeScaling hω j))).discriminantGroupEquiv
      ((D 4).glueAlphabetIsometry (valid_D.mpr le_rfl) (isSimplyLaced_D 4) x) =
      typeD4QuaternaryDiscriminantQuadraticIsometry hF hω
        (d4SixHexacodeScaling hω j * typeD4GlueAlphabetQuaternaryIsometry hF hω x) := by
  rw [Isometry.discriminantGroupEquiv_trans, glueAlphabetIsometry_D_four_apply hF hω,
    Isometry.discriminantGroupEquiv_symm]
  exact (LinearEquiv.trans_apply _).trans ((congrArg _ (LinearEquiv.apply_symm_apply _ _)).trans
    (discriminantGroupEquiv_checkerboardScalarIsometry_typeD4QuaternaryDiscriminantQuadraticIsometry
      hF hω (d4SixHexacodeScaling hω j) _))

/-- **The root-lattice comparison acts on glue words by the hexacode comparison.** It carries the
discriminant class of a `D₄⁶` glue word `w` to the class of the quaternary word
`d4SixHexacodeIsometry hF hω w` in the discriminant group of `(D₄)⁶`. -/
theorem discriminantGroupEquiv_d4SixRootIsometry_glueWordIsometry (w : d4SixGlueModule) :
    (d4SixRootIsometry hF hω).discriminantGroupEquiv
        (glueWordIsometry (fun _ : Fin 6 ↦ D 4) (fun _ ↦ isSimplyLaced_D 4)
          (fun _ ↦ valid_D.mpr le_rfl) w) =
      (typeD4QuaternaryDiscriminantQuadraticIsometry hF hω).coordinatePowerDiscriminant (Fin 6)
        (d4SixHexacodeIsometry hF hω w) := by
  apply (discriminantGroupPiEquiv fun _ : Fin 6 ↦ checkerboardLattice 4).injective
  funext j
  have hw : d4SixHexacodeIsometry hF hω w j =
      d4SixHexacodeScaling hω j * typeD4GlueAlphabetQuaternaryIsometry hF hω (w j) := by
    rw [d4SixHexacodeIsometry_apply, d4SixQuaternaryIsometry_apply, coe_d4SixHexacodeScaling]
  -- `glueWordIsometry` and `coordinatePowerDiscriminant` land in discriminant quadratic-module
  -- carriers, so the `discriminantGroupPiEquiv` evaluations on both sides are combined in term
  -- mode rather than with `rw`.
  refine (discriminantGroupPiEquiv_discriminantGroupEquiv_pi
    (fun j ↦ (rootLatticeIsometryCheckerboard 4 le_rfl (isSimplyLaced_D 4)).trans
      (checkerboardScalarIsometry hF hω (d4SixHexacodeScaling hω j))) _ j).trans ?_
  refine (congrArg _ (discriminantGroupPiEquiv_glueWordIsometry _ _ _ w j)).trans ?_
  exact (discriminantGroupEquiv_rootLatticeIsometryCheckerboard_trans_d4SixHexacodeScaling hF hω
    j (w j)).trans ((congrArg (typeD4QuaternaryDiscriminantQuadraticIsometry hF hω) hw.symm).trans
      (FiniteQuadraticModule.Isometry.discriminantGroupPiEquiv_coordinatePowerDiscriminant_apply
        (typeD4QuaternaryDiscriminantQuadraticIsometry hF hω) (d4SixHexacodeIsometry hF hω w)
        j).symm)

/-- The root-lattice comparison carries the `D₄⁶` glue subgroup, read in the discriminant group of
`d4SixRootLattice`, onto the hexacode in the discriminant group of `(D₄)⁶`. -/
private theorem map_discriminantGroupEquiv_d4SixRootIsometry :
    (d4SixGlueSubgroup.map (glueWordIsometry (fun _ : Fin 6 ↦ D 4)
        (fun _ ↦ isSimplyLaced_D 4) (fun _ ↦ valid_D.mpr le_rfl)).toAddEquiv.toAddMonoidHom).map
      (d4SixRootIsometry hF hω).discriminantGroupEquiv.toAddEquiv.toAddMonoidHom =
      codeInTypeD4CoordinatePowerDiscriminant hF hω (Hexacode.code ω).toAddSubgroup := by
  have hcode : codeInTypeD4CoordinatePowerDiscriminant hF hω (Hexacode.code ω).toAddSubgroup =
      (Hexacode.code ω).toAddSubgroup.map ((typeD4QuaternaryDiscriminantQuadraticIsometry hF hω)
        |>.coordinatePowerDiscriminant (Fin 6)).toAddEquiv.toAddMonoidHom :=
    AddSubgroup.ext fun x ↦ (mem_codeInTypeD4CoordinatePowerDiscriminant_iff hF hω _ x).trans
      AddSubgroup.mem_map_equiv.symm
  refine Eq.trans ?_ hcode.symm
  exact (AddSubgroup.map_map _ _ _).trans <|
    ((congrArg d4SixGlueSubgroup.map
      (AddMonoidHom.ext (discriminantGroupEquiv_d4SixRootIsometry_glueWordIsometry hF hω))).trans
        (AddSubgroup.map_map _ _ _).symm).trans
      (congrArg (AddSubgroup.map _) (map_d4SixGlueSubgroup_d4SixHexacodeIsometry hF hω))

/-- **`D₄⁶` is the hexacode gluing of `(D₄)⁶`.** The root-lattice comparison `d4SixRootIsometry`
restricts to an isometry from the Niemeier lattice `d4SixLattice` onto the overlattice of the
coordinate power `(D₄)⁶` glued along the hexacode, placed in its discriminant group by
`TauCeti.codeInTypeD4CoordinatePowerDiscriminant`. -/
noncomputable def d4SixHexacodeOverlatticeIsometry :
    Isometry d4SixLattice
      (((checkerboardLattice 4).coordinatePower (Fin 6)).ofIsotropicSubgroup
        ((isEven_checkerboardLattice 4).coordinatePower (Fin 6))
        (codeInTypeD4CoordinatePowerDiscriminant hF hω (Hexacode.code ω).toAddSubgroup)
        (Hexacode.isLagrangian_codeInTypeD4CoordinatePowerDiscriminant hF hω hω).isIsotropic) :=
  (Isometry.ofEq (gluedLattice_def _ _ _ _ _)).trans
    ((d4SixRootIsometry hF hω).ofIsotropicSubgroups (isEven_pi_rootLattice _ _) _ _ _
      (map_discriminantGroupEquiv_d4SixRootIsometry hF hω))

/-- The isometry onto the hexacode gluing acts by the root-lattice comparison
`d4SixRootIsometry`. -/
-- Not `@[simp]`: `simp` rewrites `(D 4).rank` inside the left-hand side by `rank_D`.
theorem d4SixHexacodeOverlatticeIsometry_apply (x : Fin 6 → Fin (D 4).rank → ℚ) (j : Fin 6) :
    d4SixHexacodeOverlatticeIsometry hF hω x j =
      checkerboardScalarIsometry hF hω (d4SixHexacodeScaling hω j)
        (rootLatticeIsometryCheckerboard 4 le_rfl (isSimplyLaced_D 4) (x j)) :=
  (congrFun (Isometry.trans_apply _ _ x) j).trans <|
    (congrFun (Isometry.ofIsotropicSubgroups_apply _ _ _ _ _ _ _) j).trans <|
      (congrFun (congrArg (d4SixRootIsometry hF hω) (Isometry.ofEq_apply _ x)) j).trans
        (d4SixRootIsometry_apply hF hω x j)

/-- The inverse of `d4SixHexacodeOverlatticeIsometry` acts by the inverse of `d4SixRootIsometry`. -/
-- Not `@[simp]`: `simp` rewrites `(D 4).rank` inside the ambient codomain type on the left-hand
-- side by `rank_D`.
theorem d4SixHexacodeOverlatticeIsometry_symm_apply (y : Fin 6 → Fin 4 → ℚ) (j : Fin 6) :
    (d4SixHexacodeOverlatticeIsometry hF hω).symm y j =
      (rootLatticeIsometryCheckerboard 4 le_rfl (isSimplyLaced_D 4)).symm
        (checkerboardScalarIsometry hF hω (d4SixHexacodeScaling hω j)⁻¹ (y j)) :=
  -- Unfolding `d4SixHexacodeOverlatticeIsometry` exposes `codeInTypeD4CoordinatePowerDiscriminant`
  -- as a subgroup of `discriminantQuadraticModule.carrier`, so combine the evaluations with `trans`
  -- rather than `rw`.
  (congrFun ((DFunLike.congr_fun (Isometry.symm_trans _ _) y).trans <|
    (Isometry.trans_apply _ _ y).trans <|
      (DFunLike.congr_fun (Isometry.symm_ofEq _) _).trans <|
        (Isometry.ofEq_apply _ _).trans <|
          Isometry.ofIsotropicSubgroups_symm_apply _ _ _ _ _ _ y) j).trans
    (d4SixRootIsometry_symm_apply hF hω y j)

end HexacodeOverlattice

end TauCeti
