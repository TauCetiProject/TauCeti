/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.D4Six.Glue
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.Roots

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

end TauCeti
