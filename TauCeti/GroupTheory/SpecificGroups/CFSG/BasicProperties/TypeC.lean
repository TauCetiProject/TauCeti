/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import TauCeti.GroupTheory.SpecificGroups.CFSG.SymplecticFrobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Simple

/-!
# The Steinberg fixed points and simplicity of the type-`C` groups on the classification list

The type-`C` carrier of `TauCeti.TypeCLieIndex` is the explicit full-weight standard symplectic
carrier, and `TauCeti.TypeCLieIndex.carrierEquivSymplectic` identifies it with the standard
symplectic matrix group `Sp_{2r}` over the algebraic closure of the prime field, leaving the
underlying matrices unchanged. The family is untwisted, so its Steinberg map is the carrier's
`q`-power Frobenius, and `TauCeti.TypeCLieIndex.carrierEquivSymplectic_frobenius` matches that
Frobenius with the entrywise `q`-power Frobenius of the matrix group.

This file transports the fixed points of the Steinberg map along that identification. The carrier
equivalence intertwines the two endomorphisms, so `TauCeti.fixedSubgroupCongr` turns their fixed
subgroups into isomorphic groups, and the fixed subgroup of the entrywise Frobenius is the finite
symplectic group `Sp_{2r}(𝔽_q)` of
`TauCeti.ValidLieTypeIndex.symplecticEquivFrobeniusFixedPoints`. The composite is
`TauCeti.TypeCLieIndex.symplecticEquivFixedPoints`, an isomorphism between that finite matrix group
and the fixed points `TauCeti.TypeCLieIndex.FixedPoints` of the index. Through
`TauCeti.DerivedCentralQuotient.congr` it identifies the candidate group
`TauCeti.TypeCLieIndex.Group` with the derived subgroup of `Sp_{2r}(𝔽_q)` modulo its centre, so
properties of `C_r(q)` can be proved on the finite matrix group itself.

A valid `C_r(q)` has rank `r ≥ 3`, so `Sp_{2r}(𝔽_q)` is perfect by
`TauCeti.GLSymplecticFin.commutator_eq_top_of_three_le`, over every finite field. Its derived
subgroup is then the whole group, and the candidate group of `C_r(q)` is the projective symplectic
group `PSp_{2r}(𝔽_q) = Sp_{2r}(𝔽_q) ⧸ Z(Sp_{2r}(𝔽_q))`, which is simple by Iwasawa's criterion
(`TauCeti.GLSymplecticFin.isSimpleGroup_quotient_center_of_commutator_eq_top`). This is the
simplicity of every `C_r(q)` on the classification list, read both on the type-`C` index and on the
assembled carrier `TauCeti.ValidLieTypeIndex.Group`.

`TauCeti.SpStd.pointsMulEquivFixedSubgroupFrobenius` describes the same fixed points as the
carrier's own points over the Frobenius-fixed subring of the closure. The isomorphism here lands
instead in the classical symplectic matrix group over Mathlib's `GaloisField`, with its root
subgroups `TauCeti.GLSymplecticFin.RootSubgroupIndex.hom` available over that field.

## Main definitions and results

* `TauCeti.TypeCLieIndex.symplecticEquivFixedPoints`: the fixed points of the Steinberg map of a
  type-`C` index of rank `r` and field order `q` are the finite symplectic group `Sp_{2r}(𝔽_q)`.
* `TauCeti.TypeCLieIndex.coe_symplecticEquivFixedPoints`: the isomorphism extends the coefficients
  of a finite-field symplectic matrix to the closure.
* `TauCeti.TypeCLieIndex.commutator_symplectic_eq_top`: `Sp_{2r}(𝔽_q)` is perfect.
* `TauCeti.TypeCLieIndex.projectiveSymplecticEquivGroup`: the group attached to `C_r(q)` is
  `PSp_{2r}(𝔽_q)`.
* `TauCeti.TypeCLieIndex.isSimpleGroup_group` and `TauCeti.ValidLieTypeIndex.isSimpleGroup_C`: the
  group attached to `C_r(q)` is simple.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§1.2 and 11.3.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.

The organization follows `TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.TypeA`, the same
transport for the special linear group.
-/

public section

noncomputable section

namespace TauCeti.TypeCLieIndex

variable (d : TypeCLieIndex)

/-- **The Steinberg fixed points of `C_r(q)` are the finite symplectic group `Sp_{2r}(𝔽_q)`.**

The carrier equivalence intertwines the carrier Steinberg map with the entrywise `q`-power
Frobenius of the standard symplectic matrix group, so it identifies their fixed subgroups, while
the fixed subgroup of that Frobenius is the finite symplectic group by the coefficient
identification. Here `r = carrierRank + 1` is the rank of the index. -/
def symplecticEquivFixedPoints :
    GLSymplecticFin (d.carrierRank + 1) (GaloisField d.1.characteristic d.1.fieldExponent) ≃*
      d.FixedPoints :=
  (ValidLieTypeIndex.symplecticEquivFrobeniusFixedPoints d.1 (d.carrierRank + 1)).trans
    (fixedSubgroupCongr d.carrierEquivSymplectic
      (MonoidHom.ext fun g => by
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.coe_ofClass, steinberg_def,
          carrierEquivSymplectic_frobenius, symplecticFrobenius_def])).symm

/-- **The isomorphism to the Steinberg fixed points extends the coefficients of a finite-field
symplectic matrix to the closure**: the fixed point attached to a matrix over `𝔽_q` has, as its
underlying invertible matrix, that matrix read over the closure. -/
@[simp]
theorem coe_symplecticEquivFixedPoints
    (g : GLSymplecticFin (d.carrierRank + 1)
      (GaloisField d.1.characteristic d.1.fieldExponent)) :
    (((d.symplecticEquivFixedPoints g : d.AmbientGroup) : SpStd.points d.carrierRank d.1.Closure) :
        Matrix.GeneralLinearGroup (Fin (d.carrierRank + 1 + (d.carrierRank + 1))) d.1.Closure) =
      Matrix.GeneralLinearGroup.map d.1.galoisFieldEmbedding
        (g : Matrix.GeneralLinearGroup (Fin (d.carrierRank + 1 + (d.carrierRank + 1)))
          (GaloisField d.1.characteristic d.1.fieldExponent)) := by
  rw [symplecticEquivFixedPoints, MulEquiv.trans_apply, coe_fixedSubgroupCongr_symm_apply,
    coe_carrierEquivSymplectic_symm_apply,
    ValidLieTypeIndex.coe_symplecticEquivFrobeniusFixedPoints]

/-- **The finite symplectic group of `C_r(q)` is perfect**, because the rank `r` of a valid index
is at least three. -/
theorem commutator_symplectic_eq_top :
    commutator (GLSymplecticFin (d.carrierRank + 1)
      (GaloisField d.1.characteristic d.1.fieldExponent)) = ⊤ :=
  GLSymplecticFin.commutator_eq_top_of_three_le (by
    rw [carrierRank_add_one]
    exact d.three_le_rank)

/-- **The group attached to `C_r(q)` is the projective symplectic group `PSp_{2r}(𝔽_q)`.**

The fixed points are `Sp_{2r}(𝔽_q)` by `TauCeti.TypeCLieIndex.symplecticEquivFixedPoints`. That
group is perfect, so its derived subgroup is the whole group and the derived central quotient is
its quotient by the centre. -/
def projectiveSymplecticEquivGroup :
    GLSymplecticFin (d.carrierRank + 1) (GaloisField d.1.characteristic d.1.fieldExponent) ⧸
        Subgroup.center (GLSymplecticFin (d.carrierRank + 1)
          (GaloisField d.1.characteristic d.1.fieldExponent)) ≃* d.Group :=
  DerivedCentralQuotient.quotientCenterEquivOfPerfect d.commutator_symplectic_eq_top
    d.symplecticEquivFixedPoints

/-- The isomorphism with `PSp_{2r}(𝔽_q)` sends the class of a matrix in the derived subgroup to the
class of the corresponding fixed point. -/
@[simp]
theorem projectiveSymplecticEquivGroup_mk
    (x : commutator (GLSymplecticFin (d.carrierRank + 1)
      (GaloisField d.1.characteristic d.1.fieldExponent))) :
    d.projectiveSymplecticEquivGroup (QuotientGroup.mk (s := Subgroup.center _)
        (x : GLSymplecticFin (d.carrierRank + 1)
          (GaloisField d.1.characteristic d.1.fieldExponent))) =
      ((MulEquiv.commutatorCongr d.symplecticEquivFixedPoints x :
          commutator d.FixedPoints) : d.Group) :=
  DerivedCentralQuotient.quotientCenterEquivOfPerfect_mk _ _ x

/-- **The group attached to `C_r(q)` is simple**, for every valid index: it is `PSp_{2r}(𝔽_q)`,
which is simple by Iwasawa's criterion because `Sp_{2r}(𝔽_q)` is perfect. -/
theorem isSimpleGroup_group : IsSimpleGroup d.Group :=
  have := GLSymplecticFin.isSimpleGroup_quotient_center_of_commutator_eq_top
    d.commutator_symplectic_eq_top
  d.projectiveSymplecticEquivGroup.symm.isSimpleGroup

end TauCeti.TypeCLieIndex

namespace TauCeti.ValidLieTypeIndex

/-- **Every `C_r(q)` on the classification list is simple.** On the constructor `C r q` the
Steinberg endomorphism of the assembly is that of the type-`C` family, so the assembled candidate
is the type-`C` one. -/
theorem isSimpleGroup_C {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.C r q).Valid) :
    IsSimpleGroup (ValidLieTypeIndex.Group ⟨_, hv⟩) := by
  unfold ValidLieTypeIndex.Group
  rw [steinberg_C, GraphTwistedIndex.steinberg_C]
  exact TypeCLieIndex.isSimpleGroup_group ⟨⟨_, hv⟩, trivial⟩

end TauCeti.ValidLieTypeIndex

end
