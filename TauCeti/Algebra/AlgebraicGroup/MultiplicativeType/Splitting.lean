/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.CharacterLattice
public import TauCeti.Algebra.HopfAlgebra.GroupLike.FiniteExtension
public import TauCeti.Algebra.Bialgebra.GroupLike.PurelyInseparable
public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Reconstruction
public import Mathlib.FieldTheory.Galois.GaloisClosure
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange

/-!
# Finite Galois splitting fields for groups of multiplicative type

Every finite-type affine group of multiplicative type becomes diagonalizable over a finite
Galois intermediate field of an algebraic closure. Purely inseparable descent first gives
splitting over the separable closure. Finitely many character generators then give a finite
separable splitting field, whose normal closure is Galois. Neither perfectness nor smoothness
is required. The original coordinate Hopf algebra is recovered as the invariant group algebra
of its characters over this splitting field.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.multiplicativeTypeCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- Every finite-type group of multiplicative type is diagonalizable over a finite algebraic
extension. -/
theorem exists_finiteDimensional_groupLikeSpanned_baseChange
    (hH : multiplicativeTypeCommHopfAlgProperty k H) :
    ∃ L : IntermediateField k (AlgebraicClosure k), FiniteDimensional k L ∧
      DiagonalizableGroup.groupLikeSpannedProperty L
        (FiniteTypeCommHopfAlgCat.baseChange (K := L) H) := by
  let _ := CommHopfAlgCat.geometricCharacterGroup_fg_of_multiplicativeType H hH
  have hspan := (Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top
    (R := AlgebraicClosure k)
    (C := CommHopfAlgCat.baseChange (K := AlgebraicClosure k) H.obj)).mp
      ((DiagonalizableGroup.groupLikeSpannedProperty_iff _ _).mp
        ((multiplicativeTypeCommHopfAlgProperty_iff k H).mp hH))
  obtain ⟨L, hL, hspanL⟩ := exists_finiteDimensional_span_groupLike_eq_top hspan
  refine ⟨L, hL, (DiagonalizableGroup.groupLikeSpannedProperty_iff _ _).mpr ?_⟩
  exact Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top.mpr hspanL

/-- Over the separable closure, a multiplicative-type coordinate algebra is spanned
by its group-like elements, even when the ground field is imperfect. -/
theorem span_groupLike_separableClosure_eq_top
    (hH : multiplicativeTypeCommHopfAlgProperty k H) :
    Submodule.span (separableClosure k (AlgebraicClosure k))
      (Set.range (_root_.GroupLike.val
        (R := separableClosure k (AlgebraicClosure k))
        (A := separableClosure k (AlgebraicClosure k) ⊗[k] H))) = ⊤ := by
  have hspanΩ := (DiagonalizableGroup.groupLikeSpannedProperty_iff _ _).mp
    ((multiplicativeTypeCommHopfAlgProperty_iff k H).mp hH)
  apply span_groupLike_eq_top_of_isPurelyInseparable
    (k := separableClosure k (AlgebraicClosure k)) (L := AlgebraicClosure k)
    (A := separableClosure k (AlgebraicClosure k) ⊗[k] H)
  rw [← Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top]
  exact (Subcoalgebra.groupLikeSetSpan_eq_top_iff_of_coalgEquiv
    (Bialgebra.TensorProduct.baseChangeTowerBialgEquiv k
      (separableClosure k (AlgebraicClosure k)) H (AlgebraicClosure k)).toCoalgEquiv).mpr hspanΩ

/-- Every finite-type group of multiplicative type becomes diagonalizable over a finite
Galois intermediate field of the algebraic closure, over an arbitrary base field. -/
theorem exists_finiteGalois_groupLikeSpanned_baseChange
    (hH : multiplicativeTypeCommHopfAlgProperty k H) :
    ∃ L : FiniteGaloisIntermediateField k (AlgebraicClosure k),
      DiagonalizableGroup.groupLikeSpannedProperty L
        (FiniteTypeCommHopfAlgCat.baseChange (K := L) H) := by
  let F := separableClosure k (AlgebraicClosure k)
  have hspanF : Submodule.span F
      (Set.range (_root_.GroupLike.val (R := F) (A := F ⊗[k] H))) = ⊤ :=
    hH.span_groupLike_separableClosure_eq_top
  let _ := CommHopfAlgCat.geometricCharacterGroup_fg_of_multiplicativeType H hH
  let _ : Group (_root_.GroupLike F (F ⊗[k] H)) :=
    _root_.GroupLike.instGroup (R := F) (A := F ⊗[k] H)
  let e := groupLikeScalarTowerEquiv (K := AlgebraicClosure k) hspanF
  let _ : Group.FG (_root_.GroupLike F (F ⊗[k] H)) :=
    Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨E, hE, hspanE⟩ := exists_finiteDimensional_span_groupLike_eq_top hspanF
  let _ := hE
  let i : E →ₐ[k] AlgebraicClosure k := (IsScalarTower.toAlgHom k F _).comp E.val
  let _ : Algebra E (AlgebraicClosure k) := i.toRingHom.toAlgebra
  let _ : IsScalarTower k E (AlgebraicClosure k) := IsScalarTower.of_algHom i
  let _ : Algebra.IsSeparable k E := Algebra.isSeparable_tower_bot_of_isSeparable k E F
  let M : FiniteGaloisIntermediateField k (AlgebraicClosure k) :=
    { IntermediateField.normalClosure k E (AlgebraicClosure k) with
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  let _ : Algebra E M := inferInstanceAs
    (Algebra E (IntermediateField.normalClosure k E (AlgebraicClosure k)))
  let _ : IsScalarTower k E M := inferInstanceAs
    (IsScalarTower k E (IntermediateField.normalClosure k E (AlgebraicClosure k)))
  have hsplitE : DiagonalizableGroup.groupLikeSpannedProperty E
      (FiniteTypeCommHopfAlgCat.baseChange (K := E) H) :=
    (DiagonalizableGroup.groupLikeSpannedProperty_iff _ _).mpr
      (Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top.mpr hspanE)
  rw [← DiagonalizableGroup.essImage_coordinateRingFunctor E] at hsplitE
  obtain ⟨G, ⟨j⟩⟩ := hsplitE
  refine ⟨M, ?_⟩
  rw [← DiagonalizableGroup.essImage_coordinateRingFunctor M]
  refine ⟨G, ⟨?_⟩⟩
  exact ((DiagonalizableGroup.baseChangeCoordinateRingIso E M G).symm ≪≫
    (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := M)).mapIso j) ≪≫
    ObjectProperty.isoMk _ (CommHopfAlgCat.baseChangeTowerIso k M H.obj)

/-- A finite-type group of multiplicative type is reconstructed from its characters over
some finite Galois splitting field. The invariants use the simultaneous action on coefficients
and characters, and the comparison preserves the Hopf algebra structure. -/
theorem exists_finiteGalois_characterGroupAlgebraInvariantsEquiv
    (hH : multiplicativeTypeCommHopfAlgProperty k H) :
    ∃ L : FiniteGaloisIntermediateField k (AlgebraicClosure k),
      Nonempty (H ≃ₐc[k] GaloisDescent.groupAlgebraInvariants
        (Representation.ofMulDistribMulAction (L ≃ₐ[k] L)
          (GroupLike L (CommHopfAlgCat.baseChange (K := L) H.obj)))) := by
  obtain ⟨L, hspan⟩ := exists_finiteGalois_groupLikeSpanned_baseChange hH
  refine ⟨L, ⟨GaloisDescent.characterGroupAlgebraInvariantsEquiv k L H ?_⟩⟩
  exact Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top.mp
    ((DiagonalizableGroup.groupLikeSpannedProperty_iff L _).mp hspan)

end TauCeti.multiplicativeTypeCommHopfAlgProperty
