/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.FieldTheory.Perfect
public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Reconstruction
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Splitting
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange

/-!
# Finite Galois splitting for groups of multiplicative type

Over a perfect field, a finite algebraic splitting field for a group of multiplicative type
can be enlarged to its normal closure. The resulting finite Galois splitting field identifies
the original coordinate Hopf algebra with the invariant group algebra of its characters.

Perfectness is used to make the normal closure separable. Neither smoothness nor connectedness
is required of the group.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.multiplicativeTypeCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] [PerfectField k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- Over a perfect field, a finite-type group of multiplicative type becomes diagonalizable
over a finite Galois intermediate field of the algebraic closure. -/
theorem exists_finiteGalois_groupLikeSpanned_baseChange
    (hH : multiplicativeTypeCommHopfAlgProperty k H) :
    ∃ L : FiniteGaloisIntermediateField k (AlgebraicClosure k),
      DiagonalizableGroup.groupLikeSpannedProperty L
        (FiniteTypeCommHopfAlgCat.baseChange (K := L) H) := by
  obtain ⟨L, hL, hspan⟩ := exists_finiteDimensional_groupLikeSpanned_baseChange hH
  let _ := hL
  let _ : IsGalois k (AlgebraicClosure k) := ⟨⟩
  let M : FiniteGaloisIntermediateField k (AlgebraicClosure k) :=
    { IntermediateField.normalClosure k L (AlgebraicClosure k) with
      finiteDimensional := inferInstance
      isGalois := IsGalois.normalClosure k L (AlgebraicClosure k) }
  have hLM : L ≤ M.toIntermediateField := IntermediateField.le_normalClosure L
  let _ : Algebra L M := (IntermediateField.inclusion hLM).toRingHom.toAlgebra
  let _ : IsScalarTower k L M := IsScalarTower.of_algHom (IntermediateField.inclusion hLM)
  rw [← DiagonalizableGroup.essImage_coordinateRingFunctor L] at hspan
  obtain ⟨G, ⟨i⟩⟩ := hspan
  refine ⟨M, ?_⟩
  rw [← DiagonalizableGroup.essImage_coordinateRingFunctor M]
  refine ⟨G, ⟨?_⟩⟩
  exact ((DiagonalizableGroup.baseChangeCoordinateRingIso L M G).symm ≪≫
    (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := M)).mapIso i) ≪≫
    ObjectProperty.isoMk _ (CommHopfAlgCat.baseChangeTowerIso k M H.obj)

/-- A finite-type group of multiplicative type over a perfect field is reconstructed from
its characters over some finite Galois splitting field. The invariants use the simultaneous
action on coefficients and characters, and the comparison preserves the Hopf algebra structure. -/
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
