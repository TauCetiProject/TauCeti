/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.LieStable
public import TauCeti.Algebra.AlgebraicGroup.Representation.TriangularEmbedding
public import TauCeti.Algebra.AlgebraicGroup.Solvable.UpperTriangular
public import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.LieTheorem
import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Solvable.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType

/-!
# Solvable groups from solvable Lie algebras

Over an algebraically closed field of characteristic zero, a connected affine group of
finite type with solvable Lie algebra is solvable. More precisely, every finite-dimensional
representation admits an upper-triangular basis, and the group embeds as a closed subgroup
of an upper-triangular general linear group.

Lie's theorem gives a common eigenline for the differentiated representation. For connected
groups in characteristic zero, Lie-stable subspaces are subcomodules, so this eigenline is
a group weight line. Applying the same argument to successive quotients gives a full flag.
A finite-dimensional coefficient-generating representation then supplies the closed embedding.
In particular the points over every commutative value algebra form a solvable group, including
value algebras with nilpotents. Over an arbitrary characteristic-zero field, a geometrically
connected group with solvable Lie algebra is geometrically solvable, by scalar extension.

This criterion allows solvability of a connected closed subgroup to be established from its
Lie algebra, as needed when comparing group radicals with Lie-algebra radicals. Connectedness
is essential: finite groups in characteristic zero have zero Lie algebra.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 10, solvability and Lie algebras.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.
* The eigenline argument uses Mathlib's
  `LieModule.exists_nontrivial_weightSpace_of_isSolvable`; integration of the eigenline uses
  `Submodule.exists_subcomodule_iff_forall_differential_mem`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u w

noncomputable section

section AlgebraicallyClosed

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} [ConnectedSpace (PrimeSpectrum H)]
variable [LieAlgebra.IsSolvable (Derivation k H (Bialgebra.CounitAlgebra k H k))]

namespace Comodule

/-- A nonzero finite-dimensional representation of a connected group with solvable Lie algebra
has a nonzero weight vector, over an algebraically closed field of characteristic zero. -/
theorem hasNonzeroWeightVector_of_isSolvable_lie
    {M : Type w} [AddCommGroup M] [Module k M] [Comodule k H M]
    [FiniteDimensional k M] [Nontrivial M] : HasNonzeroWeightVector k H M := by
  let _ : LieRing (Module.End k M) := LieRing.ofAssociativeRing
  let _ : LieRingModule (Derivation k H (Bialgebra.CounitAlgebra k H k)) M :=
    LieRingModule.compLieHom M (differential (R := k) (H := H) (M := M))
  let _ : LieModule k (Derivation k H (Bialgebra.CounitAlgebra k H k)) M :=
    LieModule.compLieHom M (differential (R := k) (H := H) (M := M))
  obtain ⟨χ, hχ⟩ := LieModule.exists_nontrivial_weightSpace_of_isSolvable k
    (Derivation k H (Bialgebra.CounitAlgebra k H k)) M
  let _ := hχ
  obtain ⟨v, hv⟩ := exists_ne (0 : LieModule.weightSpace M χ)
  have hv0 : (v : M) ≠ 0 := Subtype.coe_ne_coe.mpr hv
  have hstable : ∀ d : Derivation k H (Bialgebra.CounitAlgebra k H k),
      ∀ m ∈ k ∙ (v : M), differential (R := k) (H := H) (M := M) d m ∈ k ∙ (v : M) := by
    intro d m hm
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hm
    have heigen := (LieModule.mem_weightSpace χ (v : M)).mp v.property d
    have hlie : ⁅d, (v : M)⁆ = differential (R := k) (H := H) (M := M) d v := by
      rw [LieRingModule.compLieHom_apply, Module.End.lie_apply]
    rw [map_smul, ← hlie, heigen]
    exact Submodule.smul_mem _ _
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self (v : M)))
  obtain ⟨N, hN⟩ := (Submodule.exists_subcomodule_iff_forall_differential_mem
    (H := H) (k ∙ (v : M))).mpr hstable
  exact hasNonzeroWeightVector_of_toSubmodule_eq_span N hv0 hN

/-- Every finite-dimensional representation of a connected group with solvable Lie algebra
is upper triangularizable in characteristic zero over an algebraically closed field. -/
theorem exists_basis_coefficientMatrix_isUpperTriangular_of_isSolvable_lie
    {M : Type w} [AddCommGroup M] [Module k M] [Comodule k H M]
    [FiniteDimensional k M] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k M),
      (coefficientMatrix (C := H) b).IsUpperTriangular ∧
        ∀ i, IsGroupLikeElem k (coefficientMatrix (C := H) b i i) :=
  exists_basis_coefficientMatrix_isUpperTriangular_of_weight_vectors
    fun _ _ _ _ _ _ ↦ hasNonzeroWeightVector_of_isSolvable_lie

end Comodule

/-- A connected affine group with solvable Lie algebra is a closed subgroup of an
upper-triangular general linear group, in characteristic zero over an algebraically closed field.
The surjection is in the contravariant coordinate direction. -/
theorem exists_upperTriangular_surjective_of_isSolvable_lie :
    ∃ (n : ℕ) (f : GeneralLinear.UpperTriangular.coordinateHopfAlgebra k n ⟶ H.obj),
      Function.Surjective f.hom :=
  exists_upperTriangular_surjective_of_weight_vectors fun _ _ _ _ _ _ ↦
    Comodule.hasNonzeroWeightVector_of_isSolvable_lie

/-- Every commutative-algebra-valued point group of a connected affine group with solvable
Lie algebra is solvable, in characteristic zero over an algebraically closed field. -/
theorem isSolvable_points_of_isSolvable_lie (A : Type w) [CommRing A] [Algebra k A] :
    Group.IsSolvable (WithConv (H →ₐ[k] A)) := by
  obtain ⟨n, f, hf⟩ := exists_upperTriangular_surjective_of_isSolvable_lie (H := H)
  let _ := GeneralLinear.UpperTriangular.isSolvable_points k A n
  exact Group.isSolvable_of_isSolvable_injective
    (f := BialgHom.mapDomain (A := A) f.hom)
    (CommHopfAlgCat.Hom.mapPointsFunctor_app_injective_of_surjective f hf (CommAlgCat.of k A))

/-- A connected affine group with solvable Lie algebra is geometrically solvable, in
characteristic zero over an algebraically closed field. -/
theorem geometricallySolvablePointsCommHopfAlgProperty.of_isSolvable_lie :
    geometricallySolvablePointsCommHopfAlgProperty k H.obj := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff]
  exact isSolvable_points_of_isSolvable_lie (AlgebraicClosure k)

end AlgebraicallyClosed

/-- Over any field of characteristic zero, a geometrically connected affine group of finite
type with solvable Lie algebra is geometrically solvable. -/
theorem geometricallySolvablePointsCommHopfAlgProperty.of_geometricallyConnected_of_isSolvable_lie
    {k : Type u} [Field k] [CharZero k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    [LieAlgebra.IsSolvable (Derivation k H (Bialgebra.CounitAlgebra k H k))]
    (hH : geometricallyConnectedCommHopfAlgProperty k H.obj) :
    geometricallySolvablePointsCommHopfAlgProperty k H.obj := by
  let K := AlgebraicClosure k
  let HK := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  let _ : ConnectedSpace (PrimeSpectrum HK) := hH.connectedSpace_algebraicClosureBaseChange
  let _ : LieAlgebra.IsSolvable (Module.Dual k (Bialgebra.CotangentSpace k H)) :=
    (LieAlgebra.solvable_iff_equiv_solvable Derivation.cotangentDualLieEquiv).mpr
      inferInstance
  let e := Derivation.tangentScalarExtensionLieEquiv.trans
    (tangentBaseChangeLieEquiv (R := k) (K := K) (H := H))
  let _ : LieAlgebra.IsSolvable
      (Derivation K HK (Bialgebra.CounitAlgebra K HK K)) :=
    (LieAlgebra.solvable_iff_equiv_solvable e).mp inferInstance
  exact geometricallySolvablePointsCommHopfAlgProperty.of_baseChange H.obj
    (geometricallySolvablePointsCommHopfAlgProperty.of_isSolvable_lie (H := HK))

end

end TauCeti
