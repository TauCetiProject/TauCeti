/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.LinearlyReductive
public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
public import TauCeti.Algebra.Coalgebra.Comodule.Weight.CompletelyReducible
import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.Algebra.Coalgebra.Basic
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite

/-!
# Connected solvable linearly reductive groups are tori

Over an algebraically closed field, a reduced connected affine group of finite type with
solvable points is linearly reductive if and only if it is a torus, in every characteristic.
This isolates the solvable case of the classification of smooth connected linearly reductive
groups in positive characteristic.

Lie--Kolchin supplies a weight vector in each nonzero finite-dimensional subrepresentation.
Complete reducibility makes their weight spaces span. Applying this to finite-dimensional
subcomodules of the regular representation shows that group-like elements span the coordinate
Hopf algebra, so the group is diagonalizable. Reducedness and connectedness then make it a torus.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.12, §12.l and §16.a.
* T. A. Springer, *Linear Algebraic Groups*, Theorem 6.3.1.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti

universe u v

namespace HopfAlgebra

variable (k : Type u) (H : Type v) [Field k] [CommRing H] [HopfAlgebra k H]
variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
variable [ConnectedSpace (PrimeSpectrum H)] [Group.IsSolvable (WithConv (H →ₐ[k] k))]

/-- The coordinate Hopf algebra of a reduced connected solvable linearly reductive affine
group over an algebraically closed field is spanned by its group-like elements. -/
theorem groupLikeSetSpan_eq_top_of_isLinearlyReductive_of_isSolvable
    (hlr : Coalgebra.IsLinearlyReductive.{u, v, u} k H) :
    Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ = ⊤ := by
  rw [Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top]
  refine eq_top_iff.mpr fun h _ ↦ ?_
  obtain ⟨N, hNfin, hN⟩ := Subcomodule.exists_finite_subcomodule_mem (R := k) (C := H) h
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  -- A subcomodule and its underlying submodule subtype the same carrier.
  have _ : Module.Finite k N := hNfin
  have hweights : ⨆ g : GroupLike k H, _root_.GroupLike.weightSpace (M := N) g = ⊤ := by
    apply Comodule.iSup_groupLikeWeightSpace_eq_top_of_isCompletelyReducible (M := N)
      hlr.isCompletelyReducible
    intro Q hQ
    let _ : AddCommGroup Q := Module.addCommMonoidToAddCommGroup k
    have _ : Module.Finite k Q := Q.finite
    have _ : Nontrivial Q := (Submodule.nontrivial_iff_ne_bot (p := Q.toSubmodule)).mpr
      (mt Subcomodule.toSubmodule_eq_bot.mp hQ)
    exact Comodule.hasNonzeroWeightVector_of_isSolvable (k := k) (H := H) (M := Q)
  -- A weight vector in the regular representation is a counit multiple of its character.
  have hle : (⨆ g : GroupLike k H, _root_.GroupLike.weightSpace (M := N) g) ≤
      (Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := H)))).comap
        (N.subtype.toLinearMap) := by
    refine iSup_le fun g ↦ ?_
    intro n hn
    have hw := N.subtype.map_mem_groupLikeWeightSpace hn
    rw [_root_.GroupLike.mem_weightSpace, Comodule.instSelf_coact] at hw
    have hmem : N.subtype n ∈
        Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := H))) := by
      rw [Coalgebra.eq_counit_smul_of_comul_eq_tmul hw]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self g))
    simpa only [Submodule.mem_comap, Comodule.Hom.coe_toLinearMap] using hmem
  have hmem := hle (hweights ▸ (Submodule.mem_top : (⟨h, hN⟩ : N) ∈ ⊤))
  simpa only [Submodule.mem_comap, Subcomodule.subtype_toLinearMap,
    SMulMemClass.subtype_apply] using hmem

end HopfAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (H : FiniteTypeCommHopfAlgCat.{u, u} k)
variable [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
variable [Group.IsSolvable (WithConv (H →ₐ[k] k))]

open torusCommHopfAlgProperty

/-- A reduced connected solvable linearly reductive affine group of finite type over an
algebraically closed field is a torus. Smoothness follows from the conclusion. -/
theorem torusCommHopfAlgProperty_of_isLinearlyReductive_of_isSolvable
    (hlr : linearlyReductiveCommHopfAlgProperty k H.obj) :
    torusCommHopfAlgProperty k H := by
  have hdiag : DiagonalizableGroup.groupLikeSpannedProperty k H :=
    (DiagonalizableGroup.groupLikeSpannedProperty_iff k H).mpr
      (HopfAlgebra.groupLikeSetSpan_eq_top_of_isLinearlyReductive_of_isSolvable k H
        ((linearlyReductiveCommHopfAlgProperty_iff k H.obj).mp hlr))
  rw [← DiagonalizableGroup.essImage_coordinateRingFunctor] at hdiag
  obtain ⟨G, ⟨i⟩⟩ := hdiag
  apply (iff_multiplicativeType_and_geometricallyConnected_and_geometricallyReduced
    k H).mpr
  exact ⟨(multiplicativeTypeCommHopfAlgProperty k).prop_of_iso i
      (DiagonalizableGroup.multiplicativeType_coordinateRing k G),
    (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k H.obj).mpr inferInstance,
    (geometricallyReducedCommHopfAlgProperty_iff_isReduced_of_isAlgClosed k H.obj).mpr
      inferInstance⟩

/-- Among reduced connected solvable affine groups of finite type over an algebraically closed
field, linear reductivity is equivalent to being a torus, in every characteristic. -/
theorem linearlyReductiveCommHopfAlgProperty_iff_torus_of_isSolvable :
    linearlyReductiveCommHopfAlgProperty k H.obj ↔ torusCommHopfAlgProperty k H :=
  ⟨torusCommHopfAlgProperty_of_isLinearlyReductive_of_isSolvable H,
    torusCommHopfAlgProperty.linearlyReductive⟩

end TauCeti
