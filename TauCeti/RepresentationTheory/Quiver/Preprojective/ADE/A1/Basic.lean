/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Admissible
public import TauCeti.RepresentationTheory.Quiver.AdmissibleIdeal
public import TauCeti.RepresentationTheory.Quiver.SemisimpleQuotient
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.SimpleGraph
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation

/-!
# The preprojective algebra of `A₁`

The one-vertex Dynkin quiver has no arrows. Its doubled path algebra has only the trivial path,
and the preprojective relation ideal is zero. Thus its preprojective algebra is one-dimensional
and the relation ideal is admissible. This is the rank-one case of finite-dimensionality for
finite ADE preprojective algebras.

The convention for this preprojective algebra differs from the zigzag algebra of `A₁`, which is
instead the dual numbers. See Crawley-Boevey, *Quiver algebras, weighted projective lines, and the
Deligne--Simpson problem*, Section 1, for the preprojective presentation.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

/-- The one-vertex Dynkin diagram, with no edges. -/
abbrev preprojectiveA1Graph : SimpleGraph (Fin 1) := ⊥

/-- The one-vertex graph is the Bourbaki-numbered `A₁` Dynkin diagram. -/
theorem preprojectiveA1Graph_eq_diagramGraph_cartanMatrix :
    preprojectiveA1Graph = diagramGraph (DynkinType.A 1).cartanMatrix := by
  ext i j
  fin_cases i; fin_cases j
  simp

/-- The source-to-sink orientation of the one-vertex Dynkin diagram. -/
abbrev preprojectiveA1Quiver := OrientedQuiver preprojectiveA1Graph
  (Orientation.ofLinearOrder preprojectiveA1Graph)

/-- There are no arrows in the `A₁` quiver. -/
instance (i j : preprojectiveA1Quiver) : IsEmpty (i ⟶ j) := by
  constructor
  intro e
  simpa [preprojectiveA1Graph] using e.1

/-- The doubled `A₁` quiver also has no arrows. -/
instance (i j : Symmetrify preprojectiveA1Quiver) : IsEmpty (i ⟶ j) := by
  -- The symmetrification is a type synonym, and its arrow type is a sum.
  change IsEmpty (((show preprojectiveA1Quiver from i) ⟶
    (show preprojectiveA1Quiver from j)) ⊕
    ((show preprojectiveA1Quiver from j) ⟶ (show preprojectiveA1Quiver from i)))
  infer_instance

/-- The doubled `A₁` quiver is acyclic. -/
theorem isAcyclic_symmetrify_preprojectiveA1Quiver :
    Quiver.IsAcyclic (Symmetrify preprojectiveA1Quiver) :=
  Quiver.IsAcyclic.of_isEmpty_hom

/-- Finite enumeration of vertices in the one-vertex orientation. -/
noncomputable instance instFintypePreprojectiveA1Quiver :
    Fintype preprojectiveA1Quiver := Fintype.ofFinite _

/-- Finite enumeration of arrows in the one-vertex orientation. -/
noncomputable instance instFintypePreprojectiveA1QuiverHom (i j : preprojectiveA1Quiver) :
    Fintype (i ⟶ j) := Fintype.ofFinite _

/-- The doubled `A₁` path algebra has no arrow ideal. -/
@[simp]
theorem arrowIdeal_preprojectiveA1_eq_bot (k : Type*) [CommRing k] :
    arrowIdeal k (Symmetrify preprojectiveA1Quiver) = ⊥ := by
  rw [arrowIdeal_eq_span_arrows, Set.range_eq_empty, Ideal.span_empty]

/-- The relation ideal of the rank-one preprojective algebra is zero: there are no arrows from
which to form local backtracks. -/
@[simp]
theorem preprojectiveIdeal_A1_eq_bot (k : Type*) [CommRing k] :
    (preprojectiveIdeal k preprojectiveA1Quiver).asIdeal = ⊥ := by
  apply le_antisymm
  · have h := preprojectiveIdeal_le_arrowIdeal_sq (k := k) (Q := preprojectiveA1Quiver)
    simpa [arrowIdeal_preprojectiveA1_eq_bot] using h
  · exact bot_le

/-- The relation ideal of `A₁` is admissible: in fact, both it and the arrow ideal vanish. -/
theorem isAdmissibleIdeal_preprojectiveIdeal_A1 (k : Type*) [CommRing k] :
    IsAdmissibleIdeal (preprojectiveIdeal k preprojectiveA1Quiver).asIdeal := by
  simpa only [preprojectiveIdeal_A1_eq_bot] using
    (isAdmissibleIdeal_bot_of_isAcyclic k _
      isAcyclic_symmetrify_preprojectiveA1Quiver)

/-- The preprojective algebra of `A₁` is finite-dimensional over every field. -/
noncomputable instance instFiniteDimensionalPreprojectiveAlgebraA1 (k : Type*) [Field k] :
    FiniteDimensional k (preprojectiveAlgebra k preprojectiveA1Quiver) :=
  (isAdmissibleIdeal_preprojectiveIdeal_A1 k).finiteDimensional_quotient

private noncomputable def vertices : Fin 1 ≃ Symmetrify preprojectiveA1Quiver :=
  (OrientedQuiver.vertexEquiv _ _).trans
    (Equiv.ofBijective _ symmetrify_of_obj_bijective)

/-- The doubled `A₁` quiver has exactly one path, its vertex path. -/
@[simp]
theorem card_totalPath_preprojectiveA1 :
    Nat.card (Quiver.TotalPath (Symmetrify preprojectiveA1Quiver)) = 1 := by
  let v : Symmetrify preprojectiveA1Quiver :=
    Symmetrify.of.obj (OrientedQuiver.vertex preprojectiveA1Graph
      (Orientation.ofLinearOrder preprojectiveA1Graph) 0)
  let : Subsingleton (Symmetrify preprojectiveA1Quiver) :=
    Equiv.subsingleton.symm vertices
  have hvertex (x : Symmetrify preprojectiveA1Quiver) : x = v :=
    Subsingleton.elim _ _
  have hpath (x : Quiver.TotalPath (Symmetrify preprojectiveA1Quiver)) :
      x = ⟨v, v, Path.nil⟩ := by
    rcases x with ⟨a, b, p⟩
    obtain rfl := hvertex a
    obtain rfl := hvertex b
    exact congrArg (fun q : Path v v => (⟨v, v, q⟩ : Quiver.TotalPath _))
      (isAcyclic_symmetrify_preprojectiveA1Quiver.eq_nil p)
  let : Unique (Quiver.TotalPath (Symmetrify preprojectiveA1Quiver)) :=
    { default := ⟨v, v, Path.nil⟩
      uniq := hpath }
  exact Nat.card_unique

/-- The rank-one preprojective algebra has dimension one. -/
@[simp]
theorem finrank_preprojectiveAlgebra_A1 (k : Type*) [CommRing k]
    [StrongRankCondition k] :
    Module.finrank k (preprojectiveAlgebra k preprojectiveA1Quiver) = 1 := by
  have e : preprojectiveAlgebra k preprojectiveA1Quiver ≃ₐ[k]
      pathAlgebra k (Symmetrify preprojectiveA1Quiver) :=
    (Ideal.quotientEquivAlgOfEq k (preprojectiveIdeal_A1_eq_bot k)).trans
      (AlgEquiv.quotientBot k _)
  rw [e.toLinearEquiv.finrank_eq, finrank_pathAlgebra, card_totalPath_preprojectiveA1]

/-- The rank-one preprojective algebra is canonically the coefficient ring. -/
noncomputable def preprojectiveAlgebraEquivA1 (k : Type*) [CommRing k] :
    preprojectiveAlgebra k preprojectiveA1Quiver ≃ₐ[k] k :=
  letI : Unique (Symmetrify preprojectiveA1Quiver) := Equiv.unique vertices.symm
  (Ideal.quotientEquivAlgOfEq k (preprojectiveIdeal_A1_eq_bot k)).trans
    ((Ideal.quotientEquivAlgOfEq k (arrowIdeal_preprojectiveA1_eq_bot k).symm).trans
      ((quotientArrowIdealAlgEquiv k _).trans (AlgEquiv.funUnique k _ k)))

/-- The rank-one comparison reads the coefficient of the sole vertex path. -/
@[simp]
theorem preprojectiveAlgebraEquivA1_preprojectiveMk (k : Type*) [CommRing k]
    (x : pathAlgebra k (Symmetrify preprojectiveA1Quiver)) :
    preprojectiveAlgebraEquivA1 k (preprojectiveMk k preprojectiveA1Quiver x) =
      trivialCoeff k (Symmetrify preprojectiveA1Quiver) x
        (Symmetrify.of.obj (OrientedQuiver.vertex preprojectiveA1Graph
          (Orientation.ofLinearOrder preprojectiveA1Graph) 0)) := by
  let : Unique (Symmetrify preprojectiveA1Quiver) := Equiv.unique vertices.symm
  have hv : (default : Symmetrify preprojectiveA1Quiver) =
      Symmetrify.of.obj (OrientedQuiver.vertex preprojectiveA1Graph
        (Orientation.ofLinearOrder preprojectiveA1Graph) 0) := Subsingleton.elim _ _
  simp only [preprojectiveMk_apply, preprojectiveAlgebraEquivA1, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, quotientArrowIdealAlgEquiv_mk,
    AlgEquiv.funUnique_apply, Equiv.funUnique, Equiv.piUnique_apply, hv]

end TauCeti
