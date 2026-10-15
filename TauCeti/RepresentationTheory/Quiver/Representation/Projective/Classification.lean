/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Simple
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional
public import TauCeti.RepresentationTheory.Quiver.Representation.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Cover

/-!
# Classification of indecomposable projective quiver representations

For an acyclic quiver with finitely many vertices, every pointwise finite-dimensional
indecomposable projective representation is a vertex projective `Pᵢ`, at a unique vertex `i`.
The field is arbitrary and the arrow sets need not be finite.

Every nonzero finite-dimensional representation has a simple quotient, which acyclicity identifies
with a vertex simple `Sᵢ`. For a projective representation, the projective cover `Pᵢ ↠ Sᵢ` makes
`Pᵢ` a retract. Indecomposability forces this nonzero retract to be the whole representation.
This identifies the projective vertices that must be omitted from the domain of the
Auslander--Reiten translate.

## Main results

* `TauCeti.exists_epi_simpleRep_of_isFinDim`: a nonzero finite-dimensional representation has a
  vertex-simple quotient.
* `TauCeti.existsUnique_iso_indecProjRep_of_projective`: the vertex projectives exhaust the
  finite-dimensional indecomposable projectives, without repetition.
* `TauCeti.projective_iff_exists_iso_indecProjRep`: the corresponding projectivity criterion.

## References

I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
Algebras*, Vol. 1, Chapter III, Section 2.

## Implementation notes

The projective classification uses the coefficient universe `max v w` of the existing
vertex-projective cover API: in that universe `Pᵢ` and `Sᵢ` belong to the same representation
category. The simple-quotient theorem does not need this restriction.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat

universe u v w

section SimpleQuotient

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q] [Finite Q]

/-- Every nonzero pointwise finite-dimensional representation of a finite-vertex acyclic quiver
has a vertex-simple quotient. -/
theorem exists_epi_simpleRep_of_isFinDim (hQ : Quiver.IsAcyclic Q)
    (M : QuiverRep k Q) (hfin : IsFinDim k Q M) (hM : ¬ IsZero M) :
    ∃ i : Q, ∃ f : M ⟶ simpleRep k Q i, Epi f := by
  let E := quiverRepEquivalence k Q
  have : Module.Finite k (E.functor.obj M) :=
    module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hfin
  have : IsNoetherian (pathAlgebra k Q) (E.functor.obj M) :=
    isNoetherian_of_tower k inferInstance
  have hnonzero : ¬ IsZero (E.functor.obj M) := by
    intro hz
    apply hM
    rw [IsZero.iff_id_eq_zero] at hz ⊢
    exact E.functor.map_injective (by simpa using hz)
  obtain ⟨S, hS, f, hf⟩ := ModuleCat.exists_epi_simple (E.functor.obj M) hnonzero
  have := hS
  have := hf
  have : Simple (E.inverse.obj S) := simple_obj E.inverse S
  obtain ⟨i, ⟨e⟩⟩ := exists_iso_simpleRep_of_simple hQ (E.inverse.obj S)
  exact ⟨i, (E.unitIso.app M).hom ≫ E.inverse.map f ≫ e.hom, inferInstance⟩

end SimpleQuotient

variable {k : Type (max v w)} {Q : Type v} [Field k] [Quiver.{w} Q] [Finite Q]

/-- Every pointwise finite-dimensional indecomposable projective representation of a
finite-vertex acyclic quiver is the vertex projective at a unique vertex. -/
theorem existsUnique_iso_indecProjRep_of_projective (hQ : Quiver.IsAcyclic Q)
    (M : QuiverRep k Q) (hfin : IsFinDim k Q M) (hM : Indecomposable M) [Projective M] :
    ∃! i : Q, Nonempty (M ≅ indecProjRep k Q i) := by
  obtain ⟨i, f, hf⟩ := exists_epi_simpleRep_of_isFinDim hQ M hfin hM.1
  obtain ⟨g, -, hg⟩ :=
    exists_comp_indecProjRepToSimpleRep_eq_and_isSplitEpi k (fun p ↦ hQ.eq_nil p) f hf
  have := hg
  have hs : IsIso (section_ g) := isIso_of_isIso_comp
    (fun hz ↦ not_isZero_indecProjRep (k := k) i ((IsZero.iff_id_eq_zero _).mpr hz))
    (fun _ he ↦ idempotent_eq_zero_or_id_of_indecomposable hM he)
    (section_ g) g (by rw [IsSplitEpi.id]; infer_instance)
  have : IsIso g := isIso_of_hom_comp_eq_id (section_ g) (IsSplitEpi.id g)
  refine ⟨i, ⟨asIso g⟩, fun j hj ↦ ?_⟩
  obtain ⟨e⟩ := hj
  by_contra hji
  exact not_nonempty_indecProjRep_iso_of_isAcyclic hQ hji ⟨e.symm ≪≫ asIso g⟩

/-- A pointwise finite-dimensional indecomposable representation of a finite-vertex acyclic
quiver is projective exactly when it is isomorphic to a vertex projective. -/
theorem projective_iff_exists_iso_indecProjRep (hQ : Quiver.IsAcyclic Q)
    (M : QuiverRep k Q) (hfin : IsFinDim k Q M) (hM : Indecomposable M) :
    Projective M ↔ ∃ i : Q, Nonempty (M ≅ indecProjRep k Q i) := by
  constructor
  · intro h
    have := h
    exact (existsUnique_iso_indecProjRep_of_projective hQ M hfin hM).exists
  · rintro ⟨i, ⟨e⟩⟩
    exact Projective.of_iso e.symm inferInstance

end TauCeti
