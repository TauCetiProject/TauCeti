/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Classification
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Module
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# The vertex projectives of an acyclic quiver as path-algebra modules

Over an acyclic quiver with finitely many vertices, the vertex projectives `Pᵢ` are
indecomposable, pairwise nonisomorphic, and every finite-dimensional indecomposable projective
representation is one of them (`TauCeti.indecomposable_indecProjRep_of_isAcyclic`,
`TauCeti.not_nonempty_indecProjRep_iso_of_isAcyclic`,
`TauCeti.existsUnique_iso_indecProjRep_of_projective`). This file transports those three facts
along the equivalence `TauCeti.quiverRepFunctor` to the path-algebra modules
`TauCeti.indecProjModule`, stating them in module-theoretic language: indecomposability as
`IsIndecomposableModule`, and isomorphism as a `kQ`-linear equivalence.

These are the hypotheses under which the classes `[Pᵢ]` form a basis of the Grothendieck group of
finitely generated projective `kQ`-modules, indexed by the vertices.

## Main results

* `TauCeti.finrank_end_indecProjModule_of_isAcyclic`: `Pᵢ` is a brick, `dim End(Pᵢ) = 1`.
* `TauCeti.isIndecomposableModule_indecProjModule`: `Pᵢ` is an indecomposable module.
* `TauCeti.isEmpty_linearEquiv_indecProjModule`: `Pᵢ` and `Pⱼ` are not isomorphic for `i ≠ j`.
* `TauCeti.exists_linearEquiv_indecProjModule`: every finite-dimensional indecomposable projective
  `kQ`-module is isomorphic to some `Pᵢ`.

## References

* I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter III, Section 2.
-/

public section

namespace TauCeti

open CategoryTheory
open scoped ModuleCat

universe u v w

section General

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q] [Finite Q]

/-- Over an acyclic quiver the vertex projective `Pᵢ` is a brick: the morphisms `Pᵢ ⟶ Pᵢ` are the
`i`th vertex space of `Pᵢ`, spanned by the trivial path. -/
theorem finrank_end_indecProjModule_of_isAcyclic (hQ : Quiver.IsAcyclic Q) (i : Q) :
    Module.finrank k (indecProjModule k Q i ⟶ indecProjModule k Q i) = 1 := by
  rw [finrank_hom_indecProjModule, dimVector_eq_of_iso (indecProjModuleIso k Q i),
    dimVector_indecProjRep, hQ.card_path_self]

/-- **The vertex projective `Pᵢ` of an acyclic quiver is an indecomposable `kQ`-module.** -/
theorem isIndecomposableModule_indecProjModule (hQ : Quiver.IsAcyclic Q) (i : Q) :
    IsIndecomposableModule (pathAlgebra k Q) (indecProjModule k Q i) :=
  (indecomposable_iff_isIndecomposableModule _).mp
    (indecomposable_of_finrank_end_eq_one (finrank_end_indecProjModule_of_isAcyclic hQ i))

/-- **The vertex projectives of an acyclic quiver at distinct vertices are not isomorphic** as
`kQ`-modules. -/
theorem isEmpty_linearEquiv_indecProjModule (hQ : Quiver.IsAcyclic Q) {i j : Q} (hij : i ≠ j) :
    IsEmpty (indecProjModule k Q i ≃ₗ[pathAlgebra k Q] indecProjModule k Q j) :=
  ⟨fun e ↦ not_nonempty_indecProjRep_iso_of_isAcyclic hQ hij
    ⟨(indecProjModuleIso k Q i).symm ≪≫ (quiverRepFunctor k Q).mapIso e.toModuleIso ≪≫
      indecProjModuleIso k Q j⟩⟩

end General

variable {k : Type (max v w)} {Q : Type v} [Field k] [Quiver.{w} Q] [Finite Q]

/-- **The vertex projectives exhaust the indecomposable projective `kQ`-modules**: over an acyclic
quiver with finitely many vertices, every finite-dimensional indecomposable projective `kQ`-module
is isomorphic to some vertex projective `Pᵢ`. -/
theorem exists_linearEquiv_indecProjModule (hQ : Quiver.IsAcyclic Q)
    (M : ModuleCat.{max v w} (pathAlgebra k Q)) [FiniteDimensional k M]
    [Module.Projective (pathAlgebra k Q) M] (hM : IsIndecomposableModule (pathAlgebra k Q) M) :
    ∃ i, Nonempty (M ≃ₗ[pathAlgebra k Q] indecProjModule k Q i) := by
  have hind : Indecomposable ((quiverRepFunctor k Q).obj M) :=
    (quiverRepFunctor k Q).indecomposable_obj_of_map_bijective
      ((indecomposable_iff_isIndecomposableModule M).mpr hM)
      ((quiverRepFunctorFullyFaithful k Q).map_bijective M M)
  have : Projective M := ModuleCat.projective_of_categoryTheory_projective M
  have : Projective ((quiverRepFunctor k Q).obj M) := (quiverRepFunctor k Q).projective_obj M
  obtain ⟨i, ⟨e⟩, -⟩ := existsUnique_iso_indecProjRep_of_projective hQ _
    (isFinDim_quiverRepFunctor_obj k Q M inferInstance) hind
  exact ⟨i, ⟨((quiverRepFunctorFullyFaithful k Q).preimageIso
    (e ≪≫ (indecProjModuleIso k Q i).symm)).toLinearEquiv⟩⟩

end TauCeti
