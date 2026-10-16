/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional
import TauCeti.Algebra.Category.FGModuleCat.Projective

/-!
# Projective presentations of finite-dimensional quiver representations

When the quiver has finitely many paths, every pointwise finite-dimensional representation
admits an epimorphism from a pointwise finite-dimensional ambient projective. Consequently,
the finite-dimensional full subcategory has enough projectives, and its projective objects
are exactly the ambient projective representations that belong to it.

These presentations allow almost-split factorization properties in the finite-dimensional
category to be tested against projective epimorphisms without leaving that category.

The construction uses `quiverRepEquivalence` and Mathlib's `ProjectivePresentation`, transporting
the finite projective presentations of `FGModuleCat` to quiver representations.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Sections I.2 and V.1.
-/

public section

open TauCeti CategoryTheory
open scoped ModuleCat.Algebra

section

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
  [Finite (Quiver.TotalPath Q)]

variable [Small.{t} (pathAlgebra k Q)]

namespace TauCeti.QuiverRep

/-- A finite-dimensional representation of a quiver with finitely many paths admits an
ambient projective presentation whose source remains finite-dimensional. The smallness
hypothesis allows the source to stay in the universe of the given representation. -/
theorem exists_projectivePresentation_of_isFinDim (M : QuiverRep.{u, v, w, t} k Q)
    (hM : IsFinDim k Q M) :
    ∃ P : ProjectivePresentation M, IsFinDim k Q P.p := by
  classical
  let A := pathAlgebra k Q
  let E := quiverRepEquivalence.{u, v, w, t} k Q
  have : Module.Finite k A := module_finite_pathAlgebra k Q
  have : Module.Finite k (E.functor.obj M) :=
    module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  have : Module.Finite A (E.functor.obj M) :=
    Module.Finite.of_restrictScalars_finite k A _
  let N : FGModuleCat.{t} A := FGModuleCat.of A (E.functor.obj M)
  let F := forget₂ (FGModuleCat.{t} A) (ModuleCat.{t} A)
  let V := Projective.over N
  have : Module.Projective A V := FGModuleCat.moduleProjective_of_projective V
  have : Module.Finite k V.obj := Module.Finite.trans A V
  let P : ProjectivePresentation (E.functor.obj M) :=
    { p := V.obj
      f := F.map (Projective.π N) }
  refine ⟨E.projectivePresentationOfMapProjectivePresentation M P, ?_⟩
  simpa only [Equivalence.projectivePresentationOfMapProjectivePresentation,
    E, P, quiverRepEquivalence_inverse] using
    isFinDim_quiverRepFunctor_obj k Q V.obj inferInstance

/-- The finite-dimensional category of representations of a quiver with finitely many paths
has enough projectives. -/
instance enoughProjectives_isFinDim :
    EnoughProjectives (ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q)) where
  presentation M := by
    obtain ⟨P, hP⟩ := exists_projectivePresentation_of_isFinDim M.obj M.property
    let V : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q) := ⟨P.p, hP⟩
    let F := ObjectProperty.ι (IsFinDim.{u, v, w, t} k Q)
    exact ⟨{
      p := V
      projective := F.projective_of_map_projective P.projective
      f := ObjectProperty.homMk P.f
      epi := F.epi_of_epi_map P.epi }⟩

end TauCeti.QuiverRep

namespace CategoryTheory.ObjectProperty.FullSubcategory

/-- Projectivity in the finite-dimensional category agrees with ambient projectivity for
a quiver with finitely many paths. -/
@[simp]
theorem projective_iff_projective_obj_of_finite_paths
    (M : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q)) :
    Projective M ↔ Projective M.obj := by
  let F := ObjectProperty.ι (IsFinDim.{u, v, w, t} k Q)
  refine ⟨fun hM ↦ ?_, fun hM ↦ F.projective_of_map_projective hM⟩
  have := hM
  obtain ⟨P, hP⟩ := QuiverRep.exists_projectivePresentation_of_isFinDim M.obj M.property
  let V : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q) := ⟨P.p, hP⟩
  let f : V ⟶ M := ObjectProperty.homMk P.f
  have : Epi f := F.epi_of_epi_map P.epi
  let s := Projective.factorThru (𝟙 M) f
  let r : Retract M.obj P.p :=
    { i := s.hom
      r := P.f
      retract := congrArg InducedCategory.Hom.hom (Projective.factorThru_comp (𝟙 M) f) }
  exact r.projective

end CategoryTheory.ObjectProperty.FullSubcategory

end
