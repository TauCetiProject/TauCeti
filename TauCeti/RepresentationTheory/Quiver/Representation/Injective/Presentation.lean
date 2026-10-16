/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional
import TauCeti.Algebra.Category.ModuleCat.Injective.FiniteDimensional

/-!
# Injective presentations of finite-dimensional quiver representations

For a quiver with finitely many paths, every pointwise finite-dimensional representation
embeds into a pointwise finite-dimensional ambient injective. Consequently the
finite-dimensional full subcategory has enough injectives, and its injective objects
are exactly the ambient injective representations belonging to it.

These presentations keep injective extension arguments and the left almost-split
construction inside the finite-dimensional category. Together with finite projective
presentations, they provide both sides of the homological structure used by
Auslander–Reiten duality.

The construction transports `ModuleCat.exists_injectivePresentation_of_finite` along
`quiverRepEquivalence`. No algebraic closedness assumption is needed.

This construction dualizes the formalization in
`TauCeti.RepresentationTheory.Quiver.Representation.Projective.Presentation`, specifically
`TauCeti.QuiverRep.exists_projectivePresentation_of_isFinDim`,
`TauCeti.QuiverRep.enoughProjectives_isFinDim`, and
`CategoryTheory.ObjectProperty.FullSubcategory.projective_iff_projective_obj_of_finite_paths`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Sections I.2 and V.1.
-/

public section

open TauCeti CategoryTheory
open scoped ModuleCat.Algebra

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
  [Finite (Quiver.TotalPath Q)] [Small.{t} (pathAlgebra k Q)]

namespace TauCeti.QuiverRep

/-- A finite-dimensional representation of a quiver with finitely many paths has an
ambient injective presentation whose target remains finite-dimensional. Smallness lets
the target stay in the universe of the given representation. -/
theorem exists_injectivePresentation_of_isFinDim (M : QuiverRep.{u, v, w, t} k Q)
    (hM : IsFinDim k Q M) :
    ∃ I : InjectivePresentation M, IsFinDim k Q I.J := by
  let A := pathAlgebra k Q
  let E := quiverRepEquivalence.{u, v, w, t} k Q
  have : Module.Finite k A := module_finite_pathAlgebra k Q
  have : Module.Finite k (E.functor.obj M) :=
    module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  have : Module.Finite A (E.functor.obj M) :=
    Module.Finite.of_restrictScalars_finite k A _
  obtain ⟨I, hI⟩ := ModuleCat.exists_injectivePresentation_of_finite k (E.functor.obj M)
  have : Module.Finite k I.J := Module.Finite.trans A I.J
  refine ⟨E.injectivePresentationOfMapInjectivePresentation M I, ?_⟩
  simpa only [Equivalence.injectivePresentationOfMapInjectivePresentation,
    Adjunction.injectivePresentationOfMap, E, quiverRepEquivalence_inverse] using
    isFinDim_quiverRepFunctor_obj k Q I.J inferInstance

/-- The finite-dimensional category of representations of a quiver with finitely many
paths has enough injectives. -/
instance enoughInjectives_isFinDim :
    EnoughInjectives (ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q)) where
  presentation M := by
    obtain ⟨I, hI⟩ := exists_injectivePresentation_of_isFinDim M.obj M.property
    let V : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q) := ⟨I.J, hI⟩
    let F := ObjectProperty.ι (IsFinDim.{u, v, w, t} k Q)
    exact ⟨{
      J := V
      injective := F.injective_of_map_injective I.injective
      f := ObjectProperty.homMk I.f
      mono := F.mono_of_mono_map I.mono }⟩

end TauCeti.QuiverRep

namespace CategoryTheory.ObjectProperty.FullSubcategory

/-- Injectivity in the finite-dimensional category agrees with ambient injectivity for
a quiver with finitely many paths. -/
@[simp]
theorem injective_iff_injective_obj_of_finite_paths
    (M : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q)) :
    Injective M ↔ Injective M.obj := by
  let F := ObjectProperty.ι (IsFinDim.{u, v, w, t} k Q)
  refine ⟨fun hM ↦ ?_, fun hM ↦ F.injective_of_map_injective hM⟩
  have := hM
  obtain ⟨I, hI⟩ := QuiverRep.exists_injectivePresentation_of_isFinDim M.obj M.property
  let V : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q) := ⟨I.J, hI⟩
  let f : M ⟶ V := ObjectProperty.homMk I.f
  have : Mono f := F.mono_of_mono_map I.mono
  let s := Injective.factorThru (𝟙 M) f
  let r : Retract M.obj I.J :=
    { i := I.f
      r := s.hom
      retract := congrArg InducedCategory.Hom.hom (Injective.comp_factorThru (𝟙 M) f) }
  exact r.injective

end CategoryTheory.ObjectProperty.FullSubcategory
