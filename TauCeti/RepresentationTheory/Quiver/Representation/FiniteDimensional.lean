/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.ExtensionClosed
public import TauCeti.RepresentationTheory.Quiver.Representation.AsModule
public import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.LinearAlgebra.DirectSum.Finite

/-!
# Finite-dimensional quiver representations

A representation of a quiver is **pointwise finite-dimensional** when the vector space it puts at
every vertex is finite-dimensional. This file defines that property, `TauCeti.IsFinDim`, proves
that it transports along an isomorphism, equips its full subcategory with an exact structure,
proves essential smallness for a finite vertex set, and shows that a path algebra module
finite-dimensional over the base field gives such a representation.

## Main definitions

* `TauCeti.IsFinDim`: a representation is finite-dimensional at every vertex.

## Main results

* `TauCeti.IsFinDim.of_iso`: pointwise finite-dimensionality transports along an isomorphism.
* The full subcategory of `IsFinDim` representations is essentially small for finite `Q`.
* `TauCeti.module_finite_asModule_of_isFinDim`: a pointwise finite-dimensional representation
  gives a finite module over the path algebra when the vertex set is finite.
* `TauCeti.isFinDim_quiverRepFunctor_obj`: finite-dimensionality passes from a module to its
  associated representation.

## Implementation notes

`IsFinDim` is stated vertex by vertex rather than as a single finiteness of the total space: the
category of representations is a functor category, with no ambient module to be finite over, and
over an infinite vertex set the two conditions genuinely differ. Over a finite quiver they agree,
and that is the setting the theory is meant for.

-/

public section

namespace TauCeti

open CategoryTheory
open scoped ModuleCat

universe u v w t

/-- **Pointwise finite-dimensionality** of a quiver representation: the vector space at every
vertex is finite-dimensional. Over a finite quiver this is total finite-dimensionality, and it is
the finiteness condition under which the indecomposables can be counted; the functor category
itself contains infinite-dimensional objects. -/
def IsFinDim (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q]
    (M : QuiverRep.{u, v, w, t} k Q) : Prop :=
  ∀ v : Paths Q, FiniteDimensional k (M.obj v)

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

/-- **The elimination and introduction rule for `TauCeti.IsFinDim`**: it is finite-dimensionality
at every vertex. -/
@[simp]
theorem isFinDim_iff {M : QuiverRep.{u, v, w, t} k Q} :
    IsFinDim k Q M ↔ ∀ v : Paths Q, FiniteDimensional k (M.obj v) :=
  Iff.rfl

/-- Finite-dimensionality at each vertex transports along an isomorphism of representations. -/
theorem IsFinDim.of_iso {M N : QuiverRep.{u, v, w, t} k Q} (h : IsFinDim k Q M) (e : M ≅ N) :
    IsFinDim k Q N := by
  intro v
  have := h v
  exact (e.app v).toLinearEquiv.finiteDimensional

section ExactStructure

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q]

open CategoryTheory.Limits CategoryTheory.ObjectProperty
open scoped ZeroObject

/-- Isomorphism closure makes pointwise finite-dimensionality a replete object property. -/
instance : ObjectProperty.IsClosedUnderIsomorphisms (IsFinDim.{u, v, w, t} k Q)
    where
  of_iso := fun e h => h.of_iso e

/-- The zero representation belongs to the finite-dimensional full subcategory. -/
instance : ObjectProperty.ContainsZero (IsFinDim.{u, v, w, t} k Q) where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    rw [isFinDim_iff]
    intro i
    have hi : IsZero ((0 : QuiverRep.{u, v, w, t} k Q).obj i) := Functor.zero_obj i
    let : Subsingleton ((0 : QuiverRep.{u, v, w, t} k Q).obj i) :=
      ModuleCat.subsingleton_of_isZero hi
    infer_instance

/-- Pointwise finite-dimensional representations are closed under extensions. -/
theorem isExtensionClosed_pointwiseFiniteDimensionalQuiverRepresentations :
    (ExactStructure.abelian (QuiverRep.{u, v, w, t} k Q)).IsExtensionClosed
      (IsFinDim k Q) := by
  refine ⟨fun {S} hS h₁ h₃ => ?_⟩
  rw [isFinDim_iff] at h₁ h₃ ⊢
  intro i
  let E := (evaluation (Paths Q) (ModuleCat k)).obj i
  have hSi : (S.map E).ShortExact :=
    ((ExactStructure.abelian_conflation _).mp hS).map_of_exact E
  have : Module.Finite k (S.map E).X₁ := by
    simpa only [ShortComplex.map_X₁, E, evaluation_obj_obj] using h₁ i
  have : Module.Finite k (S.map E).X₃ := by
    simpa only [ShortComplex.map_X₃, E, evaluation_obj_obj] using h₃ i
  have hfin : Module.Finite k (S.map E).X₂ :=
    Module.Finite.of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hSi.exact)
      hSi.moduleCat_surjective_g
  simpa only [ShortComplex.map_X₂, E, evaluation_obj_obj] using hfin

/-- Binary products keep the finite-dimensional full subcategory additive, as required by its
induced exact structure. -/
instance : ObjectProperty.IsClosedUnderBinaryProducts (IsFinDim.{u, v, w, t} k Q) := by
  have h := isExtensionClosed_pointwiseFiniteDimensionalQuiverRepresentations k Q
  exact h.isClosedUnderBinaryProducts

/-- The exact structure on pointwise finite-dimensional quiver representations. -/
noncomputable def pointwiseFiniteDimensionalQuiverRepresentationsExactStructure :
    ExactStructure (ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q)) :=
  (ExactStructure.abelian _).fullSubcategory _
    (isExtensionClosed_pointwiseFiniteDimensionalQuiverRepresentations k Q)

/-- Conflations of pointwise finite-dimensional quiver representations are exactly their short exact
sequences in the ambient functor category. -/
@[simp]
theorem pointwiseFiniteDimensionalQuiverRepresentationsExactStructure_conflation_iff
    (S : ShortComplex (ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q))) :
    (pointwiseFiniteDimensionalQuiverRepresentationsExactStructure k Q).Conflation S ↔
      (S.map (ObjectProperty.ι (IsFinDim k Q))).ShortExact :=
  (ExactStructure.fullSubcategory_conflation_iff
    (isExtensionClosed_pointwiseFiniteDimensionalQuiverRepresentations k Q) S).trans
    (ExactStructure.abelian_conflation _)

end ExactStructure

variable (k Q) [Finite Q]

/-- A pointwise finite-dimensional representation of a finite quiver gives a finite module over
the path algebra under `QuiverRep.asModule`. -/
theorem module_finite_asModule_of_isFinDim [DecidableEq Q]
    (M : QuiverRep.{u, v, w, t} k Q) (hM : IsFinDim k Q M) :
    Module.Finite (pathAlgebra k Q) (QuiverRep.asModule k Q M) := by
  let h (i : Q) : Module.Finite k (QuiverRep.vertexSpace k Q M i) :=
    hM ((Paths.of Q).obj i)
  let hsum : Module.Finite k (DirectSum Q (QuiverRep.vertexSpace k Q M)) := inferInstance
  let hmodule : Module.Finite k (QuiverRep.asModule k Q M) :=
    Module.Finite.equiv (QuiverRep.asModuleEquiv k Q M).symm
  exact Module.Finite.of_restrictScalars_finite k _ _

/-- Pointwise finite-dimensional representations of a finite quiver form an essentially small
category, via their finitely generated modules over the path algebra. -/
instance : EssentiallySmall.{max (max u v) w}
    (ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q)) := by
  classical
  apply essentiallySmall_of_fully_faithful
    ((ModuleCat.isFG (pathAlgebra k Q)).lift
      ((ObjectProperty.ι (IsFinDim k Q)) ⋙ (quiverRepEquivalence k Q).functor) (fun M => by
        let hmodule : Module.Finite (pathAlgebra k Q) (QuiverRep.asModule k Q M.1) :=
          module_finite_asModule_of_isFinDim k Q M.1 M.property
        let hshrink : Module.Finite (pathAlgebra k Q)
            (QuiverRep.asModuleShrink k Q M.1) :=
          Module.Finite.equiv (QuiverRep.asModuleShrinkEquiv k Q M.1).symm
        exact Module.Finite.equiv
          ((quiverRepEquivalenceFunctorObjShrinkIso k Q M.1).toLinearEquiv.symm)))

/-- A path algebra module finite-dimensional over the base field gives a representation with
finite-dimensional vertex spaces. -/
theorem isFinDim_quiverRepFunctor_obj (M : ModuleCat (pathAlgebra k Q))
    (hM : FiniteDimensional k M) :
    IsFinDim k Q ((quiverRepFunctor k Q).obj M) := by
  have := hM
  rw [isFinDim_iff]
  intro v
  -- The objects of `Paths Q` are the vertices of `Q`.
  change Q at v
  rw [quiverRepFunctor_obj, quiverRepOfModule_obj]
  infer_instance

end TauCeti
