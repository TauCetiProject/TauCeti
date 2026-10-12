/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Indecomposable
public import TauCeti.CategoryTheory.Preadditive.Equivalence
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional

/-!
# Fitting's lemma for quiver representations

A pointwise finite-dimensional representation of a quiver with finitely many vertices corresponds
to a finite-length module over its path algebra. For an indecomposable representation, Fitting's
lemma therefore says that every endomorphism is either nilpotent or an isomorphism. In particular,
its endomorphism ring is local, and the non-isomorphisms are exactly its nilpotent endomorphisms.
This supplies the local endomorphism rings used by the radical and irreducible-morphism theory.

Neither acyclicity nor finiteness of the arrows is required. The path algebra itself can be
infinite-dimensional, and the field need not be algebraically closed.

## Main results

* `TauCeti.QuiverRep.isNilpotent_or_isIso`: Fitting's dichotomy for an endomorphism.
* `TauCeti.QuiverRep.indecomposable_iff_isLocalRing_end`: a pointwise finite-dimensional
  representation is indecomposable exactly when its endomorphism ring is local.
* `TauCeti.QuiverRep.isNilpotent_iff_not_isIso`: the non-isomorphisms of an indecomposable
  representation are precisely the nilpotent endomorphisms.

## References

I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
Algebras*, Vol. 1, Section I.4. The module-level Fitting theorem is in
`TauCeti.RingTheory.KrullSchmidt.Indecomposable`.
-/

public section

namespace TauCeti.QuiverRep

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q] [Finite Q]
  {M : QuiverRep.{u, v, w, t} k Q}

/-- Every endomorphism of a pointwise finite-dimensional indecomposable representation of a
quiver with finitely many vertices is nilpotent or an isomorphism. -/
theorem isNilpotent_or_isIso (hfin : IsFinDim k Q M) (hM : Indecomposable M) (f : End M) :
    IsNilpotent f ∨ IsIso f := by
  let E := quiverRepEquivalence.{u, v, w, t} k Q
  have : Module.Finite k (E.functor.obj M) :=
    module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hfin
  have : IsArtinian (pathAlgebra k Q) (E.functor.obj M) := isArtinian_of_tower k inferInstance
  have : IsNoetherian (pathAlgebra k Q) (E.functor.obj M) := isNoetherian_of_tower k inferInstance
  have hind : Indecomposable (E.functor.obj M) :=
    Functor.indecomposable_obj_of_map_bijective E.functor hM
      (E.fullyFaithfulFunctor.map_bijective M M)
  let eCat : End M ≃+* End (E.functor.obj M) :=
    { E.fullyFaithfulFunctor.mulEquivEnd M with
      map_add' := fun _ _ ↦ E.functor.map_add }
  let e := eCat.trans (ModuleCat.endRingEquiv (E.functor.obj M))
  rcases ((TauCeti.indecomposable_iff_isIndecomposableModule _).mp hind).isNilpotent_or_isUnit
      (e f) with hnil | hunit
  · exact Or.inl (by simpa only [RingEquiv.symm_apply_apply] using hnil.map e.symm)
  · exact Or.inr ((isUnit_iff_isIso f).mp
      (by simpa only [RingEquiv.symm_apply_apply] using hunit.map e.symm))

/-- A pointwise finite-dimensional representation of a quiver with finitely many vertices is
indecomposable if and only if its endomorphism ring is local. -/
theorem indecomposable_iff_isLocalRing_end (hfin : IsFinDim k Q M) :
    Indecomposable M ↔ IsLocalRing (End M) := by
  constructor
  · intro hM
    have hid : (1 : End M) ≠ 0 := fun h ↦
      hM.1 ((IsZero.iff_id_eq_zero M).mpr h)
    have : Nontrivial (End M) := nontrivial_of_ne 1 0 hid
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f ↦ ?_
    exact (isNilpotent_or_isIso hfin hM f).symm.imp
      (isUnit_iff_isIso f).mpr IsNilpotent.isUnit_one_sub
  · intro hlocal
    have : IsLocalRing (End M) := hlocal
    refine indecomposable_of_injective_of_isLocalRing ?_ (id : End M → End M)
      Function.injective_id rfl rfl (fun _ ↦ rfl)
    exact fun h ↦ one_ne_zero (α := End M) ((IsZero.iff_id_eq_zero M).mp h)

/-- In a pointwise finite-dimensional indecomposable representation of a quiver with finitely
many vertices, an endomorphism is nilpotent exactly when it is not an isomorphism. -/
theorem isNilpotent_iff_not_isIso (hfin : IsFinDim k Q M) (hM : Indecomposable M) (f : End M) :
    IsNilpotent f ↔ ¬ IsIso f := by
  have : IsLocalRing (End M) := (indecomposable_iff_isLocalRing_end hfin).mp hM
  exact ⟨fun hf hi ↦ hf.not_isUnit ((isUnit_iff_isIso f).mpr hi),
    fun hf ↦ (isNilpotent_or_isIso hfin hM f).resolve_right hf⟩

end TauCeti.QuiverRep
