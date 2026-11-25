/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Translate
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional

/-!
# The inverse Auslander–Reiten translate of a quiver representation

For a quiver with finitely many paths, `arInverseTranslate k Q M hM` is the inverse translate
`Tr D M` of the path-algebra module of `M`, `ModuleCat.arInverseTranslate k k`, read back as a
representation: the right transpose of a finite minimal presentation of the `k`-dual of the module.
The result is pointwise finite-dimensional and independent of the presentation up to isomorphism.

It vanishes exactly on injectives. For an indecomposable input, it is indecomposable
exactly when the input is non-injective, and its nonzero values are non-projective.
These are the endpoint properties needed for inverse translation on isomorphism classes.
The inverse comparisons with `D Tr` are in
`TauCeti/RepresentationTheory/Quiver/AuslanderReiten/Recovery.lean`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

universe u v w t

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q]
  [Finite (Quiver.TotalPath Q)]

local notation "kQ" => pathAlgebra k Q
local notation "eRep" => quiverRepEquivalence k Q
local notation "F" => quiverRepFunctor k Q

/-- The inverse Auslander–Reiten translate `Tr D M` of a pointwise finite-dimensional
representation: the inverse translate of its path-algebra module, read back as a
representation. -/
noncomputable def arInverseTranslate (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) : QuiverRep.{u, v, w, max u v w t} k Q :=
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  (F).obj (ModuleCat.arInverseTranslate.{u, max u v w, t} k k ((eRep).functor.obj M))

/-- The quiver inverse translate is the module inverse translate transported through the
path-algebra equivalence. -/
theorem arInverseTranslate_eq_quiverRepFunctor_obj (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) :
    have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
    arInverseTranslate.{u, v, w, t} k Q M hM =
      (F).obj (ModuleCat.arInverseTranslate.{u, max u v w, t} k k ((eRep).functor.obj M)) :=
  (rfl)

/-- Any finite minimal presentation of the `k`-dual computes the inverse translate.
This characterizes the construction independently of its chosen presentation. -/
theorem nonempty_iso_arInverseTranslate (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M)
    (P : FiniteProjectivePresentation (ModuleCat.of kQᵐᵒᵖ (MatlisDual k k ((eRep).functor.obj M))))
    (hP : IsMinimalProjectivePresentation P.p P.π) :
    Nonempty (arInverseTranslate.{u, v, w, t} k Q M hM ≅ (F).obj P.rightTranspose) := by
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  obtain ⟨e⟩ := ModuleCat.nonempty_iso_arInverseTranslate.{u, max u v w, t} k k _ P hP
  rw [arInverseTranslate_eq_quiverRepFunctor_obj]
  exact ⟨(F).mapIso e⟩

/-- Isomorphic representations have isomorphic inverse translates. -/
theorem nonempty_iso_arInverseTranslate_of_iso
    {M N : QuiverRep.{u, v, w, max u v w t} k Q}
    (hM : IsFinDim k Q M) (hN : IsFinDim k Q N) (e : M ≅ N) :
    Nonempty (arInverseTranslate.{u, v, w, t} k Q M hM ≅
      arInverseTranslate.{u, v, w, t} k Q N hN) := by
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q N hN
  obtain ⟨f⟩ := ModuleCat.nonempty_iso_arInverseTranslate_of_iso.{u, max u v w, t} k k
    ((eRep).functor.mapIso e)
  rw [arInverseTranslate_eq_quiverRepFunctor_obj, arInverseTranslate_eq_quiverRepFunctor_obj]
  exact ⟨(F).mapIso f⟩

/-- The inverse translate is pointwise finite-dimensional. -/
theorem isFinDim_arInverseTranslate (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) : IsFinDim k Q (arInverseTranslate.{u, v, w, t} k Q M hM) := by
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  rw [arInverseTranslate_eq_quiverRepFunctor_obj]
  exact isFinDim_quiverRepFunctor_obj k Q _ (Module.Finite.trans kQ _)

/-- The inverse translate is projective exactly when the input is injective. -/
@[simp]
theorem projective_arInverseTranslate_iff (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) :
    Projective (arInverseTranslate.{u, v, w, t} k Q M hM) ↔ Injective M := by
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  let T := ModuleCat.arInverseTranslate.{u, max u v w, t} k k ((eRep).functor.obj M)
  have h : Projective ((F).obj T) ↔ Projective T := by
    simpa only [Equivalence.symm_functor, quiverRepEquivalence_inverse] using
      (eRep).symm.map_projective_iff T
  rw [arInverseTranslate_eq_quiverRepFunctor_obj]
  exact h.trans ((ModuleCat.projective_arInverseTranslate_iff.{u, max u v w, t}
    (length_quotient_linearMap_self_eq_one k) _).trans ((eRep).map_injective_iff M))

/-- The inverse translate vanishes exactly on injective representations. -/
@[simp]
theorem isZero_arInverseTranslate_iff (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) :
    IsZero (arInverseTranslate.{u, v, w, t} k Q M hM) ↔ Injective M := by
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  let T := ModuleCat.arInverseTranslate.{u, max u v w, t} k k ((eRep).functor.obj M)
  have hz : IsZero ((F).obj T) ↔ IsZero T :=
    ⟨fun h ↦ IsZero.of_full_of_faithful_of_isZero (F) T h, (F).map_isZero⟩
  rw [arInverseTranslate_eq_quiverRepFunctor_obj]
  exact hz.trans ((ModuleCat.isZero_arInverseTranslate_iff.{u, max u v w, t}
    (length_quotient_linearMap_self_eq_one k) _).trans ((eRep).map_injective_iff M))

/-- For an indecomposable input, the inverse translate is indecomposable exactly when
the input is non-injective. -/
@[simp]
theorem indecomposable_arInverseTranslate_iff (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) (hiM : Indecomposable M) :
    Indecomposable (arInverseTranslate.{u, v, w, t} k Q M hM) ↔ ¬ Injective M := by
  refine ⟨fun h hI ↦ h.1 ((isZero_arInverseTranslate_iff.{u, v, w, t} k Q M hM).mpr hI),
    fun hn ↦ ?_⟩
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  have hi := (eRep).functor.indecomposable_obj_of_map_bijective hiM
    ((eRep).fullyFaithfulFunctor.map_bijective _ _)
  have hT := (ModuleCat.indecomposable_arInverseTranslate_iff.{u, max u v w, t}
    (length_quotient_linearMap_self_eq_one k) _ hi).mpr
      (fun h ↦ hn (((eRep).map_injective_iff M).mp h))
  rw [arInverseTranslate_eq_quiverRepFunctor_obj]
  exact (F).indecomposable_obj_of_map_bijective hT
    ((Functor.FullyFaithful.ofFullyFaithful (F)).map_bijective _ _)

end TauCeti
