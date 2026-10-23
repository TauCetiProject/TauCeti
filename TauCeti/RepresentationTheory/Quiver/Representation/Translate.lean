/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Translate
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional

/-!
# The Auslander–Reiten translate of a quiver representation

For a quiver with finitely many paths, `arTranslate k Q M hM` is the representation corresponding
to the translate `ModuleCat.arTranslate` of the path-algebra module of `M`, that is, to `D Tr` of
a chosen finite minimal projective presentation of that module.
It is pointwise finite-dimensional, independent of the minimal presentation up to isomorphism,
and zero exactly when `M` is projective. For indecomposable `M`, it is indecomposable exactly
when `M` is non-projective, and every nonzero value is non-injective. These properties allow
the translate to act on isomorphism classes of indecomposables and provide the endpoints of
almost-split sequences. On non-projective indecomposables, it detects isomorphism classes.
AR duality and the inverse correspondence are separate results.

The field is arbitrary. Vertex and arrow universes are independent of the field universe.
The vertex spaces lie in a universe containing the field and the path algebra, as do the
transpose and its linear dual.

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
local notation "E" => quiverRepEquivalence k Q
local notation "F" => quiverRepFunctor k Q

/-- The Auslander–Reiten translate `τ M = D Tr M` of a pointwise finite-dimensional
representation: the translate of its path-algebra module, read back as a representation. -/
noncomputable def arTranslate (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) : QuiverRep.{u, v, w, max u v w t} k Q :=
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  (F).obj (ModuleCat.arTranslate.{u, max u v w, t} k ((E).functor.obj M))

private theorem arTranslate_eq (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) :
    have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
    arTranslate.{u, v, w, t} k Q M hM =
      (F).obj (ModuleCat.arTranslate.{u, max u v w, t} k ((E).functor.obj M)) :=
  rfl

/-- Any finite minimal projective presentation computes the same translate up to isomorphism.
This characterizes `arTranslate` without referring to its chosen presentation. -/
theorem nonempty_iso_arTranslate (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M)
    (P : FiniteProjectivePresentation ((E).functor.obj M))
    (hP : IsMinimalProjectivePresentation P.p P.π) :
    Nonempty (arTranslate.{u, v, w, t} k Q M hM ≅
      (F).obj (ModuleCat.of kQ (AuslanderReitenTranslate k P.p))) := by
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  obtain ⟨e⟩ := ModuleCat.nonempty_iso_arTranslate.{u, max u v w, t} k ((E).functor.obj M) P hP
  rw [arTranslate_eq]
  exact ⟨(F).mapIso e⟩

/-- Isomorphic representations have isomorphic Auslander–Reiten translates. -/
theorem nonempty_iso_arTranslate_of_iso {M N : QuiverRep.{u, v, w, max u v w t} k Q}
    (hM : IsFinDim k Q M) (hN : IsFinDim k Q N) (e : M ≅ N) :
    Nonempty (arTranslate.{u, v, w, t} k Q M hM ≅
      arTranslate.{u, v, w, t} k Q N hN) := by
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q N hN
  obtain ⟨f⟩ := ModuleCat.nonempty_iso_arTranslate_of_iso.{u, max u v w, t} k ((E).functor.mapIso e)
  rw [arTranslate_eq, arTranslate_eq]
  exact ⟨(F).mapIso f⟩

/-- The Auslander–Reiten translate stays within the pointwise finite-dimensional
representations. -/
theorem isFinDim_arTranslate (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) : IsFinDim k Q (arTranslate.{u, v, w, t} k Q M hM) := by
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  rw [arTranslate_eq]
  exact isFinDim_quiverRepFunctor_obj k Q _ (Module.Finite.trans kQ _)

/-- The translate vanishes precisely on the projective representations. -/
@[simp]
theorem isZero_arTranslate_iff (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) : IsZero (arTranslate.{u, v, w, t} k Q M hM) ↔ Projective M := by
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  let T := ModuleCat.arTranslate.{u, max u v w, t} k ((E).functor.obj M)
  have hzero : IsZero ((F).obj T) ↔ IsZero T :=
    ⟨fun h ↦ IsZero.of_full_of_faithful_of_isZero (F) T h, (F).map_isZero⟩
  rw [arTranslate_eq]
  exact hzero.trans ((ModuleCat.isZero_arTranslate_iff.{u, max u v w, t} k _).trans
    ((E).map_projective_iff M))

/-- The translate of a finite-dimensional indecomposable representation is indecomposable
exactly when the representation is not projective. -/
@[simp]
theorem indecomposable_arTranslate_iff (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) (hiM : Indecomposable M) :
    Indecomposable (arTranslate.{u, v, w, t} k Q M hM) ↔ ¬ Projective M := by
  constructor
  · intro h hp
    exact h.1 ((isZero_arTranslate_iff k Q M hM).mpr hp)
  · intro hp
    have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
    have hi := (E).functor.indecomposable_obj_of_map_bijective hiM
      ((E).fullyFaithfulFunctor.map_bijective _ _)
    have hT := (ModuleCat.indecomposable_arTranslate_iff.{u, max u v w, t} k _ hi).mpr
      (fun h ↦ hp (((E).map_projective_iff M).mp h))
    rw [arTranslate_eq]
    exact (F).indecomposable_obj_of_map_bijective hT
      ((Functor.FullyFaithful.ofFullyFaithful (F)).map_bijective _ _)

/-- The translate is injective exactly when the original representation is projective.
Consequently every nonzero translate is non-injective. -/
@[simp]
theorem injective_arTranslate_iff (M : QuiverRep.{u, v, w, max u v w t} k Q)
    (hM : IsFinDim k Q M) :
    Injective (arTranslate.{u, v, w, t} k Q M hM) ↔ Projective M := by
  let eRep := quiverRepEquivalence.{u, v, w, max u v w t} k Q
  let fRep := quiverRepFunctor.{u, v, w, max u v w t} k Q
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  let T := ModuleCat.arTranslate.{u, max u v w, t} k (eRep.functor.obj M)
  have hinj : Injective (fRep.obj T) ↔ Injective T := by
    simpa only [eRep, fRep, Equivalence.symm_functor, quiverRepEquivalence_inverse] using
      eRep.symm.map_injective_iff T
  rw [arTranslate_eq]
  exact hinj.trans ((ModuleCat.injective_arTranslate_iff.{u, max u v w, t} k _).trans
    (eRep.map_projective_iff M))

/-- On finite-dimensional indecomposables, with a non-projective source, isomorphism
of Auslander–Reiten translates is equivalent to isomorphism of the representations. -/
theorem nonempty_iso_arTranslate_iff {M N : QuiverRep.{u, v, w, max u v w t} k Q}
    (hM : IsFinDim k Q M) (hN : IsFinDim k Q N)
    (hiM : Indecomposable M) (hiN : Indecomposable N) (hpM : ¬ Projective M) :
    Nonempty (arTranslate.{u, v, w, t} k Q M hM ≅ arTranslate.{u, v, w, t} k Q N hN) ↔
      Nonempty (M ≅ N) := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨e⟩ ↦ nonempty_iso_arTranslate_of_iso.{u, v, w, t} k Q hM hN e⟩
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q N hN
  rw [arTranslate_eq, arTranslate_eq] at e
  have hiM' := (E).functor.indecomposable_obj_of_map_bijective hiM
    ((E).fullyFaithfulFunctor.map_bijective _ _)
  have hiN' := (E).functor.indecomposable_obj_of_map_bijective hiN
    ((E).fullyFaithfulFunctor.map_bijective _ _)
  obtain ⟨f⟩ := (ModuleCat.nonempty_iso_arTranslate_iff.{u, max u v w, t} k hiM' hiN'
    (fun h ↦ hpM (((E).map_projective_iff M).mp h))).mp
      ⟨(Functor.FullyFaithful.ofFullyFaithful (F)).preimageIso e⟩
  exact ⟨(E).fullyFaithfulFunctor.preimageIso f⟩

/-- Every finite-dimensional non-injective indecomposable representation is the translate
of a finite-dimensional non-projective indecomposable representation. -/
theorem exists_nonempty_iso_arTranslate
    (N : QuiverRep.{u, v, w, max u v w t} k Q) (hN : IsFinDim k Q N)
    (hiN : Indecomposable N) (hinj : ¬ Injective N) :
    ∃ (M : QuiverRep.{u, v, w, max u v w t} k Q) (hM : IsFinDim k Q M),
      Indecomposable M ∧ ¬ Projective M ∧
        Nonempty (arTranslate.{u, v, w, t} k Q M hM ≅ N) := by
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q N hN
  have hi := (E).functor.indecomposable_obj_of_map_bijective hiN
    ((E).fullyFaithfulFunctor.map_bijective _ _)
  obtain ⟨L, _, hiL, hpL, ⟨e⟩⟩ := ModuleCat.exists_nonempty_iso_arTranslate.{u, max u v w, t}
    k ((E).functor.obj N) hi (fun h ↦ hinj (((E).map_injective_iff N).mp h))
  let M := (E).inverse.obj L
  have hM : IsFinDim k Q M := by
    simpa only [M, quiverRepEquivalence_inverse] using
      isFinDim_quiverRepFunctor_obj k Q L (Module.Finite.trans kQ L)
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  obtain ⟨f⟩ := ModuleCat.nonempty_iso_arTranslate_of_iso.{u, max u v w, t} k
    (M := (E).functor.obj M) (N := L) ((E).counitIso.app L)
  have hiM := (E).inverse.indecomposable_obj_of_map_bijective hiL
    ((E).fullyFaithfulInverse.map_bijective _ _)
  have hpM : ¬ Projective M := fun h ↦ hpL (((E).symm.map_projective_iff L).mp h)
  refine ⟨M, hM, hiM, hpM, ⟨?_⟩⟩
  rw [arTranslate_eq, ← quiverRepEquivalence_inverse]
  exact (E).inverse.mapIso (f ≪≫ e) ≪≫ ((E).unitIso.app N).symm

end TauCeti
