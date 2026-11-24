/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.Translate
public import TauCeti.RepresentationTheory.Quiver.Representation.InverseTranslate

/-!
# Inverse identities for Auslander–Reiten translates of quiver representations

For a quiver with finitely many paths, `Tr D` recovers a non-projective indecomposable
representation from its `D Tr` translate. Conversely, `D Tr` recovers a non-injective
indecomposable from its `Tr D` translate. Thus the explicit inverse translate realizes
the inverse of the correspondence on indecomposable isomorphism classes.

The identities are isomorphisms of actual representations. They are the identities
`ModuleCat.nonempty_iso_arInverseTranslate_arTranslate` and
`ModuleCat.nonempty_iso_arTranslate_arInverseTranslate` for the path algebra, transported through
the equivalence with its modules. The base field is arbitrary; neither algebraic closedness nor
finite representation type is needed.

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

/-- The path-algebra module of a represented module is that module, through the counit. -/
private theorem nonempty_iso_functor_obj_quiverRepFunctor_obj (T : ModuleCat.{max u v w t} kQ) :
    Nonempty ((E).functor.obj ((F).obj T) ≅ T) :=
  ⟨by simpa only [quiverRepEquivalence_inverse, Functor.comp_obj, Functor.id_obj] using
    (E).counitIso.app T⟩

/-- A representation is the representation of its path-algebra module, through the unit. -/
private theorem nonempty_iso_quiverRepFunctor_obj_functor_obj
    (M : QuiverRep.{u, v, w, max u v w t} k Q) : Nonempty ((F).obj ((E).functor.obj M) ≅ M) :=
  ⟨by simpa only [quiverRepEquivalence_inverse, Functor.comp_obj, Functor.id_obj] using
    ((E).unitIso.app M).symm⟩

/-- The inverse translate `Tr D` recovers every finite-dimensional non-projective
indecomposable representation from its `D Tr` translate. -/
theorem nonempty_iso_arInverseTranslate_arTranslate
    (M : QuiverRep.{u, v, w, max u v w t} k Q) (hM : IsFinDim k Q M)
    (hiM : Indecomposable M) (hpM : ¬ Projective M) :
    Nonempty (arInverseTranslate.{u, v, w, t} k Q (arTranslate.{u, v, w, t} k Q M hM)
      (isFinDim_arTranslate.{u, v, w, t} k Q M hM) ≅ M) := by
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q _
    (isFinDim_arTranslate.{u, v, w, t} k Q M hM)
  obtain ⟨c⟩ := nonempty_iso_functor_obj_quiverRepFunctor_obj.{u, v, w, t} k Q
    (ModuleCat.arTranslate.{u, max u v w, t} k k ((E).functor.obj M))
  rw [← arTranslate_eq_quiverRepFunctor_obj] at c
  obtain ⟨a⟩ := ModuleCat.nonempty_iso_arInverseTranslate_of_iso.{u, max u v w, t} k k c
  obtain ⟨b⟩ := ModuleCat.nonempty_iso_arInverseTranslate_arTranslate.{u, max u v w, t}
    (length_quotient_linearMap_self_eq_one k) _ ((E).functor.indecomposable_obj_of_map_bijective
      hiM ((E).fullyFaithfulFunctor.map_bijective _ _))
    (fun h ↦ hpM (((E).map_projective_iff M).mp h))
  obtain ⟨cM⟩ := nonempty_iso_quiverRepFunctor_obj_functor_obj.{u, v, w, t} k Q M
  rw [arInverseTranslate_eq_quiverRepFunctor_obj]
  exact ⟨(F).mapIso (a ≪≫ b) ≪≫ cM⟩

/-- The translate `D Tr` recovers every finite-dimensional non-injective indecomposable
representation from its `Tr D` inverse translate. -/
theorem nonempty_iso_arTranslate_arInverseTranslate
    (N : QuiverRep.{u, v, w, max u v w t} k Q) (hN : IsFinDim k Q N)
    (hiN : Indecomposable N) (hinj : ¬ Injective N) :
    Nonempty (arTranslate.{u, v, w, t} k Q (arInverseTranslate.{u, v, w, t} k Q N hN)
      (isFinDim_arInverseTranslate.{u, v, w, t} k Q N hN) ≅ N) := by
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q N hN
  have := module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q _
    (isFinDim_arInverseTranslate.{u, v, w, t} k Q N hN)
  obtain ⟨c⟩ := nonempty_iso_functor_obj_quiverRepFunctor_obj.{u, v, w, t} k Q
    (ModuleCat.arInverseTranslate.{u, max u v w, t} k k ((E).functor.obj N))
  rw [← arInverseTranslate_eq_quiverRepFunctor_obj] at c
  obtain ⟨a⟩ := ModuleCat.nonempty_iso_arTranslate_of_iso.{u, max u v w, t} k k c
  obtain ⟨b⟩ := ModuleCat.nonempty_iso_arTranslate_arInverseTranslate.{u, max u v w, t}
    (length_quotient_linearMap_self_eq_one k) _ ((E).functor.indecomposable_obj_of_map_bijective
      hiN ((E).fullyFaithfulFunctor.map_bijective _ _))
    (fun h ↦ hinj (((E).map_injective_iff N).mp h))
  obtain ⟨cN⟩ := nonempty_iso_quiverRepFunctor_obj_functor_obj.{u, v, w, t} k Q N
  rw [arTranslate_eq_quiverRepFunctor_obj]
  exact ⟨(F).mapIso (a ≪≫ b) ≪≫ cN⟩

end TauCeti
