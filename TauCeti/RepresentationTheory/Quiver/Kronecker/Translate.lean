/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Module.AuslanderReiten.Indecomposable
import TauCeti.Algebra.Module.AuslanderReiten.Injective
public import TauCeti.RepresentationTheory.Quiver.Representation.Translate
public import TauCeti.RepresentationTheory.Quiver.Kronecker.Injective
import TauCeti.RepresentationTheory.Quiver.Kronecker.AlmostSplit
import Mathlib.Algebra.Category.ModuleCat.Injective

/-!
# Auslander–Reiten translation for the one-arrow quiver

For the quiver `1 → 2`, the translate defined by a minimal projective presentation and scalar
duality sends the source simple `S₁` to the target simple `S₂`. This identifies the `D Tr`
construction with the left endpoint of the almost-split sequence `0 → S₂ → P₁ → S₁ → 0`.

The vertex injectives are identified as `I₁ ≅ S₁` and `I₂ ≅ P₁`. Thus among the three
indecomposables only `S₂` is non-injective, which determines the nonzero translate of `S₁`.
All statements hold over an arbitrary field.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras* (1995), IV.1.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

open Quiver.Kronecker

universe u

variable (k : Type u) [Field k] (A : Type) [Unique A]

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

/-- The `D Tr` Auslander–Reiten translate of the source simple of `1 → 2` is the target simple.
In particular it is the left endpoint of `kroneckerARSequence`. -/
theorem nonempty_iso_arTranslate_simpleRep_src_kronecker
    (hS : IsFinDim k (Quiver.Kronecker A) (simpleRep k (Quiver.Kronecker A) src)) :
    Nonempty (arTranslate k (Quiver.Kronecker A) (simpleRep k (Quiver.Kronecker A) src) hS ≅
      simpleRep k (Quiver.Kronecker A) tgt) := by
  -- Work with any finite minimal presentation of the source simple.
  let Q := Quiver.Kronecker A
  let E := quiverRepEquivalence k Q
  let S := simpleRep k Q src
  let M := E.functor.obj S
  have : Module.Finite k (pathAlgebra k Q) := module_finite_pathAlgebra k Q
  have : IsArtinianRing (pathAlgebra k Q) := IsArtinianRing.of_finite k _
  have : IsNoetherianRing (pathAlgebra k Q) := IsNoetherianRing.of_finite k _
  have : Module.Finite k M :=
    module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim k Q S hS
  have : Module.Finite (pathAlgebra k Q) M := Module.Finite.of_restrictScalars_finite k _ _
  obtain ⟨P, hP⟩ := FiniteProjectivePresentation.exists_isMinimal (M := M)
  have hnp : ¬ Module.Projective (pathAlgebra k Q) M := by
    intro hp
    have hp' := (IsProjective.iff_projective M).mp hp
    have : Projective S := (E.map_projective_iff S).mp hp'
    exact (isAlmostSplit_kroneckerARSequence k A).not_projective_X₃ this
  have hiM : IsIndecomposableModule (pathAlgebra k Q) M :=
    (indecomposable_iff_isIndecomposableModule M).mp
      (Functor.indecomposable_obj_of_map_bijective E.functor (indecomposable_of_simple S)
        (E.fullyFaithfulFunctor.map_bijective S S))
  have hlen : IsFiniteLength (pathAlgebra k Q) M :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩
  have : Module.Finite k (AuslanderReitenTranspose P.p) :=
    Module.Finite.trans (pathAlgebra k Q)ᵐᵒᵖ _
  let T := ModuleCat.of (pathAlgebra k Q) (AuslanderReitenTranslate k P.p)
  have hiT : Indecomposable T := (indecomposable_iff_isIndecomposableModule T).mpr
    ((AuslanderReitenTranslate.isIndecomposableModule_iff P.p k).mpr
      ((P.isIndecomposableModule_auslanderReitenTranspose_iff hP hlen hiM).mpr hnp))
  have hnT : ¬ Injective T := by
    intro ht
    have := (Module.injective_iff_injective_object (pathAlgebra k Q)
      (AuslanderReitenTranslate k P.p)).mpr ht
    exact hnp (hP.moduleInjective_auslanderReitenTranslate_iff_projective.mp this)
  -- Transport the landing properties of D Tr, then classify its indecomposable value.
  have hiF : Indecomposable (E.inverse.obj T) :=
    Functor.indecomposable_obj_of_map_bijective E.inverse hiT
      (E.fullyFaithfulInverse.map_bijective T T)
  have hnF : ¬ Injective (E.inverse.obj T) := fun h ↦ hnT ((E.symm.map_injective_iff T).mp h)
  rcases nonempty_iso_simpleRep_src_or_simpleRep_tgt_or_indecProjRep_of_indecomposable_kronecker
    (E.inverse.obj T) hiF with h | h | h
  · obtain ⟨e⟩ := h
    obtain ⟨f⟩ := nonempty_iso_indecInjRep_src_simpleRep_kronecker k A
    exact False.elim (hnF (Injective.of_iso (f ≪≫ e.symm) inferInstance))
  · -- Presentation independence identifies this value with the object-level translate.
    obtain ⟨e⟩ := nonempty_iso_arTranslate k Q S hS P hP
    rw [← quiverRepEquivalence_inverse] at e
    exact h.map (fun f ↦ e ≪≫ f)
  · obtain ⟨e⟩ := h
    obtain ⟨f⟩ := nonempty_iso_indecInjRep_tgt_indecProjRep_kronecker k A
    exact False.elim (hnF (Injective.of_iso (f ≪≫ e.symm) inferInstance))

end TauCeti
