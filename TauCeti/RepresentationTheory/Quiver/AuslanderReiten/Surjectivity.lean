/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.AuslanderReiten.Injectivity
import TauCeti.Algebra.Module.AuslanderReiten.Surjectivity

/-!
# Surjectivity of Auslander–Reiten translation on quiver representations

For a quiver with finitely many paths, every pointwise finite-dimensional non-injective
indecomposable representation is a translate. Its preimage is a finite-dimensional
non-projective indecomposable. On isomorphism classes that preimage is unique, so the
partial translation gives a bijection from non-projective to non-injective vertices.

The construction transports module-level surjectivity through the equivalence with
path-algebra modules. No algebraic closedness or finite representation type is required.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Sections IV.1 and VII.1.
-/

public section

namespace TauCeti

open CategoryTheory

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

universe u v w t

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q]
  [Finite (Quiver.TotalPath Q)]

/-- Every finite-dimensional non-injective indecomposable representation is the translate
of a finite-dimensional non-projective indecomposable representation. -/
theorem exists_nonempty_iso_arTranslate
    (N : QuiverRep.{u, v, w, max u v w t} k Q) (hN : IsFinDim k Q N)
    (hiN : Indecomposable N) (hinj : ¬ Injective N) :
    ∃ (M : QuiverRep.{u, v, w, max u v w t} k Q) (hM : IsFinDim k Q M),
      Indecomposable M ∧ ¬ Projective M ∧
        Nonempty (arTranslate.{u, v, w, t} k Q M hM ≅ N) := by
  let E := quiverRepEquivalence.{u, v, w, max u v w t} k Q
  have : Module.Finite k (E.functor.obj N) :=
    module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim k Q N hN
  have hi := E.functor.indecomposable_obj_of_map_bijective hiN
    (E.fullyFaithfulFunctor.map_bijective _ _)
  obtain ⟨L, hL, hiL, hpL, P, hP, ⟨e⟩⟩ :=
    ModuleCat.exists_auslanderReitenTranslate.{u, max u v w, t}
      (k := k) (E.functor.obj N) hi
      (fun h ↦ hinj ((E.map_injective_iff N).mp h))
  let M := E.inverse.obj L
  have hM : IsFinDim k Q M := by
    simpa only [M, E, quiverRepEquivalence_inverse] using
      isFinDim_quiverRepFunctor_obj k Q L hL
  let d := (E.counitIso.app L).symm.toLinearEquiv
  -- Transport only the augmentation: the presenting map and its transpose stay fixed.
  let P' : FiniteProjectivePresentation (E.functor.obj M) :=
    { P with
      π := d.toLinearMap ∘ₗ P.π
      exact := LinearEquiv.postcomp_exact_iff_exact.mpr P.exact
      surjective := d.surjective.comp P.surjective }
  obtain ⟨f⟩ := nonempty_iso_arTranslate.{u, v, w, t} k Q M hM P'
    (hP.comp_linearEquiv d)
  have hiM := E.inverse.indecomposable_obj_of_map_bijective hiL
    (E.fullyFaithfulInverse.map_bijective _ _)
  have hpM : ¬ Projective M := fun h ↦ hpL ((E.symm.map_projective_iff L).mp h)
  refine ⟨M, hM, hiM, hpM, ⟨?_⟩⟩
  -- The canonical presentation comparison lands in the module-to-representation functor.
  rw [← quiverRepEquivalence_inverse] at f
  exact f ≪≫ E.inverse.mapIso e.toModuleIso ≪≫ (E.unitIso.app N).symm

namespace irreducibleMorphismQuiver

variable {k Q}

/-- A vertex has a unique preimage under defined Auslander–Reiten translation exactly
when it is non-injective. Thus translation bijects non-projective and non-injective classes. -/
@[simp]
theorem existsUnique_translate_eq_some_iff
    (b : irreducibleMorphismQuiver.{u, v, w, max u v w t} k Q) :
    (∃! a, translate.{u, v, w, t} a = some b) ↔ ¬ Injective b.representative := by
  refine ⟨fun ⟨a, ha, _⟩ ↦ not_injective_of_translate_eq_some ha, fun hb ↦ ?_⟩
  obtain ⟨M, hM, hiM, hpM, e⟩ := exists_nonempty_iso_arTranslate.{u, v, w, t} k Q
    b.representative b.representative_property.1 b.representative_property.2 hb
  have ha : translate.{u, v, w, t} (of hM hiM) = some b := by
    simpa only [of_representative] using
      (translate_of_eq_some_of_iff.{u, v, w, t} hM hiM
        b.representative_property.1 b.representative_property.2).mpr ⟨hpM, e⟩
  exact ⟨of hM hiM, ha, fun a h ↦ eq_of_translate_eq_some h ha⟩

end irreducibleMorphismQuiver

end TauCeti
