/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Projectivization
import Mathlib.Algebra.Category.ModuleCat.Injective
import TauCeti.Algebra.Module.Injective.SelfInjective

/-!
# Splitting epimorphisms in an additive closure

If `End M` is left self-injective, every epimorphism between objects in `add M` splits.
Contravariant projectivization sends it to a monomorphism with finitely generated projective
source. This source is injective, so the monomorphism splits and full faithfulness lifts the
retraction. This gives the splitting obstruction used for nonsemisimple Auslander algebras.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace TauCeti

/-- Over a left self-injective `End M`, an epimorphism between objects of `add M` splits. -/
theorem isSplitEpi_of_injective_end {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] {M X Y : C} (hX : additiveClosure M X) (hY : additiveClosure M Y)
    (hEnd : Module.Injective (End M) (End M)) (f : X ⟶ Y) [Epi f] : IsSplitEpi f := by
  let F := preadditiveYonedaObj M
  have : Mono (F.map f.op) := (ModuleCat.mono_iff_injective _).2 fun g g' h ↦
    (cancel_epi f).1 h
  obtain ⟨hfinite, hproj⟩ := finiteProjectiveModules_iff.mp
    (finiteProjectiveModules_preadditiveYonedaObj_obj hY)
  have hmodule : Module.Injective (End M) (F.obj (op Y)) := .of_finite_projective hEnd
  have : Injective (F.obj (op Y)) :=
    Module.injective_object_of_injective_module _ _ (inj := hmodule)
  obtain ⟨s, hs⟩ := (preadditiveYonedaObj_map_bijective hX Y).surjective
    (Injective.factorThru (𝟙 (F.obj (op Y))) (F.map f.op))
  refine ⟨⟨s.unop, Quiver.Hom.op_inj ?_⟩⟩
  apply (preadditiveYonedaObj_map_bijective hY Y).injective
  rw [op_comp, Functor.map_comp, Quiver.Hom.op_unop, hs, Injective.comp_factorThru]
  exact (F.map_id _).symm

end TauCeti
