/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Projectivization
import Mathlib.Algebra.Category.ModuleCat.Injective
import TauCeti.Algebra.Module.Injective.SelfInjective
import TauCeti.CategoryTheory.Abelian.Injective.Basic

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
theorem isSplitEpi_of_selfInjective_end {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] {M X Y : C} (hX : additiveClosure M X) (hY : additiveClosure M Y)
    (hEnd : Module.Injective (End M) (End M)) (f : X ⟶ Y) [Epi f] : IsSplitEpi f := by
  let F := preadditiveYonedaObj M
  have : Mono (F.map f.op) := (ModuleCat.mono_iff_injective _).2 fun g g' h ↦ by
    -- Expose the Yoneda map for rewriting, then read the bundled linear maps as compositions.
    change (preadditiveYonedaObj M).map f.op g = (preadditiveYonedaObj M).map f.op g' at h
    rw [preadditiveYonedaObj_map] at h
    change f ≫ g = f ≫ g' at h
    exact (cancel_epi f).mp h
  obtain ⟨hfinite, hproj⟩ := finiteProjectiveModules_iff.mp
    (finiteProjectiveModules_preadditiveYonedaObj_obj hY)
  have hmodule : Module.Injective (End M) (F.obj (op Y)) := .of_finite_projective hEnd
  have hInjective : Injective (F.obj (op Y)) :=
    Module.injective_object_of_injective_module _ _ (inj := hmodule)
  have hsplit := (injective_iff_forall_isSplitMono _).mp hInjective (F.map f.op)
  let P := additiveClosure M
  let g : (⟨X, hX⟩ : P.FullSubcategory) ⟶ ⟨Y, hY⟩ := ObjectProperty.homMk f
  have hg : IsSplitMono g.op := ((P.ι.op ⋙ F).isSplitMono_iff g.op).mp hsplit
  have : IsSplitEpi g := .mk' ⟨(retraction g.op).unop, Quiver.Hom.op_inj (IsSplitMono.id g.op)⟩
  exact inferInstanceAs (IsSplitEpi (P.ι.map g))

end TauCeti
