/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Projectivization
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import TauCeti.Algebra.Module.Injective.SelfInjective
import TauCeti.CategoryTheory.Abelian.Injective.Basic

/-!
# Splitting ambient epimorphisms between objects of an additive closure

If `End M` is left self-injective, every epimorphism in `C` with source and target in
`add M` splits.
Contravariant projectivization sends it to a monomorphism with finitely generated projective
source. This source is injective, so the monomorphism splits and full faithfulness lifts the
retraction. This gives the splitting obstruction used for nonsemisimple Auslander algebras.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace TauCeti

/-- If `End M` is left self-injective, an epimorphism in `C` with source and target in
`add M` splits. -/
theorem isSplitEpi_of_selfInjective_end {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] {M X Y : C} (hX : additiveClosure M X) (hY : additiveClosure M Y)
    (hEnd : Module.Injective (End M) (End M)) (f : X ⟶ Y) [Epi f] : IsSplitEpi f := by
  let F := preadditiveYonedaObj M
  have : Mono (F.map f.op) := F.map_mono f.op
  obtain ⟨hfinite, hproj⟩ := finiteProjectiveModules_iff.mp
    (finiteProjectiveModules_preadditiveYonedaObj_obj hY)
  have hmodule : Module.Injective (End M) (F.obj (op Y)) := .of_finite_projective hEnd
  have hInjective : Injective (F.obj (op Y)) :=
    Module.injective_object_of_injective_module _ _ (inj := hmodule)
  have hsplit := (injective_iff_forall_isSplitMono _).mp hInjective (F.map f.op)
  let P := additiveClosure M
  let g : (⟨X, hX⟩ : P.FullSubcategory) ⟶ ⟨Y, hY⟩ := ObjectProperty.homMk f
  have hι : P.ι.map g = f := by
    simp only [ObjectProperty.ι_map, g, ObjectProperty.homMk_hom]
  have hmap : (P.ι.op ⋙ F).map g.op = F.map f.op := by
    rw [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, hι]
  have hg : IsSplitMono g.op := ((P.ι.op ⋙ F).isSplitMono_iff g.op).mp (hmap ▸ hsplit)
  have : IsSplitEpi g.op.op := inferInstance
  have : IsSplitEpi g := by
    simpa only [unopUnop_map, Quiver.Hom.unop_op] using
      (inferInstance : IsSplitEpi ((unopUnop P.FullSubcategory).map g.op.op))
  rw [← hι]
  infer_instance

end TauCeti
