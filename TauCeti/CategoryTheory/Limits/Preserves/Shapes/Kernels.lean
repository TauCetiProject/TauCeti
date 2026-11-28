/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Transporting cokernel presentations along a fully faithful functor

Let `G` be a fully faithful functor preserving cokernels, and fix isomorphisms `G(A) ≅ A'` and
`G(B) ≅ B'`. Then an object `F` is a cokernel of some morphism `A ⟶ B` exactly when `G(F)` is a
cokernel of some morphism `A' ⟶ B'`
(`CategoryTheory.Limits.exists_cokernel_iso_iff_of_fullyFaithful`).
-/

public section

universe v v' u u'

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasCokernels C] [HasCokernels D]

/-- A fully faithful functor preserving cokernels identifies the cokernel presentations of `F`
by morphisms `A ⟶ B` with those of `G(F)` by morphisms between objects isomorphic to `G(A)`
and `G(B)`. -/
theorem exists_cokernel_iso_iff_of_fullyFaithful (G : C ⥤ D) [G.Full] [G.Faithful]
    [G.PreservesZeroMorphisms] {A B : C} {A' B' : D}
    [∀ d : A ⟶ B, PreservesColimit (parallelPair d 0) G]
    (eA : G.obj A ≅ A') (eB : G.obj B ≅ B') (F : C) :
    (∃ d : A ⟶ B, Nonempty (cokernel d ≅ F)) ↔
      ∃ f : A' ⟶ B', Nonempty (cokernel f ≅ G.obj F) := by
  constructor
  · rintro ⟨d, ⟨e⟩⟩
    let f := eA.inv ≫ G.map d ≫ eB.hom
    let i := cokernel.mapIso (G.map d) f eA eB (by simp [f])
    exact ⟨f, ⟨i.symm ≪≫ (PreservesCokernel.iso G d).symm ≪≫ G.mapIso e⟩⟩
  · rintro ⟨f, ⟨e⟩⟩
    let d := G.preimage (eA.hom ≫ f ≫ eB.inv)
    let i := cokernel.mapIso (G.map d) f eA eB (by
      dsimp only [d]
      rw [Functor.map_preimage]
      simp)
    exact ⟨d, ⟨G.preimageIso (PreservesCokernel.iso G d ≪≫ i ≪≫ e)⟩⟩

end CategoryTheory.Limits
