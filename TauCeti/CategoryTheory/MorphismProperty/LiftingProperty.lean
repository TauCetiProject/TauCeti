/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Lifting properties of images of morphism properties

The right lifting property against a union of classes of morphisms is the intersection of the
right lifting properties against each class (`MorphismProperty.rlp_iSup`).

For an adjunction `F ⊣ G`, a morphism `p` has the right lifting property against the image
`T.strictMap F` of a class `T` exactly when `G.map p` has the right lifting property against
`T` (`CategoryTheory.Adjunction.rlp_strictMap`). Dually, `F` carries maps with the left lifting
property against a class `P` to maps with the left lifting property against every class whose
image under `G` lies in `P` (`CategoryTheory.Adjunction.strictMap_llp_le_llp`).

These are the formal steps that transfer generating cofibrations along a left adjoint, as in the
construction of projective model structures on diagram categories or on module categories. The
image of a small class of morphisms is small (`MorphismProperty.isSmall_strictMap`), so such
transferred generators remain admissible for the small object argument.

## References

* P. S. Hirschhorn, *Model categories and their localizations*, Mathematical Surveys and
  Monographs 99, American Mathematical Society, 2003, Section 11.3.
-/

public section

universe w v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace MorphismProperty

/-- The right lifting property against a union of classes is the intersection of the right
lifting properties against each class. -/
@[simp]
lemma rlp_iSup {ι : Sort*} (T : ι → MorphismProperty C) :
    (⨆ i, T i).rlp = ⨅ i, (T i).rlp :=
  gc_llp_rlp.u_iInf

/-- The image of a family of morphisms is the family of their images. -/
lemma strictMap_ofHoms {ι : Type*} {A B : ι → C} (f : ∀ i, A i ⟶ B i) (F : C ⥤ D) :
    (ofHoms f).strictMap F = ofHoms (fun i ↦ F.map (f i)) := by
  ext X Y g
  constructor
  · rintro ⟨⟨i⟩⟩
    exact ⟨i⟩
  · rintro ⟨i⟩
    exact ⟨⟨i⟩⟩

/-- The image of a small class of morphisms is small. -/
instance isSmall_strictMap (T : MorphismProperty C) [IsSmall.{w} T] (F : C ⥤ D) :
    IsSmall.{w} (T.strictMap F) := by
  obtain ⟨ι, A, B, f, rfl⟩ := (isSmall_iff_eq_ofHoms.{w} T).1 inferInstance
  rw [strictMap_ofHoms]
  infer_instance

end MorphismProperty

namespace Adjunction

open MorphismProperty

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

include adj

/-- A morphism has the right lifting property against the images under a left adjoint `F` of
the morphisms of `T` exactly when its image under the right adjoint has the right lifting
property against `T`. -/
lemma rlp_strictMap (T : MorphismProperty C) :
    (T.strictMap F).rlp = T.rlp.inverseImage G := by
  ext X Y p
  constructor
  · intro hp A B i hi
    exact (adj.hasLiftingProperty_iff i p).1 (hp _ ⟨hi⟩)
  · rintro hp _ _ _ ⟨hi⟩
    exact (adj.hasLiftingProperty_iff _ p).2 (hp _ hi)

/-- A left adjoint `F` carries maps with the left lifting property against `P` to maps with the
left lifting property against every class `W` whose image under the right adjoint lies in `P`. -/
lemma strictMap_llp_le_llp {P : MorphismProperty C} {W : MorphismProperty D}
    (h : W ≤ P.inverseImage G) : P.llp.strictMap F ≤ W.llp := by
  rintro _ _ _ ⟨hi⟩ X Y p hp
  exact (adj.hasLiftingProperty_iff _ p).2 (hi _ (h _ hp))

end Adjunction

end CategoryTheory
