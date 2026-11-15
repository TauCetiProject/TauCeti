/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.SmallObject.Basic
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda

/-!
# The small object argument for monomorphisms in Grothendieck abelian categories

Let `C` be a Grothendieck abelian category and `I` a `w`-small family of monomorphisms of `C`.
Then `I` permits the small object argument
(`CategoryTheory.IsGrothendieckAbelian.hasSmallObjectArgument_of_le_monomorphisms`). Hence every
morphism of `C` factors functorially as a morphism in `I.rlp.llp` followed by a morphism in
`I.rlp`. More precisely, any regular cardinal `κ` such that the sources of the morphisms in `I`
have fewer than `κ` subobjects is suitable for the small object argument
(`CategoryTheory.IsGrothendieckAbelian.isCardinalForSmallObjectArgument_of_le_monomorphisms`);
since `C` is well-powered, such a cardinal exists.

The point is that relative `I`-cell complexes are transfinite compositions of monomorphisms,
because monomorphisms are stable under coproducts, pushouts and transfinite compositions in `C`,
and that `Hom(A, -)` commutes with the colimits of such chains when `A` has fewer than `κ`
subobjects. The inclusions of the subobjects of a generator form such a family; this is how
Grothendieck abelian categories are shown to have enough injectives. Families of monomorphic
quasi-isomorphisms of cochain complexes give K-injective resolutions in the same way.

## References

* The instance `HasSmallObjectArgument (generatingMonomorphisms G)` in Mathlib's
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`, by Joël Riou, which is
  the case of the inclusions of the subobjects of `G` and whose proof this file follows.
-/

public section

universe w v u

namespace CategoryTheory.IsGrothendieckAbelian

open Limits MorphismProperty

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- In a Grothendieck abelian category, a regular cardinal `κ` is suitable for the small object
argument applied to a `w`-small family of monomorphisms whose sources have fewer than `κ`
subobjects. -/
lemma isCardinalForSmallObjectArgument_of_le_monomorphisms (I : MorphismProperty C)
    [IsSmall.{w} I] (hI : I ≤ monomorphisms C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [OrderBot κ.ord.ToType]
    (hIκ : ∀ ⦃A B : C⦄ (i : A ⟶ B), I i → HasCardinalLT (Subobject A) κ) :
    IsCardinalForSmallObjectArgument.{w} I κ where
  preservesColimit {A B X Y} i hi f hf := by
    let hf' : (monomorphisms C).TransfiniteCompositionOfShape κ.ord.ToType f :=
      { toTransfiniteCompositionOfShape := hf.toTransfiniteCompositionOfShape
        map_mem j hj := by
          have := (hf.attachCells j hj).pushouts_coproducts
          simp only [ofHoms_homFamily] at this
          refine (?_ : _ ≤ monomorphisms C) _ this
          simpa only [pushouts_le_iff, coproducts_le_iff] using hI }
    have (j j' : κ.ord.ToType) (φ : j ⟶ j') : Mono (hf'.F.map φ) := hf'.mem_map φ
    exact preservesColimit_coyoneda_obj_of_mono (Y := hf'.F) (κ := κ) (hIκ i hi)

/-- In a Grothendieck abelian category, a `w`-small family of monomorphisms permits the small
object argument. -/
lemma hasSmallObjectArgument_of_le_monomorphisms (I : MorphismProperty C) [IsSmall.{w} I]
    (hI : I ≤ monomorphisms C) : HasSmallObjectArgument.{w} I := by
  obtain ⟨κ, hκ, hIκ⟩ :=
    HasCardinalLT.exists_regular_cardinal_forall.{w} fun f : I.toSet ↦ Subobject f.1.left
  have : Fact κ.IsRegular := ⟨hκ⟩
  have : Nonempty κ.ord.ToType := by simpa using hκ.ne_zero
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  exact ⟨κ, inferInstance, inferInstance,
    isCardinalForSmallObjectArgument_of_le_monomorphisms I hI κ fun A B i hi ↦
      hIκ ⟨Arrow.mk i, hi⟩⟩

end CategoryTheory.IsGrothendieckAbelian
