/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Sheaves for comparable topologies

Let `J ≤ K` be Grothendieck topologies on a category `C`, so that `K` is finer than `J`. Every
`K`-sheaf is a `J`-sheaf, which gives the fully faithful inclusion
`CategoryTheory.GrothendieckTopology.sheafInclusionOfLE h A : Sheaf K A ⥤ Sheaf J A`. When
`K`-sheafification exists, its left adjoint is `K`-sheafification of the underlying presheaf,
`sheafToPresheaf J A ⋙ presheafToSheaf K A`
(`CategoryTheory.GrothendieckTopology.sheafifyAdjunctionOfLE`). This is the morphism of topoi
`Sh(C, K) → Sh(C, J)` induced by the identity of `C`: the inclusion is its direct image and
sheafification its inverse image, which preserves finite limits whenever `K`-sheafification does.
The counit of the adjunction is an isomorphism because the inclusion is fully faithful
(Mathlib's `CategoryTheory.Adjunction.counit_isIso_of_R_fully_faithful`).

For instance, the small Nisnevich topology of a scheme is coarser than its small étale topology,
and this gives the comparison morphism of topoi from étale sheaves to Nisnevich sheaves.

## Main declarations

* `CategoryTheory.GrothendieckTopology.sheafInclusionOfLE`: `K`-sheaves as `J`-sheaves.
* `CategoryTheory.GrothendieckTopology.sheafifyAdjunctionOfLE`: `K`-sheafification of `J`-sheaves
  is left adjoint to `sheafInclusionOfLE`.

## References

* A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IV, §4, for morphisms of topoi.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J K : GrothendieckTopology C} (h : J ≤ K)
  (A : Type u') [Category.{v'} A]

/-- For topologies `J ≤ K`, every `K`-sheaf is a `J`-sheaf: the direct image of the morphism of
topoi `Sh(C, K) → Sh(C, J)` induced by the identity of `C`. -/
abbrev sheafInclusionOfLE : Sheaf K A ⥤ Sheaf J A :=
  ObjectProperty.ιOfLE fun _ hF ↦ hF.of_le h

/-- The inclusion of `K`-sheaves into `J`-sheaves does not change underlying presheaves. -/
def sheafInclusionOfLECompSheafToPresheafIso :
    sheafInclusionOfLE h A ⋙ sheafToPresheaf J A ≅ sheafToPresheaf K A :=
  Iso.refl _

variable [HasWeakSheafify K A]

/-- For topologies `J ≤ K`, `K`-sheafification of the presheaf underlying a `J`-sheaf is left
adjoint to the inclusion of `K`-sheaves into `J`-sheaves. It is the restriction of the
sheafification adjunction for `K` to `J`-sheaves. This is the morphism of topoi
`Sh(C, K) → Sh(C, J)` induced by the identity of `C`, with inverse image
`sheafToPresheaf J A ⋙ presheafToSheaf K A`. -/
noncomputable def sheafifyAdjunctionOfLE :
    sheafToPresheaf J A ⋙ presheafToSheaf K A ⊣ sheafInclusionOfLE h A :=
  (sheafificationAdjunction K A).restrictFullyFaithful (fullyFaithfulSheafToPresheaf J A)
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

end CategoryTheory.GrothendieckTopology
