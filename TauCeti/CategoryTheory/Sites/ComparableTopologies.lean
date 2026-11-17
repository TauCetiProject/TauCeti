/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Sheaves for comparable topologies

Let `J ≤ K` be Grothendieck topologies on a category `C`, so that `K` is finer than `J`. Every
`K`-sheaf is a `J`-sheaf, so the identity functor of `C` is continuous from `J` to `K`
(`TauCeti.CategoryTheory.isContinuous_id_of_le`), and Mathlib's pushforward
`(𝟭 C).sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A` regards a `K`-sheaf as a
`J`-sheaf. This file shows that this pushforward is fully faithful, and that when
`K`-sheafification exists its left adjoint is `K`-sheafification of the underlying presheaf,
`sheafToPresheaf J A ⋙ presheafToSheaf K A`
(`TauCeti.CategoryTheory.sheafifyAdjunctionPushforwardId`), so the pushforward is reflective.
This identifies Mathlib's abstract pullback `(𝟭 C).sheafPullback A J K` with sheafification
(`TauCeti.CategoryTheory.sheafPullbackIdIso`).

For `A = Type _`, this is the morphism of topoi `Sh(C, K) → Sh(C, J)` induced by the identity of
`C`: the pushforward is its direct image and sheafification its inverse image. More generally, the
inverse image preserves finite limits when `A` has finite limits and `K`-sheafification preserves
them (`[HasFiniteLimits A] [HasSheafify K A]`).

For instance, the small Nisnevich topology of a scheme is coarser than its small étale topology,
and this gives the comparison morphism of topoi from étale sheaves to Nisnevich sheaves.

## Main declarations

* `TauCeti.CategoryTheory.isContinuous_id_of_le`: for `J ≤ K`, the identity is continuous.
* `TauCeti.CategoryTheory.fullyFaithfulSheafPushforwardContinuousId`: the pushforward of sheaves
  along the identity is fully faithful.
* `TauCeti.CategoryTheory.sheafifyAdjunctionPushforwardId`: `K`-sheafification of `J`-sheaves is
  left adjoint to the pushforward along the identity.

## References

* A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IV, §4, for morphisms of topoi.
-/

public section

universe v u v' u'

open CategoryTheory Limits GrothendieckTopology

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] {J K : GrothendieckTopology C}

/-- For topologies `J ≤ K`, every `K`-sheaf is a `J`-sheaf, so the identity functor is continuous
from `J` to `K`. -/
theorem isContinuous_id_of_le (h : J ≤ K) : (𝟭 C).IsContinuous J K where
  op_comp_isSheaf_of_types G :=
    Presieve.isSheaf_of_le _ h ((isSheaf_iff_isSheaf_of_type _ _).1 G.2)

variable (J K) (A : Type u') [Category.{v'} A] [(𝟭 C).IsContinuous J K]

/-- The pushforward of sheaves along the identity functor, which regards a `K`-sheaf as a
`J`-sheaf, is fully faithful. -/
def fullyFaithfulSheafPushforwardContinuousId :
    ((𝟭 C).sheafPushforwardContinuous A J K).FullyFaithful where
  preimage f := ⟨f.hom⟩

instance fullSheafPushforwardContinuousId : ((𝟭 C).sheafPushforwardContinuous A J K).Full :=
  (fullyFaithfulSheafPushforwardContinuousId J K A).full

instance faithfulSheafPushforwardContinuousId :
    ((𝟭 C).sheafPushforwardContinuous A J K).Faithful :=
  (fullyFaithfulSheafPushforwardContinuousId J K A).faithful

variable [HasWeakSheafify K A]

/-- `K`-sheafification of the presheaf underlying a `J`-sheaf is left adjoint to the pushforward
of sheaves along the identity, which regards a `K`-sheaf as a `J`-sheaf. It is the restriction of
the sheafification adjunction for `K` to `J`-sheaves. For `A = Type _`, this is the morphism of
topoi `Sh(C, K) → Sh(C, J)` induced by the identity of `C`, with inverse image
`sheafToPresheaf J A ⋙ presheafToSheaf K A`. -/
noncomputable def sheafifyAdjunctionPushforwardId :
    sheafToPresheaf J A ⋙ presheafToSheaf K A ⊣ (𝟭 C).sheafPushforwardContinuous A J K :=
  (sheafificationAdjunction K A).restrictFullyFaithful (fullyFaithfulSheafToPresheaf J A)
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

@[simp]
theorem sheafifyAdjunctionPushforwardId_unit_app_hom (F : Sheaf J A) :
    ((sheafifyAdjunctionPushforwardId J K A).unit.app F).hom = toSheafify K F.obj := by
  have := (sheafificationAdjunction K A).map_restrictFullyFaithful_unit_app
    (L := sheafToPresheaf J A ⋙ presheafToSheaf K A)
    (R := (𝟭 C).sheafPushforwardContinuous A J K)
    (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _) F
  simp only [Functor.id_obj, Functor.comp_obj, sheafificationAdjunction_unit_app, Iso.refl_hom,
    NatTrans.id_app] at this
  refine this.trans ?_
  erw [Category.comp_id, Category.comp_id]
  rfl

@[simp]
theorem sheafifyAdjunctionPushforwardId_counit_app_hom (G : Sheaf K A) :
    ((sheafifyAdjunctionPushforwardId J K A).counit.app G).hom =
      sheafifyLift K (𝟙 G.obj) G.property := by
  have := (sheafificationAdjunction K A).map_restrictFullyFaithful_counit_app
    (L := sheafToPresheaf J A ⋙ presheafToSheaf K A)
    (R := (𝟭 C).sheafPushforwardContinuous A J K)
    (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _) G
  simp only [Functor.comp_obj, Functor.id_obj, Functor.id_map, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp] at this
  rw [← sheafificationAdjunction_counit_app_val, sheafifyAdjunctionPushforwardId]
  erw [this, CategoryTheory.Functor.map_id, Category.id_comp]

noncomputable instance reflectiveSheafPushforwardContinuousId :
    Reflective ((𝟭 C).sheafPushforwardContinuous A J K) where
  L := sheafToPresheaf J A ⋙ presheafToSheaf K A
  adj := sheafifyAdjunctionPushforwardId J K A

/-- Mathlib's pullback of sheaves along the identity functor, defined abstractly as the left
adjoint of the pushforward, is `K`-sheafification of the underlying presheaf. -/
noncomputable def sheafPullbackIdIso :
    (𝟭 C).sheafPullback A J K ≅ sheafToPresheaf J A ⋙ presheafToSheaf K A :=
  ((𝟭 C).sheafAdjunctionContinuous A J K).leftAdjointUniq (sheafifyAdjunctionPushforwardId J K A)

end TauCeti.CategoryTheory
