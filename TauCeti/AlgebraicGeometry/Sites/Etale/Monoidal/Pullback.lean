/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Etale.Monoidal
public import TauCeti.CategoryTheory.Sites.Point.Comap.Monoidal

/-!
# Inverse image of étale sheaves of modules commutes with tensor products

Let `f : X ⟶ Y` be a morphism of schemes and `Λ` a commutative ring. The inverse image
`f^* = f.smallEtalePullback (ModuleCat Λ)` of étale sheaves of `Λ`-modules commutes with tensor
products: the canonical comparison `f^* (F ⊗ G) ⟶ f^* F ⊗ f^* G`
(`CategoryTheory.Functor.sheafPullbackTensorHom`) is an isomorphism. It is checked on stalks at
geometric points `s` of `X`, where it becomes the identity of the tensor product of the stalks of
`F` and `G` at `s ≫ f`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.isIso_smallEtalePullbackTensorHom`: the comparison is an
  isomorphism.
* `AlgebraicGeometry.Scheme.Hom.smallEtalePullbackTensorIso`: the isomorphism
  `f^* (F ⊗ G) ≅ f^* F ⊗ f^* G`.

-/

public section

universe u

open CategoryTheory Limits MonoidalCategory TauCeti.AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type u) [CommRing Λ]

/-- **Inverse image commutes with tensor products.** For a morphism of schemes `f : X ⟶ Y`, the
comparison `f^* (F ⊗ G) ⟶ f^* F ⊗ f^* G` of étale sheaves of `Λ`-modules is an isomorphism. -/
theorem isIso_smallEtalePullbackTensorHom
    (F G : Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) :
    IsIso (f.smallEtaleBaseChange.sheafPullbackTensorHom (ModuleCat.{u} Λ)
      (smallEtaleTopology Y) (smallEtaleTopology X) F G) :=
  isIso_of_forall_isIso_etaleStalk _ fun _ _ _ s ↦
    (pointSmallEtale s).isIso_sheafFiber_map_sheafPullbackTensorHom f.smallEtaleBaseChange
      (f.pointSmallEtaleFiberCompIso s) _ F G

/-- **Inverse image commutes with tensor products.** For a morphism of schemes `f : X ⟶ Y` and
étale sheaves of `Λ`-modules `F` and `G` on `Y`, `f^* (F ⊗ G) ≅ f^* F ⊗ f^* G`. -/
noncomputable def smallEtalePullbackTensorIso
    (F G : Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) :
    (f.smallEtalePullback (ModuleCat.{u} Λ)).obj (F ⊗ G) ≅
      (f.smallEtalePullback (ModuleCat.{u} Λ)).obj F ⊗
        (f.smallEtalePullback (ModuleCat.{u} Λ)).obj G :=
  haveI := f.isIso_smallEtalePullbackTensorHom Λ F G
  asIso (f.smallEtaleBaseChange.sheafPullbackTensorHom (ModuleCat.{u} Λ)
    (smallEtaleTopology Y) (smallEtaleTopology X) F G)

end AlgebraicGeometry.Scheme.Hom
