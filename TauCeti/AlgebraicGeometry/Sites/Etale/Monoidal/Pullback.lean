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
`f^* = f.smallEtalePullback (ModuleCat Λ)` of étale sheaves of `Λ`-modules is oplax monoidal, as
the left adjoint of the lax monoidal pushforward
(`CategoryTheory.Functor.sheafPullbackOplaxMonoidal`), and it commutes with tensor products: its
tensor comparison
`OplaxMonoidal.δ f^* F G : f^* (F ⊗ G) ⟶ f^* F ⊗ f^* G` is an isomorphism, and so is its unit
comparison `OplaxMonoidal.η f^* : f^* 𝟙_ ⟶ 𝟙_`. Both are checked on stalks at geometric points
`s` of `X`: there the stalks of `f^* F` and `f^* G` are the stalks of `F` and `G` at `s ≫ f`, and
the comparisons are isomorphisms on every such stalk.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.isIso_smallEtalePullback_δ`: the tensor comparison of `f^*` is
  an isomorphism.
* `AlgebraicGeometry.Scheme.Hom.isIso_smallEtalePullback_η`: the unit comparison of `f^*` is an
  isomorphism.
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.OplaxMonoidal TauCeti.AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type u) [CommRing Λ]

/-- **Inverse image commutes with tensor products.** For a morphism of schemes `f : X ⟶ Y`, the
tensor comparison `f^* (F ⊗ G) ⟶ f^* F ⊗ f^* G` of étale sheaves of `Λ`-modules is an
isomorphism. -/
instance isIso_smallEtalePullback_δ (F G : Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) :
    IsIso (δ (f.smallEtalePullback (ModuleCat.{u} Λ)) F G) :=
  isIso_of_forall_isIso_etaleStalk _ fun _ _ _ s ↦
    (pointSmallEtale s).isIso_sheafFiber_map_sheafPullback_δ f.smallEtaleBaseChange
      (f.pointSmallEtaleFiberCompIso s) _ F G

/-- **Inverse image preserves the unit.** For a morphism of schemes `f : X ⟶ Y`, the unit
comparison `f^* 𝟙_ ⟶ 𝟙_` of étale sheaves of `Λ`-modules is an isomorphism. -/
instance isIso_smallEtalePullback_η : IsIso (η (f.smallEtalePullback (ModuleCat.{u} Λ))) :=
  isIso_of_forall_isIso_etaleStalk _ fun _ _ _ s ↦
    (pointSmallEtale s).isIso_sheafFiber_map_sheafPullback_η f.smallEtaleBaseChange
      (f.pointSmallEtaleFiberCompIso s) _

end AlgebraicGeometry.Scheme.Hom
