/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Direct and inverse images of big étale sheaves

For a morphism of schemes `f : Y ⟶ X`, base change `Over.pullback f : Over X ⥤ Over Y` is
continuous for the big étale topologies, so restriction along it is the direct image of big étale
sheaves `f.bigEtalePushforward A`, sending an étale sheaf `F` on `Y`-schemes to
`T ↦ F(T ×_X Y)`. The inverse image `f.bigEtalePullback A` is the restriction along
`Over.map f` (Mathlib's `GrothendieckTopology.overMapPullback`), left adjoint to the direct image
(`f.bigEtaleAdjunction A`) since `Over.map f ⊣ Over.pullback f`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.bigEtalePushforward`,
  `AlgebraicGeometry.Scheme.Hom.bigEtalePullback`: the direct and inverse images of big étale
  sheaves along a morphism of schemes.
* `AlgebraicGeometry.Scheme.Hom.bigEtaleAdjunction`: the inverse image is left adjoint to the
  direct image.
-/

public section

universe v' u u'

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (A : Type u') [Category.{v'} A] {Y : Scheme.{u}} (f : Y ⟶ X)

/-- The direct image of big étale sheaves along `f : Y ⟶ X`: an étale sheaf `F` on `Y`-schemes
gives the étale sheaf `T ↦ F(T ×_X Y)` on `X`-schemes, the restriction along base change
`Over.pullback f`, which is continuous for the étale topologies. -/
noncomputable abbrev Hom.bigEtalePushforward :
    Sheaf (etaleTopology.over Y) A ⥤ Sheaf (etaleTopology.over X) A :=
  (Over.pullback f).sheafPushforwardContinuous A (etaleTopology.over X) (etaleTopology.over Y)

/-- The inverse image of big étale sheaves along `f : Y ⟶ X`: the restriction along `Over.map f`
(Mathlib's `GrothendieckTopology.overMapPullback`). -/
noncomputable abbrev Hom.bigEtalePullback :
    Sheaf (etaleTopology.over X) A ⥤ Sheaf (etaleTopology.over Y) A :=
  etaleTopology.overMapPullback A f

/-- The inverse image of big étale sheaves along `f` is left adjoint to the direct image, as
`Over.map f` is left adjoint to `Over.pullback f`. -/
noncomputable abbrev Hom.bigEtaleAdjunction : f.bigEtalePullback A ⊣ f.bigEtalePushforward A :=
  (Over.mapPullbackAdj f).sheafPushforwardContinuous (etaleTopology.over Y) (etaleTopology.over X)

end AlgebraicGeometry.Scheme
