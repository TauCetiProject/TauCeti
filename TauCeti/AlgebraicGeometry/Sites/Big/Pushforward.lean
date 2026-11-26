/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Direct and inverse images of sheaves on big sites

Let `J` be a Grothendieck topology on schemes, such as the étale or the fppf topology, and
`f : Y ⟶ X` a morphism of schemes. Base change `Over.pullback f : Over X ⥤ Over Y` is continuous
for the induced topologies on the big sites, so restriction along it is the direct image of big
`J`-sheaves `f.bigPushforward J A`, sending a sheaf `F` on `Y`-schemes to `T ↦ F(T ×_X Y)`. The
inverse image is Mathlib's `J.overMapPullback A f`, the restriction along `Over.map f`, left
adjoint to the direct image (`f.bigAdjunction J A`) since `Over.map f ⊣ Over.pullback f`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.bigPushforward`: the direct image of big `J`-sheaves along a
  morphism of schemes.
* `AlgebraicGeometry.Scheme.Hom.bigAdjunction`: the inverse image
  `GrothendieckTopology.overMapPullback` is left adjoint to the direct image.
-/

public section

universe v' u u'

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (J : GrothendieckTopology Scheme.{u}) (A : Type u') [Category.{v'} A]
  {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The direct image of big `J`-sheaves along `f : Y ⟶ X`: a sheaf `F` on `Y`-schemes gives the
sheaf `T ↦ F(T ×_X Y)` on `X`-schemes, the restriction along base change `Over.pullback f`, which
is continuous for the induced topologies. -/
noncomputable abbrev Hom.bigPushforward : Sheaf (J.over Y) A ⥤ Sheaf (J.over X) A :=
  (Over.pullback f).sheafPushforwardContinuous A (J.over X) (J.over Y)

/-- The inverse image of big `J`-sheaves along `f`, Mathlib's `J.overMapPullback A f` (a sheaf `G`
on `X`-schemes gives the sheaf `V ↦ G(V)` on `Y`-schemes, regarding a `Y`-scheme as an `X`-scheme
via `f`), is left adjoint to the direct image, as `Over.map f` is left adjoint to
`Over.pullback f`. -/
noncomputable abbrev Hom.bigAdjunction : J.overMapPullback A f ⊣ f.bigPushforward J A :=
  (Over.mapPullbackAdj f).sheafPushforwardContinuous (J.over Y) (J.over X)

end AlgebraicGeometry.Scheme
