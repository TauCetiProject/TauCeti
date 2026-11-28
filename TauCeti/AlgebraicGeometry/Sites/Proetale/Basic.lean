/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Basic facts about the small pro-étale site

Facts about the objects of Mathlib's small pro-étale site `X.ProEt` of weakly étale `X`-schemes.

## Main declarations

* `AlgebraicGeometry.Scheme.isEmpty_proEt_left`: a weakly étale scheme over an empty scheme is
  empty, as Tau Ceti's `AlgebraicGeometry.Scheme.isEmpty_etale_left` says for étale schemes.
-/

public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Every scheme weakly étale over an empty scheme is itself empty. -/
instance isEmpty_proEt_left {X : Scheme.{u}} [IsEmpty X] (V : X.ProEt) : IsEmpty V.left :=
  Function.isEmpty (β := X) V.hom

end AlgebraicGeometry.Scheme
