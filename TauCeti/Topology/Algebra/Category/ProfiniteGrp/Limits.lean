/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

/-!
# Morphisms into a profinite group as a limit

A profinite group `H` is the limit of its finite quotients `H ⧸ N` over the open normal subgroups
`N` (`ProfiniteGrp.isLimitCone`). Its finite quotients are finite, and continuous homomorphisms
from a profinite group `X` into `H` are the compatible families of continuous homomorphisms from
`X` into the quotients `H ⧸ N`.

## Main definitions

* `ProfiniteGrp.homLimitIso X H`: the bijection
  `(X ⟶ H) ≅ lim_N (X ⟶ H ⧸ N)`.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace ProfiniteGrp

/-- The quotient of a profinite group by an open normal subgroup is finite. -/
instance (H : ProfiniteGrp.{u}) (N : OpenNormalSubgroup H) : Finite (H.diagram.obj N) :=
  (H.toFiniteQuotientFunctor.obj N).isFinite

/-- Continuous homomorphisms from a profinite group `X` into a profinite group `H` are the
compatible families of continuous homomorphisms from `X` into the finite quotients of `H`. -/
def homLimitIso (X H : ProfiniteGrp.{u}) :
    (X ⟶ H) ≅ Limits.limit (H.diagram ⋙ coyoneda.obj (op X)) :=
  (isLimitOfPreserves (coyoneda.obj (op X)) H.isLimitCone).conePointUniqueUpToIso
    (Limits.limit.isLimit _)

/-- The coordinate of `homLimitIso X H` at an open normal subgroup `N` of `H` is composition with
the projection `H → H ⧸ N`. -/
@[reassoc]
theorem homLimitIso_hom_π (X H : ProfiniteGrp.{u}) (N : OpenNormalSubgroup H) :
    (homLimitIso X H).hom ≫ Limits.limit.π _ N = (coyoneda.obj (op X)).map (proj N) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ N

end ProfiniteGrp
