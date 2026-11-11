/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Scheme.ConnectedComponent
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Connected components of finite étale schemes

Every connected component of a scheme finite étale over a locally Noetherian base is an
open and closed subscheme, finite étale over the same base. This permits treating components
of finite locally constant étale sheaves as finite étale schemes in their own right.
No geometric unibranchness or quasi-compactness of the base is required.

Local Noetherianness of the base makes the source locally Noetherian and hence locally
connected. The component inclusion is then both open and closed: closedness preserves
finiteness of the composite, while openness preserves étaleness.

## References

* The Stacks Project, Lemma 59.64.4 (03RV), finite locally constant sheaves and
  finite étale schemes.
* The Stacks Project, Lemma 5.9.6 (04MF), locally Noetherian spaces are locally connected.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {Y X : Scheme.{u}}

/-- Every connected component of a finite étale scheme with locally connected source is an
open and closed subscheme, finite étale over the same base. The component carries its full
open-subscheme structure, not its reduction. -/
theorem exists_connectedComponent_finite_etale (p : Y ⟶ X) [IsFinite p] [Etale p]
    [LocallyConnectedSpace Y] (y : Y) :
    ∃ U : Y.Opens, (U : Set Y) = connectedComponent y ∧ IsClosed (U : Set Y) ∧
      IsFinite (U.ι ≫ p) ∧ Etale (U.ι ≫ p) :=
  ⟨Y.connectedComponentOpen y, Y.coe_connectedComponentOpen y,
    by simpa using (isClosed_connectedComponent (x := y)), inferInstance, inferInstance⟩

-- In particular, the hypothesis holds for a finite étale scheme over a locally Noetherian base.
example (p : Y ⟶ X) [IsFinite p] [Etale p] [IsLocallyNoetherian X] (y : Y) :
    ∃ U : Y.Opens, (U : Set Y) = connectedComponent y ∧ IsClosed (U : Set Y) ∧
      IsFinite (U.ι ≫ p) ∧ Etale (U.ι ≫ p) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  exact p.exists_connectedComponent_finite_etale y

end AlgebraicGeometry.Scheme.Hom
