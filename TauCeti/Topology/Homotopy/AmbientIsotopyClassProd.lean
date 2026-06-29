/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Topology.Homotopy.AmbientIsotopyClass
public import TauCeti.Topology.Homotopy.IsotopyProd

/-!
# Products of ambient-isotopy classes

The geometric-topology roadmap asks for isotopy and ambient isotopy to be defined once for
continuous maps, then specialised to geometric knot presentations and other embedding
presentations. `TauCeti.Topology.Homotopy.IsotopyProd` proves that products preserve the
ambient-isotopy relation. This file records the corresponding quotient-level product operation
on continuous ambient-isotopy classes.

This is still a point-set topological construction: it takes classes of continuous maps
`X → Y` and `X' → Y'` to the class of the product map `X × X' → Y × Y'`.

## Main definitions

* `TauCeti.AmbientIsotopyClass.prodMap`: the product of two continuous ambient-isotopy classes.
* `TauCeti.AmbientIsotopyClass.prodMap_mk_mk`: the representative computation rule.
-/

public section

namespace TauCeti

open ContinuousMap

variable {X Y X' Y' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

namespace AmbientIsotopyClass

/-- The product of ambient-isotopy classes of continuous maps.

This is the quotient-level operation induced by `ContinuousMap.prodMap`; product closure of
ambient isotopy is supplied by `TauCeti.AmbientIsotopic.prodMap`. -/
def prodMap :
    AmbientIsotopyClass X Y → AmbientIsotopyClass X' Y' →
      AmbientIsotopyClass (X × X') (Y × Y') :=
  map₂ (fun f g => f.prodMap g) fun {_ _} hff' {_ _} hgg' =>
    AmbientIsotopic.prodMap hff' hgg'

/-- Computation rule for `AmbientIsotopyClass.prodMap` on representatives. -/
@[simp]
theorem prodMap_mk_mk (f : C(X, Y)) (g : C(X', Y')) :
    prodMap (mk f) (mk g) = mk (f.prodMap g) :=
  map₂_mk_mk (fun f g => f.prodMap g)
    (fun {_ _} hff' {_ _} hgg' => AmbientIsotopic.prodMap hff' hgg') f g

end AmbientIsotopyClass

end TauCeti
