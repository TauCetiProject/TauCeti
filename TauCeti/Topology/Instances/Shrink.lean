/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Shrink
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Compactness and the Hausdorff property of `Shrink X`

`Shrink X` carries the topology transported along `equivShrink X`, so it is homeomorphic to `X`
(`Shrink.homeomorph`). It is therefore compact, respectively Hausdorff, when `X` is. With these
instances a `v`-small compact Hausdorff space `X` gives an object `CompHaus.of (Shrink.{v} X)` of
the category of compact Hausdorff spaces in universe `v`, through which a construction in that
category can reach spaces of other universes.
-/

public section

universe v u

namespace Shrink

variable (X : Type u) [TopologicalSpace X] [Small.{v} X]

instance [CompactSpace X] : CompactSpace (Shrink.{v} X) :=
  (homeomorph X).compactSpace

instance [T2Space X] : T2Space (Shrink.{v} X) :=
  (homeomorph X).symm.isEmbedding.t2Space

end Shrink
