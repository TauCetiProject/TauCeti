/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Genus
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.TopBranchedCover.Basic

/-!
# Euler characteristic and genus of topological branched covers

Isomorphism invariance of `eulerChar X.Z` and `genus X.Z` for finite-CW branched covers.
-/

public noncomputable section

namespace TauCeti.TopBranchedCover

open RiemannSurface

universe u

/-- Isomorphic topological branched covers have the same Euler characteristic. -/
theorem Iso.eulerChar_eq {n : ℕ} {X Y : TopBranchedCover.{u} n} [FiniteCWType X.Z]
    [FiniteCWType Y.Z] (ι : X.Iso Y) : eulerChar X.Z = eulerChar Y.Z := ι.toHomeomorph.eulerChar_eq

/-- Isomorphic topological branched covers have the same topological genus. -/
theorem Iso.genus_eq {n : ℕ} {X Y : TopBranchedCover.{u} n} [FiniteCWType X.Z] [FiniteCWType Y.Z]
    (ι : X.Iso Y) : genus X.Z = genus Y.Z := ι.toHomeomorph.toHomotopyEquiv.genus_eq

end TauCeti.TopBranchedCover
