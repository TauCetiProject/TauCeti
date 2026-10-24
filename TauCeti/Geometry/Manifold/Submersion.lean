/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Submersion

-- Access the body of `Manifold.IsSubmersionOfComplement`, which Mathlib does not expose, to supply
-- its missing pointwise characterization.
import all Mathlib.Geometry.Manifold.Submersion

/-!
# Submersions are pointwise submersions

A map is a submersion with a fixed complement `F` exactly when it is a submersion with
complement `F` at every point (`Manifold.isSubmersionOfComplement_iff`). Mathlib states only the
forward direction, `Manifold.IsSubmersionOfComplement.isSubmersionAt`, and does not expose the
definition, so the converse is needed to build global submersions from pointwise local normal
forms, for instance with `Manifold.IsSubmersionAtOfComplement.mk_of_continuousAt`.
-/

public section

namespace Manifold

variable {𝕜 E E' F H G M N : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] {f : M → N}

/-- A map is a submersion with complement `F` exactly when it is a submersion with complement `F`
at every point. -/
theorem isSubmersionOfComplement_iff :
    IsSubmersionOfComplement F I J n f ↔ ∀ x, IsSubmersionAtOfComplement F I J n f x :=
  Iff.rfl

end Manifold
