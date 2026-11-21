/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Closed inclusions and local Noetherianity of scheme coproducts

The summands of a scheme coproduct are open and closed. The open cover by the summands
transfers local Noetherianity to the coproduct, without a finiteness condition on the index type.
-/

public section

open CategoryTheory Limits Set

namespace AlgebraicGeometry

universe u

variable {ι : Type u} (X : ι → Scheme.{u})

/-- The summand inclusions of a scheme coproduct are also closed immersions. -/
instance isClosedImmersion_sigmaι (i : ι) : IsClosedImmersion (Sigma.ι X i) := by
  apply IsClosedImmersion.of_isPreimmersion
  simpa only [← range_comp, Function.comp_def, sigmaMk_mk] using
    (sigmaMk X).isClosedMap _ (isClosed_range_sigmaMk (σ := fun j ↦ X j) (i := i))

/-- A coproduct of locally Noetherian schemes is locally Noetherian. -/
instance isLocallyNoetherian_sigma [h : ∀ i, IsLocallyNoetherian (X i)] :
    IsLocallyNoetherian (∐ X) :=
  (isLocallyNoetherian_iff_openCover (sigmaOpenCover X)).2 fun i ↦ h i

end AlgebraicGeometry
