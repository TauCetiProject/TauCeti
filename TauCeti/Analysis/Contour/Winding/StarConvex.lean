/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cycle.Winding
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.StarConvex

/-!
# Cycles in a star-shaped set are null-homologous there

A contour cycle drawn inside a set `Ω` that is star-shaped about `x` has winding number `0` about
every point outside `Ω` (`TauCeti.Contour.Cycle.isNullHomologous_of_starConvex`). Each generator is
a closed absolutely continuous curve in `Ω`, which is null-homologous there by
`AbsolutelyContinuousOnInterval.isNullHomologous_of_starConvex`: the straight-line contraction of
the curve to the centre `x` stays in `Ω`, so it avoids every point outside `Ω`.

This discharges the null-homology hypothesis carried by the homology form of Cauchy's theorem for
cycles and by everything built on it, on the domains that ordinary applications supply — a disc, a
half-plane, a strip, a rectangle, the slit plane. Star-shapedness is a condition on the *domain*
alone. The homotopy route, `TauCeti.Contour.isNullHomologous_of_pathHomotopy_refl`, covers strictly
more domains, but asks the caller to exhibit a contracting homotopy; a star-shaped domain supplies
one for free.

## Main results

* `TauCeti.Contour.Cycle.isNullHomologous_of_starConvex` — a contour cycle of closed absolutely
  continuous curves in a star-shaped set is null-homologous there.

A convex `Ω` is star-shaped about any of its points, so a caller holding `hconv : Convex ℝ Ω` and a
point `x ∈ Ω` supplies `hconv.starConvex hx`.

## Provenance

No formalization is vendored. That a cycle in a star-shaped (indeed, in a simply connected) domain
is null-homologous is standard complex analysis; see, e.g., Lang, *Complex Analysis*, Ch. IV.
-/

public section

open Set

namespace TauCeti.Contour

namespace Cycle

/-- **A cycle in a star-shaped set is null-homologous there.** Every generator of the cycle is a
closed absolutely continuous curve confined to `Ω`, so each has vanishing winding number outside
`Ω` by `AbsolutelyContinuousOnInterval.isNullHomologous_of_starConvex`, and the cycle winding number
is their `ℤ`-combination. -/
theorem isNullHomologous_of_starConvex {C : Cycle} {Ω : Set ℂ} {x : ℂ}
    (hstar : StarConvex ℝ x Ω) (hC : IsIn C Ω) : IsNullHomologous C Ω := by
  refine isNullHomologous_iff.mpr fun w hw ↦ ?_
  rw [windingNumber_eq_sum_support]
  refine Finset.sum_eq_zero fun δ hδ ↦ ?_
  rw [TauCeti.Contour.isNullHomologous_iff.mp
    (δ.absolutelyContinuousOnInterval.isNullHomologous_of_starConvex hstar
      δ.source_eq_target (hC.mapsTo_of_mem_support hδ)) w hw, mul_zero]

end Cycle

end TauCeti.Contour

end
