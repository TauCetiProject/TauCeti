/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless
public import TauCeti.Geometry.Manifold.RegularValue
import TauCeti.Geometry.Manifold.RegularValue.Diffeomorph

/-!
# Regular points and values under boundaryless model transport

Replacing a boundaryless source model `I` on `M` by its vector-space-modelled copy
`TauCeti.BoundarylessModel I M` preserves regular points and regular values of maps into any
charted target `(N, J)`, with no manifold smoothness or finite-dimensionality assumption.

## Main results

* `TauCeti.BoundarylessModel.isRegularPoint_comp_homeomorph_symm_iff`: precomposing with
  `(TauCeti.BoundarylessModel.homeomorph I M).symm` preserves regular points.
* `TauCeti.BoundarylessModel.isRegularValue_comp_homeomorph_symm_iff`: precomposing with
  `(TauCeti.BoundarylessModel.homeomorph I M).symm` preserves regular values.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.BoundarylessModel

variable {𝕜 E H M E' G N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace G] {J : ModelWithCorners 𝕜 E' G}
  [TopologicalSpace N] [ChartedSpace G N]

/-- Replacing a boundaryless source model `(M, I)` by `BoundarylessModel I M` preserves regular
points. -/
@[simp]
theorem isRegularPoint_comp_homeomorph_symm_iff (f : M → N) (x : BoundarylessModel I M) :
    IsRegularPoint 𝓘(𝕜, E) J (f ∘ (homeomorph I M).symm) x ↔
      IsRegularPoint I J f ((homeomorph I M).symm x) := by
  simpa only [coe_diffeomorph_symm] using
    (diffeomorph I (M := M) 1).symm.isRegularPoint_comp_iff one_ne_zero
      (J := J) (f := f) (x := x)

/-- Replacing a boundaryless source model `(M, I)` by `BoundarylessModel I M` preserves regular
values. -/
@[simp]
theorem isRegularValue_comp_homeomorph_symm_iff (f : M → N) (y : N) :
    IsRegularValue 𝓘(𝕜, E) J (f ∘ (homeomorph I M).symm) y ↔ IsRegularValue I J f y := by
  simpa only [coe_diffeomorph_symm] using
    (diffeomorph I (M := M) 1).symm.isRegularValue_comp_iff one_ne_zero
      (J := J) (f := f) (y := y)

end TauCeti.BoundarylessModel
