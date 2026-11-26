/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.FirstPage

/-!
# The first page of the spectral sequence of a spectral object with finitely many rows

For `l : ℕ` and a spectral object `X` indexed by `Fin (l + 1)`, Mathlib's recipe
`coreE₂CohomologicalFin l` gives a spectral sequence starting on the page `2`, with objects at
`(p, q) : ℤ × Fin l`. On the page `r` the object at `(p, q)` is `E^{p+q}(i₀ ≤ q ≤ q + 1 ≤ i₃)` with
the clamped indices `i₀ = max(0, q - r + 2)` and `i₃ = min(l, q + r - 1)`. On the page `2` these
are `i₀ = q` and `i₃ = q + 1`, since `q < l`. So the recipe satisfies
`SpectralSequenceDataCore.HasFirstPageComputation`
(`SpectralSequenceDataCore.instHasFirstPageComputationCoreE₂CohomologicalFin`), and Mathlib's
`spectralSequenceFirstPageXIso` identifies the object at `(p, q)` on the page `2` with
`H^{p+q}(q ≤ q + 1)`, as for the recipes on `EInt`.

## References

* G. O. Helle and J. Rognes, *Boardman's whole-plane obstruction group for Cartan–Eilenberg
  systems*, Documenta Math. 24 (2019), 1855–1878, Definition 4.5 and Remark 4.6.
-/

public section

namespace CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore

/-- The recipe `coreE₂CohomologicalFin l` has the indices `i₀ = i₁` and `i₂ = i₃` on its first
page `2`, so its first page is computed by the objects `H^n(q ≤ q + 1)`. -/
instance instHasFirstPageComputationCoreE₂CohomologicalFin (l : ℕ) :
    (coreE₂CohomologicalFin l).HasFirstPageComputation where
  hi₀₁ pq := by
    ext
    simp
  hi₂₃ pq := by
    ext
    simp [Fin.clamp]
    lia

end CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore
