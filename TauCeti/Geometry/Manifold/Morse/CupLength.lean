/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Length
public import TauCeti.Geometry.Manifold.Morse.MinCriticalCount

/-!
# The cup-length bound on critical points

A smooth function `f` on a nonempty compact boundaryless manifold `M` has at least
`cat M + 1` critical points, where `cat M = normalizedLSCategory M` is the normalized
Lusternik–Schnirelmann category (`TauCeti.lsCategoryCount_univ_le_totalCriticalCount`). The
category is bounded below by the cup length of `M` with coefficients in any commutative ring `k`
(`TauCeti.lsCupLength_le_normalizedLSCategory`), so

`#Crit(f) ≥ cat M + 1 ≥ lsCupLength M k + 1`.

No nondegeneracy is assumed, critical points are counted rather than critical values, and an
infinite critical set has count `⊤`. The same bounds hold for the minimal number of critical points
of a smooth function on `M`, `TauCeti.minCriticalCount`.

## Main results

* `TauCeti.normalizedLSCategory_add_one_le_totalCriticalCount` and
  `TauCeti.lsCupLength_add_one_le_totalCriticalCount`: a smooth function on a nonempty compact
  manifold has at least `cat M + 1`, hence at least `lsCupLength M k + 1`, critical points.
* `TauCeti.lsCupLength_add_one_le_minCriticalCount`: the same lower bound for the minimal number
  of critical points.

## References

* L. Lusternik and L. Schnirelmann, *Méthodes topologiques dans les problèmes variationnels*,
  Hermann, Paris, 1934.
* O. Cornea, G. Lupton, J. Oprea and D. Tanré, *Lusternik–Schnirelmann Category*, Mathematical
  Surveys and Monographs 103, American Mathematical Society, 2003, Chapter 1.
-/

public section

open Set
open scoped ContDiff Manifold

universe w

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [CompactSpace M] [Nonempty M]

/-- **The Lusternik–Schnirelmann theorem, normalized.** A smooth function on a nonempty compact
boundaryless manifold `M` has at least `normalizedLSCategory M + 1` critical points. -/
theorem normalizedLSCategory_add_one_le_totalCriticalCount {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) : normalizedLSCategory M + 1 ≤ totalCriticalCount I f := by
  rw [← lsCategoryCount_univ_eq_normalizedLSCategory_add_one]
  exact lsCategoryCount_univ_le_totalCriticalCount hf

/-- **The cup-length bound on critical points.** A smooth function on a nonempty compact
boundaryless manifold `M` has more critical points than the cup length of `M` with coefficients in
any commutative ring `k`. -/
theorem lsCupLength_add_one_le_totalCriticalCount (k : Type w) [CommRing k] {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) : lsCupLength (TopCat.of M) k + 1 ≤ totalCriticalCount I f :=
  (lsCupLength_add_one_le_lsCategoryCount (X := TopCat.of M)).trans
    (lsCategoryCount_univ_le_totalCriticalCount hf)

/-- **The cup-length bound on the minimal number of critical points.** Every smooth function on a
nonempty compact boundaryless manifold `M` has more critical points than the cup length of `M`
with coefficients in any commutative ring `k`. -/
theorem lsCupLength_add_one_le_minCriticalCount (k : Type w) [CommRing k] :
    lsCupLength (TopCat.of M) k + 1 ≤ minCriticalCount I M :=
  (lsCupLength_add_one_le_lsCategoryCount (X := TopCat.of M)).trans
    lsCategoryCount_univ_le_minCriticalCount

end TauCeti
