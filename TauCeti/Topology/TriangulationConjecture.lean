/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ChartedSpace
public import TauCeti.Topology.Triangulable

/-!
# The triangulation conjecture

The **triangulation conjecture** in dimension `n` asserts that every closed topological
`n`-manifold is homeomorphic to the geometric realization of an abstract simplicial complex.
Here a closed topological `n`-manifold is a compact Hausdorff space carrying charts to
`EuclideanSpace ℝ (Fin n)`; no smooth, PL, or other compatibility of the transition maps is
imposed. Second countability is not assumed separately, since a compact space locally
homeomorphic to Euclidean space is second countable
(`ChartedSpace.secondCountable_of_sigmaCompact`). The Hausdorff hypothesis is essential: a
realization is Hausdorff, so without it a compact non-Hausdorff locally Euclidean space would
refute the conjecture for a trivial reason.

The conclusion uses the general predicate `TauCeti.IsTriangulable`, which imposes no link
condition on the triangulating complex. This is the form relevant to Manolescu's theorem:
for every `n ≥ 5` there is a closed topological `n`-manifold admitting no triangulation at all,
that is `∀ n, 5 ≤ n → ¬ TauCeti.TriangulationConjecture n`. The older Kirby–Siebenmann result
instead gives the weaker conclusion that some manifolds admit no combinatorial triangulation;
combinatorial triangulability (`TauCeti.IsCombinatoriallyTriangulable`) is itself the stronger
notion because it imposes an additional link condition.

The conjecture is stated, not proved. It holds in dimension zero, where every such space is
discrete (`TauCeti.triangulationConjecture_zero`); it is also known in dimensions at most three
(Radó, Moise), fails in dimension four by the work of Freedman and Casson, and fails in every
dimension at least five by Manolescu.

## Main definitions

* `TauCeti.TriangulationConjecture`: every closed topological `n`-manifold is triangulable.

## Main results

* `TauCeti.not_triangulationConjecture_iff`: a disproof is a closed topological manifold that is
  not triangulable, the shape of Manolescu's theorem.
* `TauCeti.isTriangulable_of_chartedSpace_zero`: every space locally homeomorphic to `ℝ⁰` is
  triangulable.
* `TauCeti.triangulationConjecture_zero`: the conjecture holds in dimension zero.

## References

* C. Manolescu, *Pin(2)-equivariant Seiberg-Witten Floer homology and the triangulation
  conjecture*, J. Amer. Math. Soc. 29 (2016), 147–176.
* D. Galewski, R. Stern, *Classification of simplicial triangulations of topological manifolds*,
  Ann. of Math. 111 (1980), 1–34.
* S. Akbulut, J. McCarthy, *Casson's invariant for oriented homology 3-spheres: an exposition*,
  Princeton University Press (1990).
* E. E. Moise, *Geometric Topology in Dimensions 2 and 3*, Springer GTM 47 (1977).
-/

public section

noncomputable section

namespace TauCeti

universe u

/-- The **triangulation conjecture** in dimension `n`: every compact Hausdorff space locally
homeomorphic to `ℝⁿ` (a closed topological `n`-manifold) is homeomorphic to the geometric
realization of an abstract simplicial complex.

Manolescu proved that this fails for every `n ≥ 5`. -/
def TriangulationConjecture.{v} (n : ℕ) : Prop :=
  ∀ (M : Type v) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M], IsTriangulable.{v} M

/-- The triangulation conjecture fails in dimension `n` exactly when some closed topological
`n`-manifold is not triangulable. This is the shape of Manolescu's theorem. -/
@[simp]
theorem not_triangulationConjecture_iff {n : ℕ} :
    ¬ TriangulationConjecture.{u} n ↔
      ∃ (M : Type u) (_ : TopologicalSpace M) (_ : T2Space M) (_ : CompactSpace M)
        (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M), ¬ IsTriangulable.{u} M := by
  simp only [TriangulationConjecture, not_forall, exists_prop]

/-- Every topological space locally homeomorphic to the zero-dimensional Euclidean space is
triangulable. -/
theorem isTriangulable_of_chartedSpace_zero (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M] : IsTriangulable.{u} M := by
  have := ChartedSpace.discreteTopology (EuclideanSpace ℝ (Fin 0)) M
  exact isTriangulable_of_discreteTopology M

/-- The triangulation conjecture holds in dimension zero: a space locally homeomorphic to the
one-point space `ℝ⁰` is discrete, hence triangulated by its points. -/
@[simp]
theorem triangulationConjecture_zero : TriangulationConjecture.{u} 0 := by
  intro M _ _ _ _
  exact isTriangulable_of_chartedSpace_zero M

end TauCeti
