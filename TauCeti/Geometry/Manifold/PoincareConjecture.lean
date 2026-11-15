/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PoincareConjecture
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Noncompact
public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected

/-!
# Topological hypotheses detected by a homotopy equivalence to a sphere

Mathlib states the smooth generalized Poincaré conjecture as
`ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n`: any Hausdorff smooth `n`-manifold `M`
homotopy equivalent to the unit sphere `Sⁿ` is diffeomorphic to `Sⁿ`, without assuming upfront that
`M` is compact, connected, simply connected, or second countable.

Combining the manifold compactness and second-countability transfers in
`TauCeti.AlgebraicTopology.Singular.LocalHomology.Noncompact`
(`ContinuousMap.HomotopyEquiv.compactSpace_of_sphere`,
`ContinuousMap.HomotopyEquiv.secondCountableTopology_of_sphere`) with the general sphere
connectivity transfers in `TauCeti.AlgebraicTopology.Sphere.SimplyConnected`
(`ContinuousMap.HomotopyEquiv.pathConnectedSpace_of_sphere`,
`ContinuousMap.HomotopyEquiv.simplyConnectedSpace_of_sphere`), this file reduces both the smooth
statement `ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n` and its topological
counterpart on a fixed `[ChartedSpace E M]` (for real normed spaces `E` of dimension `n` and `F`
of dimension `n + 1`, in possibly different universes):

* **Reductions for `1 ≤ n`.** Both the smooth and topological statements reduce to compact
  path-connected second-countable manifolds
  (`TauCeti.nonemptyDiffeomorphSphere_iff_of_one_le`,
  `TauCeti.nonempty_homeomorph_sphere_of_homotopyEquiv_iff_of_one_le`).
* **Reductions for `2 ≤ n`.** Both the smooth and topological statements reduce to compact simply
  connected second-countable manifolds
  (`TauCeti.nonemptyDiffeomorphSphere_iff_of_two_le`,
  `TauCeti.nonemptyDiffeomorphSphere_of_two_le_of_forall`,
  `TauCeti.nonempty_homeomorph_sphere_of_homotopyEquiv_iff_of_two_le`,
  `TauCeti.nonempty_homeomorph_sphere_of_homotopyEquiv_of_two_le_of_forall`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Proposition 3.29.
-/

public section

noncomputable section

open Metric Module
open scoped ContinuousMap ContDiff Manifold

namespace TauCeti

section PoincareConjecture

/-- For `1 ≤ n`, Mathlib's smooth Poincaré statement
`ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n` is equivalent to the same statement
restricted to compact path-connected second-countable smooth `n`-manifolds. -/
theorem nonemptyDiffeomorphSphere_iff_of_one_le (M : Type*) [TopologicalSpace M] [T2Space M]
    {n : ℕ} (hn : 1 ≤ n) :
    ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n ↔
      ∀ (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M) (_ : IsManifold (𝓡 n) ∞ M)
        [CompactSpace M] [PathConnectedSpace M] [SecondCountableTopology M],
        (M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) →
          Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  constructor
  · intro h c hm _ _ _ e
    exact h c hm e
  · intro h c hm e
    have hF : finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := finrank_euclideanSpace_fin
    have := e.compactSpace_of_sphere (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) hF
    have := e.pathConnectedSpace_of_sphere (one_lt_rank_of_one_lt_finrank (by omega)) zero_le_one
    have := e.secondCountableTopology_of_sphere (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) hF
    exact h c hm e

/-- For `2 ≤ n`, Mathlib's smooth Poincaré statement
`ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n` is equivalent to the same statement
restricted to compact simply connected second-countable smooth `n`-manifolds. -/
theorem nonemptyDiffeomorphSphere_iff_of_two_le (M : Type*) [TopologicalSpace M] [T2Space M]
    {n : ℕ} (hn : 2 ≤ n) :
    ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n ↔
      ∀ (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M) (_ : IsManifold (𝓡 n) ∞ M)
        [CompactSpace M] [SimplyConnectedSpace M] [SecondCountableTopology M],
        (M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) →
          Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  constructor
  · intro h c hm _ _ _ e
    exact h c hm e
  · intro h c hm e
    have hF : finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := finrank_euclideanSpace_fin
    have := e.compactSpace_of_sphere (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) hF
    have hrank : 2 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
      simpa using lt_rank_of_lt_finrank (R := ℝ) (M := EuclideanSpace ℝ (Fin (n + 1)))
        (n := 2) (by omega)
    have := e.simplyConnectedSpace_of_sphere hrank zero_le_one
    have := e.secondCountableTopology_of_sphere (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) hF
    exact h c hm e

/-- For `2 ≤ n`, if every compact simply connected second-countable smooth `n`-manifold structure on
`M` is diffeomorphic to `Sⁿ`, then `ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n`
holds. -/
theorem nonemptyDiffeomorphSphere_of_two_le_of_forall (M : Type*) [TopologicalSpace M]
    [T2Space M] {n : ℕ} (hn : 2 ≤ n)
    (h : ∀ (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M) (_ : IsManifold (𝓡 n) ∞ M)
      [CompactSpace M] [SimplyConnectedSpace M] [SecondCountableTopology M],
      Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n := by
  refine (nonemptyDiffeomorphSphere_iff_of_two_le M hn).2 ?_
  intro c hm _ _ _ _
  exact h c hm

/-- For `1 ≤ n`, the topological generalized Poincaré statement on a Hausdorff `n`-manifold `M`
(homotopy equivalence to `Sⁿ` implies homeomorphism to `Sⁿ`) is equivalent to the same statement
assuming `M` is compact, path-connected, and second countable. -/
theorem nonempty_homeomorph_sphere_of_homotopyEquiv_iff_of_one_le (M : Type*)
    [TopologicalSpace M] [T2Space M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) (hn : 1 ≤ n) :
    ((M ≃ₕ sphere (0 : F) 1) → Nonempty (M ≃ₜ sphere (0 : F) 1)) ↔
      ∀ [CompactSpace M] [PathConnectedSpace M] [SecondCountableTopology M],
        (M ≃ₕ sphere (0 : F) 1) → Nonempty (M ≃ₜ sphere (0 : F) 1) := by
  constructor
  · intro h _ _ _ e
    exact h e
  · intro h e
    have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
    have := e.compactSpace_of_sphere hE hF
    have := e.pathConnectedSpace_of_sphere (one_lt_rank_of_one_lt_finrank (by omega)) zero_le_one
    have := e.secondCountableTopology_of_sphere hE hF
    exact h e

/-- For `2 ≤ n`, the topological generalized Poincaré statement on a Hausdorff `n`-manifold `M`
(homotopy equivalence to `Sⁿ` implies homeomorphism to `Sⁿ`) is equivalent to the same statement
assuming `M` is compact, simply connected, and second countable. -/
theorem nonempty_homeomorph_sphere_of_homotopyEquiv_iff_of_two_le (M : Type*)
    [TopologicalSpace M] [T2Space M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) (hn : 2 ≤ n) :
    ((M ≃ₕ sphere (0 : F) 1) → Nonempty (M ≃ₜ sphere (0 : F) 1)) ↔
      ∀ [CompactSpace M] [SimplyConnectedSpace M] [SecondCountableTopology M],
        (M ≃ₕ sphere (0 : F) 1) → Nonempty (M ≃ₜ sphere (0 : F) 1) := by
  constructor
  · intro h _ _ _ e
    exact h e
  · intro h e
    have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
    have := e.compactSpace_of_sphere hE hF
    have := e.simplyConnectedSpace_of_sphere
      (by simpa using lt_rank_of_lt_finrank (R := ℝ) (M := F) (n := 2) (by omega)) zero_le_one
    have := e.secondCountableTopology_of_sphere hE hF
    exact h e

/-- For `2 ≤ n`, if a Hausdorff `n`-manifold `M` is homeomorphic to `Sⁿ` whenever `M` is compact,
simply connected, and second countable, then `M` is homeomorphic to `Sⁿ` whenever `M` is homotopy
equivalent to `Sⁿ`. -/
theorem nonempty_homeomorph_sphere_of_homotopyEquiv_of_two_le_of_forall (M : Type*)
    [TopologicalSpace M] [T2Space M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) (hn : 2 ≤ n)
    (h : ∀ [CompactSpace M] [SimplyConnectedSpace M] [SecondCountableTopology M],
      Nonempty (M ≃ₜ sphere (0 : F) 1)) :
    (M ≃ₕ sphere (0 : F) 1) → Nonempty (M ≃ₜ sphere (0 : F) 1) :=
  (nonempty_homeomorph_sphere_of_homotopyEquiv_iff_of_two_le M hE hF hn).2 fun _ ↦ h

end PoincareConjecture

end TauCeti
