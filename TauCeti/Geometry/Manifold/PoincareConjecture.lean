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

Building on the general sphere homology and connectivity transfers in
`TauCeti.AlgebraicTopology.Singular.Sphere` and `TauCeti.AlgebraicTopology.Sphere.SimplyConnected`,
this file proves that a homotopy equivalence `e : M ≃ₕ Sⁿ` automatically supplies compactness and
second countability on any Hausdorff boundaryless `n`-manifold `M` (modelled on a real normed space
`E` of dimension `n`, with `Sⁿ` the unit sphere of a real normed space `F` of dimension `n + 1`, in
possibly different universes), and deduces manifold obstructions and reductions of both the smooth
and topological generalized Poincaré statements:

* **Compactness and second countability.** For `1 ≤ n`, `M` is connected
  (`e.connectedSpace_of_sphere`) and `Hₙ(M; ℤ) ≅ ℤ ≠ 0` (`e.singularHomologySphereIso` with
  `ModuleCat.of ℤ (ULift ℤ)`), so Hatcher's noncompact vanishing theorem
  (`TauCeti.compactSpace_of_not_isZero_singularHomology`) forces `CompactSpace M`; for `n = 0`, `M`
  is discrete and `π₀(M) ≃ π₀(S⁰)` is finite, again giving `CompactSpace M`
  (`ContinuousMap.HomotopyEquiv.compactSpace_of_sphere`). Compactness then yields
  `SecondCountableTopology M` (`ContinuousMap.HomotopyEquiv.secondCountableTopology_of_sphere`).
* **Manifold obstructions.** No noncompact Hausdorff `n`-manifold and no proper open subset of a
  preconnected Hausdorff `n`-manifold is homotopy equivalent to `Sⁿ`
  (`TauCeti.isEmpty_homotopyEquiv_sphere_of_not_compactSpace`,
  `TauCeti.isEmpty_homotopyEquiv_sphere_of_isOpen_ne_univ`); see
  `TauCeti.AlgebraicTopology.Sphere.Contractible` for the contractibility obstructions on normed and
  Euclidean spaces.
* **Reductions of the Poincaré conjecture.** Both the smooth statement
  `ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n` and its topological counterpart on a
  fixed `[ChartedSpace E M]` reduce for `1 ≤ n` to compact path-connected second-countable manifolds
  (`TauCeti.nonemptyDiffeomorphSphere_iff_of_one_le`,
  `TauCeti.nonempty_homeomorph_sphere_of_homotopyEquiv_iff_of_one_le`) and for `2 ≤ n` to compact
  simply connected second-countable manifolds
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

open CategoryTheory Limits Metric Module Set Topology
open scoped ContinuousMap ContDiff Manifold

universe w

namespace ContinuousMap.HomotopyEquiv

section Manifold

variable {M : Type w} [TopologicalSpace M] [T2Space M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **A Hausdorff `n`-manifold homotopy equivalent to `Sⁿ` is compact.** -/
theorem compactSpace_of_sphere {n : ℕ} (e : M ≃ₕ sphere (0 : F) 1) (hE : finrank ℝ E = n)
    (hF : finrank ℝ F = n + 1) :
    CompactSpace M := by
  rcases n with _ | m
  · have : Subsingleton E := Module.finrank_zero_iff.1 hE
    have : DiscreteTopology M := ChartedSpace.discreteTopology E M
    have : Finite (sphere (0 : F) 1) := TauCeti.finite_sphere_of_finrank_eq_one hF 0 1
    have : Finite (ZerothHomotopy (sphere (0 : F) 1)) :=
      Finite.of_surjective _ ZerothHomotopy.mk_surjective
    have : Finite (ZerothHomotopy M) := Finite.of_equiv _ e.zerothHomotopyCongr.symm
    have : Finite M :=
      Finite.of_injective _ ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace
    exact Finite.compactSpace
  · have := e.connectedSpace_of_sphere hF (Nat.succ_pos m)
    let N : ModuleCat.{w} ℤ := ModuleCat.of ℤ (ULift.{w} ℤ)
    have hN : ¬ IsZero N := fun h ↦
      one_ne_zero (α := ULift.{w} ℤ) ((ModuleCat.subsingleton_of_isZero h).elim ⟨1⟩ ⟨0⟩)
    have hH : ¬ IsZero (((AlgebraicTopology.singularHomologyFunctor
        (ModuleCat.{w} ℤ) (m + 1)).obj N).obj (TopCat.of M)) :=
      fun h ↦ hN (h.of_iso (e.singularHomologySphereIso N hF (Nat.succ_pos m)).symm)
    exact TauCeti.compactSpace_of_not_isZero_singularHomology N hE le_rfl hH

/-- **A Hausdorff `n`-manifold homotopy equivalent to `Sⁿ` is second countable.** -/
theorem secondCountableTopology_of_sphere {n : ℕ} (e : M ≃ₕ sphere (0 : F) 1)
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) :
    SecondCountableTopology M := by
  have := e.compactSpace_of_sphere hE hF
  exact ChartedSpace.secondCountable_of_sigmaCompact E M

end Manifold

end ContinuousMap.HomotopyEquiv

namespace TauCeti

section Obstructions

/-- **No noncompact Hausdorff `n`-manifold is homotopy equivalent to `Sⁿ`.** -/
theorem isEmpty_homotopyEquiv_sphere_of_not_compactSpace {M : Type*} [TopologicalSpace M]
    [T2Space M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) (hM : ¬ CompactSpace M) :
    IsEmpty (M ≃ₕ sphere (0 : F) 1) :=
  ⟨fun e ↦ hM (e.compactSpace_of_sphere hE hF)⟩

/-- **No proper open subset of a preconnected Hausdorff `n`-manifold is homotopy equivalent to
`Sⁿ`.** -/
theorem isEmpty_homotopyEquiv_sphere_of_isOpen_ne_univ {M : Type*} [TopologicalSpace M] [T2Space M]
    [PreconnectedSpace M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : ℕ} (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) {U : Set M}
    (hUo : IsOpen U) (hU : U ≠ univ) :
    IsEmpty (U ≃ₕ sphere (0 : F) 1) := by
  refine ⟨fun e ↦ hU ?_⟩
  have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  have : Nonempty U := e.nonempty_of_sphere
  obtain ⟨x⟩ := ‹Nonempty U›
  let _ : ChartedSpace E U := TopologicalSpace.Opens.instChartedSpace ⟨U, hUo⟩
  have hUc : IsCompact U := isCompact_iff_compactSpace.2 (e.compactSpace_of_sphere hE hF)
  exact IsClopen.eq_univ ⟨hUc.isClosed, hUo⟩ ⟨x.1, x.2⟩

end Obstructions

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
    have := e.compactSpace_of_sphere (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1))
    have := e.pathConnectedSpace_of_sphere
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1)) hn
    have := e.secondCountableTopology_of_sphere (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1))
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
    have := e.compactSpace_of_sphere (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1))
    have := e.simplyConnectedSpace_of_sphere
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1)) hn
    have := e.secondCountableTopology_of_sphere (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1))
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
    [FiniteDimensional ℝ E] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : ℕ} (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) (hn : 1 ≤ n) :
    ((M ≃ₕ sphere (0 : F) 1) → Nonempty (M ≃ₜ sphere (0 : F) 1)) ↔
      ∀ [CompactSpace M] [PathConnectedSpace M] [SecondCountableTopology M],
        (M ≃ₕ sphere (0 : F) 1) → Nonempty (M ≃ₜ sphere (0 : F) 1) := by
  constructor
  · intro h _ _ _ e
    exact h e
  · intro h e
    have := e.compactSpace_of_sphere hE hF
    have := e.pathConnectedSpace_of_sphere hF hn
    have := e.secondCountableTopology_of_sphere hE hF
    exact h e

/-- For `2 ≤ n`, the topological generalized Poincaré statement on a Hausdorff `n`-manifold `M`
(homotopy equivalence to `Sⁿ` implies homeomorphism to `Sⁿ`) is equivalent to the same statement
assuming `M` is compact, simply connected, and second countable. -/
theorem nonempty_homeomorph_sphere_of_homotopyEquiv_iff_of_two_le (M : Type*)
    [TopologicalSpace M] [T2Space M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : ℕ} (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) (hn : 2 ≤ n) :
    ((M ≃ₕ sphere (0 : F) 1) → Nonempty (M ≃ₜ sphere (0 : F) 1)) ↔
      ∀ [CompactSpace M] [SimplyConnectedSpace M] [SecondCountableTopology M],
        (M ≃ₕ sphere (0 : F) 1) → Nonempty (M ≃ₜ sphere (0 : F) 1) := by
  constructor
  · intro h _ _ _ e
    exact h e
  · intro h e
    have := e.compactSpace_of_sphere hE hF
    have := e.simplyConnectedSpace_of_sphere hF hn
    have := e.secondCountableTopology_of_sphere hE hF
    exact h e

/-- For `2 ≤ n`, if a Hausdorff `n`-manifold `M` is homeomorphic to `Sⁿ` whenever `M` is compact,
simply connected, and second countable, then `M` is homeomorphic to `Sⁿ` whenever `M` is homotopy
equivalent to `Sⁿ`. -/
theorem nonempty_homeomorph_sphere_of_homotopyEquiv_of_two_le_of_forall (M : Type*)
    [TopologicalSpace M] [T2Space M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : ℕ} (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) (hn : 2 ≤ n)
    (h : ∀ [CompactSpace M] [SimplyConnectedSpace M] [SecondCountableTopology M],
      Nonempty (M ≃ₜ sphere (0 : F) 1)) :
    (M ≃ₕ sphere (0 : F) 1) → Nonempty (M ≃ₜ sphere (0 : F) 1) :=
  (nonempty_homeomorph_sphere_of_homotopyEquiv_iff_of_two_le M hE hF hn).2 fun _ ↦ h

end PoincareConjecture

end TauCeti
