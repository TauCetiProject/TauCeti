/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Geometry.Manifold.PoincareConjecture
public import Mathlib.Topology.Category.TopCat.Sphere
public import TauCeti.Topology.Homotopy.TotallyDisconnected
import Mathlib.Algebra.Ring.ULift
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Noncompact
import TauCeti.AlgebraicTopology.Singular.Sphere
import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
import TauCeti.Topology.Homotopy.HomotopyEquiv

/-!
# Topological properties forced by homotopy equivalence to a sphere

In `Mathlib.Geometry.Manifold.PoincareConjecture`, the smooth `n`-dimensional Poincaré statement
`ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n` asks whether every Hausdorff smooth
`n`-manifold `M` without boundary equipped with a homotopy equivalence `M ≃ₕ 𝕊ⁿ` is diffeomorphic
to `𝕊ⁿ`; neither compactness nor simple connectedness of `M` is assumed a priori.

This file proves that a homotopy equivalence `e : M ≃ₕ S` from a Hausdorff topological `n`-manifold
`M` without boundary to the unit sphere `S` of an `(n + 1)`-dimensional real normed space
automatically forces the closed-manifold and connectivity hypotheses:

* **Path connectedness and connectedness (`n ≥ 1`):** for `2 ≤ finrank ℝ F`, the unit sphere of `F`
  is path connected, and path connectedness transports across `e.symm`
  (`ContinuousMap.HomotopyEquiv.pathConnectedSpace_of_sphere` and
  `ContinuousMap.HomotopyEquiv.connectedSpace_of_sphere`).
* **Simple connectedness (`n ≥ 2`):** for `3 ≤ finrank ℝ F`, the unit sphere of `F` is simply
  connected (`TauCeti.simplyConnectedSpace_sphere`), so `M` is simply connected
  (`ContinuousMap.HomotopyEquiv.simplyConnectedSpace_of_sphere`).
* **Compactness and second countability (all `n : ℕ`):** for `n = 0`, both `M` and `S⁰` are
  discrete, so `e` is already a homeomorphism onto the two-point sphere
  (`ContinuousMap.HomotopyEquiv.homeomorphOfSphereZero`), which also settles the `0`-dimensional
  topological and smooth Poincaré statements unconditionally
  (`ContinuousMap.HomotopyEquiv.nonemptyDiffeomorphSphere_zero`). For `n = d + 1`, `M` is connected
  and `H_{d+1}(M; ℤ) ≅ H_{d+1}(S^{d+1}; ℤ) ≅ ℤ` is nonzero, whereas Hatcher's Proposition 3.29
  (`TauCeti.isZero_singularHomology_of_noncompactSpace`) forces top singular homology to vanish on
  any noncompact connected `n`-manifold; hence `M` is compact
  (`ContinuousMap.HomotopyEquiv.compactSpace_of_sphere`) and second countable
  (`ContinuousMap.HomotopyEquiv.secondCountableTopology_of_sphere`).

Consequently, for `2 ≤ n`, proving `ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n` (or
its topological counterpart `M ≃ₕ 𝕊ⁿ → Nonempty (M ≃ₜ 𝕊ⁿ)`) reduces to the closed simply connected
case where `[CompactSpace M]` and `[SimplyConnectedSpace M]` are already available
(`ContinuousMap.HomotopyEquiv.nonemptyDiffeomorphSphere_of_simplyConnected_compact` and
`ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_simplyConnected_compact`).

The final section records non-vacuity and sharpness: no noncompact Hausdorff `n`-manifold is
homotopy equivalent to `Sⁿ` (`TauCeti.isEmpty_homotopyEquiv_sphere_of_noncompactSpace`), in
particular `ℝⁿ⁺¹` is not homotopy equivalent to `Sⁿ⁺¹`
(`TauCeti.isEmpty_homotopyEquiv_sphere_normedSpace`), whereas `Sⁿ × ℝ` is a noncompact
`(n + 1)`-manifold homotopy equivalent to `Sⁿ` (`TauCeti.noncompactSpace_sphere_prod_real`), showing
that matching the manifold dimension `n` to the sphere dimension `n` is essential.

## Main definitions and results

* `ContinuousMap.HomotopyEquiv.homeomorphOfSphereZero` and
  `ContinuousMap.HomotopyEquiv.nonemptyDiffeomorphSphere_zero`: the `0`-dimensional topological and
  smooth Poincaré theorems.
* `ContinuousMap.HomotopyEquiv.pathConnectedSpace_of_sphere`,
  `ContinuousMap.HomotopyEquiv.connectedSpace_of_sphere`, and
  `ContinuousMap.HomotopyEquiv.simplyConnectedSpace_of_sphere`: connectivity and simple
  connectedness of a space homotopy equivalent to a sphere.
* `ContinuousMap.HomotopyEquiv.compactSpace_of_topCatSphere`,
  `ContinuousMap.HomotopyEquiv.compactSpace_of_sphere`, and
  `ContinuousMap.HomotopyEquiv.secondCountableTopology_of_sphere`: compactness and second
  countability of a Hausdorff `n`-manifold without boundary homotopy equivalent to `Sⁿ`.
* `ContinuousMap.HomotopyEquiv.nonemptyDiffeomorphSphere_of_simplyConnected_compact` and
  `ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_simplyConnected_compact`: reduction of
  the smooth and topological Poincaré statements for `2 ≤ n` to compact simply connected manifolds.
* `TauCeti.isEmpty_homotopyEquiv_sphere_of_noncompactSpace`,
  `TauCeti.isEmpty_homotopyEquiv_sphere_normedSpace`, and
  `TauCeti.noncompactSpace_sphere_prod_real`: non-vacuity and dimension-matching sharpness.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Proposition 3.29, p. 239.
-/

public section

open AlgebraicTopology CategoryTheory Metric Module
open scoped ContinuousMap Manifold ContDiff

universe u

namespace ContinuousMap.HomotopyEquiv

section Connectivity

variable {M : Type*} [TopologicalSpace M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A space homotopy equivalent to the unit sphere of a real normed space of dimension at least `2`
is path connected. -/
theorem pathConnectedSpace_of_sphere (e : M ≃ₕ sphere (0 : F) 1) (hF : 2 ≤ finrank ℝ F) :
    PathConnectedSpace M := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by lia)
  have hrank : 1 < Module.rank ℝ F := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast (by lia : 1 < finrank ℝ F)
  have : PathConnectedSpace (sphere (0 : F) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hrank 0 zero_le_one)
  exact e.symm.pathConnectedSpace

/-- A space homotopy equivalent to the unit sphere of a real normed space of dimension at least `2`
is connected. -/
theorem connectedSpace_of_sphere (e : M ≃ₕ sphere (0 : F) 1) (hF : 2 ≤ finrank ℝ F) :
    ConnectedSpace M := by
  have := e.pathConnectedSpace_of_sphere hF
  infer_instance

/-- A space homotopy equivalent to the unit sphere of a real normed space of dimension at least `3`
is simply connected. -/
theorem simplyConnectedSpace_of_sphere (e : M ≃ₕ sphere (0 : F) 1) (hF : 3 ≤ finrank ℝ F) :
    SimplyConnectedSpace M := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by lia)
  have hrank : 2 < Module.rank ℝ F := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast (by lia : 2 < finrank ℝ F)
  have := TauCeti.simplyConnectedSpace_sphere hrank (0 : F) zero_le_one
  exact e.simplyConnectedSpace

/-- A space homotopy equivalent to the Euclidean `n`-sphere with `2 ≤ n` is simply connected. -/
theorem simplyConnectedSpace_of_sphere_euclideanSpace {n : ℕ}
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (hn : 2 ≤ n) :
    SimplyConnectedSpace M :=
  e.simplyConnectedSpace_of_sphere (by rw [finrank_euclideanSpace_fin]; lia)

end Connectivity

section DimensionZero

variable {M : Type*} [TopologicalSpace M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Zero-dimensional topological Poincaré theorem.** A `0`-dimensional manifold `M` homotopy
equivalent to the unit sphere `S⁰` of a `1`-dimensional real normed space is homeomorphic to `S⁰`
via the same underlying maps. -/
def homeomorphOfSphereZero (e : M ≃ₕ sphere (0 : F) 1) (hE : finrank ℝ E = 0)
    (hF : finrank ℝ F = 1) : M ≃ₜ sphere (0 : F) 1 := by
  have : Subsingleton E := (Module.finrank_eq_zero_iff_of_free ℝ E).1 hE
  have := ChartedSpace.discreteTopology E M
  have := TauCeti.discreteTopology_sphere_of_finrank_eq_one hF 0 1
  exact e.toHomeomorphOfTotallyDisconnectedSpace

@[simp]
theorem coe_homeomorphOfSphereZero (e : M ≃ₕ sphere (0 : F) 1) (hE : finrank ℝ E = 0)
    (hF : finrank ℝ F = 1) :
    ⇑(e.homeomorphOfSphereZero hE hF) = ⇑e :=
  (rfl)

@[simp]
theorem coe_homeomorphOfSphereZero_symm (e : M ≃ₕ sphere (0 : F) 1) (hE : finrank ℝ E = 0)
    (hF : finrank ℝ F = 1) :
    ⇑(e.homeomorphOfSphereZero hE hF).symm = ⇑e.symm :=
  (rfl)

/-- **Zero-dimensional smooth Poincaré theorem.** Every Hausdorff smooth `0`-manifold homotopy
equivalent to `𝕊⁰` is diffeomorphic to `𝕊⁰`. -/
theorem nonemptyDiffeomorphSphere_zero {M : Type*} [TopologicalSpace M] [T2Space M] :
    NonemptyDiffeomorphSphere M 0 := by
  intro _ _ e
  have := ChartedSpace.discreteTopology (EuclideanSpace ℝ (Fin 0)) M
  have := TauCeti.discreteTopology_sphere_of_finrank_eq_one
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 1)) 0 1
  let φ := e.homeomorphOfSphereZero finrank_euclideanSpace_fin finrank_euclideanSpace_fin
  exact ⟨{
    toEquiv := φ.toEquiv
    contMDiff_toFun := contMDiff_of_discreteTopology
    contMDiff_invFun := contMDiff_of_discreteTopology }⟩

end DimensionZero

section Compactness

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- **A Hausdorff `n`-manifold homotopy equivalent to `TopCat.sphere n` is compact.** For `n = 0`
it is homeomorphic to the finite two-point sphere; for `n = d + 1` it is connected and its top
integral homology `H_{d+1}(M; ℤ) ≅ ℤ` is nonzero, forcing compactness by Hatcher's
Proposition 3.29 (`TauCeti.compactSpace_of_not_isZero_singularHomology`). -/
theorem compactSpace_of_topCatSphere {n : ℕ} (e : M ≃ₕ TopCat.sphere.{u} n)
    (hE : finrank ℝ E = n) : CompactSpace M := by
  cases n with
  | zero =>
    let e' := e.trans (TauCeti.diskBoundaryHomeomorph 1).toHomotopyEquiv
    have hF1 : finrank ℝ (EuclideanSpace ℝ (ULift.{u} (Fin 1))) = 1 :=
      TauCeti.finrank_euclideanSpace_ulift_fin 1
    have := TauCeti.finite_sphere_of_finrank_eq_one hF1 0 1
    exact (e'.homeomorphOfSphereZero hE hF1).symm.compactSpace
  | succ d =>
    have : PathConnectedSpace (TopCat.sphere.{u} (d + 1)) :=
      TauCeti.TopCat.pathConnectedSpace_diskBoundary (n := d + 2) (by lia)
    have := e.symm.pathConnectedSpace
    let Z : ModuleCat.{u} (ULift.{u} ℤ) := ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ)
    let iso : ((singularHomologyFunctor (ModuleCat.{u} (ULift.{u} ℤ)) (d + 1)).obj Z).obj
        (TopCat.of M) ≅ Z :=
      e.singularHomologyIso Z (d + 1) ≪≫
        ((TauCeti.reducedSingularHomologySuccIso Z d).app (TopCat.sphere.{u} (d + 1))).symm ≪≫
        TauCeti.reducedSingularHomologyTopCatSphereIso Z (d + 1)
    refine TauCeti.compactSpace_of_not_isZero_singularHomology Z hE le_rfl fun hz ↦ ?_
    have h01 : (⟨0⟩ : ULift.{u} ℤ) = ⟨1⟩ :=
      (ModuleCat.subsingleton_of_isZero (hz.of_iso iso.symm)).elim (⟨0⟩ : ULift.{u} ℤ) ⟨1⟩
    exact zero_ne_one (congrArg ULift.down h01)

/-- **A Hausdorff `n`-manifold homotopy equivalent to an `n`-sphere is compact.** If `M` is a
Hausdorff space modelled on an `n`-dimensional real normed space and `F` has dimension `n + 1`,
any homotopy equivalence `M ≃ₕ sphere (0 : F) 1` forces `CompactSpace M`. -/
theorem compactSpace_of_sphere {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (e : M ≃ₕ sphere (0 : F) 1) (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) :
    CompactSpace M := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by lia)
  let eS : sphere (0 : F) 1 ≃ₜ TopCat.sphere.{u} n :=
    (TauCeti.sphereHomeomorphOfFinrankEq
        (hF.trans (TauCeti.finrank_euclideanSpace_ulift_fin.{u} (n + 1)).symm)).trans
      (TauCeti.diskBoundaryHomeomorph (n + 1)).symm
  exact (e.trans eS.toHomotopyEquiv).compactSpace_of_topCatSphere hE

/-- A Hausdorff `n`-manifold homotopy equivalent to the Euclidean `n`-sphere is compact. -/
theorem compactSpace_of_sphere_euclideanSpace {n : ℕ}
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (hE : finrank ℝ E = n) :
    CompactSpace M :=
  e.compactSpace_of_sphere hE finrank_euclideanSpace_fin

/-- **A Hausdorff `n`-manifold homotopy equivalent to an `n`-sphere is second countable.** -/
theorem secondCountableTopology_of_sphere {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (e : M ≃ₕ sphere (0 : F) 1) (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) :
    SecondCountableTopology M := by
  have := e.compactSpace_of_sphere hE hF
  exact ChartedSpace.secondCountable_of_sigmaCompact E M

end Compactness

section Reduction

/-- **Reduction of the smooth Poincaré statement to closed simply connected manifolds (`2 ≤ n`).**
To prove `ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n` for `2 ≤ n`, it suffices to
construct the diffeomorphism under the additional hypotheses `[CompactSpace M]` and
`[SimplyConnectedSpace M]`, since both are forced by `M ≃ₕ 𝕊ⁿ`. -/
theorem nonemptyDiffeomorphSphere_of_simplyConnected_compact {M : Type*} [TopologicalSpace M]
    [T2Space M] {n : ℕ} (hn : 2 ≤ n)
    (h : ∀ [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [CompactSpace M] [SimplyConnectedSpace M],
      (M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) →
        Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    NonemptyDiffeomorphSphere M n := by
  intro _ _ e
  have := e.compactSpace_of_sphere_euclideanSpace finrank_euclideanSpace_fin
  have := e.simplyConnectedSpace_of_sphere_euclideanSpace hn
  exact h e

/-- **Reduction of the topological Poincaré statement to closed simply connected manifolds
(`2 ≤ n`).** If a Hausdorff `n`-manifold `M` with `2 ≤ n` is homotopy equivalent to the unit sphere
`S` of an `(n + 1)`-dimensional real normed space, proving `Nonempty (M ≃ₜ S)` reduces to the case
where `M` is compact, second countable, and simply connected. -/
theorem nonempty_homeomorph_sphere_of_simplyConnected_compact {M : Type*} [TopologicalSpace M]
    [T2Space M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ} (hn : 2 ≤ n)
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) (e : M ≃ₕ sphere (0 : F) 1)
    (h : [CompactSpace M] → [SecondCountableTopology M] → [SimplyConnectedSpace M] →
      Nonempty (M ≃ₜ sphere (0 : F) 1)) :
    Nonempty (M ≃ₜ sphere (0 : F) 1) := by
  have := e.compactSpace_of_sphere hE hF
  have := e.secondCountableTopology_of_sphere hE hF
  have := e.simplyConnectedSpace_of_sphere (by lia)
  exact h

end Reduction

end ContinuousMap.HomotopyEquiv

namespace TauCeti

/-- **No noncompact Hausdorff `n`-manifold is homotopy equivalent to `Sⁿ`.** -/
theorem isEmpty_homotopyEquiv_sphere_of_noncompactSpace {M : Type*} [TopologicalSpace M]
    [T2Space M] [NoncompactSpace M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) :
    IsEmpty (M ≃ₕ sphere (0 : F) 1) :=
  ⟨fun e ↦ not_compactSpace_iff.2 ‹_› (e.compactSpace_of_sphere hE hF)⟩

/-- **A positive-dimensional real normed space is not homotopy equivalent to the sphere of the same
dimension.** Even though `E` is contractible (hence simply connected), it is noncompact, so no
homotopy equivalence `E ≃ₕ Sⁿ⁺¹` exists when `dim E = n + 1`. -/
theorem isEmpty_homotopyEquiv_sphere_normedSpace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (hE : finrank ℝ E = n + 1) (hF : finrank ℝ F = n + 2) :
    IsEmpty (E ≃ₕ sphere (0 : F) 1) := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by lia)
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  exact isEmpty_homotopyEquiv_sphere_of_noncompactSpace hE hF

/-- Euclidean space `ℝⁿ⁺¹` is not homotopy equivalent to `Sⁿ⁺¹`. -/
theorem isEmpty_homotopyEquiv_sphere_euclideanSpace (n : ℕ) :
    IsEmpty (EuclideanSpace ℝ (Fin (n + 1)) ≃ₕ
      sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
  isEmpty_homotopyEquiv_sphere_normedSpace finrank_euclideanSpace_fin finrank_euclideanSpace_fin

/-- **Sharpness of dimension matching in `compactSpace_of_sphere`.** For `1 ≤ finrank ℝ F`, the
cylinder `sphere (0 : F) 1 × ℝ` is homotopy equivalent to `sphere (0 : F) 1` via
`ContinuousMap.HomotopyEquiv.prodContractible`, yet is noncompact because its manifold dimension is
`finrank ℝ F` rather than `finrank ℝ F - 1`. -/
theorem noncompactSpace_sphere_prod_real {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hF : 1 ≤ finrank ℝ F) :
    NoncompactSpace (sphere (0 : F) 1 × ℝ) := by
  have : Nontrivial F := Module.nontrivial_of_finrank_pos (R := ℝ) (by lia)
  have : Nonempty (sphere (0 : F) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  infer_instance

end TauCeti
