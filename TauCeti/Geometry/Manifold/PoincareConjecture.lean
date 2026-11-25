/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Geometry.Manifold.PoincareConjecture
public import Mathlib.Topology.Category.TopCat.Sphere
public import TauCeti.Geometry.Manifold.Smoothable
public import TauCeti.Topology.Homotopy.TotallyDisconnected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Noncompact
import TauCeti.AlgebraicTopology.Singular.Sphere
import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Topology.Homotopy.HomotopyEquiv

/-!
# Topological properties forced by homotopy equivalence to a sphere

In `Mathlib.Geometry.Manifold.PoincareConjecture`, the smooth `n`-dimensional Poincaré statement
`ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n` asks whether every Hausdorff smooth
`n`-manifold `M` without boundary equipped with a homotopy equivalence `M ≃ₕ 𝕊ⁿ` is diffeomorphic
to `𝕊ⁿ`; neither compactness, second countability, nor simple connectedness of `M` is assumed a
priori.

Combined with the sphere homotopy-equivalence connectivity results in
`TauCeti.AlgebraicTopology.Sphere.SimplyConnected`, this file proves that a homotopy equivalence
`e : M ≃ₕ S` from a Hausdorff topological `n`-manifold `M` without boundary to a sphere `S` of
positive radius in an `(n + 1)`-dimensional real normed space automatically forces the
closed-manifold hypotheses:

* **Dimension zero:** both `M` and any `0`-sphere `sphere c r` are discrete, so `e` upgrades to a
  homeomorphism (`ContinuousMap.HomotopyEquiv.toHomeomorphOfSphereZero`), which supplies the
  `n = 0` case of compactness.
* **Compactness and second countability (all `n : ℕ`):** for `n = d + 1`, `M` is path connected and
  `H_{d+1}(M; ℤ) ≅ H_{d+1}(S^{d+1}; ℤ) ≅ ℤ` is nontrivial, whereas Hatcher's Proposition 3.29
  (`TauCeti.compactSpace_of_nontrivial_singularHomology`) forces any preconnected Hausdorff
  `(d + 1)`-manifold with nontrivial top singular homology to be compact; hence `M` is compact
  (`ContinuousMap.HomotopyEquiv.compactSpace_of_sphere`,
  `ContinuousMap.HomotopyEquiv.compactSpace_of_sphere_of_pos`) and second countable
  (`ContinuousMap.HomotopyEquiv.secondCountableTopology_of_sphere`,
  `ContinuousMap.HomotopyEquiv.secondCountableTopology_of_sphere_of_pos`).

Consequently, for `2 ≤ n`, proving `ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n` (or
its topological counterpart `M ≃ₕ 𝕊ⁿ → Nonempty (M ≃ₜ 𝕊ⁿ)`) reduces to the closed simply connected
case where `[CompactSpace M]`, `[SecondCountableTopology M]`, and `[SimplyConnectedSpace M]` are
already available
(`ContinuousMap.HomotopyEquiv.nonemptyDiffeomorphSphere_of_compactSpace_simplyConnectedSpace_imp`,
`ContinuousMap.HomotopyEquiv.nonemptyDiffeomorphSphere_of_simplyConnected`, and
`ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_compactSpace_simplyConnectedSpace_imp`),
and a topological manifold `M ≃ₕ 𝕊ⁿ` that is smoothable once compact and second countable
(`TauCeti.IsSmoothable (𝓡 n) M`) is homeomorphic to `𝕊ⁿ` whenever `NonemptyDiffeomorphSphere M n`
holds (`ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_isSmoothable`,
`ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_isSmoothable_of_simplyConnected`).

The final section records non-vacuity and sharpness: no noncompact Hausdorff `n`-manifold is
homotopy equivalent to an `n`-sphere of positive radius
(`TauCeti.isEmpty_homotopyEquiv_sphere_of_noncompactSpace_of_pos`), and no `n`-dimensional real
normed space (including `n = 0`, where `E` is path connected while `S⁰` has two path components) is
homotopy equivalent to an `n`-sphere of positive radius
(`TauCeti.isEmpty_homotopyEquiv_normedSpace_sphere_of_pos`,
`TauCeti.isEmpty_homotopyEquiv_normedSpace_sphere`,
`TauCeti.isEmpty_homotopyEquiv_euclideanSpace_sphere`). By contrast, at radius `0` the sphere is a
singleton (`ℝ³ ≃ₕ sphere 0 0`), and for a nontrivial real normed space `F` the cylinder
`sphere (0 : F) 1 × ℝ` is homotopy equivalent to `sphere (0 : F) 1` yet noncompact: when
`dim F = n + 1`, its manifold dimension is `n + 1` rather than `n`, so
`ContinuousMap.HomotopyEquiv.compactSpace_of_sphere` does not apply without matching the manifold
and sphere dimensions.

For `1 ≤ n`, both statements are moreover equivalent to their restrictions to compact, path
connected, second countable manifolds
(`ContinuousMap.HomotopyEquiv.nonemptyDiffeomorphSphere_iff_of_one_le` and
`ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_homotopyEquiv_iff_of_one_le`), and for
`2 ≤ n` to their restrictions to compact, simply connected, second countable manifolds
(`ContinuousMap.HomotopyEquiv.nonemptyDiffeomorphSphere_iff_of_two_le` and
`ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_homotopyEquiv_iff_of_two_le`).

## Main definitions and results

* `ContinuousMap.HomotopyEquiv.toHomeomorphOfSphereZero`: upgrades a homotopy equivalence from a
  `0`-manifold to a `0`-sphere `sphere c r` to a homeomorphism.
* `ContinuousMap.HomotopyEquiv.compactSpace_of_topCatSphere`,
  `ContinuousMap.HomotopyEquiv.compactSpace_of_sphere`,
  `ContinuousMap.HomotopyEquiv.compactSpace_of_sphere_of_pos`,
  `ContinuousMap.HomotopyEquiv.secondCountableTopology_of_sphere`,
  `ContinuousMap.HomotopyEquiv.secondCountableTopology_of_sphere_of_pos`, and
  `ContinuousMap.HomotopyEquiv.secondCountableTopology_of_sphere_euclideanSpace`: compactness and
  second countability of a Hausdorff `n`-manifold without boundary homotopy equivalent to an
  `n`-sphere of positive radius.
* `ContinuousMap.HomotopyEquiv.nonemptyDiffeomorphSphere_of_compactSpace_simplyConnectedSpace_imp`,
  `ContinuousMap.HomotopyEquiv.nonemptyDiffeomorphSphere_of_simplyConnected`, and
  `ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_compactSpace_simplyConnectedSpace_imp`:
  reduction of the smooth and topological Poincaré statements for `2 ≤ n` to compact, second
  countable, simply connected manifolds.
* `ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_isSmoothable` and
  `ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_isSmoothable_of_simplyConnected`:
  topological homotopy-equivalence Poincaré from `TauCeti.IsSmoothable` and smooth Poincaré.
* `ContinuousMap.HomotopyEquiv.nonemptyDiffeomorphSphere_iff_of_one_le`,
  `ContinuousMap.HomotopyEquiv.nonemptyDiffeomorphSphere_iff_of_two_le`,
  `ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_homotopyEquiv_iff_of_one_le`, and
  `ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_homotopyEquiv_iff_of_two_le`: the
  corresponding equivalences with the restricted statements.
* `TauCeti.isEmpty_homotopyEquiv_sphere_of_noncompactSpace`,
  `TauCeti.isEmpty_homotopyEquiv_sphere_of_noncompactSpace_of_pos`,
  `TauCeti.isEmpty_homotopyEquiv_normedSpace_sphere`,
  `TauCeti.isEmpty_homotopyEquiv_normedSpace_sphere_of_pos`, and
  `TauCeti.isEmpty_homotopyEquiv_euclideanSpace_sphere`: nonexistence of homotopy equivalences from
  noncompact `n`-manifolds and `n`-dimensional normed/Euclidean spaces (for all `n : ℕ`) to spheres
  of positive radius of the same dimension.
* `TauCeti.isEmpty_homotopyEquiv_sphere_of_isOpen_ne_univ` and
  `TauCeti.isEmpty_homotopyEquiv_sphere_of_isOpen_ne_univ_of_pos`: no proper open subset of a
  preconnected Hausdorff `n`-manifold is homotopy equivalent to an `n`-sphere of positive radius.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Proposition 3.29, p. 239.
* J. Milnor, *Lectures on the h-Cobordism Theorem*, Princeton University Press, 1965, §9.
-/

public section

open AlgebraicTopology CategoryTheory Metric Module
open scoped ContinuousMap Manifold ContDiff

universe u

namespace ContinuousMap.HomotopyEquiv

section DimensionZero

variable {M : Type*} [TopologicalSpace M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {c : F} {r : ℝ}

/-- **Zero-dimensional topological Poincaré theorem.** Upgrade a homotopy equivalence
`e : M ≃ₕ sphere c r` from a `0`-dimensional manifold `M` to a `0`-sphere `sphere c r` in a
`1`-dimensional real normed space to a homeomorphism with the same underlying forward and inverse
maps. -/
def toHomeomorphOfSphereZero (e : M ≃ₕ sphere c r) (hE : finrank ℝ E = 0)
    (hF : finrank ℝ F = 1) : M ≃ₜ sphere c r :=
  have : Subsingleton E := (Module.finrank_eq_zero_iff_of_free ℝ E).1 hE
  have := ChartedSpace.discreteTopology E M
  have := TauCeti.discreteTopology_sphere_of_finrank_eq_one hF c r
  e.toHomeomorphOfTotallyDisconnectedSpace

@[simp]
theorem coe_toHomeomorphOfSphereZero (e : M ≃ₕ sphere c r) (hE : finrank ℝ E = 0)
    (hF : finrank ℝ F = 1) :
    ⇑(e.toHomeomorphOfSphereZero hE hF) = ⇑e := by
  simp [toHomeomorphOfSphereZero]

@[simp]
theorem coe_toHomeomorphOfSphereZero_symm (e : M ≃ₕ sphere c r) (hE : finrank ℝ E = 0)
    (hF : finrank ℝ F = 1) :
    ⇑(e.toHomeomorphOfSphereZero hE hF).symm = ⇑e.symm := by
  simp [toHomeomorphOfSphereZero]

@[simp]
theorem toHomeomorphOfSphereZero_toHomotopyEquiv (e : M ≃ₕ sphere c r)
    (hE : finrank ℝ E = 0) (hF : finrank ℝ F = 1) :
    (e.toHomeomorphOfSphereZero hE hF).toHomotopyEquiv = e := by
  simp [toHomeomorphOfSphereZero]

@[simp]
theorem _root_.Homeomorph.toHomotopyEquiv_toHomeomorphOfSphereZero
    (h : M ≃ₜ sphere c r) (hE : finrank ℝ E = 0) (hF : finrank ℝ F = 1) :
    h.toHomotopyEquiv.toHomeomorphOfSphereZero hE hF = h := by
  simp [toHomeomorphOfSphereZero]

end DimensionZero

section Compactness

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- **A Hausdorff `n`-manifold homotopy equivalent to `TopCat.sphere n` is compact.** If `M` is a
Hausdorff space modelled on an `n`-dimensional real normed space, any homotopy equivalence
`M ≃ₕ TopCat.sphere n` forces `CompactSpace M`. -/
theorem compactSpace_of_topCatSphere {n : ℕ} (e : M ≃ₕ TopCat.sphere.{u} n)
    (hE : finrank ℝ E = n) : CompactSpace M := by
  cases n with
  | zero =>
    let e' := e.trans (TauCeti.diskBoundaryHomeomorph 1).toHomotopyEquiv
    have hF1 : finrank ℝ (EuclideanSpace ℝ (ULift.{u} (Fin 1))) = 1 :=
      TauCeti.finrank_euclideanSpace_ulift_fin 1
    have := TauCeti.finite_sphere_of_finrank_eq_one hF1 0 1
    exact (e'.toHomeomorphOfSphereZero hE hF1).symm.compactSpace
  | succ d =>
    have := e.symm.pathConnectedSpace
    let Z : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
    let iso : ((singularHomologyFunctor (ModuleCat.{u} ℤ) (d + 1)).obj Z).obj
        (TopCat.of M) ≅ Z :=
      e.singularHomologyIso Z (d + 1) ≪≫
        ((TauCeti.reducedSingularHomologySuccIso Z d).app (TopCat.sphere.{u} (d + 1))).symm ≪≫
        TauCeti.reducedSingularHomologyTopCatSphereIso Z (d + 1)
    have : Nontrivial Z := inferInstanceAs (Nontrivial (ULift.{u} ℤ))
    have := iso.toLinearEquiv.toEquiv.nontrivial
    exact TauCeti.compactSpace_of_nontrivial_singularHomology Z hE le_rfl

/-- **A Hausdorff `n`-manifold homotopy equivalent to an `n`-sphere is compact.** If `M` is a
Hausdorff space modelled on an `n`-dimensional real normed space and `F` has dimension `n + 1`,
any homotopy equivalence `M ≃ₕ sphere (0 : F) 1` forces `CompactSpace M`. -/
theorem compactSpace_of_sphere {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (e : M ≃ₕ sphere (0 : F) 1) (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) :
    CompactSpace M :=
  (e.topCatSphere hF).compactSpace_of_topCatSphere hE

/-- **A Hausdorff `n`-manifold homotopy equivalent to an `n`-sphere of positive radius is
compact.** -/
theorem compactSpace_of_sphere_of_pos {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {c : F} {r : ℝ} {n : ℕ} (e : M ≃ₕ sphere c r) (hE : finrank ℝ E = n)
    (hF : finrank ℝ F = n + 1) (hr : 0 < r) : CompactSpace M :=
  (e.trans (TauCeti.sphereHomeomorphOfPos c hr).symm.toHomotopyEquiv).compactSpace_of_sphere hE hF

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

/-- **A Hausdorff `n`-manifold homotopy equivalent to an `n`-sphere of positive radius is second
countable.** -/
theorem secondCountableTopology_of_sphere_of_pos {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {c : F} {r : ℝ} {n : ℕ} (e : M ≃ₕ sphere c r) (hE : finrank ℝ E = n)
    (hF : finrank ℝ F = n + 1) (hr : 0 < r) : SecondCountableTopology M := by
  have := e.compactSpace_of_sphere_of_pos hE hF hr
  exact ChartedSpace.secondCountable_of_sigmaCompact E M

/-- A Hausdorff `n`-manifold homotopy equivalent to the Euclidean `n`-sphere is second countable. -/
theorem secondCountableTopology_of_sphere_euclideanSpace {n : ℕ}
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (hE : finrank ℝ E = n) :
    SecondCountableTopology M :=
  e.secondCountableTopology_of_sphere hE finrank_euclideanSpace_fin

end Compactness

section Reduction

/-- **Reduction of the smooth Poincaré statement to closed simply connected manifolds (`2 ≤ n`).**
For `2 ≤ n`, `ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n` holds once the
diffeomorphism exists under the additional assumptions `[CompactSpace M]`,
`[SecondCountableTopology M]`, and `[SimplyConnectedSpace M]`. -/
theorem nonemptyDiffeomorphSphere_of_compactSpace_simplyConnectedSpace_imp
    {M : Type*} [TopologicalSpace M] [T2Space M] {n : ℕ} (hn : 2 ≤ n)
    (h : ∀ [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [CompactSpace M] [SecondCountableTopology M] [SimplyConnectedSpace M],
      (M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) →
        Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    NonemptyDiffeomorphSphere M n := by
  intro _ _ e
  have := e.compactSpace_of_sphere_euclideanSpace finrank_euclideanSpace_fin
  have := e.secondCountableTopology_of_sphere_euclideanSpace finrank_euclideanSpace_fin
  have := e.simplyConnectedSpace_of_sphere_euclideanSpace hn
  exact h e

/-- **Smooth Poincaré from the closed simply connected case, without the homotopy-equivalence
premise.** For `2 ≤ n` (in particular for `n = 3`), to prove `NonemptyDiffeomorphSphere M n` it
suffices to show—without assuming `M ≃ₕ 𝕊ⁿ`—that every compact, second-countable, simply connected
smooth `n`-manifold structure on `M` is diffeomorphic to `𝕊ⁿ`. -/
theorem nonemptyDiffeomorphSphere_of_simplyConnected
    {M : Type*} [TopologicalSpace M] [T2Space M] {n : ℕ} (hn : 2 ≤ n)
    (h : ∀ [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [CompactSpace M] [SecondCountableTopology M] [SimplyConnectedSpace M],
      Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    NonemptyDiffeomorphSphere M n :=
  nonemptyDiffeomorphSphere_of_compactSpace_simplyConnectedSpace_imp hn fun _ ↦ h

/-- **Reduction of the topological Poincaré statement to closed simply connected manifolds
(`2 ≤ n`).** If a Hausdorff `n`-manifold `M` with `2 ≤ n` is homotopy equivalent to the unit sphere
`S` of an `(n + 1)`-dimensional real normed space, `Nonempty (M ≃ₜ S)` holds once it holds under
`[CompactSpace M]`, `[SecondCountableTopology M]`, and `[SimplyConnectedSpace M]`. -/
theorem nonempty_homeomorph_sphere_of_compactSpace_simplyConnectedSpace_imp
    {M : Type*} [TopologicalSpace M] [T2Space M] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ} (hn : 2 ≤ n)
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) (e : M ≃ₕ sphere (0 : F) 1)
    (h : [CompactSpace M] → [SecondCountableTopology M] → [SimplyConnectedSpace M] →
      Nonempty (M ≃ₜ sphere (0 : F) 1)) :
    Nonempty (M ≃ₜ sphere (0 : F) 1) := by
  have := e.compactSpace_of_sphere hE hF
  have := e.secondCountableTopology_of_sphere hE hF
  have := e.simplyConnectedSpace_of_sphere
    (by exact_mod_cast (lt_rank_of_lt_finrank (n := 2) (by lia))) zero_le_one
  exact h

/-- **Topological Poincaré from smoothing and smooth Poincaré.** If a Hausdorff space `M` charted
on `ℝⁿ` and homotopy equivalent to `𝕊ⁿ` admits a smooth `n`-manifold structure whenever it is
compact and second countable (`TauCeti.IsSmoothable (𝓡 n) M`), and `NonemptyDiffeomorphSphere M n`
holds, then `M` is homeomorphic to `𝕊ⁿ`. -/
theorem nonempty_homeomorph_sphere_of_isSmoothable
    {M : Type*} [TopologicalSpace M] [T2Space M] {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (hsmooth : [CompactSpace M] → [SecondCountableTopology M] → TauCeti.IsSmoothable (𝓡 n) M)
    (hpoincare : NonemptyDiffeomorphSphere M n) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  have := e.compactSpace_of_sphere_euclideanSpace finrank_euclideanSpace_fin
  have := e.secondCountableTopology_of_sphere_euclideanSpace finrank_euclideanSpace_fin
  obtain ⟨c_smooth, h_man⟩ := TauCeti.isSmoothable_iff.mp hsmooth
  obtain ⟨d⟩ := hpoincare c_smooth h_man e
  exact ⟨d.toHomeomorph⟩

/-- **Topological Poincaré from smoothing and closed simply connected smooth Poincaré.** Combines
`nonempty_homeomorph_sphere_of_isSmoothable` and
`nonemptyDiffeomorphSphere_of_compactSpace_simplyConnectedSpace_imp` for `2 ≤ n`. -/
theorem nonempty_homeomorph_sphere_of_isSmoothable_of_simplyConnected
    {M : Type*} [TopologicalSpace M] [T2Space M] {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (hn : 2 ≤ n)
    (hsmooth : [CompactSpace M] → [SecondCountableTopology M] → [SimplyConnectedSpace M] →
      TauCeti.IsSmoothable (𝓡 n) M)
    (hpoincare : ∀ [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [CompactSpace M] [SecondCountableTopology M] [SimplyConnectedSpace M],
      (M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) →
        Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  have := e.simplyConnectedSpace_of_sphere_euclideanSpace hn
  exact e.nonempty_homeomorph_sphere_of_isSmoothable hsmooth
    (nonemptyDiffeomorphSphere_of_compactSpace_simplyConnectedSpace_imp hn hpoincare)

/-- For `1 ≤ n`, Mathlib's smooth Poincaré statement
`ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n` is equivalent to the same statement
restricted to compact path-connected second-countable smooth `n`-manifolds. -/
theorem nonemptyDiffeomorphSphere_iff_of_one_le (M : Type*) [TopologicalSpace M] [T2Space M]
    {n : ℕ} (hn : 1 ≤ n) :
    NonemptyDiffeomorphSphere M n ↔
      ∀ (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M) (_ : IsManifold (𝓡 n) ∞ M)
        [CompactSpace M] [PathConnectedSpace M] [SecondCountableTopology M],
        (M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) →
          Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  constructor
  · intro h c hm _ _ _ e
    exact h c hm e
  · intro h c hm e
    have := e.compactSpace_of_sphere_euclideanSpace finrank_euclideanSpace_fin
    have := e.pathConnectedSpace_of_sphere (one_lt_rank_of_one_lt_finrank (by simp; lia))
      zero_le_one
    have := e.secondCountableTopology_of_sphere_euclideanSpace finrank_euclideanSpace_fin
    exact h c hm e

/-- For `2 ≤ n`, Mathlib's smooth Poincaré statement
`ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n` is equivalent to the same statement
restricted to compact simply connected second-countable smooth `n`-manifolds. -/
theorem nonemptyDiffeomorphSphere_iff_of_two_le (M : Type*) [TopologicalSpace M] [T2Space M]
    {n : ℕ} (hn : 2 ≤ n) :
    NonemptyDiffeomorphSphere M n ↔
      ∀ (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M) (_ : IsManifold (𝓡 n) ∞ M)
        [CompactSpace M] [SecondCountableTopology M] [SimplyConnectedSpace M],
        (M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) →
          Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  ⟨fun h c hm _ _ _ e ↦ h c hm e, fun h ↦
    nonemptyDiffeomorphSphere_of_compactSpace_simplyConnectedSpace_imp hn fun e ↦
      h inferInstance inferInstance e⟩

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
    have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by lia)
    have := e.compactSpace_of_sphere hE hF
    have := e.pathConnectedSpace_of_sphere (one_lt_rank_of_one_lt_finrank (by lia)) zero_le_one
    have := e.secondCountableTopology_of_sphere hE hF
    exact h e

/-- For `2 ≤ n`, the topological generalized Poincaré statement on a Hausdorff `n`-manifold `M`
(homotopy equivalence to `Sⁿ` implies homeomorphism to `Sⁿ`) is equivalent to the same statement
assuming `M` is compact, second countable, and simply connected. -/
theorem nonempty_homeomorph_sphere_of_homotopyEquiv_iff_of_two_le (M : Type*)
    [TopologicalSpace M] [T2Space M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) (hn : 2 ≤ n) :
    ((M ≃ₕ sphere (0 : F) 1) → Nonempty (M ≃ₜ sphere (0 : F) 1)) ↔
      ∀ [CompactSpace M] [SecondCountableTopology M] [SimplyConnectedSpace M],
        (M ≃ₕ sphere (0 : F) 1) → Nonempty (M ≃ₜ sphere (0 : F) 1) := by
  refine ⟨fun h _ _ _ e ↦ h e, fun h e ↦ ?_⟩
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by lia)
  exact nonempty_homeomorph_sphere_of_compactSpace_simplyConnectedSpace_imp hn hE hF e (h e)

end Reduction

end ContinuousMap.HomotopyEquiv

namespace TauCeti

/-- **No noncompact Hausdorff `n`-manifold is homotopy equivalent to an `n`-sphere of positive
radius.** -/
theorem isEmpty_homotopyEquiv_sphere_of_noncompactSpace_of_pos {M : Type*} [TopologicalSpace M]
    [T2Space M] [NoncompactSpace M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {c : F} {r : ℝ} {n : ℕ} (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) (hr : 0 < r) :
    IsEmpty (M ≃ₕ sphere c r) :=
  ⟨fun e ↦ not_compactSpace_iff.mpr ‹_› (e.compactSpace_of_sphere_of_pos hE hF hr)⟩

/-- **No noncompact Hausdorff `n`-manifold is homotopy equivalent to `Sⁿ`.** -/
theorem isEmpty_homotopyEquiv_sphere_of_noncompactSpace {M : Type*} [TopologicalSpace M]
    [T2Space M] [NoncompactSpace M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) :
    IsEmpty (M ≃ₕ sphere (0 : F) 1) :=
  isEmpty_homotopyEquiv_sphere_of_noncompactSpace_of_pos hE hF one_pos

/-- **No real normed space is homotopy equivalent to a sphere of positive radius of the same
dimension.** When `finrank ℝ E = n` and `finrank ℝ F = n + 1` with `0 < r`, no homotopy equivalence
`E ≃ₕ sphere c r` exists: for `n = 0`, `E` is path connected while `sphere c r` has two path
components; for `n ≥ 1`, `E` is noncompact. -/
theorem isEmpty_homotopyEquiv_normedSpace_sphere_of_pos {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) {c : F} {r : ℝ} (hr : 0 < r) :
    IsEmpty (E ≃ₕ sphere c r) := by
  cases n with
  | zero =>
    refine ⟨fun e ↦ ?_⟩
    have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
    obtain ⟨p⟩ : Nonempty (sphere (0 : F) 1) :=
      (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
    let e₁ : E ≃ₕ sphere (0 : F) 1 :=
      e.trans (sphereHomeomorphOfPos c hr).symm.toHomotopyEquiv
    have hpath : ZerothHomotopy.mk (e₁.symm (-p)) = ZerothHomotopy.mk (e₁.symm p) :=
      Quotient.sound (PathConnectedSpace.joined _ _)
    have hp : ZerothHomotopy.mk (-p) = ZerothHomotopy.mk p := by
      apply e₁.zerothHomotopyCongr.symm.injective
      simpa only [ContinuousMap.HomotopyEquiv.zerothHomotopyCongr_symm_mk] using hpath
    exact zerothHomotopy_mk_neg_ne hF p hp
  | succ _ =>
    have : FiniteDimensional ℝ E := .of_finrank_pos (by lia)
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
    exact isEmpty_homotopyEquiv_sphere_of_noncompactSpace_of_pos hE hF hr

/-- **A real normed space is not homotopy equivalent to the unit sphere of the same dimension.**
When `finrank ℝ E = n` and `finrank ℝ F = n + 1`, no homotopy equivalence `E ≃ₕ sphere (0 : F) 1`
exists, for any `n : ℕ` (including `n = 0`). -/
theorem isEmpty_homotopyEquiv_normedSpace_sphere {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) :
    IsEmpty (E ≃ₕ sphere (0 : F) 1) :=
  isEmpty_homotopyEquiv_normedSpace_sphere_of_pos hE hF one_pos

/-- Euclidean space `ℝⁿ` is not homotopy equivalent to `Sⁿ`, for any `n : ℕ`. -/
theorem isEmpty_homotopyEquiv_euclideanSpace_sphere (n : ℕ) :
    IsEmpty (EuclideanSpace ℝ (Fin n) ≃ₕ
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  isEmpty_homotopyEquiv_normedSpace_sphere finrank_euclideanSpace_fin finrank_euclideanSpace_fin

/-- **No proper open subset of a preconnected Hausdorff `n`-manifold is homotopy equivalent to an
`n`-sphere of positive radius.** -/
theorem isEmpty_homotopyEquiv_sphere_of_isOpen_ne_univ_of_pos {M : Type*} [TopologicalSpace M]
    [T2Space M] [PreconnectedSpace M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {c : F} {r : ℝ} {n : ℕ} (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1)
    {U : Set M} (hUo : IsOpen U) (hU : U ≠ Set.univ) (hr : 0 < r) :
    IsEmpty (U ≃ₕ sphere c r) := by
  refine ⟨fun e ↦ hU ?_⟩
  have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  have : Nonempty (sphere c r) := (NormedSpace.sphere_nonempty.mpr hr.le).to_subtype
  obtain ⟨x⟩ := e.symm.nonempty
  let _ : ChartedSpace E U := TopologicalSpace.Opens.instChartedSpace ⟨U, hUo⟩
  have hUc : IsCompact U :=
    isCompact_iff_compactSpace.mpr (e.compactSpace_of_sphere_of_pos hE hF hr)
  exact IsClopen.eq_univ ⟨hUc.isClosed, hUo⟩ ⟨x.val, x.property⟩

/-- **No proper open subset of a preconnected Hausdorff `n`-manifold is homotopy equivalent to
`Sⁿ`.** -/
theorem isEmpty_homotopyEquiv_sphere_of_isOpen_ne_univ {M : Type*} [TopologicalSpace M] [T2Space M]
    [PreconnectedSpace M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : ℕ} (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) {U : Set M}
    (hUo : IsOpen U) (hU : U ≠ Set.univ) :
    IsEmpty (U ≃ₕ sphere (0 : F) 1) :=
  isEmpty_homotopyEquiv_sphere_of_isOpen_ne_univ_of_pos hE hF hUo hU one_pos

-- Dimension-matching sharpness check: for a nontrivial real normed space `F`, the cylinder
-- `sphere (0 : F) 1 × ℝ` is homotopy equivalent to `sphere (0 : F) 1` yet noncompact.
example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Nontrivial F] :
    Nonempty ((sphere (0 : F) 1 × ℝ) ≃ₕ sphere (0 : F) 1) ∧
      NoncompactSpace (sphere (0 : F) 1 × ℝ) := by
  have : Nonempty (sphere (0 : F) 1) := (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  exact ⟨⟨ContinuousMap.HomotopyEquiv.prodContractible _ ℝ⟩, inferInstance⟩

-- Radius-positivity sharpness check: `0 < r` cannot be weakened to `0 ≤ r` in
-- `compactSpace_of_sphere_of_pos` or `isEmpty_homotopyEquiv_normedSpace_sphere_of_pos`, since at
-- `r = 0` the sphere `sphere 0 0` is a singleton and therefore homotopy equivalent to `ℝ³`.
example :
    Nonempty (EuclideanSpace ℝ (Fin 3) ≃ₕ
      sphere (0 : EuclideanSpace ℝ (Fin 4)) 0) := by
  rw [Metric.sphere_zero]
  obtain ⟨e₁⟩ := ContractibleSpace.hequiv_unit (EuclideanSpace ℝ (Fin 3))
  obtain ⟨e₂⟩ := ContractibleSpace.hequiv_unit ({(0 : EuclideanSpace ℝ (Fin 4))} : Set _)
  exact ⟨e₁.trans e₂.symm⟩

end TauCeti
