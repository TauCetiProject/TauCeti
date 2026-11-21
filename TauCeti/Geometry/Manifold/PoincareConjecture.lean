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
to `𝕊ⁿ`; neither compactness, second countability, nor simple connectedness of `M` is assumed a
priori.

Combined with the sphere homotopy-equivalence connectivity results in
`TauCeti.AlgebraicTopology.Sphere.SimplyConnected`, this file proves that a homotopy equivalence
`e : M ≃ₕ S` from a Hausdorff topological `n`-manifold `M` without boundary to the unit sphere `S`
of an `(n + 1)`-dimensional real normed space automatically forces the closed-manifold hypotheses:

* **Dimension zero:** both `M` and `S⁰` are discrete, so `e` upgrades to a homeomorphism onto the
  two-point sphere (`ContinuousMap.HomotopyEquiv.toHomeomorphOfSphereZero`), which supplies the
  `n = 0` case of compactness.
* **Compactness and second countability (all `n : ℕ`):** for `n = d + 1`, `M` is path connected and
  `H_{d+1}(M; ℤ) ≅ H_{d+1}(S^{d+1}; ℤ) ≅ ℤ` is nontrivial, whereas Hatcher's Proposition 3.29
  (`TauCeti.compactSpace_of_nontrivial_singularHomology`) forces any preconnected Hausdorff
  `(d + 1)`-manifold with nontrivial top singular homology to be compact; hence `M` is compact
  (`ContinuousMap.HomotopyEquiv.compactSpace_of_sphere`) and second countable
  (`ContinuousMap.HomotopyEquiv.secondCountableTopology_of_sphere`).

Consequently, for `2 ≤ n`, proving `ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n` (or
its topological counterpart `M ≃ₕ 𝕊ⁿ → Nonempty (M ≃ₜ 𝕊ⁿ)`) reduces to the closed simply connected
case where `[CompactSpace M]`, `[SecondCountableTopology M]`, and `[SimplyConnectedSpace M]` are
already available
(`ContinuousMap.HomotopyEquiv.nonemptyDiffeomorphSphere_of_compactSpace_simplyConnectedSpace_imp`
and
`ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_compactSpace_simplyConnectedSpace_imp`).

The final section records non-vacuity and sharpness: no noncompact Hausdorff `n`-manifold is
homotopy equivalent to `Sⁿ` (`TauCeti.isEmpty_homotopyEquiv_sphere_of_noncompactSpace`), and in
particular `ℝⁿ⁺¹` is not homotopy equivalent to `Sⁿ⁺¹`
(`TauCeti.isEmpty_homotopyEquiv_normedSpace_sphere`). By contrast, for a nontrivial real normed
space `F`, the cylinder `sphere (0 : F) 1 × ℝ` is homotopy equivalent to `sphere (0 : F) 1` yet
noncompact: when `dim F = n + 1`, its manifold dimension is `n + 1` rather than `n`, so
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
  `0`-manifold to `S⁰` to a homeomorphism.
* `ContinuousMap.HomotopyEquiv.compactSpace_of_topCatSphere`,
  `ContinuousMap.HomotopyEquiv.compactSpace_of_sphere`, and
  `ContinuousMap.HomotopyEquiv.secondCountableTopology_of_sphere`: compactness and second
  countability of a Hausdorff `n`-manifold without boundary homotopy equivalent to `Sⁿ`.
* `ContinuousMap.HomotopyEquiv.nonemptyDiffeomorphSphere_of_compactSpace_simplyConnectedSpace_imp`
  and
  `ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_compactSpace_simplyConnectedSpace_imp`:
  reduction of the smooth and topological Poincaré statements for `2 ≤ n` to compact, second
  countable, simply connected manifolds.
* `ContinuousMap.HomotopyEquiv.nonemptyDiffeomorphSphere_iff_of_one_le`,
  `ContinuousMap.HomotopyEquiv.nonemptyDiffeomorphSphere_iff_of_two_le`,
  `ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_homotopyEquiv_iff_of_one_le`, and
  `ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_homotopyEquiv_iff_of_two_le`: the
  corresponding equivalences with the restricted statements.
* `TauCeti.isEmpty_homotopyEquiv_sphere_of_noncompactSpace`,
  `TauCeti.isEmpty_homotopyEquiv_normedSpace_sphere`, and
  `TauCeti.isEmpty_homotopyEquiv_euclideanSpace_sphere`: nonexistence of homotopy equivalences from
  noncompact `n`-manifolds (and `(n + 1)`-dimensional normed/Euclidean spaces) to spheres of the
  same dimension.
* `TauCeti.isEmpty_homotopyEquiv_sphere_of_isOpen_ne_univ`: no proper open subset of a
  preconnected Hausdorff `n`-manifold is homotopy equivalent to `Sⁿ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Proposition 3.29, p. 239.
-/

public section

open AlgebraicTopology CategoryTheory Metric Module
open scoped ContinuousMap Manifold ContDiff

universe u

namespace ContinuousMap.HomotopyEquiv

section DimensionZero

variable {M : Type*} [TopologicalSpace M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Zero-dimensional topological Poincaré theorem.** Upgrade a homotopy equivalence
`e : M ≃ₕ sphere (0 : F) 1` from a `0`-dimensional manifold `M` to the unit sphere `S⁰` of a
`1`-dimensional real normed space to a homeomorphism with the same underlying forward and inverse
maps. -/
def toHomeomorphOfSphereZero (e : M ≃ₕ sphere (0 : F) 1) (hE : finrank ℝ E = 0)
    (hF : finrank ℝ F = 1) : M ≃ₜ sphere (0 : F) 1 :=
  have : Subsingleton E := (Module.finrank_eq_zero_iff_of_free ℝ E).1 hE
  have := ChartedSpace.discreteTopology E M
  have := TauCeti.discreteTopology_sphere_of_finrank_eq_one hF 0 1
  e.toHomeomorphOfTotallyDisconnectedSpace

@[simp]
theorem coe_toHomeomorphOfSphereZero (e : M ≃ₕ sphere (0 : F) 1) (hE : finrank ℝ E = 0)
    (hF : finrank ℝ F = 1) :
    ⇑(e.toHomeomorphOfSphereZero hE hF) = ⇑e := by
  simp [toHomeomorphOfSphereZero]

@[simp]
theorem coe_toHomeomorphOfSphereZero_symm (e : M ≃ₕ sphere (0 : F) 1) (hE : finrank ℝ E = 0)
    (hF : finrank ℝ F = 1) :
    ⇑(e.toHomeomorphOfSphereZero hE hF).symm = ⇑e.symm := by
  simp [toHomeomorphOfSphereZero]

@[simp]
theorem toHomeomorphOfSphereZero_toHomotopyEquiv (e : M ≃ₕ sphere (0 : F) 1)
    (hE : finrank ℝ E = 0) (hF : finrank ℝ F = 1) :
    (e.toHomeomorphOfSphereZero hE hF).toHomotopyEquiv = e := by
  simp [toHomeomorphOfSphereZero]

@[simp]
theorem _root_.Homeomorph.toHomotopyEquiv_toHomeomorphOfSphereZero
    (h : M ≃ₜ sphere (0 : F) 1) (hE : finrank ℝ E = 0) (hF : finrank ℝ F = 1) :
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
  have := e.secondCountableTopology_of_sphere finrank_euclideanSpace_fin finrank_euclideanSpace_fin
  have := e.simplyConnectedSpace_of_sphere_euclideanSpace hn
  exact h e

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
    have := e.secondCountableTopology_of_sphere finrank_euclideanSpace_fin
      finrank_euclideanSpace_fin
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

/-- **No noncompact Hausdorff `n`-manifold is homotopy equivalent to `Sⁿ`.** -/
theorem isEmpty_homotopyEquiv_sphere_of_noncompactSpace {M : Type*} [TopologicalSpace M]
    [T2Space M] [NoncompactSpace M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) :
    IsEmpty (M ≃ₕ sphere (0 : F) 1) :=
  ⟨fun e ↦ not_compactSpace_iff.2 ‹_› (e.compactSpace_of_sphere hE hF)⟩

/-- **A positive-dimensional real normed space is not homotopy equivalent to the sphere of the same
dimension.** When `finrank ℝ E = n + 1` and `finrank ℝ F = n + 2`, no homotopy equivalence
`E ≃ₕ sphere (0 : F) 1` exists. -/
theorem isEmpty_homotopyEquiv_normedSpace_sphere {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (hE : finrank ℝ E = n + 1) (hF : finrank ℝ F = n + 2) :
    IsEmpty (E ≃ₕ sphere (0 : F) 1) := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by lia)
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  exact isEmpty_homotopyEquiv_sphere_of_noncompactSpace hE hF

/-- Euclidean space `ℝⁿ⁺¹` is not homotopy equivalent to `Sⁿ⁺¹`. -/
theorem isEmpty_homotopyEquiv_euclideanSpace_sphere (n : ℕ) :
    IsEmpty (EuclideanSpace ℝ (Fin (n + 1)) ≃ₕ
      sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
  isEmpty_homotopyEquiv_normedSpace_sphere finrank_euclideanSpace_fin finrank_euclideanSpace_fin

/-- **No proper open subset of a preconnected Hausdorff `n`-manifold is homotopy equivalent to
`Sⁿ`.** -/
theorem isEmpty_homotopyEquiv_sphere_of_isOpen_ne_univ {M : Type*} [TopologicalSpace M] [T2Space M]
    [PreconnectedSpace M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : ℕ} (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) {U : Set M}
    (hUo : IsOpen U) (hU : U ≠ Set.univ) :
    IsEmpty (U ≃ₕ sphere (0 : F) 1) := by
  refine ⟨fun e ↦ hU ?_⟩
  have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  have : Nonempty (sphere (0 : F) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  obtain ⟨x⟩ := e.symm.nonempty
  let _ : ChartedSpace E U := TopologicalSpace.Opens.instChartedSpace ⟨U, hUo⟩
  have hUc : IsCompact U := isCompact_iff_compactSpace.2 (e.compactSpace_of_sphere hE hF)
  exact IsClopen.eq_univ ⟨hUc.isClosed, hUo⟩ ⟨x.val, x.property⟩

-- Dimension-matching sharpness check: for a nontrivial real normed space `F`, the cylinder
-- `sphere (0 : F) 1 × ℝ` is homotopy equivalent to `sphere (0 : F) 1` yet noncompact.
example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Nontrivial F] :
    Nonempty ((sphere (0 : F) 1 × ℝ) ≃ₕ sphere (0 : F) 1) ∧
      NoncompactSpace (sphere (0 : F) 1 × ℝ) := by
  have : Nonempty (sphere (0 : F) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  exact ⟨⟨ContinuousMap.HomotopyEquiv.prodContractible _ ℝ⟩, inferInstance⟩

end TauCeti
