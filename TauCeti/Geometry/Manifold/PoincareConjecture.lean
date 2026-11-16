/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Geometry.Manifold.PoincareConjecture
public import TauCeti.Geometry.Manifold.Smoothable
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Noncompact
import TauCeti.AlgebraicTopology.Singular.Sphere
import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
import TauCeti.AlgebraicTopology.Sphere.Zero
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Topology.Homotopy.HomotopyEquiv

/-!
# Topological hypotheses of the generalized Poincaré conjecture

Mathlib's smooth generalized Poincaré predicate
`ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n` asks only for a Hausdorff smooth
`n`-manifold `M` without boundary and a homotopy equivalence `M ≃ₕ 𝕊ⁿ`, without assuming
compactness, simple connectivity or second countability of `M`. This file recovers all three
topological properties from the homotopy equivalence itself, for arbitrary topological manifolds
without boundary, and deduces the corresponding reductions of the smooth and topological
homotopy-equivalence Poincaré problems.

Let `M` be a Hausdorff space charted on a finite-dimensional real normed space `E` of dimension `n`,
and let `e : M ≃ₕ sphere c r` be a homotopy equivalence to a sphere of positive radius `r > 0` in a
real normed space `F` of dimension `n + 1`:

* **Compactness** (`ContinuousMap.HomotopyEquiv.compactSpace_of_sphere`): for `n = 0`, `M` is
  discrete and `ZerothHomotopy M` is in bijection with the two-element set of path components of the
  `0`-sphere, so `M` is finite; for `n ≥ 1`, the `n`-sphere is path-connected with
  `Hₙ(Sⁿ; ℤ) ≅ ℤ ≠ 0`, so `M` is path-connected and cannot be noncompact by Hatcher's Proposition
  3.29 (`TauCeti.compactSpace_of_not_isZero_singularHomology`). Positivity of `r` is essential: at
  `r = 0`, `sphere c 0 = {c}` is contractible and therefore homotopy equivalent to `E` itself.
* **Second countability** (`ContinuousMap.HomotopyEquiv.secondCountableTopology_of_sphere`): a
  compact space is Lindelöf, and a Lindelöf space charted on a finite-dimensional real normed space
  is second-countable (`ChartedSpace.secondCountable_of_lindelof`).
* **Simple connectivity** (`ContinuousMap.HomotopyEquiv.simplyConnectedSpace_of_sphere`,
  `ContinuousMap.HomotopyEquiv.simplyConnectedSpace_of_sphere_of_two_lt_rank`): when `dim_ℝ F ≥ 3`
  (that is, `n ≥ 2`), `sphere c r` is simply connected (`TauCeti.simplyConnectedSpace_sphere`) and
  simple connectivity is invariant under homotopy equivalence.

Consequently, for `n ≥ 2`, `ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n` is equivalent
to the closed simply connected second-countable formulation
(`ContinuousMap.HomotopyEquiv.nonemptyDiffeomorphSphere_iff_of_two_le`), and a topological manifold
`M ≃ₕ 𝕊ⁿ` that is smoothable once compact and second-countable (`TauCeti.IsSmoothable (𝓡 n) M`) is
homeomorphic to `𝕊ⁿ` whenever `NonemptyDiffeomorphSphere M n` holds
(`ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_isSmoothable`). Contrapositively, no
noncompact Hausdorff `n`-manifold—and in particular no positive-dimensional real normed space
`E`—is homotopy equivalent to a sphere of positive radius in dimension `n + 1`
(`TauCeti.isEmpty_homotopyEquiv_sphere_of_noncompactSpace`), and in dimension `n = 0` the same holds
because `E` is path-connected while the `0`-sphere has two path components
(`TauCeti.isEmpty_homotopyEquiv_sphere_of_finrank_succ`).

## Main results

* `ContinuousMap.HomotopyEquiv.compactSpace_of_sphere` and
  `ContinuousMap.HomotopyEquiv.compactSpace_of_sphere_euclideanSpace`: a Hausdorff `n`-manifold
  without boundary homotopy equivalent to an `n`-sphere of positive radius is compact.
* `ContinuousMap.HomotopyEquiv.secondCountableTopology_of_sphere` and
  `ContinuousMap.HomotopyEquiv.secondCountableTopology_of_sphere_euclideanSpace`: such a manifold is
  second-countable.
* `ContinuousMap.HomotopyEquiv.nonemptyDiffeomorphSphere_iff_of_two_le` and
  `ContinuousMap.HomotopyEquiv.nonemptyDiffeomorphSphere_of_simplyConnected`: for `n ≥ 2`, Mathlib's
  `NonemptyDiffeomorphSphere M n` reduces to compact simply connected second-countable smooth
  manifolds.
* `ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_simplyConnected`,
  `ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_isSmoothable`, and
  `ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere_of_isSmoothable_of_simplyConnected`: the
  corresponding topological reductions, directly and through `TauCeti.IsSmoothable`.
* `TauCeti.isEmpty_homotopyEquiv_sphere_of_noncompactSpace`,
  `TauCeti.isEmpty_homotopyEquiv_sphere_of_finrank_succ`, and
  `TauCeti.isEmpty_homotopyEquiv_sphere_euclideanSpace`: noncompact `n`-manifolds and
  `n`-dimensional real normed spaces are never homotopy equivalent to `n`-spheres of positive
  radius.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Proposition 3.29.
* J. Milnor, *Lectures on the h-Cobordism Theorem*, Princeton University Press, 1965, §9.
-/

public section

open AlgebraicTopology CategoryTheory ContinuousMap Metric Module Topology
open scoped ContDiff Manifold

local macro:max "ℝ" noWs n:superscript(term) : term => `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))
local macro:max "𝕊" noWs n:superscript(term) : term =>
  `(sphere (0 : EuclideanSpace ℝ (Fin ($(⟨n.raw[0]⟩) + 1))) 1)

universe u v w

namespace ContinuousMap.HomotopyEquiv

section TopologicalInvariants

/-- **A topological `n`-manifold homotopy equivalent to an `n`-sphere is compact.** If `M` is a
Hausdorff space charted on a finite-dimensional real normed space `E` of dimension `n`, and `M` is
homotopy equivalent to a sphere of positive radius in a real normed space `F` of dimension `n + 1`,
then `M` is compact. -/
theorem compactSpace_of_sphere {M : Type u} [TopologicalSpace M] [T2Space M]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {c : F} {r : ℝ} (e : M ≃ₕ sphere c r) (hEF : finrank ℝ E + 1 = finrank ℝ F)
    (hr : 0 < r) : CompactSpace M := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by lia)
  cases hn : finrank ℝ E with
  | zero =>
    let V : Type u := EuclideanSpace ℝ (ULift.{u} (Fin 1))
    have hV1 : finrank ℝ V = 1 := TauCeti.finrank_euclideanSpace_ulift_fin.{u} 1
    have hFV_dim : finrank ℝ F = finrank ℝ V := (by lia : finrank ℝ F = 1).trans hV1.symm
    let eV : M ≃ₕ sphere (0 : V) 1 :=
      e.trans ((TauCeti.sphereHomeomorphOfPos c hr).symm.trans
        (TauCeti.sphereHomeomorphOfFinrankEq hFV_dim)).toHomotopyEquiv
    have : Subsingleton E := Module.finrank_zero_iff.mp hn
    have : DiscreteTopology M := ChartedSpace.discreteTopology E M
    have : Finite (sphere (0 : V) 1) := TauCeti.finite_sphere_of_finrank_eq_one hV1 0 1
    have : Finite (ZerothHomotopy (sphere (0 : V) 1)) :=
      Finite.of_surjective _ ZerothHomotopy.mk_surjective
    have : Finite (ZerothHomotopy M) := Finite.of_equiv _ eV.zerothHomotopyCongr.symm
    have : Finite M :=
      Finite.of_injective _ ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace
    exact Finite.compactSpace
  | succ d =>
    let V : Type u := EuclideanSpace ℝ (ULift.{u} (Fin (d + 2)))
    have hV : finrank ℝ V = d + 2 := TauCeti.finrank_euclideanSpace_ulift_fin.{u} (d + 2)
    have hFV_dim : finrank ℝ F = finrank ℝ V := (by lia : finrank ℝ F = d + 2).trans hV.symm
    let eV : M ≃ₕ sphere (0 : V) 1 :=
      e.trans ((TauCeti.sphereHomeomorphOfPos c hr).symm.trans
        (TauCeti.sphereHomeomorphOfFinrankEq hFV_dim)).toHomotopyEquiv
    have hrankV : 1 < Module.rank ℝ V := by
      rw [← Module.finrank_eq_rank, hV]
      exact_mod_cast (by lia : 1 < d + 2)
    have : PathConnectedSpace (sphere (0 : V) 1) :=
      isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hrankV 0 zero_le_one)
    have : PathConnectedSpace M := eV.symm.pathConnectedSpace
    let R : ModuleCat.{u} (ULift.{u} ℤ) := ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ)
    let eTop : M ≃ₕ TopCat.sphere.{u} (d + 1) :=
      eV.trans (TauCeti.diskBoundaryHomeomorph.{u} (d + 2)).symm.toHomotopyEquiv
    let isoM :
        (((singularHomologyFunctor (ModuleCat.{u} (ULift.{u} ℤ)) (d + 1)).obj R).obj
          (TopCat.of M)) ≅ R :=
      eTop.singularHomologyIso R (d + 1) ≪≫
        ((TauCeti.reducedSingularHomologySuccIso R d).app (TopCat.sphere.{u} (d + 1))).symm ≪≫
        TauCeti.reducedSingularHomologyTopCatSphereIso R (d + 1)
    refine TauCeti.compactSpace_of_not_isZero_singularHomology (E := E) R (k := d + 1)
      (by lia) fun hzero ↦ ?_
    have hR : Subsingleton (ULift.{u} ℤ) :=
      ModuleCat.isZero_iff_subsingleton.mp (hzero.of_iso isoM.symm)
    exact zero_ne_one (ULift.up_injective (hR.elim ⟨0⟩ ⟨1⟩))

/-- **A Hausdorff space charted on `ℝⁿ` and homotopy equivalent to `𝕊ⁿ` is compact.** -/
theorem compactSpace_of_sphere_euclideanSpace {M : Type u} [TopologicalSpace M] [T2Space M]
    {n : ℕ} [ChartedSpace ℝⁿ M] (e : M ≃ₕ 𝕊ⁿ) : CompactSpace M :=
  e.compactSpace_of_sphere (E := ℝⁿ) (by simp) one_pos

/-- **A topological `n`-manifold homotopy equivalent to an `n`-sphere is second-countable.** -/
theorem secondCountableTopology_of_sphere {M : Type u} [TopologicalSpace M] [T2Space M]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {c : F} {r : ℝ} (e : M ≃ₕ sphere c r) (hEF : finrank ℝ E + 1 = finrank ℝ F)
    (hr : 0 < r) : SecondCountableTopology M := by
  have : CompactSpace M := e.compactSpace_of_sphere hEF hr
  exact ChartedSpace.secondCountable_of_lindelof E M

/-- **A Hausdorff space charted on `ℝⁿ` and homotopy equivalent to `𝕊ⁿ` is second-countable.** -/
theorem secondCountableTopology_of_sphere_euclideanSpace {M : Type u} [TopologicalSpace M]
    [T2Space M] {n : ℕ} [ChartedSpace ℝⁿ M] (e : M ≃ₕ 𝕊ⁿ) : SecondCountableTopology M :=
  e.secondCountableTopology_of_sphere (E := ℝⁿ) (by simp) one_pos

end TopologicalInvariants

section PoincareReductions

/-- **Closed simply connected reduction of the smooth Poincaré conjecture.** For `2 ≤ n`, Mathlib's
`ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n` holds if and only if every compact,
simply connected, second-countable smooth `n`-manifold structure on `M` that is homotopy equivalent
to `𝕊ⁿ` is diffeomorphic to `𝕊ⁿ`. -/
theorem nonemptyDiffeomorphSphere_iff_of_two_le {M : Type u} [TopologicalSpace M] [T2Space M]
    {n : ℕ} (hn : 2 ≤ n) :
    NonemptyDiffeomorphSphere M n ↔
      ∀ (_ : ChartedSpace ℝⁿ M) (_ : IsManifold (𝓡 n) ∞ M),
        CompactSpace M → SimplyConnectedSpace M → SecondCountableTopology M →
          M ≃ₕ 𝕊ⁿ → Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ 𝕊ⁿ) :=
  ⟨fun h c hm _ _ _ e ↦ h c hm e, fun h c hm e ↦
    h c hm e.compactSpace_of_sphere_euclideanSpace
      (e.simplyConnectedSpace_of_sphere_euclideanSpace hn)
      e.secondCountableTopology_of_sphere_euclideanSpace e⟩

/-- **Smooth Poincaré from the closed simply connected case, without the homotopy-equivalence
premise.** For `2 ≤ n` (in particular for `n = 3`), to prove `NonemptyDiffeomorphSphere M n` it
suffices to show—without assuming `M ≃ₕ 𝕊ⁿ`—that every compact, simply connected, second-countable
smooth `n`-manifold structure on `M` is diffeomorphic to `𝕊ⁿ`. -/
theorem nonemptyDiffeomorphSphere_of_simplyConnected {M : Type u} [TopologicalSpace M] [T2Space M]
    {n : ℕ} (hn : 2 ≤ n)
    (h : ∀ (_ : ChartedSpace ℝⁿ M) (_ : IsManifold (𝓡 n) ∞ M),
      CompactSpace M → SimplyConnectedSpace M → SecondCountableTopology M →
        Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ 𝕊ⁿ)) :
    NonemptyDiffeomorphSphere M n :=
  (nonemptyDiffeomorphSphere_iff_of_two_le hn).2 fun c hm hcpt hsc hsec _ ↦ h c hm hcpt hsc hsec

/-- **Closed simply connected reduction of the topological homotopy-equivalence Poincaré problem.**
If `M` is a Hausdorff `n`-manifold (`2 ≤ n`) without boundary homotopy equivalent to an `n`-sphere
`sphere c r` of positive radius, to construct a homeomorphism `M ≃ₜ sphere c r` it suffices to
treat the case where `M` is compact, simply connected, and second-countable. -/
theorem nonempty_homeomorph_sphere_of_simplyConnected {M : Type u} [TopologicalSpace M] [T2Space M]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {c : F} {r : ℝ} (e : M ≃ₕ sphere c r) (hEF : finrank ℝ E + 1 = finrank ℝ F)
    (hE : 2 ≤ finrank ℝ E) (hr : 0 < r)
    (h : CompactSpace M → SimplyConnectedSpace M → SecondCountableTopology M →
      Nonempty (M ≃ₜ sphere c r)) :
    Nonempty (M ≃ₜ sphere c r) :=
  h (e.compactSpace_of_sphere hEF hr)
    (e.simplyConnectedSpace_of_sphere (by lia) hr.le)
    (e.secondCountableTopology_of_sphere hEF hr)

/-- **Topological Poincaré from smoothing and smooth Poincaré.** If a Hausdorff space `M` charted
on `ℝⁿ` and homotopy equivalent to `𝕊ⁿ` admits a smooth `n`-manifold structure whenever it is
compact and second-countable (`TauCeti.IsSmoothable (𝓡 n) M`), and `NonemptyDiffeomorphSphere M n`
holds, then `M` is homeomorphic to `𝕊ⁿ`. -/
theorem nonempty_homeomorph_sphere_of_isSmoothable {M : Type u} [TopologicalSpace M] [T2Space M]
    {n : ℕ} [ChartedSpace ℝⁿ M] (e : M ≃ₕ 𝕊ⁿ)
    (hsmooth : CompactSpace M → SecondCountableTopology M → TauCeti.IsSmoothable (𝓡 n) M)
    (hpoincare : NonemptyDiffeomorphSphere M n) :
    Nonempty (M ≃ₜ 𝕊ⁿ) := by
  obtain ⟨c_smooth, h_man⟩ :=
    TauCeti.isSmoothable_iff.mp
      (hsmooth e.compactSpace_of_sphere_euclideanSpace
        e.secondCountableTopology_of_sphere_euclideanSpace)
  obtain ⟨d⟩ := hpoincare c_smooth h_man e
  exact ⟨d.toHomeomorph⟩

/-- **Topological Poincaré from smoothing and closed simply connected smooth Poincaré.** Combines
`nonempty_homeomorph_sphere_of_isSmoothable` and `nonemptyDiffeomorphSphere_iff_of_two_le` for
`2 ≤ n`. -/
theorem nonempty_homeomorph_sphere_of_isSmoothable_of_simplyConnected {M : Type u}
    [TopologicalSpace M] [T2Space M] {n : ℕ} [ChartedSpace ℝⁿ M] (e : M ≃ₕ 𝕊ⁿ) (hn : 2 ≤ n)
    (hsmooth : CompactSpace M → SimplyConnectedSpace M → SecondCountableTopology M →
      TauCeti.IsSmoothable (𝓡 n) M)
    (hpoincare : ∀ (_ : ChartedSpace ℝⁿ M) (_ : IsManifold (𝓡 n) ∞ M),
      CompactSpace M → SimplyConnectedSpace M → SecondCountableTopology M →
        M ≃ₕ 𝕊ⁿ → Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ 𝕊ⁿ)) :
    Nonempty (M ≃ₜ 𝕊ⁿ) :=
  e.nonempty_homeomorph_sphere_of_isSmoothable
    (fun hcpt hsec ↦ hsmooth hcpt (e.simplyConnectedSpace_of_sphere_euclideanSpace hn) hsec)
    ((nonemptyDiffeomorphSphere_iff_of_two_le hn).2 hpoincare)

end PoincareReductions

end ContinuousMap.HomotopyEquiv

namespace TauCeti

/-- **No noncompact Hausdorff `n`-manifold without boundary is homotopy equivalent to an `n`-sphere
of positive radius.** -/
theorem isEmpty_homotopyEquiv_sphere_of_noncompactSpace {M : Type u} [TopologicalSpace M]
    [T2Space M] [NoncompactSpace M] {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] {F : Type w} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {c : F} {r : ℝ} (hEF : finrank ℝ E + 1 = finrank ℝ F) (hr : 0 < r) :
    IsEmpty (M ≃ₕ sphere c r) :=
  ⟨fun e ↦ not_compactSpace_iff.mpr ‹NoncompactSpace M› (e.compactSpace_of_sphere hEF hr)⟩

/-- **No finite-dimensional real normed space `E` is homotopy equivalent to a sphere of positive
radius in dimension `finrank ℝ E + 1`.** For `finrank ℝ E > 0`, `E` is noncompact; for
`finrank ℝ E = 0`, `E` is path-connected while the `0`-sphere of positive radius has two path
components. -/
theorem isEmpty_homotopyEquiv_sphere_of_finrank_succ {E : Type v} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {F : Type w} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {c : F} {r : ℝ} (hEF : finrank ℝ E + 1 = finrank ℝ F) (hr : 0 < r) :
    IsEmpty (E ≃ₕ sphere c r) := by
  rcases Nat.eq_zero_or_pos (finrank ℝ E) with hE0 | hEpos
  · refine ⟨fun e ↦ ?_⟩
    have hF1 : finrank ℝ F = 1 := by lia
    have : Nontrivial F := Module.nontrivial_of_finrank_pos (by lia : 0 < finrank ℝ F)
    obtain ⟨p⟩ : Nonempty (sphere (0 : F) 1) :=
      (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
    let e₁ : E ≃ₕ sphere (0 : F) 1 := e.trans (sphereHomeomorphOfPos c hr).symm.toHomotopyEquiv
    have hpath : ZerothHomotopy.mk (e₁.symm (-p)) = ZerothHomotopy.mk (e₁.symm p) :=
      Quotient.sound (PathConnectedSpace.joined _ _)
    have hp : ZerothHomotopy.mk (-p) = ZerothHomotopy.mk p := by
      apply e₁.zerothHomotopyCongr.symm.injective
      simpa only [ContinuousMap.HomotopyEquiv.zerothHomotopyCongr_symm_mk] using hpath
    exact zerothHomotopy_mk_neg_ne hF1 p hp
  · have : Nontrivial E := Module.nontrivial_of_finrank_pos hEpos
    exact isEmpty_homotopyEquiv_sphere_of_noncompactSpace hEF hr

/-- **Euclidean `n`-space `ℝⁿ` is not homotopy equivalent to `𝕊ⁿ`, for any `n : ℕ`.** -/
theorem isEmpty_homotopyEquiv_sphere_euclideanSpace (n : ℕ) : IsEmpty (ℝⁿ ≃ₕ 𝕊ⁿ) :=
  isEmpty_homotopyEquiv_sphere_of_finrank_succ (by simp) one_pos

section Checks

-- Sanity check: `𝕊³` satisfies all hypotheses of `compactSpace_of_sphere_euclideanSpace`,
-- `secondCountableTopology_of_sphere_euclideanSpace`, and
-- `simplyConnectedSpace_of_sphere_euclideanSpace`.
private example : CompactSpace 𝕊³ ∧ SecondCountableTopology 𝕊³ ∧ SimplyConnectedSpace 𝕊³ := by
  let e : 𝕊³ ≃ₕ 𝕊³ := ContinuousMap.HomotopyEquiv.refl 𝕊³
  exact ⟨e.compactSpace_of_sphere_euclideanSpace,
    e.secondCountableTopology_of_sphere_euclideanSpace,
    e.simplyConnectedSpace_of_sphere_euclideanSpace (by decide)⟩

-- Sanity check: `ℝ³` is a simply connected smooth `3`-manifold without boundary, yet
-- `isEmpty_homotopyEquiv_sphere_euclideanSpace 3` rules out any homotopy equivalence `ℝ³ ≃ₕ 𝕊³`.
private example : SimplyConnectedSpace ℝ³ ∧ IsEmpty (ℝ³ ≃ₕ 𝕊³) :=
  ⟨inferInstance, isEmpty_homotopyEquiv_sphere_euclideanSpace 3⟩

-- Sharpness check: the hypothesis `0 < r` in `compactSpace_of_sphere` and
-- `isEmpty_homotopyEquiv_sphere_of_finrank_succ` cannot be weakened to `0 ≤ r`, since at `r = 0`
-- the sphere `sphere 0 0` is a singleton and therefore homotopy equivalent to noncompact `ℝ³`.
private example : Nonempty (ℝ³ ≃ₕ sphere (0 : ℝ⁴) 0) := by
  rw [Metric.sphere_zero]
  obtain ⟨e₁⟩ := ContractibleSpace.hequiv_unit ℝ³
  obtain ⟨e₂⟩ := ContractibleSpace.hequiv_unit ({(0 : ℝ⁴)} : Set ℝ⁴)
  exact ⟨e₁.trans e₂.symm⟩

end Checks

end TauCeti
