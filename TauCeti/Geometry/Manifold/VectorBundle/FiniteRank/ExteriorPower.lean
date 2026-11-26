/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.ExteriorPower
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.CoordinateFunctor

/-!
# Smooth and holomorphic exterior powers and determinant lines

The transitions of the exterior power `⋀^j A` of a finite-rank core `A` are the compound matrices
of the transitions of `A`. Their entries are minors, polynomials in the entries of the original
transitions, so the compound matrix depends on the operator by an analytic map
(`ContinuousLinearMap.contDiff_exteriorPowerCoords`). Hence exterior powers preserve
regularity at every order `n`, including analytic regularity:

* `TauCeti.FiniteRankBundleCore.isContMDiff_exteriorPower_obj`: the exterior powers of a `C^n`
  core are `C^n` cores;
* `TauCeti.FiniteRankBundleCore.contMDiff_totalSpaceMap_exteriorPower_map`: the exterior powers
  of a bundle map with `C^n` map of total spaces again have `C^n` maps of total spaces.

In particular the determinant line `A.det = ⋀^r A` of a `C^n` core of rank `r` is a `C^n` line
bundle (`TauCeti.FiniteRankBundleCore.isContMDiff_det`), whose transitions are the determinants
of the transitions of `A` (`TauCeti.FiniteRankBundleCore.coordChange_det`), induced morphisms on
determinant lines of equal-rank `C^n` cores preserve `C^n` regularity on total spaces
(`TauCeti.FiniteRankBundleCore.contMDiff_totalSpaceMap_detMap`), and exterior and determinant wedges
of `C^n` sections are `C^n` (`TauCeti.FiniteRankBundleCore.contMDiff_wedgeSection`,
`TauCeti.FiniteRankBundleCore.contMDiff_detSection`). Over a complex
manifold, with `𝕜 = ℂ` and `n = ∞`, these are the holomorphic exterior powers and the holomorphic
determinant line bundle of a holomorphic vector bundle presented by holomorphic transition
functions.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
* M. F. Atiyah, *K-Theory*, §1.2.
-/

public section

open Bundle CategoryTheory
open scoped Manifold ContDiff

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}

/-- The exterior powers of a `C^n` core are `C^n`. For complex scalars at regularity `∞`, this is
the holomorphic structure on the exterior powers of a holomorphic core. -/
instance isContMDiff_exteriorPower_obj (j : ℕ) (A : FiniteRankBundleCore 𝕜 B)
    [A.core.IsContMDiff I n] : ((exteriorPower 𝕜 B j).obj A).core.IsContMDiff I n :=
  (CoordinateFunctor.exteriorPower 𝕜 j).isContMDiff_mapCore A
    (ContinuousLinearMap.contDiff_exteriorPowerCoords j _ _)

/-- The determinant line of a `C^n` core is a `C^n` line bundle. For complex scalars at
regularity `∞`, this is the holomorphic determinant line bundle of a holomorphic core. -/
instance isContMDiff_det (A : FiniteRankBundleCore 𝕜 B) [A.core.IsContMDiff I n] :
    A.det.core.IsContMDiff I n :=
  det_def A ▸ isContMDiff_exteriorPower_obj A.rank A

/-- The exterior powers of a bundle map between `C^n` cores with `C^n` map of total spaces have
`C^n` maps of total spaces. -/
theorem contMDiff_totalSpaceMap_exteriorPower_map [CompleteSpace 𝕜] (j : ℕ)
    {A D : FiniteRankBundleCore 𝕜 B} [A.core.IsContMDiff I n] [D.core.IsContMDiff I n]
    (f : A ⟶ D)
    (hf : ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      f.totalSpaceMap) :
    ContMDiff (I.prod 𝓘(𝕜, Fin ((exteriorPower 𝕜 B j).obj A).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin ((exteriorPower 𝕜 B j).obj D).rank → 𝕜)) n
      ((exteriorPower 𝕜 B j).map f).totalSpaceMap := by
  -- The exterior power functor is the functor of the coordinate functor `exteriorPower 𝕜 j`;
  -- restate the instances on its objects in that form.
  have : ((CoordinateFunctor.exteriorPower 𝕜 j).mapCore A).core.IsContMDiff I n :=
    isContMDiff_exteriorPower_obj j A
  have : ((CoordinateFunctor.exteriorPower 𝕜 j).mapCore D).core.IsContMDiff I n :=
    isContMDiff_exteriorPower_obj j D
  exact (CoordinateFunctor.exteriorPower 𝕜 j).contMDiff_totalSpaceMap_mapHom
    (ContinuousLinearMap.contDiff_exteriorPowerCoords j _ _) f hf

/-- The induced morphism on determinant line bundles of a `C^n` bundle map between `C^n` cores of
equal rank is `C^n` on total spaces. -/
theorem contMDiff_totalSpaceMap_detMap [CompleteSpace 𝕜]
    {A D : FiniteRankBundleCore 𝕜 B} [A.core.IsContMDiff I n] [D.core.IsContMDiff I n]
    (f : A ⟶ D) (hr : A.rank = D.rank)
    (hf : ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      f.totalSpaceMap) :
    ContMDiff (I.prod 𝓘(𝕜, Fin A.det.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.det.rank → 𝕜)) n
      (detMap f hr).totalSpaceMap := by
  have heq : ∀ {C₁ C₂ : FiniteRankBundleCore 𝕜 B} (h : C₁ = C₂),
      ContMDiff (I.prod 𝓘(𝕜, Fin C₁.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin C₂.rank → 𝕜)) n
        (eqToHom h).totalSpaceMap := by
    rintro _ _ rfl
    rw [eqToHom_refl]
    exact contMDiff_id.congr fun p ↦ congrFun (VectorBundleCore.CoordinateHom.totalSpaceMap_id _) p
  rw [totalSpaceMap_detMap]
  exact (heq _).comp (contMDiff_totalSpaceMap_exteriorPower_map A.rank f hf)

/-- The exterior product `wedgeSection j A s` of `j` `C^n` sections of `A` is a `C^n` section of
`(exteriorPower 𝕜 B j).obj A`, without completeness of `𝕜` or `IsContMDiff` hypotheses on `A`. -/
theorem contMDiff_wedgeSection (j : ℕ) (A : FiniteRankBundleCore 𝕜 B)
    {s : Fin j → ∀ x, A.core.Fiber x}
    (hs : ∀ k, ContMDiff I (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      fun x ↦ TotalSpace.mk' (Fin A.rank → 𝕜) x (s k x)) :
    ContMDiff I (I.prod 𝓘(𝕜, Fin ((exteriorPower 𝕜 B j).obj A).rank → 𝕜)) n
      fun x ↦ TotalSpace.mk' (Fin ((exteriorPower 𝕜 B j).obj A).rank → 𝕜) x
        (wedgeSection j A s x) := by
  intro x₀
  have hc (k : Fin j) :
      ContMDiffAt I 𝓘(𝕜, Fin A.rank → 𝕜) n
        (fun x ↦ (A.core.localTriv x₀ ⟨x, s k x⟩).2) x₀ := by
    have h := (Bundle.contMDiffAt_totalSpace_iff.1 (hs k x₀)).2
    rwa [show (TotalSpace.mk' (Fin A.rank → 𝕜) x₀ (s k x₀)).proj = x₀ from rfl,
      A.trivializationAt_core x₀] at h
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨contMDiffAt_id, ?_⟩
  rw [show (TotalSpace.mk' (Fin ((exteriorPower 𝕜 B j).obj A).rank → 𝕜) x₀
    (wedgeSection j A s x₀)).proj = x₀ from rfl,
    ((exteriorPower 𝕜 B j).obj A).trivializationAt_core x₀]
  exact ((exteriorPower.contDiff_piEquiv_ιMulti 𝕜 j A.rank).comp_contMDiffAt
    (contMDiffAt_pi_module_iff.2 hc)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x ↦ localTriv_wedgeSection_snd j A s x₀ x)

/-- The determinant wedge `detSection A s` of `A.rank` `C^n` sections of `A` is a `C^n` section of
`A.det`, without completeness of `𝕜` or `IsContMDiff` hypotheses on `A`. -/
theorem contMDiff_detSection (A : FiniteRankBundleCore 𝕜 B)
    {s : Fin A.rank → ∀ x, A.core.Fiber x}
    (hs : ∀ k, ContMDiff I (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      fun x ↦ TotalSpace.mk' (Fin A.rank → 𝕜) x (s k x)) :
    ContMDiff I (I.prod 𝓘(𝕜, Fin A.det.rank → 𝕜)) n
      fun x ↦ TotalSpace.mk' (Fin A.det.rank → 𝕜) x (detSection A s x) := by
  rw [detSection_def]
  exact contMDiff_wedgeSection A.rank A hs

end TauCeti.FiniteRankBundleCore
