/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.MetricCoeff

import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Topology.MetricSpace.Annulus

/-!
# Asymptotically Euclidean ends and finite-ended structures

An *asymptotically Euclidean (AE) end* of order `t` on a Riemannian `n`-manifold `M` is a smooth
injective parametrization of an open subset of `M` by the coordinate exterior
`exteriorOpen n R = {x ∈ ℝⁿ : R < ‖x‖}` (`0 < R`), with bijective differential on that exterior,
in which the pullback metric coefficients `g_ij(x) = ⟨dφ_x e_i, dφ_x e_j⟩` are `C²` on the
exterior and decay to `δ_ij` at rate `‖x‖ ^ (-t)` together with their first two Euclidean
derivatives at rates `‖x‖ ^ (-t - 1)` and `‖x‖ ^ (-t - 2)`. Following Lee–Parker and decoupling
the analytic hypotheses of Cecchini–Zeidler, integrability of the scalar curvature on the end is
kept separate from `AsymptoticallyEuclideanEnd` so that coordinate flux computations and geometric
constructions apply without curvature integrability assumptions.

An end stores its parametrization on the open submanifold `exteriorOpen n radius`, making
`AsymptoticallyEuclideanEnd` extensional (`@[ext]`). Its coordinate metric coefficients
`AsymptoticallyEuclideanEnd.metricCoeff` extend canonically by `0` on `{x : ‖x‖ ≤ radius}` and
agree near every exterior point with `pullbackMetricCoeff φ` for any local ambient extension
`φ : ℝⁿ → M`. A *finite-ended asymptotically Euclidean structure* `FiniteEndedAE n M t` is a finite
nonempty family of pairwise disjoint AE ends whose union has compact complement in `M`.

## Main definitions

* `TauCeti.AsymptoticallyEuclideanEnd`: an AE end of `M` of order `t`, with constructors `ofFun`
  and `ofIsManifold` (requiring only `[IsManifold (𝓡 n) 1 M]`), order monotonicity `ofLE`, radius
  restriction `restrictRadius`, and coordinate radius `endRadius`.
* `TauCeti.AsymptoticallyEuclideanEnd.homeomorphImage` and `diffeomorphImage`: the homeomorphism
  (on a `C¹` manifold) and smooth diffeomorphism (on a `C^∞` manifold) onto the open image of an
  AE end.
* `TauCeti.FiniteEndedAE`: a finite nonempty family of pairwise disjoint AE ends with compact
  complement, witnessed on flat space by `FiniteEndedAE.euclideanSpace`.

## Main results

* `TauCeti.AsymptoticallyEuclideanEnd.isPathConnected_image` and `isConnected_image`: for `2 ≤ n`,
  the image of an AE end is path-connected and connected.
* `TauCeti.AsymptoticallyEuclideanEnd.isCompact_image_annulus` and `isProperMap_endRadius`:
  compactness of closed coordinate annuli in `M` and properness of the coordinate radius on a `C¹`
  manifold.
* `TauCeti.not_exists_asymptoticallyEuclideanEnd_smul`: for `1 ≤ n`, `0 < t`, and `|c| ≠ 1`, the
  rescaled parametrization `x ↦ c • x` of flat `ℝⁿ` is not an AE end of order `t`.

## References

* S. Cecchini, R. Zeidler, *The positive mass theorem and distance estimates in the spin setting*,
  Trans. Amer. Math. Soc. 377 (2024), 5271–5288 (arXiv:2108.11972v2), §2 (Definitions 2.1 and 2.3).
* J. M. Lee, T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. (N.S.) 17 (1987), 37–91,
  §§8–9.
-/

public section

noncomputable section

open Set Function Filter Metric TopologicalSpace Bundle
open scoped Topology Manifold ContDiff RealInnerProductSpace

namespace TauCeti

/-! ### Asymptotically Euclidean ends -/

/-- An *asymptotically Euclidean end* of `M` of order `t`: a smooth injective parametrization
`param : exteriorOpen n radius → M` of an open subset of `M` by `{x ∈ ℝⁿ : radius < ‖x‖}`
(`0 < radius`), with bijective differential everywhere on that exterior, whose metric coefficients
`g_ij` are `C²` on the exterior and decay to `δ_ij` at rate `‖x‖ ^ (-t)` along with their first and
second Euclidean derivatives at rates `‖x‖ ^ (-t - 1)` and `‖x‖ ^ (-t - 2)` (Cecchini–Zeidler,
Definition 2.1, without the scalar-curvature integrability clause). -/
@[ext]
structure AsymptoticallyEuclideanEnd (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] (t : ℝ) where
  /-- The radius of the excised coordinate ball. -/
  radius : ℝ
  /-- The excision radius is strictly positive. -/
  radius_pos : 0 < radius
  /-- The end parametrization defined on the open exterior `{x ∈ ℝⁿ : radius < ‖x‖}`. -/
  param : exteriorOpen n radius → M
  /-- Smoothness of the parametrization on the exterior. -/
  contMDiff : ContMDiff (𝓡 n) (𝓡 n) ∞ param
  /-- Injectivity of the parametrization on the exterior. -/
  injective : Injective param
  /-- Openness of the end image in `M`. -/
  isOpen_range : IsOpen (range param)
  /-- Bijectivity of the differential at every point of the exterior. -/
  mfderiv_bijective : ∀ x : exteriorOpen n radius, Bijective (mfderiv (𝓡 n) (𝓡 n) param x)
  /-- `C²` regularity of the coordinate metric coefficients on the exterior. -/
  contDiffOn_exteriorMetricCoeff : ∀ i j : Fin n,
    ContDiffOn ℝ 2 (fun y => exteriorMetricCoeff param y i j) (exteriorOpen n radius)
  /-- Asymptotic Euclidean decay up to second derivatives of the metric coefficients. -/
  decay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), radius < ‖x‖ → ∀ i j : Fin n,
    |exteriorMetricCoeff param x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
    ‖fderiv ℝ (fun y => exteriorMetricCoeff param y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1) ∧
    ‖fderiv ℝ (fderiv ℝ (fun y => exteriorMetricCoeff param y i j)) x‖ ≤ C * ‖x‖ ^ (-t - 2)

namespace AsymptoticallyEuclideanEnd

section Basic

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] {t : ℝ}
  (E : AsymptoticallyEuclideanEnd n M t)

/-- Pointwise extensionality for `AsymptoticallyEuclideanEnd` in terms of ambient points `x ∈ ℝⁿ`
with `radius < ‖x‖`. -/
theorem ext_iff_forall {E₁ E₂ : AsymptoticallyEuclideanEnd n M t} :
    E₁ = E₂ ↔ ∃ hR : E₁.radius = E₂.radius,
      ∀ (x : EuclideanSpace ℝ (Fin n)) (hx : E₁.radius < ‖x‖),
        E₁.param ⟨x, mem_exteriorOpen.mpr hx⟩ =
          E₂.param ⟨x, mem_exteriorOpen.mpr (hR ▸ hx)⟩ := by
  refine ⟨by rintro rfl; exact ⟨rfl, fun _ _ => rfl⟩, fun ⟨hR, hφ⟩ => ?_⟩
  rcases E₁ with ⟨R₁, hR₁, φ₁, _, _, _, _, _, _⟩
  rcases E₂ with ⟨R₂, hR₂, φ₂, _, _, _, _, _, _⟩
  dsimp only at hR hφ; subst hR
  suffices φ₁ = φ₂ by subst this; rfl
  exact funext fun ⟨x, hx⟩ => hφ x (mem_exteriorOpen.mp hx)

/-- The coordinate metric coefficients `g_ij : ℝⁿ → ℝ` of an end `E`, equal to
`⟨d(E.param)_x e_i, d(E.param)_x e_j⟩` for `E.radius < ‖x‖` and `0` otherwise. -/
def metricCoeff (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) : ℝ :=
  exteriorMetricCoeff E.param x i j

theorem metricCoeff_def (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    E.metricCoeff x i j = exteriorMetricCoeff E.param x i j := (rfl)

theorem metricCoeff_of_lt {x : EuclideanSpace ℝ (Fin n)} (hx : E.radius < ‖x‖)
    (i j : Fin n) :
    E.metricCoeff x i j =
      ⟪mfderiv (𝓡 n) (𝓡 n) E.param ⟨x, mem_exteriorOpen.mpr hx⟩
          (EuclideanSpace.basisFun (Fin n) ℝ i),
        mfderiv (𝓡 n) (𝓡 n) E.param ⟨x, mem_exteriorOpen.mpr hx⟩
          (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ :=
  exteriorMetricCoeff_of_lt E.param hx i j

@[simp] theorem metricCoeff_of_le {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ E.radius)
    (i j : Fin n) :
    E.metricCoeff x i j = 0 :=
  exteriorMetricCoeff_of_le E.param hx i j

/-- Symmetry of the metric coefficients of an end. -/
theorem metricCoeff_symm (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    E.metricCoeff x i j = E.metricCoeff x j i :=
  exteriorMetricCoeff_symm E.param x i j

/-- Every diagonal metric coefficient of an end is strictly positive on `{x : E.radius < ‖x‖}`. -/
theorem metricCoeff_diag_pos {x : EuclideanSpace ℝ (Fin n)} (hx : E.radius < ‖x‖) (i : Fin n) :
    0 < E.metricCoeff x i i :=
  exteriorMetricCoeff_diag_pos hx (E.mfderiv_bijective ⟨x, mem_exteriorOpen.mpr hx⟩).1 i

/-- On `{x : E.radius < ‖x‖}`, the metric coefficients `E.metricCoeff · i j` are `C²`. -/
theorem contDiffOn_metricCoeff (i j : Fin n) :
    ContDiffOn ℝ 2 (fun y => E.metricCoeff y i j) (exteriorOpen n E.radius) :=
  E.contDiffOn_exteriorMetricCoeff i j

/-- Asymptotic Euclidean `C²` decay of the coordinate metric coefficients `E.metricCoeff` on
`{x : E.radius < ‖x‖}`. -/
theorem decay_metricCoeff :
    ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), E.radius < ‖x‖ → ∀ i j : Fin n,
      |E.metricCoeff x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
      ‖fderiv ℝ (fun y => E.metricCoeff y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1) ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => E.metricCoeff y i j)) x‖ ≤ C * ‖x‖ ^ (-t - 2) :=
  E.decay

/-- At every point of `{x : E.radius < ‖x‖}`, the metric coefficients `E.metricCoeff · i j` are
`C²`. -/
theorem contDiffAt_metricCoeff {x : EuclideanSpace ℝ (Fin n)} (hx : E.radius < ‖x‖)
    (i j : Fin n) : ContDiffAt ℝ 2 (fun y => E.metricCoeff y i j) x :=
  (E.contDiffOn_metricCoeff i j).contDiffAt
    ((exteriorOpen n E.radius).isOpen.mem_nhds (mem_exteriorOpen.mpr hx))

/-- If an ambient map `φ : ℝⁿ → M` agrees with `E.param` on a neighbourhood of `⟨x, ...⟩`, then
`E.metricCoeff` agrees with `pullbackMetricCoeff φ` on a neighbourhood of `x`. -/
theorem eventuallyEq_metricCoeff_pullbackMetricCoeff {φ : EuclideanSpace ℝ (Fin n) → M}
    {x : EuclideanSpace ℝ (Fin n)} (hx : E.radius < ‖x‖)
    (hφ : E.param =ᶠ[𝓝 (⟨x, mem_exteriorOpen.mpr hx⟩ : exteriorOpen n E.radius)]
      φ ∘ Subtype.val)
    (i j : Fin n) :
    (fun y => E.metricCoeff y i j) =ᶠ[𝓝 x] (fun y => pullbackMetricCoeff φ y i j) :=
  (eventuallyEq_exteriorMetricCoeff hx hφ i j).trans
    (eventuallyEq_exteriorMetricCoeff_comp_subtypeVal φ hx i j)

/-- Pointwise agreement of `E.metricCoeff` and `pullbackMetricCoeff φ` at an exterior point `x`
where `E.param` agrees locally with `φ ∘ Subtype.val`. -/
theorem metricCoeff_eq_pullbackMetricCoeff {φ : EuclideanSpace ℝ (Fin n) → M}
    {x : EuclideanSpace ℝ (Fin n)} (hx : E.radius < ‖x‖)
    (hφ : E.param =ᶠ[𝓝 (⟨x, mem_exteriorOpen.mpr hx⟩ : exteriorOpen n E.radius)]
      φ ∘ Subtype.val)
    (i j : Fin n) :
    E.metricCoeff x i j = pullbackMetricCoeff φ x i j :=
  (E.eventuallyEq_metricCoeff_pullbackMetricCoeff hx hφ i j).self_of_nhds

/-- The image of the end in `M`. -/
def image : Set M := range E.param

theorem image_def : E.image = range E.param := (rfl)

/-- Every value `E.param x` belongs to `E.image`. -/
@[simp] theorem param_mem_image (x : exteriorOpen n E.radius) : E.param x ∈ E.image := ⟨x, rfl⟩

/-- Membership in `E.image` means being of the form `E.param ⟨x, ...⟩` for some `x` with
`E.radius < ‖x‖`. -/
theorem mem_image_iff {p : M} :
    p ∈ E.image ↔ ∃ (x : EuclideanSpace ℝ (Fin n)) (hx : E.radius < ‖x‖),
      E.param ⟨x, mem_exteriorOpen.mpr hx⟩ = p := by
  rw [image_def, mem_range]
  exact ⟨fun ⟨⟨x, hx⟩, hp⟩ => ⟨x, mem_exteriorOpen.mp hx, hp⟩,
    fun ⟨x, hx, hp⟩ => ⟨⟨x, mem_exteriorOpen.mpr hx⟩, hp⟩⟩

/-- The image of an AE end is open in `M`. -/
theorem isOpen_image : IsOpen E.image := E.isOpen_range

/-- The image of an AE end packaged as an element of `TopologicalSpace.Opens M`. -/
def openImage : Opens M := ⟨E.image, E.isOpen_image⟩

@[simp] theorem coe_openImage : (E.openImage : Set M) = E.image := (rfl)

@[simp] theorem mem_openImage_iff {p : M} : p ∈ E.openImage ↔ p ∈ E.image := Iff.rfl

theorem mem_openImage_param (x : exteriorOpen n E.radius) : E.param x ∈ E.openImage :=
  E.param_mem_image x

/-- In positive dimension, the image of an AE end is nonempty. -/
theorem image_nonempty (hn : 1 ≤ n) : E.image.Nonempty := by
  obtain ⟨x, hx⟩ := exteriorOpen_nonempty hn E.radius
  exact ⟨E.param ⟨x, hx⟩, E.param_mem_image ⟨x, hx⟩⟩

/-- In dimension at least `2`, the image of an AE end is path-connected. -/
theorem isPathConnected_image (hn : 2 ≤ n) : IsPathConnected E.image := by
  have : PathConnectedSpace (exteriorOpen n E.radius) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_exteriorOpen hn E.radius)
  exact isPathConnected_range E.contMDiff.continuous

/-- In dimension at least `2`, the image of an AE end is connected. -/
theorem isConnected_image (hn : 2 ≤ n) : IsConnected E.image :=
  (E.isPathConnected_image hn).isConnected

/-- The coordinate radius `‖φ⁻¹(·)‖ : E.openImage → Set.Ioi E.radius` on the open image of an AE
end. -/
def endRadius (y : E.openImage) : Ioi E.radius :=
  ⟨‖((Equiv.ofInjective E.param E.injective).symm
      ⟨y.1, E.image_def ▸ E.mem_openImage_iff.mp y.2⟩ : EuclideanSpace ℝ (Fin n))‖,
    mem_exteriorOpen.mp
      ((Equiv.ofInjective E.param E.injective).symm
        ⟨y.1, E.image_def ▸ E.mem_openImage_iff.mp y.2⟩).2⟩

/-- The real value of `E.endRadius y` is the Euclidean norm of the preimage of `y` under
`E.param`. -/
theorem coe_endRadius (y : E.openImage) :
    (E.endRadius y : ℝ) =
      ‖((Equiv.ofInjective E.param E.injective).symm
        ⟨y.1, E.image_def ▸ E.mem_openImage_iff.mp y.2⟩ : EuclideanSpace ℝ (Fin n))‖ := (rfl)

/-- Evaluating `E.endRadius` on `E.param x` recovers `‖x‖`. -/
@[simp] theorem coe_endRadius_param (x : exteriorOpen n E.radius) :
    (E.endRadius ⟨E.param x, E.mem_openImage_param x⟩ : ℝ) =
      ‖(x : EuclideanSpace ℝ (Fin n))‖ := by
  change ‖((Equiv.ofInjective E.param E.injective).symm
    (Equiv.ofInjective E.param E.injective x) : EuclideanSpace ℝ (Fin n))‖ = _
  rw [Equiv.symm_apply_apply]

/-- Every closed coordinate annulus `{E.param x : r₁ ≤ ‖x‖ ≤ r₂}` with `E.radius < r₁` is compact
in `M`. -/
theorem isCompact_image_annulus {r₁ r₂ : ℝ} (hr₁ : E.radius < r₁) :
    IsCompact (E.param '' {x : exteriorOpen n E.radius |
      r₁ ≤ ‖(x : EuclideanSpace ℝ (Fin n))‖ ∧ ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ r₂}) := by
  have hK : IsCompact {z : EuclideanSpace ℝ (Fin n) | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂} := by
    simpa only [sub_zero] using isCompact_setOf_le_norm_sub_le (0 : EuclideanSpace ℝ (Fin n)) r₁ r₂
  refine (Topology.IsInducing.subtypeVal.isCompact_preimage' hK ?_).image E.contMDiff.continuous
  rintro z ⟨hz₁, _⟩
  exact ⟨⟨z, mem_exteriorOpen.mpr (hr₁.trans_le hz₁)⟩, rfl⟩

/-- **Smart constructor from an ambient map.** Any map `φ : ℝⁿ → M` that is smooth, injective, open
onto its image, and has injective differential on `{x : R < ‖x‖}`, such that
`pullbackMetricCoeff φ` is `C²` there and satisfies the `C²` decay bounds, defines an
`AsymptoticallyEuclideanEnd`. -/
def ofFun {R : ℝ} (hR : 0 < R) (φ : EuclideanSpace ℝ (Fin n) → M)
    (hφ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ φ {x | R < ‖x‖})
    (hinj : InjOn φ {x | R < ‖x‖})
    (hopen : IsOpen (φ '' {x | R < ‖x‖}))
    (hmf : ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ → Injective (mfderiv (𝓡 n) (𝓡 n) φ x))
    (hreg : ∀ i j : Fin n, ContDiffOn ℝ 2 (fun y => pullbackMetricCoeff φ y i j) {x | R < ‖x‖})
    (hdecay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ → ∀ i j : Fin n,
      |pullbackMetricCoeff φ x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
      ‖fderiv ℝ (fun y => pullbackMetricCoeff φ y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1) ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => pullbackMetricCoeff φ y i j)) x‖ ≤ C * ‖x‖ ^ (-t - 2)) :
    AsymptoticallyEuclideanEnd n M t where
  radius := R
  radius_pos := hR
  param := φ ∘ Subtype.val
  contMDiff := hφ.comp_contMDiff contMDiff_subtype_val fun x => mem_exteriorOpen.mp x.2
  injective x₁ x₂ h := Subtype.ext (hinj (mem_exteriorOpen.mp x₁.2) (mem_exteriorOpen.mp x₂.2) h)
  isOpen_range := by
    rw [range_comp, Subtype.range_coe_subtype]
    simpa only [mem_exteriorOpen] using hopen
  mfderiv_bijective x := by
    have hφx : MDifferentiableAt (𝓡 n) (𝓡 n) φ x.1 :=
      (hφ.contMDiffAt (coe_exteriorOpen n R ▸ (exteriorOpen n R).isOpen.mem_nhds
        x.2)).mdifferentiableAt (by simp)
    have hcomp : mfderiv (𝓡 n) (𝓡 n) (φ ∘ (Subtype.val : exteriorOpen n R → _)) x =
        (mfderiv (𝓡 n) (𝓡 n) φ x.1).comp
          (TauCeti.Manifold.tangentSpaceOpenEquiv x).toContinuousLinearMap := by
      rw [mfderiv_comp x hφx (contMDiff_subtype_val.mdifferentiableAt one_ne_zero),
        TauCeti.Manifold.mfderiv_subtype_val]
    have hinj_x : Injective (mfderiv (𝓡 n) (𝓡 n) φ x.1) := hmf x.1 (mem_exteriorOpen.mp x.2)
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x.1) =
        Module.finrank ℝ (TangentSpace (𝓡 n) (φ x.1)) := by
      simp [TauCeti.finrank_tangentSpace]
    have hbij_x : Bijective (mfderiv (𝓡 n) (𝓡 n) φ x.1) :=
      ⟨hinj_x, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj_x⟩
    rw [hcomp]
    exact hbij_x.comp (TauCeti.Manifold.tangentSpaceOpenEquiv x).bijective
  contDiffOn_exteriorMetricCoeff i j := by
    rw [coe_exteriorOpen]
    exact (hreg i j).congr fun y hy => exteriorMetricCoeff_comp_subtypeVal_of_lt φ hy i j
  decay := by
    obtain ⟨C, hC⟩ := hdecay
    refine ⟨C, fun x hx i j => ?_⟩
    have hev := eventuallyEq_exteriorMetricCoeff_comp_subtypeVal φ hx i j
    rw [exteriorMetricCoeff_comp_subtypeVal_of_lt φ hx i j, hev.fderiv_eq,
      (hev.fderiv (𝕜 := ℝ)).fderiv_eq]
    exact hC x hx i j

@[simp] theorem ofFun_radius {R : ℝ} (hR : 0 < R) (φ : EuclideanSpace ℝ (Fin n) → M)
    (hφ) (hinj) (hopen) (hmf) (hreg) (hdecay) :
    (ofFun (t := t) hR φ hφ hinj hopen hmf hreg hdecay).radius = R := (rfl)

@[simp] theorem ofFun_param_apply {R : ℝ} (hR : 0 < R) (φ : EuclideanSpace ℝ (Fin n) → M)
    (hφ) (hinj) (hopen) (hmf) (hreg) (hdecay)
    (x : exteriorOpen n (ofFun (t := t) hR φ hφ hinj hopen hmf hreg hdecay).radius) :
    (ofFun (t := t) hR φ hφ hinj hopen hmf hreg hdecay).param x = φ x.1 := (rfl)

@[simp] theorem ofFun_image {R : ℝ} (hR : 0 < R) (φ : EuclideanSpace ℝ (Fin n) → M)
    (hφ) (hinj) (hopen) (hmf) (hreg) (hdecay) :
    (ofFun (t := t) hR φ hφ hinj hopen hmf hreg hdecay).image = φ '' {x | R < ‖x‖} := by
  rw [ofFun, image_def, range_comp, Subtype.range_coe_subtype]
  simp only [mem_exteriorOpen]

@[simp] theorem ofFun_metricCoeff_of_lt {R : ℝ} (hR : 0 < R) (φ : EuclideanSpace ℝ (Fin n) → M)
    (hφ) (hinj) (hopen) (hmf) (hreg) (hdecay) {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖)
    (i j : Fin n) :
    (ofFun (t := t) hR φ hφ hinj hopen hmf hreg hdecay).metricCoeff x i j =
      pullbackMetricCoeff φ x i j :=
  exteriorMetricCoeff_comp_subtypeVal_of_lt φ hx i j

/-- **Monotonicity in the decay order.** Every AE end of order `t₂` is also an AE end of any lower
order `t₁ ≤ t₂`, with the same excision radius and parametrization. -/
def ofLE {t₁ t₂ : ℝ} (E : AsymptoticallyEuclideanEnd n M t₂) (ht : t₁ ≤ t₂) :
    AsymptoticallyEuclideanEnd n M t₁ where
  radius := E.radius
  radius_pos := E.radius_pos
  param := E.param
  contMDiff := E.contMDiff
  injective := E.injective
  isOpen_range := E.isOpen_range
  mfderiv_bijective := E.mfderiv_bijective
  contDiffOn_exteriorMetricCoeff := E.contDiffOn_exteriorMetricCoeff
  decay := by
    obtain ⟨C, hC⟩ := E.decay
    refine ⟨max C 0 * E.radius ^ (t₁ - t₂), fun x hx i j => ?_⟩
    have hx_pos : 0 < ‖x‖ := E.radius_pos.trans hx
    have hscale (k : ℝ) : C * ‖x‖ ^ (-t₂ - k) ≤
        (max C 0 * E.radius ^ (t₁ - t₂)) * ‖x‖ ^ (-t₁ - k) := by
      have hrpow : ‖x‖ ^ (t₁ - t₂) ≤ E.radius ^ (t₁ - t₂) :=
        Real.rpow_le_rpow_of_nonpos E.radius_pos hx.le (by linarith)
      have hsplit : ‖x‖ ^ (-t₂ - k) = ‖x‖ ^ (t₁ - t₂) * ‖x‖ ^ (-t₁ - k) := by
        rw [← Real.rpow_add hx_pos]; congr 1; ring
      calc
        C * ‖x‖ ^ (-t₂ - k) ≤ max C 0 * ‖x‖ ^ (-t₂ - k) :=
          mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg hx_pos.le _)
        _ = max C 0 * (‖x‖ ^ (t₁ - t₂) * ‖x‖ ^ (-t₁ - k)) := by rw [hsplit]
        _ ≤ max C 0 * (E.radius ^ (t₁ - t₂) * ‖x‖ ^ (-t₁ - k)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hrpow (Real.rpow_nonneg hx_pos.le _)) (le_max_right C 0)
        _ = (max C 0 * E.radius ^ (t₁ - t₂)) * ‖x‖ ^ (-t₁ - k) := (mul_assoc _ _ _).symm
    obtain ⟨h₀, h₁, h₂⟩ := hC x hx i j
    exact ⟨h₀.trans (by simpa only [sub_zero] using hscale 0),
      h₁.trans (hscale 1), h₂.trans (hscale 2)⟩

@[simp] theorem ofLE_radius {t₁ t₂ : ℝ} (E : AsymptoticallyEuclideanEnd n M t₂) (ht : t₁ ≤ t₂) :
    (E.ofLE ht).radius = E.radius := (rfl)

@[simp] theorem ofLE_param_apply {t₁ t₂ : ℝ} (E : AsymptoticallyEuclideanEnd n M t₂)
    (ht : t₁ ≤ t₂) (x : exteriorOpen n (E.ofLE ht).radius) :
    (E.ofLE ht).param x =
      E.param ⟨x.1, mem_exteriorOpen.mpr (by simpa [ofLE_radius] using mem_exteriorOpen.mp x.2)⟩ :=
  (rfl)

@[simp] theorem ofLE_image {t₁ t₂ : ℝ} (E : AsymptoticallyEuclideanEnd n M t₂) (ht : t₁ ≤ t₂) :
    (E.ofLE ht).image = E.image := (rfl)

@[simp] theorem ofLE_metricCoeff {t₁ t₂ : ℝ} (E : AsymptoticallyEuclideanEnd n M t₂)
    (ht : t₁ ≤ t₂) : (E.ofLE ht).metricCoeff = E.metricCoeff := (rfl)

end Basic

/-! ### Local diffeomorphism, radius restriction, and properness on `C¹` manifolds -/

section C1Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] {t : ℝ}

/-- **Smart constructor on a `C¹` manifold.** On a `C¹` `n`-manifold `M`, a smooth injective map
`φ : exteriorOpen n R → M` with injective differential everywhere on the exterior and `C²` metric
coefficients with asymptotic Euclidean decay defines an `AsymptoticallyEuclideanEnd`. -/
def ofIsManifold {R : ℝ} (hR : 0 < R) (φ : exteriorOpen n R → M)
    (hφ : ContMDiff (𝓡 n) (𝓡 n) ∞ φ) (hinj : Injective φ)
    (hmf : ∀ x : exteriorOpen n R, Injective (mfderiv (𝓡 n) (𝓡 n) φ x))
    (hreg : ∀ i j : Fin n,
      ContDiffOn ℝ 2 (fun y => exteriorMetricCoeff φ y i j) (exteriorOpen n R))
    (hdecay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ → ∀ i j : Fin n,
      |exteriorMetricCoeff φ x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
      ‖fderiv ℝ (fun y => exteriorMetricCoeff φ y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1) ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => exteriorMetricCoeff φ y i j)) x‖ ≤ C * ‖x‖ ^ (-t - 2)) :
    AsymptoticallyEuclideanEnd n M t :=
  let hloc : IsLocalDiffeomorph (𝓡 n) (𝓡 n) 1 φ :=
    isLocalDiffeomorph_of_injective_mfderiv (hφ.of_le (by simp)) le_rfl hmf rfl
  { radius := R
    radius_pos := hR
    param := φ
    contMDiff := hφ
    injective := hinj
    isOpen_range := hloc.isOpen_range
    mfderiv_bijective := fun x => (hloc.isInvertible_mfderiv one_ne_zero x).bijective
    contDiffOn_exteriorMetricCoeff := hreg
    decay := hdecay }

@[simp] theorem ofIsManifold_radius {R : ℝ} (hR : 0 < R) (φ : exteriorOpen n R → M)
    (hφ) (hinj) (hmf) (hreg) (hdecay) :
    (ofIsManifold (t := t) hR φ hφ hinj hmf hreg hdecay).radius = R := (rfl)

@[simp] theorem ofIsManifold_param_apply {R : ℝ} (hR : 0 < R) (φ : exteriorOpen n R → M)
    (hφ) (hinj) (hmf) (hreg) (hdecay)
    (x : exteriorOpen n (ofIsManifold (t := t) hR φ hφ hinj hmf hreg hdecay).radius) :
    (ofIsManifold (t := t) hR φ hφ hinj hmf hreg hdecay).param x = φ ⟨x.1,
      mem_exteriorOpen.mpr (by simpa [ofIsManifold_radius] using mem_exteriorOpen.mp x.2)⟩ := (rfl)

@[simp] theorem ofIsManifold_image {R : ℝ} (hR : 0 < R) (φ : exteriorOpen n R → M)
    (hφ) (hinj) (hmf) (hreg) (hdecay) :
    (ofIsManifold (t := t) hR φ hφ hinj hmf hreg hdecay).image = range φ := (rfl)

@[simp] theorem ofIsManifold_metricCoeff {R : ℝ} (hR : 0 < R) (φ : exteriorOpen n R → M)
    (hφ) (hinj) (hmf) (hreg) (hdecay) :
    (ofIsManifold (t := t) hR φ hφ hinj hmf hreg hdecay).metricCoeff = exteriorMetricCoeff φ :=
  (rfl)

variable (E : AsymptoticallyEuclideanEnd n M t)

/-- On a `C¹` manifold `M`, the parametrization of an AE end is a `C¹` local diffeomorphism. -/
theorem isLocalDiffeomorph_one : IsLocalDiffeomorph (𝓡 n) (𝓡 n) 1 E.param :=
  isLocalDiffeomorph_of_injective_mfderiv (E.contMDiff.of_le (by simp)) le_rfl
    (fun x => (E.mfderiv_bijective x).1) rfl

/-- On a `C¹` manifold `M`, an AE end parametrizes its open image by a homeomorphism
`exteriorOpen n E.radius ≃ₜ E.openImage`. -/
def homeomorphImage : exteriorOpen n E.radius ≃ₜ E.openImage :=
  (Equiv.ofInjective E.param E.injective).toHomeomorphOfIsInducing <|
    Topology.IsInducing.subtypeVal.of_comp_iff.mp
      (E.isLocalDiffeomorph_one.isLocalHomeomorph.isOpenEmbedding_of_injective
        E.injective).toIsInducing

@[simp] theorem coe_homeomorphImage_apply (x : exteriorOpen n E.radius) :
    (E.homeomorphImage x : M) = E.param x := (rfl)

@[simp] theorem homeomorphImage_symm_param (x : exteriorOpen n E.radius) :
    E.homeomorphImage.symm ⟨E.param x, E.mem_openImage_param x⟩ = x :=
  (Equiv.ofInjective E.param E.injective).symm_apply_apply x

@[simp] theorem param_homeomorphImage_symm (y : E.openImage) :
    E.param (E.homeomorphImage.symm y) = (y : M) :=
  congrArg Subtype.val ((Equiv.ofInjective E.param E.injective).apply_symm_apply y)

/-- **Shrinking an AE end to a larger excision radius.** Restricting an AE end `E` on a `C¹`
manifold `M` from `E.radius` to any `R' ≥ E.radius` gives an AE end of the same order `t`. -/
def restrictRadius {R' : ℝ} (hR' : E.radius ≤ R') : AsymptoticallyEuclideanEnd n M t :=
  ofIsManifold (E.radius_pos.trans_le hR')
    (E.param ∘ Opens.inclusion (exteriorOpen_anti hR'))
    (E.contMDiff.comp (contMDiff_inclusion (exteriorOpen_anti hR')))
    (E.injective.comp (Set.inclusion_injective (exteriorOpen_anti hR')))
    (fun x => by
      have hinc : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) 1
          (Opens.inclusion (exteriorOpen_anti hR')) x :=
        IsLocalDiffeomorphAt.of_comp_left (K := 𝓡 n)
          (f := (Subtype.val : exteriorOpen n E.radius → EuclideanSpace ℝ (Fin n)))
          (e := Opens.inclusion (exteriorOpen_anti hR'))
          (TauCeti.isLocalDiffeomorph_subtype_val x)
          (TauCeti.isLocalDiffeomorph_subtype_val _)
          (continuous_subtype_val.subtype_mk _).continuousAt
      exact ((hinc.comp (hg := E.isLocalDiffeomorph_one _)).isInvertible_mfderiv
        one_ne_zero).injective)
    (fun i j =>
      (E.contDiffOn_metricCoeff i j).congr_mono
        (fun y hy => exteriorMetricCoeff_comp_inclusion_of_lt hR' E.param
          (mem_exteriorOpen.mp hy) i j)
        (exteriorOpen_anti hR'))
    (by
      obtain ⟨C, hC⟩ := E.decay_metricCoeff
      refine ⟨C, fun x hx i j => ?_⟩
      have hev : (fun y =>
          exteriorMetricCoeff (E.param ∘ Opens.inclusion (exteriorOpen_anti hR')) y i j) =ᶠ[𝓝 x]
          (fun y => E.metricCoeff y i j) := by
        filter_upwards [(exteriorOpen n R').isOpen.mem_nhds (mem_exteriorOpen.mpr hx)] with y hy
        exact exteriorMetricCoeff_comp_inclusion_of_lt hR' E.param (mem_exteriorOpen.mp hy) i j
      rw [exteriorMetricCoeff_comp_inclusion_of_lt hR' E.param hx i j, ← E.metricCoeff_def,
        hev.fderiv_eq, (hev.fderiv (𝕜 := ℝ)).fderiv_eq]
      exact hC x (hR'.trans_lt hx) i j)

@[simp] theorem restrictRadius_radius {R' : ℝ} (hR' : E.radius ≤ R') :
    (E.restrictRadius hR').radius = R' := (rfl)

@[simp] theorem restrictRadius_param_apply {R' : ℝ} (hR' : E.radius ≤ R')
    (x : exteriorOpen n (E.restrictRadius hR').radius) :
    (E.restrictRadius hR').param x = E.param ⟨x.1, mem_exteriorOpen.mpr
      (hR'.trans_lt (by simpa [restrictRadius_radius] using mem_exteriorOpen.mp x.2))⟩ := (rfl)

@[simp] theorem restrictRadius_image {R' : ℝ} (hR' : E.radius ≤ R') :
    (E.restrictRadius hR').image =
      E.param '' {x : exteriorOpen n E.radius | R' < ‖(x : EuclideanSpace ℝ (Fin n))‖} := by
  rw [restrictRadius, ofIsManifold_image, range_comp]
  congr 1
  ext ⟨x, hx⟩
  simp [Opens.inclusion, Set.inclusion]

/-- Restricting an AE end to a larger excision radius `R' ≥ E.radius` shrinks its image in `M`. -/
theorem restrictRadius_image_subset {R' : ℝ} (hR' : E.radius ≤ R') :
    (E.restrictRadius hR').image ⊆ E.image := by
  rw [restrictRadius_image, image_def]
  exact image_subset_range _ _

@[simp] theorem restrictRadius_metricCoeff_of_lt {R' : ℝ} (hR' : E.radius ≤ R')
    {x : EuclideanSpace ℝ (Fin n)} (hx : R' < ‖x‖) (i j : Fin n) :
    (E.restrictRadius hR').metricCoeff x i j = E.metricCoeff x i j :=
  exteriorMetricCoeff_comp_inclusion_of_lt hR' E.param hx i j

/-- **Properness of the end radius.** On a `C¹` manifold `M`, the coordinate radius
`E.endRadius : E.openImage → Set.Ioi E.radius` is a proper map. -/
theorem isProperMap_endRadius : IsProperMap E.endRadius := by
  have heq : E.endRadius =
      (fun x : exteriorOpen n E.radius =>
        (⟨‖(x : EuclideanSpace ℝ (Fin n))‖, mem_exteriorOpen.mp x.2⟩ : Ioi E.radius)) ∘
        E.homeomorphImage.symm :=
    rfl
  rw [heq]
  exact isProperMap_exteriorOpen_norm.comp E.homeomorphImage.symm.isProperMap

end C1Manifold

/-! ### Smooth diffeomorphism onto the open image -/

section SmoothManifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] {t : ℝ}
  (E : AsymptoticallyEuclideanEnd n M t)

/-- On a smooth manifold `M`, the parametrization of an AE end is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ E.param :=
  isLocalDiffeomorph_of_injective_mfderiv E.contMDiff (by simp)
    (fun x => (E.mfderiv_bijective x).1) rfl

/-- On a smooth manifold `M`, an AE end parametrizes its open image by a smooth diffeomorphism
`exteriorOpen n E.radius ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ E.openImage`. -/
def diffeomorphImage : exteriorOpen n E.radius ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ E.openImage where
  toEquiv := E.homeomorphImage.toEquiv
  contMDiff_toFun := (TauCeti.ContMDiff.subtypeVal_comp_iff E.openImage _).mp E.contMDiff
  contMDiff_invFun :=
    ContMDiff.of_comp_isLocalDiffeomorph E.isLocalDiffeomorph
      E.homeomorphImage.symm.continuous <| by
        have hcomp :
            E.param ∘ E.homeomorphImage.toEquiv.symm = (Subtype.val : E.openImage → M) :=
          funext E.param_homeomorphImage_symm
        rw [hcomp]
        exact contMDiff_subtype_val

@[simp] theorem coe_diffeomorphImage_apply (x : exteriorOpen n E.radius) :
    (E.diffeomorphImage x : M) = E.param x := (rfl)

@[simp] theorem diffeomorphImage_symm_param (x : exteriorOpen n E.radius) :
    E.diffeomorphImage.symm ⟨E.param x, E.mem_openImage_param x⟩ = x :=
  E.homeomorphImage_symm_param x

@[simp] theorem param_diffeomorphImage_symm (y : E.openImage) :
    E.param (E.diffeomorphImage.symm y) = (y : M) :=
  E.param_homeomorphImage_symm y

/-- The real-valued coordinate radius `y ↦ (E.endRadius y : ℝ)` is smooth on `E.openImage`. -/
theorem contMDiff_coe_endRadius :
    ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (fun y : E.openImage => (E.endRadius y : ℝ)) := by
  have heq : (fun y : E.openImage => (E.endRadius y : ℝ)) =
      norm ∘ fun z : E.openImage => (E.diffeomorphImage.symm z : EuclideanSpace ℝ (Fin n)) :=
    rfl
  rw [heq]
  intro y
  have hne : (E.diffeomorphImage.symm y : EuclideanSpace ℝ (Fin n)) ≠ 0 :=
    exteriorOpen_coe_ne_zero E.radius_pos.le _
  exact ((contDiffAt_norm ℝ hne).contMDiffAt).comp y
    (contMDiff_subtype_val.comp E.diffeomorphImage.symm.contMDiff).contMDiffAt

end SmoothManifold

end AsymptoticallyEuclideanEnd

/-! ### Finite-ended asymptotically Euclidean structures -/

/-- A *finite-ended asymptotically Euclidean structure* of order `t` on `M`: a finite nonempty
family of AE ends of order `t` with pairwise disjoint images whose union has compact complement in
`M` (Cecchini–Zeidler, Definition 2.3, without boundary). -/
@[ext]
structure FiniteEndedAE (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] (t : ℝ) where
  /-- The number of ends. -/
  numEnds : ℕ
  /-- Nonemptiness of the family of ends, ruling out closed manifolds. -/
  numEnds_pos : 0 < numEnds
  /-- The indexed family of AE ends. -/
  ends : Fin numEnds → AsymptoticallyEuclideanEnd n M t
  /-- Distinct ends have disjoint images in `M`. -/
  pairwise_disjoint : Pairwise fun a b => Disjoint (ends a).image (ends b).image
  /-- The complement of the union of the end images is compact in `M`. -/
  isCompact_compl : IsCompact (⋃ a, (ends a).image)ᶜ

namespace FiniteEndedAE

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] {t : ℝ}
  (A : FiniteEndedAE n M t)

/-- Extensionality for `FiniteEndedAE` across equal end counts. -/
theorem ext_iff_forall {A₁ A₂ : FiniteEndedAE n M t} :
    A₁ = A₂ ↔ ∃ h : A₁.numEnds = A₂.numEnds,
      ∀ a : Fin A₁.numEnds, A₁.ends a = A₂.ends (a.cast h) := by
  refine ⟨by rintro rfl; exact ⟨rfl, fun _ => rfl⟩, fun ⟨h, hends⟩ => ?_⟩
  rcases A₁ with ⟨m₁, hm₁, e₁, _, _⟩; rcases A₂ with ⟨m₂, hm₂, e₂, _, _⟩
  dsimp only at h hends; subst h
  suffices e₁ = e₂ by subst this; rfl
  exact funext hends

instance : Nonempty (Fin A.numEnds) := ⟨⟨0, A.numEnds_pos⟩⟩

/-- The union of the images of all ends in `A`. -/
def endsUnion : Set M := ⋃ a, (A.ends a).image

theorem endsUnion_def : A.endsUnion = ⋃ a, (A.ends a).image := (rfl)

@[simp] theorem mem_endsUnion_iff {p : M} : p ∈ A.endsUnion ↔ ∃ a, p ∈ (A.ends a).image :=
  mem_iUnion

/-- The union of all end images is open in `M`. -/
theorem isOpen_endsUnion : IsOpen A.endsUnion := isOpen_iUnion fun a => (A.ends a).isOpen_image

/-- The compact core of `M` outside the union of the ends. -/
def compactCore : Set M := A.endsUnionᶜ

theorem compactCore_def : A.compactCore = A.endsUnionᶜ := (rfl)

@[simp] theorem mem_compactCore_iff {p : M} : p ∈ A.compactCore ↔ ∀ a, p ∉ (A.ends a).image := by
  simp [compactCore_def]

/-- The compact core is closed in `M`. -/
theorem isClosed_compactCore : IsClosed A.compactCore := A.isOpen_endsUnion.isClosed_compl

/-- The compact core is compact in `M`. -/
theorem isCompact_compactCore : IsCompact A.compactCore := A.isCompact_compl

/-- **Monotonicity in the decay order** for finite-ended AE structures. -/
def ofLE {t₁ t₂ : ℝ} (A : FiniteEndedAE n M t₂) (ht : t₁ ≤ t₂) : FiniteEndedAE n M t₁ :=
  ⟨A.numEnds, A.numEnds_pos, fun a => (A.ends a).ofLE ht, A.pairwise_disjoint, A.isCompact_compl⟩

@[simp] theorem ofLE_numEnds {t₁ t₂ : ℝ} (A : FiniteEndedAE n M t₂) (ht : t₁ ≤ t₂) :
    (A.ofLE ht).numEnds = A.numEnds := (rfl)

@[simp] theorem ofLE_ends {t₁ t₂ : ℝ} (A : FiniteEndedAE n M t₂) (ht : t₁ ≤ t₂)
    (a : Fin (A.ofLE ht).numEnds) :
    (A.ofLE ht).ends a = (A.ends (a.cast (A.ofLE_numEnds ht))).ofLE ht := (rfl)

@[simp] theorem ofLE_endsUnion {t₁ t₂ : ℝ} (A : FiniteEndedAE n M t₂) (ht : t₁ ≤ t₂) :
    (A.ofLE ht).endsUnion = A.endsUnion := (rfl)

@[simp] theorem ofLE_compactCore {t₁ t₂ : ℝ} (A : FiniteEndedAE n M t₂) (ht : t₁ ≤ t₂) :
    (A.ofLE ht).compactCore = A.compactCore := (rfl)

end FiniteEndedAE

/-! ### Euclidean witnesses and scaling obstruction -/

/-- **Flat Euclidean space as an AE end.** For every `R > 0` and every decay order `t : ℝ`, the
identity parametrization of `{x ∈ ℝⁿ : R < ‖x‖}` is an asymptotically Euclidean end of flat
`EuclideanSpace ℝ (Fin n)`. -/
def AsymptoticallyEuclideanEnd.euclideanId (n : ℕ) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    AsymptoticallyEuclideanEnd n (EuclideanSpace ℝ (Fin n)) t :=
  AsymptoticallyEuclideanEnd.ofFun hR id contMDiffOn_id (Set.injOn_id {x | R < ‖x‖})
    (by simpa only [image_id] using isOpen_lt continuous_const continuous_norm)
    (fun x _ => by simpa [mfderiv_id] using Function.injective_id)
    (fun i j => by simp only [pullbackMetricCoeff_id]; exact contDiffOn_const)
    ⟨0, fun x _ i j => by
      have hd1 : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
          pullbackMetricCoeff id y i j) = 0 := by simp [pullbackMetricCoeff_id]
      rw [pullbackMetricCoeff_id, sub_self, abs_zero, zero_mul, hd1]
      refine ⟨le_rfl, ?_, ?_⟩
      · rw [Pi.zero_apply, norm_zero, zero_mul]
      · rw [Pi.zero_def, fderiv_const_apply, zero_mul]
        exact (norm_zero (E :=
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).le⟩

@[simp] theorem AsymptoticallyEuclideanEnd.euclideanId_radius (n : ℕ) {R : ℝ} (hR : 0 < R)
    (t : ℝ) : (AsymptoticallyEuclideanEnd.euclideanId n hR t).radius = R := (rfl)

@[simp] theorem AsymptoticallyEuclideanEnd.euclideanId_param_apply (n : ℕ) {R : ℝ} (hR : 0 < R)
    (t : ℝ) (x : exteriorOpen n (AsymptoticallyEuclideanEnd.euclideanId n hR t).radius) :
    (AsymptoticallyEuclideanEnd.euclideanId n hR t).param x = x.1 := (rfl)

@[simp] theorem AsymptoticallyEuclideanEnd.euclideanId_image (n : ℕ) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    (AsymptoticallyEuclideanEnd.euclideanId n hR t).image = {x | R < ‖x‖} := by
  rw [euclideanId, ofFun_image, image_id]

@[simp] theorem AsymptoticallyEuclideanEnd.euclideanId_metricCoeff_of_lt (n : ℕ) {R : ℝ}
    (hR : 0 < R) (t : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖) (i j : Fin n) :
    (AsymptoticallyEuclideanEnd.euclideanId n hR t).metricCoeff x i j =
      if i = j then 1 else 0 := by
  rw [euclideanId, ofFun_metricCoeff_of_lt _ _ _ _ _ _ _ _ hx, pullbackMetricCoeff_id]

/-- **Flat Euclidean space is finite-ended AE of every order.** Excising `closedBall 0 1` gives a
single AE end of flat `EuclideanSpace ℝ (Fin n)` with compact complement. -/
def FiniteEndedAE.euclideanSpace (n : ℕ) (t : ℝ) :
    FiniteEndedAE n (EuclideanSpace ℝ (Fin n)) t where
  numEnds := 1
  numEnds_pos := Nat.one_pos
  ends _ := AsymptoticallyEuclideanEnd.euclideanId n zero_lt_one t
  pairwise_disjoint a b hab := False.elim (hab (Subsingleton.elim a b))
  isCompact_compl := by
    have hu : (⋃ _ : Fin 1, (AsymptoticallyEuclideanEnd.euclideanId n zero_lt_one t).image)ᶜ =
        closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      ext x; simp [dist_zero_right]
    rw [hu]; exact isCompact_closedBall 0 1

@[simp] theorem FiniteEndedAE.euclideanSpace_numEnds (n : ℕ) (t : ℝ) :
    (FiniteEndedAE.euclideanSpace n t).numEnds = 1 := (rfl)

@[simp] theorem FiniteEndedAE.euclideanSpace_ends (n : ℕ) (t : ℝ)
    (a : Fin (FiniteEndedAE.euclideanSpace n t).numEnds) :
    (FiniteEndedAE.euclideanSpace n t).ends a =
      AsymptoticallyEuclideanEnd.euclideanId n zero_lt_one t := (rfl)

/-- **Non-unit scaling is not asymptotically Euclidean.** In dimension `n ≥ 1`, for any `t > 0` and
any `c : ℝ` with `|c| ≠ 1` (in particular `c = 2`, where `g_ij - δ_ij = 3 δ_ij`), no
`AsymptoticallyEuclideanEnd` of flat `EuclideanSpace ℝ (Fin n)` of order `t` has parametrization
`x ↦ c • x`. -/
theorem not_exists_asymptoticallyEuclideanEnd_smul {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 < t)
    {c : ℝ} (hc : |c| ≠ 1) :
    ¬ ∃ E : AsymptoticallyEuclideanEnd n (EuclideanSpace ℝ (Fin n)) t,
      ∀ x : exteriorOpen n E.radius, E.param x = c • (x : EuclideanSpace ℝ (Fin n)) := by
  rintro ⟨E, hE⟩
  obtain ⟨C, hC⟩ := E.decay_metricCoeff
  let i₀ : Fin n := ⟨0, hn⟩
  let e₀ : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i₀ 1
  have he₀ : ‖e₀‖ = 1 := by simp [e₀]
  have hgap : 0 < |c ^ 2 - 1| := by
    rw [abs_pos, sub_ne_zero]; intro hc2; apply hc; nlinarith [abs_nonneg c, sq_abs c]
  have htend : Tendsto (fun r : ℝ => C * r ^ (-t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop ht).const_mul C
  obtain ⟨r, hr_bound, hrR⟩ :=
    ((htend.eventually (gt_mem_nhds hgap)).and (eventually_gt_atTop E.radius)).exists
  have hr_pos : 0 < r := E.radius_pos.trans hrR
  have hnorm : ‖r • e₀‖ = r := by rw [norm_smul, Real.norm_of_nonneg hr_pos.le, he₀, mul_one]
  have hxr : E.radius < ‖r • e₀‖ := hnorm.symm ▸ hrR
  have hcoeff : E.metricCoeff (r • e₀) i₀ i₀ = c ^ 2 := by
    rw [E.metricCoeff_eq_pullbackMetricCoeff (φ := fun y => c • y) hxr
      (Eventually.of_forall hE) i₀ i₀, pullbackMetricCoeff_const_smul]
    simp only [↓reduceIte]
  have hle := (hC (r • e₀) hxr i₀ i₀).1
  simp only [hcoeff, ↓reduceIte, hnorm] at hle
  exact not_lt_of_ge hle hr_bound

end TauCeti
