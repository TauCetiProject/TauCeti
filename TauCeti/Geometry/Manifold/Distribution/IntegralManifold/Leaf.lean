/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.SecondCountable

import Mathlib.Topology.Connected.LocallyConnected
import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.Existence
import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.Involutive
import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.Overlap
import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.Topology
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Topology

/-!
# Global leaves of involutive distributions

Every point of a finite-dimensional real `C^r` manifold with boundaryless model lies on a global
leaf of an involutive `C^m` distribution of constant rank `k`, for `1 ≤ m` and `m + 1 ≤ r`: a
connected `k`-dimensional `C^m` integral manifold with its own intrinsic manifold topology whose
parametrization is injective and whose image contains the image of every preconnected horizontal
differentiable manifold meeting it. Consequently, the images of the leaves partition the ambient
manifold, any maximal connected injectively parametrized `C^m` integral manifold through a point
is `C^m` diffeomorphic to the canonical leaf over the ambient manifold, and when `2 ≤ m` a `C^m`
constant-rank distribution is involutive if and only if every point lies on a `C^m` integral
manifold (or global leaf).

The construction glues the family of all Euclidean-modelled integral plaques into an intrinsic
`k`-dimensional `C^m` manifold structure on `WithTopology M t` via
`TauCeti.chartedSpaceOfIntegralManifolds`, and takes the open connected component of the base
point in this intrinsic topology. No Hausdorff or second-countability hypothesis on `M` is needed
for existence, connectedness, injectivity, or maximality; Hausdorffness and second countability of
`M` each pass to the leaf carrier when present. Boundarylessness of the model `I` cannot be
weakened to `BoundarylessManifold I M` uniformly in `k`: for `k = 0`, Mathlib's immersion normal
form sends the unique chart coordinate `0` of `ℝ⁰` to `0` in the extended target chart, whereas
interior points of an open subset of the half-space model `𝓡∂ 1` have strictly positive chart
coordinates.

## Main definitions

* `TauCeti.IsInvolutiveDistribution.leaf`: the canonical global `C^m` leaf of an involutive
  distribution through a point `x : M`, as a packaged `IntegralManifold` in the same universe as
  `M`.

## Main results

* `TauCeti.IsInvolutiveDistribution.mem_range_leaf_self`,
  `TauCeti.IsInvolutiveDistribution.connectedSpace_leaf`,
  `TauCeti.IsInvolutiveDistribution.injective_leaf_map`: base-point membership, connectedness, and
  injectivity of the canonical leaf.
* `TauCeti.IsInvolutiveDistribution.t2Space_leaf` and
  `TauCeti.IsInvolutiveDistribution.secondCountableTopology_leaf`: separation and second
  countability inherited from the ambient manifold.
* `TauCeti.IsInvolutiveDistribution.range_subset_leaf_of_isHorizontalMap`,
  `TauCeti.IsInvolutiveDistribution.range_subset_leaf_of_isIntegralManifold`, and
  `TauCeti.IsInvolutiveDistribution.range_subset_leaf`: maximality of the leaf among preconnected
  horizontal and integral manifolds meeting it.
* `TauCeti.IsInvolutiveDistribution.range_leaf_eq_iff` and
  `TauCeti.IsInvolutiveDistribution.disjoint_range_leaf_iff`: the leaf images partition `M`.
* `TauCeti.IsInvolutiveDistribution.exists_diffeomorph_leaf_of_maximal`: uniqueness of maximal
  connected injective `C^m` integral manifolds up to `C^m` diffeomorphism over `M`.
* `TauCeti.IsInvolutiveDistribution.exists_contMDiff_factor_leaf`: unique `C^m` factorization into
  a leaf over a second-countable ambient manifold.
* `TauCeti.IsInvolutiveDistribution.exists_leaf`: packaged global Frobenius leaf existence.
* `TauCeti.IsContMDiffDistribution.isInvolutiveDistribution_iff_forall_exists_integralManifold`
  and `TauCeti.IsContMDiffDistribution.isInvolutiveDistribution_iff_forall_exists_leaf`: the global
  Frobenius integrability theorem (`2 ≤ m`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition (2013), Theorem 19.21 and
  Lemmas 19.22–19.23, pp. 502–505 (the global Frobenius theorem and maximal integral manifolds).
-/

public section

noncomputable section

open Set Function Filter Topology TopologicalSpace Manifold
open scoped Manifold ContDiff Topology

universe u

namespace TauCeti

section Construction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [tM : TopologicalSpace M] [ChartedSpace H M]

/-- An injective Euclidean-modelled `C^m` integral plaque of `D` in `M`. Because
`Opens (EuclideanSpace ℝ (Fin k))` lives in `Type`, the type of all such plaques lives in the same
universe `u` as `M`. -/
private structure Plaque (m : ℕ∞) (k : ℕ) (D : ∀ x : M, Submodule ℝ (TangentSpace I x)) :
    Type u where
  dom : Opens (EuclideanSpace ℝ (Fin k))
  map : dom → M
  injective : Injective map
  isIntegralManifold : IsIntegralManifold (𝓡 k) m D map

/-- The intrinsic leaf topology on `M`, coinduced by all injective Euclidean integral plaques. -/
private abbrev leafTop (m : ℕ∞) (k : ℕ) (D : ∀ x : M, Submodule ℝ (TangentSpace I x)) :
    TopologicalSpace M :=
  ⨆ p : Plaque (I := I) m k D, TopologicalSpace.coinduced p.map inferInstance

private theorem plaque_cover {m : ℕ∞} (hm : 1 ≤ m) {r : ℕ∞ω} (hmr : (m : ℕ∞ω) + 1 ≤ r)
    [IsManifold I 1 M] [IsManifold I r M] {k : ℕ}
    {D : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) (x : M) :
    ∃ (p : Plaque (I := I) m k D) (y : p.dom), p.map y = x := by
  obtain ⟨_, _, V, v, g, _, _, _, hgv, _, hemb, _, hg⟩ :=
    hinv.exists_isIntegralManifold_euclidean hm hmr hD x
  exact ⟨⟨V, g, hemb.injective, hg⟩, v, hgv⟩

/-- The intrinsic `k`-dimensional charted-space structure on `M` glued from its integral plaques. -/
@[instance_reducible]
private def leafChartedSpace {m : ℕ∞} (hm : 1 ≤ m) {r : ℕ∞ω} (hmr : (m : ℕ∞ω) + 1 ≤ r)
    [IsManifold I 1 M] [IsManifold I r M] {k : ℕ}
    {D : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) :
    ChartedSpace (EuclideanSpace ℝ (Fin k)) (WithTopology M (leafTop (I := I) m k D)) :=
  chartedSpaceOfIntegralManifolds (J := 𝓡 k) (fun p : Plaque (I := I) m k D ↦ p.isIntegralManifold)
    hm hmr hinv hD (fun p ↦ p.injective) (plaque_cover hm hmr hinv hD)

private theorem isManifold_leafChartedSpace {m : ℕ∞} (hm : 1 ≤ m)
    {r : ℕ∞ω} (hmr : (m : ℕ∞ω) + 1 ≤ r) [IsManifold I 1 M] [IsManifold I r M] {k : ℕ}
    {D : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) :
    letI := leafChartedSpace hm hmr hinv hD
    IsManifold (𝓡 k) m (WithTopology M (leafTop (I := I) m k D)) :=
  isManifold_chartedSpaceOfIntegralManifolds (J := 𝓡 k)
    (fun p : Plaque (I := I) m k D ↦ p.isIntegralManifold)
    hm hmr hinv hD (fun p ↦ p.injective) (plaque_cover hm hmr hinv hD)

/-- The connected component of `x` in the intrinsic leaf topology is open, since `M` with its
intrinsic leaf atlas is locally path-connected. -/
private def leafOpen {m : ℕ∞} (hm : 1 ≤ m) {r : ℕ∞ω} (hmr : (m : ℕ∞ω) + 1 ≤ r)
    [IsManifold I 1 M] [IsManifold I r M] {k : ℕ}
    {D : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) (x : M) :
    Opens (WithTopology M (leafTop (I := I) m k D)) where
  carrier := connectedComponent (WithTopology.toTopology (leafTop (I := I) m k D) x)
  is_open' := by
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) (WithTopology M (leafTop (I := I) m k D)) :=
      leafChartedSpace hm hmr hinv hD
    have _ : LocallyPathConnectedSpace (WithTopology M (leafTop (I := I) m k D)) :=
      (𝓡 k).locallyPathConnectedSpace_of_chartedSpace _
    exact isOpen_connectedComponent

/-- The canonical global `C^m` leaf of an involutive `C^m` distribution `D` of rank `k` through
`x`, on a finite-dimensional real `C^r` manifold with boundaryless model (`1 ≤ m`, `m + 1 ≤ r`). -/
def IsInvolutiveDistribution.leaf {m : ℕ∞} (hm : 1 ≤ m) {r : ℕ∞ω} (hmr : (m : ℕ∞ω) + 1 ≤ r)
    [IsManifold I 1 M] [IsManifold I r M] {k : ℕ}
    {D : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) (x : M) :
    IntegralManifold.{u, u} (I := I) m D k :=
  let t := leafTop (I := I) m k D
  -- A local topology-valued term is a typeclass candidate; retain the ambient topology on `M`.
  let : TopologicalSpace M := tM
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) (WithTopology M t) :=
    leafChartedSpace hm hmr hinv hD
  let _ : IsManifold (𝓡 k) m (WithTopology M t) :=
    isManifold_leafChartedSpace hm hmr hinv hD
  let L : Opens (WithTopology M t) := leafOpen hm hmr hinv hD x
  { carrier := L
    nonempty := ⟨⟨WithTopology.toTopology t x, mem_connectedComponent⟩⟩
    map := WithTopology.ofTopology (t := t) ∘ (Subtype.val : L → WithTopology M t)
    isImmersion := by
      have : Nonempty M := ⟨x⟩
      have hOfTop : IsIntegralManifold (I := I) (𝓡 k) m D (WithTopology.ofTopology (t := t)) :=
        isIntegralManifold_ofTopology (J := 𝓡 k)
          (fun p : Plaque (I := I) m k D ↦ p.isIntegralManifold)
          hm hmr hinv hD (fun p ↦ p.injective) (plaque_cover hm hmr hinv hD)
      exact isImmersion_comp_isLocalDiffeomorph isLocalDiffeomorph_subtype_val hOfTop.isImmersion
    range_mfderiv := fun y ↦ by
      have : Nonempty M := ⟨x⟩
      have hOfTop : IsIntegralManifold (I := I) (𝓡 k) m D (WithTopology.ofTopology (t := t)) :=
        isIntegralManifold_ofTopology (J := 𝓡 k)
          (fun p : Plaque (I := I) m k D ↦ p.isIntegralManifold)
          hm hmr hinv hD (fun p ↦ p.injective) (plaque_cover hm hmr hinv hD)
      have hm0 : (m : ℕ∞ω) ≠ 0 := ne_of_gt (zero_lt_one.trans_le (by exact_mod_cast hm))
      exact ((isLocalDiffeomorph_subtype_val (I := 𝓡 k) (n := m) y).range_mfderiv_comp hm0).trans
        (hOfTop.range_mfderiv y.1) }

omit [I.Boundaryless] in
/-- A horizontal differentiable map into `M` locally lands in the affine slice plaque through each
image point. -/
private theorem eventually_mem_slice_plaque {m : ℕ∞} (hm : 1 ≤ m)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold J 1 P]
    {D : ∀ z : M, Submodule ℝ (TangentSpace I z)} {g : P → M}
    (hg_hor : IsHorizontalMap J D g) (hg_diff : MDifferentiable J I g) {q₀ : P}
    {W : Submodule ℝ E} {Φ : PartialDiffeomorph I 𝓘(ℝ, E) M E m}
    (hxΦ : g q₀ ∈ Φ.source)
    (hΦflat : ∀ y ∈ Φ.source, (D y).map (mfderiv I 𝓘(ℝ, E) Φ y).toLinearMap = W)
    {S : Set M}
    (hslice : IsSliceChart Φ.toOpenPartialHomeomorph
      (range fun w : W ↦ Φ (g q₀) + (w : E)) S) :
    ∀ᶠ q in 𝓝 q₀, g q ∈ S := by
  have hm0 : (m : ℕ∞ω) ≠ 0 := ne_of_gt (zero_lt_one.trans_le (by exact_mod_cast hm))
  have hDp (z : M) (hz : z ∈ Φ.source) : (D z).map (mvfderiv I Φ z).toLinearMap ≤ W := by
    rw [(D z).map_mvfderiv_eq_map_mfderiv (I := I) (x := z) Φ]
    exact (hΦflat z hz).le
  have hstay := hg_hor.eventually_sub_mem hg_diff.mdifferentiableOn isOpen_univ
    (Φ.contMDiffOn.mdifferentiableOn hm0) Φ.open_source W.isClosed_of_finiteDimensional hDp
    (mem_univ q₀) hxΦ
  have hgΦ := hg_diff.continuous.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hxΦ)
  filter_upwards [hgΦ, hstay] with q hqΦ hqW
  refine (isSliceChart_iff.mp hslice (g q) hqΦ).mpr ⟨⟨Φ (g q) - Φ (g q₀), hqW⟩, ?_⟩
  simp only [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, add_sub_cancel]

/-- Every horizontal differentiable map from a `C¹` manifold (possibly with boundary or corners)
into `M` is continuous into the intrinsic leaf topology on `M`. -/
private theorem continuous_toTopology_comp_of_isHorizontalMap {m : ℕ∞} (hm : 1 ≤ m)
    {r : ℕ∞ω} (hmr : (m : ℕ∞ω) + 1 ≤ r) [IsManifold I 1 M] [IsManifold I r M] {k : ℕ}
    {D : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold J 1 P]
    {g : P → M} (hg_hor : IsHorizontalMap J D g) (hg_diff : MDifferentiable J I g) :
    Continuous (WithTopology.toTopology (leafTop (I := I) m k D) ∘ g) := by
  classical
  let t := leafTop (I := I) m k D
  let : TopologicalSpace M := tM
  rw [continuous_iff_continuousAt]
  intro q₀
  obtain ⟨W, Φ, V, v, f, _, hxΦ, hΦflat, _, _, hemb, hslice, hf⟩ :=
    hinv.exists_isIntegralManifold_euclidean hm hmr hD (g q₀)
  have hmem : ∀ᶠ q in 𝓝 q₀, g q ∈ range f :=
    eventually_mem_slice_plaque hm hg_hor hg_diff hxΦ hΦflat hslice
  let hloc : P → V := fun q ↦ if hq : g q ∈ range f then hq.choose else v
  have hfeq : f ∘ hloc =ᶠ[𝓝 q₀] g := by
    filter_upwards [hmem] with q hq
    simp only [hloc, Function.comp_apply, hq, ↓reduceDIte, hq.choose_spec]
  have hhcont : ContinuousAt hloc q₀ :=
    hemb.isInducing.continuousAt_iff.mpr (hg_diff.continuous.continuousAt.congr hfeq.symm)
  let p₀ : Plaque (I := I) m k D := ⟨V, f, hemb.injective, hf⟩
  have hp₀ : Continuous (WithTopology.toTopology t ∘ p₀.map) :=
    (isOpenEmbedding_integral_coinduced (J := 𝓡 k)
      (fun p : Plaque (I := I) m k D ↦ p.isIntegralManifold)
      hm hmr hinv hD (fun p ↦ p.injective) p₀).continuous
  exact (hp₀.continuousAt.comp hhcont).congr (hfeq.fun_comp (WithTopology.toTopology t))

end Construction

section API

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [tM : TopologicalSpace M] [ChartedSpace H M]
  {m : ℕ∞} {r : ℕ∞ω} [IsManifold I 1 M] [IsManifold I r M] {k : ℕ}
  {D : ∀ x : M, Submodule ℝ (TangentSpace I x)}

/-- A point belongs to the image of the canonical leaf through `x` precisely when its intrinsic
connected component equals that of `x`. -/
private theorem mem_range_leaf_iff_mem_connectedComponent (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) {x y : M} :
    y ∈ range (hinv.leaf hm hmr hD x).map ↔
      WithTopology.toTopology (leafTop (I := I) m k D) y ∈
        connectedComponent (WithTopology.toTopology (leafTop (I := I) m k D) x) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact (WithTopology.toTopology_ofTopology (leafTop (I := I) m k D) z.1).symm ▸ z.2
  · intro hy
    exact ⟨⟨WithTopology.toTopology (leafTop (I := I) m k D) y, hy⟩,
      WithTopology.ofTopology_toTopology (leafTop (I := I) m k D) y⟩

/-- Every point lies in the image of the canonical leaf through it. -/
theorem IsInvolutiveDistribution.mem_range_leaf_self (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) (x : M) :
    x ∈ range (hinv.leaf hm hmr hD x).map :=
  (mem_range_leaf_iff_mem_connectedComponent hm hmr hinv hD).mpr mem_connectedComponent

/-- The intrinsic carrier of the canonical leaf through any point is connected. -/
instance IsInvolutiveDistribution.connectedSpace_leaf (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) (x : M) :
    ConnectedSpace (hinv.leaf hm hmr hD x).carrier :=
  Subtype.connectedSpace isConnected_connectedComponent

/-- The ambient parametrization of the canonical leaf is injective. -/
theorem IsInvolutiveDistribution.injective_leaf_map (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) (x : M) :
    Injective (hinv.leaf hm hmr hD x).map :=
  (WithTopology.ofTopology_injective _).comp Subtype.val_injective

/-- When the ambient manifold is Hausdorff, the intrinsic carrier of each leaf is Hausdorff. -/
theorem IsInvolutiveDistribution.t2Space_leaf [T2Space M] (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) (x : M) :
    T2Space (hinv.leaf hm hmr hD x).carrier :=
  .of_injective_continuous (hinv.injective_leaf_map hm hmr hD x)
    (hinv.leaf hm hmr hD x).contMDiff_map.continuous

/-- When the ambient manifold is second countable, the intrinsic carrier of each leaf is second
countable. -/
theorem IsInvolutiveDistribution.secondCountableTopology_leaf [SecondCountableTopology M]
    (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) (x : M) :
    SecondCountableTopology (hinv.leaf hm hmr hD x).carrier :=
  (hinv.leaf hm hmr hD x).secondCountableTopology hm hmr hinv hD
    (hinv.injective_leaf_map hm hmr hD x)

/-- Every horizontal differentiable map from a preconnected `C¹` manifold whose image meets a
canonical leaf has its entire image contained in that leaf. -/
theorem IsInvolutiveDistribution.range_subset_leaf_of_isHorizontalMap
    (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) {x : M}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold J 1 P] [PreconnectedSpace P]
    {g : P → M} (hg_hor : IsHorizontalMap J D g) (hg_diff : MDifferentiable J I g)
    (hmeet : (range g ∩ range (hinv.leaf hm hmr hD x).map).Nonempty) :
    range g ⊆ range (hinv.leaf hm hmr hD x).map := by
  let : TopologicalSpace M := tM
  have hcont : Continuous (WithTopology.toTopology (leafTop (I := I) m k D) ∘ g) :=
    continuous_toTopology_comp_of_isHorizontalMap hm hmr hinv hD hg_hor hg_diff
  have hpre : IsPreconnected (range (WithTopology.toTopology (leafTop (I := I) m k D) ∘ g)) :=
    isPreconnected_range hcont
  obtain ⟨_, ⟨q₀, rfl⟩, hgx⟩ := hmeet
  have hq₀ := (mem_range_leaf_iff_mem_connectedComponent hm hmr hinv hD).mp hgx
  have hsub : range (WithTopology.toTopology (leafTop (I := I) m k D) ∘ g) ⊆
      connectedComponent (WithTopology.toTopology (leafTop (I := I) m k D) x) := by
    rw [connectedComponent_eq hq₀]
    exact hpre.subset_connectedComponent (mem_range_self q₀)
  rintro _ ⟨q, rfl⟩
  exact (mem_range_leaf_iff_mem_connectedComponent hm hmr hinv hD).mpr (hsub (mem_range_self q))

/-- Every preconnected integral manifold of regularity at least `C¹` whose image meets a canonical
leaf has its entire image contained in that leaf. -/
theorem IsInvolutiveDistribution.range_subset_leaf_of_isIntegralManifold
    (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) {x : M}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
    {m' : ℕ∞ω} (hm' : 1 ≤ m') [IsManifold J m' P] [PreconnectedSpace P]
    {g : P → M} (hg : IsIntegralManifold J m' D g)
    (hmeet : (range g ∩ range (hinv.leaf hm hmr hD x).map).Nonempty) :
    range g ⊆ range (hinv.leaf hm hmr hD x).map := by
  let _ : IsManifold J 1 P := .of_le hm'
  have hm'0 : m' ≠ 0 := ne_of_gt (zero_lt_one.trans_le hm')
  exact hinv.range_subset_leaf_of_isHorizontalMap hm hmr hD
    (isHorizontalMap_iff_range_mfderiv_le.mpr fun z ↦ (hg.range_mfderiv z).le)
    (hg.contMDiff.mdifferentiable hm'0) hmeet

/-- Every preconnected packaged integral manifold of regularity at least `C¹` whose image meets a
canonical leaf has its entire image contained in that leaf. -/
theorem IsInvolutiveDistribution.range_subset_leaf
    (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) {x : M}
    {m' : ℕ∞ω} (hm' : 1 ≤ m') (N' : IntegralManifold (I := I) m' D k)
    [PreconnectedSpace N'.carrier]
    (hmeet : (range N'.map ∩ range (hinv.leaf hm hmr hD x).map).Nonempty) :
    range N'.map ⊆ range (hinv.leaf hm hmr hD x).map :=
  hinv.range_subset_leaf_of_isIntegralManifold hm hmr hD hm' N'.isIntegralManifold hmeet

/-- The canonical leaf through any point of a leaf has the same ambient image as that leaf. -/
theorem IsInvolutiveDistribution.range_leaf_eq_of_mem (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) {x y : M}
    (hy : y ∈ range (hinv.leaf hm hmr hD x).map) :
    range (hinv.leaf hm hmr hD y).map = range (hinv.leaf hm hmr hD x).map := by
  have hm' : (1 : ℕ∞ω) ≤ m := by exact_mod_cast hm
  have hsub : range (hinv.leaf hm hmr hD y).map ⊆ range (hinv.leaf hm hmr hD x).map :=
    hinv.range_subset_leaf hm hmr hD hm' (hinv.leaf hm hmr hD y)
      ⟨y, hinv.mem_range_leaf_self hm hmr hD y, hy⟩
  refine Subset.antisymm hsub ?_
  exact hinv.range_subset_leaf hm hmr hD hm' (hinv.leaf hm hmr hD x)
    ⟨y, hy, hinv.mem_range_leaf_self hm hmr hD y⟩

/-- Membership in the ambient image of a canonical leaf is symmetric in the two points. -/
theorem IsInvolutiveDistribution.mem_range_leaf_comm (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) {x y : M} :
    y ∈ range (hinv.leaf hm hmr hD x).map ↔ x ∈ range (hinv.leaf hm hmr hD y).map := by
  refine ⟨fun hy ↦ ?_, fun hx ↦ ?_⟩
  · rw [hinv.range_leaf_eq_of_mem hm hmr hD hy]
    exact hinv.mem_range_leaf_self hm hmr hD x
  · rw [hinv.range_leaf_eq_of_mem hm hmr hD hx]
    exact hinv.mem_range_leaf_self hm hmr hD y

/-- Two canonical leaves have the same ambient image if and only if one base point lies in the
image of the other leaf. -/
@[simp]
theorem IsInvolutiveDistribution.range_leaf_eq_iff (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) {x y : M} :
    range (hinv.leaf hm hmr hD x).map = range (hinv.leaf hm hmr hD y).map ↔
      x ∈ range (hinv.leaf hm hmr hD y).map :=
  ⟨fun h ↦ h ▸ hinv.mem_range_leaf_self hm hmr hD x, hinv.range_leaf_eq_of_mem hm hmr hD⟩

/-- Two canonical leaves have disjoint ambient images if and only if neither base point lies in the
image of the other leaf; thus the leaf images partition `M`. -/
@[simp]
theorem IsInvolutiveDistribution.disjoint_range_leaf_iff (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) {x y : M} :
    Disjoint (range (hinv.leaf hm hmr hD x).map) (range (hinv.leaf hm hmr hD y).map) ↔
      x ∉ range (hinv.leaf hm hmr hD y).map := by
  refine ⟨fun h hx ↦ disjoint_left.mp h (hinv.mem_range_leaf_self hm hmr hD x) hx, fun h ↦ ?_⟩
  refine disjoint_left.mpr fun z hzx hzy ↦ h ?_
  rw [← hinv.range_leaf_eq_of_mem hm hmr hD hzy, hinv.range_leaf_eq_of_mem hm hmr hD hzx]
  exact hinv.mem_range_leaf_self hm hmr hD x

/-- For any point `y` in the ambient image of the leaf through `x`, the intrinsic carriers of the
leaves through `y` and `x` are `C^m` diffeomorphic over `M`. -/
theorem IsInvolutiveDistribution.exists_diffeomorph_leaf_of_mem
    (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) {x y : M}
    (hy : y ∈ range (hinv.leaf hm hmr hD x).map) :
    ∃ e : Diffeomorph (𝓡 k) (𝓡 k)
        (hinv.leaf hm hmr hD y).carrier (hinv.leaf hm hmr hD x).carrier m,
      ∀ z, (hinv.leaf hm hmr hD x).map (e z) = (hinv.leaf hm hmr hD y).map z :=
  (hinv.leaf hm hmr hD y).isIntegralManifold.exists_diffeomorph_of_range_eq
    (hinv.leaf hm hmr hD x).isIntegralManifold hm hmr hinv hD
    (hinv.injective_leaf_map hm hmr hD y) (hinv.injective_leaf_map hm hmr hD x)
    (hinv.range_leaf_eq_of_mem hm hmr hD hy)

/-- Any preconnected injectively parametrized `C^m` integral manifold through `x` that contains the
image of every connected `C^m` integral manifold meeting it has the same ambient image as the
canonical leaf through `x` and is `C^m` diffeomorphic to it over `M`. -/
theorem IsInvolutiveDistribution.exists_diffeomorph_leaf_of_maximal
    (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) {x : M}
    (L : IntegralManifold (I := I) m D k) [PreconnectedSpace L.carrier]
    (hinj : Injective L.map) (hx : x ∈ range L.map)
    (hmax : ∀ N' : IntegralManifold.{u, u} (I := I) m D k, ConnectedSpace N'.carrier →
      (range N'.map ∩ range L.map).Nonempty → range N'.map ⊆ range L.map) :
    range L.map = range (hinv.leaf hm hmr hD x).map ∧
      ∃ e : Diffeomorph (𝓡 k) (𝓡 k) L.carrier (hinv.leaf hm hmr hD x).carrier m,
        ∀ z, (hinv.leaf hm hmr hD x).map (e z) = L.map z := by
  have hm' : (1 : ℕ∞ω) ≤ m := by exact_mod_cast hm
  have hrange : range L.map = range (hinv.leaf hm hmr hD x).map := Subset.antisymm
    (hinv.range_subset_leaf hm hmr hD hm' L ⟨x, hx, hinv.mem_range_leaf_self hm hmr hD x⟩)
    (hmax (hinv.leaf hm hmr hD x) inferInstance ⟨x, hinv.mem_range_leaf_self hm hmr hD x, hx⟩)
  exact ⟨hrange, L.isIntegralManifold.exists_diffeomorph_of_range_eq
    (hinv.leaf hm hmr hD x).isIntegralManifold hm hmr hinv hD
    hinj (hinv.injective_leaf_map hm hmr hD x) hrange⟩

/-- Over a second-countable ambient manifold, every `C^m` map into the ambient image of a canonical
leaf factors uniquely as a `C^m` map through the leaf's intrinsic carrier. -/
theorem IsInvolutiveDistribution.exists_contMDiff_factor_leaf [SecondCountableTopology M]
    (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) {x : M}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : Type*} [TopologicalSpace A] {K : ModelWithCorners ℝ V A}
    {P : Type*} [TopologicalSpace P] [ChartedSpace A P]
    {g : P → M} (hg : ContMDiff K I m g) (hr : range g ⊆ range (hinv.leaf hm hmr hD x).map) :
    ∃! h : P → (hinv.leaf hm hmr hD x).carrier,
      ContMDiff K (𝓡 k) m h ∧ (hinv.leaf hm hmr hD x).map ∘ h = g := by
  obtain ⟨h, hh, hcomp⟩ :=
    (hinv.leaf hm hmr hD x).exists_contMDiff_factor_of_preconnectedSpace hm
      (hinv.injective_leaf_map hm hmr hD x) hmr hinv hD hg hr
  refine ⟨h, ⟨hh, hcomp⟩, fun h' ⟨_, hcomp'⟩ ↦ funext fun p ↦ ?_⟩
  exact hinv.injective_leaf_map hm hmr hD x (congrFun (hcomp'.trans hcomp.symm) p)

/-- **Global Frobenius leaf existence.** Through every point `x` of a finite-dimensional real `C^r`
manifold with boundaryless model, an involutive `C^m` distribution of rank `k` (`1 ≤ m`,
`m + 1 ≤ r`) admits a connected, injectively parametrized `C^m` integral manifold containing `x`,
containing the image of every connected `C^m` integral manifold meeting it, and inheriting second
countability from `M`. -/
theorem IsInvolutiveDistribution.exists_leaf (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) (x : M) :
    ∃ N : IntegralManifold.{u, u} (I := I) m D k,
      x ∈ range N.map ∧ ConnectedSpace N.carrier ∧ Injective N.map ∧
        (∀ N' : IntegralManifold.{u, u} (I := I) m D k, ConnectedSpace N'.carrier →
          (range N'.map ∩ range N.map).Nonempty → range N'.map ⊆ range N.map) ∧
        (SecondCountableTopology M → SecondCountableTopology N.carrier) :=
  ⟨hinv.leaf hm hmr hD x, hinv.mem_range_leaf_self hm hmr hD x, inferInstance,
    hinv.injective_leaf_map hm hmr hD x,
    fun N' _ hmeet ↦ hinv.range_subset_leaf hm hmr hD (by exact_mod_cast hm) N' hmeet,
    fun _ ↦ hinv.secondCountableTopology_leaf hm hmr hD x⟩

/-- **Global Frobenius integrability theorem.** For `2 ≤ m` and `m + 1 ≤ r`, a `C^m` distribution
of constant rank `k` on a finite-dimensional real `C^r` manifold with boundaryless model is
involutive if and only if every point lies in the image of a `C^m` integral manifold. -/
theorem IsContMDiffDistribution.isInvolutiveDistribution_iff_forall_exists_integralManifold
    (hm : 2 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r) (hD : IsContMDiffDistribution I m k D) :
    IsInvolutiveDistribution I D ↔
      ∀ x : M, ∃ N : IntegralManifold.{u, u} (I := I) m D k, x ∈ range N.map := by
  have hm1 : 1 ≤ m := one_le_two.trans hm
  have hm2 : (2 : ℕ∞ω) ≤ m := WithTop.coe_le_coe.mpr hm
  let _ : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  let _ : IsManifold I 2 M := .of_le (hm2.trans (le_self_add.trans hmr))
  exact ⟨fun hinv x ↦ ⟨hinv.leaf hm1 hmr hD x, hinv.mem_range_leaf_self hm1 hmr hD x⟩,
    hD.isInvolutiveDistribution_of_forall_exists_integralManifold
      (WithTop.coe_le_coe.mpr hm1) hm2⟩

/-- **Global Frobenius theorem in leaf form.** For `2 ≤ m` and `m + 1 ≤ r`, a `C^m` distribution of
constant rank `k` on a finite-dimensional real `C^r` manifold with boundaryless model is involutive
if and only if every point lies on a connected, injectively parametrized, maximal `C^m` integral
manifold. -/
theorem IsContMDiffDistribution.isInvolutiveDistribution_iff_forall_exists_leaf
    (hm : 2 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r) (hD : IsContMDiffDistribution I m k D) :
    IsInvolutiveDistribution I D ↔
      ∀ x : M, ∃ N : IntegralManifold.{u, u} (I := I) m D k,
        x ∈ range N.map ∧ ConnectedSpace N.carrier ∧ Injective N.map ∧
          (∀ N' : IntegralManifold.{u, u} (I := I) m D k, ConnectedSpace N'.carrier →
            (range N'.map ∩ range N.map).Nonempty → range N'.map ⊆ range N.map) ∧
          (SecondCountableTopology M → SecondCountableTopology N.carrier) := by
  have hm1 : 1 ≤ m := one_le_two.trans hm
  refine ⟨fun hinv x ↦ hinv.exists_leaf hm1 hmr hD x, fun h ↦ ?_⟩
  exact (hD.isInvolutiveDistribution_iff_forall_exists_integralManifold hm hmr).mpr
    fun x ↦ let ⟨N, hx, _⟩ := h x; ⟨N, hx⟩

end API

end TauCeti
