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
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Topology

/-!
# Global leaves of involutive distributions

Every point of a finite-dimensional real `C^r` manifold with boundaryless model lies on a global
leaf of an involutive `C^m` distribution of constant rank `k`, for `1 ≤ m` (`m : ℕ∞`) and
`m + 1 ≤ r`: a connected `k`-dimensional `C^m` integral manifold with its own intrinsic manifold
topology whose parametrization is injective and whose image contains the image of every horizontal
differentiable map from a preconnected `C¹` manifold meeting it. Consequently, the images of the
leaves partition the ambient manifold, any maximal connected injectively parametrized `C^m`
integral manifold through a point is `C^m` diffeomorphic to the canonical leaf over the ambient
manifold, and when `2 ≤ m` a `C^m` constant-rank distribution is involutive if and only if every
point lies on a `C^m` integral manifold (or global leaf).

A global leaf need not be an embedded submanifold of `M`, as illustrated by dense irrational-slope
lines on a torus, so its ambient image with the subspace topology need not be a manifold. Equipping
each leaf with an intrinsic `k`-dimensional `C^m` manifold carrier preserves smooth factorization,
as needed for foliation leaf manifolds and immersed Lie subgroups: horizontal `C^n` maps (`1 ≤ n`,
`n ≤ m`) from `C¹` manifolds into a leaf factor uniquely through its carrier without topological
hypotheses on `M`, and arbitrary `C^n` maps (`n ≤ m`) into a leaf factor uniquely when `M` is
second countable. No Hausdorff or second-countability hypothesis on `M` is needed for existence,
connectedness, injectivity, or maximality; Hausdorffness and second countability of `M` each pass to
the leaf carrier as typeclass instances when present. Boundarylessness of the model `I` cannot be
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
  `TauCeti.IsInvolutiveDistribution.map_leaf_injective`: base-point membership, connectedness, and
  injectivity of the canonical leaf.
* `TauCeti.IsInvolutiveDistribution.t2Space_leaf` and
  `TauCeti.IsInvolutiveDistribution.secondCountableTopology_leaf`: separation and second
  countability instances inherited from the ambient manifold.
* `TauCeti.IsInvolutiveDistribution.range_subset_leaf_of_isHorizontalMap`,
  `TauCeti.IsInvolutiveDistribution.range_subset_leaf_of_isIntegralManifold`, and
  `TauCeti.IsInvolutiveDistribution.range_subset_leaf`: maximality of the leaf among preconnected
  horizontal maps and integral manifolds meeting it.
* `TauCeti.IsInvolutiveDistribution.range_leaf_eq_range_leaf`: independence of the ambient leaf
  image from the chosen leaf and ambient regularities.
* `TauCeti.IsInvolutiveDistribution.range_leaf_eq_iff` and
  `TauCeti.IsInvolutiveDistribution.disjoint_range_leaf_iff`: the leaf images partition `M`.
* `TauCeti.IsInvolutiveDistribution.range_eq_range_leaf_of_maximal` and
  `TauCeti.IsInvolutiveDistribution.exists_diffeomorph_leaf_of_maximal`: ambient-image equality and
  uniqueness of maximal preconnected injective `C^m` integral manifolds up to `C^m` diffeomorphism
  over `M`.
* `TauCeti.IsInvolutiveDistribution.existsUnique_contMDiff_factor_leaf_of_isHorizontalMap` and
  `TauCeti.IsInvolutiveDistribution.existsUnique_contMDiff_factor_leaf`: unique `C^n` (`n ≤ m`)
  factorization into a leaf for horizontal maps without `SecondCountableTopology M`, and for all
  maps over a second-countable ambient manifold.
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
  have : Nonempty M := ⟨x⟩
  have hne : Nonempty L := ⟨⟨WithTopology.toTopology t x, mem_connectedComponent⟩⟩
  have hm0 : (m : ℕ∞ω) ≠ 0 := ne_of_gt (zero_lt_one.trans_le (by exact_mod_cast hm))
  have hL : IsIntegralManifold (I := I) (𝓡 k) m D
      (WithTopology.ofTopology (t := t) ∘ (Subtype.val : L → WithTopology M t)) :=
    (isIntegralManifold_ofTopology (J := 𝓡 k)
      (fun p : Plaque (I := I) m k D ↦ p.isIntegralManifold)
      hm hmr hinv hD (fun p ↦ p.injective) (plaque_cover hm hmr hinv hD)).comp_subtypeVal hm0
  { carrier := L
    nonempty := hne
    map := WithTopology.ofTopology (t := t) ∘ (Subtype.val : L → WithTopology M t)
    isImmersion := hL.isImmersion
    range_mfderiv := hL.range_mfderiv }

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
theorem IsInvolutiveDistribution.map_leaf_injective (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) (x : M) :
    Injective (hinv.leaf hm hmr hD x).map :=
  (WithTopology.ofTopology_injective _).comp Subtype.val_injective

/-- When the ambient manifold is Hausdorff, the intrinsic carrier of each leaf is Hausdorff. -/
instance IsInvolutiveDistribution.t2Space_leaf [T2Space M] (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) (x : M) :
    T2Space (hinv.leaf hm hmr hD x).carrier :=
  .of_injective_continuous (hinv.map_leaf_injective hm hmr hD x)
    (hinv.leaf hm hmr hD x).contMDiff_map.continuous

/-- When the ambient manifold is second countable, the intrinsic carrier of each leaf is second
countable. -/
instance IsInvolutiveDistribution.secondCountableTopology_leaf [SecondCountableTopology M]
    (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) (x : M) :
    SecondCountableTopology (hinv.leaf hm hmr hD x).carrier :=
  (hinv.leaf hm hmr hD x).secondCountableTopology hm hmr hinv hD
    (hinv.map_leaf_injective hm hmr hD x)

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

omit [IsManifold I r M] in
/-- For an involutive constant-rank distribution on a finite-dimensional real manifold with
boundaryless model, the ambient point-set image of the canonical global leaf through `x` is
independent of the chosen leaf regularities `m₁, m₂ : ℕ∞` (`1 ≤ m₁`, `1 ≤ m₂`) and ambient
regularities `r₁, r₂` (`m₁ + 1 ≤ r₁`, `m₂ + 1 ≤ r₂`). -/
theorem IsInvolutiveDistribution.range_leaf_eq_range_leaf
    {m₁ m₂ : ℕ∞} {r₁ r₂ : ℕ∞ω} [IsManifold I r₁ M] [IsManifold I r₂ M] {k₁ k₂ : ℕ}
    (hinv : IsInvolutiveDistribution I D)
    (hm₁ : 1 ≤ m₁) (hmr₁ : (m₁ : ℕ∞ω) + 1 ≤ r₁) (hD₁ : IsContMDiffDistribution I m₁ k₁ D)
    (hm₂ : 1 ≤ m₂) (hmr₂ : (m₂ : ℕ∞ω) + 1 ≤ r₂) (hD₂ : IsContMDiffDistribution I m₂ k₂ D)
    (x : M) :
    range (hinv.leaf hm₁ hmr₁ hD₁ x).map = range (hinv.leaf hm₂ hmr₂ hD₂ x).map :=
  Subset.antisymm
    (hinv.range_subset_leaf_of_isIntegralManifold hm₂ hmr₂ hD₂ (WithTop.coe_le_coe.mpr hm₁)
      (hinv.leaf hm₁ hmr₁ hD₁ x).isIntegralManifold
      ⟨x, hinv.mem_range_leaf_self hm₁ hmr₁ hD₁ x, hinv.mem_range_leaf_self hm₂ hmr₂ hD₂ x⟩)
    (hinv.range_subset_leaf_of_isIntegralManifold hm₁ hmr₁ hD₁ (WithTop.coe_le_coe.mpr hm₂)
      (hinv.leaf hm₂ hmr₂ hD₂ x).isIntegralManifold
      ⟨x, hinv.mem_range_leaf_self hm₂ hmr₂ hD₂ x, hinv.mem_range_leaf_self hm₁ hmr₁ hD₁ x⟩)

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
    (hinv.map_leaf_injective hm hmr hD y) (hinv.map_leaf_injective hm hmr hD x)
    (hinv.range_leaf_eq_of_mem hm hmr hD hy)

/-- On a finite-dimensional real `C^r` manifold with boundaryless model, any preconnected `C^m`
integral manifold (`m : ℕ∞`, `1 ≤ m`, `m + 1 ≤ r`) of an involutive `C^m` distribution `D` of rank
`k` through `x` that contains the image of every connected `C^m` integral manifold meeting it has
the same ambient image as the canonical leaf through `x`. -/
theorem IsInvolutiveDistribution.range_eq_range_leaf_of_maximal
    (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) {x : M}
    (L : IntegralManifold (I := I) m D k) [PreconnectedSpace L.carrier] (hx : x ∈ range L.map)
    (hmax : ∀ N' : IntegralManifold.{u, u} (I := I) m D k, ConnectedSpace N'.carrier →
      (range N'.map ∩ range L.map).Nonempty → range N'.map ⊆ range L.map) :
    range L.map = range (hinv.leaf hm hmr hD x).map :=
  Subset.antisymm
    (hinv.range_subset_leaf hm hmr hD (WithTop.coe_le_coe.mpr hm) L
      ⟨x, hx, hinv.mem_range_leaf_self hm hmr hD x⟩)
    (hmax (hinv.leaf hm hmr hD x) inferInstance ⟨x, hinv.mem_range_leaf_self hm hmr hD x, hx⟩)

/-- On a finite-dimensional real `C^r` manifold with boundaryless model, any preconnected
injectively parametrized `C^m` integral manifold (`m : ℕ∞`, `1 ≤ m`, `m + 1 ≤ r`) of an involutive
`C^m` distribution `D` of rank `k` through `x` that contains the image of every connected `C^m`
integral manifold meeting it is `C^m` diffeomorphic over `M` to the canonical leaf through `x`. -/
theorem IsInvolutiveDistribution.exists_diffeomorph_leaf_of_maximal
    (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) {x : M}
    (L : IntegralManifold (I := I) m D k) [PreconnectedSpace L.carrier]
    (hinj : Injective L.map) (hx : x ∈ range L.map)
    (hmax : ∀ N' : IntegralManifold.{u, u} (I := I) m D k, ConnectedSpace N'.carrier →
      (range N'.map ∩ range L.map).Nonempty → range N'.map ⊆ range L.map) :
    ∃ e : Diffeomorph (𝓡 k) (𝓡 k) L.carrier (hinv.leaf hm hmr hD x).carrier m,
      ∀ z, (hinv.leaf hm hmr hD x).map (e z) = L.map z :=
  L.isIntegralManifold.exists_diffeomorph_of_range_eq
    (hinv.leaf hm hmr hD x).isIntegralManifold hm hmr hinv hD
    hinj (hinv.map_leaf_injective hm hmr hD x)
    (hinv.range_eq_range_leaf_of_maximal hm hmr hD L hx hmax)

/-- On a finite-dimensional real `C^r` manifold with boundaryless model (`1 ≤ m`, `m + 1 ≤ r`),
every horizontal `C^n` map (`1 ≤ n`, `n ≤ m`) from a `C¹` manifold into the ambient image of a
canonical `C^m` leaf of an involutive `C^m` distribution of rank `k` factors uniquely as a `C^n` map
through the leaf's intrinsic carrier, without assuming second countability of `M`. -/
theorem IsInvolutiveDistribution.existsUnique_contMDiff_factor_leaf_of_isHorizontalMap
    (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) {x : M}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : Type*} [TopologicalSpace A] {K : ModelWithCorners ℝ V A}
    {P : Type*} [TopologicalSpace P] [ChartedSpace A P] [IsManifold K 1 P]
    {n : ℕ∞ω} (hn : 1 ≤ n) (hnm : n ≤ m)
    {g : P → M} (hg_hor : IsHorizontalMap K D g) (hg : ContMDiff K I n g)
    (hr : range g ⊆ range (hinv.leaf hm hmr hD x).map) :
    ∃! h : P → (hinv.leaf hm hmr hD x).carrier,
      ContMDiff K (𝓡 k) n h ∧ (hinv.leaf hm hmr hD x).map ∘ h = g := by
  let : TopologicalSpace M := tM
  let _ : IsManifold (𝓡 k) n (hinv.leaf hm hmr hD x).carrier := .of_le hnm
  let _ : IsManifold I n M := .of_le (hnm.trans (le_self_add.trans hmr))
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hmem (p : P) : WithTopology.toTopology (leafTop (I := I) m k D) (g p) ∈
      connectedComponent (WithTopology.toTopology (leafTop (I := I) m k D) x) :=
    (mem_range_leaf_iff_mem_connectedComponent hm hmr hinv hD).mp (hr (mem_range_self p))
  let h : P → (hinv.leaf hm hmr hD x).carrier :=
    fun p ↦ ⟨WithTopology.toTopology (leafTop (I := I) m k D) (g p), hmem p⟩
  have hc : Continuous h :=
    (continuous_toTopology_comp_of_isHorizontalMap hm hmr hinv hD hg_hor
      (hg.mdifferentiable hn0)).subtype_mk hmem
  have hcomp : (hinv.leaf hm hmr hD x).map ∘ h = g :=
    funext fun p ↦ WithTopology.ofTopology_toTopology (leafTop (I := I) m k D) (g p)
  refine ⟨h, ⟨(ContMDiff.iff_comp_isImmersion
      ((hinv.leaf hm hmr hD x).isImmersion.of_le hnm)).mpr ⟨hc, hcomp.symm ▸ hg⟩, hcomp⟩,
    fun h' ⟨_, hcomp'⟩ ↦ funext fun p ↦ ?_⟩
  exact hinv.map_leaf_injective hm hmr hD x (congrFun (hcomp'.trans hcomp.symm) p)

/-- Over a second-countable finite-dimensional real `C^r` manifold with boundaryless model (`1 ≤ m`,
`m + 1 ≤ r`), every `C^n` map (`n ≤ m`) into the ambient image of a canonical `C^m` leaf of an
involutive `C^m` distribution of rank `k` factors uniquely as a `C^n` map through the leaf's
intrinsic carrier. -/
theorem IsInvolutiveDistribution.existsUnique_contMDiff_factor_leaf [SecondCountableTopology M]
    (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D) {x : M}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : Type*} [TopologicalSpace A] {K : ModelWithCorners ℝ V A}
    {P : Type*} [TopologicalSpace P] [ChartedSpace A P]
    {n : ℕ∞ω} (hnm : n ≤ m)
    {g : P → M} (hg : ContMDiff K I n g) (hr : range g ⊆ range (hinv.leaf hm hmr hD x).map) :
    ∃! h : P → (hinv.leaf hm hmr hD x).carrier,
      ContMDiff K (𝓡 k) n h ∧ (hinv.leaf hm hmr hD x).map ∘ h = g := by
  obtain ⟨h, hh, hcomp⟩ :=
    (hinv.leaf hm hmr hD x).exists_contMDiff_factor_of_preconnectedSpace hm
      (hinv.map_leaf_injective hm hmr hD x) hmr hinv hD hnm hg hr
  refine ⟨h, ⟨hh, hcomp⟩, fun h' ⟨_, hcomp'⟩ ↦ funext fun p ↦ ?_⟩
  exact hinv.map_leaf_injective hm hmr hD x (congrFun (hcomp'.trans hcomp.symm) p)

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
    hinv.map_leaf_injective hm hmr hD x,
    fun N' _ hmeet ↦ hinv.range_subset_leaf hm hmr hD (by exact_mod_cast hm) N' hmeet,
    fun _ ↦ inferInstance⟩

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
manifold inheriting second countability from `M`. -/
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
