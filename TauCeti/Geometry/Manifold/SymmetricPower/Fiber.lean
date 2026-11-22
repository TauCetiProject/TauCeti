/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.FiberMultiset
public import TauCeti.Geometry.Manifold.SymmetricPower.Manifold
import TauCeti.Analysis.Analytic.Multiset
import TauCeti.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Geometry.Manifold.Diffeomorph.ChartLinear

/-!
# The unordered fibres of a finite holomorphic map as a holomorphic map to a symmetric power

Let `f : X → Y` be a finite holomorphic map from a compact Riemann surface to a connected one, of
degree `d`, and let `u : X → Z` be a map to a third Riemann surface. Sending a point `y` of `Y` to
the images under `u` of the points of the fibre of `f` over `y`, each repeated according to the
local multiplicity of `f` there, gives an unordered `d`-tuple of points of `Z`
(`TauCeti.RiemannSurface.FiniteHolomorphicMap.fiberSym`): the divisor `u_* (f^* y)`. For `u` the
identity this is the classical map `Y → Sym^d X`, `y ↦ f^* y`.

The main result is that this map is holomorphic, across the branch values of `f` included, for
the elementary-symmetric complex structure of the symmetric power
(`TauCeti.RiemannSurface.FiniteHolomorphicMap.contMDiff_fiberSym`), and continuous for continuous
`u` (`TauCeti.RiemannSurface.FiniteHolomorphicMap.continuous_fiberSym`). Lipshitz's comparison of
the cylindrical and symmetric-product formulations of Heegaard Floer homology applies this
construction with `f` the projection of a holomorphic curve in `Σ × [0,1] × ℝ` to the strip and
`u` its projection to `Σ`. There the source is a punctured surface with boundary and `f` is a
proper branched cover; here the source is a closed surface.

In an elementary-symmetric chart of `Sym Z d` around the tuple over `y₀`, built from pairwise
disjoint coordinate patches `V i`, the coordinates of a nearby tuple are the elementary symmetric
functions of the coordinates of its points in each patch. The function equal to a power of the
coordinate of `u x` when `u x` lies in `V i`, and to `0` otherwise, is holomorphic near the fibre
over `y₀`, because the patches are disjoint and open. So its sums along the fibres of `f` are
holomorphic (`TauCeti.RiemannSurface.analyticAt_sum_map_fiberMultiset`); these sums are the power
sums of the coordinates of the points in `V i`, and the elementary symmetric functions follow by
Newton's identities. The zeroth power counts the points in `V i`, which is therefore locally
constant, and since `f` is a closed map the whole fibre stays in the patches: so the tuple over a
nearby point stays in the chart.

## Main declarations

* `TauCeti.RiemannSurface.FiniteHolomorphicMap.fiberSym`: the unordered fibre `u_* (f^* y)` as a
  point of `Sym Z (degree f)`.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.mem_fiberSym`: its points are the images of the
  points of the fibre.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.contMDiff_fiberSym`: it is holomorphic.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.continuous_fiberSym`: it is continuous for
  continuous `u`.

## References

* Robert Lipshitz, *A cylindrical reformulation of Heegaard Floer homology*, Geometry & Topology
  10 (2006), §13, proof of Proposition 13.2 (the map to the symmetric product obtained from the
  fibres of the branched cover).
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §8 (symmetric functions of the values along the fibres of a branched covering).
-/

public noncomputable section

open Filter Function IsManifold Set Topology

open scoped Manifold ContDiff

namespace TauCeti.RiemannSurface

variable {X Y Z : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [T2Space X] [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
  [T2Space Y] [PreconnectedSpace Y]

namespace FiniteHolomorphicMap

variable (f : FiniteHolomorphicMap X Y) (u : X → Z)

/-- **The unordered fibre of a finite holomorphic map, pushed forward along `u`.** For a finite
holomorphic map `f : X → Y` from a compact Riemann surface to a connected one, and `u : X → Z`,
the unordered `degree f`-tuple of the images under `u` of the points of the fibre of `f` over `y`,
each repeated according to the local multiplicity of `f` there. -/
def fiberSym (y : Y) : Sym Z (degree f) :=
  ⟨(fiberMultiset f y).map u, by rw [Multiset.card_map, f.card_fiberMultiset]⟩

/-- The unordered fibre over `y`, as a multiset, is the image under `u` of the fibre multiset. -/
@[simp]
theorem coe_fiberSym (y : Y) : (f.fiberSym u y : Multiset Z) = (fiberMultiset f y).map u :=
  (rfl)

/-- The points of the unordered fibre over `y` are the images under `u` of the points of the fibre
of `f` over `y`. -/
@[simp]
theorem mem_fiberSym {y : Y} {z : Z} : z ∈ f.fiberSym u y ↔ ∃ x, f x = y ∧ u x = z := by
  rw [← Sym.mem_coe, coe_fiberSym, Multiset.mem_map]
  simp [mem_fiberMultiset (f.finite_fiber y), localMultiplicity_pos f]

/-- Pushing the unordered fibres forward along `u` and then along `v` is pushing them forward along
`v ∘ u`. -/
theorem fiberSym_comp {W : Type*} (v : Z → W) (y : Y) :
    f.fiberSym (v ∘ u) y = Sym.map v (f.fiberSym u y) :=
  Sym.coe_injective <| by simp [Multiset.map_map]

/-! ### Holomorphy in elementary-symmetric charts

Fix a finite family of pairwise disjoint open coordinate patches `V i` of `Z`, with charts `φ i`
defined on them, such that every point of the tuple over `y₀` lies in one of them. -/

section Chart

variable [TopologicalSpace Z] {ι : Type*} [Fintype ι] {V : ι → Set Z} [∀ i, DecidablePred (· ∈ V i)]
  {y₀ : Y}

omit [Fintype ι] [∀ i, DecidablePred (· ∈ V i)] in
/-- Since `f` is a closed map, the tuples over points near `y₀` stay in the patches. -/
private theorem eventually_forall_mem_fiberSym {u : X → Z} (hu : Continuous u)
    (hVo : ∀ i, IsOpen (V i)) (hy₀ : ∀ a ∈ f.fiberSym u y₀, ∃ i, a ∈ V i) :
    ∀ᶠ y in 𝓝 y₀, ∀ a ∈ f.fiberSym u y, ∃ i, a ∈ V i := by
  have hU : IsOpen (u ⁻¹' ⋃ i, V i) := (isOpen_iUnion hVo).preimage hu
  have hfy₀ : y₀ ∉ f '' (u ⁻¹' ⋃ i, V i)ᶜ := by
    rintro ⟨x, hx, rfl⟩
    exact hx (mem_iUnion.2 (hy₀ (u x) ((f.mem_fiberSym u).2 ⟨x, rfl, rfl⟩)))
  filter_upwards [((f.holomorphic.continuous.isClosedMap _ hU.isClosed_compl).isOpen_compl
    ).mem_nhds hfy₀] with y hy a ha
  obtain ⟨x, rfl, rfl⟩ := (f.mem_fiberSym u).1 ha
  by_contra h
  exact hy ⟨x, fun hx ↦ h (mem_iUnion.1 hx), rfl⟩

variable [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) 1 Z] {φ : ι → OpenPartialHomeomorph Z ℂ}

omit [IsManifold 𝓘(ℂ) 1 X] [Fintype ι] [CompactSpace X] [T2Space X] in
/-- The `j`-th power of the `i`-th patch coordinate of `u`, extended by zero off the patch, is
holomorphic near every point mapped into one of the patches, since the patches are disjoint and
open. -/
private theorem eventually_mdifferentiableAt_patchPow {u : X → Z}
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (hVo : ∀ i, IsOpen (V i)) (hφ : ∀ i, φ i ∈ atlas ℂ Z)
    (hVsub : ∀ i, V i ⊆ (φ i).source) (hVdisj : Pairwise (Function.onFun Disjoint V)) {x : X}
    (hx : ∃ k, u x ∈ V k) (i : ι) (j : ℕ) :
    ∀ᶠ x' in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun x ↦ if u x ∈ V i then φ i (u x) ^ j else 0) x' := by
  obtain ⟨k, hk⟩ := hx
  have hO : IsOpen (u ⁻¹' V k) := (hVo k).preimage hu.continuous
  filter_upwards [hO.mem_nhds hk] with x' hx'
  by_cases hik : i = k
  · subst hik
    refine ((mdifferentiableAt_atlas (hφ i) (hVsub i hx')).comp x' (hu x')).pow j
      |>.congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds hx'] with x'' (hx'' : u x'' ∈ V i)
    simp [hx'']
  · refine (mdifferentiableAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds hx'] with x'' (hx'' : u x'' ∈ V k)
    have hx''i : u x'' ∉ V i := fun h ↦ Set.disjoint_left.1 (hVdisj hik) h hx''
    simp [hx''i]

omit [Fintype ι] in
/-- Read in the chart at `y₀`, the power sums of the `i`-th patch coordinates of the points of the
tuple over `y` are holomorphic, branch values included. -/
private theorem analyticAt_sum_map_pow_filter_fiberSym {u : X → Z}
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (hVo : ∀ i, IsOpen (V i)) (hφ : ∀ i, φ i ∈ atlas ℂ Z)
    (hVsub : ∀ i, V i ⊆ (φ i).source) (hVdisj : Pairwise (Function.onFun Disjoint V))
    (hy₀ : ∀ a ∈ f.fiberSym u y₀, ∃ i, a ∈ V i) (i : ι) (j : ℕ) :
    AnalyticAt ℂ (fun z ↦ (((f.fiberSym u ((chartAt ℂ y₀).symm z) : Multiset Z).filter
      (· ∈ V i)).map fun a ↦ φ i a ^ j).sum) (chartAt ℂ y₀ y₀) := by
  -- Each sum is the sum along the fibre of the extended patch power.
  have hsum (y : Y) : (((f.fiberSym u y : Multiset Z).filter (· ∈ V i)).map fun a ↦ φ i a ^ j).sum =
      ((fiberMultiset f y).map fun x ↦ if u x ∈ V i then φ i (u x) ^ j else 0).sum := by
    rw [coe_fiberSym, Multiset.filter_map, Multiset.map_map]
    induction fiberMultiset f y using Multiset.induction_on with
    | empty => simp
    | cons a M ih => by_cases ha : u a ∈ V i <;> simpa [ha] using ih
  simp only [hsum]
  exact analyticAt_sum_map_fiberMultiset f.holomorphic f.not_eventuallyConst
    (chart_mem_maximalAtlas y₀) (mem_chart_source ℂ y₀) fun x hx ↦
      eventually_mdifferentiableAt_patchPow hu hVo hφ hVsub hVdisj
        (hy₀ (u x) ((f.mem_fiberSym u).2 ⟨x, hx, rfl⟩)) i j

omit [Fintype ι] in
/-- The number of points of the tuple over `y` in each patch is the same for `y` near `y₀`: it is
the zeroth power sum, so it is continuous, and it is a natural number. -/
private theorem eventually_card_filter_fiberSym_eq {u : X → Z}
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (hVo : ∀ i, IsOpen (V i)) (hφ : ∀ i, φ i ∈ atlas ℂ Z)
    (hVsub : ∀ i, V i ⊆ (φ i).source) (hVdisj : Pairwise (Function.onFun Disjoint V))
    (hy₀ : ∀ a ∈ f.fiberSym u y₀, ∃ i, a ∈ V i) (i : ι) :
    ∀ᶠ y in 𝓝 y₀, Multiset.card ((f.fiberSym u y : Multiset Z).filter (· ∈ V i)) =
      Multiset.card ((f.fiberSym u y₀ : Multiset Z).filter (· ∈ V i)) := by
  have h := (analyticAt_sum_map_pow_filter_fiberSym f hu hVo hφ hVsub hVdisj hy₀ i 0
    ).continuousAt.eventually (Metric.ball_mem_nhds _ one_pos)
  filter_upwards [((chartAt ℂ y₀).continuousAt (mem_chart_source ℂ y₀)).eventually h,
    (chartAt ℂ y₀).open_source.mem_nhds (mem_chart_source ℂ y₀)] with y hy hy'
  refine Nat.cast_injective (R := ℤ) (eq_of_dist_intCast_lt_one ?_)
  simpa [(chartAt ℂ y₀).left_inv hy', (chartAt ℂ y₀).left_inv (mem_chart_source ℂ y₀)] using hy

end Chart

/-- **The unordered fibres of a finite holomorphic map form a holomorphic map to the symmetric
power.** For a finite holomorphic map `f : X → Y` from a compact Riemann surface to a connected one
and a holomorphic map `u : X → Z` to a Hausdorff Riemann surface, `y ↦ u_* (f^* y)` is a
holomorphic map from `Y` to `Sym Z (degree f)` with its elementary-symmetric charts, branch values
of `f` included. -/
theorem contMDiff_fiberSym [TopologicalSpace Z] [T2Space Z] [ChartedSpace ℂ Z]
    [IsManifold 𝓘(ℂ) 1 Z] {u : X → Z} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) :
    letI := symChartedSpace (K := ℂ) (α := Z) (n := degree f)
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin (degree f) → ℂ) ω (f.fiberSym u) := by
  classical
  let := symChartedSpace (K := ℂ) (α := Z) (n := degree f)
  intro y₀
  set F := f.fiberSym u
  -- The chosen chart `C` at the tuple over `y₀` is built from disjoint coordinate patches `V i`.
  obtain ⟨V, m, hm, hVo, hVsub, hVdisj, e, hp, hC⟩ := symChartAt_spec (K := ℂ) (F y₀)
  set C := symChartAt (K := ℂ) (F y₀)
  have hφ (i : ↥(symChartSupport (F y₀))) : chartAt ℂ (i : Z) ∈ atlas ℂ Z := chart_mem_atlas ℂ _
  have hsrc (s) : s ∈ C.source ↔ s ∈ range (Sym.sumSubtype V m hm) := by
    rw [hC, symOpenPartialHomeomorph_source]
  obtain ⟨hy₀, hcard₀⟩ :=
    (Sym.mem_range_sumSubtype hVdisj hm).1 ((hsrc _).1 (mem_symChartAt_source (F y₀)))
  -- Near `y₀`, the tuple over `y` stays in the source of `C`.
  have hmem : ∀ᶠ y in 𝓝 y₀, F y ∈ C.source := by
    filter_upwards [eventually_forall_mem_fiberSym f hu.continuous hVo hy₀,
      eventually_all.2 fun i ↦ eventually_card_filter_fiberSym_eq f hu hVo hφ hVsub hVdisj hy₀ i]
      with y hy hy'
    exact (hsrc _).2 <|
      (Sym.mem_range_sumSubtype hVdisj hm).2 ⟨hy, fun i ↦ (hy' i).trans (hcard₀ i)⟩
  -- There its coordinates are elementary symmetric functions of the patch coordinates.
  have hy₀e : y₀ ∈ (chartAt ℂ y₀).source := mem_chart_source ℂ y₀
  set P : ↥(symChartSupport (F y₀)) → ℂ → Multiset ℂ :=
    fun i z ↦ ((F ((chartAt ℂ y₀).symm z) : Multiset Z).filter (· ∈ V i)).map (chartAt ℂ (i : Z))
  set G : ℂ → Fin (degree f) → ℂ := fun z j ↦
    (-1) ^ (m (e.symm j).1 - (e.symm j).2) *
      (P (e.symm j).1 z).esymm (m (e.symm j).1 - (e.symm j).2)
  have hG : AnalyticAt ℂ G (chartAt ℂ y₀ y₀) := AnalyticAt.pi fun j ↦ analyticAt_const.mul <|
    analyticAt_esymm_of_forall_analyticAt_sum_map_pow _ fun k _ _ ↦ by
      simpa [P, F, Multiset.map_map, Function.comp_def] using
        analyticAt_sum_map_pow_filter_fiberSym f hu hVo hφ hVsub hVdisj hy₀ _ k
  have hCG (z : ℂ) (hz : F ((chartAt ℂ y₀).symm z) ∈ C.source) :
      C (F ((chartAt ℂ y₀).symm z)) = G z := by
    obtain ⟨q, hq⟩ := (hsrc _).1 hz
    rw [hC, ← hq, symOpenPartialHomeomorph_apply]
    funext j
    rw [piSigmaConstHomeomorph_apply, Sym.coeffEquiv_apply]
    simp only [G, P, ← hq, Sym.filter_mem_sumSubtype hVdisj, Sym.coe_map, Multiset.map_map,
      Function.comp_def]
  -- So near `y₀` the map reads as `G` in the charts at `y₀` and at the tuple over it.
  have hFG : ∀ᶠ y in 𝓝 y₀, C (F y) = G (chartAt ℂ y₀ y) := by
    filter_upwards [hmem, (chartAt ℂ y₀).open_source.mem_nhds hy₀e] with y hy hy'
    rw [← hCG (chartAt ℂ y₀ y) (by rwa [(chartAt ℂ y₀).left_inv hy']),
      (chartAt ℂ y₀).left_inv hy']
  have hcont : ContinuousAt F y₀ :=
    (C.continuousAt_iff_continuousAt_comp_left hmem).2 <|
      (hG.continuousAt.comp ((chartAt ℂ y₀).continuousAt hy₀e)).congr (hFG.mono fun _ h ↦ h.symm)
  refine contMDiffAt_of_eventually_chartAt_apply_eq hcont hG.contDiffAt ?_
  rw [symChartedSpace_chartAt]
  exact hFG

/-- **The unordered fibres of a finite holomorphic map vary continuously.** For a finite
holomorphic map `f : X → Y` from a compact Riemann surface to a connected one and a continuous map
`u : X → Z`, the map `y ↦ u_* (f^* y)` from `Y` to `Sym Z (degree f)` is continuous. -/
theorem continuous_fiberSym [TopologicalSpace Z] {u : X → Z} (hu : Continuous u) :
    Continuous (f.fiberSym u) := by
  let := symChartedSpace (K := ℂ) (α := X) (n := degree f)
  have h : f.fiberSym u = Sym.map u ∘ f.fiberSym id := funext (f.fiberSym_comp id u)
  rw [h]
  exact (Sym.continuous_map hu).comp (f.contMDiff_fiberSym mdifferentiable_id).continuous

end FiniteHolomorphicMap

end TauCeti.RiemannSurface
