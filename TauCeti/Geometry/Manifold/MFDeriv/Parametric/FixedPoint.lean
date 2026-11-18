/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Geometry.Manifold.Boundary.Basic

/-!
# Continuation of nondegenerate fixed points in families

Let `f : N → M → M` be a family of self-maps of a manifold `M`, parametrized by a manifold `N`
and jointly `C^n` at `(p₀, x₀)`, `n ≥ 1`, and let `x₀` be a nondegenerate fixed point of `f p₀`
(`TauCeti.IsNondegenerateFixedPt`): `1` is not an eigenvalue of its differential. Then the fixed
point persists. For parameters `p` near `p₀` the map `f p` has a fixed point `g p` near `x₀`,
which is the only fixed point of `f p` near `x₀`, depends `C^n` on `p` at `p₀` and is again
nondegenerate (`TauCeti.IsNondegenerateFixedPt.exists_contMDiffAt_fixedPt_continuation`).
More generally every fixed point `x` of `f p` with `(p, x)` close to `(p₀, x₀)` is nondegenerate
(`TauCeti.IsNondegenerateFixedPt.eventually_isNondegenerateFixedPt_of_isFixedPt`).

This is the implicit function theorem applied to the equation `f p x = x`. In the extended charts
`ψ` at `p₀` and `φ` at `x₀` it reads `G (a, z) = 0` for
`G (a, z) = φ (f (ψ⁻¹ a) (φ⁻¹ z)) - z`. The partial derivative of `G` in `z` at
`(ψ p₀, φ x₀)` is `df_{x₀} - 1` read in the chart, which is invertible because `x₀` is
nondegenerate and the model space of `M` is finite dimensional. So Mathlib's `C^n` implicit
function theorem `ContDiffAt.implicitFunction` solves for `z` as a function of `a`. The partial
derivative stays invertible near the base point, since `G` is `C¹` there and invertible operators
form an open set, and this gives the nondegeneracy of the nearby fixed points.

Families of this kind arise as the return maps of a periodic orbit of a family of vector fields,
and as the time-one maps of a family of time-dependent Hamiltonians. Once such a family is known
to depend smoothly on the parameter, these results continue its nondegenerate periodic orbits
under perturbation. Both manifolds are boundaryless; the parameter manifold may be modelled on any
Banach space.

## Main results

* `TauCeti.IsNondegenerateFixedPt.eventually_isNondegenerateFixedPt_of_isFixedPt`: fixed points
  of nearby maps, close to a nondegenerate fixed point, are nondegenerate.
* `TauCeti.IsNondegenerateFixedPt.exists_contMDiffAt_fixedPt_continuation`: a nondegenerate
  fixed point continues to a unique, `C^n`, nondegenerate branch of fixed points of nearby maps.

This is the fixed-point counterpart of the continuation of nondegenerate critical points,
`TauCeti.IsManifoldNondegenerateCriticalPoint.exists_contMDiffAt_criticalPoint_continuation`.

## References

* J. Palis, W. de Melo, *Geometric Theory of Dynamical Systems*, Springer 1982, Chapter 2
  (hyperbolic fixed points persist under perturbation, by the implicit function theorem).
* V. Guillemin, A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 1, §6
  (stability of transverse intersections), and Chapter 3, §4 (nondegenerate fixed points as
  transverse intersections of the graph with the diagonal).
-/

public section

open Filter Function Set
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {𝕜 E F H G M N : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω} {f : N → M → M} {p₀ : N} {x₀ : M}

/-- The fixed-point equation `f p x = x` read in the extended charts at `p₀` and `x₀`. -/
private noncomputable def fixedPtCoord (f : N → M → M) (p₀ : N) (x₀ : M) : F × E → E :=
  fun a ↦ extChartAt I x₀ (f ((extChartAt J p₀).symm a.1) ((extChartAt I x₀).symm a.2)) - a.2

/-- The fixed-point equation in coordinates is `C^n` at the base point. -/
private theorem contDiffAt_fixedPtCoord [BoundarylessManifold I M] [BoundarylessManifold J N]
    (hf : ContMDiffAt (J.prod I) I n (uncurry f) (p₀, x₀)) (hx : f p₀ x₀ = x₀) :
    ContDiffAt 𝕜 n (fixedPtCoord (I := I) (J := J) f p₀ x₀)
      (extChartAt J p₀ p₀, extChartAt I x₀ x₀) := by
  have h := (contMDiffAt_iff.1 hf).2
  simp only [uncurry_apply_pair, hx, extChartAt_prod, ModelWithCorners.range_prod,
    PartialEquiv.prod_coe] at h
  have hmem : range J ×ˢ range I ∈ 𝓝 (extChartAt J p₀ p₀, extChartAt I x₀ x₀) :=
    prod_mem_nhds (range_mem_nhds_isInteriorPoint BoundarylessManifold.isInteriorPoint)
      (range_mem_nhds_isInteriorPoint BoundarylessManifold.isInteriorPoint)
  exact (h.contDiffAt hmem).sub contDiffAt_snd

/-- On the parameter chart, the fixed-point equation in coordinates is the coordinate expression
of `f p` minus the identity. -/
private theorem fixedPtCoord_extChartAt {p : N} (hp : p ∈ (extChartAt J p₀).source) (z : E) :
    fixedPtCoord (I := I) (J := J) f p₀ x₀ (extChartAt J p₀ p, z) =
      extChartAt I x₀ (f p ((extChartAt I x₀).symm z)) - z := by
  simp only [fixedPtCoord]
  rw [(extChartAt J p₀).left_inv hp]

/-- Inside the charts, `x` is a fixed point of `f p` exactly when its coordinates solve the
fixed-point equation in coordinates. -/
private theorem isFixedPt_iff_fixedPtCoord_eq_zero {p : N} {x : M}
    (hp : p ∈ (extChartAt J p₀).source) (hx : x ∈ (extChartAt I x₀).source)
    (hfx : f p x ∈ (extChartAt I x₀).source) :
    IsFixedPt (f p) x ↔
      fixedPtCoord (I := I) (J := J) f p₀ x₀ (extChartAt J p₀ p, extChartAt I x₀ x) = 0 := by
  rw [fixedPtCoord_extChartAt hp, (extChartAt I x₀).left_inv hx, sub_eq_zero]
  exact ⟨fun h ↦ by rw [h.eq], fun h ↦ (extChartAt I x₀).injOn hfx hx h⟩

variable [FiniteDimensional 𝕜 E] [BoundarylessManifold I M] [BoundarylessManifold J N]

/-- At a nondegenerate fixed point, the partial derivative of the fixed-point equation in
coordinates in the point variable is invertible: it is the chart derivative of `f p₀` at `x₀`
minus the identity. -/
private theorem isInvertible_fderiv_fixedPtCoord_comp_inr (hn : n ≠ 0)
    (hf : ContMDiffAt (J.prod I) I n (uncurry f) (p₀, x₀))
    (h : IsNondegenerateFixedPt I (f p₀) x₀) :
    (fderiv 𝕜 (fixedPtCoord (I := I) (J := J) f p₀ x₀)
        (extChartAt J p₀ p₀, extChartAt I x₀ x₀) ∘L
      ContinuousLinearMap.inr 𝕜 F E).IsInvertible := by
  have hx : f p₀ x₀ = x₀ := h.isFixedPt
  have hG := (contDiffAt_fixedPtCoord hf hx).differentiableAt hn
  have h1 : HasFDerivAt
      (fun z ↦ fixedPtCoord (I := I) (J := J) f p₀ x₀ (extChartAt J p₀ p₀, z))
      (fderiv 𝕜 (fixedPtCoord (I := I) (J := J) f p₀ x₀)
        (extChartAt J p₀ p₀, extChartAt I x₀ x₀) ∘L ContinuousLinearMap.inr 𝕜 F E)
      (extChartAt I x₀ x₀) :=
    hG.hasFDerivAt.comp _ (hasFDerivAt_prodMk_right _ _)
  -- The same partial map is the chart expression of `f p₀` minus the identity.
  set D : E →L[𝕜] E := mfderiv I I (f p₀) x₀
  have h2 : HasFDerivAt
      (fun z ↦ fixedPtCoord (I := I) (J := J) f p₀ x₀ (extChartAt J p₀ p₀, z))
      (D - ContinuousLinearMap.id 𝕜 E) (extChartAt I x₀ x₀) := by
    have hφ : extChartAt I (f p₀ x₀) = extChartAt I x₀ := by rw [hx]
    have hD := h.mdifferentiableAt.hasMFDerivAt.2
    simp only [writtenInExtChartAt, hφ] at hD
    refine ((hD.hasFDerivAt (range_mem_nhds_isInteriorPoint
      BoundarylessManifold.isInteriorPoint)).sub (hasFDerivAt_id _)).congr_of_eventuallyEq
      (Eventually.of_forall fun z ↦ fixedPtCoord_extChartAt (mem_extChartAt_source p₀) z)
  rw [h1.unique h2]
  have hinj : Injective (D - ContinuousLinearMap.id 𝕜 E) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact h.eq_zero_of_mfderiv_apply_eq (sub_eq_zero.1 hv)
  exact ⟨(LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv, by ext; simp⟩

/-- **Nondegenerate fixed points persist.** Let `f : N → M → M` be a family of self-maps of a
boundaryless manifold modelled on a finite-dimensional space, parametrized by a boundaryless
manifold and jointly `C^n`, `n ≥ 1`, at `(p₀, x₀)`. If `x₀` is a nondegenerate fixed point of
`f p₀`, then every fixed point `x` of `f p` with `(p, x)` close to `(p₀, x₀)` is a nondegenerate
fixed point of `f p`. -/
theorem IsNondegenerateFixedPt.eventually_isNondegenerateFixedPt_of_isFixedPt [IsManifold I n M]
    [IsManifold J n N] (hn : n ≠ 0)
    (hf : ContMDiffAt (J.prod I) I n (uncurry f) (p₀, x₀))
    (h : IsNondegenerateFixedPt I (f p₀) x₀) :
    ∀ᶠ q in 𝓝 (p₀, x₀), IsFixedPt (f q.1) q.2 → IsNondegenerateFixedPt I (f q.1) q.2 := by
  have : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
  have h1 : (1 : ℕ∞ω) ≤ n := ENat.one_le_iff_ne_zero_withTop.2 hn
  have : IsManifold I 1 M := IsManifold.of_le h1
  have : IsManifold J 1 N := IsManifold.of_le h1
  have hx : f p₀ x₀ = x₀ := h.isFixedPt
  -- The equation in coordinates is `C¹` near the base point, with continuous derivative `G'`.
  obtain ⟨G', U, hU, hG'c, hG'⟩ :=
    contDiffAt_one_iff.1 ((contDiffAt_fixedPtCoord hf hx).of_le h1)
  -- Its partial derivative in the point variable stays invertible near the base point.
  have hinv : ∀ᶠ v in 𝓝 (extChartAt J p₀ p₀, extChartAt I x₀ x₀),
      (G' v ∘L ContinuousLinearMap.inr 𝕜 F E).IsInvertible := by
    have hcont : ContinuousAt (fun v ↦ G' v ∘L ContinuousLinearMap.inr 𝕜 F E)
        (extChartAt J p₀ p₀, extChartAt I x₀ x₀) :=
      ((ContinuousLinearMap.compL 𝕜 E (F × E) E).flip
        (ContinuousLinearMap.inr 𝕜 F E)).continuous.continuousAt.comp (hG'c.continuousAt hU)
    have hu := (hG' _ (mem_of_mem_nhds hU)).fderiv
    have hinv₀ : (G' (extChartAt J p₀ p₀, extChartAt I x₀ x₀) ∘L
        ContinuousLinearMap.inr 𝕜 F E).IsInvertible :=
      hu ▸ isInvertible_fderiv_fixedPtCoord_comp_inr hn hf h
    exact hcont.eventually hinv₀.eventually_nhds
  have htend : Tendsto (fun q : N × M ↦ (extChartAt J p₀ q.1, extChartAt I x₀ q.2))
      (𝓝 (p₀, x₀)) (𝓝 (extChartAt J p₀ p₀, extChartAt I x₀ x₀)) :=
    (((continuousAt_extChartAt p₀).comp (x := (p₀, x₀)) continuousAt_fst).prodMk
      ((continuousAt_extChartAt x₀).comp (x := (p₀, x₀)) continuousAt_snd)).tendsto
  have hC1 : ∀ᶠ q in 𝓝 (p₀, x₀), ContMDiffAt (J.prod I) I 1 (uncurry f) q :=
    (contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 (hf.of_le h1)
  have hsrcN : ∀ᶠ q : N × M in 𝓝 (p₀, x₀), q.1 ∈ (extChartAt J p₀).source :=
    continuousAt_fst.preimage_mem_nhds (extChartAt_source_mem_nhds p₀)
  have hsrcM : ∀ᶠ q : N × M in 𝓝 (p₀, x₀), q.2 ∈ (extChartAt I x₀).source :=
    continuousAt_snd.preimage_mem_nhds (extChartAt_source_mem_nhds x₀)
  filter_upwards [htend.eventually hinv,
    htend.eventually hU, hC1, hsrcN, hsrcM]
    with q hqinv hqU hqC1 hqN hqM hfix
  have hmd : MDifferentiableAt I I (f q.1) q.2 :=
    (hqC1.mdifferentiableAt one_ne_zero).comp (f := fun x : M ↦ (q.1, x)) q.2
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  -- The chart expression of `f q.1` has derivative `G' v ∘ inr + 1` at the point.
  have hB : HasFDerivAt (fun z ↦ extChartAt I x₀ (f q.1 ((extChartAt I x₀).symm z)))
      (G' (extChartAt J p₀ q.1, extChartAt I x₀ q.2) ∘L ContinuousLinearMap.inr 𝕜 F E +
        ContinuousLinearMap.id 𝕜 E) (extChartAt I x₀ q.2) := by
    refine (((hG' _ hqU).comp _ (hasFDerivAt_prodMk_right _ _)).add
      (hasFDerivAt_id _)).congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_)
    simp only [Pi.add_apply, Function.comp_apply, id_eq]
    rw [fixedPtCoord_extChartAt hqN, sub_add_cancel]
  refine (isNondegenerateFixedPt_iff_injective_sub_id_of_hasFDerivWithinAt hfix hmd hqM
    hB.hasFDerivWithinAt).2 ?_
  obtain ⟨e, he⟩ := hqinv
  rw [add_sub_cancel_right, ← he]
  exact e.injective

/-- **Continuation of a nondegenerate fixed point.** Let `f : N → M → M` be a family of
self-maps of a boundaryless manifold modelled on a finite-dimensional space, parametrized by a
boundaryless manifold and jointly `C^n`, `n ≥ 1`, at `(p₀, x₀)`, and let `x₀` be a nondegenerate
fixed point of `f p₀`. Then there is a map `g` from the parameters to `M`, `C^n` at `p₀` with
`g p₀ = x₀`, such that for `p` near `p₀` the point `g p` is a nondegenerate fixed point of `f p`,
and for `(p, x)` near `(p₀, x₀)` the point `x` is a fixed point of `f p` exactly when `x = g p`. -/
theorem IsNondegenerateFixedPt.exists_contMDiffAt_fixedPt_continuation [CompleteSpace F]
    [IsManifold I n M] [IsManifold J n N] (hn : n ≠ 0)
    (hf : ContMDiffAt (J.prod I) I n (uncurry f) (p₀, x₀))
    (h : IsNondegenerateFixedPt I (f p₀) x₀) :
    ∃ g : N → M, g p₀ = x₀ ∧ ContMDiffAt J I n g p₀ ∧
      (∀ᶠ p in 𝓝 p₀, IsNondegenerateFixedPt I (f p) (g p)) ∧
      ∀ᶠ q in 𝓝 (p₀, x₀), IsFixedPt (f q.1) q.2 ↔ g q.1 = q.2 := by
  have : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
  have hx : f p₀ x₀ = x₀ := h.isFixedPt
  have hGc := contDiffAt_fixedPtCoord hf hx
  have hinv := isInvertible_fderiv_fixedPtCoord_comp_inr hn hf h
  set k := hGc.implicitFunction hn hinv
  have hk₀ : k (extChartAt J p₀ p₀) = extChartAt I x₀ x₀ :=
    hGc.implicitFunction_apply_self hn hinv
  have hkc : ContDiffAt 𝕜 n k (extChartAt J p₀ p₀) := hGc.contDiffAt_implicitFunction hn hinv
  have hG₀ : fixedPtCoord (I := I) (J := J) f p₀ x₀
      (extChartAt J p₀ p₀, extChartAt I x₀ x₀) = 0 := by
    rw [fixedPtCoord_extChartAt (mem_extChartAt_source p₀), extChartAt_to_inv, hx, sub_self]
  obtain ⟨g, hg⟩ : ∃ g : N → M, ∀ p, g p = (extChartAt I x₀).symm (k (extChartAt J p₀ p)) :=
    ⟨_, fun _ ↦ rfl⟩
  have hg₀ : g p₀ = x₀ := by rw [hg, hk₀, extChartAt_to_inv]
  have hgc : ContMDiffAt J I n g p₀ := by
    rw [funext hg]
    have hsymm : ContMDiffAt 𝓘(𝕜, E) I n (extChartAt I x₀).symm (k (extChartAt J p₀ p₀)) := by
      rw [hk₀]
      exact (contMDiffOn_extChartAt_symm x₀).contMDiffAt
        (TauCeti.ModelWithCorners.extChartAt_target_mem_nhds_of_isInteriorPoint hn x₀
          (mem_extChartAt_source x₀) BoundarylessManifold.isInteriorPoint)
    exact hsymm.comp p₀ (hkc.contMDiffAt.comp p₀ contMDiffAt_extChartAt)
  have htend : Tendsto (fun q : N × M ↦ (extChartAt J p₀ q.1, extChartAt I x₀ q.2))
      (𝓝 (p₀, x₀)) (𝓝 (extChartAt J p₀ p₀, extChartAt I x₀ x₀)) :=
    (((continuousAt_extChartAt p₀).comp (x := (p₀, x₀)) continuousAt_fst).prodMk
      ((continuousAt_extChartAt x₀).comp (x := (p₀, x₀)) continuousAt_snd)).tendsto
  -- Uniqueness: a nearby fixed point solves the equation in coordinates, so it lies on the
  -- implicit function.
  have huniq : ∀ᶠ q in 𝓝 (p₀, x₀), IsFixedPt (f q.1) q.2 → q.2 = g q.1 := by
    filter_upwards [htend.eventually
        (hGc.eventually_apply_eq_iff_implicitFunction hn hinv),
      continuousAt_fst.preimage_mem_nhds (extChartAt_source_mem_nhds (I := J) p₀),
      continuousAt_snd.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) x₀)]
      with q hq hqN hqM hfix
    have hfq : f q.1 q.2 ∈ (extChartAt I x₀).source := by
      rw [hfix.eq]
      exact hqM
    have hzero := (isFixedPt_iff_fixedPtCoord_eq_zero hqN hqM hfq).1 hfix
    have hkq : k (extChartAt J p₀ q.1) = extChartAt I x₀ q.2 := hq.1 (hzero.trans hG₀.symm)
    rw [hg, hkq, (extChartAt I x₀).left_inv hqM]
  -- Existence: on the implicit function the equation holds, so `g p` is a fixed point.
  have hpair : Tendsto (fun p ↦ (p, g p)) (𝓝 p₀) (𝓝 (p₀, x₀)) := by
    simpa [hg₀] using (continuousAt_id.prodMk hgc.continuousAt).tendsto
  have hfix : ∀ᶠ p in 𝓝 p₀, IsFixedPt (f p) (g p) := by
    have hkt : ∀ᶠ p in 𝓝 p₀, k (extChartAt J p₀ p) ∈ (extChartAt I x₀).target := by
      refine (hkc.continuousAt.comp (continuousAt_extChartAt p₀)).preimage_mem_nhds ?_
      rw [Function.comp_apply, hk₀]
      exact TauCeti.ModelWithCorners.extChartAt_target_mem_nhds_of_isInteriorPoint hn x₀
        (mem_extChartAt_source x₀) BoundarylessManifold.isInteriorPoint
    have hfsrc : ∀ᶠ p in 𝓝 p₀, f p (g p) ∈ (extChartAt I x₀).source := by
      refine hpair.eventually (hf.continuousAt.preimage_mem_nhds ?_)
      rw [uncurry_apply_pair, hx]
      exact extChartAt_source_mem_nhds x₀
    filter_upwards [(continuousAt_extChartAt p₀).tendsto.eventually
      (hGc.eventually_apply_implicitFunction hn hinv),
      extChartAt_source_mem_nhds (I := J) p₀, hkt, hfsrc] with p hp hpN hpt hpf
    have hgp : g p ∈ (extChartAt I x₀).source := hg p ▸ (extChartAt I x₀).map_target hpt
    rw [isFixedPt_iff_fixedPtCoord_eq_zero hpN hgp hpf, hg, (extChartAt I x₀).right_inv hpt,
      hp, hG₀]
  refine ⟨g, hg₀, hgc, ?_, ?_⟩
  · filter_upwards [hfix, hpair.eventually
      (h.eventually_isNondegenerateFixedPt_of_isFixedPt hn hf)] with p hp hnd
    exact hnd hp
  · filter_upwards [huniq, continuousAt_fst.tendsto.eventually hfix] with q hq hq'
    exact ⟨fun hfx ↦ (hq hfx).symm, fun hgq ↦ hgq ▸ hq'⟩

end TauCeti
