/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Along
public import TauCeti.Analysis.GradientFlow.RelaxedSlope
public import TauCeti.Data.EReal.Operations
public import TauCeti.Topology.MetricSpace.CATZero

import TauCeti.Analysis.Convex.Function.Along

/-!
# Geodesic convexity of energies

Let `φ : X → EReal` be an energy on a metric space and `m : ℝ`. The predicate
`TauCeti.ConvexAlong m φ γ` expresses `m`-convexity along a fixed curve `γ` on `[0, 1]`.
Its stability properties are developed in `TauCeti.Analysis.Convex.Along`.

The energy is *`m`-geodesically convex* if any two points of its effective domain `{x | φ x ≠ ⊤}`
are joined by a geodesic segment along which it is `m`-convex, and *`m`-convex along geodesics* if
it is `m`-convex along every such segment. The effective domain includes points of energy `⊥`.
The parameter `m` may be negative, and the two notions agree in a uniquely geodesic space.
On the Wasserstein space `P_p(X)` these are the weak and the strong forms of displacement
convexity. Geodesic convexity is the basic structural
hypothesis of the theory of gradient flows in metric spaces of Ambrosio–Gigli–Savaré; under it the
descending slope, which drives curves of maximal slope, takes the global form below.

The convention for `m` is the one of Mathlib's `StrongConvexOn`: an `m`-strongly convex function
on a real normed space is `m`-geodesically convex (`StrongConvexOn.geodesicallyConvex`). In a
CAT(0) space the squared distance from a point is `2`-convex along geodesics
(`TauCeti.convexAlongGeodesics_dist_sq`).

The main result identifies the descending slope of a geodesically convex energy with a supremum
over all points rather than a limit at `x`:

`|∂φ|(x) = sup_y ((φ x - φ y) / d(x, y) + (m / 2) d(x, y))⁺`

at every point `x` with `φ x ≠ ⊤` (`TauCeti.GeodesicallyConvex.descendingSlope_eq_iSup`). The
supremum is written as `(φ x - φ y + (m / 2) d(x, y)²)⁺ / d(x, y)`; its term at `y = x` is `0`.
The inequality `≤` holds for every energy (`TauCeti.descendingSlope_le_iSup`); geodesic convexity
gives `≥`, by comparing `φ` with its convexity bound near `x` along a geodesic towards `y`. As a
supremum of lower semicontinuous functions, the descending slope of a lower semicontinuous
geodesically convex energy is lower semicontinuous on its effective domain `{x | φ x ≠ ⊤}`
(`TauCeti.GeodesicallyConvex.lowerSemicontinuousOn_descendingSlope`), so it is also the relaxed
slope there (`TauCeti.GeodesicallyConvex.relaxedSlope_eq_descendingSlope`).

Convexity along every geodesic inherits the stability properties of `TauCeti.ConvexAlong` and
restricts to every piece of a geodesic. Geodesic convexity, which provides some geodesic for each
pair of points, is stable under positive multiples and under adding an energy that is convex
along every geodesic. Two geodesically convex energies may have different witnessing geodesics.
The sum results for both notions assume that the energies never take the value `⊥`, so the
effective domain of a sum is the intersection of the effective domains.

## Main definitions

* `TauCeti.GeodesicallyConvex m φ`: any two points with energy `≠ ⊤` are joined by a geodesic
  segment along which `φ` is `m`-convex.
* `TauCeti.ConvexAlongGeodesics m φ`: `φ` is `m`-convex along every geodesic segment joining two
  points with energy `≠ ⊤`.

## Main results

* `TauCeti.ConvexAlongGeodesics.geodesicallyConvex`: in a geodesic space, convexity along every
  geodesic implies geodesic convexity.
* `TauCeti.ConvexAlongGeodesics.add`, `TauCeti.ConvexAlongGeodesics.const_mul`,
  `TauCeti.ConvexAlongGeodesics.iSup` and `TauCeti.ConvexAlongGeodesics.of_tendsto`: convexity
  along geodesics is stable under sums, nonnegative multiples, suprema and pointwise limits.
* `TauCeti.ConvexAlongGeodesics.convexAlong_comp_lineMap`: convexity along geodesics restricts to
  pieces of geodesics.
* `TauCeti.GeodesicallyConvex.add_convexAlongGeodesics` and
  `TauCeti.GeodesicallyConvex.const_mul`: geodesic convexity is stable under adding an energy
  convex along geodesics and under positive multiples.
* `TauCeti.GeodesicallyConvex.descendingSlope_eq_iSup`: the descending slope of an
  `m`-geodesically convex energy is its global slope.
* `TauCeti.GeodesicallyConvex.lowerSemicontinuousOn_descendingSlope`: the descending slope of a
  lower semicontinuous `m`-geodesically convex energy is lower semicontinuous on its effective
  domain.
* `TauCeti.GeodesicallyConvex.relaxedSlope_eq_descendingSlope`: for such an energy the relaxed
  and the descending slopes agree on the effective domain.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 2, Section 2.4, Theorem 2.4.9 and
  Corollary 2.4.10.
-/

public section

open Filter Set Topology
open scoped ENNReal

namespace TauCeti

section PseudoMetricSpace

variable {X : Type*} [PseudoMetricSpace X] {m m' : ℝ} {φ ψ : X → EReal} {γ : ℝ → X} {x y : X}

/-- Convexity along a geodesic segment from `x` to `y`, in terms of its endpoints. -/
theorem IsGeodesicSegment.convexAlong_iff (hγ : IsGeodesicSegment γ x y) :
    ConvexAlong m φ γ ↔ ∀ t ∈ Icc (0 : ℝ) 1, φ (γ t) ≤ ((1 - t : ℝ) : EReal) * φ x +
      (t : EReal) * φ y - ((m / 2 * t * (1 - t) * dist x y ^ 2 : ℝ) : EReal) := by
  rw [convexAlong_def, hγ.source, hγ.target]

/-- The energy `φ` is *`m`-geodesically convex*: any two points of its effective domain, that is
with `φ x ≠ ⊤` (energy `⊥` is allowed), are joined by a geodesic segment along which `φ` is
`m`-convex. -/
def GeodesicallyConvex (m : ℝ) (φ : X → EReal) : Prop :=
  ∀ ⦃x y : X⦄, φ x ≠ ⊤ → φ y ≠ ⊤ → ∃ γ : ℝ → X, IsGeodesicSegment γ x y ∧ ConvexAlong m φ γ

/-- The energy `φ` is *`m`-convex along geodesics*: it is `m`-convex along every geodesic segment
joining two points of its effective domain, that is with `φ x ≠ ⊤` (energy `⊥` is allowed). -/
def ConvexAlongGeodesics (m : ℝ) (φ : X → EReal) : Prop :=
  ∀ ⦃x y : X⦄, φ x ≠ ⊤ → φ y ≠ ⊤ → ∀ ⦃γ : ℝ → X⦄, IsGeodesicSegment γ x y → ConvexAlong m φ γ

/-- The defining condition of geodesic convexity. -/
theorem geodesicallyConvex_def :
    GeodesicallyConvex m φ ↔ ∀ ⦃x y : X⦄, φ x ≠ ⊤ → φ y ≠ ⊤ →
      ∃ γ : ℝ → X, IsGeodesicSegment γ x y ∧ ConvexAlong m φ γ :=
  Iff.rfl

/-- The defining condition of convexity along geodesics. -/
theorem convexAlongGeodesics_def :
    ConvexAlongGeodesics m φ ↔ ∀ ⦃x y : X⦄, φ x ≠ ⊤ → φ y ≠ ⊤ →
      ∀ ⦃γ : ℝ → X⦄, IsGeodesicSegment γ x y → ConvexAlong m φ γ :=
  Iff.rfl

/-- Geodesic convexity with a parameter `m` implies it for every smaller parameter. -/
theorem GeodesicallyConvex.mono (h : GeodesicallyConvex m φ) (hm : m' ≤ m) :
    GeodesicallyConvex m' φ := fun _ _ hx hy ↦
  (h hx hy).imp fun _ hγ ↦ ⟨hγ.1, hγ.2.mono hm⟩

/-- Convexity along geodesics with a parameter `m` implies it for every smaller parameter. -/
theorem ConvexAlongGeodesics.mono (h : ConvexAlongGeodesics m φ) (hm : m' ≤ m) :
    ConvexAlongGeodesics m' φ := fun _ _ hx hy _ hγ ↦ (h hx hy hγ).mono hm

/-- In a geodesic space, an energy that is `m`-convex along every geodesic segment is
`m`-geodesically convex. -/
theorem ConvexAlongGeodesics.geodesicallyConvex [IsGeodesicSpace X]
    (h : ConvexAlongGeodesics m φ) : GeodesicallyConvex m φ := fun x y hx hy ↦
  (IsGeodesicSpace.exists_isGeodesicSegment x y).imp fun _ hγ ↦ ⟨hγ, h hx hy hγ⟩

/-- In a CAT(0) space the squared distance from a point is `2`-convex along geodesics: this is the
CAT(0) comparison inequality `d(γ t, z)² ≤ (1 - t) d(x, z)² + t d(y, z)² - t (1 - t) d(x, y)²`. -/
theorem convexAlongGeodesics_dist_sq [IsCATZeroSpace X] (z : X) :
    ConvexAlongGeodesics 2 fun x ↦ ((dist x z ^ 2 : ℝ) : EReal) := by
  intro x y _ _ γ hγ
  rw [hγ.convexAlong_iff]
  intro t ht
  have h := hγ.dist_sq_le z ht
  simp only [dist_comm z] at h
  have : dist (γ t) z ^ 2 ≤
      (1 - t) * dist x z ^ 2 + t * dist y z ^ 2 - 2 / 2 * t * (1 - t) * dist x y ^ 2 := by
    linarith
  exact_mod_cast this

/-! ### Endpoints, restriction and stability -/

/-- **Restriction to a piece of a geodesic.** If `φ` is `m`-convex along geodesics, then along a
geodesic segment `γ` between two points of its effective domain, `φ` is also `m`-convex along the
piece of `γ` between any two times `a, b ∈ [0, 1]`, reparametrised over `[0, 1]`. -/
theorem ConvexAlongGeodesics.convexAlong_comp_lineMap (h : ConvexAlongGeodesics m φ)
    (hγ : IsGeodesicSegment γ x y) (hx : φ x ≠ ⊤) (hy : φ y ≠ ⊤) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    ConvexAlong m φ fun t ↦ γ (AffineMap.lineMap a b t) := by
  have hγφ := h hx hy hγ
  have h₀ : φ (γ 0) ≠ ⊤ := hγ.source ▸ hx
  have h₁ : φ (γ 1) ≠ ⊤ := hγ.target ▸ hy
  exact h (hγφ.apply_ne_top h₀ h₁ ha) (hγφ.apply_ne_top h₀ h₁ hb) (hγ.comp_lineMap ha hb)

/-- **Sum of energies convex along geodesics.** If `φ` is `m`-convex and `ψ` is `m'`-convex along
geodesics, and neither takes the value `⊥`, then `φ + ψ` is `(m + m')`-convex along geodesics. -/
theorem ConvexAlongGeodesics.add (hφ : ConvexAlongGeodesics m φ) (hψ : ConvexAlongGeodesics m' ψ)
    (hφ' : ∀ x, φ x ≠ ⊥) (hψ' : ∀ x, ψ x ≠ ⊥) : ConvexAlongGeodesics (m + m') (φ + ψ) :=
  fun x y hx hy _ hγ ↦
    have hx' := (EReal.add_ne_top_iff_ne_top₂ (hφ' x) (hψ' x)).1 hx
    have hy' := (EReal.add_ne_top_iff_ne_top₂ (hφ' y) (hψ' y)).1 hy
    (hφ hx'.1 hy'.1 hγ).add (hψ hx'.2 hy'.2 hγ)

/-- **Adding an energy convex along geodesics.** If `φ` is `m`-geodesically convex and `ψ` is
`m'`-convex along geodesics, and neither takes the value `⊥`, then `φ + ψ` is
`(m + m')`-geodesically convex, along the geodesics that witness the convexity of `φ`. -/
theorem GeodesicallyConvex.add_convexAlongGeodesics (hφ : GeodesicallyConvex m φ)
    (hψ : ConvexAlongGeodesics m' ψ) (hφ' : ∀ x, φ x ≠ ⊥) (hψ' : ∀ x, ψ x ≠ ⊥) :
    GeodesicallyConvex (m + m') (φ + ψ) := fun x y hx hy ↦
  have hx' := (EReal.add_ne_top_iff_ne_top₂ (hφ' x) (hψ' x)).1 hx
  have hy' := (EReal.add_ne_top_iff_ne_top₂ (hφ' y) (hψ' y)).1 hy
  (hφ hx'.1 hy'.1).imp fun _ hγ ↦ ⟨hγ.1, hγ.2.add (hψ hx'.2 hy'.2 hγ.1)⟩

/-- **Positive multiple of a geodesically convex energy.** If `φ` is `m`-geodesically convex and
`c > 0`, then `c φ` is `(c m)`-geodesically convex. -/
theorem GeodesicallyConvex.const_mul (h : GeodesicallyConvex m φ) {c : ℝ} (hc : 0 < c) :
    GeodesicallyConvex (c * m) fun x ↦ (c : EReal) * φ x := fun _ _ hx hy ↦
  (h (EReal.ne_top_of_coe_mul_ne_top hc hx) (EReal.ne_top_of_coe_mul_ne_top hc hy)).imp
    fun _ hγ ↦ ⟨hγ.1, hγ.2.const_mul hc.le⟩

/-- **Nonnegative multiple of an energy convex along geodesics.** If `φ` is `m`-convex along
geodesics and `c ≥ 0`, then `c φ` is `(c m)`-convex along geodesics. For `c = 0` this is the zero
energy, which is convex along every curve. -/
theorem ConvexAlongGeodesics.const_mul (h : ConvexAlongGeodesics m φ) {c : ℝ} (hc : 0 ≤ c) :
    ConvexAlongGeodesics (c * m) fun x ↦ (c : EReal) * φ x := by
  rcases hc.eq_or_lt with rfl | hc
  · intro _ _ _ _ γ _
    simpa only [zero_mul, EReal.coe_zero] using (convexAlong_zero (γ := γ))
  exact fun _ _ hx hy _ hγ ↦
    (h (EReal.ne_top_of_coe_mul_ne_top hc hx) (EReal.ne_top_of_coe_mul_ne_top hc hy) hγ).const_mul
      hc.le

/-- **Supremum of energies convex along geodesics.** The pointwise supremum of a family of
energies, each `m`-convex along geodesics, is `m`-convex along geodesics. -/
theorem ConvexAlongGeodesics.iSup {ι : Sort*} {φs : ι → X → EReal}
    (h : ∀ i, ConvexAlongGeodesics m (φs i)) : ConvexAlongGeodesics m (⨆ i, φs i) :=
  fun x y hx hy _ hγ ↦ ConvexAlong.iSup fun i ↦
    h i (ne_top_of_le_ne_top hx (by rw [iSup_apply]; exact le_iSup (fun i ↦ φs i x) i))
      (ne_top_of_le_ne_top hy (by rw [iSup_apply]; exact le_iSup (fun i ↦ φs i y) i)) hγ

/-- **Convexity along geodesics passes to pointwise limits.** If the energies `φs i` are eventually
`m`-convex along geodesics and converge pointwise to `φ`, then `φ` is `m`-convex along
geodesics. -/
theorem ConvexAlongGeodesics.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {φs : ι → X → EReal} (h : ∀ᶠ i in l, ConvexAlongGeodesics m (φs i))
    (hφ : ∀ x, Tendsto (fun i ↦ φs i x) l (𝓝 (φ x))) : ConvexAlongGeodesics m φ := by
  intro x y hx hy γ hγ
  -- Near a point of the effective domain of `φ`, the `φs i` are eventually `≠ ⊤` as well.
  have hev {z : X} (hz : φ z ≠ ⊤) : ∀ᶠ i in l, φs i z ≠ ⊤ :=
    ((hφ z).eventually (gt_mem_nhds hz.lt_top)).mono fun _ hi ↦ hi.ne
  refine ConvexAlong.of_tendsto ((h.and ((hev hx).and (hev hy))).mono fun i hi ↦
    hi.1 hi.2.1 hi.2.2 hγ) (fun t _ ↦ hφ (γ t)) ?_ ?_
  · rwa [hγ.source]
  · rwa [hγ.target]

end PseudoMetricSpace

/-- An `m`-strongly convex function on a real normed space is `m`-geodesically convex: it is
`m`-convex along the affine segments. -/
theorem _root_.StrongConvexOn.geodesicallyConvex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {m : ℝ} {f : E → ℝ} (hf : StrongConvexOn univ m f) :
    GeodesicallyConvex m fun x ↦ (f x : EReal) :=
  fun x y _ _ ↦ ⟨AffineMap.lineMap x y, isGeodesicSegment_lineMap x y,
    hf.convexAlong_lineMap (mem_univ x) (mem_univ y)⟩

section MetricSpace

variable {X : Type*} [MetricSpace X] {m : ℝ} {φ : X → EReal} {x : X}

/-- If `φ y = ⊥` at the end of a geodesic segment from `x`, the slope at `x` is infinite. -/
private theorem top_le_descendingSlope_of_eq_bot {γ : ℝ → X} {y : X}
    (hγ : IsGeodesicSegment γ x y) (hconv : ConvexAlong m φ γ) (hd : 0 < dist x y)
    (hx : φ x ≠ ⊤) (hxb : φ x ≠ ⊥) (hyb : φ y = ⊥) : ⊤ ≤ descendingSlope φ x := by
  rw [hγ.convexAlong_iff] at hconv
  have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  have hr : φ x = (φ x).toReal := (EReal.coe_toReal hx hxb).symm
  refine le_descendingSlope_of_tendsto (hγ.tendsto_nhdsGT_zero hd) tendsto_const_nhds ?_
  filter_upwards [hmem] with t ht
  have h := hconv t ⟨ht.1.le, ht.2.le⟩
  rw [hyb, EReal.coe_mul_bot_of_pos ht.1, EReal.add_bot, EReal.bot_sub, le_bot_iff] at h
  rw [h, hr, EReal.sub_bot (EReal.coe_ne_bot _), EReal.toENNReal_top,
    hγ.edist_source_apply ⟨ht.1.le, ht.2.le⟩, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]

/-- The term of the global slope at a finite-valued `y`, at the end of a geodesic segment from `x`,
is at most the descending slope at `x`. -/
private theorem term_le_descendingSlope_of_finite {γ : ℝ → X} {y : X}
    (hγ : IsGeodesicSegment γ x y) (hconv : ConvexAlong m φ γ) (hd : 0 < dist x y)
    (hx : φ x ≠ ⊤) (hxb : φ x ≠ ⊥) (hy : φ y ≠ ⊤) (hyb : φ y ≠ ⊥) :
    (φ x - φ y + ((m / 2 * dist x y ^ 2 : ℝ) : EReal)).toENNReal / edist x y ≤
      descendingSlope φ x := by
  rw [hγ.convexAlong_iff] at hconv
  have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  set r := (φ x).toReal
  have hr : φ x = r := (EReal.coe_toReal hx hxb).symm
  set s := (φ y).toReal
  have hs : φ y = s := (EReal.coe_toReal hy hyb).symm
  -- Along the geodesic, the rate of decrease at time `t` is at least
  -- `(r - s + (m / 2) (1 - t) d(x, y)²) / d(x, y)`.
  have hf : Tendsto (fun t : ℝ ↦ ENNReal.ofReal ((r - s + m / 2 * (1 - t) * dist x y ^ 2) /
      dist x y)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal ((r - s + m / 2 * (1 - 0) * dist x y ^ 2) /
        dist x y))) :=
    ((ENNReal.continuous_ofReal.comp (by fun_prop)).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [sub_zero, mul_one] at hf
  rw [hr, hs, ← EReal.coe_sub, ← EReal.coe_add, EReal.real_coe_toENNReal, edist_dist,
    ← ENNReal.ofReal_div_of_pos hd]
  refine le_descendingSlope_of_tendsto (hγ.tendsto_nhdsGT_zero hd) hf ?_
  filter_upwards [hmem] with t ht
  have hu : φ (γ t) ≤ (((1 - t) * r + t * s - m / 2 * t * (1 - t) * dist x y ^ 2 : ℝ) : EReal) := by
    have h := hconv t ⟨ht.1.le, ht.2.le⟩
    rw [hr, hs] at h
    exact_mod_cast h
  calc ENNReal.ofReal ((r - s + m / 2 * (1 - t) * dist x y ^ 2) / dist x y)
      = ENNReal.ofReal (t * (r - s + m / 2 * (1 - t) * dist x y ^ 2)) /
          ENNReal.ofReal (t * dist x y) := by
        rw [← ENNReal.ofReal_div_of_pos (mul_pos ht.1 hd), mul_div_mul_left _ _ ht.1.ne']
    _ ≤ (φ x - φ (γ t)).toENNReal / edist x (γ t) := by
        rw [hγ.edist_source_apply ⟨ht.1.le, ht.2.le⟩]
        refine ENNReal.div_le_div_right ?_ _
        rw [hr]
        calc ENNReal.ofReal (t * (r - s + m / 2 * (1 - t) * dist x y ^ 2))
            = ((r : EReal) - (((1 - t) * r + t * s - m / 2 * t * (1 - t) * dist x y ^ 2 : ℝ) :
                EReal)).toENNReal := by
              rw [← EReal.coe_sub, EReal.real_coe_toENNReal]
              congr 1
              ring
          _ ≤ ((r : EReal) - φ (γ t)).toENNReal :=
              EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl hu)

/-- **Lower bound for the slope of a geodesically convex energy.** At a point `x` with `φ x ≠ ⊤`
of an `m`-geodesically convex energy, each term `(φ x - φ y + (m / 2) d(x, y)²)⁺ / d(x, y)` of the
global slope is at most the descending slope. -/
theorem GeodesicallyConvex.le_descendingSlope (hφ : GeodesicallyConvex m φ) (hx : φ x ≠ ⊤)
    (y : X) : (φ x - φ y + ((m / 2 * dist x y ^ 2 : ℝ) : EReal)).toENNReal / edist x y ≤
      descendingSlope φ x := by
  -- If `y = x`, `φ y = ⊤` or `φ x = ⊥`, the left side is `0`. Otherwise compare `φ` near `x`, along
  -- a geodesic from `x` to `y`, with its convexity bound.
  rcases eq_or_ne y x with rfl | hyx
  · rw [dist_self, EReal.toENNReal_of_nonpos (by simpa using EReal.sub_self_le_zero)]
    simp
  rcases eq_or_ne (φ y) ⊤ with hy | hy
  · simp [hy]
  rcases eq_or_ne (φ x) ⊥ with hxb | hxb
  · simp [hxb]
  obtain ⟨γ, hγ, hconv⟩ := hφ hx hy
  have hd : 0 < dist x y := dist_pos.2 hyx.symm
  rcases eq_or_ne (φ y) ⊥ with hyb | hyb
  · exact le_top.trans (top_le_descendingSlope_of_eq_bot hγ hconv hd hx hxb hyb)
  · exact term_le_descendingSlope_of_finite hγ hconv hd hx hxb hy hyb

/-- **The slope of a geodesically convex energy is its global slope.** If `φ` is `m`-geodesically
convex and `φ x ≠ ⊤`, then
`|∂φ|(x) = sup_y (φ x - φ y + (m / 2) d(x, y)²)⁺ / d(x, y)`,
that is, `|∂φ|(x) = sup_{y ≠ x} ((φ x - φ y) / d(x, y) + (m / 2) d(x, y))⁺`. -/
theorem GeodesicallyConvex.descendingSlope_eq_iSup (hφ : GeodesicallyConvex m φ) (hx : φ x ≠ ⊤) :
    descendingSlope φ x =
      ⨆ y, (φ x - φ y + ((m / 2 * dist x y ^ 2 : ℝ) : EReal)).toENNReal / edist x y :=
  le_antisymm (descendingSlope_le_iSup m φ x) (iSup_le (hφ.le_descendingSlope hx))

/-- The finite-valued case of `GeodesicallyConvex.lowerSemicontinuousOn_descendingSlope`: if a term
of the global slope at `x₀` exceeds `M`, then the slope exceeds `M` near `x₀`. -/
private theorem eventually_lt_descendingSlope_of_finite (hφ : GeodesicallyConvex m φ)
    (hlsc : LowerSemicontinuousOn φ {x | φ x ≠ ⊤}) {x₀ y : X} {M : ℝ≥0∞} (hx₀ : φ x₀ ≠ ⊤)
    (hxb : φ x₀ ≠ ⊥) (hy : φ y ≠ ⊤) (hyb : φ y ≠ ⊥) (hd : 0 < dist x₀ y)
    (hyM : M < (φ x₀ - φ y + ((m / 2 * dist x₀ y ^ 2 : ℝ) : EReal)).toENNReal / edist x₀ y) :
    ∀ᶠ x in 𝓝[{x | φ x ≠ ⊤}] x₀, M < descendingSlope φ x := by
  have hev : ∀ᶠ x in 𝓝[{x | φ x ≠ ⊤}] x₀, φ x ≠ ⊤ ∧ x ≠ y :=
    eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds (eventually_ne_nhds (dist_pos.1 hd)))
  set r := (φ x₀).toReal
  have hr : φ x₀ = r := (EReal.coe_toReal hx₀ hxb).symm
  set s := (φ y).toReal
  have hs : φ y = s := (EReal.coe_toReal hy hyb).symm
  rw [hr, hs, ← EReal.coe_sub, ← EReal.coe_add, EReal.real_coe_toENNReal, edist_dist,
    ← ENNReal.ofReal_div_of_pos hd] at hyM
  -- Choose `a` with `M < a < (r - s + (m / 2) d(x₀, y)²) / d(x₀, y)`; the term at `y` stays above
  -- `a` near `x₀`, where `φ x > s - (m / 2) d(x, y)² + a d(x, y)`.
  obtain ⟨a, ha, hMa, haq⟩ := ENNReal.lt_iff_exists_real_btwn.1 hyM
  rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha, lt_div_iff₀ hd] at haq
  set h : X → ℝ := fun x ↦ s - m / 2 * dist x y ^ 2 + a * dist x y
  have hcont : Continuous h := by fun_prop
  have hε : 0 < (r - h x₀) / 2 := by
    simp only [h]
    linarith
  have h₀ : ((r - (r - h x₀) / 2 : ℝ) : EReal) < φ x₀ := by
    rw [hr]
    exact_mod_cast sub_lt_self r hε
  have hφev : ∀ᶠ x in 𝓝[{x | φ x ≠ ⊤}] x₀, ((r - (r - h x₀) / 2 : ℝ) : EReal) < φ x :=
    hlsc x₀ hx₀ _ h₀
  have hhev : ∀ᶠ x in 𝓝 x₀, h x < h x₀ + (r - h x₀) / 2 :=
    hcont.continuousAt.eventually_lt continuousAt_const (lt_add_of_pos_right _ hε)
  filter_upwards [hev, hφev, nhdsWithin_le_nhds hhev]
    with x ⟨hx, hxy⟩ hφx hhx
  refine hMa.trans_le <| le_trans ?_ (hφ.le_descendingSlope hx y)
  have hdx : 0 < dist x y := dist_pos.2 hxy
  have hhx' : ((h x : ℝ) : EReal) ≤ φ x :=
    (EReal.coe_le_coe_iff.2 (by linarith)).trans hφx.le
  rw [hs, edist_dist]
  calc ENNReal.ofReal a = ENNReal.ofReal (a * dist x y) / ENNReal.ofReal (dist x y) := by
        rw [← ENNReal.ofReal_div_of_pos hdx, mul_div_cancel_right₀ _ hdx.ne']
    _ ≤ (φ x - s + ((m / 2 * dist x y ^ 2 : ℝ) : EReal)).toENNReal /
          ENNReal.ofReal (dist x y) := by
        refine ENNReal.div_le_div_right ?_ _
        calc ENNReal.ofReal (a * dist x y)
            = ((h x : EReal) - s + ((m / 2 * dist x y ^ 2 : ℝ) : EReal)).toENNReal := by
              rw [← EReal.coe_sub, ← EReal.coe_add, EReal.real_coe_toENNReal]
              congr 1
              simp only [h]
              ring
          _ ≤ (φ x - s + ((m / 2 * dist x y ^ 2 : ℝ) : EReal)).toENNReal :=
              EReal.toENNReal_le_toENNReal (add_le_add_left (EReal.sub_le_sub hhx' le_rfl) _)

/-- **The slope of a lower semicontinuous geodesically convex energy is lower semicontinuous** on
its effective domain `{x | φ x ≠ ⊤}`, being a supremum of lower semicontinuous functions there. -/
theorem GeodesicallyConvex.lowerSemicontinuousOn_descendingSlope (hφ : GeodesicallyConvex m φ)
    (hlsc : LowerSemicontinuousOn φ {x | φ x ≠ ⊤}) :
    LowerSemicontinuousOn (descendingSlope φ) {x | φ x ≠ ⊤} := by
  -- If `M` is below the slope at `x₀`, it is below one term of the global slope at `x₀`, and that
  -- term stays above `M` near `x₀`; at nearby points it is still at most the slope.
  intro x₀ hx₀ M hM
  have hx₀ : φ x₀ ≠ ⊤ := hx₀
  have hM : M < descendingSlope φ x₀ := hM
  rw [hφ.descendingSlope_eq_iSup hx₀, lt_iSup_iff] at hM
  obtain ⟨y, hyM⟩ := hM
  have hne : (φ x₀ - φ y + ((m / 2 * dist x₀ y ^ 2 : ℝ) : EReal)).toENNReal ≠ 0 := by
    rintro h
    rw [h, ENNReal.zero_div] at hyM
    exact absurd hyM (by simp)
  have hyx : y ≠ x₀ := by
    rintro rfl
    exact hne <| EReal.toENNReal_of_nonpos (by simpa using EReal.sub_self_le_zero)
  have hy : φ y ≠ ⊤ := by
    rintro h
    simp [h] at hne
  have hxb : φ x₀ ≠ ⊥ := by
    rintro h
    simp [h] at hne
  have hd : 0 < dist x₀ y := dist_pos.2 hyx.symm
  rcases eq_or_ne (φ y) ⊥ with hyb | hyb
  · -- If `φ y = ⊥`, the term at `y` is infinite at every point near `x₀` where `φ ≠ ⊥`.
    have hM : M < ⊤ := hyM.trans_le le_top
    filter_upwards [eventually_mem_nhdsWithin, hlsc x₀ hx₀ ⊥ (bot_lt_iff_ne_bot.2 hxb)]
      with x hx hxb'
    refine hM.trans_le <| le_trans ?_ (hφ.le_descendingSlope hx y)
    rw [hyb, EReal.sub_bot hxb'.ne', EReal.top_add_coe, EReal.toENNReal_top,
      ENNReal.top_div_of_ne_top (edist_ne_top x y)]
  exact eventually_lt_descendingSlope_of_finite hφ hlsc hx₀ hxb hy hyb hd hyM

/-- **The relaxed slope of a lower semicontinuous geodesically convex energy is its descending
slope** at every point of its effective domain `{x | φ x ≠ ⊤}`. -/
theorem GeodesicallyConvex.relaxedSlope_eq_descendingSlope (hφ : GeodesicallyConvex m φ)
    (hlsc : LowerSemicontinuousOn φ {x | φ x ≠ ⊤}) (hx : φ x ≠ ⊤) :
    relaxedSlope φ x = descendingSlope φ x :=
  TauCeti.relaxedSlope_eq_descendingSlope hx (hφ.lowerSemicontinuousOn_descendingSlope hlsc x hx)

end MetricSpace

end TauCeti
