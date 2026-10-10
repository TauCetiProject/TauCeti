/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.Slope
public import TauCeti.Topology.MetricSpace.CATZero

/-!
# Geodesic convexity of energies

Let `φ : X → EReal` be an energy on a metric space and `m : ℝ`. The energy is *`m`-convex along*
a curve `γ` on `[0, 1]` if for every `t ∈ [0, 1]`

`φ (γ t) ≤ (1 - t) φ (γ 0) + t φ (γ 1) - (m / 2) t (1 - t) d(γ 0, γ 1)²`.

It is *`m`-geodesically convex* if any two points of finite energy are joined by a geodesic segment
along which it is `m`-convex, and *`m`-convex along geodesics* if it is `m`-convex along every
geodesic segment joining two points of finite energy. The parameter `m` may be negative, and the
two notions agree in a uniquely geodesic space. On the Wasserstein space `P_p(X)` these are the
weak and the strong forms of displacement convexity. Geodesic convexity is the basic structural
hypothesis of the theory of gradient flows in metric spaces of Ambrosio–Gigli–Savaré; under it the
descending slope, which drives curves of maximal slope, takes the global form below.

The convention for `m` is the one of Mathlib's `StrongConvexOn`: an `m`-strongly convex function
on a real normed space is `m`-geodesically convex (`StrongConvexOn.geodesicallyConvex`). In a
CAT(0) space the squared distance from a point is `2`-convex along geodesics
(`TauCeti.convexAlongGeodesics_dist_sq`).

The main result identifies the descending slope of a geodesically convex energy with a supremum
over all points rather than a limit at `x`:

`|∂φ|(x) = sup_y ((φ x - φ y) / d(x, y) + (m / 2) d(x, y))⁺`

at every point of finite energy (`TauCeti.GeodesicallyConvex.descendingSlope_eq_iSup`). The
supremum is written as `(φ x - φ y + (m / 2) d(x, y)²)⁺ / d(x, y)`; its term at `y = x` is `0`.
The inequality `≤` holds for every energy (`TauCeti.descendingSlope_le_iSup`); geodesic convexity
gives `≥`, by comparing `φ` with its convexity bound near `x` along a geodesic towards `y`. As a
supremum of lower semicontinuous functions, the descending slope of a lower semicontinuous
geodesically convex energy is lower semicontinuous on the set of points of finite energy
(`TauCeti.GeodesicallyConvex.lowerSemicontinuousOn_descendingSlope`).

## Main definitions

* `TauCeti.ConvexAlong m φ γ`: `φ` is `m`-convex along the curve `γ`.
* `TauCeti.GeodesicallyConvex m φ`: any two points of finite energy are joined by a geodesic
  segment along which `φ` is `m`-convex.
* `TauCeti.ConvexAlongGeodesics m φ`: `φ` is `m`-convex along every geodesic segment joining two
  points of finite energy.

## Main results

* `TauCeti.ConvexAlongGeodesics.geodesicallyConvex`: in a geodesic space, convexity along every
  geodesic implies geodesic convexity.
* `TauCeti.GeodesicallyConvex.descendingSlope_eq_iSup`: the descending slope of an
  `m`-geodesically convex energy is its global slope.
* `TauCeti.GeodesicallyConvex.lowerSemicontinuousOn_descendingSlope`: the descending slope of a
  lower semicontinuous `m`-geodesically convex energy is lower semicontinuous on its effective
  domain.

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

variable {X : Type*} [PseudoMetricSpace X] {m m' : ℝ} {φ : X → EReal} {γ : ℝ → X} {x y : X}

/-- The energy `φ` is *`m`-convex along* the curve `γ`, read on `[0, 1]`: for every `t ∈ [0, 1]`,
`φ (γ t) ≤ (1 - t) φ (γ 0) + t φ (γ 1) - (m / 2) t (1 - t) d(γ 0, γ 1)²`. -/
def ConvexAlong (m : ℝ) (φ : X → EReal) (γ : ℝ → X) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, φ (γ t) ≤ ((1 - t : ℝ) : EReal) * φ (γ 0) + (t : EReal) * φ (γ 1) -
    ((m / 2 * t * (1 - t) * dist (γ 0) (γ 1) ^ 2 : ℝ) : EReal)

/-- Convexity along a geodesic segment from `x` to `y`, in terms of its endpoints. -/
theorem IsGeodesicSegment.convexAlong_iff (hγ : IsGeodesicSegment γ x y) :
    ConvexAlong m φ γ ↔ ∀ t ∈ Icc (0 : ℝ) 1, φ (γ t) ≤ ((1 - t : ℝ) : EReal) * φ x +
      (t : EReal) * φ y - ((m / 2 * t * (1 - t) * dist x y ^ 2 : ℝ) : EReal) := by
  rw [ConvexAlong, hγ.source, hγ.target]

/-- Convexity along a curve with a parameter `m` implies it for every smaller parameter. -/
theorem ConvexAlong.mono (h : ConvexAlong m φ γ) (hm : m' ≤ m) : ConvexAlong m' φ γ :=
  fun t ht ↦ (h t ht).trans <| EReal.sub_le_sub le_rfl <| EReal.coe_le_coe_iff.2 <| by
    have : 0 ≤ t * (1 - t) * dist (γ 0) (γ 1) ^ 2 :=
      mul_nonneg (mul_nonneg ht.1 (sub_nonneg.2 ht.2)) (sq_nonneg _)
    nlinarith

/-- The energy `φ` is *`m`-geodesically convex*: any two points of finite energy are joined by a
geodesic segment along which `φ` is `m`-convex. -/
def GeodesicallyConvex (m : ℝ) (φ : X → EReal) : Prop :=
  ∀ ⦃x y : X⦄, φ x ≠ ⊤ → φ y ≠ ⊤ → ∃ γ : ℝ → X, IsGeodesicSegment γ x y ∧ ConvexAlong m φ γ

/-- The energy `φ` is *`m`-convex along geodesics*: it is `m`-convex along every geodesic segment
joining two points of finite energy. -/
def ConvexAlongGeodesics (m : ℝ) (φ : X → EReal) : Prop :=
  ∀ ⦃x y : X⦄, φ x ≠ ⊤ → φ y ≠ ⊤ → ∀ ⦃γ : ℝ → X⦄, IsGeodesicSegment γ x y → ConvexAlong m φ γ

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

end PseudoMetricSpace

/-- An `m`-strongly convex function on a real normed space is `m`-geodesically convex: it is
`m`-convex along the affine segments. -/
theorem _root_.StrongConvexOn.geodesicallyConvex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {m : ℝ} {f : E → ℝ} (hf : StrongConvexOn univ m f) :
    GeodesicallyConvex m fun x ↦ (f x : EReal) := by
  intro x y _ _
  refine ⟨AffineMap.lineMap x y, isGeodesicSegment_lineMap x y, ?_⟩
  rw [(isGeodesicSegment_lineMap x y).convexAlong_iff]
  intro t ht
  have h := hf.2 (mem_univ x) (mem_univ y) (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t)
  simp only [smul_eq_mul] at h
  have : f (AffineMap.lineMap x y t) ≤
      (1 - t) * f x + t * f y - m / 2 * t * (1 - t) * dist x y ^ 2 := by
    rw [AffineMap.lineMap_apply_module, dist_eq_norm]
    linarith
  exact_mod_cast this

section MetricSpace

variable {X : Type*} [MetricSpace X] {m : ℝ} {φ : X → EReal} {x : X}

/-- The descending slope of any energy is at most its global slope
`sup_y (φ x - φ y + (m / 2) d(x, y)²)⁺ / d(x, y)`, for every `m`: near `x` the correction
`(m / 2) d(x, y)` vanishes. -/
theorem descendingSlope_le_iSup (m : ℝ) (φ : X → EReal) (x : X) :
    descendingSlope φ x ≤
      ⨆ y, (φ x - φ y + ((m / 2 * dist x y ^ 2 : ℝ) : EReal)).toENNReal / edist x y := by
  set S := ⨆ y, (φ x - φ y + ((m / 2 * dist x y ^ 2 : ℝ) : EReal)).toENNReal / edist x y
  set K := ENNReal.ofReal (-m / 2)
  have key (ε : ℝ) (hε : 0 < ε) : descendingSlope φ x ≤ S + K * ENNReal.ofReal ε := by
    refine descendingSlope_le_of_eventually_le ?_
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds x hε), self_mem_nhdsWithin]
      with y (hy : dist y x < ε) (hyx : y ≠ x)
    have hd0 : edist x y ≠ 0 := (edist_pos.2 hyx.symm).ne'
    have hS : (φ x - φ y + ((m / 2 * dist x y ^ 2 : ℝ) : EReal)).toENNReal ≤ S * edist x y := by
      refine (ENNReal.div_mul_cancel hd0 (edist_ne_top x y)).symm.trans_le ?_
      gcongr
      exact le_iSup (fun y ↦
        (φ x - φ y + ((m / 2 * dist x y ^ 2 : ℝ) : EReal)).toENNReal / edist x y) y
    have hK : ENNReal.ofReal (-(m / 2 * dist x y ^ 2)) ≤ K * ENNReal.ofReal ε * edist x y := by
      rw [show -(m / 2 * dist x y ^ 2) = -m / 2 * dist x y ^ 2 by ring,
        ENNReal.ofReal_mul' (sq_nonneg _), ENNReal.ofReal_pow dist_nonneg, edist_dist, sq,
        mul_assoc]
      gcongr
      rw [dist_comm] at hy
      exact hy.le
    -- Adding the real term `c = (m / 2) d(x, y)²` and removing it again costs at most `(-c)⁺`.
    calc (φ x - φ y).toENNReal
        = (φ x - φ y + ((m / 2 * dist x y ^ 2 : ℝ) : EReal) +
            ((-(m / 2 * dist x y ^ 2) : ℝ) : EReal)).toENNReal := by
          rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
      _ ≤ (φ x - φ y + ((m / 2 * dist x y ^ 2 : ℝ) : EReal)).toENNReal +
            ENNReal.ofReal (-(m / 2 * dist x y ^ 2)) := by
          rw [← EReal.real_coe_toENNReal]
          exact EReal.toENNReal_add_le
      _ ≤ S * edist x y + K * ENNReal.ofReal ε * edist x y := add_le_add hS hK
      _ = (S + K * ENNReal.ofReal ε) * edist x y := (add_mul _ _ _).symm
  have hlim : Tendsto (fun ε : ℝ ↦ S + K * ENNReal.ofReal ε) (𝓝[>] 0) (𝓝 S) := by
    have h0 : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal ε) (𝓝[>] 0) (𝓝 0) := by
      simpa using (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.add (ENNReal.Tendsto.const_mul h0 (Or.inr ENNReal.ofReal_ne_top))
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall key)

/-- **Lower bound for the slope of a geodesically convex energy.** At a point `x` of finite energy
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
  rw [hγ.convexAlong_iff] at hconv
  have hd : 0 < dist x y := dist_pos.2 hyx.symm
  have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  have hedist {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
      edist x (γ t) = ENNReal.ofReal (t * dist x y) := by
    rw [edist_dist, hγ.dist_source_apply ⟨ht.1.le, ht.2.le⟩]
  set r := (φ x).toReal
  have hr : φ x = r := (EReal.coe_toReal hx hxb).symm
  rcases eq_or_ne (φ y) ⊥ with hyb | hyb
  · -- If `φ y = ⊥`, then `φ = ⊥` along the geodesic and the slope at `x` is infinite.
    refine le_top.trans <| le_descendingSlope_of_tendsto (hγ.tendsto_nhdsGT_zero hd)
      tendsto_const_nhds ?_
    filter_upwards [hmem] with t ht
    have h := hconv t ⟨ht.1.le, ht.2.le⟩
    rw [hyb, EReal.coe_mul_bot_of_pos ht.1, EReal.add_bot, EReal.bot_sub, le_bot_iff] at h
    rw [h, hr, EReal.sub_bot (EReal.coe_ne_bot r), EReal.toENNReal_top, hedist ht,
      ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
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
        rw [hedist ht]
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

/-- **The slope of a geodesically convex energy is its global slope.** If `φ` is `m`-geodesically
convex and `φ x` is finite, then
`|∂φ|(x) = sup_y (φ x - φ y + (m / 2) d(x, y)²)⁺ / d(x, y)`,
that is, `|∂φ|(x) = sup_{y ≠ x} ((φ x - φ y) / d(x, y) + (m / 2) d(x, y))⁺`. -/
theorem GeodesicallyConvex.descendingSlope_eq_iSup (hφ : GeodesicallyConvex m φ) (hx : φ x ≠ ⊤) :
    descendingSlope φ x =
      ⨆ y, (φ x - φ y + ((m / 2 * dist x y ^ 2 : ℝ) : EReal)).toENNReal / edist x y :=
  le_antisymm (descendingSlope_le_iSup m φ x) (iSup_le (hφ.le_descendingSlope hx))

/-- **The slope of a lower semicontinuous geodesically convex energy is lower semicontinuous** on
the set of points of finite energy, being a supremum of lower semicontinuous functions there. -/
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
  have hev : ∀ᶠ x in 𝓝[{x | φ x ≠ ⊤}] x₀, φ x ≠ ⊤ ∧ x ≠ y :=
    eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds (eventually_ne_nhds hyx.symm))
  set r := (φ x₀).toReal
  have hr : φ x₀ = r := (EReal.coe_toReal hx₀ hxb).symm
  rcases eq_or_ne (φ y) ⊥ with hyb | hyb
  · -- If `φ y = ⊥`, the term at `y` is infinite at every point near `x₀` where `φ ≠ ⊥`.
    have hM : M < ⊤ := hyM.trans_le le_top
    filter_upwards [hev, hlsc x₀ hx₀ ⊥ (bot_lt_iff_ne_bot.2 hxb)]
      with x ⟨hx, hxy⟩ hxb'
    refine hM.trans_le <| le_trans ?_ (hφ.le_descendingSlope hx y)
    rw [hyb, EReal.sub_bot hxb'.ne', EReal.top_add_coe, EReal.toENNReal_top,
      ENNReal.top_div_of_ne_top (edist_ne_top x y)]
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

end MetricSpace

end TauCeti
