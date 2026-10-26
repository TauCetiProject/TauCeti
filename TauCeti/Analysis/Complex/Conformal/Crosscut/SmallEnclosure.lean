/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.ShortCrosscut
public import TauCeti.Topology.UniformlyLocallyConnected
import TauCeti.Analysis.Complex.Conformal.Crosscut.Path
import TauCeti.Analysis.Complex.Conformal.Crosscut.Image
import TauCeti.Topology.Path.Puncture

/-!
# Small enclosing sets through image crosscuts

Let `f` be a conformal map of a disc onto a domain whose frontier is uniformly locally connected.
The length--area method supplies, at every point `ζ` of the source circle, arbitrarily small
circular crosscuts with short images. This file closes such an image crosscut up along the frontier
of the image domain into a small compact set `K` which stays preconnected when any point of the
open image crosscut is removed.

The closed image crosscut is the range of a path `γ` from `u` to `v`, both on the image frontier,
whose interior values are the values of `f` on the crosscut
(`TauCeti.exists_path_range_eq_closure_image_ball_inter_sphere_of_injOn`). The ends `u` and `v` are
close, so uniform local connectedness joins them by a small connected subset `C` of the frontier,
and `K` is `range γ ∪ closure C`. Removing an interior point `γ t` of the crosscut leaves the two
preconnected pieces of the path before and after `t`, one through `u` and one through `v`, and the
connected set `closure C` through both; so `K \ {γ t}` is preconnected by
`Path.isPreconnected_range_union_sdiff_singleton`.

That puncture property is exactly what the enclosure theorem
`TauCeti.image_inter_ball_subset_filledHull_of_diam_lt_of_isPreconnected_sdiff_singleton` needs to
trap the near side of the crosscut inside the filled hull of `K`. No Jordan curve is formed, and
the ends `u` and `v` may coincide; this is what lets Carathéodory's continuity theorem run on any
locally connected boundary rather than on a Jordan curve only.

## Main result

* `TauCeti.exists_isCompact_superset_image_ball_inter_sphere_diam_le` -- below every prescribed
  radius, a short image crosscut lies in an arbitrarily small compact set, contained in the closed
  image crosscut and the image frontier, that stays preconnected when any point of the image
  crosscut is removed.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Theorem 2.1 and Sections 2.2--2.3.
-/

public section

namespace TauCeti

open Bornology Complex MeasureTheory Metric Set

variable {f : ℂ → ℂ} {c ζ : ℂ} {r : ℝ}

/-- **A short image crosscut lies in a small enclosing set.** Let `f` be holomorphic and injective
on `ball c r`, with finite Dirichlet integral and uniformly locally connected image frontier. For
every `ε > 0`, every boundary point `ζ` of the disc, and every radius bound `R > 0`, there is a
genuine circular crosscut of radius `ρ < R` whose image is contained in a compact set `K` with

* `K ⊆ closure (f '' (ball c r ∩ sphere ζ ρ)) ∪ frontier (f '' ball c r)`,
* `K \ {f z}` preconnected for every point `z` of the crosscut, and
* `Metric.diam K ≤ ε`.

The set `K` is the closed image crosscut together with a small connected piece of the image
frontier joining its two ends. -/
theorem exists_isCompact_superset_image_ball_inter_sphere_diam_le
    (hζ : dist ζ c = r) (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) (hdir : ∫⁻ z in ball c r, ‖deriv f z‖ₑ ^ 2 ≠ ⊤)
    (hfrontier : IsUniformlyLocallyConnected (frontier (f '' ball c r))) {ε R : ℝ}
    (hε : 0 < ε) (hR : 0 < R) :
    ∃ ρ ∈ Ioo 0 R, ρ < 2 * r ∧ ∃ K : Set ℂ, IsCompact K ∧
      f '' (ball c r ∩ sphere ζ ρ) ⊆ K ∧
      K ⊆ closure (f '' (ball c r ∩ sphere ζ ρ)) ∪ frontier (f '' ball c r) ∧
      (∀ z ∈ ball c r ∩ sphere ζ ρ, IsPreconnected (K \ {f z})) ∧ diam K ≤ ε := by
  obtain ⟨δ, hδ, hjoin⟩ := hfrontier.exists_isConnected_diam_le (half_pos hε)
  -- one scale `κ` caps the crosscut diameter at half the tolerance and keeps its two ends within
  -- the distance `δ` at which the frontier joins them by a small connected set
  obtain ⟨κ, hκ, hκε, hκδ⟩ : ∃ κ : ℝ, 0 < κ ∧ κ ≤ ε / 2 ∧ κ < δ :=
    ⟨min (ε / 2) (δ / 2), lt_min (by positivity) (by positivity), min_le_left _ _,
      (min_le_right _ _).trans_lt (by linarith)⟩
  obtain ⟨ρ, hρmem, hlenFin, hcross, -⟩ :=
    exists_diam_image_ball_inter_sphere_le_and_circleImageLength_ne_top (ζ := ζ) hf hdir hκ
      (lt_min hR (by linarith : (0 : ℝ) < 2 * r))
  have hρ : ρ ∈ Ioo 0 R := ⟨hρmem.1, hρmem.2.trans_le (min_le_left _ _)⟩
  have hρr : ρ < 2 * r := hρmem.2.trans_le (min_le_right _ _)
  obtain ⟨u, v, γ, hγrange, -, -, hu, hv, hγsimple, -⟩ :=
    exists_path_range_eq_closure_image_ball_inter_sphere_of_injOn hζ hρ.1 hρr hf hinj hlenFin
  have hdiamγ : diam (range γ) ≤ κ := by rwa [hγrange, diam_closure]
  have hγb : IsBounded (range γ) := (isCompact_range γ.continuous).isBounded
  obtain ⟨C, hCs, hCconn, huC, hvC, hCb, hCdiam⟩ :=
    hjoin u hu v hv ((dist_le_diam_of_mem hγb ⟨0, γ.source⟩ ⟨1, γ.target⟩).trans_lt
      (hdiamγ.trans_lt hκδ))
  have hΩ : IsOpen (f '' ball c r) := isOpen_image_of_differentiableOn_of_injOn isOpen_ball hf hinj
  have hCfr : closure C ⊆ frontier (f '' ball c r) := isClosed_frontier.closure_subset_iff.mpr hCs
  refine ⟨ρ, hρ, hρr, range γ ∪ closure C,
    (isCompact_range γ.continuous).union hCb.isCompact_closure,
    (hγrange ▸ subset_closure).trans subset_union_left,
    union_subset (hγrange.le.trans subset_union_left) (hCfr.trans subset_union_right),
    fun z hz => ?_, ?_⟩
  · -- the image of a crosscut point is a value of the path visited only once, and off the frontier
    have hfz : f z ∉ frontier (f '' ball c r) :=
      disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hΩ).symm (mem_image_of_mem f hz.1)
    obtain ⟨t, ht⟩ : f z ∈ range γ := hγrange ▸ subset_closure (mem_image_of_mem f hz)
    rw [← ht] at hfz ⊢
    have ht0 : t ≠ 0 := by rintro rfl; rw [γ.source] at hfz; exact hfz hu
    have ht1 : t ≠ 1 := by rintro rfl; rw [γ.target] at hfz; exact hfz hv
    refine γ.isPreconnected_range_union_sdiff_singleton (fun s hst => ?_)
      hCconn.isPreconnected.closure (subset_closure huC) (subset_closure hvC) fun h => hfz (hCfr h)
    rcases hγsimple hst with h | ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exact absurd h ht1
    · exact absurd h ht0
  · calc diam (range γ ∪ closure C) ≤ diam (range γ) + diam (closure C) :=
          diam_union' ⟨u, ⟨0, γ.source⟩, subset_closure huC⟩
      _ ≤ ε / 2 + ε / 2 := by rw [diam_closure]; exact add_le_add (hdiamγ.trans hκε) hCdiam
      _ = ε := add_halves ε

end TauCeti
