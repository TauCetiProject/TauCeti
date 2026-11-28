/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Chart
public import TauCeti.Geometry.Manifold.SmoothTriangulation.StarImmersion
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.Convex.SecantEstimate
import TauCeti.Analysis.Normed.Group.Pi
import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization
import TauCeti.Geometry.Convex.ConvexSpace.Defs
import TauCeti.Geometry.Manifold.SmoothTriangulation.LocallyFinite

/-!
# The differential of a smooth triangulation is injective on stars

Let `κ : |K| ≃ₜ M` be a smooth triangulation of a manifold modelled on a finite-dimensional real
space `E`: on every closed simplex `κ` is an immersion of the simplex. Read in an extended chart
`φ`, its differential at a point `b` sends a point `x` of a closed simplex containing `b` to the
derivative from the right at `0` of `φ ∘ κ` along the segment from `b` to `x`. This differential is
injective on the whole closed star of `b`, also for points of different simplices
(`TauCeti.IsSmoothTriangulation.eq_of_hasDerivWithinAt_extChartAt`). This is Munkres' Theorem 8.4:
a homeomorphism onto a manifold which is non-degenerate on every closed simplex is an immersion of
the complex. Consequently a smooth triangulation, read in a chart on a subcomplex whose image lies
in the chart source, is a star immersion
(`TauCeti.IsSmoothTriangulation.isStarImmersion_extChartAt_comp_realizationMap`), the form in which
the secant approximation and rectification theorems for star immersions apply to it.

The homeomorphism is essential: the two edges `t ↦ (t, t ^ 2)` and `t ↦ (t, -t ^ 2)` leaving the
origin of the plane form an injective map which is an immersion on each edge, but its differential
at the common vertex identifies the two edges.

## Implementation notes

Let `x` and `y` be points of closed simplices containing `b` along which `φ ∘ κ` has the same right
derivative `u`, and suppose that a barycentric coordinate `i` has `x i < y i`. For small `t > 0`
the points `b + t (x - b)` and `b + t (y - b)` have images within `ε t` of `φ (κ b) + t u`. The
segment between these images lies in the range of the model, which is convex, so in the chart
target; its inverse image in `|K|` is connected, so by the intermediate value theorem it contains
a point `z` with `z i = b i + t l` for any `l` strictly between `x i - b i` and `y i - b i`. Read
in a closed simplex `ρ` containing `z` and `b`, `(z - b) / t` is then a direction `a` of `ρ` with
`a i = l` whose derivative at `b` is within `ε (‖a‖ + 1)` of `u`. As `b` lies in finitely many
simplices, and each has at most one direction with derivative `u`, we may choose `l` to avoid the
`i`-th coordinates of all of these, and a compactness argument excludes such `a` for small `ε`.
Only the convexity of the range of the model is used, so `M` may have boundary or corners.

## Main results

* `TauCeti.IsSmoothTriangulation.eq_of_hasDerivWithinAt_extChartAt`: read in a chart, the
  differential of a smooth triangulation at a point is injective on its closed star.
* `TauCeti.IsSmoothTriangulation.isStarImmersion_extChartAt_comp_realizationMap`: a smooth
  triangulation, read in a chart on a subcomplex whose image lies in the chart source, is a star
  immersion.

## References

* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Chapter II,
  Definitions 8.1–8.3 and Theorem 8.4.
* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
-/

public section

open Set Function Filter Metric Topology AbstractSimplicialComplex TauCeti.SetLike
open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}
  {K : AbstractSimplicialComplex ι}

/-- Let `D` be injective on the directions of the simplex on `ρ`, the vectors with coordinate sum
zero, and let `l` be a value which is not the `i`-th coordinate of a direction `a` with `D a = u`.
For all small `ε > 0`, no direction `a` with `‖D a - u‖ ≤ ε * ‖a‖ + ε` has `i`-th coordinate
`l`. -/
private theorem eventually_forall_apply_ne {ρ : Finset ι} {D : (ρ → ℝ) →L[ℝ] E}
    (hD : ∀ v : ρ → ℝ, ∑ a, v a = 0 → D v = 0 → v = 0) {u : E} (i : ρ) {l : ℝ}
    (hl : ∀ a : ρ → ℝ, ∑ j, a j = 0 → D a = u → a i ≠ l) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a : ρ → ℝ, ∑ j, a j = 0 → ‖D a - u‖ ≤ ε * ‖a‖ + ε → a i ≠ l := by
  obtain ⟨c, hc, hcD⟩ := D.exists_pos_mul_sum_abs_le_norm hD
  set R := 2 * (‖u‖ + 1) / c
  have hR : 0 < R + 1 := by positivity
  -- On the bounded part of the hyperplane `a i = l` of directions, `‖D a - u‖` is bounded below.
  have hK : IsCompact ({a : ρ → ℝ | ∑ j, a j = 0 ∧ a i = l} ∩ closedBall 0 R) :=
    (isCompact_closedBall 0 R).inter_left
      ((isClosed_eq (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const).inter
        (isClosed_eq (continuous_apply i) continuous_const))
  obtain ⟨m, hm, hmK⟩ := hK.exists_forall_le' (f := fun a => ‖D a - u‖)
    (D.continuous.sub continuous_const).norm.continuousOn (a := 0) fun a ha =>
      norm_pos_iff.2 (sub_ne_zero.2 fun h => hl a ha.1.1 h ha.1.2)
  filter_upwards [Ioo_mem_nhdsGT (half_pos hc), Ioo_mem_nhdsGT one_pos,
    Ioo_mem_nhdsGT (div_pos hm hR)] with ε hεc hε1 hεm a ha haε hai
  have hεm' : ε * (R + 1) < m := (lt_div_iff₀ hR).mp hεm.2
  -- Directions whose derivative is close to `u` are bounded.
  have hnorm : ‖a‖ ≤ ∑ j, |a j| := by simpa using Pi.norm_pow_le_sum_norm_pow a one_ne_zero
  have hca : c * ‖a‖ ≤ ‖D a‖ := (mul_le_mul_of_nonneg_left hnorm hc.le).trans (hcD a ha)
  have hDa : ‖D a‖ ≤ ‖u‖ + (ε * ‖a‖ + ε) :=
    calc ‖D a‖ = ‖u + (D a - u)‖ := by rw [add_sub_cancel]
      _ ≤ ‖u‖ + ‖D a - u‖ := norm_add_le _ _
      _ ≤ ‖u‖ + (ε * ‖a‖ + ε) := by gcongr
  have haR : ‖a‖ ≤ R := by
    rw [le_div_iff₀ hc]
    nlinarith [mul_le_mul_of_nonneg_right hεc.2.le (norm_nonneg a), hε1.2]
  have hm' := hmK a ⟨⟨ha, hai⟩, mem_closedBall_zero_iff.2 haR⟩
  nlinarith [mul_le_mul_of_nonneg_left haR hεc.1.le]

/-- Rescaling a first-order estimate. Let `w` and `w₀` be points of the simplex on `ρ`, and suppose
that `F w - F w₀` is within `ε * t` of `t • u` and within `ε * ‖w - w₀‖` of `D (w - w₀)`. Then the
direction `(w - w₀) / t` has derivative within `ε (‖(w - w₀) / t‖ + 1)` of `u`. -/
private theorem sum_smul_sub_eq_zero_and_norm_sub_le {ρ : Finset ι} {F : (ρ → ℝ) → E}
    {D : (ρ → ℝ) →L[ℝ] E} {w w₀ : ρ → ℝ} (hw : ∑ a, w a = 1) (hw₀ : ∑ a, w₀ a = 1) {u : E}
    {t ε : ℝ} (ht : 0 < t) (hF : ‖F w - F w₀ - D (w - w₀)‖ ≤ ε * ‖w - w₀‖)
    (hFt : ‖F w - F w₀ - t • u‖ ≤ ε * t) :
    ∑ a, (t⁻¹ • (w - w₀)) a = 0 ∧ ‖D (t⁻¹ • (w - w₀)) - u‖ ≤ ε * ‖t⁻¹ • (w - w₀)‖ + ε := by
  refine ⟨by simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ← Finset.mul_sum,
    Finset.sum_sub_distrib, hw, hw₀, sub_self, mul_zero], ?_⟩
  have hDv : ‖D (w - w₀) - t • u‖ ≤ ε * ‖w - w₀‖ + ε * t :=
    calc ‖D (w - w₀) - t • u‖ = ‖(F w - F w₀ - t • u) - (F w - F w₀ - D (w - w₀))‖ := by
          congr 1; abel
      _ ≤ ‖F w - F w₀ - t • u‖ + ‖F w - F w₀ - D (w - w₀)‖ := norm_sub_le _ _
      _ ≤ ε * ‖w - w₀‖ + ε * t := by linarith
  have hscale : D (t⁻¹ • (w - w₀)) - u = t⁻¹ • (D (w - w₀) - t • u) := by
    rw [map_smul, smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  rw [hscale, norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le)]
  calc t⁻¹ * ‖D (w - w₀) - t • u‖ ≤ t⁻¹ * (ε * ‖w - w₀‖ + ε * t) :=
        mul_le_mul_of_nonneg_left hDv (inv_nonneg.2 ht.le)
    _ = ε * (t⁻¹ * ‖w - w₀‖) + ε := by field_simp

/-- Near a point `b` of `|K|` lying in finitely many closed simplices, every point lies in the open
star of `b`, and on every closed simplex `ρ` containing `b` a map `F ρ` with a derivative `D ρ`
within the simplex at `b` differs from its first-order approximation at `b` by at most `ε` times
the distance to `b`. -/
private theorem eventually_nhds_norm_sub_sub_le {b : Realization K}
    (hfin : {ρ : Face K | b.val.support ⊆ ρ.val}.Finite)
    {F : ∀ ρ : Face K, b.val.support ⊆ ρ.val → (ρ.val → ℝ) → E}
    {D : ∀ ρ : Face K, b.val.support ⊆ ρ.val → (ρ.val → ℝ) →L[ℝ] E}
    (hFD : ∀ ρ hρ, HasFDerivWithinAt (F ρ hρ) (D ρ hρ)
      (range fun t : Convexity.StdSimplex ℝ ρ.val => ⇑t.weights) (fun a => b.val a))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 b, (∀ v ∈ b.val.support, 0 < z.val v) ∧
      ∀ (ρ : Face K) (hρ : b.val.support ⊆ ρ.val) (w : StandardSimplex ρ.val),
        faceInclusion K ρ w = z →
        ‖F ρ hρ (fun a => w.val a) - F ρ hρ (fun a => b.val a) -
            D ρ hρ ((fun a : ρ.val => w.val a) - fun a : ρ.val => b.val a)‖ ≤
          ε * ‖(fun a : ρ.val => w.val a) - fun a : ρ.val => b.val a‖ := by
  -- On each closed simplex containing `b`, pull the first-order estimate back from the simplex,
  -- which is closed embedded in `|K|`.
  have hρev (ρ : Face K) (hρ : b.val.support ⊆ ρ.val) : ∀ᶠ z in 𝓝 b,
      ∀ (hρ' : b.val.support ⊆ ρ.val) (w : StandardSimplex ρ.val), faceInclusion K ρ w = z →
        ‖F ρ hρ' (fun a => w.val a) - F ρ hρ' (fun a => b.val a) -
            D ρ hρ' ((fun a : ρ.val => w.val a) - fun a : ρ.val => b.val a)‖ ≤
          ε * ‖(fun a : ρ.val => w.val a) - fun a : ρ.val => b.val a‖ := by
    set bρ : StandardSimplex ρ.val := ⟨b.val, Realization.mem_convexHull_of_support_subset K b hρ⟩
    have hind : IsInducing (faceInclusion K ρ) :=
      ((continuous_faceInclusion K ρ).isClosedEmbedding fun w w' hww' => Subtype.ext <| by
        simpa only [faceInclusion_val] using congrArg Subtype.val hww').isInducing
    have hcoords : Continuous fun w : StandardSimplex ρ.val => fun a : ρ.val => w.val a :=
      continuous_pi fun a => (continuous_apply a.val).comp continuous_induced_dom
    have hS (w : StandardSimplex ρ.val) :
        (fun a : ρ.val => w.val a) ∈ range fun t : Convexity.StdSimplex ℝ ρ.val => ⇑t.weights := by
      rw [← Finset.range_standardSimplex_coordinates]
      exact mem_range_self w
    have h := (tendsto_nhdsWithin_iff.2 ⟨hcoords.tendsto bρ, Eventually.of_forall hS⟩).eventually
      ((hFD ρ hρ).isLittleO.bound hε)
    rw [hind.nhds_eq_comap, faceInclusion_mk_val, eventually_comap] at h
    exact h.mono fun z hz _ w hw => hz w hw
  exact ((eventually_all_finset _).2 fun v hv =>
    (((continuous_apply v).comp (continuous_realization_coe K)).tendsto b).eventually
      (lt_mem_nhds (Realization.pos_of_mem_support K b hv))).and
    (((eventually_all_finite hfin).2 hρev).mono fun z hz ρ hρ => hz ρ hρ hρ)

/-- Along the segment from `bσ` to `x` in a closed simplex, along which `φ ∘ κ` has right derivative
`u`, the points at small parameter `t > 0` map into the chart source, within `ε * t` of
`φ (κ bσ) + t • u` and within `r` of `φ (κ bσ)`, where `φ` is an extended chart. -/
private theorem eventually_exists_extChartAt_mem_ball (κ : Realization K ≃ₜ M) (x₀ : M)
    {σ : Face K} {bσ x : StandardSimplex σ.val}
    (hb : κ (faceInclusion K σ bσ) ∈ (extChartAt I x₀).source) {u : E}
    (hx : HasDerivWithinAt (IccExtend zero_le_one
      (extChartAt I x₀ ∘ κ ∘ faceInclusion K σ ∘ StandardSimplex.lineMap bσ x)) u (Icc 0 1) 0)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ p : Realization K, κ p ∈ (extChartAt I x₀).source ∧
      ‖extChartAt I x₀ (κ p) - extChartAt I x₀ (κ (faceInclusion K σ bσ)) - t • u‖ ≤ ε * t ∧
      extChartAt I x₀ (κ p) ∈ ball (extChartAt I x₀ (κ (faceInclusion K σ bσ))) r ∧
      ∀ i, p.val i = bσ.val i + t * (x.val i - bσ.val i) := by
  set P : ℝ → Realization K := fun t =>
    faceInclusion K σ (StandardSimplex.lineMap bσ x (projIcc 0 1 zero_le_one t))
  have hP0 : P 0 = faceInclusion K σ bσ := by simp [P, projIcc_left]
  have hPc : Continuous P := (continuous_faceInclusion K σ).comp
    ((StandardSimplex.continuous_lineMap bσ x).comp continuous_projIcc)
  have hIcc : Icc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    mem_of_superset (Ioo_mem_nhdsGT one_pos) Ioo_subset_Icc_self
  have hxP : HasDerivWithinAt (fun t => extChartAt I x₀ (κ (P t))) u (Ioi 0) 0 := by
    refine (hx.mono_of_mem_nhdsWithin hIcc).congr (fun t _ => ?_) ?_ <;>
      rw [IccExtend_apply] <;> rfl
  have hc := hxP.continuousWithinAt.tendsto
  rw [hP0] at hc
  filter_upwards [hxP.isLittleO.bound hε, self_mem_nhdsWithin, Ioo_mem_nhdsGT one_pos,
    hc.eventually (ball_mem_nhds _ hr), nhdsWithin_le_nhds ((κ.continuous.comp hPc).continuousAt
      |>.preimage_mem_nhds (by
        rw [comp_apply, hP0]; exact (isOpen_extChartAt_source x₀).mem_nhds hb))]
    with t ht ht0 ht1 htr hts
  refine ⟨P t, hts, ?_, htr, fun i => ?_⟩
  · simpa only [hP0, sub_zero, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < t from ht0)] using ht
  · simp only [P, faceInclusion_val, projIcc_of_mem _ (Ioo_subset_Icc_self ht1),
      StandardSimplex.lineMap_apply]
    ring

/-- Let `κ` be a homeomorphism, `b` a point of `|K|` with `κ b` in the source of an extended chart
`φ`, and `x` and `y` points of closed simplices containing `b` along whose segments from `b` the map
`φ ∘ κ` has the same right derivative `u`. Then every neighbourhood `G` of `b` contains, for
`l` between `x i - b i` and `y i - b i`, a point `z` with `z i = b i + t * l` whose image is within
`ε * t` of `φ (κ b) + t • u`, for some `t > 0`. The point `z` lies on the inverse image of a segment
in the model, which is connected. -/
private theorem exists_pos_exists_mem_apply_eq (κ : Realization K ≃ₜ M) (x₀ : M)
    {b : Realization K} (hb : κ b ∈ (extChartAt I x₀).source) {G : Set (Realization K)}
    (hG : G ∈ 𝓝 b) {σ τ : Face K} {bσ x : StandardSimplex σ.val} {bτ y : StandardSimplex τ.val}
    {u : E} (hbσ : faceInclusion K σ bσ = b) (hbτ : faceInclusion K τ bτ = b)
    (hx : HasDerivWithinAt (IccExtend zero_le_one
      (extChartAt I x₀ ∘ κ ∘ faceInclusion K σ ∘ StandardSimplex.lineMap bσ x)) u (Icc 0 1) 0)
    (hy : HasDerivWithinAt (IccExtend zero_le_one
      (extChartAt I x₀ ∘ κ ∘ faceInclusion K τ ∘ StandardSimplex.lineMap bτ y)) u (Icc 0 1) 0)
    {i : ι} {l : ℝ} (hl : l ∈ Icc (x.val i - b.val i) (y.val i - b.val i)) {ε : ℝ} (hε : 0 < ε) :
    ∃ t > 0, ∃ z ∈ G, ‖extChartAt I x₀ (κ z) - extChartAt I x₀ (κ b) - t • u‖ ≤ ε * t ∧
      z.val i = b.val i + t * l := by
  set φ := extChartAt I x₀
  -- Points of the model range near `φ (κ b)` are in the chart target, with inverse image in `G`.
  have hlim : Tendsto (κ.symm ∘ φ.symm) (𝓝[range I] (φ (κ b))) (𝓝 b) := by
    have h := (κ.symm.continuous.continuousAt.comp_continuousWithinAt
      ((continuousOn_extChartAt_symm x₀ _ (φ.map_source hb)).mono_of_mem_nhdsWithin
        (extChartAt_target_mem_nhdsWithin' hb))).tendsto
    rwa [comp_apply, φ.left_inv hb, κ.symm_apply_apply] at h
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhdsWithin_iff.1
    (inter_mem (extChartAt_target_mem_nhdsWithin' hb) (hlim hG))
  have hbσ' (j : ι) : bσ.val j = b.val j := by rw [← hbσ, faceInclusion_val]
  have hbτ' (j : ι) : bτ.val j = b.val j := by rw [← hbτ, faceInclusion_val]
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht0, ⟨p, hps, hpt, hpb, hpi⟩, ⟨q, hqs, hqt, hqb, hqi⟩⟩ := (hpos.and
    ((eventually_exists_extChartAt_mem_ball κ x₀ (by rwa [hbσ]) hx hε hr).and
      (eventually_exists_extChartAt_mem_ball κ x₀ (by rwa [hbτ]) hy hε hr))).exists
  rw [hbσ] at hpt hpb
  rw [hbτ] at hqt hqb
  -- The segment between the images of `p` and `q`, and its connected inverse image.
  have hmemI (z : Realization K) : φ (κ z) ∈ range I := by
    rw [extChartAt_coe]
    exact mem_range_self _
  set s := segment ℝ (φ (κ p)) (φ (κ q))
  have hs1 : s ⊆ ball (φ (κ b)) r ∩ range I :=
    ((convex_ball _ _).inter I.convex_range).segment_subset ⟨hpb, hmemI _⟩ ⟨hqb, hmemI _⟩
  have hs2 : s ⊆ closedBall (φ (κ b) + t • u) (ε * t) := by
    refine (convex_closedBall _ _).segment_subset ?_ ?_ <;>
      rw [mem_closedBall, dist_eq_norm, ← sub_sub]
    exacts [hpt, hqt]
  have hC : IsPreconnected ((κ.symm ∘ φ.symm) '' s) :=
    (convex_segment _ _).isPreconnected.image _ (κ.symm.continuous.comp_continuousOn
      ((continuousOn_extChartAt_symm x₀).mono fun e he => (hrsub (hs1 he)).1))
  have hpC : p ∈ (κ.symm ∘ φ.symm) '' s :=
    ⟨φ (κ p), left_mem_segment ℝ _ _, by simp [φ.left_inv hps]⟩
  have hqC : q ∈ (κ.symm ∘ φ.symm) '' s :=
    ⟨φ (κ q), right_mem_segment ℝ _ _, by simp [φ.left_inv hqs]⟩
  have hlevel : b.val i + t * l ∈ Icc (p.val i) (q.val i) := by
    rw [hpi, hqi, hbσ', hbτ']
    constructor <;> nlinarith [hl.1, hl.2]
  obtain ⟨_, ⟨e, he, rfl⟩, hzi⟩ := hC.intermediate_value hpC hqC
    ((continuous_apply i).comp (continuous_realization_coe K)).continuousOn hlevel
  have hfz : φ (κ ((κ.symm ∘ φ.symm) e)) = e := by
    simp [φ.right_inv (hrsub (hs1 he)).1]
  refine ⟨t, ht0, _, (hrsub (hs1 he)).2, ?_, hzi⟩
  have := hs2 he
  rwa [mem_closedBall, dist_eq_norm, ← sub_sub, ← hfz] at this

/-- The choice of a coordinate value `l` and a scale `ε`. Let finitely many simplices `ρ` contain
`b`, each with a linear map `D ρ` injective on its directions. Between any `α < β` there are
`l ≠ 0` and `ε > 0` such that no direction `a` of a simplex `ρ` containing the vertex `i` has
`‖D ρ a - u‖ ≤ ε * ‖a‖ + ε` and `a i = l`: we avoid the `i`-th coordinates of the finitely many
directions with `D ρ a = u`, at most one in each simplex. -/
private theorem exists_mem_Ioo_ne_zero_exists_pos {b : Realization K}
    (hfin : {ρ : Face K | b.val.support ⊆ ρ.val}.Finite)
    {D : ∀ ρ : Face K, b.val.support ⊆ ρ.val → (ρ.val → ℝ) →L[ℝ] E}
    (hinj : ∀ ρ hρ, ∀ v : ρ.val → ℝ, ∑ a, v a = 0 → D ρ hρ v = 0 → v = 0) (u : E) (i : ι)
    {α β : ℝ} (hαβ : α < β) :
    ∃ l ∈ Ioo α β, l ≠ 0 ∧ ∃ ε > 0, ∀ (ρ : Face K) (hρ : b.val.support ⊆ ρ.val) (hi : i ∈ ρ.val)
      (a : ρ.val → ℝ), ∑ j, a j = 0 → ‖D ρ hρ a - u‖ ≤ ε * ‖a‖ + ε → a ⟨i, hi⟩ ≠ l := by
  set B : Set ℝ := {0} ∪ ⋃ ρ : Face K, ⋃ hρ : ρ ∈ {ρ : Face K | b.val.support ⊆ ρ.val},
    {l | ∃ a : ρ.val → ℝ, ∑ j, a j = 0 ∧ D ρ hρ a = u ∧ ∃ h : i ∈ ρ.val, a ⟨i, h⟩ = l}
  have hB : B.Finite := by
    refine (finite_singleton 0).union (hfin.biUnion' fun ρ hρ => Set.Subsingleton.finite ?_)
    rintro l₁ ⟨a₁, h₁, hD₁, hi₁, rfl⟩ l₂ ⟨a₂, h₂, hD₂, hi₂, rfl⟩
    rw [sub_eq_zero.1 (hinj ρ hρ (a₁ - a₂)
      (by simp only [Pi.sub_apply, Finset.sum_sub_distrib, h₁, h₂, sub_self])
      (by rw [map_sub, hD₁, hD₂, sub_self]))]
  obtain ⟨l, hl, hlB⟩ := ((Ioo_infinite hαβ).sdiff hB).nonempty
  have hgood : ∀ ρ ∈ {ρ : Face K | b.val.support ⊆ ρ.val}, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ (hρ' : b.val.support ⊆ ρ.val) (hi : i ∈ ρ.val) (a : ρ.val → ℝ), ∑ j, a j = 0 →
        ‖D ρ hρ' a - u‖ ≤ ε * ‖a‖ + ε → a ⟨i, hi⟩ ≠ l := by
    intro ρ hρ
    by_cases hi : i ∈ ρ.val
    · exact (eventually_forall_apply_ne (hinj ρ hρ) ⟨i, hi⟩ fun a ha hDa hai =>
        hlB (Or.inr (mem_iUnion₂.2 ⟨ρ, hρ, a, ha, hDa, hi, hai⟩))).mono fun _ h _ _ => h
    · exact Eventually.of_forall fun _ _ h => absurd h hi
  obtain ⟨ε, hεgood, hε⟩ :=
    (((eventually_all_finite hfin).2 hgood).and self_mem_nhdsWithin).exists
  exact ⟨l, hl, fun h => hlB (Or.inl h), ε, hε, fun ρ hρ => hεgood ρ hρ hρ⟩

/-- The core of Munkres' Theorem 8.4. Let `κ : |K| ≃ₜ M` be a homeomorphism, `b` a point of `|K|`
in finitely many closed simplices, with `κ b` in the source of the extended chart `φ`, and suppose
that on every closed simplex `ρ` containing `b` the map `φ ∘ κ` has, in barycentric coordinates, a
derivative within the simplex at `b` which is injective on the directions of the simplex. Then two
points `x` and `y` of closed simplices containing `b` along whose segments from `b` the map
`φ ∘ κ` has the same right derivative cannot have `x i < y i` for any vertex `i`. -/
private theorem false_of_hasDerivWithinAt_of_lt (κ : Realization K ≃ₜ M) (x₀ : M)
    {b : Realization K} (hb : κ b ∈ (extChartAt I x₀).source)
    (hfin : {ρ : Face K | b.val.support ⊆ ρ.val}.Finite)
    (hD : ∀ ρ : Face K, b.val.support ⊆ ρ.val → ∃ F : (ρ.val → ℝ) → E,
      ∃ D : (ρ.val → ℝ) →L[ℝ] E,
        (∀ z : StandardSimplex ρ.val,
          F (fun a => z.val a) = extChartAt I x₀ (κ (faceInclusion K ρ z))) ∧
        HasFDerivWithinAt F D (range fun t : Convexity.StdSimplex ℝ ρ.val => ⇑t.weights)
          (fun a => b.val a) ∧
        ∀ v : ρ.val → ℝ, ∑ a, v a = 0 → D v = 0 → v = 0)
    {σ τ : Face K} {bσ x : StandardSimplex σ.val} {bτ y : StandardSimplex τ.val} {u : E}
    (hbσ : faceInclusion K σ bσ = b) (hbτ : faceInclusion K τ bτ = b)
    (hx : HasDerivWithinAt (IccExtend zero_le_one
      (extChartAt I x₀ ∘ κ ∘ faceInclusion K σ ∘ StandardSimplex.lineMap bσ x)) u (Icc 0 1) 0)
    (hy : HasDerivWithinAt (IccExtend zero_le_one
      (extChartAt I x₀ ∘ κ ∘ faceInclusion K τ ∘ StandardSimplex.lineMap bτ y)) u (Icc 0 1) 0)
    {i : ι} (hi : x.val i < y.val i) : False := by
  classical
  choose F D hF hFD hinj using hD
  obtain ⟨l, hl, hl0, ε, hε, hεgood⟩ := exists_mem_Ioo_ne_zero_exists_pos hfin hinj u i
    (by linarith : x.val i - b.val i < y.val i - b.val i)
  -- A point `z` near `b` with `z i = b i + t * l` and image within `ε * t` of `φ (κ b) + t • u`.
  obtain ⟨t, ht, z, ⟨hpos, hest⟩, hzt, hzi⟩ := exists_pos_exists_mem_apply_eq κ x₀ hb
    (eventually_nhds_norm_sub_sub_le hfin hFD hε) hbσ hbτ hx hy (Ioo_subset_Icc_self hl) hε
  -- Read `(z - b) / t` in the closed simplex `ρ` of the carrier of `z`, which contains `b`.
  set ρ := carrier K z
  have hρ : b.val.support ⊆ ρ.val := fun v hv => by
    rw [carrier_val, Finsupp.mem_support_iff]
    exact (hpos v hv).ne'
  obtain ⟨w, hw⟩ : z ∈ range (faceInclusion K ρ) := mem_range_faceInclusion_carrier K z
  set bρ : StandardSimplex ρ.val := ⟨b.val, Realization.mem_convexHull_of_support_subset K b hρ⟩
  by_cases hiρ : i ∈ ρ.val
  · have hFb := hF ρ hρ bρ
    rw [faceInclusion_mk_val] at hFb
    obtain ⟨ha, haε⟩ := sum_smul_sub_eq_zero_and_norm_sub_le
      (Finset.sum_standardSimplex_eq_one w) (Finset.sum_standardSimplex_eq_one bρ) ht
      (hest ρ hρ w hw) (by rwa [hF ρ hρ w, hw, hFb])
    refine hεgood ρ hρ hiρ _ ha haε ?_
    have hwi : w.val i = z.val i := by rw [← hw, faceInclusion_val]
    simp only [bρ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hwi, hzi]
    field_simp
    ring
  · -- Off `ρ` both coordinates vanish, so `t * l = 0`, while `l ≠ 0`.
    have hzi0 : z.val i = 0 := by rwa [← Finsupp.notMem_support_iff, ← carrier_val]
    have hbi0 : b.val i = 0 := Finsupp.notMem_support_iff.mp fun h => hiρ (hρ h)
    rw [hzi0, hbi0, zero_add, eq_comm, mul_eq_zero] at hzi
    exact hzi.elim ht.ne' hl0

namespace IsSmoothTriangulation

variable [FiniteDimensional ℝ E] [IsManifold I 1 M] {κ : Realization K ≃ₜ M}

/-- **Munkres, Theorem 8.4: the differential of a smooth triangulation is injective on stars.**
Let `κ` be a `Cⁿ` triangulation of a `C¹` manifold modelled on a finite-dimensional space, read in
an extended chart whose source contains `κ b`. If `κ` has, in the chart, the same derivative from
the right along the segments from `b` to points `x` and `y` of closed simplices containing `b`,
then `x = y`. This is the star condition of `TauCeti.IsStarImmersion` for the chart
representative of `κ`. -/
theorem eq_of_hasDerivWithinAt_extChartAt (h : IsSmoothTriangulation I n κ) {x₀ : M}
    {σ τ : Face K} {b x : StandardSimplex σ.val} {b' y : StandardSimplex τ.val} {u : E}
    (hb : (b : ι →₀ ℝ) = b') (hb₀ : κ (faceInclusion K σ b) ∈ (extChartAt I x₀).source)
    (hx : HasDerivWithinAt (IccExtend zero_le_one
      (extChartAt I x₀ ∘ κ ∘ faceInclusion K σ ∘ StandardSimplex.lineMap b x)) u (Icc 0 1) 0)
    (hy : HasDerivWithinAt (IccExtend zero_le_one
      (extChartAt I x₀ ∘ κ ∘ faceInclusion K τ ∘ StandardSimplex.lineMap b' y)) u (Icc 0 1) 0) :
    (x : ι →₀ ℝ) = y := by
  set p := faceInclusion K σ b
  -- `p` lies in finitely many closed simplices, as `K` is locally finite.
  have hfin : {ρ : Face K | p.val.support ⊆ ρ.val}.Finite := by
    obtain ⟨v, hv⟩ := exists_mem_openStarRealization K p
    refine ((finite_setOf_mem_of_homeomorph_manifold I κ v).preimage
      Subtype.val_injective.injOn).subset fun ρ hρ => ⟨ρ.property, hρ ?_⟩
    exact Finsupp.mem_support_iff.2 ((mem_openStarRealization K).1 hv).ne'
  have hD (ρ : Face K) (hρ : p.val.support ⊆ ρ.val) :=
    (isSmoothTriangulation_iff.mp h ρ).exists_hasFDerivWithinAt_extChartAt
      (w := ⟨p.val, Realization.mem_convexHull_of_support_subset K p hρ⟩)
      (by rwa [comp_apply, faceInclusion_mk_val])
  have hbp : faceInclusion K τ b' = p := Subtype.ext <| by
    rw [faceInclusion_val, faceInclusion_val, hb]
  refine DFunLike.coe_injective (funext fun i => ?_)
  rcases lt_trichotomy (x.val i) (y.val i) with hlt | heq | hlt
  · exact (false_of_hasDerivWithinAt_of_lt κ x₀ hb₀ hfin hD rfl hbp hx hy hlt).elim
  · exact heq
  · exact (false_of_hasDerivWithinAt_of_lt κ x₀ hb₀ hfin hD hbp rfl hy hx hlt).elim

/-- **A smooth triangulation is a star immersion in charts.** Let `κ` be a `Cⁿ` triangulation of a
`Cⁿ` and `C¹` manifold modelled on a finite-dimensional space, and `L` a subcomplex of `K` whose
realization `κ` maps into the source of an extended chart `φ`. Then `φ ∘ κ` on `|L|` is a `Cⁿ`
star immersion: it is an immersion on every closed simplex, and by Munkres' Theorem 8.4
(`TauCeti.IsSmoothTriangulation.eq_of_hasDerivWithinAt_extChartAt`) its differential is injective
on the closed star of every point. -/
theorem isStarImmersion_extChartAt_comp_realizationMap [IsManifold I n M]
    (h : IsSmoothTriangulation I n κ) {L : AbstractSimplicialComplex ι} (hLK : L ≤ K) {x₀ : M}
    (hL : ∀ z, κ (realizationMap hLK z) ∈ (extChartAt I x₀).source) :
    IsStarImmersion n (extChartAt I x₀ ∘ κ ∘ realizationMap hLK) := by
  have hR (σ : Face L) (z : StandardSimplex σ.val) :
      realizationMap hLK (faceInclusion L σ z) = faceInclusion K ⟨σ.val, hLK σ.property⟩ z :=
    congrFun (realizationMap_comp_faceInclusion hLK σ) z
  have hcomp (σ : Face L) : (extChartAt I x₀ ∘ κ ∘ realizationMap hLK) ∘ faceInclusion L σ =
      extChartAt I x₀ ∘ κ ∘ faceInclusion K ⟨σ.val, hLK σ.property⟩ :=
    funext fun z => by simp only [comp_apply, hR]
  refine isStarImmersion_iff.mpr ⟨fun σ => ?_, fun σ τ b x b' y u hb hx hy => ?_⟩
  · rw [hcomp]
    refine (isSmoothTriangulation_iff.mp h _).extChartAt_comp ?_
    rintro _ ⟨z, rfl⟩
    rw [comp_apply, ← hR]
    exact hL _
  · rw [← comp_assoc, hcomp, comp_assoc, comp_assoc] at hx hy
    refine h.eq_of_hasDerivWithinAt_extChartAt (σ := ⟨σ.val, hLK σ.property⟩)
      (τ := ⟨τ.val, hLK τ.property⟩) hb ?_ hx hy
    rw [← hR]
    exact hL _

end IsSmoothTriangulation

end TauCeti
