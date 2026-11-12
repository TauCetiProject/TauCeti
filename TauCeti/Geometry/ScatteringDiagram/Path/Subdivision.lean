/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.ScatteringDiagram.Path.Basic

/-!
# Subdividing admissible segments

Restricting an admissible segment to the interval between any two parameters
with allowed endpoints gives an admissible segment, whose crossings are those of the
original segment at the rescaled parameters. In particular, inserting an allowed
vertex inside an admissible segment gives two admissible segments.
`Quiver.Path.IsSubdivision` records finite repetitions and concatenations
of these insertions. Their crossing parameters rescale to the original parameter interval.
These formulas retain the wall indices, including simultaneous crossings in an
arbitrary wall family, and allow ordered crossing lists to be compared after subdivision.

A function that is locally constant off the walls takes the value at the start of a segment
at every point before the first crossing, and the value at the end at every point after the
last crossing. On a segment whose crossings all occur at one time `t`, the crossings are the
walls through the point at time `t`.

The affine parameter calculations use Mathlib's `AffineMap.lineMap_lineMap_right`
and `AffineMap.lineMap_lineMap_left`.

Adapted from `Mei/Geometry/Convex/Polyhedron/SegmentSubdivision.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
Original copyright (c) 2026 Mei contributors; original author: Codex.
-/

public section

open Set

namespace TauCeti.WallComplement

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : ι → Set V} {x y z : WallComplement W} {t : ℝ}

/-- Restricting an admissible segment to the interval between two parameters in `[0, 1]`
preserves admissibility, provided the new endpoints lie off all walls. The two parameters
may occur in either order. -/
theorem AdmissibleSegment.subsegment (e : AdmissibleSegment x y) {a b : WallComplement W}
    {s u : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (ha : a.val = AffineMap.lineMap x.val y.val s)
    (hb : b.val = AffineMap.lineMap x.val y.val u) : AdmissibleSegment a b := by
  have hline (r : ℝ) : AffineMap.lineMap a.val b.val r =
      AffineMap.lineMap x.val y.val (s + r * (u - s)) := by
    simp only [ha, hb, AffineMap.lineMap_apply_module']
    module
  have hmem {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) : s + r * (u - s) ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨hr₀, hr₁⟩ := hr
    constructor <;> nlinarith [hs.1, hs.2, hu.1, hu.2, mul_nonneg hr₀ hu.1,
      mul_nonneg (sub_nonneg.mpr hr₁) hs.1, mul_nonneg hr₀ (sub_nonneg.mpr hu.2),
      mul_nonneg (sub_nonneg.mpr hr₁) (sub_nonneg.mpr hs.2)]
  refine ⟨fun j hj => ?_, fun r hr => by simpa only [hline] using e.regular _ (hmem hr)⟩
  obtain ⟨r, hr, hj⟩ := hj
  rw [hline] at hj
  have hd := e.transverse j ⟨_, hmem hr, hj⟩
  have hba : b.val - a.val = (u - s) • (y.val - x.val) := by
    simp only [ha, hb, AffineMap.lineMap_apply_module']
    module
  by_cases hus : u - s = 0
  · refine (a.notMem j ?_).elim
    simpa only [ha, hus, mul_zero, add_zero] using hj
  · rw [hba]
    exact fun hmem' => hd ((Submodule.smul_mem_iff _ hus).mp hmem')

/-- The parameter `r` on a subsegment between parameters `s` and `u` corresponds to the
original parameter `s + r * (u - s)`. -/
theorem mem_crossings_subsegment {a b : WallComplement W} {s u : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (ha : a.val = AffineMap.lineMap x.val y.val s)
    (hb : b.val = AffineMap.lineMap x.val y.val u) (i : ι) (r : ℝ) :
    (i, r) ∈ crossings a b ↔ r ∈ Icc (0 : ℝ) 1 ∧ (i, s + r * (u - s)) ∈ crossings x y := by
  have hline : AffineMap.lineMap a.val b.val r =
      AffineMap.lineMap x.val y.val (s + r * (u - s)) := by
    simp only [ha, hb, AffineMap.lineMap_apply_module']
    module
  simp only [mem_crossings, hline]
  constructor
  · rintro ⟨hr, hi⟩
    obtain ⟨hr₀, hr₁⟩ := hr
    refine ⟨⟨hr₀, hr₁⟩, ⟨?_, ?_⟩, hi⟩ <;> nlinarith [hs.1, hs.2, hu.1, hu.2,
      mul_nonneg hr₀ hu.1, mul_nonneg (sub_nonneg.mpr hr₁) hs.1,
      mul_nonneg hr₀ (sub_nonneg.mpr hu.2), mul_nonneg (sub_nonneg.mpr hr₁) (sub_nonneg.mpr hs.2)]
  · rintro ⟨hr, -, hi⟩
    exact ⟨hr, hi⟩

/-- Restricting an admissible segment to its first, nonconstant parameter interval
preserves admissibility, provided the new vertex lies off all walls. -/
theorem AdmissibleSegment.subdivide_left (e : AdmissibleSegment x y)
    (ht : t ∈ Ioc (0 : ℝ) 1) (hz : z.val = AffineMap.lineMap x.val y.val t) :
    AdmissibleSegment x z :=
  e.subsegment ⟨le_rfl, zero_le_one⟩ ⟨ht.1.le, ht.2⟩ (AffineMap.lineMap_apply_zero _ _).symm hz

/-- Restricting an admissible segment to its last, nonconstant parameter interval
preserves admissibility. -/
theorem AdmissibleSegment.subdivide_right (e : AdmissibleSegment x y)
    (ht : t ∈ Ico (0 : ℝ) 1) (hz : z.val = AffineMap.lineMap x.val y.val t) :
    AdmissibleSegment z y := by
  have hz' : z.val = AffineMap.lineMap y.val x.val (1 - t) := by
    rw [AffineMap.lineMap_apply_one_sub, hz]
  exact (e.symm.subdivide_left ⟨by linarith [ht.2], by linarith [ht.1]⟩ hz').symm

/-- The first subsegment's parameter `s` corresponds to the original parameter `s * t`. -/
theorem mem_crossings_subdivide_left (hz : z.val = AffineMap.lineMap x.val y.val t)
    (ht : t ∈ Ioc (0 : ℝ) 1) (i : ι) (s : ℝ) :
    (i, s) ∈ crossings x z ↔ (i, s * t) ∈ crossings x y ∧ s ≤ 1 := by
  simp only [mem_crossings, hz, AffineMap.lineMap_lineMap_right, mem_Icc]
  constructor
  · rintro ⟨⟨hs₀, hs₁⟩, hi⟩
    exact ⟨⟨⟨mul_nonneg hs₀ ht.1.le, by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs₁) ht.1.le, ht.2]⟩, hi⟩, hs₁⟩
  · rintro ⟨⟨⟨hs₀, -⟩, hi⟩, hs₁⟩
    exact ⟨⟨by nlinarith [ht.1], hs₁⟩, hi⟩

/-- The last subsegment's parameter `s` corresponds to `1 - (1 - s) * (1 - t)`. -/
theorem mem_crossings_subdivide_right (hz : z.val = AffineMap.lineMap x.val y.val t)
    (ht : t ∈ Ico (0 : ℝ) 1) (i : ι) (s : ℝ) :
    (i, s) ∈ crossings z y ↔
      (i, 1 - (1 - s) * (1 - t)) ∈ crossings x y ∧ 0 ≤ s := by
  rw [mem_crossings_swap y z, mem_crossings_subdivide_left (x := y) (y := x)
    (by simpa only [AffineMap.lineMap_apply_one_sub] using hz)
    (⟨by linarith [ht.2], by linarith [ht.1]⟩ :
      1 - t ∈ Ioc (0 : ℝ) 1),
    mem_crossings_swap x y]
  constructor <;> rintro ⟨hi, hs⟩ <;> exact ⟨hi, by linarith⟩

/-- Rescaling the two subsegments recovers exactly the original indexed crossings. -/
theorem crossings_subdivide (hz : z.val = AffineMap.lineMap x.val y.val t)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    crossings x y =
      (fun a : ι × ℝ => (a.1, a.2 * t)) '' crossings x z ∪
      (fun a : ι × ℝ => (a.1, 1 - (1 - a.2) * (1 - t))) '' crossings z y := by
  ext ⟨i, s⟩
  constructor
  · intro hs
    by_cases hst : s ≤ t
    · left
      refine ⟨(i, s / t), ?_, by simp [ht.1.ne']⟩
      rw [mem_crossings_subdivide_left hz ⟨ht.1, ht.2.le⟩]
      exact ⟨by simpa only [div_mul_cancel₀ _ ht.1.ne'] using hs,
        (div_le_one ht.1).mpr hst⟩
    · right
      have he : 1 - (1 - (s - t) / (1 - t)) * (1 - t) = s := by
        field_simp [(sub_pos.mpr ht.2).ne']
        ring
      refine ⟨(i, (s - t) / (1 - t)), ?_, Prod.ext rfl he⟩
      rw [mem_crossings_subdivide_right hz ⟨ht.1.le, ht.2⟩, he]
      exact ⟨hs, div_nonneg (by linarith) (by linarith [ht.2])⟩
  · rintro (⟨⟨j, r⟩, hr, he⟩ | ⟨⟨j, r⟩, hr, he⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ((mem_crossings_subdivide_left hz ⟨ht.1, ht.2.le⟩ j r).mp hr).1
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ((mem_crossings_subdivide_right hz ⟨ht.1.le, ht.2⟩ j r).mp hr).1

section Constant

variable {Y : Type*} {F : V → Y} (hF : ∀ θ, (∀ i, θ ∉ W i) → ∀ᶠ φ in nhds θ, F φ = F θ)
  {a : WallComplement W} {r : ℝ}

include hF in
/-- A function locally constant off the walls agrees at the start of a segment and at a point
of it before all crossings. -/
theorem apply_eq_of_lt_crossings (hr : r ∈ Icc (0 : ℝ) 1)
    (ha : a.val = AffineMap.lineMap x.val y.val r)
    (hcr : ∀ i t, (i, t) ∈ crossings x y → r < t) : F x.val = F a.val := by
  refine apply_eq_of_crossings_eq_empty hF (eq_empty_iff_forall_notMem.mpr fun ⟨i, t⟩ ht => ?_)
  obtain ⟨⟨-, ht₁⟩, hit⟩ := (mem_crossings_subsegment ⟨le_rfl, zero_le_one⟩ hr
    (AffineMap.lineMap_apply_zero _ _).symm ha i t).mp ht
  have hlt := hcr _ _ hit
  have hle : t * r ≤ r := mul_le_of_le_one_left hr.1 ht₁
  rw [zero_add, sub_zero] at hlt
  linarith

include hF in
/-- A function locally constant off the walls agrees at a point of a segment after all
crossings and at its end. -/
theorem apply_eq_of_crossings_lt (hr : r ∈ Icc (0 : ℝ) 1)
    (ha : a.val = AffineMap.lineMap x.val y.val r)
    (hcr : ∀ i t, (i, t) ∈ crossings x y → t < r) : F a.val = F y.val := by
  refine apply_eq_of_crossings_eq_empty hF (eq_empty_iff_forall_notMem.mpr fun ⟨i, t⟩ ht => ?_)
  obtain ⟨⟨ht₀, -⟩, hit⟩ := (mem_crossings_subsegment hr ⟨zero_le_one, le_rfl⟩ ha
    (AffineMap.lineMap_apply_one _ _).symm i t).mp ht
  have hlt := hcr _ _ hit
  have hle : 0 ≤ t * (1 - r) := mul_nonneg ht₀ (sub_nonneg.mpr hr.2)
  linarith

omit hF in
/-- On a segment whose crossings all occur at one time `t`, the crossings are exactly the walls
through the point at time `t`. -/
theorem mem_crossings_iff_of_subsingleton (he : (Prod.snd '' crossings x y).Subsingleton)
    {i₀ : ι} {t : ℝ} (ht : (i₀, t) ∈ crossings x y) (i : ι) (s : ℝ) :
    (i, s) ∈ crossings x y ↔ AffineMap.lineMap x.val y.val t ∈ W i ∧ s = t := by
  constructor
  · intro hs
    obtain rfl : s = t := he ⟨_, hs, rfl⟩ ⟨_, ht, rfl⟩
    exact ⟨((mem_crossings _ _ _ _).mp hs).2, rfl⟩
  · rintro ⟨hi, rfl⟩
    exact (mem_crossings _ _ _ _).mpr ⟨((mem_crossings _ _ _ _).mp ht).1, hi⟩

include hF in
/-- On a segment whose crossings all occur at one time `t`, a function locally constant off the
walls takes its endpoint values at the points of times `t - s` and `t + s` for `0 < s` with
`t ± s ∈ [0, 1]`. -/
theorem apply_eq_lineMap_of_subsingleton (he : (Prod.snd '' crossings x y).Subsingleton)
    {i₀ : ι} {t : ℝ} (ht : (i₀, t) ∈ crossings x y) {s : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (hst' : s ≤ 1 - t) :
    F x.val = F (AffineMap.lineMap x.val y.val (t - s)) ∧
      F (AffineMap.lineMap x.val y.val (t + s)) = F y.val := by
  have htime {i : ι} {r : ℝ} (hr : (i, r) ∈ crossings x y) : r = t :=
    he ⟨_, hr, rfl⟩ ⟨_, ht, rfl⟩
  have hoff {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hrt : r ≠ t) (i : ι) :
      AffineMap.lineMap x.val y.val r ∉ W i := fun hi =>
    hrt (htime ((mem_crossings _ _ _ _).mpr ⟨hr, hi⟩))
  exact ⟨apply_eq_of_lt_crossings (a := ⟨_, hoff ⟨by linarith, by linarith⟩ (by linarith)⟩) hF
      ⟨by linarith, by linarith⟩ rfl fun _ _ hr => by linarith [htime hr],
    apply_eq_of_crossings_lt (a := ⟨_, hoff ⟨by linarith, by linarith⟩ (by linarith)⟩) hF
      ⟨by linarith, by linarith⟩ rfl fun _ _ hr => by linarith [htime hr]⟩

end Constant

end TauCeti.WallComplement

namespace Quiver.Path

open TauCeti

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : ι → Set V}

/-- Finite subdivision of an admissible polygonal path by allowed interior vertices.
The relation is generated by splitting a segment, concatenating subdivisions,
and repeating these operations. The first path is the original, the second the refinement. -/
inductive IsSubdivision : {x y : WallComplement W} →
    AdmissiblePLPath x y → AdmissiblePLPath x y → Prop
  /-- Every path subdivides itself. -/
  | refl {x y} (p : AdmissiblePLPath x y) : IsSubdivision p p
  /-- Inserting an allowed interior vertex splits one segment into two. -/
  | split {x y z : WallComplement W} (e : x ⟶ y) (e₁ : x ⟶ z) (e₂ : z ⟶ y)
      {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
      (hz : z.val = AffineMap.lineMap x.val y.val t) :
      IsSubdivision e.toPath (e₁.toPath.comp e₂.toPath)
  /-- Subdivisions can be performed on either side of a concatenation. -/
  | comp {x y z} {p p' : AdmissiblePLPath x y} {q q' : AdmissiblePLPath y z}
      (hp : IsSubdivision p p') (hq : IsSubdivision q q') :
      IsSubdivision (p.comp q) (p'.comp q')
  /-- A subdivision of a subdivision is a subdivision of the original path. -/
  | trans {x y} {p q r : AdmissiblePLPath x y}
      (hpq : IsSubdivision p q) (hqr : IsSubdivision q r) : IsSubdivision p r

/-- Subdivision retains exactly the wall indices encountered by a path.
See `TauCeti.WallComplement.crossings_subdivide` for the crossing-parameter formulas
for a single split. -/
theorem IsSubdivision.image_crossingEvents {x y : WallComplement W}
    {p q : AdmissiblePLPath x y} (h : IsSubdivision p q) :
    (fun c : ℕ × (ι × ℝ) => c.2.1) '' p.crossingEvents =
      (fun c : ℕ × (ι × ℝ) => c.2.1) '' q.crossingEvents := by
  induction h with
  | refl => rfl
  | split e e₁ e₂ ht hz =>
    simpa only [crossingEvents_comp, crossingEvents_toPath,
      Set.image_union, Set.image_image] using
      congrArg (Set.image Prod.fst) (WallComplement.crossings_subdivide hz ht)
  | comp hp hq ihp ihq =>
    simp only [crossingEvents_comp, Set.image_union, Set.image_image]
    rw [ihp, ihq]
  | trans _ _ ihpq ihqr => exact ihpq.trans ihqr

end Quiver.Path
