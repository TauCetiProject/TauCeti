/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.TypeTags
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Topology.MetricSpace.BundledFun
public import TauCeti.Algebra.Order.Group.IntervalIsometry

/-!
# `Λ`-metric spaces and `Λ`-trees

Let `Λ` be a linearly ordered abelian group. A `Λ`-metric on a type `X` is a function
`d : X → X → Λ` satisfying the axioms of a metric, with values in `Λ` instead of `ℝ`. A *segment*
from `x` to `y` is the image of an isometric embedding of the interval `[0, d x y]` of `Λ` into
`X` sending `0` to `x` and `d x y` to `y`; the space is *geodesic* when any two points are joined
by a segment. A *`Λ`-tree* is a nonempty geodesic `Λ`-metric space in which

* (T2) two segments meeting in a single point, which is an endpoint of both, have a segment as
  their union, and
* (T3) two segments with a common endpoint intersect in a segment.

For `Λ = ℤ` these are the vertex sets of simplicial trees with their path metric, and for
`Λ = ℝ` they are the `ℝ`-trees. Groups acting freely on `Λ`-trees are exactly the groups with a
free Lyndon length function with values in `Λ` (Chiswell), which is how `Λ`-trees enter the
study of limit groups: a finitely generated fully residually free group acts freely on a
`ℤⁿ`-tree.

Measuring the distance from `x` identifies a segment from `x` to `y` isometrically with the
interval `[0, d x y]`, so the part of a segment between two of its points is again a segment. We
prove that segments in a `Λ`-tree are unique, hence convex, that `Λ` itself, with the metric
`|a - b|`, is a `Λ`-tree whose segments are its closed intervals, and that a one-point space is a
`Λ`-tree. An injective map `f : Y → X` induces the `Λ`-metric `d (f x) (f y)` on `Y`, whose
segments are the sets with image a segment of `X`; when `X` is a `Λ`-tree it makes `Y` a `Λ`-tree
exactly when `Y` is nonempty and the range of `f` contains the segment between any two of its
points. In particular the subsets of `Λ` which are `Λ`-trees are the nonempty order-connected
(convex) ones. The vertex set of a cycle of length four, with its path metric, is a geodesic
`ℤ`-metric space which is not a `ℤ`-tree, so geodesicity alone does not make a `Λ`-metric space a
`Λ`-tree.

## Main definitions

* `TauCeti.LambdaMetric Λ X`: a `Λ`-valued metric on `X`.
* `TauCeti.LambdaMetric.self Λ`: the metric `|a - b|` on `Λ`.
* `TauCeti.LambdaMetric.comap d f hf`: the `Λ`-metric induced on `Y` by an injective map
  `f : Y → X`.
* `TauCeti.LambdaMetric.IsIsometricAction d G`: `G` acts on `X` by isometries of `d`.
* `TauCeti.LambdaMetric.IsSegment d σ x y`: `σ` is a segment from `x` to `y`.
* `TauCeti.LambdaMetric.IsGeodesic d`: any two points are joined by a segment.
* `TauCeti.LambdaMetric.IsTree d`: `d` makes `X` a `Λ`-tree.
* `TauCeti.LambdaMetric.IsTree.segment`: the unique segment `[x, y]` in a `Λ`-tree.

## Main results

* `TauCeti.LambdaMetric.isSegment_iff_exists_Icc`: segments are the isometric images of arbitrary
  closed intervals `[a, b]` of `Λ`.
* `TauCeti.LambdaMetric.IsSegment.eq_of_subset`: a segment contained in a segment and containing
  its endpoints is equal to it.
* `TauCeti.LambdaMetric.IsSegment.dist_add_dist`: a point `u` of a segment from `x` to `y`
  satisfies `d x u + d u y = d x y`.
* `TauCeti.LambdaMetric.IsSegment.isSegment_sep`: the part of a segment between two of its points
  is a segment.
* `TauCeti.LambdaMetric.IsTree.isSegment_unique`: in a `Λ`-tree, two points are joined by a
  unique segment.
* `TauCeti.LambdaMetric.IsTree.segment_eq_sep`: in a `Λ`-tree, the segment between two points of
  a segment is the part of that segment between them.
* `TauCeti.LambdaMetric.isSegment_comap_iff`: a set is a segment for the metric induced by an
  injective map `f` if and only if its image under `f` is a segment.
* `TauCeti.LambdaMetric.IsTree.isTree_comap_iff`: the metric induced on `Y` by an injective map
  `f` into a `Λ`-tree makes `Y` a `Λ`-tree if and only if `Y` is nonempty and the range of `f`
  contains the segment between any two of its points.
* `TauCeti.LambdaMetric.isTree_self`: `Λ` is a `Λ`-tree.
* `TauCeti.LambdaMetric.isTree_comap_self_subtype_iff`: a subset of `Λ`, with the metric
  `|a - b|`, is a `Λ`-tree if and only if it is nonempty and order-connected.
* `TauCeti.LambdaMetric.isIsometricAction_self`: `Λ` acts on itself by isometric translations.
* `TauCeti.LambdaMetric.exists_isGeodesic_not_isTree`: a geodesic `ℤ`-metric space need not be a
  `ℤ`-tree.

## References

* I. Chiswell, *Introduction to Λ-trees*, World Scientific, 2001, §§1.2 and 2.1.
* O. Kharlampovich, A. Myasnikov, D. Serbin, *Actions, length functions, and non-Archimedean
  words*, Internat. J. Algebra Comput. 23 (2013), §4.2 (Example 9 for the convex subsets of `Λ`).
-/

public section

namespace TauCeti

open Set

/-- A `Λ`-metric on `X`, for a linearly ordered abelian group `Λ`: a `Λ`-valued pseudometric
(Mathlib's `PseudoMetric X Λ`) vanishing only on the diagonal. Nonnegativity follows
(`TauCeti.LambdaMetric.nonneg`). -/
structure LambdaMetric (Λ X : Type*) [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    extends PseudoMetric X Λ where
  eq_of_eq_zero' {x y : X} : toFun x y = 0 → x = y

namespace LambdaMetric

variable {Λ X : Type*} [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
  (d : LambdaMetric Λ X)

instance : FunLike (LambdaMetric Λ X) X (X → Λ) where
  coe d := d.toPseudoMetric
  coe_injective := fun ⟨_, _⟩ ⟨_, _⟩ h => by
    congr
    exact DFunLike.coe_injective h

@[simp]
theorem coe_toPseudoMetric : ⇑d.toPseudoMetric = d :=
  rfl

@[ext]
theorem ext {d d' : LambdaMetric Λ X} (h : ∀ x y, d x y = d' x y) : d = d' :=
  DFunLike.coe_injective (funext₂ h)

@[simp]
protected theorem refl (x : X) : d x x = 0 :=
  d.toPseudoMetric.refl x

protected theorem symm (x y : X) : d x y = d y x :=
  d.toPseudoMetric.symm x y

protected theorem triangle (x y z : X) : d x z ≤ d x y + d y z :=
  d.toPseudoMetric.triangle x y z

protected theorem nonneg (x y : X) : 0 ≤ d x y :=
  d.toPseudoMetric.nonneg x y

@[simp]
theorem eq_zero_iff {x y : X} : d x y = 0 ↔ x = y :=
  ⟨d.eq_of_eq_zero', fun h => h ▸ d.refl x⟩

theorem pos_iff {x y : X} : 0 < d x y ↔ x ≠ y := by
  rw [(d.nonneg x y).lt_iff_ne', Ne, eq_zero_iff]

variable (Λ) in
/-- The `Λ`-metric `|a - b|` on `Λ` itself. -/
def self : LambdaMetric Λ Λ where
  toFun a b := |a - b|
  refl' a := by simp
  symm' a b := abs_sub_comm a b
  triangle' a b c := abs_sub_le a b c
  eq_of_eq_zero' h := sub_eq_zero.1 (abs_eq_zero.1 h)

@[simp]
theorem self_apply (a b : Λ) : (self Λ) a b = |a - b| :=
  (rfl)

/-! ### Isometric actions -/

/-- `G` acts on `X` by isometries of the `Λ`-metric `d`. -/
def IsIsometricAction (G : Type*) [SMul G X] : Prop :=
  ∀ (g : G) (x y : X), d (g • x) (g • y) = d x y

namespace IsIsometricAction

variable {d} {G : Type*}

@[simp]
theorem dist_smul_smul [SMul G X] (hG : d.IsIsometricAction G) (g : G) (x y : X) :
    d (g • x) (g • y) = d x y :=
  hG g x y

variable [Group G] [MulAction G X]

/-- An isometry and its inverse move a point by the same distance. -/
@[simp]
theorem dist_inv_smul (hG : d.IsIsometricAction G) (g : G) (x : X) :
    d x (g⁻¹ • x) = d x (g • x) := by
  rw [← hG.dist_smul_smul g x (g⁻¹ • x), smul_inv_smul, d.symm]

/-- The distance `d x ((g⁻¹ * f) • x)` is the distance between the translates `g • x` and
`f • x`. -/
theorem dist_inv_mul_smul (hG : d.IsIsometricAction G) (g f : G) (x : X) :
    d x ((g⁻¹ * f) • x) = d (g • x) (f • x) := by
  rw [← hG.dist_smul_smul g x, mul_smul, smul_inv_smul]

end IsIsometricAction

/-! ### Segments -/

/-- `f` is isometric on the subset `s` of `Λ`: `d (f a) (f b) = |a - b|` for `a, b ∈ s`. -/
def IsometricOn (f : Λ → X) (s : Set Λ) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, d (f a) (f b) = |a - b|

theorem isometricOn_iff {f : Λ → X} {s : Set Λ} :
    d.IsometricOn f s ↔ ∀ a ∈ s, ∀ b ∈ s, d (f a) (f b) = |a - b| :=
  Iff.rfl

theorem IsometricOn.dist_eq {d : LambdaMetric Λ X} {f : Λ → X} {s : Set Λ}
    (h : d.IsometricOn f s) {a b : Λ} (ha : a ∈ s) (hb : b ∈ s) : d (f a) (f b) = |a - b| :=
  h a ha b hb

theorem IsometricOn.mono {d : LambdaMetric Λ X} {f : Λ → X} {s t : Set Λ} (h : d.IsometricOn f t)
    (hst : s ⊆ t) : d.IsometricOn f s :=
  fun a ha b hb => h a (hst ha) b (hst hb)

/-- `σ` is a segment from `x` to `y`: the image of the interval `[0, d x y]` under a map, isometric
on it, sending `0` to `x` and `d x y` to `y`. By `TauCeti.LambdaMetric.isSegment_iff_exists_Icc`
any closed interval `[a, b]` of `Λ` may be used instead of `[0, d x y]`. -/
def IsSegment (σ : Set X) (x y : X) : Prop :=
  ∃ f : Λ → X, f 0 = x ∧ f (d x y) = y ∧ d.IsometricOn f (Icc 0 (d x y)) ∧
    f '' Icc 0 (d x y) = σ

variable {d}

theorem isSegment_iff {σ : Set X} {x y : X} :
    d.IsSegment σ x y ↔ ∃ f : Λ → X, f 0 = x ∧ f (d x y) = y ∧
      d.IsometricOn f (Icc 0 (d x y)) ∧ f '' Icc 0 (d x y) = σ :=
  Iff.rfl

/-- Segments are the isometric images of closed intervals of `Λ`, with endpoints the images of
the endpoints. -/
theorem isSegment_iff_exists_Icc {σ : Set X} {x y : X} :
    d.IsSegment σ x y ↔ ∃ a b : Λ, ∃ f : Λ → X, a ≤ b ∧ f a = x ∧ f b = y ∧
      d.IsometricOn f (Icc a b) ∧ f '' Icc a b = σ := by
  refine ⟨fun ⟨f, h0, h1, hf, hσ⟩ => ⟨0, _, f, d.nonneg x y, h0, h1, hf, hσ⟩, ?_⟩
  rintro ⟨a, b, f, hab, rfl, rfl, hf, rfl⟩
  have hD : d (f a) (f b) = b - a := by
    rw [hf a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hab)]
  have hmem {s : Λ} (hs : s ∈ Icc 0 (b - a)) : a + s ∈ Icc a b :=
    ⟨le_add_of_nonneg_right hs.1, by grind⟩
  refine ⟨fun s => f (a + s), by simp, ?_⟩
  rw [hD]
  refine ⟨by simp, fun s hs t ht => ?_, ?_⟩
  · rw [hf _ (hmem hs) _ (hmem ht), add_sub_add_left_eq_sub]
  · rw [← image_image f (a + ·), image_const_add_Icc, add_zero, add_sub_cancel]

namespace IsSegment

variable {σ τ : Set X} {x y : X}

theorem left_mem (h : d.IsSegment σ x y) : x ∈ σ := by
  obtain ⟨f, rfl, -, -, rfl⟩ := h
  exact mem_image_of_mem f ⟨le_rfl, d.nonneg _ _⟩

theorem right_mem (h : d.IsSegment σ x y) : y ∈ σ := by
  obtain ⟨f, -, h1, -, rfl⟩ := h
  exact ⟨_, ⟨d.nonneg _ _, le_rfl⟩, h1⟩

/-- A segment from `x` to `y` is a segment from `y` to `x`. -/
theorem symm (h : d.IsSegment σ x y) : d.IsSegment σ y x := by
  rw [isSegment_iff_exists_Icc] at h ⊢
  obtain ⟨a, b, f, hab, rfl, rfl, hf, rfl⟩ := h
  have hmem {s : Λ} (hs : s ∈ Icc a b) : a + b - s ∈ Icc a b := ⟨by grind, by grind⟩
  refine ⟨a, b, fun s => f (a + b - s), hab, by simp, by simp, fun s hs t ht => ?_, ?_⟩
  · rw [hf _ (hmem hs) _ (hmem ht), sub_sub_sub_cancel_left, abs_sub_comm]
  · rw [← image_image f (a + b - ·), image_const_sub_Icc, add_sub_cancel_right,
      add_sub_cancel_left]

/-- In a segment, every distance up to the distance between two of its points is realised from
the first of them. -/
theorem exists_dist_eq (h : d.IsSegment σ x y) {u v : X} (hu : u ∈ σ) (hv : v ∈ σ) {r : Λ}
    (hr₀ : 0 ≤ r) (hr : r ≤ d u v) : ∃ w ∈ σ, d u w = r := by
  obtain ⟨f, -, -, hf, rfl⟩ := h
  obtain ⟨s, hs, rfl⟩ := hu
  obtain ⟨t, ht, rfl⟩ := hv
  rw [hf s hs t ht] at hr
  rcases le_total s t with hst | hts
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hst)] at hr
    have hmem : s + r ∈ Icc 0 (d x y) := ⟨by grind, by grind⟩
    exact ⟨f (s + r), mem_image_of_mem f hmem, by
      rw [hf s hs _ hmem, sub_add_cancel_left, abs_neg, abs_of_nonneg hr₀]⟩
  · rw [abs_of_nonneg (sub_nonneg.2 hts)] at hr
    have hmem : s - r ∈ Icc 0 (d x y) := ⟨by grind, by grind⟩
    exact ⟨f (s - r), mem_image_of_mem f hmem, by rw [hf s hs _ hmem, sub_sub_cancel,
      abs_of_nonneg hr₀]⟩

/-- A segment `ρ` contained in a segment `σ` and containing the endpoints of `σ` is equal to
`σ`. -/
theorem eq_of_subset {ρ : Set X} {p q : X} (hσ : d.IsSegment σ x y) (hρ : d.IsSegment ρ p q)
    (hsub : ρ ⊆ σ) (hx : x ∈ ρ) (hy : y ∈ ρ) : ρ = σ := by
  obtain ⟨f, hf0, hfD, hf, rfl⟩ := hσ
  obtain ⟨g, -, -, hg, rfl⟩ := hρ
  -- Write the parametrisation `g` of `ρ` as `f ∘ h`; then `h` is an isometric map of an interval
  -- into `Λ`, so its image is an interval, which contains both ends of `[0, d x y]`.
  have hfac : ∀ s ∈ Icc 0 (d p q), ∃ r ∈ Icc 0 (d x y), f r = g s :=
    fun s hs => hsub (mem_image_of_mem g hs)
  choose! h hhD hfh using hfac
  have hh : ∀ s ∈ Icc 0 (d p q), ∀ t ∈ Icc 0 (d p q), |h s - h t| = |s - t| :=
    fun s hs t ht => by rw [← hf _ (hhD s hs) _ (hhD t ht), hfh s hs, hfh t ht, hg s hs t ht]
  have himage := image_Icc_eq_uIcc_of_abs_sub_eq (d.nonneg p q) hh
  -- A point of `σ` lying in `ρ` has its parameter in the image of `h`.
  have hmem {r : Λ} (hr : r ∈ Icc 0 (d x y)) (hr' : f r ∈ g '' Icc 0 (d p q)) :
      r ∈ uIcc (h 0) (h (d p q)) := by
    obtain ⟨s, hs, hgs⟩ := hr'
    have : |h s - r| = 0 := by rw [← hf _ (hhD s hs) _ hr, hfh s hs, hgs, d.refl]
    rw [abs_eq_zero, sub_eq_zero] at this
    exact himage ▸ ⟨s, hs, this⟩
  have h0 := hmem ⟨le_rfl, d.nonneg x y⟩ (by rwa [hf0])
  have hD := hmem ⟨d.nonneg x y, le_rfl⟩ (by rwa [hfD])
  refine hsub.antisymm ?_
  rintro _ ⟨r, hr, rfl⟩
  have hr' : r ∈ uIcc (h 0) (h (d p q)) :=
    uIcc_subset_uIcc h0 hD (by rwa [uIcc_of_le (d.nonneg x y)])
  rw [← himage] at hr'
  obtain ⟨s, hs, rfl⟩ := hr'
  exact ⟨s, hs, (hfh s hs).symm⟩

/-- Along a parametrisation `f` of a segment from `x = f 0`, the point `f s` is at distance `s`
from `x`. -/
private theorem dist_apply_of_isometricOn {f : Λ → X} {D s : Λ} (hf0 : f 0 = x)
    (hf : d.IsometricOn f (Icc 0 D)) (hs : s ∈ Icc 0 D) : d x (f s) = s := by
  rw [← hf0, hf 0 ⟨le_rfl, hs.1.trans hs.2⟩ s hs, zero_sub, abs_neg, abs_of_nonneg hs.1]

/-- Two points of a segment from `x` are at distance the difference of their distances to `x`:
the distance from `x` is an isometry of the segment onto an interval of `Λ`. -/
theorem dist_eq_abs_sub (h : d.IsSegment σ x y) {u v : X} (hu : u ∈ σ) (hv : v ∈ σ) :
    d u v = |d x u - d x v| := by
  obtain ⟨f, hf0, -, hf, rfl⟩ := h
  obtain ⟨s, hs, rfl⟩ := hu
  obtain ⟨t, ht, rfl⟩ := hv
  rw [hf s hs t ht, dist_apply_of_isometricOn hf0 hf hs, dist_apply_of_isometricOn hf0 hf ht]

/-- A point of a segment from `x` to `y` lies between `x` and `y`. -/
theorem dist_add_dist (h : d.IsSegment σ x y) {u : X} (hu : u ∈ σ) : d x u + d u y = d x y := by
  obtain ⟨f, hf0, hfD, hf, rfl⟩ := h
  obtain ⟨s, hs, rfl⟩ := hu
  have h₂ : d (f s) y = d x y - s := by
    conv_lhs => rw [← hfD]
    rw [hf s hs _ ⟨d.nonneg x y, le_rfl⟩, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hs.2)]
  rw [dist_apply_of_isometricOn hf0 hf hs, h₂, add_sub_cancel]

/-- The part of a segment from `x` between two of its points `a` and `b`, that is, the set of its
points whose distance from `x` lies between those of `a` and `b`, is a segment from `a` to `b`. -/
theorem isSegment_sep (h : d.IsSegment σ x y) {a b : X} (ha : a ∈ σ) (hb : b ∈ σ) :
    d.IsSegment {u ∈ σ | d x u ∈ uIcc (d x a) (d x b)} a b := by
  obtain ⟨f, hf0, -, hf, rfl⟩ := h
  have hdist {s : Λ} (hs : s ∈ Icc 0 (d x y)) : d x (f s) = s := dist_apply_of_isometricOn hf0 hf hs
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  have hsub : uIcc s t ⊆ Icc 0 (d x y) := uIcc_subset_Icc hs ht
  have heq : {u ∈ f '' Icc 0 (d x y) | d x u ∈ uIcc (d x (f s)) (d x (f t))} = f '' uIcc s t := by
    rw [hdist hs, hdist ht]
    ext u
    constructor
    · rintro ⟨⟨r, hr, rfl⟩, hr'⟩
      rw [hdist hr] at hr'
      exact ⟨r, hr', rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hsub hr, rfl⟩, by rwa [hdist (hsub hr)]⟩
  rw [heq]
  rcases le_total s t with hst | hts
  · rw [uIcc_of_le hst] at hsub ⊢
    exact isSegment_iff_exists_Icc.2 ⟨s, t, f, hst, rfl, rfl, hf.mono hsub, rfl⟩
  · rw [uIcc_of_ge hts] at hsub ⊢
    exact (isSegment_iff_exists_Icc.2 ⟨t, s, f, hts, rfl, rfl, hf.mono hsub, rfl⟩).symm

end IsSegment

theorem isSegment_comm {σ : Set X} {x y : X} : d.IsSegment σ x y ↔ d.IsSegment σ y x :=
  ⟨IsSegment.symm, IsSegment.symm⟩

/-- The only segment from a point to itself is the singleton. -/
@[simp]
theorem isSegment_self_iff {σ : Set X} {x : X} : d.IsSegment σ x x ↔ σ = {x} := by
  simp only [IsSegment, d.refl, Icc_self, image_singleton]
  refine ⟨fun ⟨f, h0, _, _, hσ⟩ => by rw [← hσ, h0], fun h => ⟨fun _ => x, rfl, rfl, ?_, h.symm⟩⟩
  rintro a rfl b rfl
  simp

/-! ### Short segments in `ℤ`-metric spaces -/

section Int

variable {d : LambdaMetric ℤ X}

/-- Two points at distance `1` in a `ℤ`-metric space form a segment. -/
theorem isSegment_pair {x y : X} (h : d x y = 1) : d.IsSegment {x, y} x y := by
  have hI : Icc (0 : ℤ) 1 = {0, 1} := by
    ext t
    simp only [mem_Icc, mem_insert_iff, mem_singleton_iff]
    omega
  refine ⟨fun t => if t ≤ 0 then x else y, by simp, by simp [h], ?_, ?_⟩
  · rw [h, hI]
    rintro s (rfl | rfl) t (rfl | rfl) <;> simp [h, d.symm y x]
  · rw [h, hI, image_pair]
    simp

/-- Three points `x, m, y` with `d x m = d m y = 1` and `d x y = 2` in a `ℤ`-metric space form a
segment. -/
theorem isSegment_triple {x m y : X} (hxm : d x m = 1) (hmy : d m y = 1)
    (hxy : d x y = 2) : d.IsSegment {x, m, y} x y := by
  have hI : Icc (0 : ℤ) 2 = {0, 1, 2} := by
    ext t
    simp only [mem_Icc, mem_insert_iff, mem_singleton_iff]
    omega
  refine ⟨fun t => if t ≤ 0 then x else if t ≤ 1 then m else y, by simp, by simp [hxy], ?_, ?_⟩
  · rw [hxy, hI]
    rintro s (rfl | rfl | rfl) t (rfl | rfl | rfl) <;>
      simp [hxm, hmy, hxy, d.symm m x, d.symm y m, d.symm y x]
  · rw [hxy, hI, image_insert_eq, image_pair]
    simp

end Int

/-- `d` is geodesic: any two points are joined by a segment. -/
def IsGeodesic (d : LambdaMetric Λ X) : Prop :=
  ∀ x y : X, ∃ σ, d.IsSegment σ x y

theorem isGeodesic_iff : d.IsGeodesic ↔ ∀ x y : X, ∃ σ, d.IsSegment σ x y :=
  Iff.rfl

/-- `d` makes `X` a `Λ`-tree: `X` is nonempty and geodesic, two segments meeting only in a common
endpoint have a segment as union (T2), and two segments with a common endpoint intersect in a
segment (T3). -/
structure IsTree (d : LambdaMetric Λ X) : Prop where
  nonempty : Nonempty X
  isGeodesic : d.IsGeodesic
  exists_isSegment_union {σ τ : Set X} {x y z : X} :
    d.IsSegment σ x y → d.IsSegment τ y z → σ ∩ τ = {y} → ∃ p q, d.IsSegment (σ ∪ τ) p q
  exists_isSegment_inter {σ τ : Set X} {x y z : X} :
    d.IsSegment σ x y → d.IsSegment τ x z → ∃ p q, d.IsSegment (σ ∩ τ) p q

/-- In a `Λ`-tree, two points are joined by a unique segment. -/
theorem IsTree.isSegment_unique (hd : d.IsTree) {σ τ : Set X} {x y : X}
    (hσ : d.IsSegment σ x y) (hτ : d.IsSegment τ x y) : σ = τ := by
  obtain ⟨p, q, hστ⟩ := hd.exists_isSegment_inter hσ hτ
  have hx : x ∈ σ ∩ τ := ⟨hσ.left_mem, hτ.left_mem⟩
  have hy : y ∈ σ ∩ τ := ⟨hσ.right_mem, hτ.right_mem⟩
  exact (hσ.eq_of_subset hστ inter_subset_left hx hy).symm.trans
    (hτ.eq_of_subset hστ inter_subset_right hx hy)

/-- The segment `[x, y]` in a `Λ`-tree, unique by
`TauCeti.LambdaMetric.IsTree.isSegment_unique`. -/
noncomputable def IsTree.segment (hd : d.IsTree) (x y : X) : Set X :=
  (hd.isGeodesic x y).choose

theorem IsTree.isSegment_segment (hd : d.IsTree) (x y : X) : d.IsSegment (hd.segment x y) x y :=
  (hd.isGeodesic x y).choose_spec

/-- In a `Λ`-tree, the segments from `x` to `y` are exactly `[x, y]`. -/
theorem IsTree.isSegment_iff_eq_segment (hd : d.IsTree) {σ : Set X} {x y : X} :
    d.IsSegment σ x y ↔ σ = hd.segment x y :=
  ⟨fun h => hd.isSegment_unique h (hd.isSegment_segment x y),
    fun h => h ▸ hd.isSegment_segment x y⟩

@[simp]
theorem IsTree.left_mem_segment (hd : d.IsTree) (x y : X) : x ∈ hd.segment x y :=
  (hd.isSegment_segment x y).left_mem

@[simp]
theorem IsTree.right_mem_segment (hd : d.IsTree) (x y : X) : y ∈ hd.segment x y :=
  (hd.isSegment_segment x y).right_mem

@[simp]
theorem IsTree.segment_self (hd : d.IsTree) (x : X) : hd.segment x x = {x} :=
  isSegment_self_iff.1 (hd.isSegment_segment x x)

theorem IsTree.segment_comm (hd : d.IsTree) (x y : X) : hd.segment x y = hd.segment y x :=
  hd.isSegment_unique (hd.isSegment_segment x y) (hd.isSegment_segment y x).symm

/-- In a `Λ`-tree, the segment between two points `a` and `b` of a segment `σ` from `x` is the
part of `σ` between them. -/
theorem IsTree.segment_eq_sep (hd : d.IsTree) {σ : Set X} {x y a b : X} (hσ : d.IsSegment σ x y)
    (ha : a ∈ σ) (hb : b ∈ σ) : hd.segment a b = {u ∈ σ | d x u ∈ uIcc (d x a) (d x b)} :=
  (hd.isSegment_iff_eq_segment.1 (hσ.isSegment_sep ha hb)).symm

/-- In a `Λ`-tree, a segment contains the segment between any two of its points. -/
theorem IsTree.segment_subset (hd : d.IsTree) {σ : Set X} {x y a b : X} (hσ : d.IsSegment σ x y)
    (ha : a ∈ σ) (hb : b ∈ σ) : hd.segment a b ⊆ σ := by
  rw [hd.segment_eq_sep hσ ha hb]
  exact sep_subset _ _

/-! ### Induced metrics -/

section Comap

variable {Y : Type*} (d) (f : Y → X) (hf : Function.Injective f)

/-- The `Λ`-metric `d (f x) (f y)` induced on `Y` by an injective map `f : Y → X`. -/
def comap : LambdaMetric Λ Y where
  toFun x y := d (f x) (f y)
  refl' x := d.refl (f x)
  symm' x y := d.symm (f x) (f y)
  triangle' x y z := d.triangle (f x) (f y) (f z)
  eq_of_eq_zero' h := hf (d.eq_zero_iff.1 h)

@[simp]
theorem comap_apply (x y : Y) : d.comap f hf x y = d (f x) (f y) :=
  (rfl)

variable {d f hf}

/-- A subset of `Y` is a segment for the metric induced by `f : Y → X` if and only if its image
under `f` is a segment of `X`. -/
theorem isSegment_comap_iff {σ : Set Y} {x y : Y} :
    (d.comap f hf).IsSegment σ x y ↔ d.IsSegment (f '' σ) (f x) (f y) := by
  constructor
  · rintro ⟨g, rfl, hg1, hg, rfl⟩
    rw [comap_apply] at hg1 hg
    exact ⟨f ∘ g, rfl, congrArg f hg1, hg, image_comp f g _⟩
  · rintro ⟨h, h0, h1, hh, hσ⟩
    have : Nonempty Y := ⟨x⟩
    have hD : (0 : Λ) ≤ d (f x) (f y) := d.nonneg _ _
    -- Lift the parametrisation `h` of `f '' σ` through `f`.
    have hlift : ∀ t ∈ Icc 0 (d (f x) (f y)), ∃ u ∈ σ, f u = h t := fun t ht =>
      hσ.subset (mem_image_of_mem h ht)
    choose! g hgσ hfg using hlift
    refine ⟨g, hf ?_, hf ?_, fun s hs t ht => ?_, (image_subset_iff.2 hgσ).antisymm fun u hu => ?_⟩
    · rw [hfg 0 ⟨le_rfl, hD⟩, h0]
    · rw [comap_apply, hfg _ ⟨hD, le_rfl⟩, h1]
    · rw [comap_apply] at hs ht
      rw [comap_apply, hfg s hs, hfg t ht, hh s hs t ht]
    · obtain ⟨t, ht, htu⟩ := hσ.superset (mem_image_of_mem f hu)
      exact ⟨t, ht, hf ((hfg t ht).trans htu)⟩

/-- A subset of `Y` whose image under `f : Y → X` is a segment of `X` is a segment for the metric
induced by `f`, between the preimages of the endpoints. -/
theorem exists_isSegment_comap_of_image {σ : Set Y} {p q : X} (h : d.IsSegment (f '' σ) p q) :
    ∃ x y, (d.comap f hf).IsSegment σ x y := by
  obtain ⟨x, -, rfl⟩ := h.left_mem
  obtain ⟨y, -, rfl⟩ := h.right_mem
  exact ⟨x, y, isSegment_comap_iff.2 h⟩

/-- The metric induced by `f : Y → X` is geodesic if and only if any two points of the range of
`f` are joined by a segment contained in the range of `f`. -/
theorem isGeodesic_comap_iff :
    (d.comap f hf).IsGeodesic ↔ ∀ x y : Y, ∃ τ ⊆ range f, d.IsSegment τ (f x) (f y) := by
  refine forall₂_congr fun x y => ⟨fun ⟨σ, hσ⟩ => ⟨_, image_subset_range f σ,
    isSegment_comap_iff.1 hσ⟩, fun ⟨τ, hτ, h⟩ => ⟨f ⁻¹' τ, isSegment_comap_iff.2 ?_⟩⟩
  rwa [image_preimage_eq_of_subset hτ]

namespace IsTree

variable (hd : d.IsTree)
include hd

/-- The metric induced on `Y` by a map `f` into a `Λ`-tree is geodesic if and only if the range of
`f` contains the segment between any two of its points. -/
theorem isGeodesic_comap_iff_segment_subset :
    (d.comap f hf).IsGeodesic ↔ ∀ x y : Y, hd.segment (f x) (f y) ⊆ range f := by
  rw [isGeodesic_comap_iff]
  refine forall₂_congr fun x y => ⟨fun ⟨τ, hτ, h⟩ => ?_, fun h => ⟨_, h, hd.isSegment_segment _ _⟩⟩
  rwa [← hd.isSegment_iff_eq_segment.1 h]

/-- A geodesic metric induced by a map into a `Λ`-tree makes its domain, if nonempty, a
`Λ`-tree: the axioms (T2) and (T3) are inherited. -/
theorem comap [Nonempty Y] (h : (d.comap f hf).IsGeodesic) : (d.comap f hf).IsTree where
  nonempty := ‹_›
  isGeodesic := h
  exists_isSegment_union {σ τ x y z} hσ hτ hστ := by
    rw [isSegment_comap_iff] at hσ hτ
    obtain ⟨p, q, hpq⟩ := hd.exists_isSegment_union hσ hτ
      (by rw [← image_inter hf, hστ, image_singleton])
    exact exists_isSegment_comap_of_image (image_union f σ τ ▸ hpq)
  exists_isSegment_inter {σ τ x y z} hσ hτ := by
    rw [isSegment_comap_iff] at hσ hτ
    obtain ⟨p, q, hpq⟩ := hd.exists_isSegment_inter hσ hτ
    exact exists_isSegment_comap_of_image (image_inter hf ▸ hpq)

/-- The metric induced on `Y` by an injective map `f` into a `Λ`-tree makes `Y` a `Λ`-tree if and
only if `Y` is nonempty and the range of `f` contains the segment between any two of its
points. -/
theorem isTree_comap_iff :
    (d.comap f hf).IsTree ↔ Nonempty Y ∧ ∀ x y : Y, hd.segment (f x) (f y) ⊆ range f := by
  rw [← hd.isGeodesic_comap_iff_segment_subset (hf := hf)]
  exact ⟨fun h => ⟨h.nonempty, h.isGeodesic⟩, fun ⟨_, h⟩ => hd.comap h⟩

end IsTree

end Comap

/-! ### Examples -/

/-- The segments of `Λ` are its closed intervals. -/
theorem self_isSegment_iff {σ : Set Λ} {a b : Λ} : (self Λ).IsSegment σ a b ↔ σ = uIcc a b := by
  refine ⟨fun ⟨f, h0, h1, hf, hσ⟩ => ?_, ?_⟩
  · rw [← hσ, image_Icc_eq_uIcc_of_abs_sub_eq ((self Λ).nonneg a b)
      fun s hs t ht => (self_apply _ _).symm.trans (hf s hs t ht), h0, h1]
  rintro rfl
  rw [isSegment_iff_exists_Icc]
  rcases le_total a b with hab | hba
  · exact ⟨a, b, id, hab, rfl, rfl, fun s _ t _ => self_apply s t,
      by rw [image_id, uIcc_of_le hab]⟩
  · refine ⟨b, a, fun s => a + b - s, hba, by simp, by simp, fun s _ t _ => ?_, ?_⟩
    · rw [self_apply, sub_sub_sub_cancel_left, abs_sub_comm]
    · rw [image_const_sub_Icc, add_sub_cancel_right, add_sub_cancel_left, uIcc_of_ge hba]

/-- `Λ`, with the metric `|a - b|`, is a `Λ`-tree. -/
theorem isTree_self : (self Λ).IsTree where
  nonempty := ⟨0⟩
  isGeodesic x y := ⟨_, self_isSegment_iff.2 rfl⟩
  exists_isSegment_union {σ τ x y z} hσ hτ hστ := by
    rw [self_isSegment_iff] at hσ hτ
    subst hσ hτ
    -- Two intervals `[[x, y]]` and `[[y, z]]` meeting only in `y` lie on either side of `y`:
    -- otherwise `max x z` or `min x z` would be a second common point.
    have key (w : Λ) (h₁ : w ∈ uIcc x y) (h₂ : w ∈ uIcc y z) : w = y := by
      rw [← mem_singleton_iff, ← hστ]
      exact ⟨h₁, h₂⟩
    have k₁ := key (max x z)
    have k₂ := key (min x z)
    refine ⟨x, z, self_isSegment_iff.2 ?_⟩
    ext w
    simp only [mem_union, mem_uIcc] at k₁ k₂ ⊢
    grind
  exists_isSegment_inter {σ τ x y z} hσ hτ := by
    rw [self_isSegment_iff] at hσ hτ
    subst hσ hτ
    -- The intersection is `[[x, w]]`, where `w` is the nearer of `y` and `z` to `x` if they lie
    -- on the same side of `x`, and `x` itself otherwise.
    rcases le_total x y with h₁ | h₁ <;> rcases le_total x z with h₂ | h₂ <;>
      [refine ⟨x, min y z, ?_⟩; refine ⟨x, x, ?_⟩; refine ⟨x, x, ?_⟩; refine ⟨x, max y z, ?_⟩] <;>
    · rw [self_isSegment_iff]
      ext w
      simp only [mem_inter_iff, mem_uIcc]
      grind

/-- The segment between two points of the `Λ`-tree `Λ` is the closed interval between them. -/
@[simp]
theorem segment_isTree_self (a b : Λ) : (isTree_self (Λ := Λ)).segment a b = uIcc a b :=
  (isTree_self.isSegment_iff_eq_segment.1 (self_isSegment_iff.2 rfl)).symm

/-- The metric `|f x - f y|` induced on `Y` by an injective map `f : Y → Λ` makes `Y` a `Λ`-tree
if and only if `Y` is nonempty and the range of `f` is order-connected. -/
theorem isTree_comap_self_iff {Y : Type*} {f : Y → Λ} {hf : Function.Injective f} :
    ((self Λ).comap f hf).IsTree ↔ Nonempty Y ∧ (range f).OrdConnected := by
  simp [isTree_self.isTree_comap_iff, ordConnected_iff_uIcc_subset]

/-- A subset of `Λ`, with the metric `|a - b|`, is a `Λ`-tree if and only if it is nonempty and
order-connected. -/
theorem isTree_comap_self_subtype_iff {s : Set Λ} :
    ((self Λ).comap ((↑) : s → Λ) Subtype.val_injective).IsTree ↔ s.Nonempty ∧ s.OrdConnected := by
  rw [isTree_comap_self_iff, Subtype.range_coe, nonempty_coe_sort]

/-- `Λ` acts on the `Λ`-tree `Λ` by translations, which are isometries. -/
theorem isIsometricAction_self : (self Λ).IsIsometricAction (Multiplicative Λ) := by
  intro a x y
  obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective a
  simp [self_apply]

/-- A one-point space is a `Λ`-tree, for its unique `Λ`-metric. -/
theorem isTree_of_subsingleton [Nonempty X] [Subsingleton X] : d.IsTree where
  nonempty := ‹_›
  isGeodesic x y := ⟨{x}, Subsingleton.elim x y ▸ isSegment_self_iff.2 rfl⟩
  exists_isSegment_union {σ τ x y z} hσ hτ _ := by
    obtain rfl := Subsingleton.elim x y
    obtain rfl := Subsingleton.elim x z
    rw [isSegment_self_iff] at hσ hτ
    exact ⟨x, x, isSegment_self_iff.2 (by rw [hσ, hτ, union_self])⟩
  exists_isSegment_inter {σ τ x y z} hσ hτ := by
    obtain rfl := Subsingleton.elim x y
    obtain rfl := Subsingleton.elim x z
    rw [isSegment_self_iff] at hσ hτ
    exact ⟨x, x, isSegment_self_iff.2 (by rw [hσ, hτ, inter_self])⟩

/-! ### A geodesic `ℤ`-metric space which is not a `ℤ`-tree -/

/-- The path metric on the vertices `0, 1, 2, 3` of a cycle of length four. -/
private def cycleFour : LambdaMetric ℤ (Fin 4) where
  toFun i j := if i = j then 0 else if i - j = 2 then 2 else 1
  refl' i := by simp
  symm' := by decide
  triangle' := by decide
  eq_of_eq_zero' {i j} := by revert i j; decide

/-- A geodesic `Λ`-metric space need not be a `Λ`-tree: the vertices of a cycle of length four,
with the path metric, form a geodesic `ℤ`-metric space in which the two segments `{0, 1, 2}` and
`{0, 3, 2}` from `0` to `2` meet in `{0, 2}`, which is not a segment, so (T3) fails. -/
theorem exists_isGeodesic_not_isTree : ∃ d : LambdaMetric ℤ (Fin 4), d.IsGeodesic ∧ ¬d.IsTree := by
  have hdist : ∀ x y : Fin 4, x = y ∨ cycleFour x y = 1 ∨
      (cycleFour x (x + 1) = 1 ∧ cycleFour (x + 1) y = 1 ∧ cycleFour x y = 2) := by
    decide
  refine ⟨cycleFour, fun x y => ?_, fun hd => ?_⟩
  · rcases hdist x y with rfl | h | ⟨h₁, h₂, h₃⟩
    · exact ⟨_, isSegment_self_iff.2 rfl⟩
    · exact ⟨_, isSegment_pair h⟩
    · exact ⟨_, isSegment_triple h₁ h₂ h₃⟩
  · have hσ : cycleFour.IsSegment {0, 1, 2} 0 2 := isSegment_triple (by decide) (by decide)
      (by decide)
    have hτ : cycleFour.IsSegment {0, 3, 2} 0 2 := isSegment_triple (by decide) (by decide)
      (by decide)
    obtain ⟨p, q, h⟩ := hd.exists_isSegment_inter hσ hτ
    -- A segment containing `0` and `2` contains a point at distance `1` from `0`.
    obtain ⟨w, ⟨hw₁, hw₂⟩, hw⟩ := h.exists_dist_eq (u := 0) (v := 2) ⟨hσ.left_mem, hτ.left_mem⟩
      ⟨hσ.right_mem, hτ.right_mem⟩ zero_le_one (by decide)
    simp only [mem_insert_iff, mem_singleton_iff] at hw₁ hw₂
    rcases hw₁ with rfl | rfl | rfl <;> revert hw hw₂ <;> decide

end LambdaMetric

end TauCeti
