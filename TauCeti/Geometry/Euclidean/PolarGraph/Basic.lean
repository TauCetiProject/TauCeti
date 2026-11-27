/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Deck transformations and separation of polar graphs

Positive polar radius and an unrestricted real angle model the universal cover of the
punctured Euclidean plane. The map `projection` sends a polar point to the plane, and
`projection_eq_iff` characterizes its fibers by the integral angular translations `deckShift`.

A height function on this cover describes a multi-valued graph over the punctured plane.
The parametrization `graph` is injective on a domain exactly when its distinct deck sheets
have nonzero height `separation`, as expressed by `graph_injOn_iff`. The domain on which both
a point and its translate lie is `overlap`; for angular domains, `overlap_sector` computes
its bounds. Separation satisfies a cocycle identity, and heights invariant under a full
turn have zero separation and identify distinct sheets of the polar cover.

## References

* T. H. Colding and W. P. Minicozzi II, *The space of embedded minimal surfaces of fixed
  genus in a 3-manifold IV*, Section 0.
-/

public noncomputable section

namespace TauCeti.PolarGraph

/-- Polar coordinates with positive radius and an unrestricted real angle. -/
abbrev PolarPoint := {p : ℝ × ℝ // 0 < p.1}

/-- The radius of a point in the polar coordinate cover. -/
def radius (p : PolarPoint) : ℝ := p.val.1

/-- The angle of a point in the polar coordinate cover. -/
def angle (p : PolarPoint) : ℝ := p.val.2

theorem radius_def (p : PolarPoint) : radius p = p.val.1 := (rfl)

theorem angle_def (p : PolarPoint) : angle p = p.val.2 := (rfl)

@[simp, grind =] theorem radius_mk (r θ : ℝ) (hr : 0 < r) :
    radius ⟨(r, θ), hr⟩ = r := (rfl)

@[simp, grind =] theorem angle_mk (r θ : ℝ) (hr : 0 < r) :
    angle ⟨(r, θ), hr⟩ = θ := (rfl)

@[simp] theorem radius_pos (p : PolarPoint) : 0 < radius p := p.property

@[simp] theorem radius_ne_zero (p : PolarPoint) : radius p ≠ 0 := ne_of_gt (radius_pos p)

/-- Polar points are determined by their radius and unrestricted angle. -/
theorem PolarPoint.ext {p q : PolarPoint} (hr : radius p = radius q)
    (ha : angle p = angle q) : p = q :=
  Subtype.ext (Prod.ext hr ha)

/-- Translation by `2πk` in the angular coordinate. -/
def deckShift (k : ℤ) (p : PolarPoint) : PolarPoint :=
  ⟨(radius p, angle p + (k : ℝ) * (2 * Real.pi)), radius_pos p⟩

@[simp, grind =] theorem radius_deckShift (k : ℤ) (p : PolarPoint) :
    radius (deckShift k p) = radius p := (rfl)

@[simp, grind =] theorem angle_deckShift (k : ℤ) (p : PolarPoint) :
    angle (deckShift k p) = angle p + (k : ℝ) * (2 * Real.pi) := (rfl)

/-- A deck shift is translation by a constant vector in the coordinates of the cover. -/
theorem val_deckShift (k : ℤ) (p : PolarPoint) :
    (deckShift k p).val = p.val + (0, (k : ℝ) * (2 * Real.pi)) := by
  exact Prod.ext (by simp [deckShift, radius_def]) (by simp [deckShift, angle_def])

@[simp, grind =] theorem deckShift_zero (p : PolarPoint) : deckShift 0 p = p := by
  apply PolarPoint.ext <;> simp

@[grind =] theorem deckShift_add (k l : ℤ) (p : PolarPoint) :
    deckShift (k + l) p = deckShift l (deckShift k p) := by
  apply PolarPoint.ext
  · simp
  · simp only [angle_deckShift, Int.cast_add]
    ring

@[simp, grind =] theorem deckShift_neg_deckShift (k : ℤ) (p : PolarPoint) :
    deckShift (-k) (deckShift k p) = p := by
  rw [← deckShift_add, add_neg_cancel, deckShift_zero]

@[simp, grind =] theorem deckShift_deckShift_neg (k : ℤ) (p : PolarPoint) :
    deckShift k (deckShift (-k) p) = p := by
  rw [← deckShift_add, neg_add_cancel, deckShift_zero]

@[simp, grind =] theorem deckShift_left_inj {k l : ℤ} {p : PolarPoint} :
    deckShift k p = deckShift l p ↔ k = l := by
  constructor
  · intro h
    have ha := congrArg angle h
    simp only [angle_deckShift, add_right_inj] at ha
    exact_mod_cast mul_right_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero) ha
  · rintro rfl
    rfl

@[simp, grind =] theorem deckShift_right_inj {k : ℤ} {p q : PolarPoint} :
    deckShift k p = deckShift k q ↔ p = q := by
  constructor
  · intro h
    simpa only [deckShift_neg_deckShift] using congrArg (deckShift (-k)) h
  · rintro rfl
    rfl

/-- Only the zero deck translation fixes a polar point. -/
@[simp] theorem deckShift_eq_self_iff {k : ℤ} {p : PolarPoint} :
    deckShift k p = p ↔ k = 0 := by
  simpa only [deckShift_zero] using (deckShift_left_inj (k := k) (l := 0) (p := p))

/-- The image of a polar point in the punctured complex plane. -/
def projection (p : PolarPoint) : ℂ :=
  (radius p : ℂ) * (Circle.exp (angle p) : ℂ)

theorem projection_def (p : PolarPoint) :
    projection p = (radius p : ℂ) * (Circle.exp (angle p) : ℂ) := (rfl)

@[simp, grind =] theorem re_projection (p : PolarPoint) :
    (projection p).re = radius p * Real.cos (angle p) := by
  simp [projection_def, Circle.coe_exp]

@[simp, grind =] theorem im_projection (p : PolarPoint) :
    (projection p).im = radius p * Real.sin (angle p) := by
  simp [projection_def, Circle.coe_exp]

@[simp, grind =] theorem projection_deckShift (k : ℤ) (p : PolarPoint) :
    projection (deckShift k p) = projection p := by
  have h : Circle.exp (angle p + (k : ℝ) * (2 * Real.pi)) = Circle.exp (angle p) :=
    Circle.exp_eq_exp.mpr ⟨k, rfl⟩
  simp [projection_def, h]

/-- The Euclidean norm of the projection is the polar radius. -/
@[simp, grind =] theorem norm_projection (p : PolarPoint) : ‖projection p‖ = radius p := by
  simp [projection_def, Complex.norm_real, abs_of_pos (radius_pos p)]

/-- The polar projection avoids the origin. -/
@[simp] theorem projection_ne_zero (p : PolarPoint) : projection p ≠ 0 := by
  have h : 0 < ‖projection p‖ := by rw [norm_projection]; exact radius_pos p
  exact norm_pos_iff.mp h

/-- Two polar points have the same planar projection exactly when one is an integral deck
translate of the other. -/
theorem projection_eq_iff (p q : PolarPoint) :
    projection p = projection q ↔ ∃ k : ℤ, q = deckShift k p := by
  constructor
  · intro h
    have hr : radius p = radius q := by
      have hn := congrArg norm h
      simpa only [norm_projection] using hn
    have hc' : (Circle.exp (angle p) : ℂ) = (Circle.exp (angle q) : ℂ) := by
      have hz : (radius q : ℂ) ≠ 0 := by exact_mod_cast radius_ne_zero q
      exact mul_left_cancel₀ hz (by simpa [projection_def, hr] using h)
    have hc : Circle.exp (angle p) = Circle.exp (angle q) := Circle.ext hc'
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hc.symm
    refine ⟨k, PolarPoint.ext ?_ ?_⟩
    · simpa using hr.symm
    · simpa using hk
  · rintro ⟨k, rfl⟩
    exact (projection_deckShift k p).symm

/-- Points of a parameter domain whose `k`-th deck translate also lies in the domain. -/
def overlap (Ω : Set PolarPoint) (k : ℤ) : Set PolarPoint :=
  {p | p ∈ Ω ∧ deckShift k p ∈ Ω}

@[simp, grind =] theorem mem_overlap_iff {Ω : Set PolarPoint} {k : ℤ} {p : PolarPoint} :
    p ∈ overlap Ω k ↔ p ∈ Ω ∧ deckShift k p ∈ Ω := Iff.rfl

/-- The zero deck overlap is the original domain. -/
@[simp, grind =] theorem overlap_zero (Ω : Set PolarPoint) : overlap Ω 0 = Ω := by
  ext p
  simp

@[simp, grind =] theorem overlap_empty (k : ℤ) : overlap ∅ k = ∅ := by
  ext p
  simp

@[simp, grind =] theorem overlap_univ (k : ℤ) : overlap Set.univ k = Set.univ := by
  ext p
  simp

theorem overlap_subset (Ω : Set PolarPoint) (k : ℤ) : overlap Ω k ⊆ Ω :=
  fun _ hp ↦ (mem_overlap_iff.mp hp).1

/-- The open polar sector with angular bounds `a < angle p < b`. -/
def sector (a b : ℝ) : Set PolarPoint := {p | a < angle p ∧ angle p < b}

@[simp, grind =] theorem mem_sector_iff {a b : ℝ} {p : PolarPoint} :
    p ∈ sector a b ↔ a < angle p ∧ angle p < b := Iff.rfl

/-- The points of an angular sector whose `k`-th deck translate stays in the sector. -/
@[grind =] theorem overlap_sector (a b : ℝ) (k : ℤ) :
    overlap (sector a b) k =
      sector (max a (a - k * (2 * Real.pi))) (min b (b - k * (2 * Real.pi))) := by
  ext p
  simp only [mem_overlap_iff, mem_sector_iff, angle_deckShift, max_lt_iff, lt_min_iff]
  constructor <;> rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ <;>
    constructor <;> constructor <;> linarith

/-- For a nonnegative deck shift, only the upper bound of the sector decreases. -/
theorem overlap_sector_of_nonneg {a b : ℝ} {k : ℤ} (hk : 0 ≤ k) :
    overlap (sector a b) k = sector a (b - k * (2 * Real.pi)) := by
  have hs : 0 ≤ (k : ℝ) * (2 * Real.pi) :=
    mul_nonneg (by exact_mod_cast hk) (by positivity)
  rw [overlap_sector, max_eq_left (by linarith), min_eq_right (by linarith)]

/-- The height change `u (deckShift k p) - u p` from `p` to its `k`-th deck translate. -/
def separation (u : PolarPoint → ℝ) (k : ℤ) (p : PolarPoint) : ℝ :=
  u (deckShift k p) - u p

theorem separation_def (u : PolarPoint → ℝ) (k : ℤ) (p : PolarPoint) :
    separation u k p = u (deckShift k p) - u p := (rfl)

@[simp, grind =] theorem separation_zero (u : PolarPoint → ℝ) (p : PolarPoint) :
    separation u 0 p = 0 := by
  simp [separation_def]

@[simp] theorem separation_const (c : ℝ) (k : ℤ) (p : PolarPoint) :
    separation (fun _ ↦ c) k p = 0 := by
  simp [separation_def]

/-- The separation cocycle: the second height change is evaluated at `deckShift k p`. -/
@[grind =] theorem separation_add (u : PolarPoint → ℝ) (k l : ℤ) (p : PolarPoint) :
    separation u (k + l) p = separation u k p + separation u l (deckShift k p) := by
  simp [separation_def, deckShift_add]

/-- Reversing a deck shift from `deckShift k p` negates its height change from `p`. -/
@[simp, grind =] theorem separation_neg_deckShift (u : PolarPoint → ℝ) (k : ℤ)
    (p : PolarPoint) : separation u (-k) (deckShift k p) = -separation u k p := by
  simp [separation_def, sub_eq_add_neg, add_comm]

/-- One-turn invariance along a point's deck orbit makes every separation at that point zero. -/
theorem separation_eq_zero_of_deckShift_one_deckShift_eq {u : PolarPoint → ℝ} {p : PolarPoint}
    (hu : ∀ m : ℤ, u (deckShift 1 (deckShift m p)) = u (deckShift m p)) (k : ℤ) :
    separation u k p = 0 := by
  have hp : Function.Periodic (fun m : ℤ ↦ u (deckShift m p)) 1 := fun m ↦ by
    simpa only [deckShift_add] using hu m
  simpa [separation_def, sub_eq_zero] using hp.zsmul_eq k

/-- A height invariant under one full turn has zero separation under every deck shift. -/
theorem separation_eq_zero_of_deckShift_one_eq {u : PolarPoint → ℝ}
    (hu : ∀ p, u (deckShift 1 p) = u p) (k : ℤ) (p : PolarPoint) :
    separation u k p = 0 :=
  separation_eq_zero_of_deckShift_one_deckShift_eq (fun _ ↦ hu _) k

/-- The surface parametrization of a polar height function. -/
def graph (u : PolarPoint → ℝ) (p : PolarPoint) : ℂ × ℝ := (projection p, u p)

theorem graph_def (u : PolarPoint → ℝ) (p : PolarPoint) :
    graph u p = (projection p, u p) := (rfl)

@[simp, grind =] theorem fst_graph (u : PolarPoint → ℝ) (p : PolarPoint) :
    (graph u p).1 = projection p := (rfl)

@[simp, grind =] theorem snd_graph (u : PolarPoint → ℝ) (p : PolarPoint) :
    (graph u p).2 = u p := (rfl)

/-- A polar graph is injectively parametrized on a domain exactly when every nontrivial
deck overlap has nonzero height separation. -/
theorem graph_injOn_iff (u : PolarPoint → ℝ) (Ω : Set PolarPoint) :
    Set.InjOn (graph u) Ω ↔
      ∀ k : ℤ, k ≠ 0 → ∀ p ∈ overlap Ω k, separation u k p ≠ 0 := by
  constructor
  · intro hi k hk p hp hs
    rw [mem_overlap_iff] at hp
    rw [separation_def, sub_eq_zero] at hs
    have heq : graph u p = graph u (deckShift k p) := by
      simp [graph_def, hs]
    exact hk (deckShift_eq_self_iff.mp (hi hp.1 hp.2 heq).symm)
  · intro hs p hp q hq heq
    have hproj : projection p = projection q := by
      simpa only [fst_graph] using congrArg Prod.fst heq
    obtain ⟨k, rfl⟩ := (projection_eq_iff p q).mp hproj
    by_cases hk : k = 0
    · subst k
      exact (deckShift_zero p).symm
    · have hu : u p = u (deckShift k p) := by
        simpa only [snd_graph] using congrArg Prod.snd heq
      exact False.elim (hs k hk p (mem_overlap_iff.mpr ⟨hp, hq⟩)
        (by simp [separation_def, hu]))

/-- Equal heights at distinct deck translates in a domain obstruct injectivity on that domain. -/
theorem not_injOn_graph_of_deckShift_eq {u : PolarPoint → ℝ} {Ω : Set PolarPoint} {k : ℤ}
    (hk : k ≠ 0) {p : PolarPoint} (hp : p ∈ overlap Ω k)
    (hu : u (deckShift k p) = u p) : ¬ Set.InjOn (graph u) Ω :=
  fun h ↦ (graph_injOn_iff u Ω).mp h k hk p hp (by simp [separation_def, hu])

/-- Equal heights at one pair of distinct deck translates obstruct global injectivity. -/
theorem not_injective_graph_of_deckShift_eq {u : PolarPoint → ℝ} {k : ℤ}
    (hk : k ≠ 0) {p : PolarPoint} (hu : u (deckShift k p) = u p) :
    ¬ Function.Injective (graph u) := by
  rw [← Set.injOn_univ]
  exact not_injOn_graph_of_deckShift_eq hk (by simp) hu

/-- A constant-height polar graph identifies points on different deck sheets. -/
theorem not_injective_graph_const (c : ℝ) :
    ¬ Function.Injective (graph (fun _ : PolarPoint ↦ c)) := by
  let p : PolarPoint := ⟨(1, 0), by norm_num⟩
  exact not_injective_graph_of_deckShift_eq (k := 1) (p := p) (by norm_num) rfl

end TauCeti.PolarGraph
