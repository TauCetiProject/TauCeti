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
punctured Euclidean plane. Deck translations shift the angle by an integral multiple of
`2π`. The separation of a graph records the height change under one such translation.

## References

* T. H. Colding and W. P. Minicozzi II, *The space of embedded minimal surfaces of fixed
  genus in a 3-manifold IV*, Section 0.
-/

public noncomputable section

namespace TauCeti.PolarGraph

/-- Polar coordinates with positive radius and an unrestricted real angle. -/
abbrev PolarPoint := {p : ℝ × ℝ // 0 < p.1}

/-- The radius of a point in the polar coordinate cover. -/
@[expose] def radius (p : PolarPoint) : ℝ := p.1.1

/-- The angle of a point in the polar coordinate cover. -/
@[expose] def angle (p : PolarPoint) : ℝ := p.1.2

/-- Translation by `2πk` in the angular coordinate. -/
@[expose] def deckShift (k : ℤ) (p : PolarPoint) : PolarPoint :=
  ⟨(radius p, angle p + (k : ℝ) * (2 * Real.pi)), p.2⟩

@[simp] theorem radius_deckShift (k : ℤ) (p : PolarPoint) :
    radius (deckShift k p) = radius p := rfl

@[simp] theorem angle_deckShift (k : ℤ) (p : PolarPoint) :
    angle (deckShift k p) = angle p + (k : ℝ) * (2 * Real.pi) := rfl

@[simp] theorem deckShift_zero (p : PolarPoint) : deckShift 0 p = p := by
  apply Subtype.ext
  simp [deckShift, angle, radius]

theorem deckShift_add (k l : ℤ) (p : PolarPoint) :
    deckShift (k + l) p = deckShift l (deckShift k p) := by
  apply Subtype.ext
  simp only [deckShift, radius, angle, Subtype.coe_mk, Prod.mk.injEq, true_and,
    Int.cast_add]
  ring

/-- The image of a polar point in the punctured complex plane. -/
def projection (p : PolarPoint) : ℂ :=
  (radius p : ℂ) * (Circle.exp (angle p) : ℂ)

@[simp] theorem projection_deckShift (k : ℤ) (p : PolarPoint) :
    projection (deckShift k p) = projection p := by
  have h : Circle.exp (angle p + (k : ℝ) * (2 * Real.pi)) = Circle.exp (angle p) :=
    Circle.exp_eq_exp.mpr ⟨k, rfl⟩
  simp [projection, h]

/-- The Euclidean norm of the projection is the polar radius. -/
@[simp] theorem norm_projection (p : PolarPoint) : ‖projection p‖ = radius p := by
  simp [projection, Complex.norm_real, radius, abs_of_pos p.2]

/-- The polar projection avoids the origin. -/
theorem projection_ne_zero (p : PolarPoint) : projection p ≠ 0 := by
  have h : 0 < ‖projection p‖ := by rw [norm_projection]; exact p.2
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
      have hz : (radius q : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt q.2)
      exact mul_left_cancel₀ hz (by simpa [projection, hr] using h)
    have hc : Circle.exp (angle p) = Circle.exp (angle q) := Subtype.ext hc'
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hc.symm
    refine ⟨k, Subtype.ext (Prod.ext ?_ ?_)⟩
    · simpa [radius, deckShift] using hr.symm
    · simpa [angle, deckShift] using hk
  · rintro ⟨k, rfl⟩
    exact (projection_deckShift k p).symm

/-- Points of a parameter domain whose `k`-th deck translate also lies in the domain. -/
@[expose] def overlap (Ω : Set PolarPoint) (k : ℤ) : Set PolarPoint :=
  {p | p ∈ Ω ∧ deckShift k p ∈ Ω}

@[simp] theorem mem_overlap_iff {Ω : Set PolarPoint} {k : ℤ} {p : PolarPoint} :
    p ∈ overlap Ω k ↔ p ∈ Ω ∧ deckShift k p ∈ Ω := Iff.rfl

/-- The height difference between a point and its `k`-th deck translate. -/
@[expose] def separation (u : PolarPoint → ℝ) (k : ℤ) (p : PolarPoint) : ℝ :=
  u (deckShift k p) - u p

@[simp] theorem separation_zero (u : PolarPoint → ℝ) (p : PolarPoint) :
    separation u 0 p = 0 := by
  simp [separation]

theorem separation_add (u : PolarPoint → ℝ) (k l : ℤ) (p : PolarPoint) :
    separation u (k + l) p = separation u k p + separation u l (deckShift k p) := by
  simp [separation, deckShift_add]

theorem separation_neg (u : PolarPoint → ℝ) (k : ℤ) (p : PolarPoint) :
    separation u (-k) (deckShift k p) = -separation u k p := by
  have h : deckShift (-k) (deckShift k p) = p := by
    rw [← deckShift_add, add_neg_cancel, deckShift_zero]
  simp [separation, h, sub_eq_add_neg, add_comm]

/-- A nontrivial deck translation has no fixed points. -/
theorem deckShift_ne_self (k : ℤ) (hk : k ≠ 0) (p : PolarPoint) : deckShift k p ≠ p := by
  intro h
  have ha := congrArg angle h
  simp only [angle_deckShift] at ha
  have hm : (k : ℝ) * (2 * Real.pi) = 0 := by
    linear_combination ha
  have hk' : (k : ℝ) = 0 :=
    (mul_eq_zero.mp hm).resolve_right (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  exact hk (by exact_mod_cast hk')

/-- The surface parametrization of a polar height function. -/
def graph (u : PolarPoint → ℝ) (p : PolarPoint) : ℂ × ℝ := (projection p, u p)

/-- A polar graph is injectively parametrized on a domain exactly when every nontrivial
deck overlap has nonzero height separation. -/
theorem graph_injOn_iff (u : PolarPoint → ℝ) (Ω : Set PolarPoint) :
    Set.InjOn (graph u) Ω ↔
      ∀ k : ℤ, k ≠ 0 → ∀ p ∈ overlap Ω k, separation u k p ≠ 0 := by
  constructor
  · intro hi k hk p hp hs
    have heq : graph u p = graph u (deckShift k p) := by
      apply Prod.ext
      · exact (projection_deckShift k p).symm
      · exact (sub_eq_zero.mp hs).symm
    exact deckShift_ne_self k hk p (hi hp.1 hp.2 heq).symm
  · intro hs p hp q hq heq
    have hproj : projection p = projection q := by
      simpa only [graph] using congrArg Prod.fst heq
    obtain ⟨k, rfl⟩ := (projection_eq_iff p q).mp hproj
    by_cases hk : k = 0
    · subst k
      exact (deckShift_zero p).symm
    · have hu : u p = u (deckShift k p) := by
        simpa only [graph] using congrArg Prod.snd heq
      exact False.elim (hs k hk p ⟨hp, hq⟩ (by simp [separation, hu]))

end TauCeti.PolarGraph
