/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Chords of a curve monotone along a linear functional

Let `γ : ℝ → E` be a curve in a real vector space and `φ` a linear functional such that `φ ∘ γ` is
monotone on a set of parameters. Then `φ` bounds the chords and inscribed triangles of `γ` by its
values at their extreme vertices, and when `φ ∘ γ` is strictly increasing a chord reaches the
value of `φ` at an earlier (or later) point of the curve only at its first (or last) vertex.

These are the facts that separate nearby edges of a polygon inscribed in a regular `C¹` curve,
which is strictly increasing along a suitable continuous linear functional on short parameter
windows (`ContDiff.exists_strictMonoOn_dual_comp`).

## Main results

* `StrictMonoOn.eq_of_mem_segment_of_le`, `StrictMonoOn.eq_of_mem_segment_of_ge`: a point of the
  chord from `γ b` to `γ b'` on which `φ` is at most `φ (γ a)` for some `a ≤ b`, or at least
  `φ (γ a)` for some `a ≥ b'`, is the corresponding end of the chord.
* `MonotoneOn.le_of_mem_convexHull`, `MonotoneOn.ge_of_mem_convexHull`: `φ` is bounded on the
  triangle `γ c, γ u, γ c'`, `c ≤ u ≤ c'`, by its values at `γ c` and `γ c'`.
* `StrictMonoOn.notMem_between_of_le_or_le`: a piece of the curve over `[c, d]`, or its chord,
  lying on one side of two parameters `a`, `b` on which `φ ∘ γ` is strictly increasing does not
  meet the region where `φ` is strictly between its values at `γ a` and `γ b`.
-/

public section

open Set

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FunLike F E ℝ] [LinearMapClass F ℝ E ℝ]
  {φ : F} {γ : ℝ → E}

/-- Let `φ ∘ γ` be strictly increasing on `I`, and `a ≤ b < b'` in `I`. A point `x` of the chord
from `γ b` to `γ b'` with `φ x ≤ φ (γ a)` is the start `γ b` of the chord, and `a = b`. -/
theorem StrictMonoOn.eq_of_mem_segment_of_le {I : Set ℝ}
    (hmono : StrictMonoOn (fun t ↦ φ (γ t)) I) {a b b' : ℝ} (ha : a ∈ I) (hb : b ∈ I)
    (hb' : b' ∈ I) (hab : a ≤ b) (hbb' : b < b') {x : E} (hx : φ x ≤ φ (γ a))
    (hx' : x ∈ segment ℝ (γ b) (γ b')) : a = b ∧ x = γ b := by
  rw [segment_eq_image'] at hx'
  obtain ⟨θ, ⟨hθ, -⟩, rfl⟩ := hx'
  have h₁ : φ (γ b) < φ (γ b') := hmono hb hb' hbb'
  have h₂ : φ (γ a) ≤ φ (γ b) := hmono.monotoneOn ha hb hab
  simp only [map_add, map_smul, map_sub, smul_eq_mul] at hx
  obtain rfl : θ = 0 := by nlinarith
  simp only [zero_smul, add_zero, zero_mul] at hx ⊢
  exact ⟨hmono.injOn ha hb (le_antisymm h₂ hx), trivial⟩

/-- Let `φ ∘ γ` be strictly increasing on `I`, and `b < b' ≤ a` in `I`. A point `x` of the chord
from `γ b` to `γ b'` with `φ (γ a) ≤ φ x` is the end `γ b'` of the chord, and `b' = a`. -/
theorem StrictMonoOn.eq_of_mem_segment_of_ge {I : Set ℝ}
    (hmono : StrictMonoOn (fun t ↦ φ (γ t)) I) {a b b' : ℝ} (ha : a ∈ I) (hb : b ∈ I)
    (hb' : b' ∈ I) (hbb' : b < b') (hb'a : b' ≤ a) {x : E} (hx : φ (γ a) ≤ φ x)
    (hx' : x ∈ segment ℝ (γ b) (γ b')) : b' = a ∧ x = γ b' := by
  rw [segment_symm, segment_eq_image'] at hx'
  obtain ⟨θ, ⟨hθ, -⟩, rfl⟩ := hx'
  have h₁ : φ (γ b) < φ (γ b') := hmono hb hb' hbb'
  have h₂ : φ (γ b') ≤ φ (γ a) := hmono.monotoneOn hb' ha hb'a
  simp only [map_add, map_smul, map_sub, smul_eq_mul] at hx
  obtain rfl : θ = 0 := by nlinarith
  simp only [zero_smul, add_zero, zero_mul] at hx ⊢
  exact ⟨hmono.injOn hb' ha (le_antisymm h₂ hx), trivial⟩

/-- If `φ ∘ γ` is monotone on `[c, c']` and `c ≤ u ≤ c'`, then `φ` is at most `φ (γ c')` on the
triangle with vertices `γ c`, `γ u`, `γ c'`. -/
theorem MonotoneOn.le_of_mem_convexHull {c c' u : ℝ} {y : E}
    (hφ : MonotoneOn (fun t ↦ φ (γ t)) (Icc c c')) (hcu : c ≤ u) (huc : u ≤ c')
    (hy : y ∈ convexHull ℝ {γ c, γ u, γ c'}) : φ y ≤ φ (γ c') := by
  refine convexHull_min ?_ (convex_halfSpace_le (φ : E →ₗ[ℝ] ℝ).isLinear _) hy
  rintro _ (rfl | rfl | rfl)
  · exact hφ ⟨le_rfl, hcu.trans huc⟩ ⟨hcu.trans huc, le_rfl⟩ (hcu.trans huc)
  · exact hφ ⟨hcu, huc⟩ ⟨hcu.trans huc, le_rfl⟩ huc
  · exact le_rfl

/-- If `φ ∘ γ` is monotone on `[c, c']` and `c ≤ u ≤ c'`, then `φ` is at least `φ (γ c)` on the
triangle with vertices `γ c`, `γ u`, `γ c'`. -/
theorem MonotoneOn.ge_of_mem_convexHull {c c' u : ℝ} {y : E}
    (hφ : MonotoneOn (fun t ↦ φ (γ t)) (Icc c c')) (hcu : c ≤ u) (huc : u ≤ c')
    (hy : y ∈ convexHull ℝ {γ c, γ u, γ c'}) : φ (γ c) ≤ φ y := by
  refine convexHull_min ?_ (convex_halfSpace_ge (φ : E →ₗ[ℝ] ℝ).isLinear _) hy
  rintro _ (rfl | rfl | rfl)
  · exact le_rfl
  · exact hφ ⟨le_rfl, hcu.trans huc⟩ ⟨hcu, huc⟩ hcu
  · exact hφ ⟨le_rfl, hcu.trans huc⟩ ⟨hcu.trans huc, le_rfl⟩ (hcu.trans huc)

/-- If `φ ∘ γ` is strictly increasing on `I` and `[c, d] ⊆ I` lies entirely on one side of two
points `a`, `b` of `I` (`d ≤ a` or `b ≤ c`), then the piece of the curve over `[c, d]`, and its
chord, do not meet the region where `φ` is strictly between its values at `γ a` and `γ b`. -/
theorem StrictMonoOn.notMem_between_of_le_or_le {I : Set ℝ} {a b c d : ℝ}
    (hφ : StrictMonoOn (fun t ↦ φ (γ t)) I) (ha : a ∈ I) (hb : b ∈ I) (hcd : c ≤ d)
    (hW : Icc c d ⊆ I) (hle : d ≤ a ∨ b ≤ c) {x : E}
    (hx : x ∈ γ '' Icc c d ∪ segment ℝ (γ c) (γ d)) :
    ¬ (φ (γ a) < φ x ∧ φ x < φ (γ b)) := by
  rintro ⟨h₁, h₂⟩
  have hc₀ : c ∈ Icc c d := left_mem_Icc.2 hcd
  have hc₁ : d ∈ Icc c d := right_mem_Icc.2 hcd
  rcases hle with hle | hle
  · have hbelow : ∀ s ∈ Icc c d, φ (γ s) ≤ φ (γ a) := fun s hs ↦
      hφ.monotoneOn (hW hs) ha (hs.2.trans hle)
    have : φ x ≤ φ (γ a) := by
      rcases hx with ⟨s, hs, rfl⟩ | hx
      · exact hbelow s hs
      · exact (convex_halfSpace_le (φ : E →ₗ[ℝ] ℝ).isLinear _).segment_subset
          (hbelow c hc₀) (hbelow d hc₁) hx
    linarith
  · have habove : ∀ s ∈ Icc c d, φ (γ b) ≤ φ (γ s) := fun s hs ↦
      hφ.monotoneOn hb (hW hs) (hle.trans hs.1)
    have : φ (γ b) ≤ φ x := by
      rcases hx with ⟨s, hs, rfl⟩ | hx
      · exact habove s hs
      · exact (convex_halfSpace_ge (φ : E →ₗ[ℝ] ℝ).isLinear _).segment_subset
          (habove c hc₀) (habove d hc₁) hx
    linarith
