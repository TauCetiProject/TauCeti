/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval
public import TauCeti.Topology.FilledHull
public import TauCeti.Topology.JordanCurve.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.Conformal.Jordan.Schoenflies
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Data.Set.InjOnUnion
import TauCeti.Topology.Homeomorph.CompactQuotient
import TauCeti.Topology.Homeomorph.SetCongr
import TauCeti.Topology.Homotopy.Cube.Basic
import TauCeti.Topology.Homotopy.Cube.Radius

/-!
# Four-sided Jordan domains in the plane

Four injective paths `top : Path a b`, `bot : Path c d`, `left : Path a c`, and
`right : Path b d` in `ℂ` whose opposite edges are disjoint and whose adjacent edges meet only at
their shared corners form a Jordan curve, and the closed domain `filledHull C` they enclose is
homeomorphic to the unit square `I × I` by a homeomorphism restricting to the four given paths
along the four sides (`TauCeti.exists_homeomorph_unitInterval_prod_filledHull`).

## The argument

The square-to-disc homeomorphism `TauCeti.squareHomeomorphClosedBall` identifies `I × I` with
`closedBall (0 : ℂ) 1`, carrying the boundary `TauCeti.squareBoundary` onto the unit circle
`sphere (0 : ℂ) 1` (`TauCeti.norm_squareHomeomorphClosedBall_eq_one_iff`). Gluing the four paths
along the four closed sides of `I × I` defines a continuous bijection from the compact boundary
`TauCeti.squareBoundary` onto `C`, hence a homeomorphism. Transferring to `sphere (0 : ℂ) 1`
supplies the boundary data for the prescribed-boundary Schoenflies theorem
(`TauCeti.exists_homeomorph_sphere_eq`), whose extension restricts to the required homeomorphism
`I × I ≃ₜ filledHull C`.

## Main results

* `TauCeti.exists_homeomorph_unitInterval_prod_filledHull`: a four-sided Jordan domain in `ℂ` is
  homeomorphic to `I × I` with prescribed boundary paths along the four sides.

## References

* A. Schoenflies, *Beiträge zur Theorie der Punktmengen. III*, Math. Ann. 62 (1906), 286–328.
* E. E. Moise, *Geometric Topology in Dimensions 2 and 3*, Springer GTM 47 (1977), Chapter 10.
-/

public section

noncomputable section

open Function Metric Set Topology unitInterval

namespace TauCeti

/-- **Four-sided Jordan domains are homeomorphic to the unit square.** Given four injective paths
`top : Path a b`, `bot : Path c d`, `left : Path a c`, and `right : Path b d` in `ℂ` whose opposite
edges are disjoint and whose adjacent edges meet only at their shared endpoints, the union of their
ranges is a Jordan curve, and there is a homeomorphism from `I × I` onto its filled hull restricting
to `top`, `bot`, `left`, and `right` along the four sides of the square. -/
theorem exists_homeomorph_unitInterval_prod_filledHull {a b c d : ℂ}
    {top : Path a b} {bot : Path c d} {left : Path a c} {right : Path b d}
    (htop : Injective top) (hbot : Injective bot)
    (hleft : Injective left) (hright : Injective right)
    (htb : Disjoint (range top) (range bot)) (hlr : Disjoint (range left) (range right))
    (htl : range top ∩ range left = {a}) (htr : range top ∩ range right = {b})
    (hbl : range bot ∩ range left = {c}) (hbr : range bot ∩ range right = {d}) :
    IsJordanCurve (range top ∪ range bot ∪ range left ∪ range right) ∧
      ∃ Φ : I × I ≃ₜ filledHull (range top ∪ range bot ∪ range left ∪ range right),
        (∀ s : I, (Φ (s, 0) : ℂ) = top s) ∧
        (∀ s : I, (Φ (s, 1) : ℂ) = bot s) ∧
        (∀ t : I, (Φ (0, t) : ℂ) = left t) ∧
        (∀ t : I, (Φ (1, t) : ℂ) = right t) := by
  classical
  set C : Set ℂ := range top ∪ range bot ∪ range left ∪ range right
  -- Piecewise parametrization of the four sides of the boundary of `I × I`.
  let f : I × I → ℂ := fun p =>
    if p.2 = 0 then top p.1
    else if p.2 = 1 then bot p.1
    else if p.1 = 0 then left p.2
    else right p.2
  have hf_top (s : I) : f (s, 0) = top s := by simp [f]
  have hf_bot (s : I) : f (s, 1) = bot s := by simp [f]
  have hf_left (t : I) : f (0, t) = left t := by
    by_cases h0 : t = 0
    · subst h0; simp [f]
    · by_cases h1 : t = 1
      · subst h1; simp [f]
      · simp [f, h0, h1]
  have hf_right (t : I) : f (1, t) = right t := by
    by_cases h0 : t = 0
    · subst h0; simp [f]
    · by_cases h1 : t = 1
      · subst h1; simp [f]
      · simp [f, h0, h1]
  -- Continuity on the union of the four closed sides.
  have hfc : ContinuousOn f squareBoundary := by
    have h1 : ContinuousOn f {p : I × I | p.1 = 0} :=
      (left.continuous.comp continuous_snd).continuousOn.congr fun p hp => by
        rcases p with ⟨s, t⟩; dsimp at hp; subst hp; exact hf_left t
    have h2 : ContinuousOn f {p : I × I | p.1 = 1} :=
      (right.continuous.comp continuous_snd).continuousOn.congr fun p hp => by
        rcases p with ⟨s, t⟩; dsimp at hp; subst hp; exact hf_right t
    have h3 : ContinuousOn f {p : I × I | p.2 = 0} :=
      (top.continuous.comp continuous_fst).continuousOn.congr fun p hp => by
        rcases p with ⟨s, t⟩; dsimp at hp; subst hp; exact hf_top s
    have h4 : ContinuousOn f {p : I × I | p.2 = 1} :=
      (bot.continuous.comp continuous_fst).continuousOn.congr fun p hp => by
        rcases p with ⟨s, t⟩; dsimp at hp; subst hp; exact hf_bot s
    have hc1 : IsClosed {p : I × I | p.1 = 0} := isClosed_eq continuous_fst continuous_const
    have hc2 : IsClosed {p : I × I | p.1 = 1} := isClosed_eq continuous_fst continuous_const
    have hc3 : IsClosed {p : I × I | p.2 = 0} := isClosed_eq continuous_snd continuous_const
    have hc4 : IsClosed {p : I × I | p.2 = 1} := isClosed_eq continuous_snd continuous_const
    have heq : squareBoundary =
        ({p : I × I | p.1 = 0} ∪ {p : I × I | p.1 = 1}) ∪
          ({p : I × I | p.2 = 0} ∪ {p : I × I | p.2 = 1}) := by
      ext p; simp [mem_squareBoundary_iff, or_assoc]
    rw [heq]
    exact (h1.union_of_isClosed h2 hc1 hc2).union_of_isClosed
      (h3.union_of_isClosed h4 hc3 hc4) (hc1.union hc2) (hc3.union hc4)
  -- Coincidences between adjacent edges occur only at the shared corner.
  have hcorner {a₁ a₂ b₁ b₂ x : ℂ} {α : Path a₁ a₂} {β : Path b₁ b₂}
      (hα : Injective α) (hβ : Injective β) (hinter : range α ∩ range β = {x})
      {s₀ t₀ : I} (hs₀ : α s₀ = x) (ht₀ : β t₀ = x) {s t : I} (h : α s = β t) :
      s = s₀ ∧ t = t₀ := by
    have hm : α s ∈ ({x} : Set ℂ) := hinter ▸ ⟨mem_range_self s, h ▸ mem_range_self t⟩
    rw [mem_singleton_iff] at hm
    exact ⟨hα (hm.trans hs₀.symm), hβ ((h.symm.trans hm).trans ht₀.symm)⟩
  -- `f` maps `squareBoundary` bijectively onto `C`.
  have hbij : BijOn f squareBoundary C := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨s, t⟩ hst
      rw [mem_squareBoundary_iff] at hst
      rcases hst with rfl | rfl | rfl | rfl
      · rw [hf_left]; exact Or.inl (Or.inr (mem_range_self t))
      · rw [hf_right]; exact Or.inr (mem_range_self t)
      · rw [hf_top]; exact Or.inl (Or.inl (Or.inl (mem_range_self s)))
      · rw [hf_bot]; exact Or.inl (Or.inl (Or.inr (mem_range_self s)))
    · let S : Fin 4 → Set (I × I)
        | 0 => {p | p.1 = 0}
        | 1 => {p | p.1 = 1}
        | 2 => {p | p.2 = 0}
        | 3 => {p | p.2 = 1}
      have hS0 {p : I × I} : p ∈ S 0 ↔ p.1 = 0 := Iff.rfl
      have hS1 {p : I × I} : p ∈ S 1 ↔ p.1 = 1 := Iff.rfl
      have hS2 {p : I × I} : p ∈ S 2 ↔ p.2 = 0 := Iff.rfl
      have hS3 {p : I × I} : p ∈ S 3 ↔ p.2 = 1 := Iff.rfl
      refine injOn_of_subset_iUnion (S := S) ?_ ?_ ?_
      · rintro ⟨s, t⟩ hst
        rw [mem_squareBoundary_iff] at hst
        rcases hst with rfl | rfl | rfl | rfl
        · exact mem_iUnion.2 ⟨0, hS0.2 rfl⟩
        · exact mem_iUnion.2 ⟨1, hS1.2 rfl⟩
        · exact mem_iUnion.2 ⟨2, hS2.2 rfl⟩
        · exact mem_iUnion.2 ⟨3, hS3.2 rfl⟩
      · intro i
        fin_cases i
        · rintro ⟨s₁, t₁⟩ h1 ⟨s₂, t₂⟩ h2 heq
          obtain rfl : s₁ = 0 := hS0.1 h1; obtain rfl : s₂ = 0 := hS0.1 h2
          rw [hf_left, hf_left] at heq; exact Prod.ext rfl (hleft heq)
        · rintro ⟨s₁, t₁⟩ h1 ⟨s₂, t₂⟩ h2 heq
          obtain rfl : s₁ = 1 := hS1.1 h1; obtain rfl : s₂ = 1 := hS1.1 h2
          rw [hf_right, hf_right] at heq; exact Prod.ext rfl (hright heq)
        · rintro ⟨s₁, t₁⟩ h1 ⟨s₂, t₂⟩ h2 heq
          obtain rfl : t₁ = 0 := hS2.1 h1; obtain rfl : t₂ = 0 := hS2.1 h2
          rw [hf_top, hf_top] at heq; exact Prod.ext (htop heq) rfl
        · rintro ⟨s₁, t₁⟩ h1 ⟨s₂, t₂⟩ h2 heq
          obtain rfl : t₁ = 1 := hS3.1 h1; obtain rfl : t₂ = 1 := hS3.1 h2
          rw [hf_bot, hf_bot] at heq; exact Prod.ext (hbot heq) rfl
      · intro i j hij ⟨s₁, t₁⟩ ⟨s₂, t₂⟩ hi hj heq
        fin_cases i <;> fin_cases j
        all_goals
          try exact absurd hij (by decide)
        · obtain rfl : s₁ = 0 := hS0.1 hi; obtain rfl : s₂ = 1 := hS1.1 hj
          rw [hf_left, hf_right] at heq
          exact (hlr.ne_of_mem (mem_range_self t₁) (mem_range_self t₂) heq).elim
        · obtain rfl : s₁ = 0 := hS0.1 hi; obtain rfl : t₂ = 0 := hS2.1 hj
          rw [hf_left, hf_top] at heq
          exact Or.inl (hS2.2 (hcorner htop hleft htl top.source left.source heq.symm).2)
        · obtain rfl : s₁ = 0 := hS0.1 hi; obtain rfl : t₂ = 1 := hS3.1 hj
          rw [hf_left, hf_bot] at heq
          exact Or.inl (hS3.2 (hcorner hbot hleft hbl bot.source left.target heq.symm).2)
        · obtain rfl : s₁ = 1 := hS1.1 hi; obtain rfl : t₂ = 0 := hS2.1 hj
          rw [hf_right, hf_top] at heq
          exact Or.inl (hS2.2 (hcorner htop hright htr top.target right.source heq.symm).2)
        · obtain rfl : s₁ = 1 := hS1.1 hi; obtain rfl : t₂ = 1 := hS3.1 hj
          rw [hf_right, hf_bot] at heq
          exact Or.inl (hS3.2 (hcorner hbot hright hbr bot.target right.target heq.symm).2)
        · obtain rfl : t₁ = 0 := hS2.1 hi; obtain rfl : t₂ = 1 := hS3.1 hj
          rw [hf_top, hf_bot] at heq
          exact (htb.ne_of_mem (mem_range_self s₁) (mem_range_self s₂) heq).elim
    · rintro z (((⟨s, rfl⟩ | ⟨s, rfl⟩) | ⟨t, rfl⟩) | ⟨t, rfl⟩)
      · exact ⟨(s, 0), mem_squareBoundary_iff.2 (Or.inr (Or.inr (Or.inl rfl))), hf_top s⟩
      · exact ⟨(s, 1), mem_squareBoundary_iff.2 (Or.inr (Or.inr (Or.inr rfl))), hf_bot s⟩
      · exact ⟨(0, t), mem_squareBoundary_iff.2 (Or.inl rfl), hf_left t⟩
      · exact ⟨(1, t), mem_squareBoundary_iff.2 (Or.inr (Or.inl rfl)), hf_right t⟩
  let ψ : squareBoundary ≃ₜ C :=
    (isClosed_squareBoundary.isCompact.imageHomeomorph hfc hbij.injOn).trans
      (Homeomorph.setCongr hbij.image_eq)
  have hψ_coe (q : squareBoundary) : (ψ q : ℂ) = f q := by
    simp [ψ, Homeomorph.trans_apply, Homeomorph.setCongr_apply]
  -- Restrict `squareHomeomorphClosedBall` to a boundary homeomorphism `∂(I × I) ≃ₜ S¹`.
  have hfin : Module.finrank ℝ ℂ = 2 := by simp [Complex.finrank_real_complex]
  let sq : (I × I) ≃ₜ closedBall (0 : ℂ) 1 := squareHomeomorphClosedBall hfin
  let eQ : squareBoundary ≃ₜ sphere (0 : ℂ) 1 := squareBoundaryHomeomorphSphere hfin
  let φ : sphere (0 : ℂ) 1 ≃ₜ C := eQ.symm.trans ψ
  have hC : IsJordanCurve C :=
    isJordanCurve_iff.mpr ⟨φ.symm.trans (sphereCircleHomeomorph 0 one_pos)⟩
  obtain ⟨e, heφ, -, -, heCB⟩ := exists_homeomorph_sphere_eq φ
  let Φ : I × I ≃ₜ filledHull C :=
    sq.trans ((e.image (closedBall 0 1)).trans (Homeomorph.setCongr heCB))
  have hΦb (p : I × I) (hp : p ∈ squareBoundary) : (Φ p : ℂ) = f p := by
    have hcoe : (Φ p : ℂ) = e (sq p) := by
      simp [Φ, Homeomorph.trans_apply, Homeomorph.setCongr_apply]
    have hQ : (sq p : ℂ) = (eQ ⟨p, hp⟩ : ℂ) :=
      (coe_squareBoundaryHomeomorphSphere_apply hfin ⟨p, hp⟩).symm
    rw [hcoe, hQ, heφ (eQ ⟨p, hp⟩)]
    simp only [φ, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
    exact hψ_coe ⟨p, hp⟩
  refine ⟨hC, Φ, ?_, ?_, ?_, ?_⟩
  · intro s; rw [hΦb (s, 0) (mem_squareBoundary_iff.2 (Or.inr (Or.inr (Or.inl rfl)))), hf_top]
  · intro s; rw [hΦb (s, 1) (mem_squareBoundary_iff.2 (Or.inr (Or.inr (Or.inr rfl)))), hf_bot]
  · intro t; rw [hΦb (0, t) (mem_squareBoundary_iff.2 (Or.inl rfl)), hf_left]
  · intro t; rw [hΦb (1, t) (mem_squareBoundary_iff.2 (Or.inr (Or.inl rfl))), hf_right]

end TauCeti
