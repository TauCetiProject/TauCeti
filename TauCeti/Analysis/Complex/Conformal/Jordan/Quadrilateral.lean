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
import TauCeti.Topology.Homotopy.Cube.Radius

/-!
# Four-sided Jordan domains in the plane

Four injective paths `top : Path a b`, `bot : Path c d`, `left : Path a c`, and
`right : Path b d` in `ℂ` whose opposite edges are disjoint and whose adjacent edges meet only at
their shared corners form a Jordan curve, and the closed domain `filledHull C` they enclose is
homeomorphic to the unit square `I × I` by a homeomorphism restricting to the four given paths
along the four sides (`TauCeti.exists_homeomorph_unitInterval_prod_filledHull`).

## The argument

The cube homeomorphism `TauCeti.cubeHomeomorphClosedBall (Fin 2)` followed by
`TauCeti.closedBallHomeomorphOfFinrankEq` identifies `I × I` with `closedBall (0 : ℂ) 1`, carrying
the boundary `∂(I × I)` onto the unit circle `sphere (0 : ℂ) 1`. Gluing the four paths along the
four closed sides of `I × I` defines a continuous bijection from the compact boundary `∂(I × I)`
onto `C`, hence a homeomorphism. Transferring to `sphere (0 : ℂ) 1` proves that `C` is a Jordan
curve and supplies the boundary data for the prescribed-boundary Schoenflies theorem
(`TauCeti.IsJordanCurve.exists_homeomorph_sphere_eq`), whose extension restricts to the required
homeomorphism `I × I ≃ₜ filledHull C`.

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

/-- The boundary of the unit square `I × I`, consisting of its four sides. -/
private def squareBoundary : Set (I × I) :=
  {p | p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1}

private theorem isClosed_squareBoundary : IsClosed squareBoundary := by
  have h1 : IsClosed {p : I × I | p.1 = 0} := isClosed_eq continuous_fst continuous_const
  have h2 : IsClosed {p : I × I | p.1 = 1} := isClosed_eq continuous_fst continuous_const
  have h3 : IsClosed {p : I × I | p.2 = 0} := isClosed_eq continuous_snd continuous_const
  have h4 : IsClosed {p : I × I | p.2 = 1} := isClosed_eq continuous_snd continuous_const
  have heq : squareBoundary =
      ({p : I × I | p.1 = 0} ∪ {p : I × I | p.1 = 1}) ∪
        ({p : I × I | p.2 = 0} ∪ {p : I × I | p.2 = 1}) := by
    ext p
    simp [squareBoundary, or_assoc]
  rw [heq]
  exact (h1.union h2).union (h3.union h4)

/-- Identification of the unit square `I × I` with the closed unit disc in `ℂ`, carrying the
boundary of the square onto the unit circle. -/
private def squareHomeomorphClosedBall : (I × I) ≃ₜ closedBall (0 : ℂ) 1 :=
  Homeomorph.finTwoArrow.symm.trans <|
    (cubeHomeomorphClosedBall (Fin 2)).trans <|
      closedBallHomeomorphOfFinrankEq (by simp [Complex.finrank_real_complex])

private theorem norm_squareHomeomorphClosedBall_eq_one_iff (p : I × I) :
    ‖(squareHomeomorphClosedBall p : ℂ)‖ = 1 ↔ p ∈ squareBoundary := by
  simp only [squareHomeomorphClosedBall, Homeomorph.trans_apply,
    coe_closedBallHomeomorphOfFinrankEq_apply,
    ContinuousLinearEquiv.norm_unitBallHomeomorph_eq_one_iff,
    norm_cubeHomeomorphClosedBall_eq_one_iff, Cube.boundary, Fin.exists_fin_two,
    Homeomorph.finTwoArrow_symm_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, squareBoundary, mem_ofPred_eq, or_assoc]

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
      ext p; simp [squareBoundary, or_assoc]
    rw [heq]
    exact (h1.union_of_isClosed h2 hc1 hc2).union_of_isClosed
      (h3.union_of_isClosed h4 hc3 hc4) (hc1.union hc2) (hc3.union hc4)
  -- Coincidences between adjacent edges occur only at the shared corner.
  have hmeet_tl {s t : I} (h : top s = left t) : s = 0 ∧ t = 0 := by
    have hm : top s ∈ ({a} : Set ℂ) := htl ▸ ⟨mem_range_self s, h ▸ mem_range_self t⟩
    rw [mem_singleton_iff] at hm
    exact ⟨htop (hm.trans top.source.symm), hleft ((h.symm.trans hm).trans left.source.symm)⟩
  have hmeet_tr {s t : I} (h : top s = right t) : s = 1 ∧ t = 0 := by
    have hm : top s ∈ ({b} : Set ℂ) := htr ▸ ⟨mem_range_self s, h ▸ mem_range_self t⟩
    rw [mem_singleton_iff] at hm
    exact ⟨htop (hm.trans top.target.symm), hright ((h.symm.trans hm).trans right.source.symm)⟩
  have hmeet_bl {s t : I} (h : bot s = left t) : s = 0 ∧ t = 1 := by
    have hm : bot s ∈ ({c} : Set ℂ) := hbl ▸ ⟨mem_range_self s, h ▸ mem_range_self t⟩
    rw [mem_singleton_iff] at hm
    exact ⟨hbot (hm.trans bot.source.symm), hleft ((h.symm.trans hm).trans left.target.symm)⟩
  have hmeet_br {s t : I} (h : bot s = right t) : s = 1 ∧ t = 1 := by
    have hm : bot s ∈ ({d} : Set ℂ) := hbr ▸ ⟨mem_range_self s, h ▸ mem_range_self t⟩
    rw [mem_singleton_iff] at hm
    exact ⟨hbot (hm.trans bot.target.symm), hright ((h.symm.trans hm).trans right.target.symm)⟩
  -- `f` maps `squareBoundary` bijectively onto `C`.
  have hbij : BijOn f squareBoundary C := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨s, t⟩ (rfl | rfl | rfl | rfl)
      · rw [hf_left]; exact Or.inl (Or.inr (mem_range_self t))
      · rw [hf_right]; exact Or.inr (mem_range_self t)
      · rw [hf_top]; exact Or.inl (Or.inl (Or.inl (mem_range_self s)))
      · rw [hf_bot]; exact Or.inl (Or.inl (Or.inr (mem_range_self s)))
    · rintro ⟨s₁, t₁⟩ hp ⟨s₂, t₂⟩ hq heq
      rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl
      · rw [hf_left, hf_left] at heq; exact Prod.ext rfl (hleft heq)
      · rw [hf_left, hf_right] at heq
        exact (hlr.ne_of_mem (mem_range_self t₁) (mem_range_self t₂) heq).elim
      · rw [hf_left, hf_top] at heq
        obtain ⟨hs, ht⟩ := hmeet_tl heq.symm; exact Prod.ext hs.symm ht
      · rw [hf_left, hf_bot] at heq
        obtain ⟨hs, ht⟩ := hmeet_bl heq.symm; exact Prod.ext hs.symm ht
      · rw [hf_right, hf_left] at heq
        exact (hlr.ne_of_mem (mem_range_self t₂) (mem_range_self t₁) heq.symm).elim
      · rw [hf_right, hf_right] at heq; exact Prod.ext rfl (hright heq)
      · rw [hf_right, hf_top] at heq
        obtain ⟨hs, ht⟩ := hmeet_tr heq.symm; exact Prod.ext hs.symm ht
      · rw [hf_right, hf_bot] at heq
        obtain ⟨hs, ht⟩ := hmeet_br heq.symm; exact Prod.ext hs.symm ht
      · rw [hf_top, hf_left] at heq
        obtain ⟨hs, ht⟩ := hmeet_tl heq; exact Prod.ext hs ht.symm
      · rw [hf_top, hf_right] at heq
        obtain ⟨hs, ht⟩ := hmeet_tr heq; exact Prod.ext hs ht.symm
      · rw [hf_top, hf_top] at heq; exact Prod.ext (htop heq) rfl
      · rw [hf_top, hf_bot] at heq
        exact (htb.ne_of_mem (mem_range_self s₁) (mem_range_self s₂) heq).elim
      · rw [hf_bot, hf_left] at heq
        obtain ⟨hs, ht⟩ := hmeet_bl heq; exact Prod.ext hs ht.symm
      · rw [hf_bot, hf_right] at heq
        obtain ⟨hs, ht⟩ := hmeet_br heq; exact Prod.ext hs ht.symm
      · rw [hf_bot, hf_top] at heq
        exact (htb.ne_of_mem (mem_range_self s₂) (mem_range_self s₁) heq.symm).elim
      · rw [hf_bot, hf_bot] at heq; exact Prod.ext (hbot heq) rfl
    · rintro z (((⟨s, rfl⟩ | ⟨s, rfl⟩) | ⟨t, rfl⟩) | ⟨t, rfl⟩)
      · exact ⟨(s, 0), Or.inr (Or.inr (Or.inl rfl)), hf_top s⟩
      · exact ⟨(s, 1), Or.inr (Or.inr (Or.inr rfl)), hf_bot s⟩
      · exact ⟨(0, t), Or.inl rfl, hf_left t⟩
      · exact ⟨(1, t), Or.inr (Or.inl rfl), hf_right t⟩
  have : CompactSpace squareBoundary :=
    isCompact_iff_compactSpace.mp isClosed_squareBoundary.isCompact
  let ψ : squareBoundary ≃ₜ C :=
    Continuous.homeoOfEquivCompactToT2 (f := hbij.equiv f) (hfc.mapsToRestrict hbij.mapsTo)
  -- Restrict `squareHomeomorphClosedBall` to a boundary homeomorphism `∂(I × I) ≃ₜ S¹`.
  let eSub : {z : closedBall (0 : ℂ) 1 // (z : ℂ) ∈ sphere (0 : ℂ) 1} ≃ₜ sphere (0 : ℂ) 1 :=
    { toEquiv := Equiv.subtypeSubtypeEquivSubtype fun hx => sphere_subset_closedBall hx
      continuous_toFun := (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
      continuous_invFun := (continuous_subtypeVal.subtype_mk _).subtype_mk _ }
  let eQ : squareBoundary ≃ₜ sphere (0 : ℂ) 1 :=
    (squareHomeomorphClosedBall.subtype fun p =>
      (norm_squareHomeomorphClosedBall_eq_one_iff p).symm.trans
        mem_sphere_zero_iff_norm.symm).trans eSub
  let φ : sphere (0 : ℂ) 1 ≃ₜ C := eQ.symm.trans ψ
  have hC : IsJordanCurve C :=
    isJordanCurve_iff.mpr ⟨φ.symm.trans (sphereCircleHomeomorph 0 one_pos)⟩
  obtain ⟨e, heφ, -, -, heCB⟩ := hC.exists_homeomorph_sphere_eq φ
  let Φ : I × I ≃ₜ filledHull C :=
    squareHomeomorphClosedBall.trans ((e.image (closedBall 0 1)).trans (Homeomorph.setCongr heCB))
  have hΦb (p : I × I) (hp : p ∈ squareBoundary) : (Φ p : ℂ) = f p := by
    have hcoe : (Φ p : ℂ) = e (squareHomeomorphClosedBall p) := rfl
    rw [hcoe]
    have hQ : (squareHomeomorphClosedBall p : ℂ) = (eQ ⟨p, hp⟩ : ℂ) := rfl
    rw [hQ, heφ (eQ ⟨p, hp⟩)]
    simp only [φ, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
    rfl
  refine ⟨hC, Φ, ?_, ?_, ?_, ?_⟩
  · intro s; rw [hΦb (s, 0) (Or.inr (Or.inr (Or.inl rfl))), hf_top]
  · intro s; rw [hΦb (s, 1) (Or.inr (Or.inr (Or.inr rfl))), hf_bot]
  · intro t; rw [hΦb (0, t) (Or.inl rfl), hf_left]
  · intro t; rw [hΦb (1, t) (Or.inr (Or.inl rfl)), hf_right]

end TauCeti
