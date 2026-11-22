/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Instances.AddCircle.Annulus
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Algebra.Order.Archimedean.Basic

/-!
# Twist lifts of the annulus

Fix a period `ℓ` and real numbers `a ≤ b`. A *positive twist lift* is a homeomorphism `F` of the
closed strip `ℝ × [a, b]` that commutes with the deck translation `(x, y) ↦ (x + ℓ, y)`, maps each
boundary line `y = a`, `y = b` into itself, and twists positively: for every `x`, the first
coordinate `y ↦ F₁(x, y)` is strictly increasing (Katok–Hasselblatt, *Introduction to the Modern
Theory of Dynamical Systems*, Section 9.2; Herman, *Sur les courbes invariantes par les
difféomorphismes de l'anneau*, Chapitre I, 1.2, for the differentiable form). A *negative twist
lift* is the same with strictly decreasing; it is described here through its inverse.

## Main definitions

* `TauCeti.IsTwistLift ℓ F`: `F` is a positive twist lift with period `ℓ`.

## Main results

* `TauCeti.IsTwistLift.strictMono_fst_apply_of_mem_boundary`: for `ℓ ≠ 0`, a twist lift is
  strictly increasing along each boundary line, which it preserves
  (`TauCeti.IsTwistLift.snd_apply_of_mem_boundary`), and the induced homeomorphism of the annulus
  `Homeomorph.annulusHomeomorphOfLift` maps each boundary circle onto itself
  (`TauCeti.IsTwistLift.image_annulusHomeomorphOfLift_eq_left`,
  `TauCeti.IsTwistLift.image_annulusHomeomorphOfLift_eq_right`). The general facts about
  homeomorphisms of the strip commuting with the deck translation are in
  `TauCeti.Topology.Instances.AddCircle.Annulus`.
* `TauCeti.IsTwistLift.strictAnti_fst_symm_apply`: the inverse of a positive twist lift twists
  negatively, and `TauCeti.isTwistLift_symm_iff`: a homeomorphism is a negative twist lift exactly
  when its inverse is a positive one.
* `TauCeti.IsTwistLift.trans_stripDeck`: composing with a deck translation keeps the twist property.

## Implementation notes

The strip is `ℝ × Set.Icc a b`. The inverse of a positive twist lift twists negatively by a
one-dimensional argument: the preimage of a vertical line under `F` meets every vertical at most
once, so its first coordinate is injective and continuous in the height, hence strictly monotone;
it decreases because, by the intermediate value theorem along a horizontal segment, its points
above the boundary lie to the left of its foot.
-/

public section

open Function Set

namespace TauCeti

variable {Y : Type*} [TopologicalSpace Y] {ℓ : ℝ}

/-! ### Twist lifts -/

variable {a b : ℝ} {F : ℝ × Icc a b ≃ₜ ℝ × Icc a b}

/-- A *positive twist lift* with period `ℓ` on the closed strip `ℝ × [a, b]`: a homeomorphism `F`
commuting with the deck translation `(x, y) ↦ (x + ℓ, y)`, mapping each boundary line `y = a`,
`y = b` into itself, with `y ↦ F₁(x, y)` strictly increasing for every `x` (Katok–Hasselblatt,
Section 9.2; Herman, Chapitre I, 1.2, for the differentiable form). A *negative* twist lift is a
homeomorphism with the same properties except that `y ↦ F₁(x, y)` is strictly decreasing; these
are the inverses of the positive ones (`TauCeti.isTwistLift_symm_iff`). -/
structure IsTwistLift (ℓ : ℝ) {a b : ℝ} (F : ℝ × Icc a b ≃ₜ ℝ × Icc a b) : Prop where
  /-- `F` commutes with the deck translation `(x, y) ↦ (x + ℓ, y)`. -/
  apply_add_period : ∀ p : ℝ × Icc a b, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)
  /-- `F` maps the lower boundary line `y = a` into itself. -/
  snd_apply_of_eq_left : ∀ p : ℝ × Icc a b, (p.2 : ℝ) = a → ((F p).2 : ℝ) = a
  /-- `F` maps the upper boundary line `y = b` into itself. -/
  snd_apply_of_eq_right : ∀ p : ℝ × Icc a b, (p.2 : ℝ) = b → ((F p).2 : ℝ) = b
  /-- Positive twist: the first coordinate of `F` is strictly increasing on every vertical. -/
  strictMono_fst_apply : ∀ x : ℝ, StrictMono fun y : Icc a b => (F (x, y)).1

namespace IsTwistLift

variable (hF : IsTwistLift ℓ F)
include hF

/-- A twist lift maps each boundary line into itself. -/
theorem snd_apply_of_mem_boundary {y : Icc a b} (hy : (y : ℝ) = a ∨ (y : ℝ) = b) (x : ℝ) :
    (F (x, y)).2 = y := by
  rcases hy with hy | hy
  · exact Subtype.ext ((hF.snd_apply_of_eq_left (x, y) hy).trans hy.symm)
  · exact Subtype.ext ((hF.snd_apply_of_eq_right (x, y) hy).trans hy.symm)

/-- For a nonzero period, a twist lift is strictly increasing along each boundary line: the induced
map of each boundary circle preserves its direction. -/
theorem strictMono_fst_apply_of_mem_boundary (hℓ : ℓ ≠ 0) {y : Icc a b}
    (hy : (y : ℝ) = a ∨ (y : ℝ) = b) : StrictMono fun x : ℝ => (F (x, y)).1 :=
  strictMono_fst_of_mapsTo_line hℓ hF.apply_add_period (hF.snd_apply_of_mem_boundary hy)

/-- The homeomorphism of the annulus `AddCircle ℓ × [a, b]` induced by a twist lift with nonzero
period maps the lower boundary circle onto itself. -/
theorem image_annulusHomeomorphOfLift_eq_left (hℓ : ℓ ≠ 0) :
    F.annulusHomeomorphOfLift hF.apply_add_period '' {z | (z.2 : ℝ) = a} =
      {z | (z.2 : ℝ) = a} :=
  F.image_annulusHomeomorphOfLift_setOf_of_subsingleton hℓ hF.apply_add_period
    (p := fun y : Icc a b => (y : ℝ) = a) (fun _ _ h h' => Subtype.ext (h.trans h'.symm))
    fun x y hy => hF.snd_apply_of_eq_left (x, y) hy

/-- The homeomorphism of the annulus `AddCircle ℓ × [a, b]` induced by a twist lift with nonzero
period maps the upper boundary circle onto itself. -/
theorem image_annulusHomeomorphOfLift_eq_right (hℓ : ℓ ≠ 0) :
    F.annulusHomeomorphOfLift hF.apply_add_period '' {z | (z.2 : ℝ) = b} =
      {z | (z.2 : ℝ) = b} :=
  F.image_annulusHomeomorphOfLift_setOf_of_subsingleton hℓ hF.apply_add_period
    (p := fun y : Icc a b => (y : ℝ) = b) (fun _ _ h h' => Subtype.ext (h.trans h'.symm))
    fun x y hy => hF.snd_apply_of_eq_right (x, y) hy

/-- For a nonzero period, the inverse of a twist lift maps each boundary line into itself. -/
theorem snd_symm_apply_of_mem_boundary (hℓ : ℓ ≠ 0) {y : Icc a b}
    (hy : (y : ℝ) = a ∨ (y : ℝ) = b) (x : ℝ) : (F.symm (x, y)).2 = y :=
  snd_symm_apply_of_mapsTo_line hℓ hF.apply_add_period (hF.snd_apply_of_mem_boundary hy) x

/-- The key step for `TauCeti.IsTwistLift.strictAnti_fst_symm_apply`: the preimage under a twist
lift of a point `(x, y)` above the lower boundary lies strictly to the left of the preimage of
`(x, a)`. -/
private theorem fst_symm_apply_lt (hℓ : ℓ ≠ 0) (x : ℝ) {y₀ y : Icc a b} (hy₀ : (y₀ : ℝ) = a)
    (hy : a < y) : (F.symm (x, y)).1 < (F.symm (x, y₀)).1 := by
  set u := (F.symm (x, y₀)).1
  have hu : F (u, y₀) = (x, y₀) := by
    rw [← F.apply_symm_apply (x, y₀)]
    congr 1
    exact Prod.ext rfl (hF.snd_symm_apply_of_mem_boundary hℓ (Or.inl hy₀) x).symm
  -- No point of the vertical through `u` is sent to height `y` on or left of `x`.
  have key : ∀ (t : ℝ) (s : Icc a b), t ≤ x → F (u, s) ≠ (t, y) := by
    intro t s ht hs
    rcases (show y₀ ≤ s from Subtype.coe_le_coe.1 (by rw [hy₀]; exact s.property.1)).eq_or_lt
      with h | h
    · rw [← h, hu] at hs
      have := congrArg (fun p => (p.2 : ℝ)) hs
      simp only at this
      linarith
    · have := hF.strictMono_fst_apply u h
      simp only [hu, hs] at this
      linarith
  by_contra hle
  rw [not_lt] at hle
  obtain ⟨k, hk⟩ := exists_int_mul_gt hℓ ((F.symm (x, y)).1 - u)
  have hshift :=
    apply_add_int_mul_of_apply_add (symm_apply_add_of_apply_add hF.apply_add_period) (-k) x y
  push_cast at hshift
  obtain ⟨t, ht, htu⟩ := intermediate_value_Icc (show x + -k * ℓ ≤ x by linarith)
    (show Continuous fun t : ℝ => (F.symm (t, y)).1 by fun_prop).continuousOn
    (show u ∈ Icc (F.symm (x + -k * ℓ, y)).1 (F.symm (x, y)).1 by
      rw [hshift]
      exact ⟨by simp only; linarith, hle⟩)
  refine key t (F.symm (t, y)).2 ht.2 ?_
  rw [← htu, F.apply_symm_apply]

/-- **The inverse of a positive twist lift twists negatively**: for a nonzero period, the first
coordinate of `F⁻¹` is strictly decreasing on every vertical. Together with the deck and boundary
properties of `F⁻¹`, this makes `F⁻¹` a negative twist lift (`TauCeti.isTwistLift_symm_iff`). -/
theorem strictAnti_fst_symm_apply (hℓ : ℓ ≠ 0) (x : ℝ) :
    StrictAnti fun y : Icc a b => (F.symm (x, y)).1 := by
  rcases isEmpty_or_nonempty (Icc a b) with h | ⟨⟨y₀, hy₀⟩⟩
  · intro y
    exact h.elim y
  have : Fact (a ≤ b) := ⟨hy₀.1.trans hy₀.2⟩
  refine Continuous.strictAnti_of_inj_boundedOrder (by fun_prop) ?_ ?_
  · rcases (bot_le : (⊥ : Icc a b) ≤ ⊤).eq_or_lt with h | h
    · rw [h]
    · have h' := Subtype.coe_lt_coe.2 h
      rw [Set.Icc.coe_bot] at h'
      exact (hF.fst_symm_apply_lt hℓ x (Set.Icc.coe_bot a b) h').le
  · intro y₁ y₂ h
    simp only at h
    have hp : F.symm (x, y₁) = F.symm (x, y₂) := by
      refine Prod.ext h ((hF.strictMono_fst_apply (F.symm (x, y₁)).1).injective ?_)
      have e₁ : (F ((F.symm (x, y₁)).1, (F.symm (x, y₁)).2)).1 = x := by
        rw [Prod.mk.eta, F.apply_symm_apply]
      have e₂ : (F ((F.symm (x, y₂)).1, (F.symm (x, y₂)).2)).1 = x := by
        rw [Prod.mk.eta, F.apply_symm_apply]
      rw [← h] at e₂
      exact e₁.trans e₂.symm
    simpa using congrArg (fun p => (F p).2) hp

/-- Composing a twist lift with a deck translation gives a twist lift. -/
theorem trans_stripDeck (m : ℤ) : IsTwistLift ℓ (F.trans (stripDeck ℓ m (Icc a b))) where
  apply_add_period p := by simp [hF.apply_add_period p, add_right_comm]
  snd_apply_of_eq_left p hp := by simpa using hF.snd_apply_of_eq_left p hp
  snd_apply_of_eq_right p hp := by simpa using hF.snd_apply_of_eq_right p hp
  strictMono_fst_apply x := by
    simpa using (hF.strictMono_fst_apply x).add_const ((m : ℝ) * ℓ)

end IsTwistLift

/-- The reflection `(x, y) ↦ (-x, y)` of the strip, which conjugates negative twists to positive
ones. -/
private def stripReflect (Y : Type*) [TopologicalSpace Y] : ℝ × Y ≃ₜ ℝ × Y :=
  (Homeomorph.neg ℝ).prodCongr (Homeomorph.refl Y)

private theorem stripReflect_apply (p : ℝ × Y) : stripReflect Y p = (-p.1, p.2) := rfl

private theorem stripReflect_symm_apply (p : ℝ × Y) : (stripReflect Y).symm p = (-p.1, p.2) :=
  rfl

/-- For a nonzero period, if a homeomorphism of `ℝ × [a, b]` commuting with the deck translation
maps the horizontal line at height `c` into itself, so does its inverse. -/
private theorem snd_symm_apply_of_forall_eq (hℓ : ℓ ≠ 0)
    (hd : ∀ p : ℝ × Icc a b, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) {c : ℝ}
    (hc : ∀ p : ℝ × Icc a b, (p.2 : ℝ) = c → ((F p).2 : ℝ) = c) (p : ℝ × Icc a b)
    (hp : (p.2 : ℝ) = c) : ((F.symm p).2 : ℝ) = c :=
  (congrArg Subtype.val (snd_symm_apply_of_mapsTo_line hℓ hd
    (fun x => Subtype.ext ((hc (x, p.2) hp).trans hp.symm)) p.1)).trans hp

/-- **Negative twist lifts are the inverses of positive ones.** For a nonzero period, the inverse
of a homeomorphism `F` of `ℝ × [a, b]` is a positive twist lift exactly when `F` is a negative twist
lift: it commutes with the deck translation, maps each boundary line into itself, and
`y ↦ F₁(x, y)` is strictly decreasing for every `x`. -/
theorem isTwistLift_symm_iff (hℓ : ℓ ≠ 0) :
    IsTwistLift ℓ F.symm ↔
      (∀ p : ℝ × Icc a b, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) ∧
      (∀ p : ℝ × Icc a b, (p.2 : ℝ) = a → ((F p).2 : ℝ) = a) ∧
      (∀ p : ℝ × Icc a b, (p.2 : ℝ) = b → ((F p).2 : ℝ) = b) ∧
      ∀ x : ℝ, StrictAnti fun y : Icc a b => (F (x, y)).1 := by
  constructor
  · intro h
    have hd := symm_apply_add_of_apply_add h.apply_add_period
    simp only [Homeomorph.symm_symm] at hd
    refine ⟨hd, fun p hp => ?_, fun p hp => ?_, fun x => ?_⟩
    · simpa using snd_symm_apply_of_forall_eq hℓ h.apply_add_period h.snd_apply_of_eq_left p hp
    · simpa using snd_symm_apply_of_forall_eq hℓ h.apply_add_period h.snd_apply_of_eq_right p hp
    · simpa using h.strictAnti_fst_symm_apply hℓ x
  · rintro ⟨hd, hl, hr, hanti⟩
    -- Conjugate by the reflection `(x, y) ↦ (-x, y)` to obtain a positive twist lift.
    set G := (stripReflect (Icc a b)).trans (F.trans (stripReflect (Icc a b)))
    have hdn := apply_add_int_mul_of_apply_add hd (-1)
    have hG : IsTwistLift ℓ G := by
      refine ⟨fun p => ?_, fun p hp => ?_, fun p hp => ?_, fun x => ?_⟩
      · have := hdn (-p.1) p.2
        rw [show -p.1 + ((-1 : ℤ) : ℝ) * ℓ = -(p.1 + ℓ) by push_cast; ring] at this
        simp only [G, Homeomorph.trans_apply, stripReflect_apply, this]
        exact Prod.ext (by push_cast; ring) rfl
      · simpa [G, stripReflect_apply] using hl (-p.1, p.2) hp
      · simpa [G, stripReflect_apply] using hr (-p.1, p.2) hp
      · simpa [G, stripReflect_apply, Function.comp_def] using (hanti (-x)).neg
    refine ⟨symm_apply_add_of_apply_add hd, snd_symm_apply_of_forall_eq hℓ hd hl,
      snd_symm_apply_of_forall_eq hℓ hd hr, fun x => ?_⟩
    · have := (hG.strictAnti_fst_symm_apply hℓ (-x)).neg
      simpa [G, stripReflect_symm_apply, Function.comp_def] using this

end TauCeti
