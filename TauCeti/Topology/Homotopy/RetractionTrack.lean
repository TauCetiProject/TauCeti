/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# Replacing an annulus by a retraction track

Let `R` deform `X` onto a subset `B`, fixing `B` pointwise. An annulus
`γ : C(I × S, X)` whose outer boundary lies in `B` can be deformed to the track
`(r, θ) ↦ R (β r, γ (0, θ))`, where `β` is any continuous function from `I` to itself
with endpoints `0` and `1`. The deformation fixes the inner boundary and keeps the outer
boundary in `B`. Thus it can be glued to a deformation of the disc bounded by the inner circle.

There are two stages: first apply `R (t * β r, γ (r, θ))`, then apply
`R (β r, γ ((1-t) * r, θ))`. At their common endpoint these formulas agree. In the
second stage the outer boundary lies in `B` because the retraction has run to time `1`;
it need not be fixed pointwise. Tracks also extend homotopies of the inner circle.

This is the annulus construction used in comparing the characteristic discs of Morse charts.
See J. Milnor, *Morse Theory*, Princeton University Press, 1963, §3, Remark 3.3.
The concatenation is Mathlib's `ContinuousMap.HomotopyWith.trans`.
-/

public section

open Set unitInterval

namespace ContinuousMap.Homotopy

variable {X Y S : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace S]
  {f₀ f₁ : C(X, Y)}

/-- The track swept out by a map under a deformation, with radial time prescribed by `β`. -/
def retractionTrack (R : f₀.Homotopy f₁) (β : C(I, I)) (a : C(S, X)) :
    C(I × S, Y) where
  toFun p := R (β p.1, a p.2)
  continuous_toFun := R.continuous.comp (by fun_prop)

@[simp]
theorem retractionTrack_apply (R : f₀.Homotopy f₁) (β : C(I, I))
    (a : C(S, X)) (p : I × S) : R.retractionTrack β a p = R (β p.1, a p.2) :=
  (rfl)

/-- A homotopy of inner circles extends continuously to their entire retraction tracks. -/
def retractionTrackHomotopy (R : f₀.Homotopy f₁) (β : C(I, I))
    {a₀ a₁ : C(S, X)} (K : a₀.Homotopy a₁) :
    (R.retractionTrack β a₀).Homotopy (R.retractionTrack β a₁) where
  toFun p := R (β p.2.1, K (p.1, p.2.2))
  continuous_toFun := R.continuous.comp (by fun_prop)
  map_zero_left s := by simp
  map_one_left s := by simp

@[simp]
theorem retractionTrackHomotopy_apply (R : f₀.Homotopy f₁) (β : C(I, I))
    {a₀ a₁ : C(S, X)} (K : a₀.Homotopy a₁) (p : I × (I × S)) :
    R.retractionTrackHomotopy β K p = R (β p.2.1, K (p.1, p.2.2)) :=
  (rfl)

/-- The outer boundary of the track homotopy remains in any set containing the end map. -/
theorem retractionTrackHomotopy_one_mem (R : f₀.Homotopy f₁)
    {B : Set Y} (hr : ∀ x, f₁ x ∈ B) {β : C(I, I)} (hβ : β 1 = 1)
    {a₀ a₁ : C(S, X)} (K : a₀.Homotopy a₁) (t : I) (s : S) :
    R.retractionTrackHomotopy β K (t, 1, s) ∈ B := by
  simpa [hβ] using hr (K (t, s))

end ContinuousMap.Homotopy

namespace ContinuousMap.HomotopyRel

variable {X S : Type*} [TopologicalSpace X] [TopologicalSpace S]
  {r : C(X, X)} {B : Set X}

/-- Replace an annulus by the retraction track of its inner boundary. The inner seam is fixed
pointwise and the outer boundary stays in `B` throughout. The first half runs the retraction
with time `t * β r`; the second half collapses the radial argument of the original annulus.
Only endpoint conditions on `β` are needed. -/
noncomputable def annulusToTrack (R : (ContinuousMap.id X).HomotopyRel r B) (hr : ∀ x, r x ∈ B)
    (γ : C(I × S, X)) (hγ : ∀ s, γ (1, s) ∈ B) (β : C(I, I))
    (hβ₀ : β 0 = 0) (hβ₁ : β 1 = 1) :
    γ.HomotopyWith
      (R.toHomotopy.retractionTrack β ⟨fun s ↦ γ (0, s), by fun_prop⟩)
      (fun g ↦ (∀ s, g (0, s) = γ (0, s)) ∧ ∀ s, g (1, s) ∈ B) := by
  let middle : C(I × S, X) := ⟨fun p ↦ R (β p.1, γ p), R.continuous.comp (by fun_prop)⟩
  -- First push the outer boundary along the retraction, keeping the inner seam fixed.
  let F : γ.HomotopyWith middle
      (fun g ↦ (∀ s, g (0, s) = γ (0, s)) ∧ ∀ s, g (1, s) ∈ B) :=
    { toFun := fun p ↦ R (p.1 * β p.2.1, γ p.2)
      continuous_toFun := R.continuous.comp (by
        refine Continuous.prodMk ?_ (by fun_prop)
        apply Continuous.subtype_mk
        fun_prop)
      map_zero_left := fun p ↦ by simp
      map_one_left := fun p ↦ by simp [middle]
      prop' := fun t ↦ ⟨fun s ↦ by simp [hβ₀], fun s ↦ by
        simpa only [ContinuousMap.coe_mk] using
          (R.eq_fst (t * β 1) (hγ s)).symm ▸ hγ s⟩ }
  -- Then slide every radial argument to zero. At the outer edge R has reached time one.
  let G : middle.HomotopyWith
      (R.toHomotopy.retractionTrack β ⟨fun s ↦ γ (0, s), by fun_prop⟩)
      (fun g ↦ (∀ s, g (0, s) = γ (0, s)) ∧ ∀ s, g (1, s) ∈ B) :=
    { toFun := fun p ↦ R (β p.2.1, γ (unitInterval.symm p.1 * p.2.1, p.2.2))
      continuous_toFun := R.continuous.comp (by
        refine Continuous.prodMk (by fun_prop) (γ.continuous.comp ?_)
        refine Continuous.prodMk ?_ (by fun_prop)
        apply Continuous.subtype_mk
        fun_prop)
      map_zero_left := fun p ↦ by simp [middle]
      map_one_left := fun p ↦ by
        simpa only [unitInterval.symm_one, zero_mul, Homotopy.retractionTrack_apply,
          ContinuousMap.coe_mk] using
          (congrFun R.coe_toHomotopy (β p.1, γ (0, p.2))).symm
      prop' := fun t ↦ ⟨fun s ↦ by simp [hβ₀], fun s ↦ by
        simpa [hβ₁] using hr (γ (unitInterval.symm t * 1, s))⟩ }
  exact F.trans G

/-- Explicit formulas for both stages of the annulus deformation. At time `1/2` both
formulas give `R (β r, γ (r, θ))`, so the two stages glue continuously. -/
theorem annulusToTrack_apply (R : (ContinuousMap.id X).HomotopyRel r B)
    (hr : ∀ x, r x ∈ B) (γ : C(I × S, X)) (hγ : ∀ s, γ (1, s) ∈ B)
    (β : C(I, I)) (hβ₀ : β 0 = 0) (hβ₁ : β 1 = 1) (p : I × (I × S)) :
    R.annulusToTrack hr γ hγ β hβ₀ hβ₁ p =
      if h : (p.1 : ℝ) ≤ 1 / 2 then
        R (⟨2 * p.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨p.1.2.1, h⟩⟩ *
          β p.2.1, γ p.2)
      else
        R (β p.2.1, γ (unitInterval.symm
          ⟨2 * p.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 h).le, p.1.2.2⟩⟩ * p.2.1, p.2.2)) := by
  exact HomotopyWith.trans_apply _ _ _

end ContinuousMap.HomotopyRel
