/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Order.IntermediateValue

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
* `TauCeti.annulusHomeomorphOfLift F hF`: the homeomorphism of the annulus `AddCircle ℓ × Y`
  induced by a homeomorphism `F` of the strip `ℝ × Y` commuting with the deck translation.
* `TauCeti.stripDeck ℓ m Y`: the deck translation `(x, y) ↦ (x + m ℓ, y)` of the strip.

## Main results

* `TauCeti.strictMono_fst_of_mapsTo_line`, `TauCeti.surjective_fst_apply_of_apply_add`: for
  `ℓ ≠ 0`, a homeomorphism of the strip commuting with the deck translation and mapping a
  horizontal line into itself restricts to an increasing homeomorphism of that line. In particular
  a twist lift maps each boundary line onto itself preserving its direction
  (`TauCeti.IsTwistLift.strictMono_fst`), and so does the induced homeomorphism of the annulus on
  each boundary circle (`TauCeti.IsTwistLift.image_annulusHomeomorphOfLift_eq_left`,
  `TauCeti.IsTwistLift.image_annulusHomeomorphOfLift_eq_right`).
* `TauCeti.IsTwistLift.strictAnti_fst_symm`: the inverse of a positive twist lift is a negative
  twist lift, and `TauCeti.isTwistLift_symm_iff`: a homeomorphism is a negative twist lift exactly
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

/-! ### Homeomorphisms of the strip commuting with the deck translation -/

section Deck

variable {F : ℝ × Y ≃ₜ ℝ × Y}

/-- A homeomorphism of the strip commuting with the deck translation `(x, y) ↦ (x + ℓ, y)` commutes
with all of its integer powers. -/
theorem apply_add_int_mul_of_apply_add (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2))
    (n : ℤ) (x : ℝ) (y : Y) :
    F (x + n * ℓ, y) = ((F (x, y)).1 + n * ℓ, (F (x, y)).2) := by
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    simp only [Int.cast_natCast] at ih
    have h := hF (x + n * ℓ, y)
    rw [ih x] at h
    rw [show x + ((n + 1 : ℤ) : ℝ) * ℓ = x + n * ℓ + ℓ by push_cast; ring, h]
    ext
    · simp only
      push_cast
      ring
    · rfl
  | pred n ih =>
    have h := hF (x + (-(n : ℤ) - 1 : ℤ) * ℓ, y)
    rw [show x + ((-(n : ℤ) - 1 : ℤ) : ℝ) * ℓ + ℓ = x + (-(n : ℤ) : ℤ) * ℓ by push_cast; ring,
      ih] at h
    ext
    · have := congrArg Prod.fst h
      simp only at this
      push_cast at this ⊢
      linarith
    · simpa using (congrArg Prod.snd h).symm

/-- The inverse of a homeomorphism of the strip commuting with the deck translation commutes with
it too. -/
theorem symm_apply_add_of_apply_add (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2))
    (p : ℝ × Y) :
    F.symm (p.1 + ℓ, p.2) = ((F.symm p).1 + ℓ, (F.symm p).2) := by
  apply F.injective
  rw [F.apply_symm_apply, hF, F.apply_symm_apply]

/-- The deck translation `(x, y) ↦ (x + m ℓ, y)` of the strip `ℝ × Y`. -/
def stripDeck (ℓ : ℝ) (m : ℤ) (Y : Type*) [TopologicalSpace Y] : ℝ × Y ≃ₜ ℝ × Y :=
  (Homeomorph.addRight ((m : ℝ) * ℓ)).prodCongr (Homeomorph.refl Y)

/-- The deck translation shifts the first coordinate by `m ℓ`. -/
@[simp]
theorem stripDeck_apply (m : ℤ) (p : ℝ × Y) : stripDeck ℓ m Y p = (p.1 + m * ℓ, p.2) := by
  rfl

/-- There is an integer multiple of a nonzero period exceeding any given real number. -/
private theorem exists_int_mul_gt (hℓ : ℓ ≠ 0) (r : ℝ) : ∃ k : ℤ, r < k * ℓ := by
  rcases hℓ.lt_or_gt with h | h
  · obtain ⟨k, hk⟩ := exists_int_lt (r / ℓ)
    exact ⟨k, (lt_div_iff_of_neg h).1 hk⟩
  · obtain ⟨k, hk⟩ := exists_int_gt (r / ℓ)
    exact ⟨k, (div_lt_iff₀ h).1 hk⟩

/-- For a nonzero period, a homeomorphism of the strip commuting with the deck translation and
mapping the horizontal line at height `y` into itself is strictly increasing along that line. -/
theorem strictMono_fst_of_mapsTo_line (hℓ : ℓ ≠ 0)
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) {y : Y}
    (hy : ∀ x : ℝ, (F (x, y)).2 = y) : StrictMono fun x : ℝ => (F (x, y)).1 := by
  have hc : Continuous fun x : ℝ => (F (x, y)).1 := by fun_prop
  have hi : Injective fun x : ℝ => (F (x, y)).1 := by
    intro x x' h
    have : F (x, y) = F (x', y) := Prod.ext h (by rw [hy, hy])
    simpa using F.injective this
  refine (hc.strictMono_of_inj hi).resolve_right fun hanti => ?_
  have h1 := apply_add_int_mul_of_apply_add hF 1 0 y
  simp only [Int.cast_one, one_mul, zero_add] at h1
  have h2 : (F (ℓ, y)).1 = (F (0, y)).1 + ℓ := by rw [h1]
  rcases hℓ.lt_or_gt with h | h
  · have := hanti h
    simp only at this
    linarith
  · have := hanti h
    simp only at this
    linarith

/-- For a nonzero period, the first coordinate of a homeomorphism of the strip commuting with the
deck translation takes every real value along every horizontal line. So if it maps a horizontal
line into itself, it maps it onto itself. -/
theorem surjective_fst_apply_of_apply_add (hℓ : ℓ ≠ 0)
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) {y : Y} :
    Surjective fun x : ℝ => (F (x, y)).1 := by
  intro z
  have hc : Continuous fun x : ℝ => (F (x, y)).1 := by fun_prop
  have hg (n : ℤ) : (F (n * ℓ, y)).1 = (F (0, y)).1 + n * ℓ := by
    simpa using congrArg Prod.fst (apply_add_int_mul_of_apply_add hF n 0 y)
  obtain ⟨k, hk⟩ := exists_int_mul_gt hℓ |z - (F (0, y)).1|
  have hk' := hg (-k)
  have hkk := hg k
  push_cast at hk'
  have hk0 : 0 ≤ (k : ℝ) * ℓ := (abs_nonneg _).trans hk.le
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc (show (-k : ℝ) * ℓ ≤ k * ℓ by linarith)
    hc.continuousOn (show z ∈ Icc (F (-k * ℓ, y)).1 (F (k * ℓ, y)).1 by
      rw [hk', hkk]
      constructor <;> linarith [neg_abs_le (z - (F (0, y)).1), le_abs_self (z - (F (0, y)).1)])
  exact ⟨x, hx⟩

/-- For a nonzero period, the inverse of a homeomorphism of the strip commuting with the deck
translation and mapping the horizontal line at height `y` into itself maps that line into itself. -/
theorem snd_symm_apply_of_mapsTo_line (hℓ : ℓ ≠ 0)
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) {y : Y}
    (hy : ∀ x : ℝ, (F (x, y)).2 = y) (x : ℝ) : (F.symm (x, y)).2 = y := by
  obtain ⟨x', hx'⟩ := surjective_fst_apply_of_apply_add hℓ hF (y := y) x
  rw [show (x, y) = F (x', y) from Prod.ext hx'.symm (hy x').symm, F.symm_apply_apply]

/-! ### The homeomorphism of the annulus -/

/-- A homeomorphism of the strip commuting with the deck translation induces, for each height, a
map of the strip into the annulus that is periodic in the first coordinate. -/
theorem periodic_coe_apply_of_apply_add
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) (y : Y) :
    Periodic (fun x : ℝ => Prod.map ((↑) : ℝ → AddCircle ℓ) id (F (x, y))) ℓ := by
  intro x
  simp [hF (x, y)]
  rfl

/-- The homeomorphism of the annulus `AddCircle ℓ × Y` induced by a homeomorphism `F` of the strip
`ℝ × Y` commuting with the deck translation `(x, y) ↦ (x + ℓ, y)`: it sends the class of `(x, y)`
to the class of `F (x, y)` (`TauCeti.annulusHomeomorphOfLift_coe`). -/
def annulusHomeomorphOfLift (F : ℝ × Y ≃ₜ ℝ × Y)
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) :
    AddCircle ℓ × Y ≃ₜ AddCircle ℓ × Y where
  toFun z := (periodic_coe_apply_of_apply_add hF z.2).lift z.1
  invFun z := (periodic_coe_apply_of_apply_add (symm_apply_add_of_apply_add hF) z.2).lift z.1
  left_inv := by
    rintro ⟨θ, y⟩
    induction θ using QuotientAddGroup.induction_on with | H x => ?_
    simp
  right_inv := by
    rintro ⟨θ, y⟩
    induction θ using QuotientAddGroup.induction_on with | H x => ?_
    simp
  continuous_toFun := by
    rw [← (QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id).continuous_comp_iff]
    have : (fun z : AddCircle ℓ × Y => (periodic_coe_apply_of_apply_add hF z.2).lift z.1) ∘
        Prod.map QuotientAddGroup.mk id = Prod.map ((↑) : ℝ → AddCircle ℓ) id ∘ F := by
      ext p <;> simp
    rw [this]
    exact (continuous_quotient_mk'.prodMap continuous_id).comp F.continuous
  continuous_invFun := by
    rw [← (QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id).continuous_comp_iff]
    have : (fun z : AddCircle ℓ × Y =>
        (periodic_coe_apply_of_apply_add (symm_apply_add_of_apply_add hF) z.2).lift z.1) ∘
        Prod.map QuotientAddGroup.mk id = Prod.map ((↑) : ℝ → AddCircle ℓ) id ∘ F.symm := by
      ext p <;> simp
    rw [this]
    exact (continuous_quotient_mk'.prodMap continuous_id).comp F.symm.continuous

/-- The induced homeomorphism of the annulus sends the class of `(x, y)` to the class of
`F (x, y)`. -/
@[simp]
theorem annulusHomeomorphOfLift_coe
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) (x : ℝ) (y : Y) :
    annulusHomeomorphOfLift F hF ((x : AddCircle ℓ), y) =
      (((F (x, y)).1 : AddCircle ℓ), (F (x, y)).2) := by
  simp [annulusHomeomorphOfLift]
  rfl

/-- The inverse of the induced homeomorphism of the annulus is induced by the inverse of `F`. -/
@[simp]
theorem annulusHomeomorphOfLift_symm_coe
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) (x : ℝ) (y : Y) :
    (annulusHomeomorphOfLift F hF).symm ((x : AddCircle ℓ), y) =
      (((F.symm (x, y)).1 : AddCircle ℓ), (F.symm (x, y)).2) := by
  simp [annulusHomeomorphOfLift]
  rfl

/-- For a nonzero period, if `F` maps the horizontal line at height `y` into itself, the induced
homeomorphism of the annulus maps the circle at height `y` onto itself. -/
theorem image_annulusHomeomorphOfLift_of_mapsTo_line (hℓ : ℓ ≠ 0)
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) {y : Y}
    (hy : ∀ x : ℝ, (F (x, y)).2 = y) :
    annulusHomeomorphOfLift F hF '' {z | z.2 = y} = {z | z.2 = y} := by
  ext ⟨θ, y'⟩
  induction θ using QuotientAddGroup.induction_on with | H x => ?_
  constructor
  · rintro ⟨⟨θ', y''⟩, hy'', hz⟩
    induction θ' using QuotientAddGroup.induction_on with | H x' => ?_
    change y'' = y at hy''
    change y' = y
    subst hy''
    rw [annulusHomeomorphOfLift_coe] at hz
    have h₂ := congrArg Prod.snd hz
    simp only at h₂
    rw [← h₂]
    exact hy x'
  · intro h
    change y' = y at h
    subst h
    refine ⟨(annulusHomeomorphOfLift F hF).symm ((x : AddCircle ℓ), y'), ?_, by simp⟩
    change ((annulusHomeomorphOfLift F hF).symm ((x : AddCircle ℓ), y')).2 = y'
    rw [annulusHomeomorphOfLift_symm_coe]
    exact snd_symm_apply_of_mapsTo_line hℓ hF hy x

end Deck

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
theorem strictMono_fst (hℓ : ℓ ≠ 0) {y : Icc a b} (hy : (y : ℝ) = a ∨ (y : ℝ) = b) :
    StrictMono fun x : ℝ => (F (x, y)).1 :=
  strictMono_fst_of_mapsTo_line hℓ hF.apply_add_period (hF.snd_apply_of_mem_boundary hy)

/-- The homeomorphism of the annulus `AddCircle ℓ × [a, b]` induced by a twist lift with nonzero
period maps the lower boundary circle onto itself. -/
theorem image_annulusHomeomorphOfLift_eq_left (hℓ : ℓ ≠ 0) :
    annulusHomeomorphOfLift F hF.apply_add_period '' {z | (z.2 : ℝ) = a} =
      {z | (z.2 : ℝ) = a} := by
  rcases isEmpty_or_nonempty {y : Icc a b // (y : ℝ) = a} with h | ⟨⟨y, hy⟩⟩
  · have : {z : AddCircle ℓ × Icc a b | (z.2 : ℝ) = a} = ∅ :=
      eq_empty_of_forall_notMem fun z hz => h.elim ⟨z.2, hz⟩
    simp [this]
  · have hs : {z : AddCircle ℓ × Icc a b | (z.2 : ℝ) = a} = {z | z.2 = y} := by
      ext z
      exact ⟨fun h => Subtype.ext (h.trans hy.symm), fun h => by
        change (z.2 : ℝ) = a
        rw [h, hy]⟩
    rw [hs]
    exact image_annulusHomeomorphOfLift_of_mapsTo_line hℓ hF.apply_add_period
      (hF.snd_apply_of_mem_boundary (Or.inl hy))

/-- The homeomorphism of the annulus `AddCircle ℓ × [a, b]` induced by a twist lift with nonzero
period maps the upper boundary circle onto itself. -/
theorem image_annulusHomeomorphOfLift_eq_right (hℓ : ℓ ≠ 0) :
    annulusHomeomorphOfLift F hF.apply_add_period '' {z | (z.2 : ℝ) = b} =
      {z | (z.2 : ℝ) = b} := by
  rcases isEmpty_or_nonempty {y : Icc a b // (y : ℝ) = b} with h | ⟨⟨y, hy⟩⟩
  · have : {z : AddCircle ℓ × Icc a b | (z.2 : ℝ) = b} = ∅ :=
      eq_empty_of_forall_notMem fun z hz => h.elim ⟨z.2, hz⟩
    simp [this]
  · have hs : {z : AddCircle ℓ × Icc a b | (z.2 : ℝ) = b} = {z | z.2 = y} := by
      ext z
      exact ⟨fun h => Subtype.ext (h.trans hy.symm), fun h => by
        change (z.2 : ℝ) = b
        rw [h, hy]⟩
    rw [hs]
    exact image_annulusHomeomorphOfLift_of_mapsTo_line hℓ hF.apply_add_period
      (hF.snd_apply_of_mem_boundary (Or.inr hy))

/-- For a nonzero period, the inverse of a twist lift maps each boundary line into itself. -/
theorem snd_symm_apply_of_mem_boundary (hℓ : ℓ ≠ 0) {y : Icc a b}
    (hy : (y : ℝ) = a ∨ (y : ℝ) = b) (x : ℝ) : (F.symm (x, y)).2 = y :=
  snd_symm_apply_of_mapsTo_line hℓ hF.apply_add_period (hF.snd_apply_of_mem_boundary hy) x

/-- The key step for `TauCeti.IsTwistLift.strictAnti_fst_symm`: the preimage under a twist lift of
a point `(x, y)` above the lower boundary lies strictly to the left of the preimage of `(x, a)`. -/
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
    rcases (show y₀ ≤ s from Subtype.coe_le_coe.1 (by rw [hy₀]; exact s.2.1)).eq_or_lt
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

/-- **The inverse of a positive twist lift is a negative twist lift**: for a nonzero period, the
first coordinate of `F⁻¹` is strictly decreasing on every vertical. -/
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
    · have := h.snd_symm_apply_of_mem_boundary hℓ (y := p.2) (Or.inl hp) p.1
      simp only [Homeomorph.symm_symm, Prod.mk.eta] at this
      rw [this, hp]
    · have := h.snd_symm_apply_of_mem_boundary hℓ (y := p.2) (Or.inr hp) p.1
      simp only [Homeomorph.symm_symm, Prod.mk.eta] at this
      rw [this, hp]
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
    refine ⟨symm_apply_add_of_apply_add hd, fun p hp => ?_, fun p hp => ?_, fun x => ?_⟩
    · exact congrArg Subtype.val
        (snd_symm_apply_of_mapsTo_line hℓ hd (fun x => Subtype.ext ((hl (x, p.2) hp).trans hp.symm))
          p.1) |>.trans hp
    · exact congrArg Subtype.val
        (snd_symm_apply_of_mapsTo_line hℓ hd (fun x => Subtype.ext ((hr (x, p.2) hp).trans hp.symm))
          p.1) |>.trans hp
    · have := (hG.strictAnti_fst_symm_apply hℓ (-x)).neg
      simpa [G, stripReflect_symm_apply, Function.comp_def] using this

end TauCeti
