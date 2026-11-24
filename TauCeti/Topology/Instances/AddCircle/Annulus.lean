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
import TauCeti.Algebra.Order.Archimedean.Basic
import TauCeti.Topology.Instances.AddCircle.Lift

/-!
# Maps of the strip commuting with the deck translation

The product `AddCircle ℓ × Y` is the quotient of the strip `ℝ × Y` by the deck translation
`(x, y) ↦ (x + ℓ, y)`; we call it the strip quotient. It is a closed annulus when `ℓ ≠ 0` and `Y`
is a nondegenerate closed interval, but nothing here assumes this. This file studies maps `F` of
the strip that commute with the deck translation, `F (x + ℓ, y) = (F₁(x, y) + ℓ, F₂(x, y))`. They
commute with every integer power of the deck translation, and a homeomorphism of the strip
commuting with it induces a homeomorphism of the strip quotient. For a nonzero period, a
continuous such map takes every real value in the first coordinate along every horizontal line, so
a homeomorphism mapping a horizontal line into itself maps it onto itself, increasingly.

## Main definitions

* `TauCeti.stripDeck ℓ m Y`: the deck translation `(x, y) ↦ (x + m ℓ, y)` of the strip.
* `Homeomorph.annulusHomeomorphOfLift F hF`: the homeomorphism of the strip quotient
  `AddCircle ℓ × Y` induced by a homeomorphism `F` of the strip commuting with the deck translation.

## Main results

* `TauCeti.apply_add_int_mul_of_apply_add`: a map commuting with the deck translation commutes
  with all of its integer powers.
* `TauCeti.trans_apply_add_of_apply_add`, `Homeomorph.annulusHomeomorphOfLift_trans`,
  `Homeomorph.annulusHomeomorphOfLift_symm`, `Homeomorph.annulusHomeomorphOfLift_refl`: the
  induced homeomorphism respects composition, inverses and the identity.
* `Homeomorph.eq_annulusHomeomorphOfLift`: the induced homeomorphism is the only map of the strip
  quotient sending the class of `(x, y)` to the class of `F (x, y)`.
* `TauCeti.trans_stripDeck_apply_add_of_apply_add`,
  `Homeomorph.annulusHomeomorphOfLift_trans_stripDeck`: composing with a deck translation preserves
  commuting with the deck translation and does not change the induced homeomorphism.
* `TauCeti.surjective_fst_apply_of_apply_add`, `TauCeti.strictMono_fst_of_mapsTo_line`,
  `TauCeti.snd_symm_apply_of_mapsTo_line`: for `ℓ ≠ 0`, a homeomorphism of the strip commuting
  with the deck translation and mapping a horizontal line into itself restricts to an increasing
  homeomorphism of that line.
* `Homeomorph.image_annulusHomeomorphOfLift_of_mapsTo_line`: the induced homeomorphism of the
  strip quotient then maps the image `{z | z.2 = y}` of that line onto itself.
-/

public section

open Function Set

namespace TauCeti

variable {Y : Type*} {ℓ : ℝ}

/-- A map of the strip commuting with the deck translation `(x, y) ↦ (x + ℓ, y)` commutes with all
of its integer powers. -/
theorem apply_add_int_mul_of_apply_add {F : ℝ × Y → ℝ × Y}
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) (n : ℤ) (x : ℝ) (y : Y) :
    F (x + n * ℓ, y) = ((F (x, y)).1 + n * ℓ, (F (x, y)).2) :=
  Prod.ext
    (AddCircle.lift_add_int_mul (F := fun x ↦ (F (x, y)).1)
      (fun x ↦ congrArg Prod.fst (hF (x, y))) x n)
    (Periodic.int_mul (f := fun x ↦ (F (x, y)).2)
      (fun x ↦ by simpa using congrArg Prod.snd (hF (x, y))) n x)

/-- For a nonzero period, the first coordinate of a map of the strip commuting with the deck
translation and continuous along a horizontal line takes every real value along that line. -/
theorem surjective_fst_apply_of_apply_add {F : ℝ × Y → ℝ × Y} (hℓ : ℓ ≠ 0)
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) {y : Y}
    (hc : Continuous fun x : ℝ => (F (x, y)).1) :
    Surjective fun x : ℝ => (F (x, y)).1 := by
  intro z
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

/-- For a map `F` of the strip commuting with the deck translation and a fixed height `y`, the
function of `x : ℝ` sending `x` to `F (x, y)` with its first coordinate reduced modulo `ℓ` is
`ℓ`-periodic. -/
theorem periodic_coe_apply_of_apply_add {F : ℝ × Y → ℝ × Y}
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) (y : Y) :
    Periodic (fun x : ℝ => Prod.map ((↑) : ℝ → AddCircle ℓ) id (F (x, y))) ℓ := by
  intro x
  refine Prod.ext ?_ ?_ <;> simp [hF (x, y)]

variable [TopologicalSpace Y]

/-- The inverse of a homeomorphism of the strip commuting with the deck translation commutes with
it too. -/
theorem symm_apply_add_of_apply_add {F : ℝ × Y ≃ₜ ℝ × Y}
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) (p : ℝ × Y) :
    F.symm (p.1 + ℓ, p.2) = ((F.symm p).1 + ℓ, (F.symm p).2) := by
  apply F.injective
  rw [F.apply_symm_apply, hF, F.apply_symm_apply]

variable (ℓ) in
/-- The deck translation `(x, y) ↦ (x + m ℓ, y)` of the strip `ℝ × Y`. -/
def stripDeck (m : ℤ) (Y : Type*) [TopologicalSpace Y] : ℝ × Y ≃ₜ ℝ × Y :=
  (Homeomorph.addRight ((m : ℝ) * ℓ)).prodCongr (Homeomorph.refl Y)

/-- The deck translation shifts the first coordinate by `m ℓ`. -/
@[simp]
theorem stripDeck_apply (m : ℤ) (p : ℝ × Y) : stripDeck ℓ m Y p = (p.1 + m * ℓ, p.2) :=
  (rfl)

/-- The inverse deck translation shifts the first coordinate by `-m ℓ`. -/
@[simp]
theorem stripDeck_symm_apply (m : ℤ) (p : ℝ × Y) :
    (stripDeck ℓ m Y).symm p = (p.1 - m * ℓ, p.2) := by
  rw [Homeomorph.symm_apply_eq, stripDeck_apply, sub_add_cancel]

variable (ℓ Y) in
/-- The deck translation by `0` is the identity. -/
@[simp]
theorem stripDeck_zero : stripDeck ℓ 0 Y = Homeomorph.refl (ℝ × Y) :=
  Homeomorph.ext fun p ↦ by simp

/-- The inverse of the deck translation by `m` is the deck translation by `-m`. -/
theorem stripDeck_symm (m : ℤ) : (stripDeck ℓ m Y).symm = stripDeck ℓ (-m) Y :=
  Homeomorph.ext fun p ↦ by simp [sub_eq_add_neg]

/-- Successive deck translations by `m` and `m'` are the deck translation by `m + m'`. -/
@[simp]
theorem stripDeck_trans_stripDeck (m m' : ℤ) :
    (stripDeck ℓ m Y).trans (stripDeck ℓ m' Y) = stripDeck ℓ (m + m') Y :=
  Homeomorph.ext fun p ↦ by simp [add_mul, add_assoc]

/-- The composition of two maps of the strip commuting with the deck translation commutes with it
too. -/
theorem trans_apply_add_of_apply_add {F G : ℝ × Y ≃ₜ ℝ × Y}
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2))
    (hG : ∀ p : ℝ × Y, G (p.1 + ℓ, p.2) = ((G p).1 + ℓ, (G p).2)) (p : ℝ × Y) :
    F.trans G (p.1 + ℓ, p.2) = ((F.trans G p).1 + ℓ, (F.trans G p).2) := by
  simp only [Homeomorph.trans_apply, hF p, hG]

/-- Composing a homeomorphism of the strip commuting with the deck translation with a deck
translation gives a homeomorphism commuting with it too. -/
theorem trans_stripDeck_apply_add_of_apply_add {F : ℝ × Y ≃ₜ ℝ × Y}
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) (m : ℤ) (p : ℝ × Y) :
    F.trans (stripDeck ℓ m Y) (p.1 + ℓ, p.2) =
      ((F.trans (stripDeck ℓ m Y) p).1 + ℓ, (F.trans (stripDeck ℓ m Y) p).2) := by
  simp [hF p, add_right_comm]

/-- For a nonzero period, a homeomorphism of the strip commuting with the deck translation and
mapping the horizontal line at height `y` into itself is strictly increasing along that line. -/
theorem strictMono_fst_of_mapsTo_line {F : ℝ × Y ≃ₜ ℝ × Y} (hℓ : ℓ ≠ 0)
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

/-- For a nonzero period, the inverse of a homeomorphism of the strip commuting with the deck
translation and mapping the horizontal line at height `y` into itself maps that line into itself. -/
theorem snd_symm_apply_of_mapsTo_line {F : ℝ × Y ≃ₜ ℝ × Y} (hℓ : ℓ ≠ 0)
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) {y : Y}
    (hy : ∀ x : ℝ, (F (x, y)).2 = y) (x : ℝ) : (F.symm (x, y)).2 = y := by
  obtain ⟨x', hx'⟩ := surjective_fst_apply_of_apply_add hℓ hF (y := y) (by fun_prop) x
  rw [show (x, y) = F (x', y) from Prod.ext hx'.symm (hy x').symm, F.symm_apply_apply]

/-- A continuous map of the strip commuting with the deck translation induces a continuous map
of the strip quotient. -/
private theorem continuous_lift_periodic_coe_apply {G : ℝ × Y → ℝ × Y}
    (hG : ∀ p : ℝ × Y, G (p.1 + ℓ, p.2) = ((G p).1 + ℓ, (G p).2)) (hc : Continuous G) :
    Continuous fun z : AddCircle ℓ × Y => (periodic_coe_apply_of_apply_add hG z.2).lift z.1 := by
  rw [← (QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id).continuous_comp_iff]
  have : (fun z : AddCircle ℓ × Y => (periodic_coe_apply_of_apply_add hG z.2).lift z.1) ∘
      Prod.map QuotientAddGroup.mk id = Prod.map ((↑) : ℝ → AddCircle ℓ) id ∘ G := by
    ext p <;> simp
  rw [this]
  exact (continuous_quotient_mk'.prodMap continuous_id).comp hc

end TauCeti

namespace Homeomorph

open TauCeti

variable {Y : Type*} [TopologicalSpace Y] {ℓ : ℝ}

/-- The homeomorphism of the strip quotient `AddCircle ℓ × Y` induced by a homeomorphism `F` of
the strip `ℝ × Y` commuting with the deck translation `(x, y) ↦ (x + ℓ, y)`: it sends the class
of `(x, y)` to the class of `F (x, y)` (`Homeomorph.annulusHomeomorphOfLift_coe`). -/
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
  continuous_toFun := continuous_lift_periodic_coe_apply hF F.continuous
  continuous_invFun :=
    continuous_lift_periodic_coe_apply (symm_apply_add_of_apply_add hF) F.symm.continuous

variable {F : ℝ × Y ≃ₜ ℝ × Y}

/-- The induced homeomorphism of the strip quotient sends the class of `(x, y)` to the class of
`F (x, y)`. -/
@[simp]
theorem annulusHomeomorphOfLift_coe
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) (x : ℝ) (y : Y) :
    F.annulusHomeomorphOfLift hF ((x : AddCircle ℓ), y) =
      (((F (x, y)).1 : AddCircle ℓ), (F (x, y)).2) :=
  (rfl)

/-- The inverse of the induced homeomorphism of the strip quotient is induced by the inverse of
`F`. Simp normalizes the inverse with `Homeomorph.annulusHomeomorphOfLift_symm` instead. -/
theorem annulusHomeomorphOfLift_symm_coe
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) (x : ℝ) (y : Y) :
    (F.annulusHomeomorphOfLift hF).symm ((x : AddCircle ℓ), y) =
      (((F.symm (x, y)).1 : AddCircle ℓ), (F.symm (x, y)).2) :=
  (rfl)

/-- The induced homeomorphism of the strip quotient is the unique map `H` sending the class of
`(x, y)` to the class of `F (x, y)`. -/
theorem eq_annulusHomeomorphOfLift
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2))
    {H : AddCircle ℓ × Y ≃ₜ AddCircle ℓ × Y}
    (hHF : ∀ (x : ℝ) (y : Y), H ((x : AddCircle ℓ), y) =
      (((F (x, y)).1 : AddCircle ℓ), (F (x, y)).2)) :
    H = F.annulusHomeomorphOfLift hF := by
  ext ⟨θ, y⟩
  all_goals
    induction θ using QuotientAddGroup.induction_on with | H x => ?_
    simp [hHF]

/-- The inverse of the induced homeomorphism of the strip quotient is induced by the inverse of
`F`. -/
@[simp]
theorem annulusHomeomorphOfLift_symm
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) :
    (F.annulusHomeomorphOfLift hF).symm =
      F.symm.annulusHomeomorphOfLift (symm_apply_add_of_apply_add hF) :=
  (rfl)

/-- The identity of the strip induces the identity of the strip quotient. -/
@[simp]
theorem annulusHomeomorphOfLift_refl
    (hF : ∀ p : ℝ × Y, Homeomorph.refl (ℝ × Y) (p.1 + ℓ, p.2) =
      ((Homeomorph.refl (ℝ × Y) p).1 + ℓ, (Homeomorph.refl (ℝ × Y) p).2)) :
    (Homeomorph.refl (ℝ × Y)).annulusHomeomorphOfLift hF = Homeomorph.refl _ :=
  (eq_annulusHomeomorphOfLift hF fun _ _ ↦ rfl).symm

/-- The homeomorphism of the strip quotient induced by `F.trans G` is the composition of those
induced by `F` and `G`. -/
@[simp]
theorem annulusHomeomorphOfLift_trans {G : ℝ × Y ≃ₜ ℝ × Y}
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2))
    (hG : ∀ p : ℝ × Y, G (p.1 + ℓ, p.2) = ((G p).1 + ℓ, (G p).2)) :
    (F.trans G).annulusHomeomorphOfLift (trans_apply_add_of_apply_add hF hG) =
      (F.annulusHomeomorphOfLift hF).trans (G.annulusHomeomorphOfLift hG) :=
  (eq_annulusHomeomorphOfLift _ fun _ _ ↦ by simp).symm

/-- Composing `F` with a deck translation does not change the induced homeomorphism of the strip
quotient. The proof that `F` commutes with the deck translation is recovered from `h` by composing
with the inverse deck translation, so simp fixes every argument by matching the left-hand side. -/
@[simp]
theorem annulusHomeomorphOfLift_trans_stripDeck (m : ℤ)
    (h : ∀ p : ℝ × Y, F.trans (stripDeck ℓ m Y) (p.1 + ℓ, p.2) =
      ((F.trans (stripDeck ℓ m Y) p).1 + ℓ, (F.trans (stripDeck ℓ m Y) p).2)) :
    (F.trans (stripDeck ℓ m Y)).annulusHomeomorphOfLift h =
      F.annulusHomeomorphOfLift (by
        simpa using trans_stripDeck_apply_add_of_apply_add h (-m)) := by
  ext ⟨θ, y⟩
  all_goals
    induction θ using QuotientAddGroup.induction_on with | H x => ?_
    simp

/-- For a nonzero period, if `F` maps the horizontal line at height `y` into itself, the induced
homeomorphism of the strip quotient maps the image `{z | z.2 = y}` of that line onto itself. -/
theorem image_annulusHomeomorphOfLift_of_mapsTo_line (hℓ : ℓ ≠ 0)
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) {y : Y}
    (hy : ∀ x : ℝ, (F (x, y)).2 = y) :
    F.annulusHomeomorphOfLift hF '' {z | z.2 = y} = {z | z.2 = y} := by
  ext ⟨θ, y'⟩
  induction θ using QuotientAddGroup.induction_on with | H x => ?_
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨θ', y''⟩, rfl, hz⟩
    induction θ' using QuotientAddGroup.induction_on with | H x' => ?_
    rw [annulusHomeomorphOfLift_coe] at hz
    rw [← (Prod.mk.inj hz).2]
    exact hy x'
  · rintro rfl
    refine ⟨(F.annulusHomeomorphOfLift hF).symm ((x : AddCircle ℓ), y'), ?_, by simp⟩
    rw [annulusHomeomorphOfLift_symm_coe]
    exact snd_symm_apply_of_mapsTo_line hℓ hF hy x

/-- For a nonzero period, if at most one height `y` satisfies `p y` and `F` maps the horizontal
lines at such heights into themselves, the induced homeomorphism of the strip quotient maps the
set of points at such heights onto itself. -/
theorem image_annulusHomeomorphOfLift_setOf_of_subsingleton (hℓ : ℓ ≠ 0)
    (hF : ∀ p : ℝ × Y, F (p.1 + ℓ, p.2) = ((F p).1 + ℓ, (F p).2)) {p : Y → Prop}
    (hp : ∀ y y', p y → p y' → y = y') (hy : ∀ x y, p y → p (F (x, y)).2) :
    F.annulusHomeomorphOfLift hF '' {z | p z.2} = {z | p z.2} := by
  by_cases h : ∃ y, p y
  · obtain ⟨y, hy₀⟩ := h
    have hs : {z : AddCircle ℓ × Y | p z.2} = {z | z.2 = y} :=
      Set.ext fun z ↦ ⟨fun hz ↦ hp _ _ hz hy₀, fun hz ↦ by
        simp only [Set.mem_ofPred_eq] at hz ⊢
        exact hz ▸ hy₀⟩
    rw [hs]
    exact image_annulusHomeomorphOfLift_of_mapsTo_line hℓ hF fun x ↦ hp _ _ (hy x y hy₀) hy₀
  · have hs : {z : AddCircle ℓ × Y | p z.2} = ∅ :=
      Set.eq_empty_of_forall_notMem fun z hz ↦ h ⟨z.2, hz⟩
    simp [hs]

end Homeomorph
