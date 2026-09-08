/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.PerfectMatching
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.FinCases

/-!
# Based oriented Gauss codes

A based oriented Gauss code records the combinatorial data seen while traversing an oriented knot
diagram from a chosen base point. There are `2 * n` visits to `n` crossings; a perfect matching
pairs the two visits at each crossing, and the Boolean `over` field records which visit passes over
the other. The `visit_eq_iff` field says that the fibres of `visit` are exactly the two-element
partner orbits, so every crossing in the image is visited exactly twice. Crossing signs are stored
separately, so mirroring a code changes signs without changing its traversal data.

This is deliberately the based combinatorial presentation, rather than a claim that every abstract
code is already realised by a planar drawing. Planar realisation, Reidemeister moves, and the
geometric-to-diagram correspondence are not treated here. The code nevertheless has the structural
operations needed by those developments: relabelling crossings, mirroring, reversing orientation,
the writhe, and the crossing-free witness. `FramedOrientedGaussCode` adds the integer framing
coefficient relative to the Seifert framing, while `UnorientedGaussCode` quotients by orientation
reversal; their projections supply the roadmap's forgetful hierarchy for this presentation.

The conventions follow Lickorish, *An Introduction to Knot Theory*, Chapter 1: `over i = true`
means that the traversal passes over at visit `i`, and a positive crossing contributes `+1` to the
writhe. The `over_partner` field guarantees that exactly one visit in each partnered pair is over.
-/

public section

namespace TauCeti

/-- A based oriented Gauss code with `n` crossings.

The perfect matching `partner` pairs the visits carrying a given crossing label. The
`visit_eq_iff` and `over_partner` fields ensure that every crossing in the traversal occurs exactly
twice, once over and once under. Since there are `2 * n` visits and `n` labels, `visit_eq_iff` also
forces every label to occur. -/
structure OrientedGaussCode (n : ℕ) where
  /-- Crossing label seen at each visit along the oriented traversal. -/
  visit : Fin (2 * n) → Fin n
  /-- Whether the strand is over (`true`) or under (`false`) at a visit. -/
  over : Fin (2 * n) → Bool
  /-- The oriented sign attached to each crossing. -/
  sign : Fin n → ℤˣ
  /-- The perfect matching pairing the two visits at each crossing. -/
  partner : PerfectMatching (Fin (2 * n))
  /-- The partner orbit is exactly the fibre of a crossing label. -/
  visit_eq_iff : ∀ i j, visit i = visit j ↔ j = i ∨ j = partner.val i
  /-- The two visits at a crossing have opposite over/under status. -/
  over_partner : ∀ i, over (partner.val i) = !over i

/-- A framed based oriented Gauss code. The integer specifies the framing relative to the Seifert
framing; forgetting it retains the oriented Gauss-code presentation. -/
structure FramedOrientedGaussCode (n : ℕ) where
  /-- Forget the framing coefficient, retaining the based oriented Gauss code. -/
  forgetFraming : OrientedGaussCode n
  /-- The framing coefficient relative to the Seifert framing. -/
  framing : ℤ

namespace OrientedGaussCode

variable {n : ℕ}

attribute [simp] OrientedGaussCode.over_partner

/-- Two Gauss codes are equal when their visit labels, over/under data, and signs agree.
The partner matching is forced by the visit labels. -/
@[ext]
theorem ext {D E : OrientedGaussCode n}
    (hvisit : D.visit = E.visit) (hover : D.over = E.over) (hsign : D.sign = E.sign) : D = E := by
  have hpartner : D.partner = E.partner := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    have hsame : D.visit i = D.visit (E.partner.val i) := by
      rw [hvisit]
      exact (E.visit_eq_iff i (E.partner.val i)).mpr (Or.inr rfl)
    rcases (D.visit_eq_iff i (E.partner.val i)).mp hsame with h | h
    · exact (E.partner.apply_ne i h).elim
    · exact h.symm
  cases D
  cases E
  cases hvisit
  cases hover
  cases hsign
  cases hpartner
  rfl

/-- Partnered visits carry the same crossing label. -/
@[simp]
theorem visit_partner (D : OrientedGaussCode n) (i : Fin (2 * n)) :
    D.visit (D.partner.val i) = D.visit i := by
  exact (D.visit_eq_iff i (D.partner.val i)).mpr (Or.inr rfl) |>.symm

/-- Every crossing label occurs in the traversal. -/
theorem visit_surjective (D : OrientedGaussCode n) : Function.Surjective D.visit := by
  classical
  let s := Finset.univ.image D.visit
  have hfiber (c : Fin n) (hc : c ∈ s) :
      (Finset.univ.filter fun i => D.visit i = c).card = 2 := by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc
    have heq : (Finset.univ.filter fun j => D.visit j = D.visit i) = {i, D.partner.val i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro h
        exact (D.visit_eq_iff i j).mp h.symm
      · intro h
        exact ((D.visit_eq_iff i j).mpr h).symm
    rw [heq]
    rw [Finset.card_insert_of_notMem]
    · simp
    · simpa using (D.partner.apply_ne i).symm
  have hcount : 2 * n = 2 * s.card := by
    calc
      2 * n = Finset.univ.card := by simp
      _ = ∑ c ∈ s, (Finset.univ.filter fun i => D.visit i = c).card :=
        Finset.card_eq_sum_card_image D.visit Finset.univ
      _ = ∑ _c ∈ s, 2 := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hfiber c hc
      _ = 2 * s.card := by simp [Nat.mul_comm]
  have hcard : s.card = n := by omega
  have hs : s = Finset.univ := s.eq_univ_of_card (by simpa using hcard)
  intro c
  have hc : c ∈ s := by rw [hs]; simp
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hc
  exact ⟨i, hi⟩

/-- The two visits at every crossing have opposite over/under data. -/
theorem over_partner_ne {D : OrientedGaussCode n} (i : Fin (2 * n)) :
    D.over (D.partner.val i) ≠ D.over i := by
  rw [D.over_partner]
  exact Bool.not_ne_self _

/-- The writhe is the sum of the signs of all crossings. -/
def writhe (D : OrientedGaussCode n) : ℤ :=
  ∑ c : Fin n, ((D.sign c : ℤˣ) : ℤ)

/-- Expand the writhe as the sum of the integer values of the crossing signs. -/
theorem writhe_def (D : OrientedGaussCode n) :
    D.writhe = ∑ c : Fin n, ((D.sign c : ℤˣ) : ℤ) := by simp [writhe]

/-- Reflecting a diagram reverses every crossing sign and leaves its traversal unchanged. -/
def mirror (D : OrientedGaussCode n) : OrientedGaussCode n where
  visit := D.visit
  over := D.over
  sign := fun c => -D.sign c
  partner := D.partner
  visit_eq_iff := D.visit_eq_iff
  over_partner := D.over_partner

/-- Mirroring preserves the sequence of crossing labels. -/
@[simp] theorem visit_mirror (D : OrientedGaussCode n) : D.mirror.visit = D.visit := by
  simp [mirror]

/-- Mirroring preserves the over/under data. -/
@[simp] theorem over_mirror (D : OrientedGaussCode n) : D.mirror.over = D.over := by
  simp [mirror]

/-- Mirroring negates every crossing sign. -/
@[simp] theorem sign_mirror (D : OrientedGaussCode n) (c : Fin n) :
    D.mirror.sign c = -D.sign c := by simp [mirror]

/-- Mirroring preserves the partner matching. -/
@[simp] theorem partner_mirror (D : OrientedGaussCode n) : D.mirror.partner = D.partner := by
  simp [mirror]

/-- Mirroring twice recovers the original Gauss code. -/
@[simp] theorem mirror_mirror (D : OrientedGaussCode n) : D.mirror.mirror = D := by
  apply ext
  · simp only [visit_mirror]
  · simp only [over_mirror]
  · funext c
    simp only [sign_mirror, neg_neg]

/-- Mirroring negates the writhe. -/
@[simp] theorem writhe_mirror (D : OrientedGaussCode n) : D.mirror.writhe = -D.writhe := by
  simp only [writhe_def, sign_mirror, Units.val_neg, Finset.sum_neg_distrib]

/-- Reverse the orientation while retaining the base point. The traversal order is reversed,
crossing signs and over/under statuses are preserved, and the partner matching is conjugated by
the reversal of the visit indices. -/
def reverse (D : OrientedGaussCode n) : OrientedGaussCode n where
  visit := D.visit ∘ Fin.rev
  over := D.over ∘ Fin.rev
  sign := D.sign
  partner := PerfectMatching.congr Fin.revPerm D.partner
  visit_eq_iff := by
    intro i j
    constructor
    · intro h
      rcases (D.visit_eq_iff (Fin.rev i) (Fin.rev j)).mp h with h | h
      · exact Or.inl (Fin.rev_injective h)
      · exact Or.inr (by simpa using congrArg Fin.rev h)
    · rintro (h | h)
      · apply (D.visit_eq_iff (Fin.rev i) (Fin.rev j)).mpr
        exact Or.inl (congrArg Fin.rev h)
      · apply (D.visit_eq_iff (Fin.rev i) (Fin.rev j)).mpr
        exact Or.inr (by simpa using congrArg Fin.rev h)
  over_partner := by
    intro i
    simp [Function.comp_def]

/-- Reversing orientation reads the crossing labels in reverse order. -/
@[simp] theorem visit_reverse (D : OrientedGaussCode n) (i : Fin (2 * n)) :
    D.reverse.visit i = D.visit (Fin.rev i) := by simp [reverse]

/-- Reversing orientation reads the over/under statuses in reverse order. -/
@[simp] theorem over_reverse (D : OrientedGaussCode n) (i : Fin (2 * n)) :
    D.reverse.over i = D.over (Fin.rev i) := by simp [reverse]

/-- Reversing orientation preserves every crossing sign. -/
@[simp] theorem sign_reverse (D : OrientedGaussCode n) : D.reverse.sign = D.sign := by
  simp [reverse]

/-- Reversing orientation conjugates the partner matching by reversal of the visit indices. -/
@[simp] theorem partner_reverse (D : OrientedGaussCode n) (i : Fin (2 * n)) :
    D.reverse.partner.val i = Fin.rev (D.partner.val (Fin.rev i)) := by
  simp [reverse]

/-- Reversing orientation twice recovers the original Gauss code. -/
@[simp] theorem reverse_reverse (D : OrientedGaussCode n) : D.reverse.reverse = D := by
  apply ext <;> funext i <;> simp

/-- Reversing orientation preserves the writhe. -/
@[simp] theorem writhe_reverse (D : OrientedGaussCode n) : D.reverse.writhe = D.writhe := by
  simp [writhe_def]

/-- Mirroring and reversing orientation commute. -/
theorem mirror_reverse (D : OrientedGaussCode n) : D.reverse.mirror = D.mirror.reverse := by
  apply ext <;> funext i <;> simp

/-- Two oriented Gauss codes represent the same unoriented code when they are equal or differ by
orientation reversal. -/
private def UnorientedRel (D E : OrientedGaussCode n) : Prop := D = E ∨ D = E.reverse

private theorem unorientedRel_refl (D : OrientedGaussCode n) : UnorientedRel D D := Or.inl rfl

private theorem unorientedRel_symm {D E : OrientedGaussCode n}
    (h : UnorientedRel D E) : UnorientedRel E D := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (by rw [h, reverse_reverse])

private theorem unorientedRel_trans {D E F : OrientedGaussCode n}
    (hDE : UnorientedRel D E) (hEF : UnorientedRel E F) : UnorientedRel D F := by
  rcases hDE with hDE | hDE
  · rcases hEF with hEF | hEF
    · exact Or.inl (hDE.trans hEF)
    · exact Or.inr (hDE.trans hEF)
  · rcases hEF with hEF | hEF
    · exact Or.inr (hDE.trans (congrArg reverse hEF))
    · exact Or.inl (hDE.trans (by rw [hEF, reverse_reverse]))

/-- The setoid of oriented Gauss codes modulo orientation reversal. -/
private def unorientedSetoid : Setoid (OrientedGaussCode n) where
  r := UnorientedRel
  iseqv := ⟨unorientedRel_refl, unorientedRel_symm, unorientedRel_trans⟩

end OrientedGaussCode

/-- A based Gauss code with its orientation forgotten. -/
def UnorientedGaussCode (n : ℕ) := Quotient (OrientedGaussCode.unorientedSetoid (n := n))

namespace OrientedGaussCode

/-- The quotient map forgetting the orientation of a based oriented Gauss code. -/
def forgetOrientation (D : OrientedGaussCode n) : UnorientedGaussCode n :=
  Quotient.mk (unorientedSetoid (n := n)) D

/-- Two oriented Gauss codes have the same unoriented class exactly when they agree up to
orientation reversal. -/
@[simp] theorem forgetOrientation_eq_iff {D E : OrientedGaussCode n} :
    D.forgetOrientation = E.forgetOrientation ↔ D = E ∨ D = E.reverse := by
  simp only [forgetOrientation, UnorientedGaussCode]
  rw [Quotient.eq_iff_equiv]
  rfl

/-- Reversing orientation does not change the unoriented Gauss code. -/
@[simp] theorem forgetOrientation_reverse (D : OrientedGaussCode n) :
    D.reverse.forgetOrientation = D.forgetOrientation := by
  apply forgetOrientation_eq_iff.2
  exact Or.inr rfl

/-- Relabel crossings by `e`. The visit sequence is composed with `e`, while the partner pairing
and over/under data are unchanged; signs are transported along `e.symm`. -/
def relabel (D : OrientedGaussCode n) (e : Fin n ≃ Fin n) : OrientedGaussCode n where
  visit := e ∘ D.visit
  over := D.over
  sign := D.sign ∘ e.symm
  partner := D.partner
  visit_eq_iff := by
    intro i j
    simpa [Function.comp_def] using D.visit_eq_iff i j
  over_partner := D.over_partner

/-- Relabelling composes the visit labels with the given equivalence. -/
@[simp] theorem visit_relabel (D : OrientedGaussCode n) (e : Fin n ≃ Fin n)
    (i : Fin (2 * n)) : (D.relabel e).visit i = e (D.visit i) := by
  simp [relabel]

/-- Relabelling preserves the over/under data. -/
@[simp] theorem over_relabel (D : OrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).over = D.over := by simp [relabel]

/-- Relabelling transports signs along the inverse equivalence. -/
@[simp] theorem sign_relabel (D : OrientedGaussCode n) (e : Fin n ≃ Fin n) (c : Fin n) :
    (D.relabel e).sign c = D.sign (e.symm c) := by simp [relabel]

/-- Relabelling preserves the partner matching. -/
@[simp] theorem partner_relabel (D : OrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).partner = D.partner := by simp [relabel]

/-- Relabelling preserves the writhe. -/
@[simp] theorem writhe_relabel (D : OrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).writhe = D.writhe := by
  rw [writhe_def, writhe_def]
  simpa only [sign_relabel] using
    e.symm.sum_comp (fun c : Fin n => ((D.sign c : ℤˣ) : ℤ))

/-- Successive relabellings compose. -/
theorem relabel_relabel (D : OrientedGaussCode n) (e f : Fin n ≃ Fin n) :
    (D.relabel e).relabel f = D.relabel (e.trans f) := by
  apply ext <;> funext i <;> simp

/-- Mirroring commutes with relabelling crossings. -/
theorem mirror_relabel (D : OrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).mirror = D.mirror.relabel e := by
  apply ext <;> funext i <;> simp

/-- Reversing orientation commutes with relabelling crossings. -/
theorem reverse_relabel (D : OrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).reverse = D.reverse.relabel e := by
  apply ext <;> funext i <;> simp

/-- Relabelling by the identity equivalence has no effect. -/
@[simp] theorem relabel_refl (D : OrientedGaussCode n) :
    D.relabel (Equiv.refl (Fin n)) = D := by
  apply ext <;> funext i <;> simp

/-- The crossing-free based oriented Gauss code, representing the unknot diagram. -/
def empty : OrientedGaussCode 0 where
  visit := Fin.elim0
  over := Fin.elim0
  sign := Fin.elim0
  partner := PerfectMatching.mk (Equiv.refl (Fin 0)) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  visit_eq_iff := fun i => Fin.elim0 i
  over_partner := fun i => Fin.elim0 i

/-- Every crossing-free based oriented Gauss code is the canonical empty code. -/
theorem eq_empty (D : OrientedGaussCode 0) : D = empty := by
  apply ext <;> funext i <;> exact Fin.elim0 i

/-- The one-crossing positive kink. This is the smallest nontrivial Gauss code. -/
def positiveKink : OrientedGaussCode 1 where
  visit := fun _ => 0
  over := fun i => if i = 0 then true else false
  sign := fun _ => 1
  partner := PerfectMatching.mk (Equiv.swap 0 1) (by
    intro i
    fin_cases i <;> simp) (by
    intro i
    fin_cases i <;> simp)
  visit_eq_iff := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  over_partner := by
    intro i
    fin_cases i <;> simp

/-- Both visits of the positive kink carry its unique crossing label. -/
@[simp] theorem visit_positiveKink (i : Fin 2) :
    positiveKink.visit i = 0 := by simp [positiveKink]

/-- The first visit of the positive kink is over and the second is under. -/
@[simp] theorem over_positiveKink (i : Fin 2) :
    positiveKink.over i = decide (i = 0) := by
  simp [positiveKink]

/-- The unique crossing of the positive kink has positive sign. -/
@[simp] theorem sign_positiveKink (c : Fin 1) :
    positiveKink.sign c = 1 := by simp [positiveKink]

/-- The positive kink pairs its two visits by swapping them. -/
@[simp] theorem partner_positiveKink :
    positiveKink.partner.val = Equiv.swap 0 1 := by simp [positiveKink]

/-- The positive kink has writhe one. -/
@[simp] theorem writhe_positiveKink :
    writhe positiveKink = 1 := by
  simp [writhe_def]

/-- The empty Gauss code has writhe zero. -/
@[simp] theorem writhe_empty :
    writhe (empty : OrientedGaussCode 0) = 0 := by
  simp [writhe_def]

end OrientedGaussCode

end TauCeti
