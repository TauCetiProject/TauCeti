/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.PerfectMatching
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
operations needed by those developments: relabelling crossings, mirroring, the writhe, and the
crossing-free witness.

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

/-- The inverse permutation of the partner matching is the partner matching itself. -/
@[simp]
theorem partner_symm (D : OrientedGaussCode n) : D.partner.val.symm = D.partner.val := by
  apply Equiv.ext
  intro i
  apply D.partner.val.injective
  simp

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
@[simp] theorem mirror_visit (D : OrientedGaussCode n) : D.mirror.visit = D.visit := by
  simp [mirror]

/-- Mirroring preserves the over/under data. -/
@[simp] theorem mirror_over (D : OrientedGaussCode n) : D.mirror.over = D.over := by
  simp [mirror]

/-- Mirroring negates every crossing sign. -/
@[simp] theorem mirror_sign (D : OrientedGaussCode n) (c : Fin n) :
    D.mirror.sign c = -D.sign c := by simp [mirror]

/-- Mirroring preserves the partner matching. -/
@[simp] theorem mirror_partner (D : OrientedGaussCode n) : D.mirror.partner = D.partner := by
  simp [mirror]

/-- Mirroring twice recovers the original Gauss code. -/
@[simp] theorem mirror_mirror (D : OrientedGaussCode n) : D.mirror.mirror = D := by
  apply ext
  · simp only [mirror_visit]
  · simp only [mirror_over]
  · funext c
    simp only [mirror_sign, neg_neg]

/-- Mirroring negates the writhe. -/
@[simp] theorem writhe_mirror (D : OrientedGaussCode n) : D.mirror.writhe = -D.writhe := by
  simp only [writhe_def, mirror_sign, Units.val_neg, Finset.sum_neg_distrib]

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
@[simp] theorem relabel_visit (D : OrientedGaussCode n) (e : Fin n ≃ Fin n)
    (i : Fin (2 * n)) : (D.relabel e).visit i = e (D.visit i) := by
  simp [relabel]

/-- Relabelling preserves the over/under data. -/
@[simp] theorem relabel_over (D : OrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).over = D.over := by simp [relabel]

/-- Relabelling transports signs along the inverse equivalence. -/
@[simp] theorem relabel_sign (D : OrientedGaussCode n) (e : Fin n ≃ Fin n) (c : Fin n) :
    (D.relabel e).sign c = D.sign (e.symm c) := by simp [relabel]

/-- Relabelling preserves the partner matching. -/
@[simp] theorem relabel_partner (D : OrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).partner = D.partner := by simp [relabel]

/-- Relabelling preserves the writhe. -/
@[simp] theorem writhe_relabel (D : OrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).writhe = D.writhe := by
  rw [writhe_def, writhe_def]
  simpa only [relabel_sign] using
    e.symm.sum_comp (fun c : Fin n => ((D.sign c : ℤˣ) : ℤ))

/-- Successive relabellings compose. -/
theorem relabel_relabel (D : OrientedGaussCode n) (e f : Fin n ≃ Fin n) :
    (D.relabel e).relabel f = D.relabel (e.trans f) := by
  apply ext <;> funext i <;> simp

/-- Mirroring commutes with relabelling crossings. -/
theorem mirror_relabel (D : OrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).mirror = D.mirror.relabel e := by
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
def oneCrossingPositive : OrientedGaussCode 1 where
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
@[simp] theorem oneCrossingPositive_visit (i : Fin 2) :
    oneCrossingPositive.visit i = 0 := by simp [oneCrossingPositive]

/-- The first visit of the positive kink is over and the second is under. -/
@[simp] theorem oneCrossingPositive_over (i : Fin 2) :
    oneCrossingPositive.over i = decide (i = 0) := by
  simp [oneCrossingPositive]

/-- The unique crossing of the positive kink has positive sign. -/
@[simp] theorem oneCrossingPositive_sign (c : Fin 1) :
    oneCrossingPositive.sign c = 1 := by simp [oneCrossingPositive]

/-- The positive kink pairs its two visits by swapping them. -/
@[simp] theorem oneCrossingPositive_partner :
    oneCrossingPositive.partner.val = Equiv.swap 0 1 := by simp [oneCrossingPositive]

/-- The positive kink has writhe one. -/
@[simp] theorem writhe_oneCrossingPositive :
    writhe oneCrossingPositive = 1 := by
  simp [writhe_def]

/-- The empty Gauss code has writhe zero. -/
@[simp] theorem writhe_empty :
    writhe (empty : OrientedGaussCode 0) = 0 := by
  simp [writhe_def]

end OrientedGaussCode

end TauCeti
