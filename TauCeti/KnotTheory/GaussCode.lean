/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.PerfectMatching
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import TauCeti.GroupTheory.Perm.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
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
the writhe, and the crossing-free witness. `FramedBasedOrientedGaussCode` adds the integer framing
coefficient relative to the Seifert framing, while `BasedUnorientedGaussCode` quotients by
orientation reversal; their projections respectively forget framing and orientation.

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
structure BasedOrientedGaussCode (n : ℕ) where
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
structure FramedBasedOrientedGaussCode (n : ℕ) where
  /-- Forget the framing coefficient, retaining the based oriented Gauss code. -/
  forgetFraming : BasedOrientedGaussCode n
  /-- The framing coefficient relative to the Seifert framing. -/
  framing : ℤ

namespace BasedOrientedGaussCode

variable {n : ℕ}

attribute [simp] BasedOrientedGaussCode.visit_eq_iff BasedOrientedGaussCode.over_partner

/-- Two Gauss codes are equal when their visit labels, over/under data, and signs agree.
The partner matching is forced by the visit labels. -/
@[ext]
theorem ext {D E : BasedOrientedGaussCode n}
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
theorem visit_partner (D : BasedOrientedGaussCode n) (i : Fin (2 * n)) :
    D.visit (D.partner.val i) = D.visit i := by
  exact (D.visit_eq_iff i (D.partner.val i)).mpr (Or.inr rfl) |>.symm

/-- Every crossing label occurs in the traversal. -/
theorem visit_surjective (D : BasedOrientedGaussCode n) : Function.Surjective D.visit := by
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
theorem over_partner_ne {D : BasedOrientedGaussCode n} (i : Fin (2 * n)) :
    D.over (D.partner.val i) ≠ D.over i := by
  rw [D.over_partner]
  exact Bool.not_ne_self _

/-- Whether a visit is the later of the two visits to its crossing. -/
def isSecondVisit (D : BasedOrientedGaussCode n) (v : Fin (2 * n)) : Bool :=
  decide (D.partner.val v < v)

/-- Exactly one of the two visits to a crossing is the later one. -/
@[simp] theorem isSecondVisit_partner (D : BasedOrientedGaussCode n) (v : Fin (2 * n)) :
    D.isSecondVisit (D.partner.val v) = !D.isSecondVisit v := by
  have hne : D.partner.val v ≠ v := D.partner.apply_ne v
  simp only [isSecondVisit, PerfectMatching.apply_apply]
  rcases lt_or_gt_of_ne hne with h | h
  · simp [h, asymm h]
  · simp [h, asymm h]

/-- A visit is determined by its crossing together with whether it is the later of the two
visits to that crossing. -/
theorem visit_isSecondVisit_injective (D : BasedOrientedGaussCode n) :
    Function.Injective fun v : Fin (2 * n) => (D.visit v, D.isSecondVisit v) := by
  intro v w h
  simp only [Prod.mk.injEq] at h
  rcases (D.visit_eq_iff v w).mp h.1 with rfl | rfl
  · rfl
  · rw [isSecondVisit_partner] at h
    exact absurd h.2.symm (Bool.not_ne_self _)

/-- The visits of the traversal, indexed by the crossing visited together with whether the visit
is the later of the two to that crossing. -/
noncomputable def visitEquiv (D : BasedOrientedGaussCode n) : Fin (2 * n) ≃ Fin n × Bool :=
  Equiv.ofBijective (fun v => (D.visit v, D.isSecondVisit v))
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨D.visit_isSecondVisit_injective, by
        simp [Fintype.card_prod, Nat.mul_comm]⟩)

/-- The index of a visit is its crossing together with its position in the pair. -/
@[simp] theorem visitEquiv_apply (D : BasedOrientedGaussCode n) (v : Fin (2 * n)) :
    D.visitEquiv v = (D.visit v, D.isSecondVisit v) := by
  simp [visitEquiv]

/-- The visit to crossing `i` that is the first (`second = false`) or the second
(`second = true`) of the two along the traversal. -/
noncomputable def visitAt (D : BasedOrientedGaussCode n) (i : Fin n)
    (second : Bool) : Fin (2 * n) :=
  D.visitEquiv.symm (i, second)

/-- The visit at a crossing and index is a visit to that crossing with that index. -/
theorem visitEquiv_visitAt (D : BasedOrientedGaussCode n) (i : Fin n) (s : Bool) :
    D.visitEquiv (D.visitAt i s) = (i, s) :=
  D.visitEquiv.apply_symm_apply (i, s)

/-- The visit selected at a crossing is a visit to that crossing. -/
@[simp] theorem visit_visitAt (D : BasedOrientedGaussCode n) (i : Fin n) (s : Bool) :
    D.visit (D.visitAt i s) = i := by
  have h := D.visitEquiv_visitAt i s
  rw [visitEquiv_apply] at h
  exact congrArg Prod.fst h

/-- The visit selected at a crossing has the requested position in the pair. -/
@[simp] theorem isSecondVisit_visitAt (D : BasedOrientedGaussCode n) (i : Fin n) (s : Bool) :
    D.isSecondVisit (D.visitAt i s) = s := by
  have h := D.visitEquiv_visitAt i s
  rw [visitEquiv_apply] at h
  exact congrArg Prod.snd h

/-- Selecting the visit at a visit's own crossing and position recovers it. -/
@[simp] theorem visitAt_visit (D : BasedOrientedGaussCode n) (v : Fin (2 * n)) :
    D.visitAt (D.visit v) (D.isSecondVisit v) = v := by
  have h := D.visitEquiv.symm_apply_apply v
  rwa [visitEquiv_apply] at h

/-- The two visits to a crossing are partners in the matching. -/
theorem partner_visitAt (D : BasedOrientedGaussCode n) (i : Fin n) (s : Bool) :
    D.partner.val (D.visitAt i s) = D.visitAt i (!s) := by
  have h := D.visitAt_visit (D.partner.val (D.visitAt i s))
  rw [visit_partner, visit_visitAt, isSecondVisit_partner, isSecondVisit_visitAt] at h
  exact h.symm

/-- The two visits to a crossing carry opposite over/under data. -/
theorem over_visitAt_not (D : BasedOrientedGaussCode n) (i : Fin n) (s : Bool) :
    D.over (D.visitAt i (!s)) = !D.over (D.visitAt i s) := by
  rw [← partner_visitAt, over_partner]

/-- The writhe is the sum of the signs of all crossings. -/
def writhe (D : BasedOrientedGaussCode n) : ℤ :=
  ∑ c : Fin n, ((D.sign c : ℤˣ) : ℤ)

/-- Expand the writhe as the sum of the integer values of the crossing signs. -/
theorem writhe_def (D : BasedOrientedGaussCode n) :
    D.writhe = ∑ c : Fin n, ((D.sign c : ℤˣ) : ℤ) := by simp [writhe]

/-- Reflecting a diagram reverses every crossing sign and leaves its traversal unchanged. -/
def mirror (D : BasedOrientedGaussCode n) : BasedOrientedGaussCode n where
  visit := D.visit
  over := D.over
  sign := fun c => -D.sign c
  partner := D.partner
  visit_eq_iff := D.visit_eq_iff
  over_partner := D.over_partner

/-- Mirroring preserves the sequence of crossing labels. -/
@[simp] theorem visit_mirror (D : BasedOrientedGaussCode n) : D.mirror.visit = D.visit := by
  simp [mirror]

/-- Mirroring preserves the over/under data. -/
@[simp] theorem over_mirror (D : BasedOrientedGaussCode n) : D.mirror.over = D.over := by
  simp [mirror]

/-- Mirroring negates every crossing sign. -/
@[simp] theorem sign_mirror (D : BasedOrientedGaussCode n) (c : Fin n) :
    D.mirror.sign c = -D.sign c := by simp [mirror]

/-- Mirroring preserves the partner matching. -/
@[simp] theorem partner_mirror (D : BasedOrientedGaussCode n) : D.mirror.partner = D.partner := by
  simp [mirror]

/-- Mirroring twice recovers the original Gauss code. -/
@[simp] theorem mirror_mirror (D : BasedOrientedGaussCode n) : D.mirror.mirror = D := by
  apply ext
  · simp only [visit_mirror]
  · simp only [over_mirror]
  · funext c
    simp only [sign_mirror, neg_neg]

/-- Mirroring negates the writhe. -/
@[simp] theorem writhe_mirror (D : BasedOrientedGaussCode n) : D.mirror.writhe = -D.writhe := by
  simp only [writhe_def, sign_mirror, Units.val_neg, Finset.sum_neg_distrib]

/-- Reverse the orientation while retaining the base point. The traversal order is reversed,
crossing signs and over/under statuses are preserved, and the partner matching is conjugated by
the reversal of the visit indices. -/
def reverse (D : BasedOrientedGaussCode n) : BasedOrientedGaussCode n where
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
@[simp] theorem visit_reverse (D : BasedOrientedGaussCode n) (i : Fin (2 * n)) :
    D.reverse.visit i = D.visit (Fin.rev i) := by simp [reverse]

/-- Reversing orientation reads the over/under statuses in reverse order. -/
@[simp] theorem over_reverse (D : BasedOrientedGaussCode n) (i : Fin (2 * n)) :
    D.reverse.over i = D.over (Fin.rev i) := by simp [reverse]

/-- Reversing orientation preserves every crossing sign. -/
@[simp] theorem sign_reverse (D : BasedOrientedGaussCode n) : D.reverse.sign = D.sign := by
  simp [reverse]

/-- Reversing orientation conjugates the partner matching by reversal of the visit indices. -/
@[simp] theorem partner_reverse (D : BasedOrientedGaussCode n) (i : Fin (2 * n)) :
    D.reverse.partner.val i = Fin.rev (D.partner.val (Fin.rev i)) := by
  simp [reverse]

/-- Reversing orientation twice recovers the original Gauss code. -/
@[simp] theorem reverse_reverse (D : BasedOrientedGaussCode n) : D.reverse.reverse = D := by
  apply ext <;> funext i <;> simp

/-- Reversing orientation preserves the writhe. -/
@[simp] theorem writhe_reverse (D : BasedOrientedGaussCode n) : D.reverse.writhe = D.writhe := by
  simp [writhe_def]

/-- Mirroring and reversing orientation commute. -/
@[simp] theorem mirror_reverse (D : BasedOrientedGaussCode n) :
    D.reverse.mirror = D.mirror.reverse := by
  apply ext <;> funext i <;> simp

/-- The setoid of oriented Gauss codes modulo orientation reversal. -/
private def unorientedSetoid : Setoid (BasedOrientedGaussCode n) :=
  Equiv.Perm.SameCycle.setoid (Function.Involutive.toPerm reverse reverse_reverse)

private theorem unorientedSetoid_apply (D E : BasedOrientedGaussCode n) :
    unorientedSetoid D E ↔ D = E ∨ D = E.reverse :=
  TauCeti.sameCycle_toPerm_iff reverse reverse_reverse D E

end BasedOrientedGaussCode

/-- A based Gauss code with its orientation forgotten. -/
def BasedUnorientedGaussCode (n : ℕ) :=
  Quotient (BasedOrientedGaussCode.unorientedSetoid (n := n))

namespace BasedOrientedGaussCode

/-- The quotient map forgetting the orientation of a based oriented Gauss code. -/
def forgetOrientation (D : BasedOrientedGaussCode n) : BasedUnorientedGaussCode n :=
  Quotient.mk'' D

/-- Two oriented Gauss codes have the same unoriented class exactly when they agree up to
orientation reversal. -/
@[simp] theorem forgetOrientation_eq_iff {D E : BasedOrientedGaussCode n} :
    D.forgetOrientation = E.forgetOrientation ↔ D = E ∨ D = E.reverse := by
  simp only [forgetOrientation, BasedUnorientedGaussCode]
  rw [Quotient.eq_iff_equiv]
  exact unorientedSetoid_apply D E

/-- Reversing orientation does not change the unoriented Gauss code. -/
@[simp] theorem forgetOrientation_reverse (D : BasedOrientedGaussCode n) :
    D.reverse.forgetOrientation = D.forgetOrientation := by
  apply forgetOrientation_eq_iff.2
  exact Or.inr rfl

/-- Relabel crossings by `e`. The visit sequence is composed with `e`, while the partner pairing
and over/under data are unchanged; signs are transported along `e.symm`. -/
def relabel (D : BasedOrientedGaussCode n) (e : Fin n ≃ Fin n) : BasedOrientedGaussCode n where
  visit := e ∘ D.visit
  over := D.over
  sign := D.sign ∘ e.symm
  partner := D.partner
  visit_eq_iff := by
    intro i j
    simp
  over_partner := D.over_partner

/-- Relabelling composes the visit labels with the given equivalence. -/
@[simp] theorem visit_relabel (D : BasedOrientedGaussCode n) (e : Fin n ≃ Fin n)
    (i : Fin (2 * n)) : (D.relabel e).visit i = e (D.visit i) := by
  simp [relabel]

/-- Relabelling preserves the over/under data. -/
@[simp] theorem over_relabel (D : BasedOrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).over = D.over := by simp [relabel]

/-- Relabelling transports signs along the inverse equivalence. -/
@[simp] theorem sign_relabel (D : BasedOrientedGaussCode n) (e : Fin n ≃ Fin n) (c : Fin n) :
    (D.relabel e).sign c = D.sign (e.symm c) := by simp [relabel]

/-- Relabelling preserves the partner matching. -/
@[simp] theorem partner_relabel (D : BasedOrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).partner = D.partner := by simp [relabel]

/-- Relabelling preserves the writhe. -/
@[simp] theorem writhe_relabel (D : BasedOrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).writhe = D.writhe := by
  rw [writhe_def, writhe_def]
  simpa only [sign_relabel] using
    e.symm.sum_comp (fun c : Fin n => ((D.sign c : ℤˣ) : ℤ))

/-- Successive relabellings compose. -/
@[simp] theorem relabel_relabel (D : BasedOrientedGaussCode n) (e f : Fin n ≃ Fin n) :
    (D.relabel e).relabel f = D.relabel (e.trans f) := by
  apply ext <;> funext i <;> simp

/-- Mirroring commutes with relabelling crossings. -/
@[simp] theorem mirror_relabel (D : BasedOrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).mirror = D.mirror.relabel e := by
  apply ext <;> funext i <;> simp

/-- Reversing orientation commutes with relabelling crossings. -/
@[simp] theorem reverse_relabel (D : BasedOrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).reverse = D.reverse.relabel e := by
  apply ext <;> funext i <;> simp

/-- Relabelling by the identity equivalence has no effect. -/
@[simp] theorem relabel_refl (D : BasedOrientedGaussCode n) :
    D.relabel (Equiv.refl (Fin n)) = D := by
  apply ext <;> funext i <;> simp

/-- The crossing-free based oriented Gauss code, representing the unknot diagram. -/
def empty : BasedOrientedGaussCode 0 where
  visit := Fin.elim0
  over := Fin.elim0
  sign := Fin.elim0
  partner := PerfectMatching.mk (Equiv.refl (Fin 0)) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  visit_eq_iff := fun i => Fin.elim0 i
  over_partner := fun i => Fin.elim0 i

/-- Every crossing-free based oriented Gauss code is the canonical empty code. -/
theorem eq_empty (D : BasedOrientedGaussCode 0) : D = empty := by
  apply ext <;> funext i <;> exact Fin.elim0 i

/-- The one-crossing positive kink. This is the smallest nontrivial Gauss code. -/
def positiveKink : BasedOrientedGaussCode 1 where
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
    writhe (empty : BasedOrientedGaussCode 0) = 0 := by
  simp [writhe_def]

end BasedOrientedGaussCode

namespace BasedUnorientedGaussCode

variable {n : ℕ}

/-- A function on based oriented Gauss codes that is invariant under orientation reversal descends
to based unoriented Gauss codes. -/
protected def lift {α : Sort*} (f : BasedOrientedGaussCode n → α)
    (h : ∀ D, f D.reverse = f D) : BasedUnorientedGaussCode n → α :=
  Quotient.lift f fun D E hDE => by
    rcases (BasedOrientedGaussCode.unorientedSetoid_apply D E).mp hDE with rfl | hrev
    · rfl
    · rw [hrev]
      exact h E

/-- Lifting an orientation-invariant function and applying it to an oriented representative
recovers the original value. -/
@[simp]
protected theorem lift_forgetOrientation {α : Sort*} (f : BasedOrientedGaussCode n → α)
    (h : ∀ D, f D.reverse = f D) (D : BasedOrientedGaussCode n) :
    BasedUnorientedGaussCode.lift f h D.forgetOrientation = f D :=
  by simp [BasedUnorientedGaussCode.lift, BasedOrientedGaussCode.forgetOrientation]

/-- To prove a property of a based unoriented Gauss code, it suffices to prove it for every based
oriented representative. -/
@[elab_as_elim]
protected theorem inductionOn {motive : BasedUnorientedGaussCode n → Prop}
    (D : BasedUnorientedGaussCode n)
    (h : ∀ E : BasedOrientedGaussCode n, motive E.forgetOrientation) : motive D :=
  Quotient.inductionOn D h

/-- The writhe of a based unoriented Gauss code. -/
def writhe (D : BasedUnorientedGaussCode n) : ℤ :=
  BasedUnorientedGaussCode.lift BasedOrientedGaussCode.writhe
    BasedOrientedGaussCode.writhe_reverse D

/-- The writhe of an unoriented class is the writhe of any oriented representative. -/
@[simp] theorem writhe_forgetOrientation (D : BasedOrientedGaussCode n) :
    writhe D.forgetOrientation = D.writhe := by
  exact BasedUnorientedGaussCode.lift_forgetOrientation BasedOrientedGaussCode.writhe
    BasedOrientedGaussCode.writhe_reverse D

/-- Mirror a based unoriented Gauss code. -/
def mirror (D : BasedUnorientedGaussCode n) : BasedUnorientedGaussCode n :=
  Quotient.map' BasedOrientedGaussCode.mirror (by
    intro E F h
    apply (BasedOrientedGaussCode.unorientedSetoid_apply _ _).mpr
    rcases (BasedOrientedGaussCode.unorientedSetoid_apply E F).mp h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (h ▸ BasedOrientedGaussCode.mirror_reverse F)) D

/-- Mirroring an unoriented class is represented by mirroring any oriented representative. -/
@[simp] theorem mirror_forgetOrientation (D : BasedOrientedGaussCode n) :
    mirror D.forgetOrientation = D.mirror.forgetOrientation := by
  simp only [mirror, BasedOrientedGaussCode.forgetOrientation, Quotient.map'_mk'']
  apply Quotient.sound
  exact (BasedOrientedGaussCode.unorientedSetoid_apply _ _).mpr (Or.inl rfl)

/-- Relabel the crossings of a based unoriented Gauss code. -/
def relabel (D : BasedUnorientedGaussCode n) (e : Fin n ≃ Fin n) :
    BasedUnorientedGaussCode n :=
  Quotient.map' (fun E : BasedOrientedGaussCode n => E.relabel e) (by
    intro E F h
    apply (BasedOrientedGaussCode.unorientedSetoid_apply _ _).mpr
    rcases (BasedOrientedGaussCode.unorientedSetoid_apply E F).mp h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (h ▸ (BasedOrientedGaussCode.reverse_relabel F e).symm)) D

/-- Relabelling an unoriented class is represented by relabelling any oriented representative. -/
@[simp] theorem relabel_forgetOrientation (D : BasedOrientedGaussCode n) (e : Fin n ≃ Fin n) :
    relabel D.forgetOrientation e = (D.relabel e).forgetOrientation := by
  simp only [relabel, BasedOrientedGaussCode.forgetOrientation, Quotient.map'_mk'']
  apply Quotient.sound
  exact (BasedOrientedGaussCode.unorientedSetoid_apply _ _).mpr (Or.inl rfl)

/-- Mirroring twice recovers the original based unoriented Gauss code. -/
@[simp] theorem mirror_mirror (D : BasedUnorientedGaussCode n) : D.mirror.mirror = D := by
  refine D.inductionOn ?_
  simp

/-- Mirroring negates the writhe of a based unoriented Gauss code. -/
@[simp] theorem writhe_mirror (D : BasedUnorientedGaussCode n) : D.mirror.writhe = -D.writhe := by
  refine D.inductionOn ?_
  simp

/-- Relabelling by the identity equivalence has no effect. -/
@[simp] theorem relabel_refl (D : BasedUnorientedGaussCode n) :
    D.relabel (Equiv.refl (Fin n)) = D := by
  refine D.inductionOn ?_
  simp

/-- Successive relabellings of a based unoriented Gauss code compose. -/
@[simp] theorem relabel_relabel (D : BasedUnorientedGaussCode n) (e f : Fin n ≃ Fin n) :
    (D.relabel e).relabel f = D.relabel (e.trans f) := by
  refine D.inductionOn ?_
  simp

/-- Relabelling preserves the writhe of a based unoriented Gauss code. -/
@[simp] theorem writhe_relabel (D : BasedUnorientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).writhe = D.writhe := by
  refine D.inductionOn ?_
  simp

/-- Mirroring and relabelling commute on based unoriented Gauss codes. -/
@[simp] theorem mirror_relabel (D : BasedUnorientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).mirror = D.mirror.relabel e := by
  refine D.inductionOn ?_
  simp

end BasedUnorientedGaussCode

end TauCeti
