/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.PerfectMatching
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Sort
import TauCeti.GroupTheory.Perm.Basic
import Mathlib.Data.Fin.Rev
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

A traversal whose visits are the elements of a finite linearly ordered set, paired by a perfect
matching and decorated with over/under data and signs, determines a based code,
`BasedOrientedGaussCode.ofPerfectMatching`, with crossings numbered in the order of their first
visits. This is how the code of a concrete diagram, such as a projected polygonal knot, is built.

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

/-- A Gauss code is determined by the relative order of the crossing labels of its visits, its
over/under data, and the signs of the crossings met at each visit: two codes whose labels compare
in the same way at every pair of visits have the same labels. -/
theorem ext_of_visit_lt_visit_iff {D E : BasedOrientedGaussCode n}
    (hvisit : ∀ i j, D.visit i < D.visit j ↔ E.visit i < E.visit j) (hover : D.over = E.over)
    (hsign : ∀ i, D.sign (D.visit i) = E.sign (E.visit i)) : D = E := by
  have heq (i j : Fin (2 * n)) : D.visit i = D.visit j ↔ E.visit i = E.visit j := by
    simp only [le_antisymm_iff, ← not_lt, hvisit]
  -- Reading the labels of `D` through those of `E` gives a strictly monotone permutation.
  let e : Fin n → Fin n := fun c ↦ E.visit (Function.surjInv D.visit_surjective c)
  have he (i : Fin (2 * n)) : e (D.visit i) = E.visit i :=
    (heq _ _).1 (Function.surjInv_eq D.visit_surjective _)
  have hmono : StrictMono e := fun c c' h ↦ (hvisit _ _).1 <| by
    rwa [Function.surjInv_eq D.visit_surjective, Function.surjInv_eq D.visit_surjective]
  have hrange : Set.range e = Set.range id := by
    rw [Set.range_id, Set.eq_univ_iff_forall]
    intro c
    obtain ⟨i, rfl⟩ := E.visit_surjective c
    exact ⟨_, he i⟩
  have hid : e = id := hmono.range_inj_of_wellFoundedLT strictMono_id |>.1 hrange
  have hv : D.visit = E.visit := funext fun i ↦ by rw [← he, hid, id]
  refine ext hv hover (funext fun c ↦ ?_)
  obtain ⟨i, rfl⟩ := D.visit_surjective c
  rw [hsign, hv]

/-- The form of `TauCeti.BasedOrientedGaussCode.ext_of_visit_lt_visit_iff` for codes whose
numbers of crossings are equal but not definitionally so, such as codes read off from two
presentations of one diagram: the codes, paired with their numbers of crossings, are equal when
they satisfy its hypotheses after identifying their visits by `Fin.cast`. -/
theorem sigma_mk_eq_of_visit_lt_visit_iff {m : ℕ} (h : n = m) {D : BasedOrientedGaussCode n}
    {E : BasedOrientedGaussCode m}
    (hvisit : ∀ i j, D.visit i < D.visit j ↔
      E.visit (Fin.cast (congrArg (2 * ·) h) i) < E.visit (Fin.cast (congrArg (2 * ·) h) j))
    (hover : ∀ i, D.over i = E.over (Fin.cast (congrArg (2 * ·) h) i))
    (hsign : ∀ i, D.sign (D.visit i) = E.sign (E.visit (Fin.cast (congrArg (2 * ·) h) i))) :
    (⟨n, D⟩ : Σ n, BasedOrientedGaussCode n) = ⟨m, E⟩ := by
  subst h
  simp only [Fin.cast_eq_self] at hvisit hover hsign
  rw [ext_of_visit_lt_visit_iff hvisit (funext hover) hsign]

/-!
### Visits and crossing data
-/

/-- A visit, read as its crossing label together with whether it is the over visit. -/
def visitData (D : BasedOrientedGaussCode n) (i : Fin (2 * n)) : Fin n × Bool :=
  (D.visit i, D.over i)

/-- The two components of the data attached to a visit are its crossing label and over/under
status. -/
@[simp]
theorem visitData_apply (D : BasedOrientedGaussCode n) (i : Fin (2 * n)) :
    D.visitData i = (D.visit i, D.over i) := (rfl)

/-- The crossing label and over/under status determine a unique visit. -/
theorem visitData_bijective (D : BasedOrientedGaussCode n) : Function.Bijective D.visitData := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro i j hij
    have hvis : D.visit i = D.visit j := congrArg Prod.fst hij
    have hover : D.over i = D.over j := congrArg Prod.snd hij
    rcases (D.visit_eq_iff i j).mp hvis with rfl | hj
    · rfl
    · subst j
      exact (D.over_partner_ne i hover.symm).elim
  · simp [Nat.mul_comm]

/-- Visits are equivalent to pairs consisting of a crossing and an over/under choice. -/
noncomputable def visitDataEquiv (D : BasedOrientedGaussCode n) : Fin (2 * n) ≃ Fin n × Bool :=
  Equiv.ofBijective D.visitData D.visitData_bijective

/-- The visit equivalence sends a visit to its crossing label and over/under status. -/
@[simp]
theorem visitDataEquiv_apply (D : BasedOrientedGaussCode n) (i : Fin (2 * n)) :
    D.visitDataEquiv i = (D.visit i, D.over i) := by
  rw [visitDataEquiv, Equiv.ofBijective_apply, D.visitData_apply]

/-!
### Gauss codes of ordered traversals
-/

section OfPerfectMatching

variable {α : Type*} [LinearOrder α] [Fintype α] {m : ℕ}

/-- The visits of a matched finite linear order that come before their partner. -/
private def leadingVisits (p : PerfectMatching α) : Finset α :=
  {a | a < p.val a}

private theorem mem_leadingVisits {p : PerfectMatching α} {a : α} :
    a ∈ leadingVisits p ↔ a < p.val a := by
  simp [leadingVisits]

private theorem min_mem_leadingVisits (p : PerfectMatching α) (a : α) :
    min a (p.val a) ∈ leadingVisits p := by
  rw [mem_leadingVisits]
  rcases lt_or_gt_of_ne (p.apply_ne a).symm with h | h
  · rwa [min_eq_left h.le]
  · rwa [min_eq_right h.le, p.apply_apply]

private theorem card_leadingVisits (p : PerfectMatching α) (hα : Fintype.card α = 2 * m) :
    (leadingVisits p).card = m := by
  have hcompl : (leadingVisits p)ᶜ = (leadingVisits p).map p.val.toEmbedding := by
    ext a
    have hsymm : p.val.symm a = p.val a := (Equiv.symm_apply_eq _).2 (p.apply_apply a).symm
    simp only [Finset.mem_compl, mem_leadingVisits, not_lt, Finset.mem_map_equiv, hsymm,
      p.apply_apply]
    exact le_iff_lt_or_eq.trans (or_iff_left (p.apply_ne a))
  have h := Finset.card_add_card_compl (leadingVisits p)
  rw [hcompl, Finset.card_map] at h
  omega

/-- The leading visits, enumerated in increasing order. -/
private def leadingVisitsOrderIso (p : PerfectMatching α) (hα : Fintype.card α = 2 * m) :
    Fin m ≃o leadingVisits p :=
  (leadingVisits p).orderIsoOfFin (card_leadingVisits p hα)

/-- The crossing label of a visit: the rank of the earlier visit of its pair among all earlier
visits. -/
private def pairLabel (p : PerfectMatching α) (hα : Fintype.card α = 2 * m) (a : α) : Fin m :=
  (leadingVisitsOrderIso p hα).symm ⟨min a (p.val a), min_mem_leadingVisits p a⟩

private theorem pairLabel_eq_pairLabel_iff (p : PerfectMatching α)
    (hα : Fintype.card α = 2 * m) (a b : α) :
    pairLabel p hα a = pairLabel p hα b ↔ b = a ∨ b = p.val a := by
  rw [pairLabel, pairLabel, (leadingVisitsOrderIso p hα).symm.injective.eq_iff, Subtype.mk.injEq]
  constructor
  · intro h
    rcases min_choice a (p.val a) with ha | ha <;> rcases min_choice b (p.val b) with hb | hb <;>
      rw [ha, hb] at h
    · exact .inl h.symm
    · exact .inr (by rw [h, p.apply_apply])
    · exact .inr h.symm
    · exact .inl (p.val.injective h).symm
  · rintro (rfl | rfl)
    · rfl
    · rw [p.apply_apply, min_comm]

/-- The based oriented Gauss code of a traversal whose visits are the elements of a finite linear
order `α` of cardinality `2 * m`, met in increasing order. The two visits of each crossing are
paired by a perfect matching `p`, the over/under status of a visit is `over`, with exactly one
visit of each pair over, and the sign of a crossing is `sign` at the earlier of its two visits.
Crossings are labelled by `Fin m` in the order of their first visits. -/
noncomputable def ofPerfectMatching (hα : Fintype.card α = 2 * m) (p : PerfectMatching α)
    (over : α → Bool) (hover : ∀ a, over (p.val a) = !over a) (sign : α → ℤˣ) :
    BasedOrientedGaussCode m where
  visit i := pairLabel p hα (Fintype.orderIsoFinOfCardEq α hα i)
  over i := over (Fintype.orderIsoFinOfCardEq α hα i)
  sign c := sign (leadingVisitsOrderIso p hα c)
  partner := PerfectMatching.congr (Fintype.orderIsoFinOfCardEq α hα).symm.toEquiv p
  visit_eq_iff i j := by
    rw [pairLabel_eq_pairLabel_iff, PerfectMatching.congr_val_apply,
      (Fintype.orderIsoFinOfCardEq α hα).injective.eq_iff]
    simp [OrderIso.eq_symm_apply]
  over_partner i := by
    simp [hover]

variable (hα : Fintype.card α = 2 * m) (p : PerfectMatching α) (over : α → Bool)
  (hover : ∀ a, over (p.val a) = !over a) (sign : α → ℤˣ)

/-- The `i`-th visit of `ofPerfectMatching` is over exactly when the `i`-th element is. -/
@[simp]
theorem ofPerfectMatching_over (i : Fin (2 * m)) :
    (ofPerfectMatching hα p over hover sign).over i = over (Fintype.orderIsoFinOfCardEq α hα i) :=
  (rfl)

/-- The partner of the `i`-th visit of `ofPerfectMatching` is the visit at the partner of the
`i`-th element. -/
@[simp]
theorem orderIsoFinOfCardEq_ofPerfectMatching_partner (i : Fin (2 * m)) :
    Fintype.orderIsoFinOfCardEq α hα ((ofPerfectMatching hα p over hover sign).partner.val i) =
      p.val (Fintype.orderIsoFinOfCardEq α hα i) := by
  simp [ofPerfectMatching]

/-- **Crossings are numbered in the order of their first visits.** The crossing met at the `i`-th
visit of `ofPerfectMatching` has a smaller label than the one met at the `j`-th visit exactly when
the earlier visit of the first pair comes before the earlier visit of the second. -/
theorem ofPerfectMatching_visit_lt_visit_iff (i j : Fin (2 * m)) :
    (ofPerfectMatching hα p over hover sign).visit i <
        (ofPerfectMatching hα p over hover sign).visit j ↔
      min (Fintype.orderIsoFinOfCardEq α hα i) (p.val (Fintype.orderIsoFinOfCardEq α hα i)) <
        min (Fintype.orderIsoFinOfCardEq α hα j) (p.val (Fintype.orderIsoFinOfCardEq α hα j)) := by
  simp only [ofPerfectMatching, pairLabel, OrderIso.lt_iff_lt, Subtype.mk_lt_mk]

/-- When `sign` takes the same value at the two visits of each pair, the sign of the crossing met
at the `i`-th visit of `ofPerfectMatching` is `sign` at the `i`-th element. -/
theorem ofPerfectMatching_sign_visit (hsign : ∀ a, sign (p.val a) = sign a) (i : Fin (2 * m)) :
    (ofPerfectMatching hα p over hover sign).sign
        ((ofPerfectMatching hα p over hover sign).visit i) =
      sign (Fintype.orderIsoFinOfCardEq α hα i) := by
  simp only [ofPerfectMatching, pairLabel, OrderIso.apply_symm_apply]
  set a := Fintype.orderIsoFinOfCardEq α hα i
  rcases min_choice a (p.val a) with h | h <;> simp only [h, hsign]

end OfPerfectMatching

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
