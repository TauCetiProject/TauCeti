/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Saddle
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Transport

/-!
# Marks and their resolution circles

A mark on a PD-code lies on an arc or on a labelled crossing-free circle. An arc is an orbit
of the native arc matching, so choosing its other half-edge does not change the mark. Distinct
crossing-free circles remain distinct marks, even when their orientations agree.

Every complete smoothing selects a resolved circle through the mark. This selection commutes
with smoothing equivalences and with the native saddle correspondence towards a state having
one circle at the changed crossing. Thus a marked circle can be followed through both a merge
and the reverse correspondence of a split. These are the circle-selection data for the based
Frobenius action and the reduced complex. No geometric point, mark slide across a crossing, or
transport through a crossing-changing Reidemeister move is asserted here.

## References

* M. Khovanov, *Patterns in knot cohomology I*, §3 (marked-component reduction).
-/

public section

namespace TauCeti.PDCode

open Equiv Equiv.Perm

variable {n m r : ℕ}

/-- A combinatorial mark on an arc or a labelled crossing-free circle. The two half-edges of an
arc represent the same mark; the carrier does not depend on a smoothing state. -/
abbrev Mark (D : PDCode n) : Type :=
  Quotient (SameCycle.setoid D.edgePair.val) ⊕ Fin D.crossinglessComponentCount

namespace Mark

/-- Equality of marks is decidable by the finite arc traversal. -/
instance (D : PDCode n) : DecidableEq D.Mark :=
  letI : DecidableRel (SameCycle.setoid D.edgePair.val) :=
    fun x y ↦ inferInstanceAs (Decidable (D.edgePair.val.SameCycle x y))
  inferInstanceAs (DecidableEq
    (Quotient (SameCycle.setoid D.edgePair.val) ⊕ Fin D.crossinglessComponentCount))

/-- The arc orbits and crossing-free labels form an effective finite mark set. -/
instance (D : PDCode n) : Fintype D.Mark :=
  letI : DecidableRel (SameCycle.setoid D.edgePair.val) :=
    fun x y ↦ inferInstanceAs (Decidable (D.edgePair.val.SameCycle x y))
  inferInstanceAs (Fintype
    (Quotient (SameCycle.setoid D.edgePair.val) ⊕ Fin D.crossinglessComponentCount))

variable {D : PDCode n}

/-- The mark on the arc incident to a half-edge. -/
def onArc (D : PDCode n) (x : Fin (4 * n)) : D.Mark := .inl ⟦x⟧

/-- Two half-edges define the same marked arc exactly when they are equal or paired. -/
theorem onArc_eq_onArc_iff (x y : Fin (4 * n)) :
    onArc D x = onArc D y ↔ x = y ∨ x = D.edgePair.val y := by
  rw [onArc, onArc, Sum.inl.injEq, Quotient.eq]
  exact D.edgePair.prop.sameCycle_iff x y

/-- Choosing the other end of an arc does not change its mark. -/
@[simp]
theorem onArc_edgePair (x : Fin (4 * n)) : onArc D (D.edgePair.val x) = onArc D x := by
  exact (onArc_eq_onArc_iff _ _).mpr (Or.inr rfl)

/-- Every mark lies on an arc or is a crossing-free circle label. -/
theorem induction_on (p : D.Mark) {P : D.Mark → Prop}
    (ha : ∀ x, P (onArc D x)) (hi : ∀ i, P (.inr i)) : P p := by
  rcases p with a | i
  · induction a using Quotient.inductionOn with | h x => exact ha x
  · exact hi i

/-- The circle selected by a mark in a complete smoothing. -/
def resolvedCircle (p : D.Mark) (s : Fin n → Bool) : D.ResolvedCircle s :=
  Sum.elim
    (Quotient.lift (fun x ↦ Sum.inl (⟦x⟧ : D.CrossingCircle s)) fun x y h ↦ by
      rcases (D.edgePair.prop.sameCycle_iff x y).mp h with h | h
      · subst h
        rfl
      · subst h
        simp)
    Sum.inr p

/-- An arc mark selects the resolved circle through either of its half-edges. -/
@[simp]
theorem resolvedCircle_onArc (x : Fin (4 * n)) (s : Fin n → Bool) :
    (onArc D x).resolvedCircle s = .inl ⟦x⟧ := (rfl)

/-- A crossing-free mark selects its own labelled circle in every state. -/
@[simp]
theorem resolvedCircle_inr (i : Fin D.crossinglessComponentCount) (s : Fin n → Bool) :
    resolvedCircle (D := D) (Sum.inr i) s = .inr i := (rfl)

/-- Every resolved circle contains a mark. -/
theorem resolvedCircle_surjective (s : Fin n → Bool) :
    Function.Surjective (fun p : D.Mark ↦ p.resolvedCircle s) := by
  rintro (C | i)
  · induction C using Quotient.inductionOn with
    | h x => exact ⟨onArc D x, rfl⟩
  · exact ⟨.inr i, rfl⟩

/-- The native saddle correspondence carries the circle through a mark to the circle through
that same mark. For a split, use this statement with the source and target states reversed. -/
@[simp]
theorem saddleResolvedCircleMap_resolvedCircle (p : D.Mark) {s t : Fin n → Bool} {c : Fin n}
    (hst : ∀ j, j ≠ c → s j = t j) (ht : (D.circlesAt t c).card = 1) :
    D.saddleResolvedCircleMap hst ht (p.resolvedCircle s) = p.resolvedCircle t := by
  induction p using Mark.induction_on <;> simp

end Mark

/-- There is one mark for each of the `2 * n` arcs and each labelled crossing-free circle. -/
theorem card_mark (D : PDCode n) :
    Fintype.card D.Mark = 2 * n + D.crossinglessComponentCount := by
  rw [Fintype.card_eq_nat_card, Mark, Nat.card_sum, Nat.card_fin, ← orbitCount_def,
    orbitCount_edgePair]

namespace SmoothingEquiv

variable {D : PDCode n} {s : Fin n → Bool} {D' : PDCode m} {s' : Fin m → Bool}
  {D'' : PDCode r} {s'' : Fin r → Bool}

/-- Transport marks along a smoothing equivalence, using its arc matching and its explicit
bijection of crossing-free labels. -/
def markCongr (e : D.SmoothingEquiv s D' s') : D.Mark ≃ D'.Mark :=
  (Quotient.congr e.halfEdgeEquiv fun x y ↦ by
    change D.edgePair.val.SameCycle x y ↔
      D'.edgePair.val.SameCycle (e.halfEdgeEquiv x) (e.halfEdgeEquiv y)
    rw [e.edgePair_val_eq_permCongr, sameCycle_permCongr]).sumCongr e.crossinglessEquiv

/-- The transported arc mark is incident to the transported half-edge. -/
@[simp]
theorem markCongr_onArc (e : D.SmoothingEquiv s D' s') (x : Fin (4 * n)) :
    e.markCongr (Mark.onArc D x) = Mark.onArc D' (e.halfEdgeEquiv x) := (rfl)

/-- Crossing-free marks follow the specified label bijection. -/
@[simp]
theorem markCongr_inr (e : D.SmoothingEquiv s D' s') (i : Fin D.crossinglessComponentCount) :
    e.markCongr (.inr i) = .inr (e.crossinglessEquiv i) := (rfl)

/-- Transporting a marked circle agrees with selecting the transported mark's circle. -/
@[simp]
theorem resolvedCircleCongr_resolvedCircle (e : D.SmoothingEquiv s D' s') (p : D.Mark) :
    e.resolvedCircleCongr (p.resolvedCircle s) = (e.markCongr p).resolvedCircle s' := by
  induction p using Mark.induction_on <;> simp

/-- The identity smoothing equivalence fixes every mark. -/
@[simp]
theorem markCongr_refl : (refl D s).markCongr = Equiv.refl _ := by
  ext p
  induction p using Mark.induction_on <;> simp

/-- A composite smoothing equivalence composes the mark transports. -/
@[simp]
theorem markCongr_trans (e : D.SmoothingEquiv s D' s') (f : D'.SmoothingEquiv s' D'' s'') :
    (e.trans f).markCongr = e.markCongr.trans f.markCongr := by
  ext p
  induction p using Mark.induction_on <;> simp

/-- Inverting a smoothing equivalence inverts its transport of marks. -/
@[simp]
theorem markCongr_symm (e : D.SmoothingEquiv s D' s') :
    e.symm.markCongr = e.markCongr.symm := by
  rw [eq_comm, Equiv.symm_eq_iff_trans_eq_refl, ← markCongr_trans, self_trans_symm,
    markCongr_refl]

end SmoothingEquiv

/-- Marks of a disjoint union decompose into the marks of the two summands. -/
def disjointUnionMarkEquiv (D : PDCode n) (E : PDCode m) :
    (D.disjointUnion E).Mark ≃ D.Mark ⊕ E.Mark :=
  (((Quotient.congr (disjointUnionHalfEdgeEquiv n m).symm fun x y ↦ by
    change (D.disjointUnion E).edgePair.val.SameCycle x y ↔
      (Perm.sumCongr D.edgePair.val E.edgePair.val).SameCycle
        ((disjointUnionHalfEdgeEquiv n m).symm x)
        ((disjointUnionHalfEdgeEquiv n m).symm y)
    rw [D.disjointUnion_edgePair_val E]
    exact sameCycle_permCongr_iff (Perm.sumCongr D.edgePair.val E.edgePair.val)
      (disjointUnionHalfEdgeEquiv n m))).trans
      (sameCycleQuotientSumCongrEquiv D.edgePair.val E.edgePair.val)).sumCongr
        ((finCongr (D.disjointUnion_crossinglessComponentCount E)).trans
          finSumFinEquiv.symm)).trans (sumSumSumComm _ _ _ _)

namespace Mark

variable {D : PDCode n}

/-- Decomposition sends an arc in the first summand to that summand's mark. -/
@[simp]
theorem disjointUnionMarkEquiv_onArc_inl (D : PDCode n) (E : PDCode m) (x : Fin (4 * n)) :
    disjointUnionMarkEquiv D E
      (onArc (D.disjointUnion E) (disjointUnionHalfEdgeEquiv n m (.inl x))) =
      .inl (onArc D x) := by
  simp [disjointUnionMarkEquiv, onArc]

/-- Decomposition sends an arc in the second summand to that summand's mark. -/
@[simp]
theorem disjointUnionMarkEquiv_onArc_inr (D : PDCode n) (E : PDCode m) (x : Fin (4 * m)) :
    disjointUnionMarkEquiv D E
      (onArc (D.disjointUnion E) (disjointUnionHalfEdgeEquiv n m (.inr x))) =
      .inr (onArc E x) := by
  simp [disjointUnionMarkEquiv, onArc]

/-- The inverse includes an arc mark from the first summand. -/
@[simp]
theorem disjointUnionMarkEquiv_symm_inl_onArc (D : PDCode n) (E : PDCode m)
    (x : Fin (4 * n)) :
    (disjointUnionMarkEquiv D E).symm (.inl (onArc D x)) =
      onArc (D.disjointUnion E) (disjointUnionHalfEdgeEquiv n m (.inl x)) := by
  apply (disjointUnionMarkEquiv D E).injective
  simp

/-- The inverse includes an arc mark from the second summand. -/
@[simp]
theorem disjointUnionMarkEquiv_symm_inr_onArc (D : PDCode n) (E : PDCode m)
    (x : Fin (4 * m)) :
    (disjointUnionMarkEquiv D E).symm (.inr (onArc E x)) =
      onArc (D.disjointUnion E) (disjointUnionHalfEdgeEquiv n m (.inr x)) := by
  apply (disjointUnionMarkEquiv D E).injective
  simp

/-- The inverse includes a crossing-free mark in the first block of labels. -/
@[simp]
theorem disjointUnionMarkEquiv_symm_inl_inr (D : PDCode n) (E : PDCode m)
    (i : Fin D.crossinglessComponentCount) :
    (disjointUnionMarkEquiv D E).symm (.inl (.inr i)) =
      .inr (finCongr (D.disjointUnion_crossinglessComponentCount E).symm
        (Fin.castAdd E.crossinglessComponentCount i)) := by
  simp [disjointUnionMarkEquiv]

/-- The inverse includes a crossing-free mark in the second block of labels. -/
@[simp]
theorem disjointUnionMarkEquiv_symm_inr_inr (D : PDCode n) (E : PDCode m)
    (i : Fin E.crossinglessComponentCount) :
    (disjointUnionMarkEquiv D E).symm (.inr (.inr i)) =
      .inr (finCongr (D.disjointUnion_crossinglessComponentCount E).symm
        (Fin.natAdd D.crossinglessComponentCount i)) := by
  simp [disjointUnionMarkEquiv]

/-- Include a mark from the first diagram using the inverse decomposition. -/
def disjointUnionLeft (p : D.Mark) (E : PDCode m) : (D.disjointUnion E).Mark :=
  (disjointUnionMarkEquiv D E).symm (.inl p)

/-- Include a mark from the second diagram using the inverse decomposition. -/
def disjointUnionRight (p : D.Mark) (E : PDCode m) : (E.disjointUnion D).Mark :=
  (disjointUnionMarkEquiv E D).symm (.inr p)

/-- The first inclusion carries an arc mark along the native half-edge inclusion. -/
@[simp]
theorem disjointUnionLeft_onArc (x : Fin (4 * n)) (E : PDCode m) :
    (onArc D x).disjointUnionLeft E =
      onArc (D.disjointUnion E) (disjointUnionHalfEdgeEquiv n m (.inl x)) :=
  disjointUnionMarkEquiv_symm_inl_onArc D E x

/-- The second inclusion carries an arc mark along the native half-edge inclusion. -/
@[simp]
theorem disjointUnionRight_onArc (x : Fin (4 * n)) (E : PDCode m) :
    (onArc D x).disjointUnionRight E =
      onArc (E.disjointUnion D) (disjointUnionHalfEdgeEquiv m n (.inr x)) :=
  disjointUnionMarkEquiv_symm_inr_onArc E D x

/-- The first inclusion retains the initial block of crossing-free labels. -/
@[simp]
theorem disjointUnionLeft_inr (i : Fin D.crossinglessComponentCount) (E : PDCode m) :
    disjointUnionLeft (D := D) (.inr i) E =
      .inr (finCongr (D.disjointUnion_crossinglessComponentCount E).symm
        (Fin.castAdd E.crossinglessComponentCount i)) :=
  disjointUnionMarkEquiv_symm_inl_inr D E i

/-- The second inclusion uses the final block of crossing-free labels. -/
@[simp]
theorem disjointUnionRight_inr (i : Fin D.crossinglessComponentCount) (E : PDCode m) :
    disjointUnionRight (D := D) (.inr i) E =
      .inr (finCongr (E.disjointUnion_crossinglessComponentCount D).symm
        (Fin.natAdd E.crossinglessComponentCount i)) :=
  disjointUnionMarkEquiv_symm_inr_inr E D i

/-- Circle selection commutes with the decomposition of marks of a disjoint union. -/
@[simp]
theorem disjointUnionResolvedCircleEquiv_resolvedCircle (D : PDCode n) (E : PDCode m)
    (p : (D.disjointUnion E).Mark) (s : Fin (n + m) → Bool) :
    D.disjointUnionResolvedCircleEquiv E s (p.resolvedCircle s) =
      Sum.map (fun q : D.Mark ↦ q.resolvedCircle (s ∘ Fin.castAdd m))
        (fun q : E.Mark ↦ q.resolvedCircle (s ∘ Fin.natAdd n))
        (disjointUnionMarkEquiv D E p) := by
  obtain ⟨p, rfl⟩ := (disjointUnionMarkEquiv D E).symm.surjective p
  rcases p with p | p
  · induction p using Mark.induction_on with
    | ha x => simp
    | hi i =>
      simp only [apply_symm_apply, Sum.map_inl, resolvedCircle_inr]
      apply (D.disjointUnionResolvedCircleEquiv E s).symm.injective
      simp only [symm_apply_apply, disjointUnionMarkEquiv_symm_inl_inr,
        resolvedCircle_inr, disjointUnionResolvedCircleEquiv_symm_inl_inr]
  · induction p using Mark.induction_on with
    | ha x => simp
    | hi i =>
      simp only [apply_symm_apply, Sum.map_inr, resolvedCircle_inr]
      apply (D.disjointUnionResolvedCircleEquiv E s).symm.injective
      simp only [symm_apply_apply, disjointUnionMarkEquiv_symm_inr_inr,
        resolvedCircle_inr, disjointUnionResolvedCircleEquiv_symm_inr_inr]

end Mark

end TauCeti.PDCode
