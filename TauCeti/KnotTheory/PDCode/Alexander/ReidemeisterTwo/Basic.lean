/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Alexander.Basic
public import TauCeti.KnotTheory.PDCode.Oriented.ClaspInsertion
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The Alexander module under the second Reidemeister move

The second Reidemeister move between two distinct arcs of an oriented PD-code is the clasp
insertion `TauCeti.OrientedPDCode.insertClasp`: the arc ending at the half-edge `p` and the arc
ending at `q` are cut open and routed through two new crossings, one strand over the other at
both. This file shows that the insertion keeps the Alexander module
(`TauCeti.OrientedPDCode.AlexanderModule`) up to `ℤ[T;T⁻¹]`-linear equivalence, and therefore
every elementary ideal.

Each cut arc is split into three: from its old end to the first new crossing, between the two
new crossings, and from the second new crossing back to its other old end. On the over-strand the
three pieces are identified by the relations of the two crossings. On the under-strand the middle
piece is an affine combination `w • x + (1 - w) • y` of the incoming under-arc `x` and the
over-arc `y`, and the relation at the second crossing applies the inverse weight `w⁻¹`, since the
two new crossings have opposite signs (`TauCeti.OrientedPDCode.crossingSign_insertClasp_last`).
It therefore returns the incoming under-arc: the last piece of each cut arc gives the same
generator as its first piece. Sending the middle pieces to these affine combinations and every
other half-edge to itself identifies the two Alexander modules.

The insertions involving crossing-free circles, `TauCeti.OrientedPDCode.insertCircleClasp` and
`TauCeti.OrientedPDCode.adjoinTwoCircleClasp`, and the third Reidemeister move are not treated
here.

## Main definitions

* `TauCeti.OrientedPDCode.alexanderModuleInsertClaspEquiv`: the clasp insertion keeps the
  Alexander module.

## Main results

* `TauCeti.OrientedPDCode.elementaryIdeal_insertClasp`: the clasp insertion, in particular the
  second Reidemeister move between two arcs, keeps every elementary ideal.
* `TauCeti.OrientedPDCode.alexanderGenerator_insertClasp_inl_inl_apply_self` and
  `TauCeti.OrientedPDCode.alexanderGenerator_insertClasp_inl_inl_apply_right`: after the
  insertion, the two old ends of each cut arc still give the same generator.
* `TauCeti.OrientedPDCode.alexanderWeight_insertClasp_castSucc_last` and
  `TauCeti.OrientedPDCode.alexanderWeight_insertClasp_last`: the weights of the two new crossings.

## References

* R. H. Crowell, R. H. Fox, *Introduction to Knot Theory*, Graduate Texts in Mathematics 57,
  Springer (1977), Chapters VI and VII.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Graduate Texts in Mathematics 175,
  Springer (1997), Chapters 1 and 6.
-/

public section

noncomputable section

open LaurentPolynomial

namespace TauCeti

namespace OrientedPDCode

open PDCode

variable {n : ℕ} (D : OrientedPDCode n) (p q : Fin (4 * n)) (b : Bool) (hqp : q ≠ p)
  (hqe : q ≠ D.edgePair.val p)

/-! ### The weights of the clasp -/

private theorem crossing_insertClasp_castSucc_castSucc (i : Fin n) (slot : Fin 4) :
    (D.toPDCode.insertClasp p q b hqp hqe).crossing i.castSucc.castSucc slot =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl (D.crossing i slot)))) := by
  simp

private theorem crossing_insertClasp_castSucc_last (slot : Fin 4) :
    (D.toPDCode.insertClasp p q b hqp hqe).crossing (Fin.last n).castSucc slot =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr slot))) := by
  simp

private theorem crossing_insertClasp_last (slot : Fin 4) :
    (D.toPDCode.insertClasp p q b hqp hqe).crossing (Fin.last (n + 1)) slot =
      halfEdgeSuccEquiv (n + 1) (.inr slot) := by
  simp

/-- The old crossings keep their weights. -/
@[simp]
theorem alexanderWeight_insertClasp_castSucc_castSucc (i : Fin n) (slot : Fin 4) :
    (D.insertClasp p q b hqp hqe).alexanderWeight i.castSucc.castSucc slot =
      D.alexanderWeight i slot := by
  simp [alexanderWeight_def, PDCode.isOver_def]

/-- The weights of the first new crossing. The over-strand has weight `1`, and the under-strand has
the weight `t` or `t⁻¹` of the meridian of the over-strand: the strand through `q` when `b` holds,
and the strand through `p` otherwise. -/
@[simp]
theorem alexanderWeight_insertClasp_castSucc_last (slot : Fin 4) :
    (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc slot =
      if b then
        ![T (if D.orientation q then -1 else 1), 1, T (if D.orientation q then 1 else -1), 1] slot
      else
        ![1, T (if D.orientation p then 1 else -1), 1,
          T (if D.orientation p then -1 else 1)] slot := by
  rw [alexanderWeight_def]
  cases b <;> cases hp : D.orientation p <;> cases hq : D.orientation q <;> fin_cases slot <;>
    simp [PDCode.isOver_def, hp, hq]

/-- The weights of the second new crossing. Its over-strand is that of the first new crossing, and
its under-strand weights are inverse to the corresponding ones there, since the two new crossings
have opposite signs. -/
@[simp]
theorem alexanderWeight_insertClasp_last (slot : Fin 4) :
    (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last (n + 1)) slot =
      if b then
        ![1, T (if D.orientation q then 1 else -1), 1, T (if D.orientation q then -1 else 1)] slot
      else
        ![T (if D.orientation p then -1 else 1), 1,
          T (if D.orientation p then 1 else -1), 1] slot := by
  rw [alexanderWeight_def]
  cases b <;> cases hp : D.orientation p <;> cases hq : D.orientation q <;> fin_cases slot <;>
    simp [PDCode.isOver_def, hp, hq]

/-- Along the strand through `q`, the weight of slot `0` of the second new crossing is inverse to
the weight of slot `1` of the first. -/
private theorem alexanderWeight_insertClasp_last_zero_mul :
    (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last (n + 1)) 0 *
      (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 1 = 1 := by
  rw [alexanderWeight_insertClasp_last, alexanderWeight_insertClasp_castSucc_last]
  cases b <;> cases D.orientation p <;> cases D.orientation q <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one,
      ← T_add, neg_add_cancel, add_neg_cancel, T_zero]

/-- Along the strand through `p`, the weight of slot `1` of the second new crossing is inverse to
the weight of slot `0` of the first. -/
private theorem alexanderWeight_insertClasp_last_one_mul :
    (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last (n + 1)) 1 *
      (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 0 = 1 := by
  rw [alexanderWeight_insertClasp_last, alexanderWeight_insertClasp_castSucc_last]
  cases b <;> cases D.orientation p <;> cases D.orientation q <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one,
      ← T_add, neg_add_cancel, add_neg_cancel, T_zero]

/-- The same strand is over at both new crossings: the strand through `p` (slots `0` of the first
and `1` of the second) or the strand through `q` (slots `1` of the first and `0` of the second). -/
private theorem alexanderWeight_insertClasp_over :
    ((D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 0 = 1 ∧
        (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last (n + 1)) 1 = 1) ∨
      ((D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 1 = 1 ∧
        (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last (n + 1)) 0 = 1) := by
  cases b <;> simp

/-- The relations of the clasp. Let `x₀` and `x₁` be the arcs entering the first new crossing at
its slots `0` and `1`, and `x₂`, `x₃` the arcs leaving it at slots `2` and `3`, given by the
relations there. Slots `0` and `1` of the second new crossing are joined to slots `3` and `2` of the
first, and its relations there return `x₁` and `x₀`: its weights are inverse to those of the first
crossing, and the same strand is over at both. -/
private theorem clasp_relations {M : Type*} [AddCommGroup M] [Module ℤ[T;T⁻¹] M] {x₀ x₁ x₂ x₃ : M}
    (hx₂ : x₂ = (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 0 • x₀ +
      (1 - (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 0) • x₁)
    (hx₃ : x₃ = (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 1 • x₁ +
      (1 - (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 1) • x₂) :
    (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last (n + 1)) 0 • x₃ +
        (1 - (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last (n + 1)) 0) • x₂ = x₁ ∧
      (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last (n + 1)) 1 • x₂ +
        (1 - (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last (n + 1)) 1) • x₁ = x₀ := by
  have h₀ := alexanderWeight_insertClasp_last_zero_mul D p q b hqp hqe
  have h₁ := alexanderWeight_insertClasp_last_one_mul D p q b hqp hqe
  have hover := alexanderWeight_insertClasp_over D p q b hqp hqe
  generalize (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc = wA,
    (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last (n + 1)) = wB at *
  rcases hover with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · rw [hA, one_smul, sub_self, zero_smul, add_zero] at hx₂
    rw [hx₃, hx₂, hB]
    constructor
    · linear_combination (norm := module) h₀ • x₁ - h₀ • x₀
    · simp
  · rw [hA, one_smul, sub_self, zero_smul, add_zero] at hx₃
    rw [hx₃, hx₂, hB]
    constructor
    · simp
    · linear_combination (norm := module) h₁ • x₀ - h₁ • x₁

/-! ### The generators of the cut arcs -/

/-- In the code with the clasp, the relations of the two new crossings identify slots `2` and `3`
of the second crossing with slots `1` and `0` of the first. -/
private theorem alexanderGenerator_insertClasp_inr_two_three :
    (D.insertClasp p q b hqp hqe).alexanderGenerator (.inl (halfEdgeSuccEquiv (n + 1) (.inr 2))) =
        (D.insertClasp p q b hqp hqe).alexanderGenerator
          (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 1))))) ∧
      (D.insertClasp p q b hqp hqe).alexanderGenerator
          (.inl (halfEdgeSuccEquiv (n + 1) (.inr 3))) =
        (D.insertClasp p q b hqp hqe).alexanderGenerator
          (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 0))))) := by
  set D' := D.insertClasp p q b hqp hqe
  have rA₀ := D'.alexanderGenerator_crossing_add_two (Fin.last n).castSucc 0
  have rA₁ := D'.alexanderGenerator_crossing_add_two (Fin.last n).castSucc 1
  have rB₀ := D'.alexanderGenerator_crossing_add_two (Fin.last (n + 1)) 0
  have rB₁ := D'.alexanderGenerator_crossing_add_two (Fin.last (n + 1)) 1
  have arc₀ := D'.alexanderGenerator_edgePair (halfEdgeSuccEquiv (n + 1) (.inr 0))
  have arc₁ := D'.alexanderGenerator_edgePair (halfEdgeSuccEquiv (n + 1) (.inr 1))
  simp only [D', toPDCode_insertClasp, crossing_insertClasp_castSucc_last,
    crossing_insertClasp_last, insertClasp_edgePair_inr_zero, insertClasp_edgePair_inr_one,
    Fin.isValue, Fin.reduceAdd, zero_add] at rA₀ rA₁ rB₀ rB₁ arc₀ arc₁
  rw [← arc₀, ← arc₁] at rB₀
  rw [← arc₁] at rB₁
  obtain ⟨h₀, h₁⟩ := clasp_relations D p q b hqp hqe rA₀ rA₁
  refine ⟨rB₀.trans h₀, ?_⟩
  rw [rB₁, rB₀, h₀, h₁]

/-- After the clasp is inserted, the two old ends of the arc cut at `p` still give the same
generator of the Alexander module. -/
@[simp]
theorem alexanderGenerator_insertClasp_inl_inl_apply_self :
    (D.insertClasp p q b hqp hqe).alexanderGenerator
        (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl (D.edgePair.val p)))))) =
      (D.insertClasp p q b hqp hqe).alexanderGenerator
        (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl p))))) := by
  have hend := (D.insertClasp p q b hqp hqe).alexanderGenerator_edgePair
    (halfEdgeSuccEquiv (n + 1) (.inr 3))
  have hstart := (D.insertClasp p q b hqp hqe).alexanderGenerator_edgePair
    (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 0))))
  simp only [toPDCode_insertClasp, insertClasp_edgePair_inr_three,
    insertClasp_edgePair_inl_inr_zero] at hend hstart
  rw [hend, hstart, (alexanderGenerator_insertClasp_inr_two_three D p q b hqp hqe).2]

/-- After the clasp is inserted, the two old ends of the arc cut at `q` still give the same
generator of the Alexander module. -/
@[simp]
theorem alexanderGenerator_insertClasp_inl_inl_apply_right :
    (D.insertClasp p q b hqp hqe).alexanderGenerator
        (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl (D.edgePair.val q)))))) =
      (D.insertClasp p q b hqp hqe).alexanderGenerator
        (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl q))))) := by
  have hend := (D.insertClasp p q b hqp hqe).alexanderGenerator_edgePair
    (halfEdgeSuccEquiv (n + 1) (.inr 2))
  have hstart := (D.insertClasp p q b hqp hqe).alexanderGenerator_edgePair
    (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 1))))
  simp only [toPDCode_insertClasp, insertClasp_edgePair_inr_two,
    insertClasp_edgePair_inl_inr_one] at hend hstart
  rw [hend, hstart, (alexanderGenerator_insertClasp_inr_two_three D p q b hqp hqe).1]

/-! ### The equivalence of Alexander modules -/

/-- The images of the slots of the first new crossing: the arcs at `p` and `q`, and the affine
combinations that the relations at its slots `0` and `1` prescribe for slots `2` and `3`. -/
private def claspFirst : Fin 4 → D.AlexanderModule :=
  let w := (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc
  let x₂ := w 0 • D.alexanderGenerator (.inl p) + (1 - w 0) • D.alexanderGenerator (.inl q)
  ![D.alexanderGenerator (.inl p), D.alexanderGenerator (.inl q), x₂,
    w 1 • D.alexanderGenerator (.inl q) + (1 - w 1) • x₂]

/-- The images of the slots of the second new crossing: slots `0` and `1` are joined to slots `3`
and `2` of the first, and slots `2` and `3` to the old ends of the arcs at `q` and `p`. -/
private def claspSecond : Fin 4 → D.AlexanderModule :=
  ![claspFirst D p q b hqp hqe 3, claspFirst D p q b hqp hqe 2, D.alexanderGenerator (.inl q),
    D.alexanderGenerator (.inl p)]

/-- The images of the generators of the code with the clasp in the Alexander module of `D`. -/
private def insertClaspValue :
    Fin (4 * (n + 2)) ⊕ Fin (D.insertClasp p q b hqp hqe).crossinglessComponentCount →
      D.AlexanderModule :=
  Sum.elim
    (fun x ↦ Sum.elim
      (fun y ↦ Sum.elim (fun z ↦ D.alexanderGenerator (.inl z)) (claspFirst D p q b hqp hqe)
        ((halfEdgeSuccEquiv n).symm y))
      (claspSecond D p q b hqp hqe) ((halfEdgeSuccEquiv (n + 1)).symm x))
    fun j ↦ D.alexanderGenerator (.inr (Fin.cast (by simp) j))

/-- The images of the slots of the second new crossing satisfy its relations at slots `0`
and `1`. -/
private theorem claspSecond_relations :
    claspSecond D p q b hqp hqe 2 =
        (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last (n + 1)) 0 •
          claspSecond D p q b hqp hqe 0 +
        (1 - (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last (n + 1)) 0) •
          claspSecond D p q b hqp hqe 1 ∧
      claspSecond D p q b hqp hqe 3 =
        (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last (n + 1)) 1 •
          claspSecond D p q b hqp hqe 1 +
        (1 - (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last (n + 1)) 1) •
          claspSecond D p q b hqp hqe 2 := by
  obtain ⟨h₀, h₁⟩ := clasp_relations D p q b hqp hqe (x₀ := claspFirst D p q b hqp hqe 0)
    (x₁ := claspFirst D p q b hqp hqe 1) (x₂ := claspFirst D p q b hqp hqe 2)
    (x₃ := claspFirst D p q b hqp hqe 3) (by simp [claspFirst]) (by simp [claspFirst])
  simp only [claspSecond, Matrix.cons_val]
  exact ⟨h₀.symm, by simpa [claspFirst] using h₁.symm⟩

/-- The map from the Alexander module of the code with the clasp, sending the old half-edges to
themselves and the new ones to `claspFirst` and `claspSecond`. -/
private def insertClaspHom :
    (D.insertClasp p q b hqp hqe).AlexanderModule →ₗ[ℤ[T;T⁻¹]] D.AlexanderModule :=
  (D.insertClasp p q b hqp hqe).alexanderLift (insertClaspValue D p q b hqp hqe)
    (fun x ↦ by
      obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv (n + 1)).surjective x
      · obtain ⟨z | s, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
        · by_cases hzp : z = p
          · subst hzp
            simp [insertClaspValue, claspFirst]
          by_cases hze : z = D.edgePair.val p
          · subst hze
            simp [insertClaspValue, claspSecond]
          by_cases hzq : z = q
          · subst hzq
            simp [insertClaspValue, claspFirst]
          by_cases hze' : z = D.edgePair.val q
          · subst hze'
            simp [insertClaspValue, claspSecond]
          simp [insertClaspValue,
            D.toPDCode.insertClasp_edgePair_inl_inl_of_ne p q b hqp hqe hzp hze hzq hze']
        · fin_cases s <;> simp [insertClaspValue, claspFirst, claspSecond]
      · fin_cases s <;> simp [insertClaspValue, claspSecond])
    (fun i ↦ by
      induction i using Fin.lastCases with
      | last =>
        obtain ⟨h₀, h₁⟩ := claspSecond_relations D p q b hqp hqe
        refine (D.insertClasp p q b hqp hqe).apply_crossing_add_two_of_zero_of_one
          (fun x ↦ insertClaspValue D p q b hqp hqe (.inl x)) _ ?_ ?_
        · simpa [insertClaspValue] using h₀
        · simpa [insertClaspValue] using h₁
      | cast i =>
        induction i using Fin.lastCases with
        | last =>
          refine (D.insertClasp p q b hqp hqe).apply_crossing_add_two_of_zero_of_one
            (fun x ↦ insertClaspValue D p q b hqp hqe (.inl x)) _ ?_ ?_ <;>
            simp [insertClaspValue, claspFirst]
        | cast i =>
          intro slot
          simpa [insertClaspValue] using D.alexanderGenerator_crossing_add_two i slot)

private theorem insertClaspHom_alexanderGenerator
    (g : Fin (4 * (n + 2)) ⊕ Fin (D.insertClasp p q b hqp hqe).crossinglessComponentCount) :
    insertClaspHom D p q b hqp hqe ((D.insertClasp p q b hqp hqe).alexanderGenerator g) =
      insertClaspValue D p q b hqp hqe g :=
  alexanderLift_alexanderGenerator _ _ _ _ _

/-- The map to the Alexander module of the code with the clasp, sending each old generator to the
generator of the same half-edge or component. -/
private def insertClaspInvHom :
    D.AlexanderModule →ₗ[ℤ[T;T⁻¹]] (D.insertClasp p q b hqp hqe).AlexanderModule :=
  D.alexanderLift
    (Sum.elim (fun y ↦ (D.insertClasp p q b hqp hqe).alexanderGenerator
        (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl y))))))
      fun j ↦ (D.insertClasp p q b hqp hqe).alexanderGenerator (.inr (Fin.cast (by simp) j)))
    (fun y ↦ by
      simp only [Sum.elim_inl]
      by_cases hyp : y = p
      · subst hyp
        exact alexanderGenerator_insertClasp_inl_inl_apply_self D y q b hqp hqe
      by_cases hye : y = D.edgePair.val p
      · subst hye
        rw [PerfectMatching.apply_apply]
        exact (alexanderGenerator_insertClasp_inl_inl_apply_self D p q b hqp hqe).symm
      by_cases hyq : y = q
      · subst hyq
        exact alexanderGenerator_insertClasp_inl_inl_apply_right D p y b hqp hqe
      by_cases hye' : y = D.edgePair.val q
      · subst hye'
        rw [PerfectMatching.apply_apply]
        exact (alexanderGenerator_insertClasp_inl_inl_apply_right D p q b hqp hqe).symm
      simpa [D.toPDCode.insertClasp_edgePair_inl_inl_of_ne p q b hqp hqe hyp hye hyq hye'] using
        (D.insertClasp p q b hqp hqe).alexanderGenerator_edgePair
          (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl y)))))
    (fun i slot ↦ by
      simpa [crossing_insertClasp_castSucc_castSucc] using
        (D.insertClasp p q b hqp hqe).alexanderGenerator_crossing_add_two i.castSucc.castSucc slot)

private theorem insertClaspInvHom_alexanderGenerator
    (g : Fin (4 * n) ⊕ Fin D.crossinglessComponentCount) :
    insertClaspInvHom D p q b hqp hqe (D.alexanderGenerator g) =
      Sum.elim (fun y ↦ (D.insertClasp p q b hqp hqe).alexanderGenerator
          (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl y))))))
        (fun j ↦ (D.insertClasp p q b hqp hqe).alexanderGenerator (.inr (Fin.cast (by simp) j)))
        g :=
  alexanderLift_alexanderGenerator _ _ _ _ _

/-- The images of the slots of the first new crossing are sent back to these slots. -/
private theorem insertClaspInvHom_claspFirst (s : Fin 4) :
    insertClaspInvHom D p q b hqp hqe (claspFirst D p q b hqp hqe s) =
      (D.insertClasp p q b hqp hqe).alexanderGenerator
        (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr s))))) := by
  set D' := D.insertClasp p q b hqp hqe
  have rA₀ := D'.alexanderGenerator_crossing_add_two (Fin.last n).castSucc 0
  have rA₁ := D'.alexanderGenerator_crossing_add_two (Fin.last n).castSucc 1
  have arc₀ := D'.alexanderGenerator_edgePair
    (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 0))))
  have arc₁ := D'.alexanderGenerator_edgePair
    (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 1))))
  simp only [D', toPDCode_insertClasp, crossing_insertClasp_castSucc_last,
    insertClasp_edgePair_inl_inr_zero, insertClasp_edgePair_inl_inr_one, Fin.isValue,
    Fin.reduceAdd, zero_add] at rA₀ rA₁ arc₀ arc₁
  fin_cases s <;>
    simp [-alexanderWeight_insertClasp_castSucc_last, claspFirst,
      insertClaspInvHom_alexanderGenerator, D', arc₀, arc₁, rA₀, rA₁]

/-- **The second Reidemeister move keeps the Alexander module**: inserting a clasp into two
distinct arcs gives a code whose Alexander module is `ℤ[T;T⁻¹]`-linearly equivalent to that of
`D`. The inverse sends every generator of `D` to the generator of the same half-edge or
component. -/
def alexanderModuleInsertClaspEquiv :
    (D.insertClasp p q b hqp hqe).AlexanderModule ≃ₗ[ℤ[T;T⁻¹]] D.AlexanderModule :=
  LinearEquiv.ofLinearMap (insertClaspHom D p q b hqp hqe) (insertClaspInvHom D p q b hqp hqe)
    (by
      ext (y | j) <;>
        simp [insertClaspHom_alexanderGenerator, insertClaspInvHom_alexanderGenerator,
          insertClaspValue])
    (by
      ext (x | j)
      · obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv (n + 1)).surjective x
        · obtain ⟨z | s, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
          · simp [insertClaspHom_alexanderGenerator, insertClaspInvHom_alexanderGenerator,
              insertClaspValue]
          · simp [insertClaspHom_alexanderGenerator, insertClaspValue,
              insertClaspInvHom_claspFirst]
        · -- The slots of the second crossing: `0` and `1` are joined to slots `3` and `2` of
          -- the first, and `2` and `3` give the generators of slots `1` and `0` of the first.
          have h23 := alexanderGenerator_insertClasp_inr_two_three D p q b hqp hqe
          have arc₀ := (D.insertClasp p q b hqp hqe).alexanderGenerator_edgePair
            (halfEdgeSuccEquiv (n + 1) (.inr 0))
          have arc₁ := (D.insertClasp p q b hqp hqe).alexanderGenerator_edgePair
            (halfEdgeSuccEquiv (n + 1) (.inr 1))
          simp only [toPDCode_insertClasp, insertClasp_edgePair_inr_zero,
            insertClasp_edgePair_inr_one] at arc₀ arc₁
          fin_cases s <;>
            simp [insertClaspHom_alexanderGenerator, insertClaspValue, claspSecond,
              insertClaspInvHom_claspFirst, arc₀, arc₁, h23]
      · simp [insertClaspHom_alexanderGenerator, insertClaspInvHom_alexanderGenerator,
          insertClaspValue])

/-- The equivalence sends the generator of an old half-edge to the generator of the same
half-edge. -/
@[simp]
theorem alexanderModuleInsertClaspEquiv_apply_alexanderGenerator_inl_inl (x : Fin (4 * n)) :
    D.alexanderModuleInsertClaspEquiv p q b hqp hqe
        ((D.insertClasp p q b hqp hqe).alexanderGenerator
          (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x)))))) =
      D.alexanderGenerator (.inl x) := by
  simp [alexanderModuleInsertClaspEquiv, insertClaspHom_alexanderGenerator, insertClaspValue]

/-- The equivalence sends the generators of the slots of the first new crossing to the generators
of the half-edges `p` and `q` at slots `0` and `1`, and at slots `2` and `3` to the combinations
of these that the relations at slots `0` and `1` of that crossing prescribe. -/
@[simp]
theorem alexanderModuleInsertClaspEquiv_apply_alexanderGenerator_inl_inl_inr (s : Fin 4) :
    D.alexanderModuleInsertClaspEquiv p q b hqp hqe
        ((D.insertClasp p q b hqp hqe).alexanderGenerator
          (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr s)))))) =
      ![D.alexanderGenerator (.inl p), D.alexanderGenerator (.inl q),
        (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 0 •
            D.alexanderGenerator (.inl p) +
          (1 - (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 0) •
            D.alexanderGenerator (.inl q),
        (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 1 •
            D.alexanderGenerator (.inl q) +
          (1 - (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 1) •
            ((D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 0 •
                D.alexanderGenerator (.inl p) +
              (1 - (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 0) •
                D.alexanderGenerator (.inl q))] s := by
  simp [alexanderModuleInsertClaspEquiv, insertClaspHom_alexanderGenerator, insertClaspValue,
    claspFirst]

/-- The equivalence sends the generators of the slots of the second new crossing at slots `0` and
`1` to the images of slots `3` and `2` of the first new crossing, to which they are joined, and at
slots `2` and `3` to the generators of the half-edges `q` and `p`. -/
@[simp]
theorem alexanderModuleInsertClaspEquiv_apply_alexanderGenerator_inl_inr (s : Fin 4) :
    D.alexanderModuleInsertClaspEquiv p q b hqp hqe
        ((D.insertClasp p q b hqp hqe).alexanderGenerator
          (.inl (halfEdgeSuccEquiv (n + 1) (.inr s)))) =
      ![(D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 1 •
            D.alexanderGenerator (.inl q) +
          (1 - (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 1) •
            ((D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 0 •
                D.alexanderGenerator (.inl p) +
              (1 - (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 0) •
                D.alexanderGenerator (.inl q)),
        (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 0 •
            D.alexanderGenerator (.inl p) +
          (1 - (D.insertClasp p q b hqp hqe).alexanderWeight (Fin.last n).castSucc 0) •
            D.alexanderGenerator (.inl q),
        D.alexanderGenerator (.inl q), D.alexanderGenerator (.inl p)] s := by
  simp [alexanderModuleInsertClaspEquiv, insertClaspHom_alexanderGenerator, insertClaspValue,
    claspSecond, claspFirst]

/-- The equivalence sends the generator of a crossing-free component to the generator of the same
component. -/
@[simp]
theorem alexanderModuleInsertClaspEquiv_apply_alexanderGenerator_inr
    (j : Fin (D.insertClasp p q b hqp hqe).crossinglessComponentCount) :
    D.alexanderModuleInsertClaspEquiv p q b hqp hqe
        ((D.insertClasp p q b hqp hqe).alexanderGenerator (.inr j)) =
      D.alexanderGenerator (.inr (Fin.cast (by simp) j)) := by
  simp [alexanderModuleInsertClaspEquiv, insertClaspHom_alexanderGenerator, insertClaspValue]

/-- The inverse equivalence sends every generator to the generator of the same half-edge or
component. -/
@[simp]
theorem alexanderModuleInsertClaspEquiv_symm_apply_alexanderGenerator
    (g : Fin (4 * n) ⊕ Fin D.crossinglessComponentCount) :
    (D.alexanderModuleInsertClaspEquiv p q b hqp hqe).symm (D.alexanderGenerator g) =
      Sum.elim (fun y ↦ (D.insertClasp p q b hqp hqe).alexanderGenerator
          (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl y))))))
        (fun j ↦ (D.insertClasp p q b hqp hqe).alexanderGenerator (.inr (Fin.cast (by simp) j)))
        g :=
  insertClaspInvHom_alexanderGenerator D p q b hqp hqe g

/-- **The second Reidemeister move keeps the elementary ideals**: inserting a clasp into two
distinct arcs leaves every elementary ideal unchanged. -/
@[simp]
theorem elementaryIdeal_insertClasp (k : ℕ) :
    (D.insertClasp p q b hqp hqe).elementaryIdeal k = D.elementaryIdeal k := by
  rw [elementaryIdeal_def, elementaryIdeal_def]
  exact fittingIdeal_congr (D.alexanderModuleInsertClaspEquiv p q b hqp hqe) k

end OrientedPDCode

end TauCeti
