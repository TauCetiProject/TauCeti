/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Alexander.Invariance
public import TauCeti.KnotTheory.PDCode.Alexander.ReidemeisterTwo.Clasp
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Two.Basic

/-!
# The Alexander module under the second Reidemeister move between an arc and a circle

The circle-and-arc clasp `TauCeti.OrientedPDCode.insertCircleClasp` pushes a crossing-free
circle across the arc ending at the half-edge `p`, creating two crossings of opposite signs. This
file shows that the result has the same Alexander module (`TauCeti.OrientedPDCode.AlexanderModule`)
as `D.adjoinCircle o`, the diagram with the circle left aside, up to `ℤ[T;T⁻¹]`-linear
equivalence, and therefore the same elementary ideals.

The old crossings keep their coefficients. The two new crossings have explicit coefficients
determined by the directions of the cut arc, the new circle, and the chosen over-strand. The
cut arc enters the first new crossing at slot `0` and leaves the second at slot `3`, while the
circle runs through slots `1` and `3` of the first and `0` and `2` of the second. Its pieces are
the affine combinations `TauCeti.claspValue` of the generator of the cut arc and the generator of
the circle, exactly as in the two-arc clasp of
`TauCeti.KnotTheory.PDCode.Alexander.ReidemeisterTwo.Basic`. Since the same strand is over at
both crossings and the two crossings have opposite signs, the second crossing returns the
generator of the cut arc and closes the circle up (`TauCeti.clasp_relations`).

## Main definitions

* `TauCeti.OrientedPDCode.alexanderModuleInsertCircleClaspEquiv`: the circle-and-arc clasp keeps
  the Alexander module of the diagram with the circle adjoined.

## Main results

* `TauCeti.OrientedPDCode.elementaryIdeal_insertCircleClasp`: the second Reidemeister move
  between an arc and a crossing-free circle keeps every elementary ideal.
* `TauCeti.OrientedPDCode.alexanderGenerator_insertCircleClasp_edgePair`: after the clasp is
  inserted, the two old ends of the cut arc still give the same generator.
* `TauCeti.OrientedPDCode.alexanderWeight_insertCircleClasp_castSucc_last` and
  `TauCeti.OrientedPDCode.alexanderWeight_insertCircleClasp_last`: the coefficients of the two
  new crossings.

## References

* R. H. Crowell and R. H. Fox, *Introduction to Knot Theory*, Graduate Texts in Mathematics 57,
  Springer (1977), Chapters VI–VII (the Alexander module and its crossing weights).
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Graduate Texts in Mathematics 175,
  Springer (1997), Chapters 1 and 6 (Reidemeister moves and the Alexander polynomial).
-/

public section
noncomputable section
open LaurentPolynomial

namespace TauCeti.OrientedPDCode
open PDCode

variable {n : ℕ} (D : OrientedPDCode n) (p : Fin (4 * n)) (o b : Bool)

/-- The old crossings keep their Alexander weights after inserting the circle clasp. -/
@[simp] theorem alexanderWeight_insertCircleClasp_castSucc_castSucc (i : Fin n) (s : Fin 4) :
    (D.insertCircleClasp p o b).alexanderWeight i.castSucc.castSucc s =
      D.alexanderWeight i s := by
  simp [alexanderWeight_def, PDCode.isOver_def, crossingSign_def, crossing_apply]

/-- The four coefficients at the first new crossing, in slot order. -/
@[simp] theorem alexanderWeight_insertCircleClasp_castSucc_last (s : Fin 4) :
    (D.insertCircleClasp p o b).alexanderWeight (Fin.last n).castSucc s =
      ![
        if !b then 1 else T (if !D.orientation p then
          -if (D.orientation p ^^ o) = b then 1 else -1
        else if (D.orientation p ^^ o) = b then 1 else -1),
        if b then 1 else T (if !o then
          -if (D.orientation p ^^ o) = b then 1 else -1
        else if (D.orientation p ^^ o) = b then 1 else -1),
        if !b then 1 else T (if D.orientation p then
          -if (D.orientation p ^^ o) = b then 1 else -1
        else if (D.orientation p ^^ o) = b then 1 else -1),
        if b then 1 else T (if o then
          -if (D.orientation p ^^ o) = b then 1 else -1
        else if (D.orientation p ^^ o) = b then 1 else -1)
      ] s := by
  fin_cases s <;>
    simp [alexanderWeight_def, PDCode.isOver_def, crossingSign_def, crossing_apply,
      orientation_insertCircleClasp_first, insertCircleClasp_overPair_castSucc_last]

/-- The four coefficients at the second new crossing, in slot order. -/
@[simp] theorem alexanderWeight_insertCircleClasp_last (s : Fin 4) :
    (D.insertCircleClasp p o b).alexanderWeight (Fin.last (n + 1)) s =
      ![
        if b then 1 else T (if !o then
          -(-if (D.orientation p ^^ o) = b then 1 else -1)
        else -if (D.orientation p ^^ o) = b then 1 else -1),
        if !b then 1 else T (if !D.orientation p then
          -(-if (D.orientation p ^^ o) = b then 1 else -1)
        else -if (D.orientation p ^^ o) = b then 1 else -1),
        if b then 1 else T (if o then
          -(-if (D.orientation p ^^ o) = b then 1 else -1)
        else -if (D.orientation p ^^ o) = b then 1 else -1),
        if !b then 1 else T (if D.orientation p then
          -(-if (D.orientation p ^^ o) = b then 1 else -1)
        else -if (D.orientation p ^^ o) = b then 1 else -1)
      ] s := by
  fin_cases s <;>
    simp [alexanderWeight_def, PDCode.isOver_def, crossingSign_def, crossing_apply,
      orientation_insertCircleClasp_second, insertCircleClasp_overPair_last] <;>
    cases hD : D.orientation p <;> cases o <;> cases b <;> simp

/-! ### Cancellation of the clasp weights -/

private theorem crossing_insertCircleClasp_castSucc_castSucc (i : Fin n) (s : Fin 4) :
    (D.toPDCode.insertCircleClasp p b).crossing i.castSucc.castSucc s =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl (D.crossing i s)))) := by
  simp [crossingSlotEquiv_succ_castSucc]

private theorem crossing_insertCircleClasp_castSucc_last (s : Fin 4) :
    (D.toPDCode.insertCircleClasp p b).crossing (Fin.last n).castSucc s =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr s))) := by
  simp [crossingSlotEquiv_succ_castSucc, crossingSlotEquiv_succ_last]

private theorem crossing_insertCircleClasp_last (s : Fin 4) :
    (D.toPDCode.insertCircleClasp p b).crossing (Fin.last (n + 1)) s =
      halfEdgeSuccEquiv (n + 1) (.inr s) := by
  simp [crossingSlotEquiv_succ_last]

/-- Along the circle, the weight of slot `0` of the second new crossing is inverse to the weight
of slot `1` of the first. -/
private theorem alexanderWeight_insertCircleClasp_last_zero_mul :
    (D.insertCircleClasp p o b).alexanderWeight (Fin.last (n + 1)) 0 *
      (D.insertCircleClasp p o b).alexanderWeight (Fin.last n).castSucc 1 = 1 := by
  rw [alexanderWeight_insertCircleClasp_last, alexanderWeight_insertCircleClasp_castSucc_last]
  cases D.orientation p <;> cases o <;> cases b <;>
    simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
      Bool.xor_true, Bool.xor_false, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_one, neg_neg, ← T_add, neg_add_cancel, add_neg_cancel, T_zero]

/-- Along the cut arc, the weight of slot `1` of the second new crossing is inverse to the weight
of slot `0` of the first. -/
private theorem alexanderWeight_insertCircleClasp_last_one_mul :
    (D.insertCircleClasp p o b).alexanderWeight (Fin.last (n + 1)) 1 *
      (D.insertCircleClasp p o b).alexanderWeight (Fin.last n).castSucc 0 = 1 := by
  rw [alexanderWeight_insertCircleClasp_last, alexanderWeight_insertCircleClasp_castSucc_last]
  cases D.orientation p <;> cases o <;> cases b <;>
    simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
      Bool.xor_true, Bool.xor_false, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_one, neg_neg, ← T_add, neg_add_cancel, add_neg_cancel, T_zero]

/-- The same strand is over at both new crossings: the cut arc (slots `0` of the first and `1` of
the second) or the circle (slots `1` of the first and `0` of the second). -/
private theorem alexanderWeight_insertCircleClasp_over :
    ((D.insertCircleClasp p o b).alexanderWeight (Fin.last n).castSucc 0 = 1 ∧
        (D.insertCircleClasp p o b).alexanderWeight (Fin.last (n + 1)) 1 = 1) ∨
      ((D.insertCircleClasp p o b).alexanderWeight (Fin.last n).castSucc 1 = 1 ∧
        (D.insertCircleClasp p o b).alexanderWeight (Fin.last (n + 1)) 0 = 1) := by
  cases b <;> simp

/-! ### The generators of the cut arc -/

/-- In the code with the clasp, the relations of the two new crossings identify slots `2` and `3`
of the second crossing with slots `1` and `0` of the first. -/
private theorem alexanderGenerator_insertCircleClasp_inr_two_three :
    (D.insertCircleClasp p o b).alexanderGenerator (.inl (halfEdgeSuccEquiv (n + 1) (.inr 2))) =
        (D.insertCircleClasp p o b).alexanderGenerator
          (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 1))))) ∧
      (D.insertCircleClasp p o b).alexanderGenerator
          (.inl (halfEdgeSuccEquiv (n + 1) (.inr 3))) =
        (D.insertCircleClasp p o b).alexanderGenerator
          (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 0))))) := by
  set D' := D.insertCircleClasp p o b
  have rA₀ := D'.alexanderGenerator_crossing_add_two (Fin.last n).castSucc 0
  have rA₁ := D'.alexanderGenerator_crossing_add_two (Fin.last n).castSucc 1
  have rB₀ := D'.alexanderGenerator_crossing_add_two (Fin.last (n + 1)) 0
  have rB₁ := D'.alexanderGenerator_crossing_add_two (Fin.last (n + 1)) 1
  have arc₀ := D'.alexanderGenerator_edgePair (halfEdgeSuccEquiv (n + 1) (.inr 0))
  have arc₁ := D'.alexanderGenerator_edgePair (halfEdgeSuccEquiv (n + 1) (.inr 1))
  simp only [D', crossing_insertCircleClasp_castSucc_last, crossing_insertCircleClasp_last,
    toPDCode_insertCircleClasp, insertCircleClasp_edgePair_second, Fin.isValue, Fin.reduceAdd,
    zero_add, Matrix.cons_val_zero, Matrix.cons_val_one] at rA₀ rA₁ rB₀ rB₁ arc₀ arc₁
  rw [← arc₀, ← arc₁] at rB₀
  rw [← arc₁] at rB₁
  obtain ⟨h₀, h₁⟩ := clasp_relations
    (alexanderWeight_insertCircleClasp_last_zero_mul D p o b)
    (alexanderWeight_insertCircleClasp_last_one_mul D p o b)
    (alexanderWeight_insertCircleClasp_over D p o b) rA₀ rA₁
  refine ⟨rB₀.trans h₀, ?_⟩
  rw [rB₁, rB₀, h₀, h₁]

/-- After the clasp is inserted, the two old ends of the cut arc still give the same generator of
the Alexander module. -/
@[simp]
theorem alexanderGenerator_insertCircleClasp_edgePair :
    (D.insertCircleClasp p o b).alexanderGenerator
        (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl (D.edgePair.val p)))))) =
      (D.insertCircleClasp p o b).alexanderGenerator
        (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl p))))) := by
  have hend := (D.insertCircleClasp p o b).alexanderGenerator_edgePair
    (halfEdgeSuccEquiv (n + 1) (.inr 3))
  have hstart := (D.insertCircleClasp p o b).alexanderGenerator_edgePair
    (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 0))))
  simp only [toPDCode_insertCircleClasp, insertCircleClasp_edgePair_second,
    insertCircleClasp_edgePair_first, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val]
    at hend hstart
  rw [hend, hstart, (alexanderGenerator_insertCircleClasp_inr_two_three D p o b).2]

/-! ### The equivalence of Alexander modules -/

/-- The generator of the circle adjoined to `D`. -/
private def newCircleGenerator : (D.adjoinCircle o).AlexanderModule :=
  (D.adjoinCircle o).alexanderGenerator
    (.inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount)))

/-- The images of the slots of the two new crossings: the generators of the cut arc and of the
circle at slots `0` and `1` of the first crossing, and the affine combinations the clasp relations
prescribe elsewhere. -/
private def circleClaspValue : Fin 2 → Fin 4 → (D.adjoinCircle o).AlexanderModule :=
  claspValue ((D.insertCircleClasp p o b).alexanderWeight (Fin.last n).castSucc 0)
    ((D.insertCircleClasp p o b).alexanderWeight (Fin.last n).castSucc 1)
    ((D.adjoinCircle o).alexanderGenerator (.inl p)) (newCircleGenerator D o)

/-- The clasp arcs join slots `0`, `1`, `2`, `3` of the second new crossing to slots `3`, `2`,
`1`, `0` of the first. -/
private theorem circleClaspValue_one :
    circleClaspValue D p o b 1 =
      ![circleClaspValue D p o b 0 3, circleClaspValue D p o b 0 2, circleClaspValue D p o b 0 1,
        circleClaspValue D p o b 0 0] := by
  funext s
  fin_cases s <;> simp [circleClaspValue, -alexanderWeight_insertCircleClasp_castSucc_last]

/-- The images of the generators of the code with the clasp in the Alexander module of the code
with the circle adjoined. -/
private def insertCircleClaspValue :
    Fin (4 * (n + 2)) ⊕ Fin (D.insertCircleClasp p o b).crossinglessComponentCount →
      (D.adjoinCircle o).AlexanderModule :=
  Sum.elim
    (fun x ↦ Sum.elim
      (fun y ↦ Sum.elim (fun z ↦ (D.adjoinCircle o).alexanderGenerator (.inl z))
        (circleClaspValue D p o b 0) ((halfEdgeSuccEquiv n).symm y))
      (circleClaspValue D p o b 1) ((halfEdgeSuccEquiv (n + 1)).symm x))
    fun j ↦ (D.adjoinCircle o).alexanderGenerator
      (.inr (Fin.cast (by simp)
        (Fin.castSucc (Fin.cast (m := D.crossinglessComponentCount) (by simp) j))))

/-- The map from the Alexander module of the code with the clasp, sending the old half-edges to
themselves and the new ones to `circleClaspValue`. -/
private def insertCircleClaspHom :
    (D.insertCircleClasp p o b).AlexanderModule →ₗ[ℤ[T;T⁻¹]] (D.adjoinCircle o).AlexanderModule :=
  (D.insertCircleClasp p o b).alexanderLift (insertCircleClaspValue D p o b)
    (fun x ↦ by
      have hp := (D.adjoinCircle o).alexanderGenerator_edgePair p
      simp only [toPDCode_adjoinCircle, PDCode.adjoinCircle_edgePair] at hp
      obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv (n + 1)).surjective x
      · obtain ⟨z | s, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
        · by_cases hzp : z = p
          · subst hzp
            simp [insertCircleClaspValue, circleClaspValue]
          by_cases hze : z = D.edgePair.val p
          · subst hze
            simp [insertCircleClaspValue, circleClaspValue, hp]
          simpa [insertCircleClaspValue, D.toPDCode.insertCircleClasp_edgePair_old p b hzp hze]
            using (D.adjoinCircle o).alexanderGenerator_edgePair z
        · fin_cases s <;> simp [insertCircleClaspValue, circleClaspValue]
      · fin_cases s <;> simp [insertCircleClaspValue, circleClaspValue, hp])
    (fun i ↦ by
      induction i using Fin.lastCases with
      | last =>
        obtain ⟨h₀, h₁⟩ := claspValue_relations
          (alexanderWeight_insertCircleClasp_last_zero_mul D p o b)
          (alexanderWeight_insertCircleClasp_last_one_mul D p o b)
          (alexanderWeight_insertCircleClasp_over D p o b)
          ((D.adjoinCircle o).alexanderGenerator (.inl p)) (newCircleGenerator D o)
        refine (D.insertCircleClasp p o b).apply_crossing_add_two_of_zero_of_one
          (fun x ↦ insertCircleClaspValue D p o b (.inl x)) _ ?_ ?_
        · simpa [insertCircleClaspValue, circleClaspValue, crossing_insertCircleClasp_last]
            using h₀
        · simpa [insertCircleClaspValue, circleClaspValue, crossing_insertCircleClasp_last]
            using h₁
      | cast i =>
        induction i using Fin.lastCases with
        | last =>
          refine (D.insertCircleClasp p o b).apply_crossing_add_two_of_zero_of_one
            (fun x ↦ insertCircleClaspValue D p o b (.inl x)) _ ?_ ?_ <;>
            simp [insertCircleClaspValue, circleClaspValue]
        | cast i =>
          intro slot
          simpa [insertCircleClaspValue, crossing_insertCircleClasp_castSucc_castSucc] using
            (D.adjoinCircle o).alexanderGenerator_crossing_add_two i slot)

private theorem insertCircleClaspHom_alexanderGenerator
    (g : Fin (4 * (n + 2)) ⊕ Fin (D.insertCircleClasp p o b).crossinglessComponentCount) :
    insertCircleClaspHom D p o b ((D.insertCircleClasp p o b).alexanderGenerator g) =
      insertCircleClaspValue D p o b g :=
  alexanderLift_alexanderGenerator _ _ _ _ _

/-- The images of the generators of the code with the circle adjoined: the old half-edges and
crossing-free components go to themselves, and the circle to slot `1` of the first new crossing. -/
private def insertCircleClaspInvValue :
    Fin (4 * n) ⊕ Fin (D.adjoinCircle o).crossinglessComponentCount →
      (D.insertCircleClasp p o b).AlexanderModule :=
  Sum.elim (fun y ↦ (D.insertCircleClasp p o b).alexanderGenerator
      (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl y))))))
    fun j ↦ Fin.lastCases (motive := fun _ ↦ (D.insertCircleClasp p o b).AlexanderModule)
      ((D.insertCircleClasp p o b).alexanderGenerator
        (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 1))))))
      (fun j ↦ (D.insertCircleClasp p o b).alexanderGenerator (.inr (Fin.cast (by simp) j)))
      (Fin.cast (m := D.crossinglessComponentCount + 1) (by simp) j)

/-- The map to the Alexander module of the code with the clasp, sending the circle to slot `1` of
the first new crossing and every other generator to itself. -/
private def insertCircleClaspInvHom :
    (D.adjoinCircle o).AlexanderModule →ₗ[ℤ[T;T⁻¹]] (D.insertCircleClasp p o b).AlexanderModule :=
  (D.adjoinCircle o).alexanderLift (insertCircleClaspInvValue D p o b)
    (fun y ↦ by
      simp only [insertCircleClaspInvValue, toPDCode_adjoinCircle, PDCode.adjoinCircle_edgePair,
        Sum.elim_inl]
      by_cases hyp : y = p
      · subst hyp
        exact alexanderGenerator_insertCircleClasp_edgePair D y o b
      by_cases hye : y = D.edgePair.val p
      · subst hye
        rw [PerfectMatching.apply_apply]
        exact (alexanderGenerator_insertCircleClasp_edgePair D p o b).symm
      simpa [D.toPDCode.insertCircleClasp_edgePair_old p b hyp hye] using
        (D.insertCircleClasp p o b).alexanderGenerator_edgePair
          (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl y)))))
    (fun i slot ↦ by
      simpa [insertCircleClaspInvValue, crossing_insertCircleClasp_castSucc_castSucc] using
        (D.insertCircleClasp p o b).alexanderGenerator_crossing_add_two i.castSucc.castSucc slot)

private theorem insertCircleClaspInvHom_alexanderGenerator
    (g : Fin (4 * n) ⊕ Fin (D.adjoinCircle o).crossinglessComponentCount) :
    insertCircleClaspInvHom D p o b ((D.adjoinCircle o).alexanderGenerator g) =
      insertCircleClaspInvValue D p o b g :=
  alexanderLift_alexanderGenerator _ _ _ _ _

/-- The images of the slots of the first new crossing are sent back to these slots. -/
private theorem insertCircleClaspInvHom_circleClaspValue_zero (s : Fin 4) :
    insertCircleClaspInvHom D p o b (circleClaspValue D p o b 0 s) =
      (D.insertCircleClasp p o b).alexanderGenerator
        (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr s))))) := by
  set D' := D.insertCircleClasp p o b
  have rA₀ := D'.alexanderGenerator_crossing_add_two (Fin.last n).castSucc 0
  have rA₁ := D'.alexanderGenerator_crossing_add_two (Fin.last n).castSucc 1
  have arc₀ := D'.alexanderGenerator_edgePair
    (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 0))))
  simp only [D', crossing_insertCircleClasp_castSucc_last, toPDCode_insertCircleClasp,
    insertCircleClasp_edgePair_first, Fin.isValue, Fin.reduceAdd, zero_add,
    Matrix.cons_val_zero] at rA₀ rA₁ arc₀
  fin_cases s <;>
    simp [-alexanderWeight_insertCircleClasp_castSucc_last, circleClaspValue, newCircleGenerator,
      insertCircleClaspInvHom_alexanderGenerator, insertCircleClaspInvValue, D', arc₀, rA₀, rA₁]

/-- **The second Reidemeister move between an arc and a circle keeps the Alexander module**:
pushing a crossing-free circle across an arc gives a code whose Alexander module is
`ℤ[T;T⁻¹]`-linearly equivalent to that of `D` with the circle adjoined. The inverse sends the
generator of the circle to slot `1` of the first new crossing, and every other generator to the
generator of the same half-edge or component. -/
def alexanderModuleInsertCircleClaspEquiv :
    (D.insertCircleClasp p o b).AlexanderModule ≃ₗ[ℤ[T;T⁻¹]] (D.adjoinCircle o).AlexanderModule :=
  LinearEquiv.ofLinearMap (insertCircleClaspHom D p o b) (insertCircleClaspInvHom D p o b)
    (by
      ext (y | j)
      · simp [insertCircleClaspHom_alexanderGenerator, insertCircleClaspInvHom_alexanderGenerator,
          insertCircleClaspValue, insertCircleClaspInvValue]
      · obtain ⟨j, rfl⟩ := (finCongr (by simp : (D.adjoinCircle o).crossinglessComponentCount =
          D.crossinglessComponentCount + 1)).symm.surjective j
        induction j using Fin.lastCases <;>
          simp [insertCircleClaspHom_alexanderGenerator, insertCircleClaspInvHom_alexanderGenerator,
            insertCircleClaspValue, insertCircleClaspInvValue, circleClaspValue,
            newCircleGenerator])
    (by
      ext (x | j)
      · obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv (n + 1)).surjective x
        · obtain ⟨z | s, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
          · simp [insertCircleClaspHom_alexanderGenerator,
              insertCircleClaspInvHom_alexanderGenerator, insertCircleClaspValue,
              insertCircleClaspInvValue]
          · simp [insertCircleClaspHom_alexanderGenerator, insertCircleClaspValue,
              insertCircleClaspInvHom_circleClaspValue_zero]
        · -- The slots of the second crossing take the values of the slots of the first to which
          -- the clasp arcs join them, and slot `3` is identified with slot `0` of the first.
          have h23 := alexanderGenerator_insertCircleClasp_inr_two_three D p o b
          have arc₀ := (D.insertCircleClasp p o b).alexanderGenerator_edgePair
            (halfEdgeSuccEquiv (n + 1) (.inr 0))
          have arc₁ := (D.insertCircleClasp p o b).alexanderGenerator_edgePair
            (halfEdgeSuccEquiv (n + 1) (.inr 1))
          simp only [toPDCode_insertCircleClasp, insertCircleClasp_edgePair_second, Fin.isValue,
            Matrix.cons_val] at arc₀ arc₁
          fin_cases s <;>
            simp [insertCircleClaspHom_alexanderGenerator, insertCircleClaspValue,
              circleClaspValue_one, insertCircleClaspInvHom_circleClaspValue_zero, arc₀, arc₁, h23]
      · simp [insertCircleClaspHom_alexanderGenerator, insertCircleClaspInvHom_alexanderGenerator,
          insertCircleClaspValue, insertCircleClaspInvValue])

/-- The equivalence sends the generator of an old half-edge to the generator of the same
half-edge. -/
@[simp]
theorem alexanderModuleInsertCircleClaspEquiv_apply_alexanderGenerator_inl_inl (x : Fin (4 * n)) :
    D.alexanderModuleInsertCircleClaspEquiv p o b
        ((D.insertCircleClasp p o b).alexanderGenerator
          (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x)))))) =
      (D.adjoinCircle o).alexanderGenerator (.inl x) := by
  simp [alexanderModuleInsertCircleClaspEquiv, insertCircleClaspHom_alexanderGenerator,
    insertCircleClaspValue]

/-- The equivalence sends the generators of the slots of the first new crossing to the generators
of the cut arc and of the circle at slots `0` and `1`, and at slots `2` and `3` to the combinations
of these that the relations at slots `0` and `1` of that crossing prescribe. -/
@[simp]
theorem alexanderModuleInsertCircleClaspEquiv_apply_alexanderGenerator_inl_inl_inr (s : Fin 4) :
    D.alexanderModuleInsertCircleClaspEquiv p o b
        ((D.insertCircleClasp p o b).alexanderGenerator
          (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr s)))))) =
      claspValue ((D.insertCircleClasp p o b).alexanderWeight (Fin.last n).castSucc 0)
        ((D.insertCircleClasp p o b).alexanderWeight (Fin.last n).castSucc 1)
        ((D.adjoinCircle o).alexanderGenerator (.inl p))
        ((D.adjoinCircle o).alexanderGenerator
          (.inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount)))) 0 s := by
  simp [alexanderModuleInsertCircleClaspEquiv, insertCircleClaspHom_alexanderGenerator,
    insertCircleClaspValue, circleClaspValue, newCircleGenerator]

/-- The equivalence sends the generators of the slots of the second new crossing to the images of
the slots of the first to which the clasp arcs join them: slots `0`, `1`, `2` and `3` go to the
images of slots `3`, `2`, `1` and `0` of the first new crossing. -/
@[simp]
theorem alexanderModuleInsertCircleClaspEquiv_apply_alexanderGenerator_inl_inr (s : Fin 4) :
    D.alexanderModuleInsertCircleClaspEquiv p o b
        ((D.insertCircleClasp p o b).alexanderGenerator
          (.inl (halfEdgeSuccEquiv (n + 1) (.inr s)))) =
      claspValue ((D.insertCircleClasp p o b).alexanderWeight (Fin.last n).castSucc 0)
        ((D.insertCircleClasp p o b).alexanderWeight (Fin.last n).castSucc 1)
        ((D.adjoinCircle o).alexanderGenerator (.inl p))
        ((D.adjoinCircle o).alexanderGenerator
          (.inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount)))) 1 s := by
  simp [alexanderModuleInsertCircleClaspEquiv, insertCircleClaspHom_alexanderGenerator,
    insertCircleClaspValue, circleClaspValue, newCircleGenerator]

/-- The equivalence sends the generator of a crossing-free component to the generator of the same
component. -/
@[simp]
theorem alexanderModuleInsertCircleClaspEquiv_apply_alexanderGenerator_inr
    (j : Fin (D.insertCircleClasp p o b).crossinglessComponentCount) :
    D.alexanderModuleInsertCircleClaspEquiv p o b
        ((D.insertCircleClasp p o b).alexanderGenerator (.inr j)) =
      (D.adjoinCircle o).alexanderGenerator
        (.inr (Fin.cast (by simp)
          (Fin.castSucc (Fin.cast (m := D.crossinglessComponentCount) (by simp) j)))) := by
  simp [alexanderModuleInsertCircleClaspEquiv, insertCircleClaspHom_alexanderGenerator,
    insertCircleClaspValue]

/-- The inverse equivalence sends the generator of the circle to slot `1` of the first new
crossing, and every other generator to the generator of the same half-edge or component. -/
@[simp]
theorem alexanderModuleInsertCircleClaspEquiv_symm_apply_alexanderGenerator
    (g : Fin (4 * n) ⊕ Fin (D.adjoinCircle o).crossinglessComponentCount) :
    (D.alexanderModuleInsertCircleClaspEquiv p o b).symm ((D.adjoinCircle o).alexanderGenerator g) =
      Sum.elim (fun y ↦ (D.insertCircleClasp p o b).alexanderGenerator
          (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl y))))))
        (fun j ↦ Fin.lastCases (motive := fun _ ↦ (D.insertCircleClasp p o b).AlexanderModule)
          ((D.insertCircleClasp p o b).alexanderGenerator
            (.inl (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 1))))))
          (fun j ↦ (D.insertCircleClasp p o b).alexanderGenerator (.inr (Fin.cast (by simp) j)))
          (Fin.cast (m := D.crossinglessComponentCount + 1) (by simp) j)) g :=
  insertCircleClaspInvHom_alexanderGenerator D p o b g

/-- **The second Reidemeister move between an arc and a circle keeps the elementary ideals**:
pushing a crossing-free circle across an arc leaves every elementary ideal of `D` with the circle
adjoined unchanged. -/
@[simp]
theorem elementaryIdeal_insertCircleClasp (k : ℕ) :
    (D.insertCircleClasp p o b).elementaryIdeal k = (D.adjoinCircle o).elementaryIdeal k := by
  rw [elementaryIdeal_def, elementaryIdeal_def]
  exact fittingIdeal_congr (D.alexanderModuleInsertCircleClaspEquiv p o b) k

end TauCeti.OrientedPDCode
