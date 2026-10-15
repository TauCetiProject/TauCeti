/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Alexander.Invariance
public import TauCeti.KnotTheory.PDCode.Alexander.DisjointUnion
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Two.Circles
public import TauCeti.KnotTheory.PDCode.Alexander.ReidemeisterTwo.Clasp

/-!
# Alexander invariance of the second Reidemeister move on two circles

Replacing two crossing-free circles by a cancelling clasp preserves the Alexander module,
and hence every elementary ideal, in any surrounding oriented diagram. The equivalence
identifies the old generators and sends slots `0` and `1` of the first clasp crossing to the
two new circle generators; its inverse reverses this correspondence. The first crossing
relations determine its remaining slots, and arc matching determines the second crossing slots.
Both choices of over-component and all component orientations are allowed.

The construction uses the presentation and lifting API of
`TauCeti.OrientedPDCode.alexanderLift`, following the same generator-elimination method as
`TauCeti.OrientedPDCode.alexanderModuleAdjoinKinkEquiv`.

## Main definitions

* `TauCeti.OrientedPDCode.alexanderModuleAdjoinTwoCircleClaspEquiv`: the equivalence between
  the Alexander modules of the clasped diagram and the diagram with two additional circles.

## Main results

* `TauCeti.OrientedPDCode.elementaryIdeal_adjoinTwoCircleClasp`: invariance of every elementary
  ideal under the two-circle second Reidemeister move.
* `TauCeti.OrientedPDCode.alexanderWeight_twoCircleClasp`: explicit clasp weights.
* `alexanderModuleAdjoinTwoCircleClaspEquiv_apply_alexanderGenerator_inl_inl`,
  `alexanderModuleAdjoinTwoCircleClaspEquiv_apply_alexanderGenerator_inl_inr`,
  `alexanderModuleAdjoinTwoCircleClaspEquiv_apply_alexanderGenerator_inr`,
  and `alexanderModuleAdjoinTwoCircleClaspEquiv_symm_apply_alexanderGenerator`:
  generator formulas in both directions.

## References

* R. H. Crowell, R. H. Fox, *Introduction to Knot Theory*, GTM 57, Chapters VI–VII.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, GTM 175, Chapters 1 and 6.
-/

public section

noncomputable section

namespace TauCeti.OrientedPDCode

open PDCode LaurentPolynomial

variable (o₁ o₂ b : Bool)

/-- The explicit weights of the closed clasp. The second crossing reverses the slot order
and the crossing sign, so its under-strand weights invert those of the first.
The over-strand has weight `1`; the under-strand weight is the meridian `t^{±1}` of the
over-component, oriented by `o₂` when `b` holds and by `o₁` otherwise. -/
@[simp]
theorem alexanderWeight_twoCircleClasp (i : Fin 2) (s : Fin 4) :
    (twoCircleClasp o₁ o₂ b).alexanderWeight i s =
      (if i = 0 then
        if b then ![T (if o₂ then -1 else 1), 1, T (if o₂ then 1 else -1), 1]
        else ![1, T (if o₁ then 1 else -1), 1, T (if o₁ then -1 else 1)]
      else
        if b then ![1, T (if o₂ then 1 else -1), 1, T (if o₂ then -1 else 1)]
        else ![T (if o₁ then -1 else 1), 1, T (if o₁ then 1 else -1), 1]) s := by
  fin_cases i
  · simp only [Fin.zero_eta]
    simp only [alexanderWeight_def, PDCode.isOver_def, crossingSign_def, crossing_apply,
      toPDCode_twoCircleClasp, PDCode.twoCircleClasp_halfEdge, Equiv.Perm.one_apply,
      PDCode.twoCircleClasp_overPair, orientation_twoCircleClasp]
    cases o₁ <;> cases o₂ <;> cases b <;> fin_cases s <;> simp
  · simp only [Fin.mk_one]
    rw [alexanderWeight_def, crossingSign_twoCircleClasp_one]
    simp only [PDCode.isOver_def, crossingSign_def, crossing_apply,
      toPDCode_twoCircleClasp, PDCode.twoCircleClasp_halfEdge, Equiv.Perm.one_apply,
      PDCode.twoCircleClasp_overPair, orientation_twoCircleClasp]
    cases o₁ <;> cases o₂ <;> cases b <;> fin_cases s <;> simp

/-- The second crossing's slot `0` weight inverts the first crossing's slot `1` weight. -/
private theorem alexanderWeight_twoCircleClasp_one_zero_mul :
    (twoCircleClasp o₁ o₂ b).alexanderWeight 1 0 *
      (twoCircleClasp o₁ o₂ b).alexanderWeight 0 1 = 1 := by
  have h := (twoCircleClasp o₁ o₂ b).alexanderWeight_add_two_mul_alexanderWeight 0 1
  convert h using 1
  cases b <;>
    simp only [alexanderWeight_twoCircleClasp, Fin.reduceAdd, Fin.reduceEq,
      Bool.false_eq_true, ↓reduceIte, Matrix.cons_val]

/-- The second crossing's slot `1` weight inverts the first crossing's slot `0` weight. -/
private theorem alexanderWeight_twoCircleClasp_one_one_mul :
    (twoCircleClasp o₁ o₂ b).alexanderWeight 1 1 *
      (twoCircleClasp o₁ o₂ b).alexanderWeight 0 0 = 1 := by
  have h := (twoCircleClasp o₁ o₂ b).alexanderWeight_add_two_mul_alexanderWeight 0 0
  convert h using 1
  cases b <;>
    simp only [alexanderWeight_twoCircleClasp, zero_add, Fin.reduceEq,
      Bool.false_eq_true, ↓reduceIte, Matrix.cons_val]

/-- The same component is over at both crossings. -/
private theorem alexanderWeight_twoCircleClasp_over :
    ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 0 = 1 ∧
        (twoCircleClasp o₁ o₂ b).alexanderWeight 1 1 = 1) ∨
      ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 1 = 1 ∧
        (twoCircleClasp o₁ o₂ b).alexanderWeight 1 0 = 1) := by
  cases b <;> simp

private theorem claspValue_crossing_add_two {M : Type*} [AddCommGroup M] [Module ℤ[T;T⁻¹] M]
    (x y : M) (i : Fin 2) (s : Fin 4) :
    claspValue ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 0)
      ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 1) x y i (s + 2) =
      (twoCircleClasp o₁ o₂ b).alexanderWeight i s •
        claspValue ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 0)
          ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 1) x y i s +
      (1 - (twoCircleClasp o₁ o₂ b).alexanderWeight i s) •
        claspValue ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 0)
          ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 1) x y i (s + 1) := by
  have h := (twoCircleClasp o₁ o₂ b).apply_crossing_add_two_of_zero_of_one
    (fun z ↦ let p := (crossingSlotEquiv 2).symm z
      claspValue ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 0)
        ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 1) x y p.1 p.2) i
  simp only [crossing_apply, toPDCode_twoCircleClasp, PDCode.twoCircleClasp_halfEdge,
    Equiv.Perm.one_apply, Equiv.symm_apply_apply] at h
  fin_cases i
  · apply h <;> simp
  · obtain ⟨h₀, h₁⟩ := claspValue_relations
      (alexanderWeight_twoCircleClasp_one_zero_mul o₁ o₂ b)
      (alexanderWeight_twoCircleClasp_one_one_mul o₁ o₂ b)
      (alexanderWeight_twoCircleClasp_over o₁ o₂ b) x y
    exact h h₀ h₁ s

variable {n : ℕ} (D : OrientedPDCode n)

/-- Old crossings retain their Alexander weights after clasp adjunction. -/
@[simp]
theorem alexanderWeight_adjoinTwoCircleClasp_castAdd (i : Fin n) (s : Fin 4) :
    (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderWeight (Fin.castAdd 2 i) s =
      D.alexanderWeight i s := by
  simp [adjoinTwoCircleClasp_def]

/-- The new crossings have the weights of the closed two-circle clasp. -/
@[simp]
theorem alexanderWeight_adjoinTwoCircleClasp_natAdd (i : Fin 2) (s : Fin 4) :
    (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderWeight (Fin.natAdd n i) s =
      (twoCircleClasp o₁ o₂ b).alexanderWeight i s := by
  simp [adjoinTwoCircleClasp_def]

/-- The generator of the `j`-th newly adjoined circle:
`0` has orientation `o₁`, `1` has `o₂`. -/
private def circleGenerator (j : Fin 2) :
    ((D.adjoinCircle o₁).adjoinCircle o₂).AlexanderModule :=
  ((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator
    (.inr (Fin.cast (by simp) (Fin.natAdd D.crossinglessComponentCount j)))

/-- The images of old generators and clasp slots in the module with the two new circles. -/
private def adjoinTwoCircleClaspValue :
    Fin (4 * (n + 2)) ⊕ Fin (D.adjoinTwoCircleClasp o₁ o₂ b).crossinglessComponentCount →
      ((D.adjoinCircle o₁).adjoinCircle o₂).AlexanderModule :=
  Sum.elim
    (fun z ↦ Sum.elim
      (fun h ↦ ((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator (.inl h))
      (fun h ↦ let p := (crossingSlotEquiv 2).symm h
        claspValue ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 0)
          ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 1) (circleGenerator o₁ o₂ D 0)
          (circleGenerator o₁ o₂ D 1) p.1 p.2)
      ((disjointUnionHalfEdgeEquiv n 2).symm z))
    (fun j ↦ ((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator
      (.inr (Fin.cast (by simp)
        (Fin.castAdd 2 (Fin.cast (m := D.crossinglessComponentCount) (by simp) j)))))

/-- The map from the clasp module to the circle module induced by the prescribed slot values. -/
private def adjoinTwoCircleClaspHom :
    (D.adjoinTwoCircleClasp o₁ o₂ b).AlexanderModule →ₗ[ℤ[T;T⁻¹]]
      ((D.adjoinCircle o₁).adjoinCircle o₂).AlexanderModule :=
  (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderLift (adjoinTwoCircleClaspValue o₁ o₂ b D)
    (fun z ↦ by
      obtain ⟨h | h, rfl⟩ := (disjointUnionHalfEdgeEquiv n 2).surjective z
      · simpa [adjoinTwoCircleClaspValue, adjoinTwoCircleClasp_def, disjointUnion_edgePair_val]
          using
          ((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator_edgePair h
      · obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv 2).surjective h
        simpa [adjoinTwoCircleClaspValue, adjoinTwoCircleClasp_def, disjointUnion_edgePair_val,
          Equiv.permCongr_apply] using
          claspValue_rev_rev ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 0)
            ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 1)
            (circleGenerator o₁ o₂ D 0) (circleGenerator o₁ o₂ D 1) i s)
    (fun i s ↦ by
      induction i using Fin.addCases with
      | left i =>
        rw [alexanderWeight_adjoinTwoCircleClasp_castAdd]
        simp only [adjoinTwoCircleClasp_def, toPDCode_disjointUnion,
          crossing_disjointUnion_castAdd,
          adjoinTwoCircleClaspValue, Sum.elim_inl, Equiv.symm_apply_apply]
        simpa using
          ((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator_crossing_add_two i s
      | right i =>
        rw [alexanderWeight_adjoinTwoCircleClasp_natAdd]
        simp only [adjoinTwoCircleClasp_def, toPDCode_disjointUnion,
          crossing_disjointUnion_natAdd,
          adjoinTwoCircleClaspValue, Sum.elim_inl, Equiv.symm_apply_apply, Sum.elim_inr]
        simpa only [crossing_apply, toPDCode_twoCircleClasp,
          PDCode.twoCircleClasp_halfEdge, Equiv.Perm.one_apply, Equiv.symm_apply_apply] using
          claspValue_crossing_add_two o₁ o₂ b
            (circleGenerator o₁ o₂ D 0) (circleGenerator o₁ o₂ D 1) i s)

private theorem adjoinTwoCircleClaspHom_alexanderGenerator (g) :
    adjoinTwoCircleClaspHom o₁ o₂ b D ((D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator g) =
      adjoinTwoCircleClaspValue o₁ o₂ b D g :=
  alexanderLift_alexanderGenerator _ _ _ _ _

/-- The generator of slot `s` of new crossing `i`, with `0` the first clasp crossing. -/
private def claspGenerator (i : Fin 2) (s : Fin 4) :
    (D.adjoinTwoCircleClasp o₁ o₂ b).AlexanderModule :=
  (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator
    (.inl (disjointUnionHalfEdgeEquiv n 2 (.inr (crossingSlotEquiv 2 (i, s)))))

/-- The inverse images of old generators and the two newly adjoined circle generators. -/
private def adjoinTwoCircleClaspInvValue :
    Fin (4 * n) ⊕ Fin ((D.adjoinCircle o₁).adjoinCircle o₂).crossinglessComponentCount →
      (D.adjoinTwoCircleClasp o₁ o₂ b).AlexanderModule :=
  Sum.elim
    (fun h ↦ (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator
      (.inl (disjointUnionHalfEdgeEquiv n 2 (.inl h))))
    (fun j ↦ Fin.addCases
      (fun k ↦ (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator (.inr (Fin.cast (by simp) k)))
      (fun k ↦ claspGenerator o₁ o₂ b D 0 (Fin.castAdd 2 k))
      (Fin.cast (m := D.crossinglessComponentCount + 2) (by simp) j))

/-- The map from the circle module sending the new circles
to slots `0`, `1` of crossing `0`. -/
private def adjoinTwoCircleClaspInvHom :
    ((D.adjoinCircle o₁).adjoinCircle o₂).AlexanderModule →ₗ[ℤ[T;T⁻¹]]
      (D.adjoinTwoCircleClasp o₁ o₂ b).AlexanderModule :=
  ((D.adjoinCircle o₁).adjoinCircle o₂).alexanderLift (adjoinTwoCircleClaspInvValue o₁ o₂ b D)
    (fun h ↦ by
      simpa [adjoinTwoCircleClaspInvValue, adjoinTwoCircleClasp_def, disjointUnion_edgePair_val,
        Equiv.permCongr_apply] using
        (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator_edgePair
          (disjointUnionHalfEdgeEquiv n 2 (.inl h)))
    (fun i s ↦ by
      have h := (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator_crossing_add_two
        (Fin.castAdd 2 i) s
      rw [alexanderWeight_adjoinTwoCircleClasp_castAdd] at h
      simp only [adjoinTwoCircleClasp_def, toPDCode_disjointUnion,
        crossing_disjointUnion_castAdd] at h
      simpa [adjoinTwoCircleClaspInvValue] using h)

private theorem adjoinTwoCircleClaspInvHom_alexanderGenerator (g) :
    adjoinTwoCircleClaspInvHom o₁ o₂ b D (((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator
      g) =
      adjoinTwoCircleClaspInvValue o₁ o₂ b D g :=
  alexanderLift_alexanderGenerator _ _ _ _ _

private theorem claspGenerator_arc (i : Fin 2) (s : Fin 4) :
    claspGenerator o₁ o₂ b D (Fin.rev i) (Fin.rev s) = claspGenerator o₁ o₂ b D i s := by
  simpa [claspGenerator, adjoinTwoCircleClasp_def, disjointUnion_edgePair_val,
    Equiv.permCongr_apply] using
    (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator_edgePair
      (disjointUnionHalfEdgeEquiv n 2 (.inr (crossingSlotEquiv 2 (i, s))))

private theorem claspGenerator_crossing_add_two (i : Fin 2) (s : Fin 4) :
    claspGenerator o₁ o₂ b D i (s + 2) =
      (twoCircleClasp o₁ o₂ b).alexanderWeight i s • claspGenerator o₁ o₂ b D i s +
      (1 - (twoCircleClasp o₁ o₂ b).alexanderWeight i s) •
        claspGenerator o₁ o₂ b D i (s + 1) := by
  have h := (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator_crossing_add_two
    (Fin.natAdd n i) s
  rw [alexanderWeight_adjoinTwoCircleClasp_natAdd] at h
  simp only [adjoinTwoCircleClasp_def, toPDCode_disjointUnion,
    crossing_disjointUnion_natAdd] at h
  simpa only [claspGenerator, crossing_apply, toPDCode_twoCircleClasp,
    PDCode.twoCircleClasp_halfEdge, Equiv.Perm.one_apply] using h

/-- The first crossing determines its four slots from slots `0` and `1`; the arc matching
then determines all four slots of the second crossing. -/
private theorem claspGenerator_eq_claspValue (i : Fin 2) (s : Fin 4) :
    claspGenerator o₁ o₂ b D i s =
      claspValue ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 0)
        ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 1) (claspGenerator o₁ o₂ b D 0 0)
        (claspGenerator o₁ o₂ b D 0 1) i s := by
  have h₂ := claspGenerator_crossing_add_two o₁ o₂ b D 0 0
  have h₃ := claspGenerator_crossing_add_two o₁ o₂ b D 0 1
  simp only [Fin.reduceAdd, zero_add] at h₂ h₃
  fin_cases i
  · fin_cases s <;> simp [h₂, h₃]
  · have h := (claspGenerator_arc o₁ o₂ b D 1 s).symm
    fin_cases s <;> simpa [h₂, h₃] using h

private theorem adjoinTwoCircleClaspInvHom_claspValue (i : Fin 2) (s : Fin 4) :
    adjoinTwoCircleClaspInvHom o₁ o₂ b D
      (claspValue ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 0)
        ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 1) (circleGenerator o₁ o₂ D 0)
        (circleGenerator o₁ o₂ D 1) i s) =
        claspGenerator o₁ o₂ b D i s := by
  rw [claspGenerator_eq_claspValue o₁ o₂ b D i s]
  fin_cases i <;> fin_cases s <;>
    simp [circleGenerator, adjoinTwoCircleClaspInvHom_alexanderGenerator,
      adjoinTwoCircleClaspInvValue]

/-- The second Reidemeister move between two crossing-free circles preserves the Alexander
module in any surrounding diagram, for either over-component and every orientation. -/
def alexanderModuleAdjoinTwoCircleClaspEquiv (D : OrientedPDCode n) (o₁ o₂ b : Bool) :
    (D.adjoinTwoCircleClasp o₁ o₂ b).AlexanderModule ≃ₗ[ℤ[T;T⁻¹]]
      ((D.adjoinCircle o₁).adjoinCircle o₂).AlexanderModule :=
  LinearEquiv.ofLinearMap (adjoinTwoCircleClaspHom o₁ o₂ b D) (adjoinTwoCircleClaspInvHom o₁ o₂ b D)
    (by
      ext (h | j)
      · simp [adjoinTwoCircleClaspHom_alexanderGenerator,
        adjoinTwoCircleClaspInvHom_alexanderGenerator, adjoinTwoCircleClaspInvValue,
        adjoinTwoCircleClaspValue]
      · obtain ⟨j, rfl⟩ := (finCongr (by simp :
          ((D.adjoinCircle o₁).adjoinCircle o₂).crossinglessComponentCount =
            D.crossinglessComponentCount + 2)).symm.surjective j
        induction j using Fin.addCases with
        | left j => simp [adjoinTwoCircleClaspHom_alexanderGenerator,
          adjoinTwoCircleClaspInvHom_alexanderGenerator, adjoinTwoCircleClaspInvValue,
          adjoinTwoCircleClaspValue]
        | right j =>
          fin_cases j <;>
            simp [adjoinTwoCircleClaspHom_alexanderGenerator,
              adjoinTwoCircleClaspInvHom_alexanderGenerator, adjoinTwoCircleClaspInvValue,
              adjoinTwoCircleClaspValue,
              claspGenerator, circleGenerator])
    (by
      ext (h | j)
      · obtain ⟨h | h, rfl⟩ := (disjointUnionHalfEdgeEquiv n 2).surjective h
        · simp [adjoinTwoCircleClaspHom_alexanderGenerator,
          adjoinTwoCircleClaspInvHom_alexanderGenerator, adjoinTwoCircleClaspValue,
          adjoinTwoCircleClaspInvValue]
        · obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv 2).surjective h
          simp [-alexanderWeight_twoCircleClasp, adjoinTwoCircleClaspHom_alexanderGenerator,
            adjoinTwoCircleClaspValue, adjoinTwoCircleClaspInvHom_claspValue, claspGenerator]
      · simp [adjoinTwoCircleClaspHom_alexanderGenerator,
        adjoinTwoCircleClaspInvHom_alexanderGenerator, adjoinTwoCircleClaspValue,
        adjoinTwoCircleClaspInvValue])

/-- Old half-edge generators are fixed by the two-circle clasp equivalence. -/
@[simp]
theorem alexanderModuleAdjoinTwoCircleClaspEquiv_apply_alexanderGenerator_inl_inl
    (D : OrientedPDCode n) (o₁ o₂ b : Bool)
    (h : Fin (4 * n)) :
    D.alexanderModuleAdjoinTwoCircleClaspEquiv o₁ o₂ b
      ((D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator
        (.inl (disjointUnionHalfEdgeEquiv n 2 (.inl h)))) =
      ((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator (.inl h) := by
  simp [alexanderModuleAdjoinTwoCircleClaspEquiv, adjoinTwoCircleClaspHom_alexanderGenerator,
    adjoinTwoCircleClaspValue]

/-- Clasp slots map to the combinations of the two new circle generators prescribed by the
first crossing; the second crossing has the reversed slot order. -/
@[simp]
theorem alexanderModuleAdjoinTwoCircleClaspEquiv_apply_alexanderGenerator_inl_inr
    (D : OrientedPDCode n) (o₁ o₂ b : Bool)
    (i : Fin 2) (s : Fin 4) :
    D.alexanderModuleAdjoinTwoCircleClaspEquiv o₁ o₂ b
      ((D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator
        (.inl (crossingSlotEquiv (n + 2) (Fin.natAdd n i, s)))) =
      claspValue ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 0)
        ((twoCircleClasp o₁ o₂ b).alexanderWeight 0 1)
        (((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator
          (.inr (Fin.cast (by simp) (Fin.natAdd D.crossinglessComponentCount (0 : Fin 2)))))
        (((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator
          (.inr (Fin.cast (by simp) (Fin.natAdd D.crossinglessComponentCount (1 : Fin 2)))))
        i s := by
  rw [← disjointUnionHalfEdgeEquiv_inr_crossingSlot]
  simp [alexanderModuleAdjoinTwoCircleClaspEquiv,
    adjoinTwoCircleClaspHom_alexanderGenerator, adjoinTwoCircleClaspValue, circleGenerator]

/-- Old crossing-free components map to the same components before the two new circles. -/
@[simp]
theorem alexanderModuleAdjoinTwoCircleClaspEquiv_apply_alexanderGenerator_inr
    (D : OrientedPDCode n) (o₁ o₂ b : Bool)
    (j : Fin (D.adjoinTwoCircleClasp o₁ o₂ b).crossinglessComponentCount) :
    D.alexanderModuleAdjoinTwoCircleClaspEquiv o₁ o₂ b
      ((D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator (.inr j)) =
      ((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator
        (.inr (Fin.cast (by simp)
          (Fin.castAdd 2 (Fin.cast (m := D.crossinglessComponentCount) (by simp) j)))) := by
  simp [alexanderModuleAdjoinTwoCircleClaspEquiv, adjoinTwoCircleClaspHom_alexanderGenerator,
    adjoinTwoCircleClaspValue]

/-- The inverse fixes the old generators and sends the two new circles to slots `0` and `1`
of the first clasp crossing. -/
@[simp]
theorem alexanderModuleAdjoinTwoCircleClaspEquiv_symm_apply_alexanderGenerator
    (D : OrientedPDCode n) (o₁ o₂ b : Bool)
    (g : Fin (4 * n) ⊕ Fin ((D.adjoinCircle o₁).adjoinCircle o₂).crossinglessComponentCount) :
    (D.alexanderModuleAdjoinTwoCircleClaspEquiv o₁ o₂ b).symm
      (((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator g) =
      Sum.elim
        (fun h ↦ (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator
          (.inl (disjointUnionHalfEdgeEquiv n 2 (.inl h))))
        (fun j ↦ Fin.addCases
          (fun k ↦ (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator
            (.inr (Fin.cast (by simp) k)))
          (fun k ↦ (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator
            (.inl (disjointUnionHalfEdgeEquiv n 2
              (.inr (crossingSlotEquiv 2 (0, Fin.castAdd 2 k))))))
          (Fin.cast (m := D.crossinglessComponentCount + 2) (by simp) j)) g :=
  adjoinTwoCircleClaspInvHom_alexanderGenerator o₁ o₂ b D g

/-- The second Reidemeister move on two crossing-free circles keeps every elementary ideal. -/
@[simp]
theorem elementaryIdeal_adjoinTwoCircleClasp (D : OrientedPDCode n) (o₁ o₂ b : Bool)
    (k : ℕ) :
    (D.adjoinTwoCircleClasp o₁ o₂ b).elementaryIdeal k =
      ((D.adjoinCircle o₁).adjoinCircle o₂).elementaryIdeal k := by
  rw [elementaryIdeal_def, elementaryIdeal_def]
  exact fittingIdeal_congr (D.alexanderModuleAdjoinTwoCircleClaspEquiv o₁ o₂ b) k

end TauCeti.OrientedPDCode
