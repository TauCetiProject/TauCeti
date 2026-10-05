/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Alexander.Invariance
public import TauCeti.KnotTheory.PDCode.Alexander.DisjointUnion
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Two.Circles
import Mathlib.Tactic.Module

/-!
# Alexander invariance of the second Reidemeister move on two circles

Replacing two crossing-free circles by a cancelling clasp preserves the Alexander module,
and hence every elementary ideal, in any surrounding oriented diagram. The equivalence
identifies the old generators and sends the two new circle generators to slots `0` and `1`
of the first clasp crossing. The other slots are determined by the crossing relations.
Both choices of over-component and all component orientations are allowed.

The construction uses the presentation and lifting API of
`TauCeti.OrientedPDCode.alexanderLift`, following the same generator-elimination method as
`TauCeti.OrientedPDCode.alexanderModuleAdjoinKinkEquiv`.

## References

* R. H. Crowell, R. H. Fox, *Introduction to Knot Theory*, GTM 57, Chapters VI–VII.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, GTM 175, Chapters 1 and 6.
-/

public section

noncomputable section

namespace TauCeti.OrientedPDCode

open PDCode LaurentPolynomial

variable (o₁ o₂ b : Bool)

/-- The images of the clasp slots prescribed by its first crossing and its four arcs. -/
private def claspValue {M : Type*} [AddCommGroup M] [Module ℤ[T;T⁻¹] M]
    (x y : M) (i : Fin 2) (s : Fin 4) : M :=
  let w := (twoCircleClasp o₁ o₂ b).alexanderWeight 0
  let u := w 0 • x + (1 - w 0) • y
  let v := w 1 • y + (1 - w 1) • u
  (if i = 0 then ![x, y, u, v] else ![v, u, y, x]) s

private theorem claspValue_arc {M : Type*} [AddCommGroup M] [Module ℤ[T;T⁻¹] M]
    (x y : M) (i : Fin 2) (s : Fin 4) :
    claspValue o₁ o₂ b x y (Fin.rev i) (Fin.rev s) = claspValue o₁ o₂ b x y i s := by
  fin_cases i <;> fin_cases s <;> simp [claspValue, Fin.rev]

private theorem claspValue_crossing {M : Type*} [AddCommGroup M] [Module ℤ[T;T⁻¹] M]
    (x y : M) (i : Fin 2) (s : Fin 4) :
    claspValue o₁ o₂ b x y i (s + 2) =
      (twoCircleClasp o₁ o₂ b).alexanderWeight i s • claspValue o₁ o₂ b x y i s +
      (1 - (twoCircleClasp o₁ o₂ b).alexanderWeight i s) •
        claspValue o₁ o₂ b x y i (s + 1) := by
  have h := (twoCircleClasp o₁ o₂ b).apply_crossing_add_two_of_zero_of_one
    (fun z ↦ let p := (crossingSlotEquiv 2).symm z; claspValue o₁ o₂ b x y p.1 p.2) i
  simp only [crossing_apply, toPDCode_twoCircleClasp, PDCode.twoCircleClasp_halfEdge,
    Equiv.Perm.one_apply, Equiv.symm_apply_apply] at h
  apply h
  -- The two crossings have inverse under-strand coefficients. Check their two independent
  -- relations; the presentation API supplies the opposite-slot relations.
  all_goals
    simp only [claspValue, alexanderWeight_def, PDCode.isOver_def, crossingSign_def,
      crossing_apply, toPDCode_twoCircleClasp, PDCode.twoCircleClasp_halfEdge,
      Equiv.Perm.one_apply, PDCode.twoCircleClasp_overPair]
    repeat rw [orientation_twoCircleClasp]
    fin_cases i <;> cases o₁ <;> cases o₂ <;> cases b <;> simp
  all_goals
    simp only [smul_sub, smul_smul, sub_smul, ← T_add, Int.reduceAdd, T_zero, one_smul]
    module

variable {n : ℕ} (D : OrientedPDCode n)

private def circleGenerator (j : Fin 2) :
    ((D.adjoinCircle o₁).adjoinCircle o₂).AlexanderModule :=
  ((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator
    (.inr (Fin.cast (by simp) (Fin.natAdd D.crossinglessComponentCount j)))

private def moveValue :
    Fin (4 * (n + 2)) ⊕ Fin (D.adjoinTwoCircleClasp o₁ o₂ b).crossinglessComponentCount →
      ((D.adjoinCircle o₁).adjoinCircle o₂).AlexanderModule :=
  Sum.elim
    (fun z ↦ Sum.elim
      (fun h ↦ ((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator (.inl h))
      (fun h ↦ let p := (crossingSlotEquiv 2).symm h
        claspValue o₁ o₂ b (circleGenerator o₁ o₂ D 0) (circleGenerator o₁ o₂ D 1) p.1 p.2)
      ((disjointUnionHalfEdgeEquiv n 2).symm z))
    (fun j ↦ ((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator
      (.inr (Fin.cast (by simp)
        (Fin.castAdd 2 (Fin.cast (m := D.crossinglessComponentCount) (by simp) j)))))

private def moveHom :
    (D.adjoinTwoCircleClasp o₁ o₂ b).AlexanderModule →ₗ[ℤ[T;T⁻¹]]
      ((D.adjoinCircle o₁).adjoinCircle o₂).AlexanderModule :=
  (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderLift (moveValue o₁ o₂ b D)
    (fun z ↦ by
      obtain ⟨h | h, rfl⟩ := (disjointUnionHalfEdgeEquiv n 2).surjective z
      · simpa [moveValue, adjoinTwoCircleClasp_def, disjointUnion_edgePair_val] using
          ((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator_edgePair h
      · obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv 2).surjective h
        simpa [moveValue, adjoinTwoCircleClasp_def, disjointUnion_edgePair_val,
          Equiv.permCongr_apply] using
          claspValue_arc o₁ o₂ b (circleGenerator o₁ o₂ D 0) (circleGenerator o₁ o₂ D 1) i s)
    (fun i s ↦ by
      induction i using Fin.addCases with
      | left i =>
        simp only [adjoinTwoCircleClasp_def, toPDCode_disjointUnion,
          crossing_disjointUnion_castAdd, alexanderWeight_disjointUnion_castAdd,
          moveValue, Sum.elim_inl, Equiv.symm_apply_apply]
        simpa using
          ((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator_crossing_add_two i s
      | right i =>
        simp only [adjoinTwoCircleClasp_def, toPDCode_disjointUnion,
          crossing_disjointUnion_natAdd, alexanderWeight_disjointUnion_natAdd,
          moveValue, Sum.elim_inl, Equiv.symm_apply_apply, Sum.elim_inr]
        simpa only [crossing_apply, toPDCode_twoCircleClasp,
          PDCode.twoCircleClasp_halfEdge, Equiv.Perm.one_apply, Equiv.symm_apply_apply] using
          claspValue_crossing o₁ o₂ b (circleGenerator o₁ o₂ D 0) (circleGenerator o₁ o₂ D 1) i s)

private theorem moveHom_generator (g) :
    moveHom o₁ o₂ b D ((D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator g) =
      moveValue o₁ o₂ b D g :=
  alexanderLift_alexanderGenerator _ _ _ _ _

private def claspGenerator (i : Fin 2) (s : Fin 4) :
    (D.adjoinTwoCircleClasp o₁ o₂ b).AlexanderModule :=
  (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator
    (.inl (disjointUnionHalfEdgeEquiv n 2 (.inr (crossingSlotEquiv 2 (i, s)))))

private def inverseValue :
    Fin (4 * n) ⊕ Fin ((D.adjoinCircle o₁).adjoinCircle o₂).crossinglessComponentCount →
      (D.adjoinTwoCircleClasp o₁ o₂ b).AlexanderModule :=
  Sum.elim
    (fun h ↦ (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator
      (.inl (disjointUnionHalfEdgeEquiv n 2 (.inl h))))
    (fun j ↦ Fin.addCases
      (fun k ↦ (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator (.inr (Fin.cast (by simp) k)))
      (fun k ↦ claspGenerator o₁ o₂ b D 0 (Fin.castAdd 2 k))
      (Fin.cast (m := D.crossinglessComponentCount + 2) (by simp) j))

private def inverseHom :
    ((D.adjoinCircle o₁).adjoinCircle o₂).AlexanderModule →ₗ[ℤ[T;T⁻¹]]
      (D.adjoinTwoCircleClasp o₁ o₂ b).AlexanderModule :=
  ((D.adjoinCircle o₁).adjoinCircle o₂).alexanderLift (inverseValue o₁ o₂ b D)
    (fun h ↦ by
      simpa [inverseValue, adjoinTwoCircleClasp_def, disjointUnion_edgePair_val,
        Equiv.permCongr_apply] using
        (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator_edgePair
          (disjointUnionHalfEdgeEquiv n 2 (.inl h)))
    (fun i s ↦ by
      have h := (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator_crossing_add_two
        (Fin.castAdd 2 i) s
      simp only [adjoinTwoCircleClasp_def, toPDCode_disjointUnion,
        crossing_disjointUnion_castAdd, alexanderWeight_disjointUnion_castAdd] at h
      simpa [inverseValue] using h)

private theorem inverseHom_generator (g) :
    inverseHom o₁ o₂ b D (((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator g) =
      inverseValue o₁ o₂ b D g :=
  alexanderLift_alexanderGenerator _ _ _ _ _

private theorem claspGenerator_arc (i : Fin 2) (s : Fin 4) :
    claspGenerator o₁ o₂ b D (Fin.rev i) (Fin.rev s) = claspGenerator o₁ o₂ b D i s := by
  simpa [claspGenerator, adjoinTwoCircleClasp_def, disjointUnion_edgePair_val,
    Equiv.permCongr_apply] using
    (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator_edgePair
      (disjointUnionHalfEdgeEquiv n 2 (.inr (crossingSlotEquiv 2 (i, s))))

private theorem claspGenerator_crossing (i : Fin 2) (s : Fin 4) :
    claspGenerator o₁ o₂ b D i (s + 2) =
      (twoCircleClasp o₁ o₂ b).alexanderWeight i s • claspGenerator o₁ o₂ b D i s +
      (1 - (twoCircleClasp o₁ o₂ b).alexanderWeight i s) •
        claspGenerator o₁ o₂ b D i (s + 1) := by
  have h := (D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator_crossing_add_two
    (Fin.natAdd n i) s
  simp only [adjoinTwoCircleClasp_def, toPDCode_disjointUnion,
    crossing_disjointUnion_natAdd, alexanderWeight_disjointUnion_natAdd] at h
  simpa only [claspGenerator, crossing_apply, toPDCode_twoCircleClasp,
    PDCode.twoCircleClasp_halfEdge, Equiv.Perm.one_apply] using h

/-- The first crossing determines its four slots from slots `0` and `1`; the arc matching
then determines all four slots of the second crossing. -/
private theorem claspGenerator_eq_value (i : Fin 2) (s : Fin 4) :
    claspGenerator o₁ o₂ b D i s =
      claspValue o₁ o₂ b (claspGenerator o₁ o₂ b D 0 0) (claspGenerator o₁ o₂ b D 0 1) i s := by
  have h₂ := claspGenerator_crossing o₁ o₂ b D 0 0
  have h₃ := claspGenerator_crossing o₁ o₂ b D 0 1
  simp only [Fin.reduceAdd, zero_add] at h₂ h₃
  fin_cases i
  · fin_cases s <;> simp [claspValue, h₂, h₃]
  · have h := (claspGenerator_arc o₁ o₂ b D 1 s).symm
    fin_cases s <;> simpa [claspValue, h₂, h₃] using h

private theorem inverseHom_claspValue (i : Fin 2) (s : Fin 4) :
    inverseHom o₁ o₂ b D
      (claspValue o₁ o₂ b (circleGenerator o₁ o₂ D 0) (circleGenerator o₁ o₂ D 1) i s) =
        claspGenerator o₁ o₂ b D i s := by
  rw [claspGenerator_eq_value o₁ o₂ b D i s]
  fin_cases i <;> fin_cases s <;>
    simp [claspValue, circleGenerator, inverseHom_generator, inverseValue]

/-- The second Reidemeister move between two crossing-free circles preserves the Alexander
module in any surrounding diagram, for either over-component and every orientation. -/
def alexanderModuleAdjoinTwoCircleClaspEquiv (D : OrientedPDCode n) (o₁ o₂ b : Bool) :
    (D.adjoinTwoCircleClasp o₁ o₂ b).AlexanderModule ≃ₗ[ℤ[T;T⁻¹]]
      ((D.adjoinCircle o₁).adjoinCircle o₂).AlexanderModule :=
  LinearEquiv.ofLinearMap (moveHom o₁ o₂ b D) (inverseHom o₁ o₂ b D)
    (by
      ext (h | j)
      · simp [moveHom_generator, inverseHom_generator, inverseValue, moveValue]
      · obtain ⟨j, rfl⟩ := (finCongr (by simp :
          ((D.adjoinCircle o₁).adjoinCircle o₂).crossinglessComponentCount =
            D.crossinglessComponentCount + 2)).symm.surjective j
        induction j using Fin.addCases with
        | left j => simp [moveHom_generator, inverseHom_generator, inverseValue, moveValue]
        | right j =>
          fin_cases j <;>
            simp [moveHom_generator, inverseHom_generator, inverseValue, moveValue,
              claspGenerator, claspValue, circleGenerator])
    (by
      ext (h | j)
      · obtain ⟨h | h, rfl⟩ := (disjointUnionHalfEdgeEquiv n 2).surjective h
        · simp [moveHom_generator, inverseHom_generator, moveValue, inverseValue]
        · obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv 2).surjective h
          simp [moveHom_generator, moveValue, inverseHom_claspValue, claspGenerator]
      · simp [moveHom_generator, inverseHom_generator, moveValue, inverseValue])

/-- Old half-edge generators are fixed by the two-circle clasp equivalence. -/
@[simp]
theorem alexanderModuleAdjoinTwoCircleClaspEquiv_apply_alexanderGenerator_inl
    (D : OrientedPDCode n) (o₁ o₂ b : Bool)
    (h : Fin (4 * n)) :
    D.alexanderModuleAdjoinTwoCircleClaspEquiv o₁ o₂ b
      ((D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator
        (.inl (disjointUnionHalfEdgeEquiv n 2 (.inl h)))) =
      ((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator (.inl h) := by
  simp [alexanderModuleAdjoinTwoCircleClaspEquiv, moveHom_generator, moveValue]

/-- Clasp slots map to the combinations of the two new circle generators prescribed by the
first crossing; the second crossing has the reversed slot order. -/
@[simp]
theorem alexanderModuleAdjoinTwoCircleClaspEquiv_apply_alexanderGenerator_clasp
    (D : OrientedPDCode n) (o₁ o₂ b : Bool)
    (i : Fin 2) (s : Fin 4) :
    D.alexanderModuleAdjoinTwoCircleClaspEquiv o₁ o₂ b
      ((D.adjoinTwoCircleClasp o₁ o₂ b).alexanderGenerator
        (.inl (disjointUnionHalfEdgeEquiv n 2 (.inr (crossingSlotEquiv 2 (i, s)))))) =
      let x := ((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator
        (.inr (Fin.cast (by simp) (Fin.natAdd D.crossinglessComponentCount (0 : Fin 2))))
      let y := ((D.adjoinCircle o₁).adjoinCircle o₂).alexanderGenerator
        (.inr (Fin.cast (by simp) (Fin.natAdd D.crossinglessComponentCount (1 : Fin 2))))
      let w := (twoCircleClasp o₁ o₂ b).alexanderWeight 0
      let u := w 0 • x + (1 - w 0) • y
      let v := w 1 • y + (1 - w 1) • u
      (if i = 0 then ![x, y, u, v] else ![v, u, y, x]) s := by
  simp [alexanderModuleAdjoinTwoCircleClaspEquiv, moveHom_generator, moveValue,
    claspValue, circleGenerator]

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
  simp [alexanderModuleAdjoinTwoCircleClaspEquiv, moveHom_generator, moveValue]

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
  inverseHom_generator o₁ o₂ b D g

/-- The second Reidemeister move on two crossing-free circles keeps every elementary ideal. -/
@[simp]
theorem elementaryIdeal_adjoinTwoCircleClasp (D : OrientedPDCode n) (o₁ o₂ b : Bool)
    (k : ℕ) :
    (D.adjoinTwoCircleClasp o₁ o₂ b).elementaryIdeal k =
      ((D.adjoinCircle o₁).adjoinCircle o₂).elementaryIdeal k := by
  rw [elementaryIdeal_def, elementaryIdeal_def]
  exact fittingIdeal_congr (D.alexanderModuleAdjoinTwoCircleClaspEquiv o₁ o₂ b) k

end TauCeti.OrientedPDCode
