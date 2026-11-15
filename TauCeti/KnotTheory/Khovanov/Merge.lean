/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.CircleTensor
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Saddle

/-!
# Merge maps for actual resolutions of a PD-code

Suppose two states differ at one crossing and two source circles meet that crossing. Exactly
one target circle meets it. The map `TauCeti.PDCode.resolutionMergeMap` multiplies the factors
of these two source circles and transports all remaining factors, including every labelled
crossing-free circle. It uses the native quotient correspondence of circles and the indexed
circle tensor, with no ordering or choice of representatives.

On the enhanced-state basis, two `X` labels on the merged circles give zero. In every other
case their labels multiply and every other label is retained. The map has quantum degree
`-1`, compensating for the increase of the state quantum shift along an A-to-B edge. This is
the unsigned merge block of the resolution differential; its cube sign is supplied separately.
No planarity assumption is needed for a saddle already known to merge two circles.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §2.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2.
-/

public section

open Finset PiTensorProduct DualNumber
open scoped TensorProduct

namespace TauCeti.PDCode

universe u

variable {n : ℕ} (D : PDCode n) {s t : Fin n → Bool} {c : Fin n}
  (hst : ∀ j, j ≠ c → s j = t j) (hc : s c ≠ t c) (hs : #(D.circlesAt s c) = 2)

section Semiring

variable (R : Type u) [CommSemiring R]

/-- Multiplication on the two circles merged at `c`, and identity on every other factor of the
actual resolved-circle tensor. The one-circle target condition follows from the source count. -/
noncomputable def resolutionMergeMap :
    Khovanov.CircleTensor R (D.ResolvedCircle s) →ₐ[R]
      Khovanov.CircleTensor R (D.ResolvedCircle t) :=
  fiberwiseMul (A := fun _ ↦ R[ε]) (D.saddleResolvedCircleMap hst
    (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hst hc hs))

/-- The resolution merge is the indexed multiplication along the native saddle correspondence. -/
theorem resolutionMergeMap_def :
    D.resolutionMergeMap hst hc hs R = fiberwiseMul (A := fun _ ↦ R[ε])
      (D.saddleResolvedCircleMap hst
        (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hst hc hs)) := (rfl)

/-- The merge sends a pure tensor to the tensor of the products over the saddle fibres. Each
unchanged fibre is a singleton, and the changed fibre consists of the two source circles. -/
@[simp]
theorem resolutionMergeMap_tprod (x : D.ResolvedCircle s → R[ε]) :
    D.resolutionMergeMap hst hc hs R (tprod R x) = tprod R fun C ↦
      ∏ C' with D.saddleResolvedCircleMap hst
        (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hst hc hs) C' = C, x C' := by
  rw [resolutionMergeMap_def, fiberwiseMul_tprod_eq_tprod_prod]

variable {R}

private theorem no_double_label_iff (l : D.ResolvedCircle s → Bool) :
    (∀ C, #{C' | D.saddleResolvedCircleMap hst
      (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hst hc hs) C' = C ∧ l C' = true} ≤ 1) ↔
      ¬(l (.inl ⟦D.crossing c 0⟧) = true ∧ l (.inl ⟦D.crossing c 2⟧) = true) := by
  let ht := D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hst hc hs
  have hpq : (Sum.inl ⟦D.crossing c 0⟧ : D.ResolvedCircle s) ≠ .inl ⟦D.crossing c 2⟧ :=
    fun h ↦ (D.card_circlesAt_eq_two_iff s c).mp hs (Sum.inl.inj h)
  constructor
  · intro h hl
    apply hpq
    apply card_le_one.mp (h (.inl ⟦D.crossing c 0⟧))
    · exact mem_filter.mpr ⟨mem_univ _, ⟨by simp, hl.1⟩⟩
    · simp only [mem_filter, mem_univ, true_and, hl.2, and_true]
      exact (D.saddleResolvedCircleMap_eq_crossing_iff hst ht _).mpr (Or.inr rfl)
  · intro hl C
    refine card_le_one.mpr fun a ha b hb ↦ ?_
    simp only [mem_filter, mem_univ, true_and] at ha hb
    rcases (D.saddleResolvedCircleMap_eq_iff hst ht a b).mp (ha.1.trans hb.1.symm) with h | h
    · exact h
    · rcases h with ⟨rfl | rfl, rfl | rfl⟩
      · rfl
      · exact False.elim (hl ⟨ha.2, hb.2⟩)
      · exact False.elim (hl ⟨hb.2, ha.2⟩)
      · rfl

/-- On enhanced states the merged labels obey `1·1=1`, `1·X=X·1=X`, and `X·X=0`;
all other labels follow their unchanged circle. -/
@[simp↓]
theorem resolutionMergeMap_circleBasis (l : D.ResolvedCircle s → Bool) :
    D.resolutionMergeMap hst hc hs R (Khovanov.circleBasis R _ l) =
      if l (.inl ⟦D.crossing c 0⟧) = true ∧ l (.inl ⟦D.crossing c 2⟧) = true then 0
      else Khovanov.circleBasis R _ fun C ↦ decide (∃ C', D.saddleResolvedCircleMap hst
        (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hst hc hs) C' = C ∧ l C' = true) := by
  rw [resolutionMergeMap_def, Khovanov.fiberwiseMul_circleBasis]
  simp only [D.no_double_label_iff hst hc hs, ite_not]

end Semiring

variable (R : Type u) [CommRing R]

/-- An actual resolution merge has quantum degree `-1`. -/
theorem isHomogeneous_resolutionMergeMap :
    TauCeti.LinearMap.IsHomogeneous (D.resolutionMergeMap hst hc hs R).toLinearMap
      (Khovanov.circleQuantumGrading R (D.ResolvedCircle s)).piece
      (Khovanov.circleQuantumGrading R (D.ResolvedCircle t)).piece (-1) := by
  have hcard := D.card_resolvedCircle_source_eq_target_add_one hst
    (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hst hc hs) hs
  have hdegree : (Fintype.card (D.ResolvedCircle t) : ℤ) -
      Fintype.card (D.ResolvedCircle s) = -1 := by omega
  rw [resolutionMergeMap_def, ← hdegree]
  exact Khovanov.isHomogeneous_fiberwiseMul _

end TauCeti.PDCode
