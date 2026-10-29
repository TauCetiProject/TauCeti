/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.Merge
public import TauCeti.KnotTheory.Khovanov.Split

/-!
# Split maps for actual resolutions of a PD-code

Suppose two states `s` and `t` differ at one crossing `c`, and two circles of `t` meet `c`.
Exactly one circle of `s` meets `c`, and the saddle correspondence of circles runs from `t` to
`s`: it collapses the two circles of `t` through `c` onto the circle of `s` through `c` and is a
bijection on all other circles, including every labelled crossing-free circle. The map
`TauCeti.PDCode.resolutionSplitMap` applies the comultiplication `Δ` to the factor of the circle
of `s` through `c` and transports all remaining factors along this correspondence. It is the
split map `TauCeti.Khovanov.fiberwiseSplit` of the indexed circle tensor along the native
quotient correspondence, so it involves no ordering of circles or choice of representatives.

The split is the Frobenius adjoint of the merge along the same saddle in the opposite direction
(`TauCeti.PDCode.circleDuality_resolutionSplitMap`). On the enhanced-state basis it obeys
`Δ X = X ⊗ X` and `Δ 1 = X ⊗ 1 + 1 ⊗ X`, where the two output circles are those through slots
`0` and `2` of `c`, and every other label is retained
(`TauCeti.PDCode.resolutionSplitMap_circleBasis`). The map has quantum degree `-1`, compensating
for the increase of the state quantum shift along an A-to-B edge. This is the unsigned split block
of the resolution differential; its cube sign is supplied separately. No planarity assumption is
needed for a saddle already known to split one circle into two.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §2.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2.
-/

public section

open Finset

namespace TauCeti.PDCode

universe u

variable {n : ℕ} (D : PDCode n) {s t : Fin n → Bool} {c : Fin n}
  (hst : ∀ j, j ≠ c → s j = t j) (hc : s c ≠ t c) (ht : #(D.circlesAt t c) = 2)

section Semiring

variable (R : Type u) [CommSemiring R]

/-- Comultiplication on the circle through `c`, splitting it into the two circles of the target
through `c`, and identity on every other factor of the actual resolved-circle tensor. The
one-circle source condition follows from the target count. -/
noncomputable def resolutionSplitMap :
    Khovanov.CircleTensor R (D.ResolvedCircle s) →ₗ[R]
      Khovanov.CircleTensor R (D.ResolvedCircle t) :=
  Khovanov.fiberwiseSplit (D.saddleResolvedCircleMap (fun j hj ↦ (hst j hj).symm)
    (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two (fun j hj ↦ (hst j hj).symm) hc.symm ht))

/-- The resolution split is the indexed split along the native saddle correspondence from the
target to the source. -/
theorem resolutionSplitMap_def :
    D.resolutionSplitMap hst hc ht R = Khovanov.fiberwiseSplit
      (D.saddleResolvedCircleMap (fun j hj ↦ (hst j hj).symm)
        (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two (fun j hj ↦ (hst j hj).symm)
          hc.symm ht)) := (rfl)

/-- The resolution split is adjoint, for the Frobenius pairing of circle tensors, to the
resolution merge along the same crossing in the opposite direction. -/
@[simp]
theorem circleDuality_resolutionSplitMap
    (x : Khovanov.CircleTensor R (D.ResolvedCircle s))
    (y : Khovanov.CircleTensor R (D.ResolvedCircle t)) :
    Khovanov.circleDuality R _ (D.resolutionSplitMap hst hc ht R x) y =
      Khovanov.circleDuality R _ x
        (D.resolutionMergeMap (fun j hj ↦ (hst j hj).symm) hc.symm ht R y) := by
  rw [resolutionSplitMap_def, Khovanov.circleDuality_fiberwiseSplit, resolutionMergeMap_def]

end Semiring

section Basis

variable {R : Type u} [CommSemiring R]

/-- On enhanced states the split obeys `Δ X = X ⊗ X` and `Δ 1 = X ⊗ 1 + 1 ⊗ X` on the circle
through `c`, whose two outputs are the circles through slots `0` and `2`; every other circle
retains the label of its unchanged source circle. -/
@[simp↓]
theorem resolutionSplitMap_circleBasis (l : D.ResolvedCircle s → Bool) :
    D.resolutionSplitMap hst hc ht R (Khovanov.circleBasis R _ l) =
      if l (.inl ⟦D.crossing c 0⟧) = true then
        Khovanov.circleBasis R _ fun C ↦ l (D.saddleResolvedCircleMap
          (fun j hj ↦ (hst j hj).symm)
          (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two (fun j hj ↦ (hst j hj).symm)
            hc.symm ht) C)
      else
        Khovanov.circleBasis R _ (Function.update (fun C ↦ l (D.saddleResolvedCircleMap
          (fun j hj ↦ (hst j hj).symm)
          (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two (fun j hj ↦ (hst j hj).symm)
            hc.symm ht) C)) (.inl ⟦D.crossing c 0⟧) true) +
        Khovanov.circleBasis R _ (Function.update (fun C ↦ l (D.saddleResolvedCircleMap
          (fun j hj ↦ (hst j hj).symm)
          (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two (fun j hj ↦ (hst j hj).symm)
            hc.symm ht) C)) (.inl ⟦D.crossing c 2⟧) true) := by
  have hts : ∀ j, j ≠ c → t j = s j := fun j hj ↦ (hst j hj).symm
  have hs := D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hts hc.symm ht
  rw [resolutionSplitMap_def, Khovanov.fiberwiseSplit_circleBasis_of_eq_iff
    (D.saddleResolvedCircleMap_surjective hts hs)
    (fun h ↦ (D.card_circlesAt_eq_two_iff t c).mp ht (Sum.inl.inj h))
    (D.saddleResolvedCircleMap_eq_iff hts hs),
    (D.saddleResolvedCircleMap_eq_crossing_iff hts hs _).mpr (Or.inl rfl)]

end Basis

variable (R : Type u) [CommRing R]

/-- An actual resolution split has quantum degree `-1`. -/
theorem isHomogeneous_resolutionSplitMap :
    TauCeti.LinearMap.IsHomogeneous (D.resolutionSplitMap hst hc ht R)
      (Khovanov.circleQuantumGrading R (D.ResolvedCircle s)).piece
      (Khovanov.circleQuantumGrading R (D.ResolvedCircle t)).piece (-1) := by
  have hts : ∀ j, j ≠ c → t j = s j := fun j hj ↦ (hst j hj).symm
  have hcard := D.card_resolvedCircle_source_eq_target_add_one hts
    (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hts hc.symm ht) ht
  have hdegree : (Fintype.card (D.ResolvedCircle s) : ℤ) -
      Fintype.card (D.ResolvedCircle t) = -1 := by omega
  rw [resolutionSplitMap_def, ← hdegree]
  exact Khovanov.isHomogeneous_fiberwiseSplit R _

end TauCeti.PDCode
