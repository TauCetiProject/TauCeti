/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.Homology
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Circle.Basic
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.One.Basic
import TauCeti.KnotTheory.Khovanov.Resolution.ReidemeisterOne

/-!
# The normalized Khovanov complex under the first Reidemeister move

Inserting a kink into an arc or a crossing-free circle of a planar oriented PD-code preserves
its normalized Khovanov complex up to chain homotopy equivalence in each quantum degree.
Taking homology gives an isomorphism in every bidegree over an arbitrary commutative coefficient
ring. Both signs of kink are covered.

The construction transports the unnormalized arc and isolated-circle cancellations through
`OrientedPDCode.khovanovComplexShiftIso`. These cancellations use the explicit split skein cone
and the two loop labels in the Frobenius algebra. A positive crossing contributes the quantum
correction cancelling the bracket's `+1`; a negative crossing contributes the quantum correction
cancelling its `-2`, together with the native cochain shift cancelling its `-1`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §§5.1–5.2
  (invariance under the first Reidemeister move).
* D. Bar-Natan, *Fast Khovanov homology computations*, J. Knot Theory Ramifications 16 (2007),
  243--255, Lemma 4.2 (Gaussian elimination).
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex

namespace TauCeti.OrientedPDCode

universe u

/-- Normalize a bracket cancellation with the crossing-count corrections of a kink. The two
native shifts are combined before applying the inverse normalization comparison. -/
private def normalizedKinkHomotopyEquiv {n m : ℕ}
    (D : OrientedPDCode n) (D' : OrientedPDCode m)
    (hD : D.toPDCode.IsPlanar) (hD' : D'.toPDCode.IsPlanar)
    (R : Type u) [CommRing R] (b : Bool) (j : ℤ)
    (hp : D'.positiveCrossingCount = D.positiveCrossingCount + if b then 1 else 0)
    (hn : D'.negativeCrossingCount = D.negativeCrossingCount + if b then 0 else 1)
    (e : HomotopyEquiv
      (D'.toPDCode.khovanovBracket hD' R
        (j - D'.positiveCrossingCount + 2 * D'.negativeCrossingCount))
      (if b then D.toPDCode.khovanovBracket hD R
        (j - D'.positiveCrossingCount + 2 * D'.negativeCrossingCount + 1)
      else (D.toPDCode.khovanovBracket hD R
        (j - D'.positiveCrossingCount + 2 * D'.negativeCrossingCount - 2))⟦(-1 : ℤ)⟧)) :
    HomotopyEquiv (D'.khovanovComplex hD' R j) (D.khovanovComplex hD R j) := by
  refine (HomotopyEquiv.ofIso (D'.khovanovComplexShiftIso hD' R j)).trans
    (HomotopyEquiv.trans ?_ (HomotopyEquiv.ofIso (D.khovanovComplexShiftIso hD R j).symm))
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hp hn e
    exact (e.shift (D'.negativeCrossingCount : ℤ)).trans (HomotopyEquiv.ofIso
      (((shiftFunctorAdd' (CochainComplex (ModuleCat.{u} R) ℤ) (-1)
        (D'.negativeCrossingCount : ℤ) (D.negativeCrossingCount : ℤ)
        (by rw [hn, Nat.cast_add]; simp)).app _).symm ≪≫
          eqToIso (by congr 2; simp only [hp, hn, Nat.cast_add, Nat.cast_one]; omega)))
  · simp only [↓reduceIte, Nat.add_zero] at hp hn e
    exact (e.shift (D'.negativeCrossingCount : ℤ)).trans (HomotopyEquiv.ofIso
      (eqToIso (by
        congr 2
        · exact_mod_cast hn
        · simp only [hp, hn, Nat.cast_add, Nat.cast_one]
          omega)))

variable {n : ℕ} (D : OrientedPDCode n) (h : Fin (4 * n))
  (hD : D.toPDCode.IsPlanar) (R : Type u) [CommRing R]

/-- Inserting an oriented kink of either sign preserves each quantum component of the
normalized Khovanov complex up to chain homotopy equivalence. Applying
`HomotopyEquiv.toHomologyIso` gives the induced isomorphism of `khovanovHomology` in every
bidegree. -/
def khovanovComplexReidemeisterOneHomotopyEquiv (b : Bool) (j : ℤ) :
    HomotopyEquiv
      ((D.reidemeisterOne h b).khovanovComplex
        (by simpa only [toPDCode_reidemeisterOne] using
          (PDCode.isPlanar_reidemeisterOne D.toPDCode h b).2 hD) R j)
      (D.khovanovComplex hD R j) :=
  normalizedKinkHomotopyEquiv D (D.reidemeisterOne h b) hD _ R b j
    (D.positiveCrossingCount_reidemeisterOne h b)
    (D.negativeCrossingCount_reidemeisterOne h b) (by
      cases b
      · simpa only [toPDCode_reidemeisterOne, Bool.false_eq_true, ↓reduceIte] using
          D.toPDCode.khovanovBracketReidemeisterOneFalseHomotopyEquiv h hD R
            (j - (D.reidemeisterOne h false).positiveCrossingCount +
              2 * (D.reidemeisterOne h false).negativeCrossingCount)
      · simpa only [toPDCode_reidemeisterOne, Bool.false_eq_true, ↓reduceIte] using
          D.toPDCode.khovanovBracketReidemeisterOneTrueHomotopyEquiv h hD R
            (j - (D.reidemeisterOne h true).positiveCrossingCount +
              2 * (D.reidemeisterOne h true).negativeCrossingCount))

/-- The first Reidemeister move on an isolated oriented component preserves the normalized
complex. This includes a kink on the unknot when the surrounding diagram is empty. The induced
bigraded homology isomorphism is `HomotopyEquiv.toHomologyIso` applied to this equivalence. -/
def khovanovComplexAdjoinKinkHomotopyEquiv (o b : Bool) (j : ℤ) :
    HomotopyEquiv
      ((D.adjoinKink o b).khovanovComplex
        (by simpa only [toPDCode_adjoinKink] using
          (PDCode.isPlanar_adjoinKink_iff D.toPDCode b).2 hD) R j)
      ((D.adjoinCircle o).khovanovComplex
        (by simpa only [toPDCode_adjoinCircle] using
          (PDCode.isPlanar_adjoinCircle_iff D.toPDCode).2 hD) R j) :=
  normalizedKinkHomotopyEquiv (D.adjoinCircle o) (D.adjoinKink o b) _ _ R b j
    (by rw [positiveCrossingCount_adjoinKink]; congr 1; simp [positiveCrossingCount_def])
    (by rw [negativeCrossingCount_adjoinKink]; congr 1; simp [negativeCrossingCount_def]) (by
      cases b
      · simpa only [toPDCode_adjoinKink, toPDCode_adjoinCircle, Bool.false_eq_true,
          ↓reduceIte] using
          D.toPDCode.khovanovBracketAdjoinKinkFalseHomotopyEquiv hD R
            (j - (D.adjoinKink o false).positiveCrossingCount +
              2 * (D.adjoinKink o false).negativeCrossingCount)
      · simpa only [toPDCode_adjoinKink, toPDCode_adjoinCircle, Bool.false_eq_true,
          ↓reduceIte] using
          D.toPDCode.khovanovBracketAdjoinKinkTrueHomotopyEquiv hD R
            (j - (D.adjoinKink o true).positiveCrossingCount +
              2 * (D.adjoinKink o true).negativeCrossingCount))

end TauCeti.OrientedPDCode
