/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.FlagMinor.Basic
public import TauCeti.RingTheory.MvPolynomial.MultiHomogeneous

/-!
# Row and column multigradings of flag minors

Each flag minor `TauCeti.flagMinor R I` of the generic `n × n` matrix `(z_(r,c))` is doubly
multihomogeneous:
* for the **row multigrading** `MvPolynomial.IsMultiHomogeneous`, its multidegree is the
  indicator function of `I` (`TauCeti.isMultiHomogeneous_flagMinor`);
* for the **fundamental column multigrading** `TauCeti.flagColWeight`, its degree in column `c`
  is `1` if `c < #I` and `0` otherwise (`TauCeti.isWeightedHomogeneous_flagColWeight_flagMinor`),
  corresponding to the fundamental weight `(GTPattern.rowSubset I).topRow`.

## Main definitions

* `TauCeti.flagColWeight`: the indicator weight of column `c` of the generic `n × n` matrix.

## Main results

* `TauCeti.isMultiHomogeneous_flagMinor`: row-indicator multihomogeneity of a flag minor.
* `TauCeti.isWeightedHomogeneous_flagColWeight_flagMinor`: fundamental column-weight homogeneity
  of a flag minor.
-/

public section

namespace TauCeti

open Finset MvPolynomial

variable {n : ℕ}

/-- Each flag minor `flagMinor R I` is multihomogeneous for the row multigrading on the generic
`n × n` matrix, of multidegree the indicator function of `I`. -/
theorem isMultiHomogeneous_flagMinor (R : Type*) [CommRing R] (I : Finset (Fin n)) :
    IsMultiHomogeneous (fun r : Fin n ↦ if r ∈ I then 1 else 0) (flagMinor R I) := by
  rw [flagMinor_def, Matrix.mvPolynomialMinor_eq_det_submatrix, Matrix.det_apply]
  refine IsMultiHomogeneous.sum univ _ fun σ _ ↦ ?_
  have hprod : IsMultiHomogeneous
      (∑ c : Fin #I, (Pi.single (I.orderEmbOfFin rfl (σ c)) 1 : Fin n → ℕ))
      (∏ c : Fin #I, X (I.orderEmbOfFin rfl (σ c), Fin.castLE (card_finset_fin_le I) c) :
        MvPolynomial (Fin n × Fin n) R) :=
    IsMultiHomogeneous.prod univ _ _ fun c _ ↦ isMultiHomogeneous_X _ _
  have hdeg : (∑ c : Fin #I, (Pi.single (I.orderEmbOfFin rfl (σ c)) 1 : Fin n → ℕ)) =
      fun r : Fin n ↦ if r ∈ I then 1 else 0 := by
    rw [Equiv.sum_comp σ fun c ↦ (Pi.single (I.orderEmbOfFin rfl c) 1 : Fin n → ℕ)]
    ext r
    rw [Finset.sum_apply]
    by_cases hr : r ∈ I
    · obtain ⟨c, rfl⟩ := (Finset.range_orderEmbOfFin I rfl).symm.subset hr
      rw [Fintype.sum_eq_single c fun d hd ↦
        Pi.single_eq_of_ne ((I.orderEmbOfFin rfl).injective.ne hd.symm) 1]
      simp [hr]
    · simp only [hr, ↓reduceIte]
      exact Fintype.sum_eq_zero _ fun c ↦ Pi.single_eq_of_ne
        (by rintro rfl; exact hr (I.orderEmbOfFin_mem rfl c)) 1
  rw [hdeg] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
  · rwa [hσ, one_smul]
  · rw [hσ, Units.neg_smul, one_smul]
    exact hprod.neg

/-- Indicator weight of column `c` of the generic `n × n` matrix `(z_(r,c))`. -/
def flagColWeight (c : Fin n) : Fin n × Fin n → ℕ :=
  fun p ↦ if p.snd = c then 1 else 0

@[simp]
theorem flagColWeight_apply (c : Fin n) (p : Fin n × Fin n) :
    flagColWeight c p = if p.snd = c then 1 else 0 :=
  (rfl)

/-- Each flag minor `flagMinor R I` is weighted homogeneous for the indicator weight of column `c`,
of degree `1` if `c < #I` and `0` otherwise — the fundamental weight `(rowSubset I).topRow c`. -/
theorem isWeightedHomogeneous_flagColWeight_flagMinor (R : Type*) [CommRing R]
    (I : Finset (Fin n)) (c : Fin n) :
    (flagMinor R I).IsWeightedHomogeneous (flagColWeight c) (if (c : ℕ) < #I then 1 else 0) := by
  rw [flagMinor_def, Matrix.mvPolynomialMinor_eq_det_submatrix, Matrix.det_apply]
  refine IsWeightedHomogeneous.sum univ _ _ fun σ _ ↦ ?_
  have hprod :
      (∏ d : Fin #I, X (I.orderEmbOfFin rfl (σ d), Fin.castLE (card_finset_fin_le I) d) :
        MvPolynomial (Fin n × Fin n) R).IsWeightedHomogeneous (flagColWeight c)
        (∑ d : Fin #I, flagColWeight c
          (I.orderEmbOfFin rfl (σ d), Fin.castLE (card_finset_fin_le I) d)) :=
    IsWeightedHomogeneous.prod univ _ _ fun d _ ↦ isWeightedHomogeneous_X R _ _
  have hdeg :
      (∑ d : Fin #I, flagColWeight c
        (I.orderEmbOfFin rfl (σ d), Fin.castLE (card_finset_fin_le I) d)) =
        if (c : ℕ) < #I then 1 else 0 := by
    simp only [flagColWeight_apply]
    by_cases hc : (c : ℕ) < #I
    · rw [ite_eq_left hc, Fintype.sum_eq_single ⟨c, hc⟩ fun d hd ↦ ite_eq_right fun h ↦ hd ?_]
      · simp
      · exact Fin.ext (by simpa using congrArg Fin.val h)
    · rw [ite_eq_right hc]
      exact Fintype.sum_eq_zero _ fun d ↦
        ite_eq_right fun h ↦ hc (by simp [← h])
  rw [hdeg] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
  · rwa [hσ, one_smul]
  · rw [hσ, Units.neg_smul, one_smul]
    exact hprod.neg

end TauCeti
