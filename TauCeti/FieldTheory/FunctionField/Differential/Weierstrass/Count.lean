/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Weierstrass.TotalWeight
public import TauCeti.FieldTheory.FunctionField.Hyperelliptic.WeierstrassGaps
import TauCeti.Data.Nat.Choose.Basic

/-!
# The number of Weierstrass points

Let `F / k` be a function field of genus `g ≥ 2` with exact constants over an algebraically closed
field `k`, and suppose that the Weierstrass gaps at every place are pairwise distinct in `k` (in
characteristic zero this is automatic). The *Weierstrass points* are the places of nonzero
Weierstrass weight; there are finitely many of them, and their weights add up to `g³ - g`
(`TauCeti.finsum_weierstrassWeight`). Since each weight is at least one and at most
`g (g - 1) / 2` (`TauCeti.Place.weierstrassWeight_le_genus_choose_two`), and
`g³ - g = (2g + 2) · g (g - 1) / 2`, the number of Weierstrass points lies between `2g + 2` and
`g³ - g`.

The lower bound is attained exactly by the hyperelliptic fields. If `F` is hyperelliptic, with
rational subfield `k(x)` of index two, a place has weight `g (g - 1) / 2` when it ramifies over
`k(x)` and weight `0` otherwise, so all Weierstrass points have the maximal weight and there are
exactly `2g + 2` of them. Conversely, if there are at most `2g + 2` Weierstrass points, the total
weight forces one of them to have maximal weight; `2` is then a pole number there, which makes `F`
hyperelliptic. Hence a non-hyperelliptic `F` has at least `2g + 3` Weierstrass points; by
rigidity, these detect every automorphism of `F`.

## Main results

* `TauCeti.ncard_setOf_weierstrassWeight_ne_zero_le_genus_pow_three_sub_genus`: there are at most
  `g³ - g` Weierstrass points.
* `TauCeti.two_mul_genus_add_two_le_ncard_setOf_weierstrassWeight_ne_zero`: for `g ≥ 2` there are
  at least `2g + 2` Weierstrass points.
* `TauCeti.isHyperellipticFunctionField_iff_ncard_setOf_weierstrassWeight_ne_zero_eq`: for
  `g ≥ 2`, `F` is hyperelliptic exactly when it has `2g + 2` Weierstrass points.
* `TauCeti.two_mul_genus_add_three_le_ncard_setOf_weierstrassWeight_ne_zero`: a
  non-hyperelliptic `F` of genus `g ≥ 2` has at least `2g + 3` Weierstrass points.

## References

* H. M. Farkas and I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Springer, 1992, Sections III.5
  and III.7, for the bounds `2g + 2 ≤ #𝒲 ≤ g³ - g` and the hyperelliptic equality case.
* D. M. Goldschmidt, *Algebraic Functions and Projective Curves*, GTM 215, Springer, 2003,
  the Wronskian treatment of Weierstrass points.
-/

public section

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [IsAlgClosed k]

/-- The weights of the finitely many Weierstrass points add up to `g³ - g`. -/
private theorem sum_toFinset_weierstrassWeight (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F)
    (hgaps : ∀ P : Place k F, Set.InjOn (Nat.cast : ℕ → k) P.weierstrassGaps)
    (hfin : {P : Place k F | P.weierstrassWeight ≠ 0}.Finite) :
    ∑ P ∈ hfin.toFinset, P.weierstrassWeight = genus k F ^ 3 - genus k F := by
  rw [← finsum_weierstrassWeight hF hex hgaps]
  exact (finsum_eq_sum_of_support_subset _ fun P hP ↦ by simpa using hP).symm

/-- **There are at most `g³ - g` Weierstrass points**: over an algebraically closed field, if the
gaps at every place are pairwise distinct in `k`, at most `g³ - g` places have nonzero
Weierstrass weight, since the weights add up to `g³ - g`. -/
theorem ncard_setOf_weierstrassWeight_ne_zero_le_genus_pow_three_sub_genus
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hgaps : ∀ P : Place k F, Set.InjOn (Nat.cast : ℕ → k) P.weierstrassGaps) :
    {P : Place k F | P.weierstrassWeight ≠ 0}.ncard ≤ genus k F ^ 3 - genus k F := by
  have hfin := Place.finite_setOf_weierstrassWeight_ne_zero hF hex hgaps
  rw [Set.ncard_eq_toFinset_card _ hfin, ← sum_toFinset_weierstrassWeight hF hex hgaps hfin]
  simpa using Finset.card_nsmul_le_sum hfin.toFinset (fun P ↦ P.weierstrassWeight) 1
    fun P hP ↦ Nat.one_le_iff_ne_zero.mpr (by simpa using hP)

/-- **There are at least `2g + 2` Weierstrass points**: over an algebraically closed field, if the
gaps at every place are pairwise distinct in `k`, a function field of genus `g ≥ 2` with exact
constants has at least `2g + 2` places of nonzero Weierstrass weight, since the weights add up to
`g³ - g = (2g + 2) · g (g - 1) / 2` and each is at most `g (g - 1) / 2`. -/
theorem two_mul_genus_add_two_le_ncard_setOf_weierstrassWeight_ne_zero
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hgaps : ∀ P : Place k F, Set.InjOn (Nat.cast : ℕ → k) P.weierstrassGaps)
    (hg : 2 ≤ genus k F) :
    2 * genus k F + 2 ≤ {P : Place k F | P.weierstrassWeight ≠ 0}.ncard := by
  have hfin := Place.finite_setOf_weierstrassWeight_ne_zero hF hex hgaps
  have hle := Finset.sum_le_card_nsmul hfin.toFinset (fun P ↦ P.weierstrassWeight)
    ((genus k F).choose 2) fun P _ ↦ P.weierstrassWeight_le_genus_choose_two hF hex
      (P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF)
  rw [sum_toFinset_weierstrassWeight hF hex hgaps hfin, Nat.pow_three_sub_self_eq_mul_choose_two,
    smul_eq_mul] at hle
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact Nat.le_of_mul_le_mul_right hle (Nat.choose_pos hg)

/-- If there are at most `2g + 2` Weierstrass points, one of them has the maximal weight
`g (g - 1) / 2`, since the weights add up to `(2g + 2) · g (g - 1) / 2`; so `2` is a pole number
there and `F` is hyperelliptic. -/
private theorem isHyperellipticFunctionField_of_ncard_setOf_weierstrassWeight_ne_zero_le
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hgaps : ∀ P : Place k F, Set.InjOn (Nat.cast : ℕ → k) P.weierstrassGaps)
    (hg : 2 ≤ genus k F)
    (hcard : {P : Place k F | P.weierstrassWeight ≠ 0}.ncard ≤ 2 * genus k F + 2) :
    IsHyperellipticFunctionField k F := by
  have hfin := Place.finite_setOf_weierstrassWeight_ne_zero hF hex hgaps
  have hlow := two_mul_genus_add_two_le_ncard_setOf_weierstrassWeight_ne_zero hF hex hgaps hg
  rw [Set.ncard_eq_toFinset_card _ hfin] at hcard hlow
  have hne : hfin.toFinset.Nonempty := Finset.card_pos.mp (by omega)
  have hmax : ∃ P ∈ hfin.toFinset, P.weierstrassWeight = (genus k F).choose 2 := by
    by_contra! hlt
    have hsum := Finset.sum_lt_sum_of_nonempty hne fun P hP ↦ lt_of_le_of_ne
      (P.weierstrassWeight_le_genus_choose_two hF hex
        (P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF)) (hlt P hP)
    rw [sum_toFinset_weierstrassWeight hF hex hgaps hfin, Finset.sum_const, smul_eq_mul,
      Nat.pow_three_sub_self_eq_mul_choose_two] at hsum
    exact absurd (Nat.lt_of_mul_lt_mul_right hsum) (by omega)
  obtain ⟨P, -, hP⟩ := hmax
  have hP₁ := P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF
  exact isHyperellipticFunctionField_of_isPoleNumber_two_of_perfectField hF hex hg hP₁
    ((P.weierstrassWeight_eq_genus_choose_two_iff hF hex hP₁).mp hP)

/-- **A function field of genus `g ≥ 2` is hyperelliptic exactly when it has `2g + 2` Weierstrass
points**, over an algebraically closed field, if the gaps at every place are pairwise distinct
in `k`. Every other function field of genus `g ≥ 2` has more, see
`TauCeti.two_mul_genus_add_three_le_ncard_setOf_weierstrassWeight_ne_zero`. -/
theorem isHyperellipticFunctionField_iff_ncard_setOf_weierstrassWeight_ne_zero_eq
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hgaps : ∀ P : Place k F, Set.InjOn (Nat.cast : ℕ → k) P.weierstrassGaps)
    (hg : 2 ≤ genus k F) :
    IsHyperellipticFunctionField k F ↔
      {P : Place k F | P.weierstrassWeight ≠ 0}.ncard = 2 * genus k F + 2 := by
  refine ⟨fun hhyp ↦ ?_, fun hcard ↦
    isHyperellipticFunctionField_of_ncard_setOf_weierstrassWeight_ne_zero_le hF hex hgaps hg
      hcard.le⟩
  -- All Weierstrass points have weight `g (g - 1) / 2`, and the weights add up to
  -- `(2g + 2) · g (g - 1) / 2`.
  have hfin := Place.finite_setOf_weierstrassWeight_ne_zero hF hex hgaps
  have hsum := sum_toFinset_weierstrassWeight hF hex hgaps hfin
  rw [Finset.sum_congr rfl fun P hP ↦
      weierstrassWeight_eq_genus_choose_two_of_isHyperellipticFunctionField hF hex hhyp
        (P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF) (by simpa using hP),
    Finset.sum_const, smul_eq_mul, Nat.pow_three_sub_self_eq_mul_choose_two] at hsum
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact Nat.eq_of_mul_eq_mul_right (Nat.choose_pos hg) hsum

/-- **A non-hyperelliptic function field of genus `g ≥ 2` has at least `2g + 3` Weierstrass
points**, over an algebraically closed field, if the gaps at every place are pairwise distinct
in `k`. -/
theorem two_mul_genus_add_three_le_ncard_setOf_weierstrassWeight_ne_zero
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hgaps : ∀ P : Place k F, Set.InjOn (Nat.cast : ℕ → k) P.weierstrassGaps)
    (hg : 2 ≤ genus k F) (hhyp : ¬ IsHyperellipticFunctionField k F) :
    2 * genus k F + 3 ≤ {P : Place k F | P.weierstrassWeight ≠ 0}.ncard := by
  by_contra! h
  exact hhyp (isHyperellipticFunctionField_of_ncard_setOf_weierstrassWeight_ne_zero_le hF hex
    hgaps hg (by omega))

end TauCeti
