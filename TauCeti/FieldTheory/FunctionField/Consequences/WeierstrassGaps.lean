/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import TauCeti.FieldTheory.FunctionField.Consequences.HighDegree

/-!
# Weierstrass gaps

At a place `P`, a positive integer `n` is a pole number if some function has a pole of order
exactly `n` at `P` and is regular at every other place.  Otherwise `n` is a gap.  At a rational
place of a function field of positive genus `g`, there are exactly `g` gaps: the first is `1`,
and every gap is at most `2g - 1`.  This is the Weierstrass gap theorem, Stichtenoth,
*Algebraic Function Fields and Codes*, 2nd ed., Theorem 1.6.8.

The proof counts the jumps in the filtration

`L(0) ⊆ L(P) ⊆ L(2P) ⊆ ...`.

At a rational place each step changes the dimension by at most one, and it changes the dimension
exactly when the index is a pole number.  Riemann--Roch computes `ℓ((2g - 1)P) = g`, so precisely
`g` of the first `2g - 1` steps do not change the dimension.

## Main definitions

* `TauCeti.Place.IsPoleNumber`: an integer occurring as the order of the unique pole of a
  function.
* `TauCeti.Place.IsGap`: an integer which is not a pole number.
* `TauCeti.Place.gapNumbersUpTo`: the gaps in a prescribed finite interval.
* `TauCeti.Place.weierstrassGaps`: the finite set of gaps at a place.

## Main results

* `TauCeti.Place.isPoleNumber_iff_dim_lt`: pole numbers are exactly the strict jumps in the
  one-place Riemann--Roch filtration.
* `TauCeti.Place.card_gapNumbersUpTo_add_dim`: among `1, ..., n`, the number of gaps plus
  `ℓ(nP)` is `n + 1`.
* `TauCeti.Place.card_weierstrassGaps`: the Weierstrass gap theorem: a rational place of a
  function field of genus `g` has exactly `g` gaps.
* `TauCeti.Place.one_mem_weierstrassGaps`: the first gap is `1`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 1.6.8.
* G. Li, `vaca22/riemann-roch-function-fields`, a separate Lean formalization of Weierstrass
  gaps along the same function-field route.
-/

public section

noncomputable section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Place

/-- A natural number `n` is a **pole number** at `P` if some nonzero function has order `-n` at
`P` and is regular at every other place (Stichtenoth, Definition preceding Theorem 1.6.8).

Although the classical terminology is principally used for positive `n`, this definition also
includes `0`: the constant function `1` witnesses that zero is a pole number. -/
def IsPoleNumber (P : Place k F) (n : ℕ) : Prop :=
  ∃ x : F, x ≠ 0 ∧ P.ord x = -(n : ℤ) ∧ ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord x

/-- A natural number is a **gap** at `P` if it is not a pole number at `P`. -/
def IsGap (P : Place k F) (n : ℕ) : Prop :=
  ¬ P.IsPoleNumber n

/-- Zero is a pole number at every place, witnessed by the constant function `1`. -/
theorem isPoleNumber_zero (P : Place k F) : P.IsPoleNumber 0 := by
  refine ⟨1, one_ne_zero, ?_, fun Q _ ↦ ?_⟩ <;> simp

/-- Zero is never a gap at a place. -/
@[simp]
theorem not_isGap_zero (P : Place k F) : ¬ P.IsGap 0 := by
  simpa only [IsGap, not_not] using P.isPoleNumber_zero

/-- Pole numbers are closed under addition: multiply functions having their unique poles at the
same place. -/
theorem IsPoleNumber.add {P : Place k F} {m n : ℕ}
    (hm : P.IsPoleNumber m) (hn : P.IsPoleNumber n) : P.IsPoleNumber (m + n) := by
  obtain ⟨x, hx0, hxP, hx⟩ := hm
  obtain ⟨y, hy0, hyP, hy⟩ := hn
  refine ⟨x * y, mul_ne_zero hx0 hy0, ?_, fun Q hQP ↦ ?_⟩
  · rw [P.ord_mul hx0 hy0, hxP, hyP]
    push_cast
    ring
  · rw [Q.ord_mul hx0 hy0]
    exact add_nonneg (hx Q hQP) (hy Q hQP)

/-- A positive integer is a pole number exactly when the corresponding one-place
Riemann--Roch filtration has a strict dimension jump. -/
theorem isPoleNumber_iff_dim_lt (hF : IsFunctionField k F) (P : Place k F) {n : ℕ}
    (hn : 0 < n) :
    P.IsPoleNumber n ↔
      Divisor.dim (((n - 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P) <
        Divisor.dim ((n : ℤ) • WeilDivisor.ofPoint P) := by
  let D : Divisor k F := (n : ℤ) • WeilDivisor.ofPoint P
  let E : Divisor k F := ((n - 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P
  have hnsub : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have hED : E ≤ D :=
    zsmul_le_zsmul_left
      (WeilDivisor.isEffective_iff_zero_le.mp (WeilDivisor.isEffective_ofPoint P)) (by omega)
  constructor
  · rintro ⟨x, hx0, hxP, hxQ⟩
    have hxD : x ∈ riemannRochSpace D :=
      (mem_riemannRochSpace_iff_neg_le_ord hx0).mpr fun Q ↦ by
        rcases eq_or_ne Q P with rfl | hQP
        · simp only [D, WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_self, mul_one,
            hxP]
          exact le_rfl
        · simpa [D, WeilDivisor.coeff_ofPoint_of_ne hQP] using hxQ Q hQP
    have hxE : x ∉ riemannRochSpace E := by
      rw [mem_riemannRochSpace_iff_neg_le_ord hx0]
      push Not
      refine ⟨P, ?_⟩
      simp only [E, WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_self, mul_one, hnsub,
        hxP]
      omega
    have hlt : riemannRochSpace E < riemannRochSpace D :=
      SetLike.lt_iff_le_and_exists.mpr ⟨riemannRochSpace_mono hED, x, hxD, hxE⟩
    let _ := finiteDimensional_riemannRochSpace hF D
    simpa only [E, D, Divisor.dim_def] using Submodule.finrank_lt_finrank_of_lt hlt
  · intro hdim
    exact P.exists_ord_eq_neg_and_forall_ne_ord_nonneg_of_dim_lt hF hdim

/-- A positive integer is a gap exactly when the corresponding consecutive Riemann--Roch
dimensions are equal. -/
theorem isGap_iff_dim_eq (hF : IsFunctionField k F) (P : Place k F) {n : ℕ} (hn : 0 < n) :
    P.IsGap n ↔
      Divisor.dim ((n : ℤ) • WeilDivisor.ofPoint P) =
        Divisor.dim (((n - 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P) := by
  rw [IsGap, P.isPoleNumber_iff_dim_lt hF hn, not_lt]
  have hle :
      Divisor.dim (((n - 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P) ≤
        Divisor.dim ((n : ℤ) • WeilDivisor.ofPoint P) :=
    Divisor.dim_mono hF (zsmul_le_zsmul_left
      (WeilDivisor.isEffective_iff_zero_le.mp (WeilDivisor.isEffective_ofPoint P)) (by omega))
  omega

/-- At a rational place, adjoining one more allowed pole raises the Riemann--Roch dimension by
at most one. -/
theorem dim_succ_zsmul_ofPoint_le (hF : IsFunctionField k F) {P : Place k F}
    (hP : P.degree = 1) (n : ℕ) :
    Divisor.dim (((n + 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P) ≤
      Divisor.dim ((n : ℤ) • WeilDivisor.ofPoint P) + 1 := by
  have hle :
      (n : ℤ) • WeilDivisor.ofPoint P ≤ ((n + 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P :=
    zsmul_le_zsmul_left
      (WeilDivisor.isEffective_iff_zero_le.mp (WeilDivisor.isEffective_ofPoint P)) (by omega)
  have h := Divisor.dim_le_dim_add_degree_sub hF hle
  simp only [Divisor.degree_zsmul, Divisor.degree_ofPoint, hP, Nat.cast_one, mul_one] at h
  omega

/-- The gaps at `P` among the positive integers at most `n`. -/
noncomputable def gapNumbersUpTo (P : Place k F) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 n).filter P.IsGap

/-- Membership in `gapNumbersUpTo`: the gaps in `1, ..., n`. -/
@[simp]
theorem mem_gapNumbersUpTo_iff (P : Place k F) (m n : ℕ) :
    m ∈ P.gapNumbersUpTo n ↔ 1 ≤ m ∧ m ≤ n ∧ P.IsGap m := by
  classical
  simp only [gapNumbersUpTo, Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- Among the integers `1, ..., n` at a rational place, the number of gaps plus `ℓ(nP)` is
`n + 1`.  This is the counting identity underlying the Weierstrass gap theorem. -/
theorem card_gapNumbersUpTo_add_dim (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {P : Place k F} (hP : P.degree = 1) (n : ℕ) :
    (P.gapNumbersUpTo n).card +
        Divisor.dim ((n : ℤ) • WeilDivisor.ofPoint P) = n + 1 := by
  classical
  induction n with
  | zero =>
      simp [gapNumbersUpTo, Divisor.dim_zero_of_isIntegrallyClosedIn hF hex]
  | succ n ih =>
      simp only [gapNumbersUpTo] at ih
      have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext i
        simp
        omega
      have hnmem : n + 1 ∉ Finset.Icc 1 n := by simp
      have hdim_le := P.dim_succ_zsmul_ofPoint_le hF hP n
      have hdim_mono :
          Divisor.dim ((n : ℤ) • WeilDivisor.ofPoint P) ≤
            Divisor.dim (((n + 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P) :=
        Divisor.dim_mono hF (zsmul_le_zsmul_left
          (WeilDivisor.isEffective_iff_zero_le.mp (WeilDivisor.isEffective_ofPoint P)) (by omega))
      by_cases hgap : P.IsGap (n + 1)
      · have hdim_eq := (P.isGap_iff_dim_eq hF (by omega : 0 < n + 1)).mp hgap
        have hdim_eq' :
            Divisor.dim (((n + 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P) =
              Divisor.dim ((n : ℤ) • WeilDivisor.ofPoint P) := by
          simpa only [Nat.add_sub_cancel] using hdim_eq
        have hfilter :
            (Finset.Icc 1 (n + 1)).filter P.IsGap =
              insert (n + 1) ((Finset.Icc 1 n).filter P.IsGap) := by
          simp only [hIcc, Finset.filter_insert, hgap, ↓reduceIte]
        have hnotmemfilter : n + 1 ∉ (Finset.Icc 1 n).filter P.IsGap := by
          simp
        rw [gapNumbersUpTo, hfilter, Finset.card_insert_of_notMem hnotmemfilter]
        rw [hdim_eq']
        omega
      · have hdim_ne := (P.isGap_iff_dim_eq hF (by omega : 0 < n + 1)).not.mp hgap
        have hdim_ne' :
            Divisor.dim (((n + 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P) ≠
              Divisor.dim ((n : ℤ) • WeilDivisor.ofPoint P) := by
          simpa only [Nat.add_sub_cancel] using hdim_ne
        have hfilter :
            (Finset.Icc 1 (n + 1)).filter P.IsGap = (Finset.Icc 1 n).filter P.IsGap := by
          simp only [hIcc, Finset.filter_insert, hgap, ↓reduceIte]
        have hdim_succ :
            Divisor.dim (((n + 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P) =
              Divisor.dim ((n : ℤ) • WeilDivisor.ofPoint P) + 1 := by
          omega
        rw [gapNumbersUpTo, hfilter]
        rw [hdim_succ]
        omega

/-- The gaps at `P` in the interval `1, ..., 2g - 1`.  For a function field whose constants are
integrally closed this interval captures every gap, so it is the full set of Weierstrass gaps;
see `mem_weierstrassGaps_iff_isGap`. -/
noncomputable def weierstrassGaps (P : Place k F) : Finset ℕ :=
  P.gapNumbersUpTo (2 * genus k F - 1)

/-- Membership in the finite set of Weierstrass gaps, before using the theorem that its upper
bound captures every gap. -/
@[simp]
theorem mem_weierstrassGaps_iff (P : Place k F) (n : ℕ) :
    n ∈ P.weierstrassGaps ↔ 1 ≤ n ∧ n ≤ 2 * genus k F - 1 ∧ P.IsGap n :=
  P.mem_gapNumbersUpTo_iff n (2 * genus k F - 1)

/-- No integer at least `2g` is a gap: Riemann--Roch produces a function whose only pole is at
`P`, with the prescribed order. -/
theorem not_isGap_of_two_mul_genus_le (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (P : Place k F) {n : ℕ} (hn : 2 * genus k F ≤ n) :
    ¬ P.IsGap n := by
  rw [IsGap, not_not]
  exact P.exists_ord_eq_neg_and_forall_ne_ord_nonneg hF hex hn

/-- The displayed finite set captures every gap at a place of an exact function field. -/
theorem mem_weierstrassGaps_iff_isGap (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (P : Place k F) (n : ℕ) :
    n ∈ P.weierstrassGaps ↔ P.IsGap n := by
  rw [mem_weierstrassGaps_iff]
  refine ⟨fun h ↦ h.2.2, fun hgap ↦ ⟨?_, ?_, hgap⟩⟩
  · exact Nat.one_le_iff_ne_zero.mpr fun hn ↦ by
      subst n
      exact P.not_isGap_zero hgap
  · by_contra hn
    have hlarge : 2 * genus k F ≤ n := by omega
    exact P.not_isGap_of_two_mul_genus_le hF hex hlarge hgap

/-- **Weierstrass gap theorem** (Stichtenoth, Theorem 1.6.8): at a rational place of a function
field of genus `g`, there are exactly `g` gaps. -/
theorem card_weierstrassGaps (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {P : Place k F} (hP : P.degree = 1) :
    P.weierstrassGaps.card = genus k F := by
  have hcount := P.card_gapNumbersUpTo_add_dim hF hex hP (2 * genus k F - 1)
  have hdim := Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree
    hF hex (D := ((2 * genus k F - 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P) (by
      simp only [Divisor.degree_zsmul, Divisor.degree_ofPoint, hP, Nat.cast_one, mul_one]
      omega)
  simp only [weierstrassGaps, Divisor.degree_zsmul, Divisor.degree_ofPoint, hP, Nat.cast_one,
    mul_one] at hcount hdim ⊢
  omega

/-- At a rational place of a positive-genus function field, `1` is a gap. -/
theorem one_mem_weierstrassGaps (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {P : Place k F} (hP : P.degree = 1)
    (hg : 0 < genus k F) : 1 ∈ P.weierstrassGaps := by
  by_contra hone
  have hnotgap : ¬ P.IsGap 1 := fun hgap ↦ hone ((P.mem_weierstrassGaps_iff_isGap
    hF hex 1).mpr hgap)
  have hpole : P.IsPoleNumber 1 := not_not.mp (by simpa only [IsGap] using hnotgap)
  have hall : ∀ n : ℕ, P.IsPoleNumber n := by
    intro n
    induction n with
    | zero => exact P.isPoleNumber_zero
    | succ n ih => simpa [Nat.add_comm] using hpole.add ih
  have hempty : P.weierstrassGaps = ∅ := by
    ext n
    simp only [mem_weierstrassGaps_iff, Finset.notMem_empty, iff_false, not_and]
    intro _ _
    simpa only [IsGap, not_not] using hall n
  have hcard := P.card_weierstrassGaps hF hex hP
  rw [hempty, Finset.card_empty] at hcard
  omega

end Place

end TauCeti
