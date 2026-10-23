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
place of a function field with integrally closed constants and positive genus `g`, there are
exactly `g` gaps: the first is `1`, and every gap is at most `2g - 1`.  This is the Weierstrass
gap theorem, Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Theorem 1.6.8.

The proof counts the jumps in the filtration

`L(0) ⊆ L(P) ⊆ L(2P) ⊆ ...`.

At a rational place each step changes the dimension by at most one, and it changes the dimension
exactly when the index is a pole number.  Riemann--Roch computes `ℓ((2g - 1)P) = g`, so precisely
`g` of the first `2g - 1` steps do not change the dimension.

Pole numbers are closed under addition, so subtracting a pole number from a gap leaves a gap. Below
a gap `n` there are therefore at least as many gaps as positive pole numbers, and the `j`-th gap is
at most `2j - 1`. The **Weierstrass weight** `∑ⱼ (lⱼ - j)` of the gaps `l₁ < ⋯ < l_g` at a rational
place thus lies between `0` and `g (g - 1) / 2`. It is `0` exactly when the gaps are `1, …, g`, and
`g (g - 1) / 2` exactly when `2` is a pole number, in which case the gaps are `1, 3, …, 2g - 1`.

## Main definitions

* `TauCeti.Place.IsPoleNumber`: a natural number `n` witnessed by a nonzero function of order
  `-n` at the place and nonnegative order elsewhere.
* `TauCeti.Place.IsGap`: an integer which is not a pole number.
* `TauCeti.Place.gapNumbersUpTo`: the gaps in a prescribed finite interval.
* `TauCeti.Place.weierstrassGaps`: the finite set of gaps at a place.
* `TauCeti.Place.weierstrassWeight`: the Weierstrass weight `∑ⱼ (lⱼ - j)` of the gaps at a place.

## Main results

* `TauCeti.Place.isPoleNumber_iff_dim_lt`: pole numbers are exactly the strict jumps in the
  one-place Riemann--Roch filtration.
* `TauCeti.Place.card_gapNumbersUpTo_add_dim`: among `1, ..., n`, the number of gaps plus
  `ℓ(nP)` is `n + 1`.
* `TauCeti.Place.card_weierstrassGaps`: the Weierstrass gap theorem: a rational place of a
  function field with integrally closed constants and genus `g` has exactly `g` gaps.
* `TauCeti.Place.one_mem_weierstrassGaps`: the first gap is `1`.
* `TauCeti.Place.isGap_iff_exists_mem_riemannRochSpace_ord_eq`: for a divisor `W` satisfying the
  Riemann--Roch identity, `n` is a gap at a rational place `P` exactly when some nonzero section of
  `L(W)` has order `n - 1 - W(P)` at `P`.
* `TauCeti.Place.IsGap.sub_one_le_two_mul_card_gapNumbersUpTo`: below a gap `n` at least
  `(n - 1) / 2` numbers are gaps, so the `j`-th gap is at most `2j - 1`.
* `TauCeti.Place.weierstrassWeight_le_genus_choose_two`: the weight of a rational place is at most
  `g (g - 1) / 2`.
* `TauCeti.Place.weierstrassWeight_eq_zero_iff`: the weight of a rational place vanishes exactly
  when its gaps are `1, …, g`.
* `TauCeti.Place.weierstrassWeight_eq_genus_choose_two_iff`: the weight of a rational place is
  maximal exactly when `2` is a pole number there.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 1.6.8.
* H. M. Farkas and I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Springer, 1992, Section III.5,
  for the Weierstrass weight, its bound `g (g - 1) / 2`, and gaps as orders of regular
  differentials.
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

/-- A pole number is witnessed by a nonzero function of order `-n` at `P` and nonnegative
order at every other place. -/
theorem isPoleNumber_iff (P : Place k F) (n : ℕ) :
    P.IsPoleNumber n ↔
      ∃ x : F, x ≠ 0 ∧ P.ord x = -(n : ℤ) ∧
        ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord x :=
  Iff.rfl

/-- A natural number is a **gap** at `P` if it is not a pole number at `P`. -/
def IsGap (P : Place k F) (n : ℕ) : Prop :=
  ¬ P.IsPoleNumber n

/-- Being a gap at `P` is being a non-pole number at `P`. -/
@[simp]
theorem isGap_iff_not_isPoleNumber (P : Place k F) (n : ℕ) :
    P.IsGap n ↔ ¬ P.IsPoleNumber n :=
  Iff.rfl

/-- Zero is a pole number at every place, witnessed by the constant function `1`. -/
@[simp]
theorem isPoleNumber_zero (P : Place k F) : P.IsPoleNumber 0 := by
  refine ⟨1, one_ne_zero, ?_, fun Q _ ↦ ?_⟩ <;> simp

/-- Zero is never a gap at a place. -/
theorem not_isGap_zero (P : Place k F) : ¬ P.IsGap 0 := by
  simpa only [isGap_iff_not_isPoleNumber, not_not] using P.isPoleNumber_zero

/-- Pole numbers are closed under addition: multiply their witnessing functions. -/
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
      IsConcreteLE.lt_iff_le_and_exists.mpr ⟨riemannRochSpace_mono hED, x, hxD, hxE⟩
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
  rw [isGap_iff_not_isPoleNumber, P.isPoleNumber_iff_dim_lt hF hn, not_lt]
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
  rw [isGap_iff_not_isPoleNumber, not_not]
  exact P.exists_ord_eq_neg_and_forall_ne_ord_nonneg hF hex hn

/-- The displayed finite set captures every gap at a place of a function field with integrally
closed constants. -/
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
field with integrally closed constants and genus `g`, there are exactly `g` gaps. -/
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

/-- At a rational place of a positive-genus function field with integrally closed constants, `1`
is a gap. -/
theorem one_mem_weierstrassGaps (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {P : Place k F} (hP : P.degree = 1)
    (hg : 0 < genus k F) : 1 ∈ P.weierstrassGaps := by
  by_contra hone
  have hnotgap : ¬ P.IsGap 1 := fun hgap ↦ hone ((P.mem_weierstrassGaps_iff_isGap
    hF hex 1).mpr hgap)
  have hpole : P.IsPoleNumber 1 :=
    not_not.mp (by simpa only [isGap_iff_not_isPoleNumber] using hnotgap)
  have hall : ∀ n : ℕ, P.IsPoleNumber n := by
    intro n
    induction n with
    | zero => exact P.isPoleNumber_zero
    | succ n ih => simpa [Nat.add_comm] using hpole.add ih
  have hempty : P.weierstrassGaps = ∅ := by
    ext n
    simp only [mem_weierstrassGaps_iff, Finset.notMem_empty, iff_false, not_and]
    intro _ _
    simpa only [isGap_iff_not_isPoleNumber, not_not] using hall n
  have hcard := P.card_weierstrassGaps hF hex hP
  rw [hempty, Finset.card_empty] at hcard
  omega

/-! ### Gaps and the canonical divisor -/

/-- **Gaps are the jumps of the canonical filtration**: if `W` satisfies the Riemann--Roch
identity, then a positive integer `n` is a gap at a rational place `P` exactly when
`ℓ(W - nP) < ℓ(W - (n - 1)P)`. -/
theorem isGap_iff_dim_sub_lt (hF : IsFunctionField k F) {W : Divisor k F} {g₀ : ℕ}
    (hW : W.IsRiemannRochDivisor g₀) {P : Place k F} (hP : P.degree = 1) {n : ℕ}
    (hn : 0 < n) :
    P.IsGap n ↔
      Divisor.dim (W - (n : ℤ) • WeilDivisor.ofPoint P) <
        Divisor.dim (W - ((n - 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P) := by
  have h₁ := Divisor.isRiemannRochDivisor_iff.mp hW ((n : ℤ) • WeilDivisor.ofPoint P)
  have h₂ := Divisor.isRiemannRochDivisor_iff.mp hW (((n - 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P)
  simp only [Divisor.degree_zsmul, Divisor.degree_ofPoint, hP, Nat.cast_one, mul_one] at h₁ h₂
  have hmono :
      Divisor.dim (((n - 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P) ≤
        Divisor.dim ((n : ℤ) • WeilDivisor.ofPoint P) :=
    Divisor.dim_mono hF (zsmul_le_zsmul_left
      (WeilDivisor.isEffective_iff_zero_le.mp (WeilDivisor.isEffective_ofPoint P)) (by omega))
  rw [P.isGap_iff_dim_eq hF hn]
  omega

/-- **Gaps are the orders of canonical sections** (Farkas--Kra, Section III.5, in the
divisor language of `L(W)`): if `W` satisfies the Riemann--Roch identity, then a positive integer
`n` is a gap at a rational place `P` exactly when some nonzero `f ∈ L(W)` has order
`n - 1 - W(P)` at `P`. For `W` the divisor of a Weil differential `ω`, these `f` correspond to
the regular differentials `f ω` with a zero of order `n - 1` at `P`. -/
theorem isGap_iff_exists_mem_riemannRochSpace_ord_eq (hF : IsFunctionField k F)
    {W : Divisor k F} {g₀ : ℕ} (hW : W.IsRiemannRochDivisor g₀) {P : Place k F}
    (hP : P.degree = 1) {n : ℕ} (hn : 0 < n) :
    P.IsGap n ↔ ∃ f ∈ riemannRochSpace W, f ≠ 0 ∧ P.ord f = n - 1 - W.coeff P := by
  set E : Divisor k F := W - ((n - 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P with hE
  have hP0 : (0 : Divisor k F) ≤ WeilDivisor.ofPoint P :=
    WeilDivisor.isEffective_iff_zero_le.mp (WeilDivisor.isEffective_ofPoint P)
  have hsub : W - (n : ℤ) • WeilDivisor.ofPoint P = E - WeilDivisor.ofPoint P := by
    rw [hE, Nat.cast_sub hn, Nat.cast_one, sub_smul, one_smul]
    abel
  have hEP : E.coeff P = W.coeff P - (n - 1) := by
    simp only [hE, WeilDivisor.coeff_sub, WeilDivisor.coeff_zsmul,
      WeilDivisor.coeff_ofPoint_self, mul_one]
    omega
  have hEQ : ∀ Q, Q ≠ P → E.coeff Q = W.coeff Q := fun Q hQP ↦ by
    simp [hE, WeilDivisor.coeff_ofPoint_of_ne hQP]
  have hle : riemannRochSpace (E - WeilDivisor.ofPoint P) ≤ riemannRochSpace E :=
    riemannRochSpace_mono (sub_le_self _ hP0)
  have := finiteDimensional_riemannRochSpace hF E
  rw [P.isGap_iff_dim_sub_lt hF hW hP hn, hsub, Divisor.dim_def, Divisor.dim_def]
  constructor
  · intro hlt
    obtain ⟨f, hfE, hfnot⟩ :=
      IsConcreteLE.exists_of_lt (Submodule.lt_of_le_of_finrank_lt_finrank hle hlt)
    refine ⟨f, riemannRochSpace_mono (sub_le_self _ (zsmul_nonneg hP0 (by omega))) hfE, ?_, ?_⟩
    · rintro rfl
      exact hfnot (Submodule.zero_mem _)
    · rw [Divisor.ord_eq_neg_coeff_of_not_mem_sub_ofPoint hfE hfnot, hEP]
      ring
  · rintro ⟨f, hfW, hf0, hford⟩
    have hfW' := (mem_riemannRochSpace_iff_neg_le_ord hf0).mp hfW
    have hfE : f ∈ riemannRochSpace E := by
      refine (mem_riemannRochSpace_iff_neg_le_ord hf0).mpr fun Q ↦ ?_
      rcases eq_or_ne Q P with rfl | hQP
      · rw [hEP, hford]
        omega
      · rw [hEQ Q hQP]
        exact hfW' Q
    have hfnot : f ∉ riemannRochSpace (E - WeilDivisor.ofPoint P) := fun h ↦ by
      have hPord := (mem_riemannRochSpace_iff_neg_le_ord hf0).mp h P
      rw [WeilDivisor.coeff_sub, WeilDivisor.coeff_ofPoint_self, hEP, hford] at hPord
      omega
    exact Submodule.finrank_lt_finrank_of_lt
      (IsConcreteLE.lt_iff_le_and_exists.mpr ⟨hle, f, hfE, hfnot⟩)

/-! ### Gaps below a gap -/

/-- **Subtracting a pole number from a gap leaves a gap**: if `n` is a gap at `P` and `m ≤ n` is a
pole number, then `n - m` is a gap, for otherwise `n = m + (n - m)` would be a pole number. -/
theorem IsGap.isGap_sub {P : Place k F} {m n : ℕ} (hn : P.IsGap n) (hm : P.IsPoleNumber m)
    (hmn : m ≤ n) : P.IsGap (n - m) := fun h ↦
  hn (Nat.add_sub_of_le hmn ▸ hm.add h)

/-- **Below a gap there are at least as many gaps as positive pole numbers**, since `m ↦ n - m`
sends the positive pole numbers below the gap `n` injectively to gaps below `n`. Hence
`n - 1 ≤ 2 · #{gaps in 1, …, n - 1}`: the `j`-th gap is at most `2j - 1`. -/
theorem IsGap.sub_one_le_two_mul_card_gapNumbersUpTo {P : Place k F} {n : ℕ} (hn : P.IsGap n) :
    n - 1 ≤ 2 * (P.gapNumbersUpTo (n - 1)).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 (n - 1)) P.IsGap
  have hpoles : ((Finset.Icc 1 (n - 1)).filter fun m ↦ ¬ P.IsGap m).card ≤
      (P.gapNumbersUpTo (n - 1)).card := by
    refine Finset.card_le_card_of_injOn (n - ·) (fun m hm ↦ ?_) fun a ha b hb hab ↦ ?_
    · simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq, isGap_iff_not_isPoleNumber,
        not_not] at hm
      simp only [Finset.mem_coe, mem_gapNumbersUpTo_iff]
      exact ⟨by omega, by omega, hn.isGap_sub hm.2 (by omega)⟩
    · simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at ha hb
      simp only at hab
      omega
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hsplit
  have hgaps : (P.gapNumbersUpTo (n - 1)).card = ((Finset.Icc 1 (n - 1)).filter P.IsGap).card := by
    rw [gapNumbersUpTo]
  omega

/-! ### Weierstrass weights -/

private theorem gapNumbersUpTo_zero (P : Place k F) : P.gapNumbersUpTo 0 = ∅ := by
  ext m
  simp only [mem_gapNumbersUpTo_iff, Finset.notMem_empty, iff_false]
  omega

private theorem gapNumbersUpTo_succ_of_isGap {P : Place k F} {N : ℕ} (h : P.IsGap (N + 1)) :
    P.gapNumbersUpTo (N + 1) = insert (N + 1) (P.gapNumbersUpTo N) := by
  rw [gapNumbersUpTo, gapNumbersUpTo, ← Finset.insert_Icc_right_eq_Icc_add_one (by omega),
    Finset.filter_insert]
  exact ite_eq_left h

private theorem gapNumbersUpTo_succ_of_not_isGap {P : Place k F} {N : ℕ}
    (h : ¬ P.IsGap (N + 1)) : P.gapNumbersUpTo (N + 1) = P.gapNumbersUpTo N := by
  rw [gapNumbersUpTo, gapNumbersUpTo, ← Finset.insert_Icc_right_eq_Icc_add_one (by omega),
    Finset.filter_insert]
  exact ite_eq_right h

private theorem succ_notMem_gapNumbersUpTo (P : Place k F) (N : ℕ) :
    N + 1 ∉ P.gapNumbersUpTo N := by
  simp

private theorem card_gapNumbersUpTo_le (P : Place k F) (N : ℕ) :
    (P.gapNumbersUpTo N).card ≤ N := by
  classical
  simpa [gapNumbersUpTo] using Finset.card_filter_le (Finset.Icc 1 N) P.IsGap

/-- The sum of the gaps up to `N`, minus `(c + 1).choose 2` for their number `c`, can only grow
with `N`: a new gap `N + 1` raises the sum by `N + 1` and the binomial by `c + 1 ≤ N + 1`. -/
private theorem choose_two_add_sum_gapNumbersUpTo_le (P : Place k F) {N M : ℕ} (hNM : N ≤ M) :
    ((P.gapNumbersUpTo M).card + 1).choose 2 + ∑ n ∈ P.gapNumbersUpTo N, n ≤
      ((P.gapNumbersUpTo N).card + 1).choose 2 + ∑ n ∈ P.gapNumbersUpTo M, n := by
  induction M, hNM using Nat.le_induction with
  | base => exact le_rfl
  | succ M hNM ih =>
    by_cases h : P.IsGap (M + 1)
    · have hM := card_gapNumbersUpTo_le P M
      rw [gapNumbersUpTo_succ_of_isGap h,
        Finset.card_insert_of_notMem (succ_notMem_gapNumbersUpTo P M),
        Finset.sum_insert (succ_notMem_gapNumbersUpTo P M),
        Nat.choose_succ_succ' ((P.gapNumbersUpTo M).card + 1) 1, Nat.choose_one_right]
      simp only [Nat.reduceAdd]
      omega
    · rwa [gapNumbersUpTo_succ_of_not_isGap h]

/-- The square of the number `c` of gaps up to `N`, minus their sum, can only grow with `N`: a new
gap `N + 1` raises the square by `2c + 1 ≥ N + 1`, by
`TauCeti.Place.IsGap.sub_one_le_two_mul_card_gapNumbersUpTo`. -/
private theorem sq_add_sum_gapNumbersUpTo_le (P : Place k F) {N M : ℕ} (hNM : N ≤ M) :
    (P.gapNumbersUpTo N).card ^ 2 + ∑ n ∈ P.gapNumbersUpTo M, n ≤
      (P.gapNumbersUpTo M).card ^ 2 + ∑ n ∈ P.gapNumbersUpTo N, n := by
  induction M, hNM using Nat.le_induction with
  | base => exact le_rfl
  | succ M hNM ih =>
    by_cases h : P.IsGap (M + 1)
    · have hM := h.sub_one_le_two_mul_card_gapNumbersUpTo
      rw [Nat.add_sub_cancel] at hM
      rw [gapNumbersUpTo_succ_of_isGap h,
        Finset.card_insert_of_notMem (succ_notMem_gapNumbersUpTo P M),
        Finset.sum_insert (succ_notMem_gapNumbersUpTo P M), add_sq]
      omega
    · rwa [gapNumbersUpTo_succ_of_not_isGap h]

/-- If the gaps up to `N` have the least possible sum, they are an initial segment `1, …, c`. -/
private theorem gapNumbersUpTo_eq_Icc_of_sum_eq (P : Place k F) (N : ℕ)
    (h : ∑ n ∈ P.gapNumbersUpTo N, n = ((P.gapNumbersUpTo N).card + 1).choose 2) :
    P.gapNumbersUpTo N = Finset.Icc 1 (P.gapNumbersUpTo N).card := by
  induction N with
  | zero => simp [gapNumbersUpTo_zero]
  | succ N ih =>
    by_cases hN : P.IsGap (N + 1)
    · have hlow := choose_two_add_sum_gapNumbersUpTo_le P (Nat.zero_le N)
      have hle := card_gapNumbersUpTo_le P N
      simp [gapNumbersUpTo_zero] at hlow
      rw [gapNumbersUpTo_succ_of_isGap hN,
        Finset.card_insert_of_notMem (succ_notMem_gapNumbersUpTo P N),
        Finset.sum_insert (succ_notMem_gapNumbersUpTo P N),
        Nat.choose_succ_succ' ((P.gapNumbersUpTo N).card + 1) 1, Nat.choose_one_right] at h
      simp only [Nat.reduceAdd] at h
      rw [gapNumbersUpTo_succ_of_isGap hN,
        Finset.card_insert_of_notMem (succ_notMem_gapNumbersUpTo P N)]
      have hc : (P.gapNumbersUpTo N).card = N := by omega
      rw [ih (by omega), hc, Nat.card_Icc, Nat.add_sub_cancel]
      ext m
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    · rw [gapNumbersUpTo_succ_of_not_isGap hN] at h ⊢
      exact ih h

/-- The **Weierstrass weight** of a place `P`: if `l₁ < ⋯ < l_c` are the Weierstrass gaps at `P`,
it is `∑ⱼ (lⱼ - j) = (l₁ + ⋯ + l_c) - c (c + 1) / 2`.

It measures how far the gap sequence is from `1, …, c`: at a rational place of a function field
with exact constants, `c` is the genus `g`, the weight vanishes exactly when the gaps are
`1, …, g` (`TauCeti.Place.weierstrassWeight_eq_zero_iff`), and it is at most `g (g - 1) / 2`
(`TauCeti.Place.weierstrassWeight_le_genus_choose_two`). -/
def weierstrassWeight (P : Place k F) : ℕ :=
  ∑ n ∈ P.weierstrassGaps, n - (P.weierstrassGaps.card + 1).choose 2

/-- The Weierstrass weight and `(c + 1).choose 2`, for the number `c` of gaps, add up to the sum
of the gaps; the subtraction defining the weight does not truncate. -/
theorem weierstrassWeight_add_card_add_one_choose_two (P : Place k F) :
    P.weierstrassWeight + (P.weierstrassGaps.card + 1).choose 2 = ∑ n ∈ P.weierstrassGaps, n := by
  have h := choose_two_add_sum_gapNumbersUpTo_le P (Nat.zero_le (2 * genus k F - 1))
  simp only [gapNumbersUpTo_zero, Finset.card_empty, Finset.sum_empty] at h
  exact Nat.sub_add_cancel (by simpa [weierstrassGaps] using h)

/-- The weight in terms of `c²` for the number `c` of gaps, using
`(c + 1).choose 2 + c.choose 2 = c²`. -/
private theorem weierstrassWeight_add_sq (P : Place k F) :
    P.weierstrassWeight + P.weierstrassGaps.card ^ 2 =
      P.weierstrassGaps.card.choose 2 + ∑ n ∈ P.weierstrassGaps, n := by
  have hsq : ∀ c : ℕ, (c + 1).choose 2 + c.choose 2 = c ^ 2 := fun c ↦ by
    induction c with
    | zero => rfl
    | succ c ih =>
      rw [Nat.choose_succ_succ' (c + 1) 1, Nat.choose_succ_succ' c 1, Nat.choose_one_right,
        Nat.choose_one_right] at *
      nlinarith [ih]
  rw [← P.weierstrassWeight_add_card_add_one_choose_two, ← hsq]
  ring

/-- The gaps at any place sum to at most `c²` for their number `c`: the `j`-th gap is at most
`2j - 1` (`TauCeti.Place.IsGap.sub_one_le_two_mul_card_gapNumbersUpTo`). -/
private theorem sum_weierstrassGaps_le_sq (P : Place k F) :
    ∑ n ∈ P.weierstrassGaps, n ≤ P.weierstrassGaps.card ^ 2 := by
  simpa [gapNumbersUpTo_zero, weierstrassGaps] using
    sq_add_sum_gapNumbersUpTo_le P (Nat.zero_le (2 * genus k F - 1))

/-- **The Weierstrass weight is at most `c (c - 1) / 2`** for the number `c` of gaps, at every
place: the `j`-th gap is at most `2j - 1`
(`TauCeti.Place.IsGap.sub_one_le_two_mul_card_gapNumbersUpTo`), so the gaps sum to at most
`1 + 3 + ⋯ + (2c - 1) = c²`. -/
theorem weierstrassWeight_le_card_choose_two (P : Place k F) :
    P.weierstrassWeight ≤ P.weierstrassGaps.card.choose 2 := by
  have := P.weierstrassWeight_add_sq
  have := P.sum_weierstrassGaps_le_sq
  omega

/-- **The Weierstrass weight of a rational place is at most `g (g - 1) / 2`**, for a function field
of genus `g` with exact constants. -/
theorem weierstrassWeight_le_genus_choose_two (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {P : Place k F} (hP : P.degree = 1) :
    P.weierstrassWeight ≤ (genus k F).choose 2 :=
  P.card_weierstrassGaps hF hex hP ▸ P.weierstrassWeight_le_card_choose_two

/-- **A place has Weierstrass weight zero exactly when its gaps are `1, …, c`**, for the number
`c` of gaps. -/
theorem weierstrassWeight_eq_zero_iff_card (P : Place k F) :
    P.weierstrassWeight = 0 ↔ P.weierstrassGaps = Finset.Icc 1 P.weierstrassGaps.card := by
  have hadd := P.weierstrassWeight_add_card_add_one_choose_two
  constructor
  · intro hw
    exact P.gapNumbersUpTo_eq_Icc_of_sum_eq (2 * genus k F - 1) (by rw [← weierstrassGaps]; omega)
  · intro hgaps
    rw [hgaps, Nat.card_Icc, Nat.add_sub_cancel] at hadd
    have hsum := Nat.sum_Icc_choose P.weierstrassGaps.card 1
    simp only [Nat.choose_one_right, Nat.reduceAdd] at hsum
    omega

/-- **A rational place has Weierstrass weight zero exactly when its gaps are `1, …, g`**, for a
function field of genus `g` with exact constants. -/
theorem weierstrassWeight_eq_zero_iff (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {P : Place k F} (hP : P.degree = 1) :
    P.weierstrassWeight = 0 ↔ P.weierstrassGaps = Finset.Icc 1 (genus k F) := by
  rw [weierstrassWeight_eq_zero_iff_card, P.card_weierstrassGaps hF hex hP]

/-- **The gaps at a rational place where `2` is a pole number are `1, 3, …, 2g - 1`**, for a
function field of genus `g` with exact constants: every even number is then a pole number, and the
gap theorem leaves exactly `g` gaps below `2g`. -/
theorem weierstrassGaps_eq_image_range_of_isPoleNumber_two (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {P : Place k F} (hP : P.degree = 1)
    (h2 : P.IsPoleNumber 2) :
    P.weierstrassGaps = (Finset.range (genus k F)).image fun i ↦ 2 * i + 1 := by
  have heven : ∀ j : ℕ, P.IsPoleNumber (2 * j) := by
    intro j
    induction j with
    | zero => exact P.isPoleNumber_zero
    | succ j ih => simpa [mul_add, add_comm] using h2.add ih
  refine Finset.eq_of_subset_of_card_le (fun n hn ↦ ?_) ?_
  · -- A gap lies in `1, …, 2g - 1` and is odd, since every even number is a pole number.
    rw [P.mem_weierstrassGaps_iff] at hn
    obtain ⟨hn1, hn2, hgap⟩ := hn
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' n
    · exact absurd (heven i) ((P.isGap_iff_not_isPoleNumber _).mp hgap)
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  · rw [card_weierstrassGaps hF hex hP, Finset.card_image_of_injective _
      (fun a b h ↦ by simpa using h), Finset.card_range]

/-- **A rational place has the maximal Weierstrass weight `g (g - 1) / 2` exactly when `2` is a
pole number there**, for a function field of genus `g` with exact constants; the gaps are then
`1, 3, …, 2g - 1`. For `g ≥ 2` such a place makes the function field hyperelliptic, see
`TauCeti.isHyperellipticFunctionField_of_isPoleNumber_two`. -/
theorem weierstrassWeight_eq_genus_choose_two_iff (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {P : Place k F} (hP : P.degree = 1) :
    P.weierstrassWeight = (genus k F).choose 2 ↔ P.IsPoleNumber 2 := by
  have hsq := P.weierstrassWeight_add_sq
  rw [P.card_weierstrassGaps hF hex hP] at hsq
  constructor
  · -- If `2` is a gap, so is `1`, and the gaps `1, 2` up to `2` already sum to less than `2²`.
    intro hw
    by_contra h2
    have h1 : P.IsGap 1 := fun h1 ↦ h2 (h1.add h1)
    have hmem := (P.mem_weierstrassGaps_iff_isGap hF hex 2).mpr h2
    have hle : 2 ≤ 2 * genus k F - 1 := ((P.mem_weierstrassGaps_iff 2).mp hmem).2.1
    have hmono := sq_add_sum_gapNumbersUpTo_le P hle
    rw [← weierstrassGaps, P.card_weierstrassGaps hF hex hP,
      gapNumbersUpTo_succ_of_isGap (N := 1) h2, gapNumbersUpTo_succ_of_isGap (N := 0) h1,
      gapNumbersUpTo_zero] at hmono
    simp at hmono
    omega
  · intro h2
    rw [weierstrassGaps_eq_image_range_of_isPoleNumber_two hF hex hP h2,
      Finset.sum_image fun a _ b _ h ↦ by simpa using h] at hsq
    have hodd : ∀ c : ℕ, ∑ i ∈ Finset.range c, (2 * i + 1) = c ^ 2 := fun c ↦ by
      induction c with
      | zero => rfl
      | succ c ih => rw [Finset.sum_range_succ, ih]; ring
    rw [hodd] at hsq
    omega

end Place

end TauCeti
