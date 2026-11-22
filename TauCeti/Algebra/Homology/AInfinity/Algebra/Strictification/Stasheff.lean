/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.CohomologicalUnit
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Gauge
public import TauCeti.LinearAlgebra.TensorCoalgebra.Degenerate

/-!
# The Stasheff identity on duplicated-unit words

Let `𝒜` be a minimal `A∞` algebra with cohomological unit `e` satisfying `KillsUnitUpTo 𝒜 e (m + 2)`
and `KillsUnitBeforeSlot 𝒜 e (m + 3) j`. Given an `(m + 3)`-tuple `w` with `w j = e`, duplicating
`e` at `j` produces `duplicateAt e j w`, in whose Stasheff identity `0 = m(b(duplicateAt e j w))`:
* unary and top collapses vanish by minimality, and intermediate non-binary collapses of length
  `≤ m + 2` vanish by `KillsUnitUpTo` because a copy of `e` lies inside or survives outside;
* binary collapses before `j - 1` vanish by `KillsUnitBeforeSlot`, while those at `j - 1` and `j`
  cancel (`IsMinimal.negOnePowCast_smul_splice_two_add_succ_eq_zero`), leaving `m(w)` at `j = 0` to
  cancel the tail `(m + 3)`-collapse `-m(w)`.

Only the initial `(m + 3)`-collapse and the binary collapses from `j + 1` onward survive
(`IsMinimal.taylor_barDifferential_duplicateAt`). At `j = m + 2` this forces vanishing in the final
slot (`IsMinimal.taylor_of_tprod_last_eq_zero`), and for `j < m + 2` it matches the unit-killing
coboundary in `TauCeti.Algebra.Homology.AInfinity.Algebra.Strictification.UnitKilling`.

## Main definitions

* `TauCeti.AInfinityAlgebra.KillsUnitUpTo` and `TauCeti.AInfinityAlgebra.KillsUnitBeforeSlot`:
  arity- and slot-bounded vanishing of `𝒜.taylor` on pure tensor words containing `e`.

## Main results

* `TauCeti.AInfinityAlgebra.IsMinimal.negOnePowCast_smul_splice_two_add_succ_eq_zero`: adjacent
  binary-collapse terms of `gradedCoderiv` around an interior cohomological unit cancel.
* `TauCeti.AInfinityAlgebra.IsMinimal.taylor_barDifferential_duplicateAt`: reduced Stasheff
  identity on `duplicateAt e j w`.
* `TauCeti.AInfinityAlgebra.IsMinimal.taylor_of_tprod_last_eq_zero`: automatic vanishing of `e` in
  the final slot of arity `m + 3`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1, 3.3, and 3.6.
* K. Lefèvre-Hasegawa, *Sur les `A∞`-catégories*, Ph.D. thesis, Université Paris 7 (2003), Ch. 3.
* P. Seidel, *Fukaya Categories and Picard--Lefschetz Theory* (2008), Chapter I, Section 2.
-/

public section

namespace TauCeti.AInfinityAlgebra

open ReducedTensorWords

universe uR uA

section Stasheff

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-! ### Arity- and slot-bounded unit-vanishing predicates -/

/-- `𝒜.taylor` vanishes on pure tensor words of length `k ≠ 2` with `k ≤ n` containing `e`. -/
def KillsUnitUpTo (𝒜 : AInfinityAlgebra R A) (e : A) (n : ℕ) : Prop :=
  ∀ (k : {k : ℕ // 0 < k}), k.val ≠ 2 → k.val ≤ n → ∀ x : Fin k.val → A,
    (∃ r, x r = e) → 𝒜.taylor (of R A k (PiTensorProduct.tprod R x)) = 0

/-- Unfolding `KillsUnitUpTo`. -/
theorem killsUnitUpTo_iff {𝒜 : AInfinityAlgebra R A} {e : A} {n : ℕ} :
    𝒜.KillsUnitUpTo e n ↔ ∀ (k : {k : ℕ // 0 < k}), k.val ≠ 2 → k.val ≤ n → ∀ x : Fin k.val → A,
      (∃ r, x r = e) → 𝒜.taylor (of R A k (PiTensorProduct.tprod R x)) = 0 := Iff.rfl

/-- `KillsUnitUpTo` is antitone in the arity bound. -/
theorem KillsUnitUpTo.mono {𝒜 : AInfinityAlgebra R A} {e : A} {m n : ℕ}
    (h : 𝒜.KillsUnitUpTo e n) (hmn : m ≤ n) : 𝒜.KillsUnitUpTo e m :=
  fun k hk2 hkm ↦ h k hk2 (hkm.trans hmn)

/-- `KillsUnitUpTo e n` transfers across `A∞` structures whose Taylor maps agree on
`filtration n`. -/
theorem KillsUnitUpTo.of_taylor_eq {𝒜 𝒜' : AInfinityAlgebra R A} {e : A} {n : ℕ}
    (h : 𝒜.KillsUnitUpTo e n) (htay : ∀ z ∈ filtration R A n, 𝒜'.taylor z = 𝒜.taylor z) :
    𝒜'.KillsUnitUpTo e n :=
  fun k hk2 hkn x hx ↦ (htay _ (of_mem_filtration R A hkn _)).trans (h k hk2 hkn x hx)

/-- Every minimal `A∞` algebra satisfies `KillsUnitUpTo e 2`, since `m₁ = 0`. -/
theorem IsMinimal.killsUnitUpTo_two {𝒜 : AInfinityAlgebra R A} (h𝒜 : 𝒜.IsMinimal) (e : A) :
    𝒜.KillsUnitUpTo e 2 := by
  rintro ⟨kval, _⟩ hk2 hkle _ _
  obtain rfl : kval = 1 := by dsimp only at hk2 hkle; omega
  rw [taylor_of_tprod, h𝒜.m_one]

/-- `𝒜.taylor` vanishes on pure tensor words of length `n` carrying `e` strictly before `r`. -/
def KillsUnitBeforeSlot (𝒜 : AInfinityAlgebra R A) (e : A) (n : ℕ) [NeZero n] (r : ℕ) : Prop :=
  ∀ (x : Fin n → A) (k : Fin n), k.val < r → x k = e →
    𝒜.taylor (of R A ⟨n, NeZero.pos n⟩ (PiTensorProduct.tprod R x)) = 0

/-- Unfolding `KillsUnitBeforeSlot`. -/
theorem killsUnitBeforeSlot_iff {𝒜 : AInfinityAlgebra R A} {e : A} {n : ℕ} [NeZero n] {r : ℕ} :
    𝒜.KillsUnitBeforeSlot e n r ↔ ∀ (x : Fin n → A) (k : Fin n), k.val < r → x k = e →
      𝒜.taylor (of R A ⟨n, NeZero.pos n⟩ (PiTensorProduct.tprod R x)) = 0 := Iff.rfl

/-- Vacuous base case `r = 0` of `KillsUnitBeforeSlot`. -/
theorem killsUnitBeforeSlot_zero (𝒜 : AInfinityAlgebra R A) (e : A) (n : ℕ) [NeZero n] :
    𝒜.KillsUnitBeforeSlot e n 0 := fun _ _ hk ↦ absurd hk (Nat.not_lt_zero _)

/-! ### Cancellation of adjacent binary collapses around an interior unit -/

/-- In a minimal `A∞` algebra with cohomological unit `e`, if an `(n + 1)`-tuple `x` of suspended
degrees `𝒟` has `e` at an interior slot `p + 1 < n`, then the adjacent binary-collapse terms of the
bar differential at positions `p` and `p + 1` cancel. -/
theorem IsMinimal.negOnePowCast_smul_splice_two_add_succ_eq_zero {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} (he : 𝒜.CohomologicalUnit e) {n p : ℕ} (hpn : p + 1 < n)
    {x : Fin (n + 1) → A} {𝒟 : Fin (n + 1) → ℤ}
    (hxp : x ⟨p, by omega⟩ ∈ (𝒜.grading.shift 1).piece (𝒟 ⟨p, by omega⟩))
    (hxe : x ⟨p + 1, by omega⟩ = e) :
    negOnePowCast R (∑ r ∈ Finset.range p, if h : r < n + 1 then 𝒟 ⟨r, h⟩ else 0) •
        splice R x 0 (n + 1) p 2 (𝒜.taylor (subword R x p 2)) +
      negOnePowCast R (∑ r ∈ Finset.range (p + 1), if h : r < n + 1 then 𝒟 ⟨r, h⟩ else 0) •
        splice R x 0 (n + 1) (p + 1) 2 (𝒜.taylor (subword R x (p + 1) 2)) = 0 := by
  -- Collapsing `[x_p, e]` picks up the Koszul twist `(-1)^{𝒟_p + 1}` on `x_p`.
  have hp_val : 𝒜.taylor (subword R x p 2) =
      negOnePowCast R (𝒟 ⟨p, by omega⟩ + 1) • x ⟨p, by omega⟩ := by
    rw [subword_two_eq R x (by omega), hxe, h𝒜.taylor_of_two_cohomologicalUnit_right he,
      𝒜.grading.koszulTwist_one_apply_of_mem
        (by simpa only [InternalGrading.shift_piece] using hxp), negOnePowCast_eq_intCast]
  -- Collapsing `[e, x_{p+2}]` gives `x_{p+2}`, producing the same spliced word with opposite sign.
  have hsucc_val : 𝒜.taylor (subword R x (p + 1) 2) = x ⟨p + 1 + 1, by omega⟩ := by
    rw [subword_two_eq R x (by omega), hxe, h𝒜.taylor_of_two_cohomologicalUnit_left he]
  rw [hp_val, splice_smul, smul_smul, ← negOnePowCast_add, hsucc_val,
    splice_two_succ_eq_splice_two_pred R (Nat.succ_pos p) hpn x, Finset.sum_range_succ,
    dite_eq_left (by omega : p < n + 1), ← add_assoc, negOnePowCast_add _ 1, negOnePowCast_one,
    mul_neg_one, neg_smul]
  exact neg_add_cancel _

/-! ### Stasheff identity on duplicated-unit words -/

/-- Non-binary, non-`(m + 3)` collapses of `duplicateAt e j w` vanish. -/
private theorem taylor_splice_duplicateAt_eq_zero_of_ne {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} {m : ℕ} (hlow : 𝒜.KillsUnitUpTo e (m + 2)) (j : Fin (m + 3))
    (w : Fin (m + 3) → A) {p d : ℕ} (hd : d < m + 5) (hd2 : d ≠ 2) (hdm3 : d ≠ m + 3) :
    𝒜.taylor (splice R (duplicateAt e j w) 0 (m + 4) p d
      (𝒜.taylor (subword R (duplicateAt e j w) p d))) = 0 := by
  -- Non-fitting collapses have zero `splice`.
  by_cases hfit : 0 < d ∧ p + d ≤ m + 4
  swap
  · rw [splice_eq_zero_of_not_fits R _ _ hfit, map_zero]
  -- Unary collapses (`d = 1`) vanish because `𝒜` is minimal.
  by_cases hd1 : d = 1
  · subst hd1
    have hz : 𝒜.taylor (subword R (duplicateAt e j w) p 1) = 0 := by
      rw [subword_eq_of_tprod R _ one_pos hfit.2]
      exact h𝒜.taylor_apply_eq_zero_of_mem_filtration_one _
        (of_mem_filtration R A (k := ⟨1, one_pos⟩) le_rfl _)
    rw [hz, splice_zero, map_zero]
  -- Top collapses (`d = m + 4`) leave a 1-letter word, so the outer `𝒜.taylor` vanishes.
  by_cases hdm4 : d = m + 4
  · subst hdm4
    rw [splice_eq_of_tprod R _ _ hfit.1 hfit.2 (by omega)]
    exact h𝒜.taylor_apply_eq_zero_of_mem_filtration_one _
      (of_mem_filtration R A (by dsimp only; omega) _)
  -- Intermediate collapses (`d ≤ m + 2`, `d ≠ 2`): the copy of `e` at `j.castSucc` either lies
  -- inside the collapsed block or survives outside in a non-binary word of length `≤ m + 2`.
  have hdle : d ≤ m + 2 := by omega
  have heY : duplicateAt e j w j.castSucc = e := duplicateAt_castSucc e j w
  by_cases hblock : p ≤ j.val ∧ j.val < p + d
  · have hz : 𝒜.taylor (subword R (duplicateAt e j w) p d) = 0 := by
      rw [subword_eq_of_tprod R _ hfit.1 hfit.2]
      exact hlow ⟨d, hfit.1⟩ hd2 hdle _ ⟨⟨j.val - p, by dsimp only; omega⟩, (congrArg _
        (Fin.ext (by rw [Fin.val_mk, Fin.val_mk, Fin.val_castSucc]; omega))).trans heY⟩
    rw [hz, splice_zero, map_zero]
  · obtain ⟨u, ⟨r, hr⟩, hsp⟩ := exists_splice_eq_of_tprod R (duplicateAt e j w) hfit.2
      (𝒜.taylor (subword R (duplicateAt e j w) p d)) (i := j.castSucc) (by simpa using hblock)
    rw [hsp]
    exact hlow ⟨m + 5 - d, by omega⟩ (by dsimp only; omega) (by dsimp only; omega) u
      ⟨r, hr.trans heY⟩

/-- Length-`(m + 3)` collapses of `duplicateAt e j w` at `p = 0` and `p = 1`. -/
private theorem taylor_barDifferential_duplicateAt_m_add_three {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} (he : 𝒜.CohomologicalUnit e) {m : ℕ} (j : Fin (m + 3))
    (hIH : 𝒜.KillsUnitBeforeSlot e (m + 3) j.val) {w : Fin (m + 3) → A} (𝒟 : Fin (m + 3) → ℤ)
    (hwj : w j = e) {p : ℕ} :
    negOnePowCast R (∑ r ∈ Finset.range p,
        if h : r < m + 4 then duplicateAt (-1 : ℤ) j 𝒟 ⟨r, h⟩ else 0) •
      𝒜.taylor (splice R (duplicateAt e j w) 0 (m + 4) p (m + 3)
        (𝒜.taylor (subword R (duplicateAt e j w) p (m + 3)))) =
      (if p = 0 then 𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
        ![𝒜.taylor (subword R (duplicateAt e j w) 0 (m + 3)),
          duplicateAt e j w (Fin.last (m + 3))])) else 0) +
      (if p = 1 ∧ j.val = 0 then -𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w))
       else 0) := by
  have hjlt := j.isLt
  by_cases hfit : 0 < m + 3 ∧ p + (m + 3) ≤ m + 4
  swap
  · simp (disch := omega) only [splice_eq_zero_of_not_fits R _ _ hfit, map_zero, smul_zero,
      ite_eq_right, add_zero]
  rcases Nat.eq_zero_or_pos p with rfl | hppos
  · -- Initial `(m + 3)`-collapse (`p = 0`).
    rw [ite_eq_left rfl, ite_eq_right (by omega), add_zero, Finset.sum_range_zero,
      negOnePowCast_zero, one_smul, splice_collapse_init_eq R (by omega : 0 < m + 3)]
  · -- Tail `(m + 3)`-collapse (`p = 1`): survives as `-m(w)` at `j = 0`, vanishes for `j ≥ 1`.
    obtain rfl : p = 1 := by omega
    rcases Nat.eq_zero_or_pos j.val with hj0 | hjpos
    · obtain rfl : j = 0 := Fin.ext hj0
      have hY0 : duplicateAt e 0 w 0 = e := duplicateAt_castSucc e 0 w
      have hD0 : duplicateAt (-1 : ℤ) 0 𝒟 ⟨0, by omega⟩ = -1 := duplicateAt_castSucc (-1 : ℤ) 0 𝒟
      rw [ite_eq_right (by omega), ite_eq_left ⟨rfl, Fin.val_zero _⟩, zero_add,
        Finset.sum_range_one, dite_eq_left (by omega : 0 < m + 4), hD0, negOnePowCast_neg,
        negOnePowCast_one, neg_one_smul, splice_collapse_tail_eq R (by omega : 0 < m + 3), hY0,
        subword_tail_duplicateAt_zero R (Fin.val_zero _) hwj,
        h𝒜.taylor_of_two_cohomologicalUnit_left he]
    · obtain ⟨u, hu, hsub⟩ := subword_tail_duplicateAt_of_pos R e hjpos w
      rw [hsub, hIH u ⟨j.val - 1, by omega⟩ (by dsimp only; omega) hu, splice_zero, map_zero,
        smul_zero, ite_eq_right (by omega), ite_eq_right (by omega), add_zero]

private theorem taylor_barDifferential_duplicateAt_ne_two {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} (he : 𝒜.CohomologicalUnit e) {m : ℕ}
    (hlow : 𝒜.KillsUnitUpTo e (m + 2)) (j : Fin (m + 3))
    (hIH : 𝒜.KillsUnitBeforeSlot e (m + 3) j.val) {w : Fin (m + 3) → A} (𝒟 : Fin (m + 3) → ℤ)
    (hwj : w j = e) {p d : ℕ} (hd : d < m + 5) (hd2 : d ≠ 2) :
    negOnePowCast R (∑ r ∈ Finset.range p,
        if h : r < m + 4 then duplicateAt (-1 : ℤ) j 𝒟 ⟨r, h⟩ else 0) •
      𝒜.taylor (splice R (duplicateAt e j w) 0 (m + 4) p d
        (𝒜.taylor (subword R (duplicateAt e j w) p d))) =
      (if p = 0 ∧ d = m + 3 then 𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
        ![𝒜.taylor (subword R (duplicateAt e j w) 0 (m + 3)),
          duplicateAt e j w (Fin.last (m + 3))])) else 0) +
      (if p = 1 ∧ d = m + 3 ∧ j.val = 0 then
        -𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w)) else 0) := by
  by_cases hdm3 : d = m + 3
  · subst hdm3
    simpa only [and_true, true_and] using
      taylor_barDifferential_duplicateAt_m_add_three h𝒜 he j hIH 𝒟 hwj (p := p)
  · simp (disch := omega) only [taylor_splice_duplicateAt_eq_zero_of_ne h𝒜 hlow j w hd hd2 hdm3,
      smul_zero, ite_eq_right, add_zero]

private theorem taylor_barDifferential_duplicateAt_binary_prefix {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} (he : 𝒜.CohomologicalUnit e) {m : ℕ} (j : Fin (m + 3))
    (hIH : 𝒜.KillsUnitBeforeSlot e (m + 3) j.val) {w : Fin (m + 3) → A} {𝒟 : Fin (m + 3) → ℤ}
    (hw : ∀ r, w r ∈ (𝒜.grading.shift 1).piece (𝒟 r)) (hwj : w j = e) :
    (∑ p ∈ Finset.range (j.val + 1),
      negOnePowCast R (∑ r ∈ Finset.range p,
          if h : r < m + 4 then duplicateAt (-1 : ℤ) j 𝒟 ⟨r, h⟩ else 0) •
        𝒜.taylor (splice R (duplicateAt e j w) 0 (m + 4) p 2
          (𝒜.taylor (subword R (duplicateAt e j w) p 2)))) =
      if j.val = 0 then 𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w)) else 0 := by
  have hjlt := j.isLt
  rcases Nat.eq_zero_or_pos j.val with hj0 | hjpos
  · -- At `j = 0`, collapsing `[e, e]` at slot `0` leaves `m(w)`.
    obtain rfl : j = 0 := Fin.ext hj0
    have hsp := splice_two_duplicateAt_self R hwj
    simp only [Fin.val_zero] at hsp
    have hY0 : duplicateAt e 0 w ⟨0, by omega⟩ = e := duplicateAt_castSucc e 0 w
    have hY1 : duplicateAt e 0 w ⟨0 + 1, by omega⟩ = e := duplicateAt_succ e 0 w
    rw [ite_eq_left (Fin.val_zero _), Fin.val_zero, zero_add, Finset.sum_range_one,
      Finset.sum_range_zero, negOnePowCast_zero, one_smul, subword_two_eq R _ (by omega), hY0, hY1,
      h𝒜.taylor_of_two_cohomologicalUnit_left he, hsp]
  · -- For `j > 0`, binary collapses before `j - 1` vanish by `hIH`, and slots `j - 1` and `j`
    -- cancel around the interior unit `duplicateAt e j w j = e`.
    have hj_pred : (j.val - 1) + 1 = j.val := Nat.sub_add_cancel hjpos
    have hcancel := h𝒜.negOnePowCast_smul_splice_two_add_succ_eq_zero he (n := m + 3)
      (p := j.val - 1) (x := duplicateAt e j w) (𝒟 := duplicateAt (-1 : ℤ) j 𝒟) (by omega)
      (duplicateAt_mem_piece he.mem_shift_one_piece j hw ⟨j.val - 1, by omega⟩)
      (by
        have hj_cast : (⟨(j.val - 1) + 1, by omega⟩ : Fin (m + 4)) = j.castSucc :=
          Fin.ext (by simp [hj_pred])
        rw [hj_cast, duplicateAt_castSucc])
    rw [ite_eq_right (Nat.ne_of_gt hjpos), Finset.sum_range_succ, ← hj_pred,
      Finset.sum_range_succ, Finset.sum_eq_zero fun p hp ↦ by
        rw [Finset.mem_range] at hp
        obtain ⟨u, hu, hsp⟩ := splice_two_duplicateAt_of_lt R e (by omega : p + 2 ≤ j.val) w
          (𝒜.taylor (subword R (duplicateAt e j w) p 2))
        rw [hsp, hIH u ⟨j.val - 1, by omega⟩ (by dsimp only; omega) hu, smul_zero],
      zero_add, ← map_smul, ← map_smul, ← map_add, hcancel, map_zero]

private theorem taylor_barDifferential_duplicateAt_row {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} (he : 𝒜.CohomologicalUnit e) {m : ℕ}
    (hlow : 𝒜.KillsUnitUpTo e (m + 2)) (j : Fin (m + 3))
    (hIH : 𝒜.KillsUnitBeforeSlot e (m + 3) j.val) {w : Fin (m + 3) → A} (𝒟 : Fin (m + 3) → ℤ)
    (hwj : w j = e) {p : ℕ} :
    (∑ d ∈ Finset.range (m + 5),
      negOnePowCast R (∑ r ∈ Finset.range p,
          if h : r < m + 4 then duplicateAt (-1 : ℤ) j 𝒟 ⟨r, h⟩ else 0) •
        𝒜.taylor (splice R (duplicateAt e j w) 0 (m + 4) p d
          (𝒜.taylor (subword R (duplicateAt e j w) p d)))) =
      negOnePowCast R (∑ r ∈ Finset.range p,
          if h : r < m + 4 then duplicateAt (-1 : ℤ) j 𝒟 ⟨r, h⟩ else 0) •
        𝒜.taylor (splice R (duplicateAt e j w) 0 (m + 4) p 2
          (𝒜.taylor (subword R (duplicateAt e j w) p 2))) +
      ((if p = 0 then 𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
          ![𝒜.taylor (subword R (duplicateAt e j w) 0 (m + 3)),
            duplicateAt e j w (Fin.last (m + 3))])) else 0) +
       (if p = 1 ∧ j.val = 0 then -𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w))
        else 0)) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 (by omega : 2 < m + 5))]
  congr 1
  rw [Finset.sum_congr rfl fun d hd ↦
    taylor_barDifferential_duplicateAt_ne_two h𝒜 he hlow j hIH 𝒟 hwj
      (Finset.mem_range.1 (Finset.mem_erase.1 hd).2) (Finset.mem_erase.1 hd).1]
  simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_erase, Finset.mem_range]
  congr 1 <;> split_ifs <;> first | rfl | omega

/-- **Reduced Stasheff identity on `duplicateAt e j w`**: under `KillsUnitUpTo 𝒜 e (m + 2)` and
`KillsUnitBeforeSlot 𝒜 e (m + 3) j`, the Stasheff identity on `duplicateAt e j w` reduces to the
initial `(m + 3)`-collapse plus the binary collapses from `j + 1` onward. -/
theorem IsMinimal.taylor_barDifferential_duplicateAt {𝒜 : AInfinityAlgebra R A} (h𝒜 : 𝒜.IsMinimal)
    {e : A} (he : 𝒜.CohomologicalUnit e) {m : ℕ} (hlow : 𝒜.KillsUnitUpTo e (m + 2))
    (j : Fin (m + 3)) (hIH : 𝒜.KillsUnitBeforeSlot e (m + 3) j.val) {w : Fin (m + 3) → A}
    {𝒟 : Fin (m + 3) → ℤ} (hw : ∀ r, w r ∈ (𝒜.grading.shift 1).piece (𝒟 r)) (hwj : w j = e)
    (h𝒟j : 𝒟 j = -1) :
    𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
        ![𝒜.taylor (subword R (duplicateAt e j w) 0 (m + 3)),
          duplicateAt e j w (Fin.last (m + 3))])) +
      ∑ t ∈ Finset.range (m + 2 - j.val),
        -(negOnePowCast R (∑ r ∈ Finset.range (j.val + t), if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
          𝒜.taylor (splice R (duplicateAt e j w) 0 (m + 4) (j.val + 1 + t) 2
            (𝒜.taylor (subword R w (j.val + t) 2)))) = 0 := by
  have hjlt := j.isLt
  -- Step 1: Expand `0 = m(b(duplicateAt e j w))` into `(p, d)`-summands and sum each row over `d`.
  have hzero : 𝒜.taylor (𝒜.barDifferential
      (of R A ⟨m + 4, by omega⟩ (PiTensorProduct.tprod R (duplicateAt e j w)))) = 0 := by
    rw [← 𝒜.letter_comp_barDifferential, LinearMap.comp_apply,
      ← LinearMap.comp_apply 𝒜.barDifferential, 𝒜.barDifferential_sq, LinearMap.zero_apply,
      map_zero]
  rw [barDifferential_def, gradedCoderiv_of_tprod_of_homogeneous _ _ 1 _ _
    (duplicateAt (-1 : ℤ) j 𝒟) (duplicateAt_mem_piece he.mem_shift_one_piece j hw)] at hzero
  simp only [one_mul, map_sum, map_smul, ← negOnePowCast_eq_intCast] at hzero
  rw [Finset.sum_congr rfl fun p _ ↦ taylor_barDifferential_duplicateAt_row h𝒜 he hlow j hIH 𝒟 hwj,
    Finset.sum_add_distrib, Finset.sum_add_distrib] at hzero
  simp only [ite_and, Finset.sum_ite_eq', Finset.mem_range,
    ite_eq_left (by omega : 0 < m + 4), ite_eq_left (by omega : 1 < m + 4)] at hzero
  -- Step 2: Reindex binary collapses from `j + 1` onward, pulling out `-1` from the duplicate `e`.
  have htail : (∑ t ∈ Finset.range (m + 2 - j.val),
      negOnePowCast R (∑ r ∈ Finset.range (j.val + 1 + t),
          if h : r < m + 4 then duplicateAt (-1 : ℤ) j 𝒟 ⟨r, h⟩ else 0) •
        𝒜.taylor (splice R (duplicateAt e j w) 0 (m + 4) (j.val + 1 + t) 2
          (𝒜.taylor (subword R (duplicateAt e j w) (j.val + 1 + t) 2)))) =
      ∑ t ∈ Finset.range (m + 2 - j.val),
        -(negOnePowCast R (∑ r ∈ Finset.range (j.val + t), if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
          𝒜.taylor (splice R (duplicateAt e j w) 0 (m + 4) (j.val + 1 + t) 2
            (𝒜.taylor (subword R w (j.val + t) 2)))) :=
    Finset.sum_congr rfl fun t ht ↦ by
      rw [Finset.mem_range] at ht
      rw [Nat.add_right_comm j.val 1 t,
        sum_duplicateAt_range_succ_ge j h𝒟j (by omega) (by omega),
        subword_two_duplicateAt_ge R (by omega) (by omega) hwj, negOnePowCast_add,
        negOnePowCast_neg, negOnePowCast_one, mul_neg_one, neg_smul]
  -- Step 3: Split the binary sum at `j + 1` and cancel the `j = 0` boundary terms.
  rw [Finset.sum_range_succ _ (m + 3),
    splice_eq_zero_of_not_fits R _ _ (by omega : ¬ (0 < 2 ∧ (m + 3) + 2 ≤ m + 4)), map_zero,
    smul_zero, add_zero] at hzero
  rw [Finset.sum_range_eq_sum_add_sum_sub _ (by omega : j.val + 1 ≤ m + 3), Nat.succ_sub_succ,
    taylor_barDifferential_duplicateAt_binary_prefix h𝒜 he j hIH hw hwj, htail] at hzero
  by_cases hj0 : j.val = 0 <;>
    [rw [ite_eq_left hj0, ite_eq_left hj0] at hzero;
     rw [ite_eq_right hj0, ite_eq_right hj0] at hzero] <;>
    (refine Eq.trans ?_ hzero; abel)

/-- Once `KillsUnitUpTo 𝒜 e (m + 2)` and `KillsUnitBeforeSlot 𝒜 e (m + 3) (m + 2)` hold on a
minimal `A∞` algebra, the Stasheff identity forces vanishing when `e` sits at `Fin.last (m + 2)`. -/
theorem IsMinimal.taylor_of_tprod_last_eq_zero {𝒜 : AInfinityAlgebra R A} (h𝒜 : 𝒜.IsMinimal)
    {e : A} (he : 𝒜.CohomologicalUnit e) {m : ℕ} (hlow : 𝒜.KillsUnitUpTo e (m + 2))
    (hIH : 𝒜.KillsUnitBeforeSlot e (m + 3) (m + 2)) (x : Fin (m + 3) → A)
    (hx : x (Fin.last (m + 2)) = e) :
    𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R x)) = 0 := by
  refine of_tprod_mem_of_mem_piece (𝒜.grading.shift 1) he.mem_shift_one_piece
    (S := LinearMap.ker 𝒜.taylor) ⟨m + 3, by omega⟩ (Fin.last (m + 2))
    (fun w 𝒟 hw hwlast h𝒟last ↦ ?_) x hx
  rw [LinearMap.mem_ker]
  have hst := h𝒜.taylor_barDifferential_duplicateAt he hlow (Fin.last (m + 2))
    (by simpa only [Fin.val_last] using hIH) hw hwlast h𝒟last
  have hYlast : duplicateAt e (Fin.last (m + 2)) w (Fin.last (m + 3)) = e := by
    nth_rw 2 [← Fin.succ_last]
    exact duplicateAt_succ e (Fin.last (m + 2)) w
  rw [Fin.val_last, Nat.sub_self, Finset.sum_range_zero, add_zero,
    subword_init_duplicateAt_last R hwlast, hYlast,
    h𝒜.taylor_of_two_cohomologicalUnit_right he] at hst
  simpa only [InternalGrading.koszulTwist_koszulTwist, map_zero] using
    congrArg (𝒜.grading.koszulTwist 1) hst

end Stasheff

end TauCeti.AInfinityAlgebra
