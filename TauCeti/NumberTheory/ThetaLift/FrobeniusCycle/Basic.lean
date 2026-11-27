/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.ZMod.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parahoric
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InverseTranspose

import TauCeti.Data.ZMod.Count
import TauCeti.Data.ZMod.Periodic

/-!
# Frobenius cycles, letter matrices, depth and defect

Let `W` be a local ring and `R` a commutative ring. A *Frobenius cycle* with `N` letters is a
family of ring maps `ι s : W →+* R`, `s : ZMod N`, each congruent modulo a prime `p` to the
`P`-th power of the one before, `P = p ^ e ≥ 5`, where the residue field of `W` has
`q = P ^ N` elements; the letters carry alternating parities, and `R` contains a square root
`w` of `p`. An element `g` of `GL_k(W)` has at each letter `s` the matrix `g_s`: `ι s` of `g` if
`s` is even, `ι s` of the inverse transpose of `g` if `s` is odd. The variables `x (b, s)`,
`b : Fin k`, carry the notions of depth (for a split `r` of the indices) and of defect weights
(for a pair of indices and a letter). On the parahoric subgroup
`TauCeti.GeneralLinear.parahoricSubgroup` of a labelling `τ` of the indices, `p` divides the
entry `(i, j)` of the letter matrix `g_s` when `τ i < τ j` at an even letter `s` and when
`τ j < τ i` at an odd letter `s`.

## Main definitions

* `TauCeti.FrobeniusCycle W R N`: a Frobenius cycle with `N` letters; `P` and `q` are its power
  and the size of the residue field.
* `TauCeti.FrobeniusCycle.letterMatrix`: the matrix `g_s` of `g` at a letter.
* `TauCeti.FrobeniusCycle.depth`, `TauCeti.FrobeniusCycle.defectWeight`,
  `TauCeti.FrobeniusCycle.defect`: the degree in the deep variables, and the weights and
  weighted degree measuring the defect along a pair of indices at a letter.

## Main results

* `TauCeti.FrobeniusCycle.even`: a Frobenius cycle has an even number of letters.
* `TauCeti.FrobeniusCycle.dvd_ι_of_mem_maximalIdeal`: the letter maps send the maximal ideal
  into `p R`.
* `TauCeti.FrobeniusCycle.p_dvd_letterMatrix_of_mem_parahoricSubgroup`: the letter matrices of
  an element of the parahoric subgroup of `τ` have their entry `(i, j)` divisible by `p` when
  `τ i < τ j` at an even letter and when `τ j < τ i` at an odd letter.
* `TauCeti.FrobeniusCycle.defectWeight_sub_mem_Icc`,
  `TauCeti.FrobeniusCycle.abs_defect_le`: the two defect weights at a letter differ by at most
  `3 / 2`, and an exponent of degree at most `d` in each letter has defect at most `2 * d` in
  absolute value.

## References

* The formal proof whose route this follows: the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207, file
  `New/UpperBound/ElementaryDivisors/TwistingData.lean` (`New.FrobeniusCycle`,
  `New.FrobeniusCycle.depth`, `New.FrobeniusCycle.defectWeight`,
  `New.FrobeniusCycle.p_dvd_letterMatrix_of_mem_parahoric`,
  `New.FrobeniusCycle.defectWeight_sub_mem_Icc`,
  `New.FrobeniusCycle.abs_weight_defectWeight_le`).
-/

public section

open IsLocalRing Matrix

namespace TauCeti

/-- A *Frobenius cycle* with `N` letters from a local ring `W` to a commutative ring `R`: a prime
`p`, an exponent `e` with `p ^ e ≥ 5`, ring maps `ι s : W →+* R` for the letters `s : ZMod N`,
a parity of each letter (`isEven s`) alternating along the cycle, and `w : R` with `w ^ 2 = p`,
such that the residue field of `W` has `(p ^ e) ^ N` elements and `ι (s + 1) y` is congruent to
`ι s y ^ p ^ e` modulo `p` for all `s` and `y`. -/
structure FrobeniusCycle (W : Type*) [CommRing W] [IsLocalRing W] (R : Type*) [CommRing R]
    (N : ℕ) where
  /-- The prime of the cycle. -/
  p : ℕ
  /-- `p` is prime. -/
  prime : p.Prime
  /-- The exponent: consecutive letter maps differ by the `p ^ e`-th power modulo `p`. -/
  e : ℕ
  /-- The power `p ^ e` is at least `5`. -/
  five_le_pow : 5 ≤ p ^ e
  /-- The ring map of a letter. -/
  ι : ZMod N → W →+* R
  /-- The parity of a letter: `true` for the even letters. -/
  isEven : ZMod N → Bool
  /-- Consecutive letters have opposite parities. -/
  isEven_add_one : ∀ s, isEven (s + 1) = !isEven s
  /-- A square root of `p`. -/
  w : R
  /-- `w` is a square root of `p`. -/
  w_sq : w ^ 2 = p
  /-- The residue field of `W` has `(p ^ e) ^ N` elements. -/
  card_residueField : Nat.card (ResidueField W) = (p ^ e) ^ N
  /-- The Frobenius congruences: `ι (s + 1) y ≡ ι s y ^ p ^ e` modulo `p`. -/
  dvd_ι_add_one_sub_pow : ∀ s y, (p : R) ∣ ι (s + 1) y - ι s y ^ p ^ e

namespace FrobeniusCycle

variable {W : Type*} [CommRing W] [IsLocalRing W] {R : Type*} [CommRing R] {N : ℕ}
  (T : FrobeniusCycle W R N) {k : ℕ}

/-- The power `P = p ^ e` of the Frobenius congruences. -/
def P : ℕ := T.p ^ T.e

/-- The number `q = P ^ N` of elements of the residue field. -/
def q : ℕ := T.P ^ N

/-- Unfolding `P`. -/
theorem P_def : T.P = T.p ^ T.e := (rfl)

/-- Unfolding `q`. -/
theorem q_def : T.q = T.P ^ N := (rfl)

/-- `P ≥ 5`. -/
theorem five_le_P : 5 ≤ T.P := T.five_le_pow

/-- The residue field of `W` has `q` elements. -/
theorem card_residueField_eq_q : Nat.card (ResidueField W) = T.q := T.card_residueField

include T in
/-- A Frobenius cycle has at least one letter. -/
theorem neZero : NeZero N := by
  refine ⟨fun hN ↦ ?_⟩
  have hpow : ∀ a : ℕ, a ^ N = 1 := fun a ↦ by rw [hN, pow_zero]
  have h : Nat.card (ResidueField W) = 1 := T.card_residueField.trans (hpow _)
  exact not_subsingleton (ResidueField W) (Nat.card_eq_one_iff_unique.mp h).1

/-- `q ≥ 5`. -/
theorem five_le_q : 5 ≤ T.q := by
  have := T.neZero
  calc 5 ≤ T.P := T.five_le_P
    _ ≤ T.P ^ N := Nat.le_self_pow (NeZero.ne N) _

/-- `P > 0`. -/
theorem P_pos : 0 < T.P := by
  have := T.five_le_P
  omega

/-- `q > 1`. -/
theorem one_lt_q : 1 < T.q := by
  have := T.five_le_q
  omega

/-- For every letter `s`, read in `{0, …, N - 1}`, one has `5 P ^ s ≤ q`. -/
theorem five_mul_P_pow_le_q [NeZero N] (s : ZMod N) : 5 * T.P ^ s.val ≤ T.q := by
  rw [T.q_def]
  calc 5 * T.P ^ s.val ≤ T.P * T.P ^ s.val := Nat.mul_le_mul_right _ T.five_le_P
    _ = T.P ^ (s.val + 1) := (pow_succ' ..).symm
    _ ≤ T.P ^ N := Nat.pow_le_pow_right T.P_pos s.val_lt

include T in
/-- The residue field of `W` is finite. -/
theorem finite_residueField : Finite (ResidueField W) :=
  Nat.finite_of_card_ne_zero (by rw [T.card_residueField_eq_q]; linarith [T.five_le_q])

/-- The parity of the letter `s + j` is that of `s`, flipped when `j` is odd. -/
theorem isEven_add_natCast (s : ZMod N) (j : ℕ) :
    T.isEven (s + j) = (T.isEven s ^^ decide (Odd j)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.cast_succ, ← add_assoc, T.isEven_add_one, ih]
    rcases Nat.even_or_odd j with hj | hj <;> cases T.isEven s <;>
      simp [hj, Nat.not_odd_iff_even.mpr]

include T in
/-- A Frobenius cycle has an even number of letters. -/
theorem even : Even N := by
  have h := T.isEven_add_natCast 0 N
  rw [ZMod.natCast_self, add_zero] at h
  cases hN : decide (Odd N)
  · simpa using hN
  · cases T.isEven 0 <;> simp_all

/-- Iterating the Frobenius congruences: `ι (s + j) y ≡ ι s y ^ P ^ j` modulo `p`. -/
theorem dvd_ι_add_natCast_sub_pow (s : ZMod N) (y : W) (j : ℕ) :
    (T.p : R) ∣ T.ι (s + j) y - T.ι s y ^ T.P ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hstep := T.dvd_ι_add_one_sub_pow (s + j) y
    rw [← T.P_def] at hstep
    -- raising the congruence of `ih` to the `P`-th power and adding the one-step congruence
    have h := dvd_add hstep (ih.trans (sub_dvd_pow_sub_pow _ _ T.P))
    rw [sub_add_sub_cancel, ← pow_mul, ← pow_succ] at h
    rwa [Nat.cast_succ, ← add_assoc]

/-- The letter maps send the maximal ideal into `p R`. -/
theorem dvd_ι_of_mem_maximalIdeal {y : W} (hy : y ∈ maximalIdeal W) (s : ZMod N) :
    (T.p : R) ∣ T.ι s y := by
  obtain ⟨m, hm⟩ : ∃ m, T.q = m + 1 := ⟨T.q - 1, by have := T.five_le_q; omega⟩
  have hm0 : 0 < m := by have := T.five_le_q; omega
  let π := Ideal.Quotient.mk (Ideal.span {(T.p : R)})
  -- the image of `ι s y` modulo `p` is fixed by the `q`-th power (the congruences around the cycle)
  have hcycle : π (T.ι s y) ^ (m + 1) = π (T.ι s y) := by
    have h := T.dvd_ι_add_natCast_sub_pow s y N
    rw [ZMod.natCast_self, add_zero, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq,
      map_pow] at h
    rw [← hm]
    exact h.symm
  have hunit : IsUnit (π (T.ι s (1 - y ^ m))) :=
    ((isUnit_one_sub_self_of_mem_nonunits _ ((mem_maximalIdeal _).mp
      ((maximalIdeal W).pow_mem_of_mem hy _ hm0))).map _).map _
  have hzero : π (T.ι s y) * π (T.ι s (1 - y ^ m)) = 0 := by
    simp only [map_sub, map_one, map_pow]
    linear_combination -hcycle
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  exact hunit.mul_left_eq_zero.mp hzero

/-! ### Letter matrices -/

/-- The matrix `g_s` of `g ∈ GL_k(W)` at the letter `s`: `ι s` applied to `g` if `s` is even,
and to the inverse transpose of `g` if `s` is odd. -/
noncomputable def letterMatrix (s : ZMod N) : GL (Fin k) W →* Matrix (Fin k) (Fin k) R :=
  if T.isEven s then (Units.coeHom _).comp (GeneralLinearGroup.map (T.ι s))
  else ((Units.coeHom _).comp (GeneralLinearGroup.map (T.ι s))).comp
    GeneralLinearGroup.inverseTranspose.toMonoidHom

/-- The letter matrix at an even letter. -/
@[simp]
theorem letterMatrix_of_isEven {s : ZMod N} (hs : T.isEven s = true) (g : GL (Fin k) W) :
    T.letterMatrix s g = (g : Matrix (Fin k) (Fin k) W).map (T.ι s) := by
  simp [letterMatrix, hs]

/-- The letter matrix at an odd letter. -/
@[simp]
theorem letterMatrix_of_not_isEven {s : ZMod N} (hs : T.isEven s = false) (g : GL (Fin k) W) :
    T.letterMatrix s g = (↑g⁻¹ : Matrix (Fin k) (Fin k) W)ᵀ.map (T.ι s) := by
  simp [letterMatrix, hs, GeneralLinearGroup.coe_inverseTranspose]

/-! ### Depth and defect -/

/-- The variable `x (b, s)` is *deep* for `r` if `s` is even and `r ≤ b`, or `s` is odd and
`b < r`. -/
def IsDeep (r : ℕ) (x : Fin k × ZMod N) : Prop :=
  if T.isEven x.2 then r ≤ (x.1 : ℕ) else (x.1 : ℕ) < r

/-- Unfolding `IsDeep`. -/
@[simp]
theorem isDeep_iff (r : ℕ) (x : Fin k × ZMod N) :
    T.IsDeep r x ↔ T.isEven x.2 = true ∧ r ≤ (x.1 : ℕ) ∨ T.isEven x.2 = false ∧ (x.1 : ℕ) < r := by
  unfold IsDeep
  cases T.isEven x.2 <;> simp

instance (r : ℕ) : DecidablePred (T.IsDeep (k := k) r) := fun x ↦
  decidable_of_iff _ (T.isDeep_iff r x).symm

/-- `depth r β` is the degree of `x ^ β` in the variables that are deep for `r`. -/
noncomputable def depth (r : ℕ) : (Fin k × ZMod N →₀ ℕ) →+ ℕ :=
  Finsupp.weight fun x ↦ if T.IsDeep r x then 1 else 0

/-- Unfolding `depth`. -/
theorem depth_apply (r : ℕ) (β : Fin k × ZMod N →₀ ℕ) :
    T.depth r β = β.sum fun x m ↦ if T.IsDeep r x then m else 0 := by
  simp [depth, Finsupp.weight_apply]

/-- The depth of a power of one variable. -/
@[simp]
theorem depth_single (r : ℕ) (x : Fin k × ZMod N) (m : ℕ) :
    T.depth r (Finsupp.single x m) = if T.IsDeep r x then m else 0 := by
  simp [depth, Finsupp.weight_single]

/-- The index of the variable of positive defect weight at the letter `s` along `(a, a')`:
`a'` if `s` is even, `a` if `s` is odd. -/
def posIndex (a a' : Fin k) (s : ZMod N) : Fin k := if T.isEven s then a' else a

/-- The index of the variable of negative defect weight at the letter `s` along `(a, a')`:
`a` if `s` is even, `a'` if `s` is odd. The weight there is negative only when `a ≠ a'`; when
`a = a'` this is also `posIndex a a' s`, and the positive weight takes precedence
(`defectWeight`). -/
def negIndex (a a' : Fin k) (s : ZMod N) : Fin k := if T.isEven s then a else a'

/-- Unfolding `posIndex`. -/
theorem posIndex_eq_ite (a a' : Fin k) (s : ZMod N) :
    T.posIndex a a' s = if T.isEven s then a' else a :=
  (rfl)

/-- Unfolding `negIndex`. -/
theorem negIndex_eq_ite (a a' : Fin k) (s : ZMod N) :
    T.negIndex a a' s = if T.isEven s then a else a' :=
  (rfl)

/-- `posIndex` at an even letter. -/
@[simp]
theorem posIndex_of_isEven {s : ZMod N} (hs : T.isEven s = true) (a a' : Fin k) :
    T.posIndex a a' s = a' := by
  simp [posIndex, hs]

/-- `posIndex` at an odd letter. -/
@[simp]
theorem posIndex_of_not_isEven {s : ZMod N} (hs : T.isEven s = false) (a a' : Fin k) :
    T.posIndex a a' s = a := by
  simp [posIndex, hs]

/-- `negIndex` at an even letter. -/
@[simp]
theorem negIndex_of_isEven {s : ZMod N} (hs : T.isEven s = true) (a a' : Fin k) :
    T.negIndex a a' s = a := by
  simp [negIndex, hs]

/-- `negIndex` at an odd letter. -/
@[simp]
theorem negIndex_of_not_isEven {s : ZMod N} (hs : T.isEven s = false) (a a' : Fin k) :
    T.negIndex a a' s = a' := by
  simp [negIndex, hs]

/-- The defect weights at the letter `i` along `(a, a')`: the variable `x (posIndex a a' s, s)`
has weight `P ^ (1 + (s - 1 - i).val) / (q - 1)`; if `a ≠ a'`, the variable
`x (negIndex a a' s, s)` has weight `-P ^ (s - i).val / (q - 1)`; every other variable has weight
`0`. When `a = a'` the two indices coincide and that variable gets the positive weight
(`defectWeight_posIndex`, `defectWeight_negIndex`). -/
noncomputable def defectWeight (a a' : Fin k) (i : ZMod N) (x : Fin k × ZMod N) : ℝ :=
  if x.1 = T.posIndex a a' x.2 then (T.P : ℝ) ^ (1 + (x.2 - 1 - i).val) / (T.q - 1)
  else if x.1 = T.negIndex a a' x.2 then -((T.P : ℝ) ^ (x.2 - i).val / (T.q - 1)) else 0

/-- The defect weight of the variable of positive weight. It is a pre-`simp` rule, so that it
applies before `posIndex` is evaluated by parity. -/
@[simp↓]
theorem defectWeight_posIndex (a a' : Fin k) (i s : ZMod N) :
    T.defectWeight a a' i (T.posIndex a a' s, s) =
      (T.P : ℝ) ^ (1 + (s - 1 - i).val) / (T.q - 1) := by
  simp [defectWeight]

/-- The defect weight of the variable of negative weight, for distinct indices. It is a
pre-`simp` rule, so that it applies before `negIndex` is evaluated by parity. -/
@[simp↓]
theorem defectWeight_negIndex {a a' : Fin k} (h : a ≠ a') (i s : ZMod N) :
    T.defectWeight a a' i (T.negIndex a a' s, s) = -((T.P : ℝ) ^ (s - i).val / (T.q - 1)) := by
  have hne : T.negIndex a a' s ≠ T.posIndex a a' s := by
    unfold negIndex posIndex
    split_ifs
    exacts [h, h.symm]
  simp [defectWeight, hne]

/-- The other variables have defect weight `0`. -/
@[simp]
theorem defectWeight_of_ne {a a' b : Fin k} {s : ZMod N} (hpos : b ≠ T.posIndex a a' s)
    (hneg : b ≠ T.negIndex a a' s) (i : ZMod N) : T.defectWeight a a' i (b, s) = 0 := by
  simp [defectWeight, hpos, hneg]

/-- The defect of an exponent at the letter `i` along `(a, a')`: its weighted degree for the
defect weights. -/
noncomputable def defect (a a' : Fin k) (i : ZMod N) : (Fin k × ZMod N →₀ ℕ) →+ ℝ :=
  Finsupp.weight (T.defectWeight a a' i)

/-- Unfolding `defect`. -/
theorem defect_apply (a a' : Fin k) (i : ZMod N) (β : Fin k × ZMod N →₀ ℕ) :
    T.defect a a' i β = β.sum fun x m ↦ m * T.defectWeight a a' i x := by
  simp [defect, Finsupp.weight_apply]

/-- The defect is the weighted degree for the defect weights, as a function. -/
theorem coe_defect (a a' : Fin k) (i : ZMod N) :
    ⇑(T.defect a a' i) = Finsupp.weight (T.defectWeight a a' i) :=
  (rfl)

/-- The defect of a power of one variable. -/
@[simp]
theorem defect_single (a a' : Fin k) (i : ZMod N) (x : Fin k × ZMod N) (m : ℕ) :
    T.defect a a' i (Finsupp.single x m) = m * T.defectWeight a a' i x := by
  simp [defect, Finsupp.weight_single]

/-! ### Letter matrices on the parahoric subgroup -/

open GeneralLinear in
/-- For `g` in the parahoric subgroup of `τ`, `p` divides the entry `(i, j)` of the letter matrix
`g_s` if `s` is even and `τ i < τ j`, or if `s` is odd and `τ j < τ i`. -/
theorem p_dvd_letterMatrix_of_mem_parahoricSubgroup {τ : Fin k → ℕ} {g : GL (Fin k) W}
    (hg : g ∈ parahoricSubgroup W τ) {s : ZMod N} {i j : Fin k}
    (h : T.isEven s = true ∧ τ i < τ j ∨ T.isEven s = false ∧ τ j < τ i) :
    (T.p : R) ∣ T.letterMatrix s g i j := by
  rcases h with ⟨hs, h⟩ | ⟨hs, h⟩
  · rw [T.letterMatrix_of_isEven hs, Matrix.map_apply]
    exact T.dvd_ι_of_mem_maximalIdeal ((mem_parahoricSubgroup_iff τ g).mp hg i j h) s
  · rw [T.letterMatrix_of_not_isEven hs, Matrix.map_apply, Matrix.transpose_apply]
    exact T.dvd_ι_of_mem_maximalIdeal
      ((mem_parahoricSubgroup_iff τ _).mp ((parahoricSubgroup W τ).inv_mem hg) j i h) s

/-! ### Bounds for the defect weights -/

/-- The weight of `u_s` minus that of `ū_s` lies in `[0, 3 / 2]`. -/
theorem defectWeight_sub_mem_Icc (a a' : Fin k) (i s : ZMod N) :
    T.defectWeight a a' i (T.posIndex a a' s, s) - T.defectWeight a a' i (T.negIndex a a' s, s) ∈
      Set.Icc (0 : ℝ) (3 / 2) := by
  have := T.neZero
  by_cases h : a = a'
  · -- for `a = a'` the two indices coincide and the difference is `0`
    subst h
    have hidx : T.negIndex a a s = T.posIndex a a s := by
      unfold negIndex posIndex
      split_ifs <;> rfl
    rw [hidx, sub_self]
    norm_num
  rw [T.defectWeight_posIndex, T.defectWeight_negIndex h, sub_neg_eq_add, ← add_div]
  have hP : (5 : ℝ) ≤ T.P := by exact_mod_cast T.five_le_P
  have hq : (T.q : ℝ) = (T.P : ℝ) ^ N := by rw [q_def, Nat.cast_pow]
  have hq5 : (5 : ℝ) ≤ T.q := by exact_mod_cast T.five_le_q
  refine ⟨div_nonneg (by positivity) (by linarith), (div_le_iff₀ (by linarith)).mpr ?_⟩
  -- stepping from the letter `s - 1 - i` to `s - i` either adds `1` to the residue or wraps
  have hsucc : s - 1 - i + 1 = s - i := by ring
  have hstep := ZMod.val_add_one_eq_or (s - 1 - i)
  rw [hsucc] at hstep
  have h1 := ZMod.val_lt (s - 1 - i)
  have hj := ZMod.val_lt (s - i)
  rcases hstep with hstep | hstep
  · -- no wrap: the exponent of the positive weight is `(s - i).val`
    have hexp : 1 + (s - 1 - i).val = (s - i).val := by omega
    have hle : (T.P : ℝ) * (T.P : ℝ) ^ (s - i).val ≤ T.q := by
      rw [hq, ← pow_succ']
      exact pow_le_pow_right₀ (by linarith) hj
    have hpos : (1 : ℝ) ≤ (T.P : ℝ) ^ (s - i).val := one_le_pow₀ (by linarith)
    rw [hexp]
    nlinarith [hle, hpos]
  · -- wrap: `s = i`, the exponents are `N` and `0`
    have hexp : 1 + (s - 1 - i).val = N := by omega
    have hzero : (s - i).val = 0 := by omega
    rw [hexp, hzero, pow_zero, ← hq]
    linarith

/-- Fix the reference letter `i` of the defect. At each letter `s`, the sum of the two formulas
`P ^ (1 + (s - 1 - i).val) / (q - 1)` and `P ^ (s - i).val / (q - 1)` is an upper bound for the
absolute value of every defect weight of a variable at `s` (when `a = a'` only the first occurs).
Summed over the letters `s`, these bounds give `(P + 1) / (P - 1) ≤ 2`. -/
private theorem sum_abs_defectWeight_le [NeZero N] (i : ZMod N) :
    ∑ s : ZMod N, ((T.P : ℝ) ^ (1 + (s - 1 - i).val) / (T.q - 1) +
      (T.P : ℝ) ^ (s - i).val / (T.q - 1)) ≤ 2 := by
  have hP : (5 : ℝ) ≤ T.P := by exact_mod_cast T.five_le_P
  have hq5 : (5 : ℝ) ≤ T.q := by exact_mod_cast T.five_le_q
  set S := ∑ j ∈ Finset.range N, (T.P : ℝ) ^ j
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ by positivity
  have hq : (T.q : ℝ) - 1 = S * (T.P - 1) := by
    rw [geom_sum_mul, q_def, Nat.cast_pow]
  -- the two sums over the letters are geometric sums after shifting the residues
  have h2 (c : ZMod N) : ∑ s : ZMod N, (T.P : ℝ) ^ (s - c).val = S :=
    ZMod.sum_val_sub_eq_sum_range (fun j ↦ (T.P : ℝ) ^ j) c
  have h1 : ∑ s : ZMod N, (T.P : ℝ) ^ (1 + (s - 1 - i).val) = T.P * S := by
    simp_rw [pow_add, pow_one, ← Finset.mul_sum, sub_sub, h2]
  simp only [← add_div, ← Finset.sum_div, Finset.sum_add_distrib, h1, h2 i]
  rw [div_le_iff₀ (by linarith), hq]
  nlinarith [mul_nonneg hS (by linarith : (0 : ℝ) ≤ T.P - 3)]

/-- An exponent of degree at most `d` in each letter has defect of absolute value at most
`2 * d`. -/
theorem abs_defect_le (a a' : Fin k) (i : ZMod N) {β : Fin k × ZMod N →₀ ℕ} {d : ℕ}
    (hβ : ∀ s, ∑ b, β (b, s) ≤ d) : |T.defect a a' i β| ≤ 2 * d := by
  have := T.neZero
  set M : ZMod N → ℝ := fun s ↦ (T.P : ℝ) ^ (1 + (s - 1 - i).val) / (T.q - 1)
  set m : ZMod N → ℝ := fun s ↦ (T.P : ℝ) ^ (s - i).val / (T.q - 1)
  have hq5 : (5 : ℝ) ≤ T.q := by exact_mod_cast T.five_le_q
  have hM : ∀ s, 0 ≤ M s := fun s ↦ div_nonneg (by positivity) (by linarith)
  have hm : ∀ s, 0 ≤ m s := fun s ↦ div_nonneg (by positivity) (by linarith)
  have hw : ∀ b s, |T.defectWeight a a' i (b, s)| ≤ M s + m s := by
    intro b s
    have h1 : 0 ≤ (T.P : ℝ) ^ (1 + (s - 1 - i).val) / (T.q - 1) := hM s
    have h2 : 0 ≤ (T.P : ℝ) ^ (s - i).val / (T.q - 1) := hm s
    dsimp only [M, m]
    unfold defectWeight
    split_ifs <;> simp only [abs_neg, abs_of_nonneg h1, abs_of_nonneg h2, abs_zero] <;> linarith
  have hsum : |T.defect a a' i β| ≤ d * ∑ s, (M s + m s) := by
    rw [T.defect_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type_right,
      Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ ↦ ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ b, |(β (b, s) : ℝ) * T.defectWeight a a' i (b, s)|
        ≤ ∑ b, (β (b, s) : ℝ) * (M s + m s) := Finset.sum_le_sum fun b _ ↦ by
          rw [abs_mul, Nat.abs_cast]
          exact mul_le_mul_of_nonneg_left (hw b s) (Nat.cast_nonneg _)
      _ ≤ d * (M s + m s) := by
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hβ s) (add_nonneg (hM s) (hm s))
  refine hsum.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _) |>.trans_eq (mul_comm _ _))
  exact T.sum_abs_defectWeight_le i

end FrobeniusCycle

end TauCeti
