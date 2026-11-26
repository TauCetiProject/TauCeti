/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.TwoBlockLabel
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InverseTranspose

import TauCeti.Data.ZMod.FinEquiv
import TauCeti.Data.ZMod.Periodic

/-!
# Frobenius cycles, letter matrices, depth and defect

Let `W` be a local ring and `R` a commutative ring. A *Frobenius cycle* with `N` letters is a
family of ring maps `ι s : W →+* R`, `s : ZMod N`, each congruent modulo a prime `p` to the
`P`-th power of the one before, `P = p ^ e ≥ 5`, where the residue field of `W` has
`q = P ^ N` elements; the letters carry alternating parities, and `R` contains a square root
`w` of `p`. An element `g` of `GL_k(W)` has at each letter `s` the matrix `g_s`: `ι s` of `g` if
`s` is even, `ι s` of the inverse transpose of `g` if `s` is odd.

These data serve forms in variables `x (b, s)`, `b : Fin k`, one block of `k` variables for each
letter `s`: the columns of the letter matrix `g_s` prescribe the substitution of `g` in the
variables of the letter `s` (the twisted action), and depth and defect measure the exponents
`β : Fin k × ZMod N →₀ ℕ` of the monomials of the resulting forms. The depth for a split `r` of
the indices counts the degree in the deep variables; the defect along a pair of indices `(a, a')`
at a reference letter `i` is the weighted degree for the defect weights. The comparison of the
letter matrices with the Levi and parahoric subgroups of `GL_k(W)` is in
`TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Parahoric`.

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
* `TauCeti.FrobeniusCycle.defectWeight_sub_mem_Icc`,
  `TauCeti.FrobeniusCycle.abs_defect_le`: at each letter, the weight at `posIndex` minus the
  weight at `negIndex` lies in `[0, 3 / 2]` (it is `0` when the two indices coincide), and an
  exponent of degree at most `d` in each letter has defect at most `2 * d` in
  absolute value.

## References

* The formal proof whose route this follows: the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207, file
  `New/UpperBound/ElementaryDivisors/TwistingData.lean` (`New.FrobeniusCycle`,
  `New.FrobeniusCycle.depth`, `New.FrobeniusCycle.defectWeight`,
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

/-- The Frobenius cycle obtained by composing the letter maps with a ring map `f : R →+* S`, for
instance the reduction modulo an ideal of `R`: the same prime, exponent and parities, the letter
maps `f.comp (ι s)` and the square root `f w`. -/
def map {S : Type*} [CommRing S] (f : R →+* S) : FrobeniusCycle W S N where
  p := T.p
  prime := T.prime
  e := T.e
  five_le_pow := T.five_le_pow
  ι s := f.comp (T.ι s)
  isEven := T.isEven
  isEven_add_one := T.isEven_add_one
  w := f T.w
  w_sq := by rw [← map_pow, T.w_sq, map_natCast]
  card_residueField := T.card_residueField
  dvd_ι_add_one_sub_pow s y := by
    simpa using map_dvd f (T.dvd_ι_add_one_sub_pow s y)

section Map

variable {S : Type*} [CommRing S] (f : R →+* S)

/-- `map` keeps the prime. -/
@[simp] theorem map_p : (T.map f).p = T.p := (rfl)

/-- `map` keeps the exponent. -/
@[simp] theorem map_e : (T.map f).e = T.e := (rfl)

/-- The letter maps of `map f` are those of the cycle followed by `f`. -/
@[simp] theorem map_ι (s : ZMod N) : (T.map f).ι s = f.comp (T.ι s) := (rfl)

/-- `map` keeps the parities. -/
@[simp] theorem map_isEven : (T.map f).isEven = T.isEven := (rfl)

/-- The square root of `p` of `map f` is the image of that of the cycle. -/
@[simp] theorem map_w : (T.map f).w = f T.w := (rfl)

/-- `map` keeps `P`. -/
@[simp] theorem map_P : (T.map f).P = T.P := by rw [P_def, P_def, map_p, map_e]

/-- `map` keeps `q`. -/
@[simp] theorem map_q : (T.map f).q = T.q := by rw [q_def, q_def, map_P]

/-- Changing the target along the identity does nothing. -/
@[simp] theorem map_id : T.map (RingHom.id R) = T := (rfl)

/-- Two successive changes of target are one change along the composite. -/
@[simp] theorem map_map {S' : Type*} [CommRing S'] (g : S →+* S') :
    (T.map f).map g = T.map (g.comp f) := (rfl)

end Map

/-- `P ≥ 5`. -/
theorem five_le_P : 5 ≤ T.P := by
  rw [P_def]
  exact T.five_le_pow

/-- The residue field of `W` has `q` elements. -/
theorem card_residueField_eq_q : Nat.card (ResidueField W) = T.q := by
  rw [q_def, P_def]
  exact T.card_residueField

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
  rw [q_def]
  calc 5 ≤ T.P := T.five_le_P
    _ ≤ T.P ^ N := Nat.le_self_pow (NeZero.ne N) _

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
  -- `ι s y ≡ ι s y ^ q` modulo `p` (the congruences around the cycle)
  have hcong : (T.p : R) ∣ T.ι s y - T.ι s y ^ T.q := by
    have h := T.dvd_ι_add_natCast_sub_pow s y N
    rwa [ZMod.natCast_self, add_zero, ← q_def] at h
  -- `1 - y ^ m` is a unit of `W`, so its image is a unit of `R`
  have hunit : IsUnit (T.ι s (1 - y ^ m)) :=
    (isUnit_one_sub_self_of_mem_nonunits _ ((mem_maximalIdeal _).mp
      ((maximalIdeal W).pow_mem_of_mem hy _ hm0))).map _
  have hprod : T.ι s y - T.ι s y ^ T.q = T.ι s y * T.ι s (1 - y ^ m) := by
    simp only [hm, map_sub, map_one, map_pow]
    ring
  rw [hprod] at hcong
  exact hunit.dvd_mul_right.mp hcong

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

/-- The letter matrix of the transpose of `g` is the transpose of the letter matrix of `g`. -/
@[simp]
theorem letterMatrix_unop_transposeMulEquiv (s : ZMod N) (g : GL (Fin k) W) :
    T.letterMatrix s (GeneralLinearGroup.transposeMulEquiv _ g).unop =
      (T.letterMatrix s g)ᵀ := by
  ext i j
  cases hs : T.isEven s <;>
    simp [hs, Matrix.coe_units_inv, ← Matrix.transpose_nonsing_inv]

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

/-- At every letter, the indices of the two weighted variables coincide exactly when
`a = a'`. -/
@[simp]
theorem negIndex_eq_posIndex_iff {a a' : Fin k} {s : ZMod N} :
    T.negIndex a a' s = T.posIndex a a' s ↔ a = a' := by
  unfold negIndex posIndex
  split_ifs
  exacts [Iff.rfl, eq_comm]

/-- The magnitude `P ^ (1 + (s - 1 - i).val) / (q - 1)` of the positive defect weight at the
letter `s`, for the reference letter `i`. -/
private noncomputable def posWeight (i s : ZMod N) : ℝ :=
  (T.P : ℝ) ^ (1 + (s - 1 - i).val) / (T.q - 1)

/-- The magnitude `P ^ (s - i).val / (q - 1)` of the negative defect weight at the letter `s`,
for the reference letter `i`. -/
private noncomputable def negWeight (i s : ZMod N) : ℝ :=
  (T.P : ℝ) ^ (s - i).val / (T.q - 1)

private theorem posWeight_nonneg (i s : ZMod N) : 0 ≤ T.posWeight i s := by
  have hq5 : (5 : ℝ) ≤ T.q := by exact_mod_cast T.five_le_q
  unfold posWeight
  exact div_nonneg (by positivity) (by linarith)

private theorem negWeight_nonneg (i s : ZMod N) : 0 ≤ T.negWeight i s := by
  have hq5 : (5 : ℝ) ≤ T.q := by exact_mod_cast T.five_le_q
  unfold negWeight
  exact div_nonneg (by positivity) (by linarith)

/-- The defect weights at the letter `i` along `(a, a')`: the variable `x (posIndex a a' s, s)`
has weight `P ^ (1 + (s - 1 - i).val) / (q - 1)`; if `a ≠ a'`, the variable
`x (negIndex a a' s, s)` has weight `-P ^ (s - i).val / (q - 1)`; every other variable has weight
`0`. When `a = a'` the two indices coincide and that variable gets the positive weight
(`defectWeight_posIndex`, `defectWeight_negIndex`). -/
noncomputable def defectWeight (a a' : Fin k) (i : ZMod N) (x : Fin k × ZMod N) : ℝ :=
  if x.1 = T.posIndex a a' x.2 then T.posWeight i x.2
  else if x.1 = T.negIndex a a' x.2 then -T.negWeight i x.2 else 0

/-- The defect weight of the variable of positive weight. It is a pre-`simp` rule, so that it
applies before `posIndex` is evaluated by parity. -/
@[simp↓]
theorem defectWeight_posIndex (a a' : Fin k) (i s : ZMod N) :
    T.defectWeight a a' i (T.posIndex a a' s, s) =
      (T.P : ℝ) ^ (1 + (s - 1 - i).val) / (T.q - 1) := by
  simp [defectWeight, posWeight]

/-- The defect weight of the variable of negative weight, for distinct indices. It is a
pre-`simp` rule, so that it applies before `negIndex` is evaluated by parity. -/
@[simp↓]
theorem defectWeight_negIndex {a a' : Fin k} (h : a ≠ a') (i s : ZMod N) :
    T.defectWeight a a' i (T.negIndex a a' s, s) = -((T.P : ℝ) ^ (s - i).val / (T.q - 1)) := by
  have hne : T.negIndex a a' s ≠ T.posIndex a a' s := mt T.negIndex_eq_posIndex_iff.mp h
  simp [defectWeight, hne, negWeight]

/-- The other variables have defect weight `0`. -/
@[simp]
theorem defectWeight_of_ne {a a' b : Fin k} {s : ZMod N} (hpos : b ≠ T.posIndex a a' s)
    (hneg : b ≠ T.negIndex a a' s) (i : ZMod N) : T.defectWeight a a' i (b, s) = 0 := by
  simp [defectWeight, hpos, hneg]

/-- At an even letter, the variable of index `a'` has the positive weight. -/
@[simp]
theorem defectWeight_right_of_isEven {s : ZMod N} (hs : T.isEven s = true) (a a' : Fin k)
    (i : ZMod N) :
    T.defectWeight a a' i (a', s) = (T.P : ℝ) ^ (1 + (s - 1 - i).val) / (T.q - 1) := by
  have h := T.defectWeight_posIndex a a' i s
  rwa [T.posIndex_of_isEven hs] at h

/-- At an odd letter, the variable of index `a` has the positive weight. -/
@[simp]
theorem defectWeight_left_of_not_isEven {s : ZMod N} (hs : T.isEven s = false) (a a' : Fin k)
    (i : ZMod N) :
    T.defectWeight a a' i (a, s) = (T.P : ℝ) ^ (1 + (s - 1 - i).val) / (T.q - 1) := by
  have h := T.defectWeight_posIndex a a' i s
  rwa [T.posIndex_of_not_isEven hs] at h

/-- At an even letter, the variable of index `a` has the negative weight if `a ≠ a'`. -/
@[simp]
theorem defectWeight_left_of_isEven {s : ZMod N} (hs : T.isEven s = true) {a a' : Fin k}
    (h : a ≠ a') (i : ZMod N) :
    T.defectWeight a a' i (a, s) = -((T.P : ℝ) ^ (s - i).val / (T.q - 1)) := by
  have h' := T.defectWeight_negIndex h i s
  rwa [T.negIndex_of_isEven hs] at h'

/-- At an odd letter, the variable of index `a'` has the negative weight if `a ≠ a'`. -/
@[simp]
theorem defectWeight_right_of_not_isEven {s : ZMod N} (hs : T.isEven s = false) {a a' : Fin k}
    (h : a ≠ a') (i : ZMod N) :
    T.defectWeight a a' i (a', s) = -((T.P : ℝ) ^ (s - i).val / (T.q - 1)) := by
  have h' := T.defectWeight_negIndex h i s
  rwa [T.negIndex_of_not_isEven hs] at h'

/-- The defect of an exponent at the letter `i` along `(a, a')`: its weighted degree for the
defect weights. -/
noncomputable def defect (a a' : Fin k) (i : ZMod N) : (Fin k × ZMod N →₀ ℕ) →+ ℝ :=
  Finsupp.weight (T.defectWeight a a' i)

/-- Unfolding `defect`. -/
theorem defect_apply (a a' : Fin k) (i : ZMod N) (β : Fin k × ZMod N →₀ ℕ) :
    T.defect a a' i β = β.sum fun x m ↦ m * T.defectWeight a a' i x := by
  simp [defect, Finsupp.weight_apply]

/-- The defect of a power of one variable. -/
@[simp]
theorem defect_single (a a' : Fin k) (i : ZMod N) (x : Fin k × ZMod N) (m : ℕ) :
    T.defect a a' i (Finsupp.single x m) = m * T.defectWeight a a' i x := by
  simp [defect, Finsupp.weight_single]

/-! ### Changing the target ring -/

section Map

variable {S : Type*} [CommRing S] (f : R →+* S)

/-- The letter matrices of `map f` are those of the cycle with `f` applied entrywise. -/
@[simp]
theorem map_letterMatrix (s : ZMod N) (g : GL (Fin k) W) :
    (T.map f).letterMatrix s g = (T.letterMatrix s g).map f := by
  cases hs : T.isEven s <;>
    simp only [letterMatrix_of_isEven, letterMatrix_of_not_isEven, map_isEven, hs,
      Matrix.map_map, map_ι, RingHom.coe_comp]

/-- `map` does not change depths. -/
@[simp]
theorem map_depth (r : ℕ) : (T.map f).depth (k := k) r = T.depth r := by
  refine AddMonoidHom.ext fun β ↦ ?_
  simp only [depth_apply, isDeep_iff, map_isEven]

/-- `map` does not change `posIndex`. -/
@[simp]
theorem map_posIndex (a a' : Fin k) (s : ZMod N) :
    (T.map f).posIndex a a' s = T.posIndex a a' s := by
  simp only [posIndex, map_isEven]

/-- `map` does not change `negIndex`. -/
@[simp]
theorem map_negIndex (a a' : Fin k) (s : ZMod N) :
    (T.map f).negIndex a a' s = T.negIndex a a' s := by
  simp only [negIndex, map_isEven]

/-- `map` does not change the defect weights. -/
@[simp]
theorem map_defectWeight (a a' : Fin k) (i : ZMod N) :
    (T.map f).defectWeight a a' i = T.defectWeight a a' i := by
  ext x
  simp only [defectWeight, posWeight, negWeight, map_posIndex, map_negIndex, map_P, map_q]

/-- `map` does not change defects. -/
@[simp]
theorem map_defect (a a' : Fin k) (i : ZMod N) :
    (T.map f).defect a a' i = T.defect a a' i := by
  simp only [defect, map_defectWeight]

end Map

open GeneralLinear in
/-- Two indices have the same label for `twoBlockLabel r` exactly when, at any letter, the
variables of the two indices are both deep for `r` or both not deep. -/
theorem twoBlockLabel_eq_iff_isDeep_iff (r : ℕ) (b b' : Fin k) (s : ZMod N) :
    twoBlockLabel r b = twoBlockLabel r b' ↔ (T.IsDeep r (b, s) ↔ T.IsDeep r (b', s)) := by
  rw [twoBlockLabel_eq_iff]
  cases hs : T.isEven s <;>
    simp only [isDeep_iff, hs, ← not_lt, not_iff_not, Bool.false_eq_true, Bool.true_eq_false,
      true_and, false_and, false_or, or_false]

/-! ### Bounds for the defect weights -/

/-- At each letter `s`, the defect weight of the variable at `posIndex` minus that of the
variable at `negIndex` lies in `[0, 3 / 2]`; it is `0` when the two indices coincide. -/
theorem defectWeight_sub_mem_Icc (a a' : Fin k) (i s : ZMod N) :
    T.defectWeight a a' i (T.posIndex a a' s, s) - T.defectWeight a a' i (T.negIndex a a' s, s) ∈
      Set.Icc (0 : ℝ) (3 / 2) := by
  have := T.neZero
  by_cases h : a = a'
  · -- for `a = a'` the two indices coincide and the difference is `0`
    subst h
    rw [T.negIndex_eq_posIndex_iff.mpr rfl, sub_self]
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

/-- Fix the reference letter `i` of the defect. At each letter `s`, the sum
`posWeight i s + negWeight i s` of the two magnitudes is an upper bound for the absolute value of
every defect weight of a variable at `s` (when `a = a'` only the first occurs). Summed over the
letters `s`, these bounds give `(P + 1) / (P - 1) ≤ 2`. -/
private theorem sum_posWeight_add_negWeight_le [NeZero N] (i : ZMod N) :
    ∑ s : ZMod N, (T.posWeight i s + T.negWeight i s) ≤ 2 := by
  simp only [posWeight, negWeight]
  have hP : (5 : ℝ) ≤ T.P := by exact_mod_cast T.five_le_P
  have hq5 : (5 : ℝ) ≤ T.q := by exact_mod_cast T.five_le_q
  set S := ∑ j ∈ Finset.range N, (T.P : ℝ) ^ j
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ by positivity
  have hq : (T.q : ℝ) - 1 = S * (T.P - 1) := by
    rw [geom_sum_mul, q_def, Nat.cast_pow]
  -- the two sums over the letters are geometric sums after shifting the residues
  have h2 (c : ZMod N) : ∑ s : ZMod N, (T.P : ℝ) ^ (s - c).val = S := by
    have hshift := (Equiv.subRight c).sum_comp fun s ↦ (T.P : ℝ) ^ s.val
    simp only [Equiv.subRight_apply] at hshift
    rw [hshift]
    exact ZMod.sum_val_eq_sum_range fun j ↦ (T.P : ℝ) ^ j
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
  -- `B s` bounds the absolute value of every defect weight at the letter `s`
  let B s := T.posWeight i s + T.negWeight i s
  have hB : ∀ s, 0 ≤ B s := fun s ↦ add_nonneg (T.posWeight_nonneg i s) (T.negWeight_nonneg i s)
  have hw : ∀ b s, |T.defectWeight a a' i (b, s)| ≤ B s := by
    intro b s
    have h1 := T.posWeight_nonneg i s
    have h2 := T.negWeight_nonneg i s
    unfold defectWeight
    split_ifs <;> simp only [abs_neg, abs_of_nonneg h1, abs_of_nonneg h2, abs_zero, B] <;>
      linarith
  have hsum : |T.defect a a' i β| ≤ d * ∑ s, B s := by
    rw [defect, Finsupp.weight_eq_sum]
    simp only [nsmul_eq_mul]
    rw [Fintype.sum_prod_type_right, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ ↦ ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ b, |(β (b, s) : ℝ) * T.defectWeight a a' i (b, s)|
        ≤ ∑ b, (β (b, s) : ℝ) * B s := Finset.sum_le_sum fun b _ ↦ by
          rw [abs_mul, Nat.abs_cast]
          exact mul_le_mul_of_nonneg_left (hw b s) (Nat.cast_nonneg _)
      _ ≤ d * B s := by
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hβ s) (hB s)
  refine hsum.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _) |>.trans_eq (mul_comm _ _))
  exact T.sum_posWeight_add_negWeight_le i

end FrobeniusCycle

end TauCeti
