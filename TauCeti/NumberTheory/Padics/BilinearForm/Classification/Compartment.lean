/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import TauCeti.NumberTheory.Padics.BilinearForm.Classification.Invariants
import Mathlib.Data.ZMod.Basic
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Parity
import TauCeti.LinearAlgebra.BilinearForm.Odd.LocalRing
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.NumberTheory.Padics.BilinearForm.OddUnimodular
import TauCeti.NumberTheory.Padics.BilinearForm.Oddity.Fusion
import TauCeti.NumberTheory.Padics.BilinearForm.SignWalking
import TauCeti.NumberTheory.Padics.DyadicUnits
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Compartment normalization for dyadic Jordan splittings

A *compartment* of a dyadic Jordan splitting `N` is a block `Finset.Icc c d` of consecutive type-I
(odd) constituents. Elementary moves supported inside the compartment — adjacent odd-odd sign
walking (`LinearMap.BilinForm.IsJordanSplitting.exists_signWalk_succ_of_odd_of_odd`), adjacent
oddity fusion (`LinearMap.BilinForm.IsJordanSplitting.exists_oddityFusion_succ`), and distance-two
sign walking (`LinearMap.BilinForm.IsJordanSplitting.exists_signWalk_add_two_of_odd_of_odd`) —
preserve two compartment invariants:

* the product of constituent signs `∏ i ∈ Finset.Icc c d, h.constituentSign i`, and
* the weighted compartment oddity-sign sum modulo `8`,
  `∑ i ∈ Finset.Icc c d, (h.constituentOddity hB i +`
  `if Odd (d + 1 - i) ∧ h.constituentSign i = -1 then 4 else 0)`.

This file proves that these two invariants are complete for a compartment: given two dyadic Jordan
splittings whose constituents on `Finset.Icc c d` are of type I with equal ranks, equal sign
products, and equal weighted compartment sums, elementary moves inside `Finset.Icc c d` normalize
the first splitting to match the signs and oddities of the second at every index in `Finset.Icc c d`
without changing any constituent outside `Finset.Icc c d`.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.exists_constituentSign_and_oddity_eq_on_Icc`:
  normalizing constituent signs and oddities across a type-I compartment `Finset.Icc c d`.

## Implementation notes

Each odd unimodular constituent falls into one of four rank classes (`n = 1`, `n = 2`, `n ≥ 3` odd,
`n ≥ 4` even), which determine both the realizable `(sign, oddity)` pairs and which unit residue
classes modulo `4` (`1` or `3`) the constituent represents. For length `2` (`d = c + 1`), a finite
search verifies that every valid pair reaches a canonical representative of its invariant fiber in
at most `2` adjacent moves, and moves are reversible. Longer compartments reduce to length `2` by
peeling off the left endpoint `c`: at most `2` moves on `(c, c + 1)` align `t_c + 4 s_c` modulo
`8`, and if necessary one distance-two sign walk on `(c, c + 2)` fixes `(s_c, t_c)` before applying
the induction hypothesis on `[c + 1, d]`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module ZMod
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

/-! ### Compartment invariants and finite-state transitions -/

section CompartmentState

/-- The sign boolean `decide (h.constituentSign i = -1)` used in finite-state calculations. -/
private noncomputable def signBool {M : Type*} [AddCommGroup M] [Module ℤ_[2] M]
    [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M] {B : BilinForm ℤ_[2] M}
    {N : ℕ → Submodule ℤ_[2] M} (h : B.IsJordanSplitting 2 N) (i : ℕ) : Bool :=
  decide (h.constituentSign i = -1)

/-- `signBool` determines `constituentSign` since `constituentSign ∈ {1, -1}`. -/
private theorem constituentSign_eq_iff_signBool_eq {M M' : Type*} [AddCommGroup M]
    [Module ℤ_[2] M] [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M] [AddCommGroup M']
    [Module ℤ_[2] M'] [Module.Free ℤ_[2] M'] [Module.Finite ℤ_[2] M']
    {B : BilinForm ℤ_[2] M} {N : ℕ → Submodule ℤ_[2] M}
    {B' : BilinForm ℤ_[2] M'} {N' : ℕ → Submodule ℤ_[2] M'}
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N') (i : ℕ) :
    h.constituentSign i = h'.constituentSign i ↔ signBool h i = signBool h' i := by
  unfold signBool
  rcases h.constituentSign_eq_one_or_neg_one i with h1 | h1 <;>
    rcases h'.constituentSign_eq_one_or_neg_one i with h2 | h2 <;>
    simp [h1, h2]

/-- The sign parity sum over a closed interval `[c, d]`, represented in `{0, 4} ⊆ ZMod 8`. -/
private def compS (s : ℕ → Bool) (c d : ℕ) : ZMod (2 ^ 3) :=
  ∑ i ∈ Finset.Icc c d, if s i then (4 : ZMod (2 ^ 3)) else 0

/-- The weighted oddity-sign invariant of a compartment `[c, d]` in `ZMod 8`. -/
private def compT (s : ℕ → Bool) (t : ℕ → ZMod (2 ^ 3)) (c d : ℕ) : ZMod (2 ^ 3) :=
  ∑ i ∈ Finset.Icc c d, (t i + if Odd (d + 1 - i) ∧ s i then 4 else 0)

/-- Classification of the rank `n ≥ 1` of a type-I constituent into four classes:
`0` (`n = 1`), `1` (`n = 2`), `2` (`n ≥ 3` odd), `3` (`n ≥ 4` even). -/
private def rankClass (n : ℕ) : Fin 4 :=
  if n = 1 then 0
  else if n = 2 then 1
  else if n % 2 = 1 then 2
  else 3

/-- Whether `(s, t)` is a realizable `(sign, oddity)` pair for an odd unimodular form of the given
rank class. -/
private def isValidOdd (rc : Fin 4) (s : Bool) (t : ZMod (2 ^ 3)) : Bool :=
  match rc with
  | 0 => (!s && (t == 1 || t == 7)) || (s && (t == 3 || t == 5))
  | 1 => t == 2 || t == 6 || (!s && t == 0) || (s && t == 4)
  | 2 => t == 1 || t == 3 || t == 5 || t == 7
  | 3 => t == 0 || t == 2 || t == 4 || t == 6

/-- Whether an odd unimodular form of rank class `rc` and invariants `(s, t)` represents a unit
congruent to `3` (`isThree = true`) or `1` (`isThree = false`) modulo `4`. -/
private def canRepMod4 (rc : Fin 4) (s : Bool) (t : ZMod (2 ^ 3)) (isThree : Bool) : Bool :=
  match rc with
  | 0 => if isThree then (t == 3 || t == 7) else (t == 1 || t == 5)
  | 1 => t == 0 || t == 4 || (t + (if s then 4 else 0) == if isThree then 6 else 2)
  | 2 => true
  | 3 => true

/-- For `n` units modulo `8`, their sum has the same parity as `n`. -/
private theorem zmod_eight_four_mul_sum_sub_card {ι : Type*} (s : Finset ι)
    (u : ι → ZMod (2 ^ 3)) (hu : ∀ i ∈ s, u i * u i = 1) :
    4 * (∑ i ∈ s, u i - s.card) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hua : u a * u a = 1 := hu a (Finset.mem_insert_self a s)
    have hs := ih fun i hi ↦ hu i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
    have key : ∀ x y : ZMod (2 ^ 3), x * x = 1 → 4 * y = 0 → 4 * (x - 1 + y) = 0 := by decide
    convert key (u a) (∑ i ∈ s, u i - s.card) hua hs using 2
    ring

/-- Every odd unimodular symmetric form over `ℤ_[2]` has valid `(sign, oddity)` in its rank class,
and represents a unit of residue `1` or `3` modulo `4` whenever `canRepMod4` holds. -/
private theorem isValidOdd_and_exists_rep_mod4 {M ι : Type*} [AddCommGroup M] [Module ℤ_[2] M]
    [Fintype ι] [DecidableEq ι] {C : BilinForm ℤ_[2] M} (hC : C.IsSymm)
    (b : Basis ι ℤ_[2] M) (hdet : IsUnit (C.toMatrix b).det) (hodd : ∃ x, IsUnit (C x x))
    {w : M} (hw : C.IsCharacteristic w) :
    let s := decide (χ₈ (PadicInt.toZModPow 3 (C.toMatrix b).det) = -1)
    let t := PadicInt.toZModPow 3 (C w w)
    isValidOdd (rankClass (Fintype.card ι)) s t = true ∧
      ∀ isThree : Bool, canRepMod4 (rankClass (Fintype.card ι)) s t isThree = true →
        ∃ x : M, IsUnit (C x x) ∧
          PadicInt.toZModPow 2 (C x x) = if isThree then 3 else 1 := by
  set n := Fintype.card ι
  let e := b.reindex (Fintype.equivFin ι)
  have hedet : (C.toMatrix e).det = (C.toMatrix b).det := det_toMatrix_reindex b _ C
  obtain ⟨c, hc, hcu⟩ :=
    hC.exists_orthogonal_basis_isUnit_of_exists_isUnit_apply_self e (hedet ▸ hdet) hodd
  have : Module.Free ℤ_[2] M := .of_basis c
  have : C.IsPerfPair := c.isPerfPair_of_isUnit_det c C (hc.isUnit_det_toMatrix hcu)
  let u : Fin n → ZMod (2 ^ 3) := fun i ↦ PadicInt.toZModPow 3 (C (c i) (c i))
  have hu : ∀ i, u i * u i = 1 := fun i ↦
    PadicInt.isUnit_iff_toZModPow_three_mul_self.mp (hcu i)
  have hP : IsUnit (c.toMatrix e).det :=
    Matrix.isUnit_det_of_right_inverse (c.toMatrix_mul_toMatrix_flip e)
  have hdet_eq : χ₈ (PadicInt.toZModPow 3 (C.toMatrix b).det) = χ₈ (∏ i, u i) := by
    rw [← hedet, det_toMatrix_eq_det_sq_mul_det c e, hc.det_toMatrix, map_mul, map_pow, map_mul,
      map_pow, map_prod]
    have hsq : ∀ x : ZMod (2 ^ 3), x * x = 1 → χ₈ x ^ 2 = 1 := by decide
    rw [hsq _ (PadicInt.isUnit_iff_toZModPow_three_mul_self.mp hP), one_mul]
  have ht_eq : PadicInt.toZModPow 3 (C w w) = ∑ i, u i := by
    have h8 := hw.eight_dvd_apply_self_sub_apply_self hC
      (hc.isCharacteristic_sum PadicInt.two_dvd_sq_sub_self)
    rw [hc.apply_sum_sum] at h8
    simpa [u, map_sum] using PadicInt.eight_dvd_sub_iff_toZModPow_three_eq.mp h8
  have hmod2 : ∀ (x : ℤ_[2]) (isThree : Bool),
      (PadicInt.toZModPow 3 x = (if isThree then 3 else 1) ∨
        PadicInt.toZModPow 3 x = (if isThree then 7 else 5)) →
      IsUnit x ∧ PadicInt.toZModPow 2 x = if isThree then 3 else 1 := by
    intro x isThree hx
    have hcast : PadicInt.toZModPow 2 x = ZMod.cast (PadicInt.toZModPow 3 x) :=
      (PadicInt.cast_toZModPow 2 3 (by decide) x).symm
    refine ⟨PadicInt.isUnit_iff_toZModPow_three_mul_self.mpr ?_, ?_⟩
    · cases isThree <;> rcases hx with hx | hx <;> rw [hx] <;> decide
    · rw [hcast]; cases isThree <;> rcases hx with hx | hx <;> rw [hx] <;> decide
  have hpos : 0 < n := by
    by_contra h0
    have : Module.Finite ℤ_[2] M := .of_basis c
    have hsub : Subsingleton M := (Module.finrank_eq_zero_iff_of_free ℤ_[2] M).mp
      (by rw [finrank_eq_card_basis c, Fintype.card_fin]; omega)
    obtain ⟨x, hx⟩ := hodd
    rw [Subsingleton.elim x 0, map_zero] at hx
    exact not_isUnit_zero hx
  dsimp only
  rw [hdet_eq, ht_eq]
  by_cases hn1 : n = 1
  · have hrc : rankClass n = 0 := by simp [rankClass, hn1]
    rw [hrc]
    let i0 : Fin n := ⟨0, by omega⟩
    have hprod1 : ∏ i, u i = u i0 :=
      Finset.prod_eq_single i0 (fun j _ hj ↦ absurd (Fin.ext (by omega)) hj) (by simp)
    have hsum1 : ∑ i, u i = u i0 :=
      Finset.sum_eq_single i0 (fun j _ hj ↦ absurd (Fin.ext (by omega)) hj) (by simp)
    rw [hprod1, hsum1]
    refine ⟨?_, fun isThree hcan ↦ ?_⟩
    · exact (by decide : ∀ a : ZMod (2 ^ 3), a * a = 1 →
        isValidOdd 0 (decide (χ₈ a = -1)) a = true) (u i0) (hu i0)
    · refine ⟨c i0, hmod2 (C (c i0) (c i0)) isThree ?_⟩
      exact (by decide : ∀ (a : ZMod (2 ^ 3)) (b : Bool), a * a = 1 →
        canRepMod4 0 (decide (χ₈ a = -1)) a b = true →
        a = (if b then 3 else 1) ∨ a = (if b then 7 else 5)) (u i0) isThree (hu i0) hcan
  · by_cases hn2 : n = 2
    · have hrc : rankClass n = 1 := by simp [rankClass, hn2]
      rw [hrc]
      let i0 : Fin n := ⟨0, by omega⟩
      let i1 : Fin n := ⟨1, by omega⟩
      have huniv : (Finset.univ : Finset (Fin n)) = {i0, i1} := by
        ext j
        simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff, Fin.ext_iff,
          i0, i1]
        omega
      have hne01 : i0 ≠ i1 := by simp [Fin.ext_iff, i0, i1]
      rw [show ∏ i, u i = u i0 * u i1 by rw [huniv, Finset.prod_pair hne01],
        show ∑ i, u i = u i0 + u i1 by rw [huniv, Finset.sum_pair hne01]]
      refine ⟨?_, fun isThree hcan ↦ ?_⟩
      · exact (by decide : ∀ a d : ZMod (2 ^ 3), a * a = 1 → d * d = 1 →
          isValidOdd 1 (decide (χ₈ (a * d) = -1)) (a + d) = true) (u i0) (u i1) (hu i0) (hu i1)
      · have key : ∀ (a d : ZMod (2 ^ 3)) (b : Bool), a * a = 1 → d * d = 1 →
            canRepMod4 1 (decide (χ₈ (a * d) = -1)) (a + d) b = true →
            (a = (if b then 3 else 1) ∨ a = (if b then 7 else 5)) ∨
            (d = (if b then 3 else 1) ∨ d = (if b then 7 else 5)) := by decide
        rcases key (u i0) (u i1) isThree (hu i0) (hu i1) hcan with h0 | h1
        · exact ⟨c i0, hmod2 _ isThree h0⟩
        · exact ⟨c i1, hmod2 _ isThree h1⟩
    · -- Rank `≥ 3`: parity determines `isValidOdd`, and `OddUnimodular` supplies mod-4 units.
      have hpar := zmod_eight_four_mul_sum_sub_card Finset.univ u fun i _ ↦ hu i
      simp only [Finset.card_univ, Fintype.card_fin] at hpar
      have h4n : 4 * (n : ZMod (2 ^ 3)) = if n % 2 = 1 then 4 else 0 := by
        have hq : n = 2 * (n / 2) + n % 2 := (Nat.div_add_mod n 2).symm
        have h42 : (4 : ZMod (2 ^ 3)) * 2 = 0 := by decide
        rcases Nat.mod_two_eq_zero_or_one n with hm | hm <;>
          simp only [hm, zero_ne_one, ↓reduceIte]
        · rw [hq, hm]; push_cast; linear_combination ((n / 2 : ℕ) : ZMod (2 ^ 3)) * h42
        · rw [hq, hm]; push_cast; linear_combination ((n / 2 : ℕ) : ZMod (2 ^ 3)) * h42
      have hvalid : isValidOdd (rankClass n)
          (decide (χ₈ (∏ i, u i) = -1)) (∑ i, u i) = true := by
        have h4s : 4 * ∑ i, u i = if n % 2 = 1 then 4 else 0 := by linear_combination hpar + h4n
        by_cases hmod : n % 2 = 1
        · rw [show rankClass n = 2 by simp [rankClass, hn1, hn2, hmod]]
          simp only [hmod, ↓reduceIte] at h4s
          exact (by decide : ∀ (s : Bool) (t : ZMod (2 ^ 3)), 4 * t = 4 →
            isValidOdd 2 s t = true) _ _ h4s
        · rw [show rankClass n = 3 by simp [rankClass, hn1, hn2, hmod]]
          simp only [hmod, ↓reduceIte] at h4s
          exact (by decide : ∀ (s : Bool) (t : ZMod (2 ^ 3)), 4 * t = 0 →
            isValidOdd 3 s t = true) _ _ h4s
      refine ⟨hvalid, fun isThree _ ↦ ?_⟩
      have hr : IsUnit (if isThree then (3 : ZMod (2 ^ 2)) else 1) := by
        cases isThree
        · exact isUnit_one
        · exact IsUnit.of_mul_eq_one 3 (by decide)
      exact hC.exists_isUnit_apply_self_toZModPow_two_eq_of_three_le b hdet hodd (by omega) hr

/-- Effect of the adjacent type-I move `(a, b)` on a pair of `(sign, oddity)` states. -/
private def pairStep (u : (Bool × ZMod (2 ^ 3)) × (Bool × ZMod (2 ^ 3))) (a b : Bool) :
    (Bool × ZMod (2 ^ 3)) × (Bool × ZMod (2 ^ 3)) :=
  let δ : ZMod (2 ^ 3) := if b then 6 else 2
  if a == b then
    ((!u.1.1, u.1.2 + δ), (!u.2.1, u.2.2 + δ))
  else
    ((u.1.1, u.1.2 + δ), (u.2.1, u.2.2 - δ))

/-- Whether `pairStep u a b` is a legal move for rank classes `(rc0, rc1)`. -/
private def pairCanStep (rc0 rc1 : Fin 4)
    (u : (Bool × ZMod (2 ^ 3)) × (Bool × ZMod (2 ^ 3))) (a b : Bool) : Bool :=
  canRepMod4 rc0 u.1.1 u.1.2 a && canRepMod4 rc1 u.2.1 u.2.2 b

/-- Reversing `pairStep` by flipping both choices `(a, b) ↦ (!a, !b)`. -/
private theorem pairStep_inv (rc0 rc1 : Fin 4)
    (u : (Bool × ZMod (2 ^ 3)) × (Bool × ZMod (2 ^ 3))) (a b : Bool)
    (hv0 : isValidOdd rc0 u.1.1 u.1.2 = true) (hv1 : isValidOdd rc1 u.2.1 u.2.2 = true)
    (hstep : pairCanStep rc0 rc1 u a b = true) :
    pairCanStep rc0 rc1 (pairStep u a b) (!a) (!b) = true ∧
      pairStep (pairStep u a b) (!a) (!b) = u := by
  rcases u with ⟨⟨s0, t0⟩, ⟨s1, t1⟩⟩
  revert s0 t0 s1 t1 a b hv0 hv1 hstep
  fin_cases rc0 <;> fin_cases rc1 <;> decide

/-- Whether `u` reaches `v` in at most `2` legal `pairStep` moves. -/
private def pairReach2 (rc0 rc1 : Fin 4)
    (u v : (Bool × ZMod (2 ^ 3)) × (Bool × ZMod (2 ^ 3))) : Bool :=
  u == v ||
  ([false, true].any fun a ↦ [false, true].any fun b ↦
    pairCanStep rc0 rc1 u a b && (pairStep u a b == v)) ||
  ([false, true].any fun a1 ↦ [false, true].any fun b1 ↦
    pairCanStep rc0 rc1 u a1 b1 &&
      let u1 := pairStep u a1 b1
      [false, true].any fun a2 ↦ [false, true].any fun b2 ↦
        pairCanStep rc0 rc1 u1 a2 b2 && (pairStep u1 a2 b2 == v))

/-- Unfolding `pairReach2` into `0`, `1`, or `2` legal `pairStep` moves. -/
private theorem pairReach2_iff (rc0 rc1 : Fin 4)
    (u v : (Bool × ZMod (2 ^ 3)) × (Bool × ZMod (2 ^ 3))) :
    pairReach2 rc0 rc1 u v = true ↔
      u = v ∨
      (∃ a b : Bool, pairCanStep rc0 rc1 u a b = true ∧ pairStep u a b = v) ∨
      (∃ a1 b1 : Bool, pairCanStep rc0 rc1 u a1 b1 = true ∧
        ∃ a2 b2 : Bool, pairCanStep rc0 rc1 (pairStep u a1 b1) a2 b2 = true ∧
          pairStep (pairStep u a1 b1) a2 b2 = v) := by
  have hmem (b : Bool) : b = false ∨ b = true := by cases b <;> simp
  unfold pairReach2
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_cons, List.not_mem_nil,
    or_false, Bool.and_eq_true, hmem, true_and, or_assoc]

/-- The two-constituent `(T, S)` invariant of a pair `u = ((s0, t0), (s1, t1))`. -/
private def pairInv (u : (Bool × ZMod (2 ^ 3)) × (Bool × ZMod (2 ^ 3))) :
    ZMod (2 ^ 3) × Bool :=
  (u.1.2 + u.2.2 + (if u.2.1 then 4 else 0), xor u.1.1 u.2.1)

/-- All 16 single-constituent `(sign, oddity)` pairs. -/
private def allStates : List (Bool × ZMod (2 ^ 3)) :=
  [false, true].flatMap fun s ↦ ([0, 1, 2, 3, 4, 5, 6, 7] : List (ZMod (2 ^ 3))).map fun t ↦ (s, t)

/-- Canonical representative in the `(T, S)` fiber for rank classes `(rc0, rc1)`. -/
private def pairCanon (rc0 rc1 : Fin 4) (inv : ZMod (2 ^ 3) × Bool) :
    (Bool × ZMod (2 ^ 3)) × (Bool × ZMod (2 ^ 3)) :=
  let allPairs := allStates.flatMap fun p ↦ allStates.map fun q ↦ (p, q)
  (allPairs.find? fun u ↦
    isValidOdd rc0 u.1.1 u.1.2 && isValidOdd rc1 u.2.1 u.2.2 && (pairInv u == inv)).getD
    ((false, 0), (false, 0))

/-- Every valid two-constituent state reaches the canonical representative of its `(T, S)` fiber
in at most `2` legal `pairStep` moves. -/
private theorem pairReach2_pairCanon (rc0 rc1 : Fin 4)
    (u : (Bool × ZMod (2 ^ 3)) × (Bool × ZMod (2 ^ 3)))
    (hv0 : isValidOdd rc0 u.1.1 u.1.2 = true) (hv1 : isValidOdd rc1 u.2.1 u.2.2 = true) :
    pairReach2 rc0 rc1 u (pairCanon rc0 rc1 (pairInv u)) = true := by
  rcases u with ⟨⟨s0, t0⟩, ⟨s1, t1⟩⟩
  revert s0 t0 s1 t1 hv0 hv1
  fin_cases rc0 <;> fin_cases rc1 <;> decide

/-- `pairStep` preserves validity of both constituents. -/
private theorem isValidOdd_pairStep (rc0 rc1 : Fin 4)
    (u : (Bool × ZMod (2 ^ 3)) × (Bool × ZMod (2 ^ 3))) (a b : Bool)
    (hv0 : isValidOdd rc0 u.1.1 u.1.2 = true) (hv1 : isValidOdd rc1 u.2.1 u.2.2 = true)
    (hstep : pairCanStep rc0 rc1 u a b = true) :
    isValidOdd rc0 (pairStep u a b).1.1 (pairStep u a b).1.2 = true ∧
      isValidOdd rc1 (pairStep u a b).2.1 (pairStep u a b).2.2 = true := by
  rcases u with ⟨⟨s0, t0⟩, ⟨s1, t1⟩⟩
  revert s0 t0 s1 t1 a b hv0 hv1 hstep
  fin_cases rc0 <;> fin_cases rc1 <;> decide

/-- Reversing a `pairReach2` chain from a valid starting state. -/
private theorem pairReach2_symm (rc0 rc1 : Fin 4)
    (u v : (Bool × ZMod (2 ^ 3)) × (Bool × ZMod (2 ^ 3)))
    (hu0 : isValidOdd rc0 u.1.1 u.1.2 = true) (hu1 : isValidOdd rc1 u.2.1 u.2.2 = true)
    (hreach : pairReach2 rc0 rc1 u v = true) : pairReach2 rc0 rc1 v u = true := by
  rw [pairReach2_iff] at hreach ⊢
  rcases hreach with rfl | ⟨a, b, hstep, rfl⟩ | ⟨a1, b1, hstep1, a2, b2, hstep2, rfl⟩
  · exact Or.inl rfl
  · obtain ⟨hinv, heq⟩ := pairStep_inv rc0 rc1 u a b hu0 hu1 hstep
    exact Or.inr (Or.inl ⟨!a, !b, hinv, heq⟩)
  · obtain ⟨hv10, hv11⟩ := isValidOdd_pairStep rc0 rc1 u a1 b1 hu0 hu1 hstep1
    obtain ⟨hinv2, heq2⟩ := pairStep_inv rc0 rc1 (pairStep u a1 b1) a2 b2 hv10 hv11 hstep2
    obtain ⟨hinv1, heq1⟩ := pairStep_inv rc0 rc1 u a1 b1 hu0 hu1 hstep1
    exact Or.inr (Or.inr ⟨!a2, !b2, hinv2, !a1, !b1, heq2.symm ▸ hinv1, heq2.symm ▸ heq1⟩)

/-- Every valid odd state represents at least one of `1` or `3` modulo `4`. -/
private theorem exists_canRepMod4 (rc : Fin 4) (s : Bool) (t : ZMod (2 ^ 3))
    (hv : isValidOdd rc s t = true) : ∃ b : Bool, canRepMod4 rc s t b = true := by
  revert rc s t hv
  decide

/-- Single-constituent `J`-invariant `t + 4s` modulo `8`. -/
private def stateJ (s : Bool) (t : ZMod (2 ^ 3)) : ZMod (2 ^ 3) :=
  t + if s then 4 else 0

/-- `pairStep` shifts `stateJ` of the first constituent by `2` (if `a = true`) or `6` (if
`a = false`), independently of `b`. -/
private theorem stateJ_pairStep_fst (u : (Bool × ZMod (2 ^ 3)) × (Bool × ZMod (2 ^ 3)))
    (a b : Bool) :
    stateJ (pairStep u a b).1.1 (pairStep u a b).1.2 =
      stateJ u.1.1 u.1.2 + if a then 2 else 6 := by
  rcases u with ⟨⟨s0, t0⟩, ⟨s1, t1⟩⟩
  revert s0 t0 s1 t1 a b
  decide

/-- Boolean check for reaching `stateJ s' t'` from `(s, t)` in at most two `canRepMod4` steps. -/
private def stateJReach2 (rc : Fin 4) (s : Bool) (t : ZMod (2 ^ 3))
    (s' : Bool) (t' : ZMod (2 ^ 3)) : Bool :=
  (stateJ s t == stateJ s' t') ||
  ([false, true].any fun a ↦
    canRepMod4 rc s t a && (stateJ s t + (if a then 2 else 6) == stateJ s' t')) ||
  ([false, true].any fun a1 ↦ [false, true].any fun a2 ↦
    canRepMod4 rc s t a1 &&
    (allStates.all fun p ↦
      !(isValidOdd rc p.1 p.2 && (stateJ p.1 p.2 == stateJ s t + if a1 then 2 else 6)) ||
        canRepMod4 rc p.1 p.2 a2) &&
    (stateJ s t + (if a1 then 2 else 6) + (if a2 then 2 else 6) == stateJ s' t'))

/-- For any two valid states of the same rank class, the first reaches the `stateJ` of the second
in at most two choices of `a : Bool` permitted by `canRepMod4`. -/
private theorem exists_steps_stateJ (rc : Fin 4) (s : Bool) (t : ZMod (2 ^ 3))
    (s' : Bool) (t' : ZMod (2 ^ 3))
    (hv : isValidOdd rc s t = true) (hv' : isValidOdd rc s' t' = true) :
    stateJ s t = stateJ s' t' ∨
    (∃ a : Bool, canRepMod4 rc s t a = true ∧
      stateJ s t + (if a then 2 else 6) = stateJ s' t') ∨
    (∃ a1 a2 : Bool, canRepMod4 rc s t a1 = true ∧
      (∀ (s1 : Bool) (t1 : ZMod (2 ^ 3)), isValidOdd rc s1 t1 = true →
        stateJ s1 t1 = stateJ s t + (if a1 then 2 else 6) → canRepMod4 rc s1 t1 a2 = true) ∧
      stateJ s t + (if a1 then 2 else 6) + (if a2 then 2 else 6) = stateJ s' t') := by
  have hreach : stateJReach2 rc s t s' t' = true := by
    revert s t s' t' hv hv'
    fin_cases rc <;> decide
  have hmem_all : ∀ (s1 : Bool) (t1 : ZMod (2 ^ 3)), (s1, t1) ∈ allStates := by decide
  unfold stateJReach2 at hreach
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_cons, List.not_mem_nil,
    or_false, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hreach
  rcases hreach with (h0 | ⟨a, -, h1⟩) | ⟨a1, -, a2, -, ⟨ha1, hall⟩, h2⟩
  · exact Or.inl h0
  · exact Or.inr (Or.inl ⟨a, h1⟩)
  · refine Or.inr (Or.inr ⟨a1, a2, ha1, fun s1 t1 hv1 hJ1 ↦ ?_, h2⟩)
    rcases hall (s1, t1) (hmem_all s1 t1) with hnot | hok
    · simp [hv1, hJ1] at hnot
    · exact hok

/-- Two states with the same `stateJ` are either equal or related by `(!s, t + 4)`. -/
private theorem eq_or_flip_of_stateJ_eq {s s' : Bool} {t t' : ZMod (2 ^ 3)}
    (h : stateJ s t = stateJ s' t') :
    (s = s' ∧ t = t') ∨ ((!s) = s' ∧ t + 4 = t') := by
  revert s s' t t' h
  decide

/-- Sums over `Finset.Icc c d` agree when two functions agree outside `{a, b}` and have the same
sum on `{a, b}`. -/
private theorem sum_Icc_eq_of_eq_outside_two {c d a b : ℕ} (ha : a ∈ Finset.Icc c d)
    (hb : b ∈ Finset.Icc c d) (hab : a ≠ b) {f g : ℕ → ZMod (2 ^ 3)}
    (hout : ∀ i, i ≠ a → i ≠ b → f i = g i) (hpair : f a + f b = g a + g b) :
    ∑ i ∈ Finset.Icc c d, f i = ∑ i ∈ Finset.Icc c d, g i := by
  have hb' : b ∈ (Finset.Icc c d).erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  rw [← Finset.add_sum_erase _ _ ha, ← Finset.add_sum_erase _ _ hb',
    ← Finset.add_sum_erase _ _ ha, ← Finset.add_sum_erase _ _ hb', ← add_assoc, ← add_assoc, hpair]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_erase, Finset.mem_erase] at hi
  exact hout i hi.2.1 hi.1

/-- A `pairStep` inside `[c, d]` preserves both `compT` and `compS` on `[c, d]`. -/
private theorem compT_and_compS_eq_of_pairStep {s s' : ℕ → Bool}
    {t t' : ℕ → ZMod (2 ^ 3)} {c d k : ℕ} (hck : c ≤ k) (hkd : k + 1 ≤ d)
    (hagree : ∀ i, i ≠ k → i ≠ k + 1 → s' i = s i ∧ t' i = t i)
    {a b : Bool}
    (hpair : ((s' k, t' k), (s' (k + 1), t' (k + 1))) =
      pairStep ((s k, t k), (s (k + 1), t (k + 1))) a b) :
    compT s' t' c d = compT s t c d ∧ compS s' c d = compS s c d := by
  have hk_mem : k ∈ Finset.Icc c d := Finset.mem_Icc.mpr ⟨hck, by omega⟩
  have hk1_mem : k + 1 ∈ Finset.Icc c d := Finset.mem_Icc.mpr ⟨by omega, hkd⟩
  have hpair1 := congrArg Prod.fst hpair
  have hpair2 := congrArg Prod.snd hpair
  rw [Prod.mk.injEq] at hpair1 hpair2
  have hpar : Odd (d + 1 - k) ↔ ¬Odd (d + 1 - (k + 1)) := by
    rw [show d + 1 - k = (d + 1 - (k + 1)) + 1 by omega, Nat.odd_add_one]
  refine ⟨sum_Icc_eq_of_eq_outside_two hk_mem hk1_mem (by omega) (fun i hi1 hi2 ↦ by
      obtain ⟨hs, ht⟩ := hagree i hi1 hi2; rw [hs, ht]) ?_,
    sum_Icc_eq_of_eq_outside_two hk_mem hk1_mem (by omega)
      (fun i hi1 hi2 ↦ by rw [(hagree i hi1 hi2).1]) ?_⟩
  · rw [hpair1.1, hpair1.2, hpair2.1, hpair2.2]
    by_cases ho : Odd (d + 1 - (k + 1))
    · have ho' : ¬Odd (d + 1 - k) := fun h ↦ hpar.mp h ho
      simp only [ho, ho', false_and, true_and, ↓reduceIte, add_zero]
      exact (by decide : ∀ (s0 s1 a b : Bool) (t0 t1 : ZMod (2 ^ 3)),
        (pairStep ((s0, t0), (s1, t1)) a b).1.2 +
          ((pairStep ((s0, t0), (s1, t1)) a b).2.2 +
            if (pairStep ((s0, t0), (s1, t1)) a b).2.1 then 4 else 0) =
        t0 + (t1 + if s1 then 4 else 0)) (s k) (s (k + 1)) a b (t k) (t (k + 1))
    · have ho' : Odd (d + 1 - k) := hpar.mpr ho
      simp only [ho, ho', false_and, true_and, ↓reduceIte, add_zero]
      exact (by decide : ∀ (s0 s1 a b : Bool) (t0 t1 : ZMod (2 ^ 3)),
        ((pairStep ((s0, t0), (s1, t1)) a b).1.2 +
            if (pairStep ((s0, t0), (s1, t1)) a b).1.1 then 4 else 0) +
          (pairStep ((s0, t0), (s1, t1)) a b).2.2 =
        (t0 + if s0 then 4 else 0) + t1) (s k) (s (k + 1)) a b (t k) (t (k + 1))
  · rw [hpair1.1, hpair2.1]
    exact (by decide : ∀ (s0 s1 a b : Bool) (t0 t1 : ZMod (2 ^ 3)),
      (if (pairStep ((s0, t0), (s1, t1)) a b).1.1 then (4 : ZMod (2 ^ 3)) else 0) +
        (if (pairStep ((s0, t0), (s1, t1)) a b).2.1 then 4 else 0) =
      (if s0 then 4 else 0) + (if s1 then 4 else 0)) (s k) (s (k + 1)) a b (t k) (t (k + 1))

/-- A distance-2 sign walk inside `[c, d]` preserves both `compT` and `compS` on `[c, d]`. -/
private theorem compT_and_compS_eq_of_flip_add_two {s s' : ℕ → Bool}
    {t t' : ℕ → ZMod (2 ^ 3)} {c d k : ℕ} (hck : c ≤ k) (hkd : k + 2 ≤ d)
    (hagree : ∀ i, i ≠ k → i ≠ k + 2 → s' i = s i ∧ t' i = t i)
    (hsk : s' k = !s k) (htk : t' k = t k + 4)
    (hsl : s' (k + 2) = !s (k + 2)) (htl : t' (k + 2) = t (k + 2) + 4) :
    compT s' t' c d = compT s t c d ∧ compS s' c d = compS s c d := by
  have hk_mem : k ∈ Finset.Icc c d := Finset.mem_Icc.mpr ⟨hck, by omega⟩
  have hk2_mem : k + 2 ∈ Finset.Icc c d := Finset.mem_Icc.mpr ⟨by omega, hkd⟩
  have hpar : Odd (d + 1 - k) ↔ Odd (d + 1 - (k + 2)) := by
    rw [show d + 1 - k = (d + 1 - (k + 2)) + 2 by omega]; simp [Nat.odd_add]
  refine ⟨sum_Icc_eq_of_eq_outside_two hk_mem hk2_mem (by omega) (fun i hi1 hi2 ↦ by
      obtain ⟨hs, ht⟩ := hagree i hi1 hi2; rw [hs, ht]) ?_,
    sum_Icc_eq_of_eq_outside_two hk_mem hk2_mem (by omega)
      (fun i hi1 hi2 ↦ by rw [(hagree i hi1 hi2).1]) ?_⟩
  · rw [hsk, htk, hsl, htl]
    by_cases ho : Odd (d + 1 - (k + 2))
    · simp only [ho, hpar.mpr ho, true_and]
      exact (by decide : ∀ (s0 s2 : Bool) (t0 t2 : ZMod (2 ^ 3)),
        (t0 + 4 + if !s0 then 4 else 0) + (t2 + 4 + if !s2 then 4 else 0) =
        (t0 + if s0 then 4 else 0) + (t2 + if s2 then 4 else 0))
        (s k) (s (k + 2)) (t k) (t (k + 2))
    · simp only [ho, hpar.not.mpr ho, false_and, ↓reduceIte, add_zero]
      exact (by decide : ∀ t0 t2 : ZMod (2 ^ 3), (t0 + 4) + (t2 + 4) = t0 + t2) (t k) (t (k + 2))
  · rw [hsk, hsl]
    exact (by decide : ∀ s0 s2 : Bool,
      (if !s0 then (4 : ZMod (2 ^ 3)) else 0) + (if !s2 then 4 else 0) =
      (if s0 then 4 else 0) + (if s2 then 4 else 0)) (s k) (s (k + 2))

end CompartmentState

/-! ### Realizing compartment moves on Jordan splittings -/

section CompartmentMoves

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] {B : BilinForm ℤ_[2] M}
  {N : ℕ → Submodule ℤ_[2] M}

/-- For a type-I constituent `N k`, its `(sign, oddity)` is valid in its rank class, and whenever
`canRepMod4` holds there exists `x ∈ N k` with `B x x = 2 ^ k * a` for a unit `a` of the prescribed
residue modulo `4`. -/
private theorem isValidOdd_constituent_and_exists_mem [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {k : ℕ}
    (hodd : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x) :
    isValidOdd (rankClass (finrank ℤ_[2] (N k))) (signBool h k) (h.constituentOddity hB k) = true ∧
    ∀ isThree : Bool,
      canRepMod4 (rankClass (finrank ℤ_[2] (N k))) (signBool h k) (h.constituentOddity hB k)
        isThree = true →
      ∃ x ∈ N k, ∃ a : ℤ_[2], IsUnit a ∧ B x x = 2 ^ k * a ∧
        PadicInt.toZModPow 2 a = if isThree then 3 else 1 := by
  have := h.free k
  have := h.finite k
  obtain ⟨C, hC, hCp⟩ := isModular_def.mp (h.isModular k)
  have h2k : (2 : ℤ_[2]) ^ k ∈ nonZeroDivisors ℤ_[2] :=
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k two_ne_zero)
  have hCs : C.IsSymm := IsSymm.of_smul h2k (hC ▸ hB.restrict (N k))
  let d := Module.finBasis ℤ_[2] (N k)
  have hdet : IsUnit (C.toMatrix d).det := d.isUnit_det_of_isPerfPair d C hCp
  obtain ⟨w, hw⟩ := hCs.exists_isCharacteristic PadicInt.two_dvd_sq_sub_self
  have hCodd : ∃ x : N k, IsUnit (C x x) := by
    obtain ⟨x, hx, a, ha, hxx⟩ := h.exists_mem_apply_self_eq_two_pow_mul hodd
    have hBC : (2 : ℤ_[2]) ^ k * C ⟨x, hx⟩ ⟨x, hx⟩ = B x x := by
      simpa using LinearMap.congr_fun₂ hC ⟨x, hx⟩ ⟨x, hx⟩
    have hEq : C ⟨x, hx⟩ ⟨x, hx⟩ = a := (mul_cancel_left_mem_nonZeroDivisors h2k).mp (hBC.trans hxx)
    exact ⟨⟨x, hx⟩, hEq ▸ ha⟩
  have hres := isValidOdd_and_exists_rep_mod4 hCs d hdet hCodd hw
  rw [Fintype.card_fin] at hres
  have hs : signBool h k = decide (χ₈ (PadicInt.toZModPow 3 (C.toMatrix d).det) = -1) := by
    simp only [signBool, h.constituentSign_eq hC d]
  rw [hs, h.constituentOddity_eq hB hC hw]
  refine ⟨hres.1, fun isThree hcan ↦ ?_⟩
  obtain ⟨x, hx, hmod⟩ := hres.2 isThree hcan
  have hBC : (2 : ℤ_[2]) ^ k * C x x = B x x := by
    simpa using LinearMap.congr_fun₂ hC x x
  exact ⟨x.1, x.2, C x x, hx, hBC.symm, hmod⟩

/-- Negating `constituentSign` flips `signBool`. -/
private theorem signBool_eq_not_of_constituentSign_eq_neg [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] {N' : ℕ → Submodule ℤ_[2] M} (h : B.IsJordanSplitting 2 N)
    (h' : B.IsJordanSplitting 2 N') {k : ℕ}
    (hneg : h'.constituentSign k = -h.constituentSign k) :
    signBool h' k = !signBool h k := by
  unfold signBool
  rcases h.constituentSign_eq_one_or_neg_one k with hk | hk <;> simp [hneg, hk]

/-- Sign walk between type I at `k` and type I at `k + 2`. -/
private theorem exists_move_odd_add_two_odd [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {k : ℕ}
    (hodd : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x)
    (hodd' : ¬∀ x ∈ N (k + 2), 2 * 2 ^ (k + 2) ∣ B x x) :
    ∃ N' : ℕ → Submodule ℤ_[2] M, ∃ h' : B.IsJordanSplitting 2 N',
      (∀ i, i ≠ k → i ≠ k + 2 → N' i = N i) ∧
      signBool h' k = !signBool h k ∧
      h'.constituentOddity hB k = h.constituentOddity hB k + 4 ∧
      signBool h' (k + 2) = !signBool h (k + 2) ∧
      h'.constituentOddity hB (k + 2) = h.constituentOddity hB (k + 2) + 4 := by
  obtain ⟨N', h', hagree, hdk, hdl, hok, hol⟩ :=
    h.exists_signWalk_add_two_of_odd_of_odd hB hodd hodd'
  have h5 : IsUnit (5 : ℤ_[2]) :=
    PadicInt.isUnit_iff_toZModPow_three_mul_self.mpr (by rw [map_ofNat]; decide)
  have hχ5 : χ₈ (PadicInt.toZModPow 3 (5 : ℤ_[2])) = -1 := by rw [map_ofNat]; decide
  have hsk := h.constituentSign_eq_mul_of_isSquare_det h' h5 hdk
  have hsl := h.constituentSign_eq_mul_of_isSquare_det h' h5 hdl
  rw [hχ5, neg_one_mul] at hsk hsl
  have htk := h.constituentOddity_eq_add_of_eight_dvd h' hB (δ := 4) hok
  have htl := h.constituentOddity_eq_add_of_eight_dvd h' hB (δ := 4) hol
  rw [map_ofNat] at htk htl
  exact ⟨N', h', hagree, signBool_eq_not_of_constituentSign_eq_neg h h' hsk, htk,
    signBool_eq_not_of_constituentSign_eq_neg h h' hsl, htl⟩

/-- Adjacent type-I move realizing `pairStep` on `(N k, N (k + 1))`. -/
private theorem exists_move_odd_odd [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {k : ℕ}
    (hodd0 : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x)
    (hodd1 : ¬∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x)
    (a b : Bool)
    (ha : canRepMod4 (rankClass (finrank ℤ_[2] (N k))) (signBool h k)
      (h.constituentOddity hB k) a = true)
    (hb : canRepMod4 (rankClass (finrank ℤ_[2] (N (k + 1)))) (signBool h (k + 1))
      (h.constituentOddity hB (k + 1)) b = true) :
    ∃ N' : ℕ → Submodule ℤ_[2] M, ∃ h' : B.IsJordanSplitting 2 N',
      (∀ i, i ≠ k → i ≠ k + 1 → N' i = N i) ∧
      ((signBool h' k, h'.constituentOddity hB k),
        (signBool h' (k + 1), h'.constituentOddity hB (k + 1))) =
        pairStep ((signBool h k, h.constituentOddity hB k),
          (signBool h (k + 1), h.constituentOddity hB (k + 1))) a b := by
  obtain ⟨x, hx, u, hu, hxx, humod⟩ := (isValidOdd_constituent_and_exists_mem h hB hodd0).2 a ha
  obtain ⟨y, hy, v, hv, hyy, hvmod⟩ := (isValidOdd_constituent_and_exists_mem h hB hodd1).2 b hb
  have h2v : PadicInt.toZModPow 3 (2 * v) = if b then 6 else 2 := by
    have h4 : (4 : ℤ_[2]) ∣ v - (if b then 3 else 1) := by
      rw [PadicInt.four_dvd_sub_iff_toZModPow_two_eq]
      cases b <;> simpa [map_ofNat] using hvmod.symm
    have h8 : (8 : ℤ_[2]) ∣ 2 * v - (if b then 6 else 2) := by
      obtain ⟨r, hr⟩ := h4
      refine ⟨r, ?_⟩
      cases b <;> simp only [↓reduceIte, Bool.false_eq_true] at hr ⊢ <;> linear_combination 2 * hr
    have := (PadicInt.eight_dvd_sub_iff_toZModPow_three_eq.mp h8).symm
    cases b <;> simpa [map_ofNat] using this
  by_cases hab : a = b
  · have huv : (4 : ℤ_[2]) ∣ u - v := by
      rw [PadicInt.four_dvd_sub_iff_toZModPow_two_eq, humod, hvmod, hab]
    obtain ⟨N', h', hagree, hdk, hdl, hok, hol⟩ :=
      h.exists_signWalk_succ_of_odd_of_odd hB hx hy hu hv hxx hyy huv
    have h3 : IsUnit (3 : ℤ_[2]) :=
      PadicInt.isUnit_iff_toZModPow_three_mul_self.mpr (by rw [map_ofNat]; decide)
    have hχ3 : χ₈ (PadicInt.toZModPow 3 (3 : ℤ_[2])) = -1 := by rw [map_ofNat]; decide
    have hsk := h.constituentSign_eq_mul_of_isSquare_det h' h3 hdk
    have hsl := h.constituentSign_eq_mul_of_isSquare_det h' h3 hdl
    rw [hχ3, neg_one_mul] at hsk hsl
    have htk := h.constituentOddity_eq_add_of_eight_dvd h' hB (δ := 2 * v) hok
    have htl := h.constituentOddity_eq_add_of_eight_dvd h' hB (δ := 2 * v) hol
    rw [h2v] at htk htl
    exact ⟨N', h', hagree, by
      simp [pairStep, hab, signBool_eq_not_of_constituentSign_eq_neg h h' hsk,
        signBool_eq_not_of_constituentSign_eq_neg h h' hsl, htk, htl]⟩
  · have huv : (4 : ℤ_[2]) ∣ u + v := by
      have : u + v = u - (-v) := by ring
      rw [this, PadicInt.four_dvd_sub_iff_toZModPow_two_eq, map_neg, humod, hvmod]
      cases a <;> cases b <;>
        first
        | exact absurd rfl hab
        | (simp only [↓reduceIte, Bool.false_eq_true]; decide)
    obtain ⟨N', h', hagree, hdk, hdl, hok, hol⟩ :=
      h.exists_oddityFusion_succ hB hx hy hu hv hxx hyy huv
    have hm1 : IsUnit (-1 : ℤ_[2]) := isUnit_one.neg
    have hχm1 : χ₈ (PadicInt.toZModPow 3 (-1 : ℤ_[2])) = 1 := by rw [map_neg, map_one]; decide
    have hsk := h.constituentSign_eq_mul_of_isSquare_det h' hm1
      (fun n d d' ↦ by simpa using hdk n d d')
    have hsl := h.constituentSign_eq_mul_of_isSquare_det h' hm1
      (fun n d d' ↦ by simpa using hdl n d d')
    rw [hχm1, one_mul] at hsk hsl
    have htk := h.constituentOddity_eq_add_of_eight_dvd h' hB (δ := 2 * v) hok
    have htl := h.constituentOddity_eq_add_of_eight_dvd h' hB (δ := -(2 * v))
      (fun C C' w w' hC hC' hw hw' ↦ by convert hol C C' w w' hC hC' hw hw' using 1; ring)
    rw [map_neg, h2v, ← sub_eq_add_neg] at htl
    rw [h2v] at htk
    exact ⟨N', h', hagree, by
      simp [pairStep, beq_false_of_ne hab, (constituentSign_eq_iff_signBool_eq h' h k).mp hsk,
        (constituentSign_eq_iff_signBool_eq h' h (k + 1)).mp hsl, htk, htl]⟩

/-- Realizing a `pairReach2` chain of at most `2` moves on `(N k, N (k + 1))`. -/
private theorem exists_isJordanSplitting_of_pairReach2 [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {k : ℕ}
    (hodd0 : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x)
    (hodd1 : ¬∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x)
    {v : (Bool × ZMod (2 ^ 3)) × (Bool × ZMod (2 ^ 3))}
    (hreach : pairReach2 (rankClass (finrank ℤ_[2] (N k)))
      (rankClass (finrank ℤ_[2] (N (k + 1))))
      ((signBool h k, h.constituentOddity hB k),
        (signBool h (k + 1), h.constituentOddity hB (k + 1))) v = true) :
    ∃ N' : ℕ → Submodule ℤ_[2] M, ∃ h' : B.IsJordanSplitting 2 N',
      (∀ i, i ≠ k → i ≠ k + 1 → N' i = N i) ∧
      ((signBool h' k, h'.constituentOddity hB k),
        (signBool h' (k + 1), h'.constituentOddity hB (k + 1))) = v := by
  rw [pairReach2_iff] at hreach
  rcases hreach with rfl | ⟨a, b, hstep, rfl⟩ | ⟨a1, b1, hstep1, a2, b2, hstep2, rfl⟩
  · exact ⟨N, h, fun _ _ _ ↦ rfl, rfl⟩
  · simp only [pairCanStep, Bool.and_eq_true] at hstep
    exact exists_move_odd_odd h hB hodd0 hodd1 a b hstep.1 hstep.2
  · simp only [pairCanStep, Bool.and_eq_true] at hstep1 hstep2
    obtain ⟨N1, h1, hagree1, hu1⟩ := exists_move_odd_odd h hB hodd0 hodd1 a1 b1 hstep1.1 hstep1.2
    have hrank1 (i : ℕ) : finrank ℤ_[2] (N1 i) = finrank ℤ_[2] (N i) :=
      h1.finrank_eq h two_ne_zero PadicInt.not_isUnit_two i
    have hpar1 (i : ℕ) : (∀ x ∈ N1 i, 2 * 2 ^ i ∣ B x x) ↔ ∀ x ∈ N i, 2 * 2 ^ i ∣ B x x :=
      ⟨fun he ↦ h1.forall_two_mul_pow_dvd_of_equivalent h (Equivalent.refl B)
          (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he,
        fun he ↦ h.forall_two_mul_pow_dvd_of_equivalent h1 (Equivalent.refl B)
          (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he⟩
    have hodd0' : ¬∀ x ∈ N1 k, 2 * 2 ^ k ∣ B x x := by rwa [hpar1 k]
    have hodd1' : ¬∀ x ∈ N1 (k + 1), 2 * 2 ^ (k + 1) ∣ B x x := by rwa [hpar1 (k + 1)]
    have h1_fst := congrArg Prod.fst hu1
    have h1_snd := congrArg Prod.snd hu1
    rw [Prod.mk.injEq] at h1_fst h1_snd
    have ha2 : canRepMod4 (rankClass (finrank ℤ_[2] (N1 k))) (signBool h1 k)
        (h1.constituentOddity hB k) a2 = true := by
      rw [hrank1 k, h1_fst.1, h1_fst.2]; exact hstep2.1
    have hb2 : canRepMod4 (rankClass (finrank ℤ_[2] (N1 (k + 1)))) (signBool h1 (k + 1))
        (h1.constituentOddity hB (k + 1)) b2 = true := by
      rw [hrank1 (k + 1), h1_snd.1, h1_snd.2]; exact hstep2.2
    obtain ⟨N2, h2, hagree2, hu2⟩ := exists_move_odd_odd h1 hB hodd0' hodd1' a2 b2 ha2 hb2
    exact ⟨N2, h2, fun i hik hik' ↦ (hagree2 i hik hik').trans (hagree1 i hik hik'), by
      rw [hu2, hu1]⟩

/-- Internal induction for compartment normalization on `[c, c + len]`. -/
private theorem exists_isJordanSplitting_matching_compartment [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] (hB : B.IsSymm) (s' : ℕ → Bool) (t' : ℕ → ZMod (2 ^ 3)) :
    ∀ (len c : ℕ) (N : ℕ → Submodule ℤ_[2] M) (h : B.IsJordanSplitting 2 N),
      (∀ i ∈ Finset.Icc c (c + len), ¬∀ x ∈ N i, 2 * 2 ^ i ∣ B x x) →
      (∀ i ∈ Finset.Icc c (c + len),
        isValidOdd (rankClass (finrank ℤ_[2] (N i))) (s' i) (t' i) = true) →
      compT (signBool h) (h.constituentOddity hB) c (c + len) = compT s' t' c (c + len) →
      compS (signBool h) c (c + len) = compS s' c (c + len) →
      ∃ N' : ℕ → Submodule ℤ_[2] M, ∃ h' : B.IsJordanSplitting 2 N',
        (∀ i, i ∉ Finset.Icc c (c + len) → N' i = N i) ∧
        ∀ i ∈ Finset.Icc c (c + len),
          signBool h' i = s' i ∧ h'.constituentOddity hB i = t' i
  | 0, c, N, h, _, _, hT, hS => by
    refine ⟨N, h, fun _ _ ↦ rfl, fun i hi ↦ ?_⟩
    have hic : i = c := by simp only [add_zero, Finset.mem_Icc] at hi; omega
    subst hic
    simp only [compS, compT, add_zero, Finset.Icc_self, Finset.sum_singleton,
      Nat.add_sub_cancel_left, odd_one, true_and] at hS hT
    have hs : signBool h i = s' i :=
      (by decide : ∀ a b : Bool,
        (if a then (4 : ZMod (2 ^ 3)) else 0) = (if b then 4 else 0) → a = b) _ _ hS
    rw [hs] at hT
    exact ⟨hs, add_right_cancel hT⟩
  | 1, c, N, h, hodd, hvalid', hT, hS => by
    have hodd0 : ¬∀ x ∈ N c, 2 * 2 ^ c ∣ B x x := hodd c (by simp)
    have hodd1 : ¬∀ x ∈ N (c + 1), 2 * 2 ^ (c + 1) ∣ B x x := hodd (c + 1) (by simp)
    have hv0 := (isValidOdd_constituent_and_exists_mem h hB hodd0).1
    have hv1 := (isValidOdd_constituent_and_exists_mem h hB hodd1).1
    have hv0' := hvalid' c (by simp)
    have hv1' := hvalid' (c + 1) (by simp)
    set u := ((signBool h c, h.constituentOddity hB c),
      (signBool h (c + 1), h.constituentOddity hB (c + 1)))
    set v := ((s' c, t' c), (s' (c + 1), t' (c + 1)))
    have hIcc : Finset.Icc c (c + 1) = {c, c + 1} := by
      ext i; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    have hinv_eq : pairInv u = pairInv v := by
      simp only [compT, compS, hIcc, Finset.sum_pair (show c ≠ c + 1 by omega)] at hT hS
      have h2 : ¬Odd (c + 1 + 1 - c) := by rw [show c + 1 + 1 - c = 2 by omega]; decide
      have h1 : Odd (c + 1 + 1 - (c + 1)) := by rw [show c + 1 + 1 - (c + 1) = 1 by omega]; decide
      simp only [h2, h1, false_and, true_and, ↓reduceIte, add_zero] at hT
      refine Prod.ext (by simpa [pairInv, u, v, add_assoc] using hT) ?_
      exact (by decide : ∀ a b e f : Bool,
        (if a then (4 : ZMod (2 ^ 3)) else 0) + (if b then 4 else 0) =
          (if e then 4 else 0) + (if f then 4 else 0) →
        xor a b = xor e f) _ _ _ _ hS
    set rc0 := rankClass (finrank ℤ_[2] (N c))
    set rc1 := rankClass (finrank ℤ_[2] (N (c + 1)))
    obtain ⟨N1, h1, hagree1, hu1⟩ := exists_isJordanSplitting_of_pairReach2 h hB hodd0 hodd1
      (pairReach2_pairCanon rc0 rc1 u hv0 hv1)
    have hrank1 (i : ℕ) : finrank ℤ_[2] (N1 i) = finrank ℤ_[2] (N i) :=
      h1.finrank_eq h two_ne_zero PadicInt.not_isUnit_two i
    have hpar1 (i : ℕ) : (∀ x ∈ N1 i, 2 * 2 ^ i ∣ B x x) ↔ ∀ x ∈ N i, 2 * 2 ^ i ∣ B x x :=
      ⟨fun he ↦ h1.forall_two_mul_pow_dvd_of_equivalent h (Equivalent.refl B)
          (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he,
        fun he ↦ h.forall_two_mul_pow_dvd_of_equivalent h1 (Equivalent.refl B)
          (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he⟩
    have hodd0' : ¬∀ x ∈ N1 c, 2 * 2 ^ c ∣ B x x := by rwa [hpar1 c]
    have hodd1' : ¬∀ x ∈ N1 (c + 1), 2 * 2 ^ (c + 1) ∣ B x x := by rwa [hpar1 (c + 1)]
    have hreach2 : pairReach2 (rankClass (finrank ℤ_[2] (N1 c)))
        (rankClass (finrank ℤ_[2] (N1 (c + 1))))
        ((signBool h1 c, h1.constituentOddity hB c),
          (signBool h1 (c + 1), h1.constituentOddity hB (c + 1))) v = true := by
      rw [hrank1 c, hrank1 (c + 1), hu1]
      exact pairReach2_symm rc0 rc1 v _ hv0' hv1'
        (hinv_eq.symm ▸ pairReach2_pairCanon rc0 rc1 v hv0' hv1')
    obtain ⟨N2, h2, hagree2, hu2⟩ :=
      exists_isJordanSplitting_of_pairReach2 h1 hB hodd0' hodd1' hreach2
    refine ⟨N2, h2, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · simp only [Finset.mem_Icc] at hi
      exact (hagree2 i (by omega) (by omega)).trans (hagree1 i (by omega) (by omega))
    · rw [hIcc, Finset.mem_insert, Finset.mem_singleton] at hi
      have hp1 := congrArg Prod.fst hu2
      have hp2 := congrArg Prod.snd hu2
      rw [Prod.mk.injEq] at hp1 hp2
      rcases hi with rfl | rfl
      · exact hp1
      · exact hp2
  | len + 2, c, N, h, hodd, hvalid', hT, hS => by
    have hodd0 : ¬∀ x ∈ N c, 2 * 2 ^ c ∣ B x x := hodd c (by simp)
    have hodd1 : ¬∀ x ∈ N (c + 1), 2 * 2 ^ (c + 1) ∣ B x x := hodd (c + 1) (by simp)
    have hodd2 : ¬∀ x ∈ N (c + 2), 2 * 2 ^ (c + 2) ∣ B x x := hodd (c + 2) (by simp)
    have hv0 := (isValidOdd_constituent_and_exists_mem h hB hodd0).1
    have hv0' := hvalid' c (by simp)
    -- Step 1: match `stateJ` at index `c` using at most `2` moves on `(c, c + 1)`.
    have hstep1 : ∀ (N0 : ℕ → Submodule ℤ_[2] M) (h0 : B.IsJordanSplitting 2 N0) (a : Bool),
        (¬∀ x ∈ N0 c, 2 * 2 ^ c ∣ B x x) → (¬∀ x ∈ N0 (c + 1), 2 * 2 ^ (c + 1) ∣ B x x) →
        canRepMod4 (rankClass (finrank ℤ_[2] (N0 c))) (signBool h0 c)
          (h0.constituentOddity hB c) a = true →
        ∃ N1 : ℕ → Submodule ℤ_[2] M, ∃ h1 : B.IsJordanSplitting 2 N1,
          (∀ i, i ≠ c → i ≠ c + 1 → N1 i = N0 i) ∧
          stateJ (signBool h1 c) (h1.constituentOddity hB c) =
            stateJ (signBool h0 c) (h0.constituentOddity hB c) + (if a then 2 else 6) ∧
          compT (signBool h1) (h1.constituentOddity hB) c (c + (len + 2)) =
            compT (signBool h0) (h0.constituentOddity hB) c (c + (len + 2)) ∧
          compS (signBool h1) c (c + (len + 2)) = compS (signBool h0) c (c + (len + 2)) := by
      intro N0 h0 a ho0 ho1 ha
      obtain ⟨b, hb⟩ := exists_canRepMod4 _ _ _ (isValidOdd_constituent_and_exists_mem h0 hB ho1).1
      obtain ⟨N1, h1, hagree1, hu1⟩ := exists_move_odd_odd h0 hB ho0 ho1 a b ha hb
      have hTS1 := compT_and_compS_eq_of_pairStep (c := c) (d := c + (len + 2)) (k := c)
        le_rfl (by omega) (fun i hi1 hi2 ↦
          ⟨(constituentSign_eq_iff_signBool_eq h1 h0 i).mp
              (h0.constituentSign_eq_of_eq h1 (hagree1 i hi1 hi2)),
            h0.constituentOddity_eq_of_eq h1 hB (hagree1 i hi1 hi2)⟩) hu1
      have hf := congrArg (fun p ↦ stateJ p.1.1 p.1.2) hu1
      rw [stateJ_pairStep_fst] at hf
      exact ⟨N1, h1, hagree1, hf, hTS1.1, hTS1.2⟩
    have hstepJ : ∃ N1 : ℕ → Submodule ℤ_[2] M, ∃ h1 : B.IsJordanSplitting 2 N1,
        (∀ i, i ≠ c → i ≠ c + 1 → N1 i = N i) ∧
        stateJ (signBool h1 c) (h1.constituentOddity hB c) = stateJ (s' c) (t' c) ∧
        compT (signBool h1) (h1.constituentOddity hB) c (c + (len + 2)) =
          compT s' t' c (c + (len + 2)) ∧
        compS (signBool h1) c (c + (len + 2)) = compS s' c (c + (len + 2)) := by
      rcases exists_steps_stateJ (rankClass (finrank ℤ_[2] (N c))) (signBool h c)
          (h.constituentOddity hB c) (s' c) (t' c) hv0 hv0' with
        hJ0 | ⟨a, ha, hJ1⟩ | ⟨a1, a2, ha1, ha2, hJ2⟩
      · exact ⟨N, h, fun _ _ _ ↦ rfl, hJ0, hT, hS⟩
      · obtain ⟨N1, h1, hagree1, hf1, hT1, hS1⟩ := hstep1 N h a hodd0 hodd1 ha
        exact ⟨N1, h1, hagree1, hf1.trans hJ1, hT1.trans hT, hS1.trans hS⟩
      · obtain ⟨N1, h1, hagree1, hf1, hT1, hS1⟩ := hstep1 N h a1 hodd0 hodd1 ha1
        have hrank1 (i : ℕ) : finrank ℤ_[2] (N1 i) = finrank ℤ_[2] (N i) :=
          h1.finrank_eq h two_ne_zero PadicInt.not_isUnit_two i
        have hpar1 (i : ℕ) : (∀ x ∈ N1 i, 2 * 2 ^ i ∣ B x x) ↔ ∀ x ∈ N i, 2 * 2 ^ i ∣ B x x :=
          ⟨fun he ↦ h1.forall_two_mul_pow_dvd_of_equivalent h (Equivalent.refl B)
              (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he,
            fun he ↦ h.forall_two_mul_pow_dvd_of_equivalent h1 (Equivalent.refl B)
              (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he⟩
        have hodd0' : ¬∀ x ∈ N1 c, 2 * 2 ^ c ∣ B x x := by rwa [hpar1 c]
        have hodd1' : ¬∀ x ∈ N1 (c + 1), 2 * 2 ^ (c + 1) ∣ B x x := by rwa [hpar1 (c + 1)]
        have hv1_0 := (isValidOdd_constituent_and_exists_mem h1 hB hodd0').1
        have ha2' : canRepMod4 (rankClass (finrank ℤ_[2] (N1 c))) (signBool h1 c)
            (h1.constituentOddity hB c) a2 = true := by
          rw [hrank1 c]
          exact ha2 _ _ (by rwa [← hrank1 c]) hf1
        obtain ⟨N2, h2, hagree2, hf2, hT2, hS2⟩ := hstep1 N1 h1 a2 hodd0' hodd1' ha2'
        exact ⟨N2, h2, fun i hic hic' ↦ (hagree2 i hic hic').trans (hagree1 i hic hic'),
          (hf2.trans (by rw [hf1])).trans hJ2, hT2.trans (hT1.trans hT), hS2.trans (hS1.trans hS)⟩
    obtain ⟨N1, h1, hagree1, hJ1, hT1, hS1⟩ := hstepJ
    have hpar1 (i : ℕ) : (∀ x ∈ N1 i, 2 * 2 ^ i ∣ B x x) ↔ ∀ x ∈ N i, 2 * 2 ^ i ∣ B x x :=
      ⟨fun he ↦ h1.forall_two_mul_pow_dvd_of_equivalent h (Equivalent.refl B)
          (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he,
        fun he ↦ h.forall_two_mul_pow_dvd_of_equivalent h1 (Equivalent.refl B)
          (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he⟩
    -- Step 2: if `(s c, t c) ≠ (s' c, t' c)`, flip `(c, c + 2)` by `exists_move_odd_add_two_odd`.
    have hstepC : ∃ N2 : ℕ → Submodule ℤ_[2] M, ∃ h2 : B.IsJordanSplitting 2 N2,
        (∀ i, i ∉ Finset.Icc c (c + (len + 2)) → N2 i = N i) ∧
        signBool h2 c = s' c ∧ h2.constituentOddity hB c = t' c ∧
        compT (signBool h2) (h2.constituentOddity hB) c (c + (len + 2)) =
          compT s' t' c (c + (len + 2)) ∧
        compS (signBool h2) c (c + (len + 2)) = compS s' c (c + (len + 2)) := by
      rcases eq_or_flip_of_stateJ_eq hJ1 with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · refine ⟨N1, h1, fun i hi ↦ ?_, hs, ht, hT1, hS1⟩
        simp only [Finset.mem_Icc] at hi
        exact hagree1 i (by omega) (by omega)
      · have hodd0' : ¬∀ x ∈ N1 c, 2 * 2 ^ c ∣ B x x := by rwa [hpar1 c]
        have hodd2' : ¬∀ x ∈ N1 (c + 2), 2 * 2 ^ (c + 2) ∣ B x x := by rwa [hpar1 (c + 2)]
        obtain ⟨N2, h2, hagree2, hsc, htc, hsl, htl⟩ :=
          exists_move_odd_add_two_odd h1 hB hodd0' hodd2'
        have hTS2 := compT_and_compS_eq_of_flip_add_two (c := c) (d := c + (len + 2)) (k := c)
          le_rfl (by omega) (fun i hi1 hi2 ↦
            ⟨(constituentSign_eq_iff_signBool_eq h2 h1 i).mp
                (h1.constituentSign_eq_of_eq h2 (hagree2 i hi1 hi2)),
              h1.constituentOddity_eq_of_eq h2 hB (hagree2 i hi1 hi2)⟩)
          hsc htc hsl htl
        refine ⟨N2, h2, fun i hi ↦ ?_, hsc.trans hs, htc.trans ht, hTS2.1.trans hT1,
          hTS2.2.trans hS1⟩
        simp only [Finset.mem_Icc] at hi
        exact (hagree2 i (by omega) (by omega)).trans (hagree1 i (by omega) (by omega))
    obtain ⟨N2, h2, hagree2, hsc2, htc2, hT2, hS2⟩ := hstepC
    have hrank2 (i : ℕ) : finrank ℤ_[2] (N2 i) = finrank ℤ_[2] (N i) :=
      h2.finrank_eq h two_ne_zero PadicInt.not_isUnit_two i
    have hpar2 (i : ℕ) : (∀ x ∈ N2 i, 2 * 2 ^ i ∣ B x x) ↔ ∀ x ∈ N i, 2 * 2 ^ i ∣ B x x :=
      ⟨fun he ↦ h2.forall_two_mul_pow_dvd_of_equivalent h (Equivalent.refl B)
          (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he,
        fun he ↦ h.forall_two_mul_pow_dvd_of_equivalent h2 (Equivalent.refl B)
          (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he⟩
    -- Step 3: peel off index `c` and apply the induction hypothesis to `[c + 1, c + len + 2]`.
    have hIcc_split :
        Finset.Icc c (c + (len + 2)) = insert c (Finset.Icc (c + 1) ((c + 1) + (len + 1))) := by
      ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hc_notMem : c ∉ Finset.Icc (c + 1) ((c + 1) + (len + 1)) := by
      simp only [Finset.mem_Icc]; omega
    have hT_sub : compT (signBool h2) (h2.constituentOddity hB) (c + 1)
        ((c + 1) + (len + 1)) = compT s' t' (c + 1) ((c + 1) + (len + 1)) := by
      unfold compT at hT2 ⊢
      rw [hIcc_split, Finset.sum_insert hc_notMem, Finset.sum_insert hc_notMem, hsc2, htc2] at hT2
      simpa only [show c + (len + 2) = (c + 1) + (len + 1) by omega] using add_left_cancel hT2
    have hS_sub : compS (signBool h2) (c + 1) ((c + 1) + (len + 1)) =
        compS s' (c + 1) ((c + 1) + (len + 1)) := by
      unfold compS at hS2 ⊢
      rw [hIcc_split, Finset.sum_insert hc_notMem, Finset.sum_insert hc_notMem, hsc2] at hS2
      exact add_left_cancel hS2
    have hodd_sub : ∀ i ∈ Finset.Icc (c + 1) ((c + 1) + (len + 1)),
        ¬∀ x ∈ N2 i, 2 * 2 ^ i ∣ B x x := fun i hi ↦ by
      rw [hpar2 i]
      exact hodd i (by rw [hIcc_split]; exact Finset.mem_insert_of_mem hi)
    have hvalid_sub : ∀ i ∈ Finset.Icc (c + 1) ((c + 1) + (len + 1)),
        isValidOdd (rankClass (finrank ℤ_[2] (N2 i))) (s' i) (t' i) = true := fun i hi ↦ by
      rw [hrank2 i]
      exact hvalid' i (by rw [hIcc_split]; exact Finset.mem_insert_of_mem hi)
    obtain ⟨N3, h3, hagree3, hmatch3⟩ := exists_isJordanSplitting_matching_compartment hB s' t'
      (len + 1) (c + 1) N2 h2 hodd_sub hvalid_sub hT_sub hS_sub
    refine ⟨N3, h3, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · exact (hagree3 i fun hm ↦ hi (by rw [hIcc_split]; exact Finset.mem_insert_of_mem hm)).trans
        (hagree2 i hi)
    · rw [hIcc_split, Finset.mem_insert] at hi
      rcases hi with rfl | hi'
      · have hsEq := (constituentSign_eq_iff_signBool_eq h3 h2 i).mp
          (h2.constituentSign_eq_of_eq h3 (hagree3 i hc_notMem))
        have htEq := h2.constituentOddity_eq_of_eq h3 hB (hagree3 i hc_notMem)
        exact ⟨hsEq.trans hsc2, htEq.trans htc2⟩
      · exact hmatch3 i hi'

/-- **Compartment normalization for dyadic Jordan splittings.** Let `B` and `B'` be symmetric
bilinear forms on finite free `ℤ_[2]`-modules with Jordan splittings `N` and `N'` with respect to
`2`. Suppose that on a closed interval `Finset.Icc c d`, every constituent of `N` and `N'` is of
type I, `N i` and `N' i` have equal rank, the compartment sign products agree, and the weighted
compartment oddity-sign sums agree modulo `8`. Then `B` admits a Jordan splitting `N''` agreeing
with `N` outside `Finset.Icc c d` whose constituent signs and oddities match those of `N'` on all
of `Finset.Icc c d`. -/
theorem IsJordanSplitting.exists_constituentSign_and_oddity_eq_on_Icc
    [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M'] [Module.Finite ℤ_[2] M']
    {B' : BilinForm ℤ_[2] M'} {N' : ℕ → Submodule ℤ_[2] M'}
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N')
    (hB : B.IsSymm) (hB' : B'.IsSymm) {c d : ℕ}
    (hrank : ∀ i ∈ Finset.Icc c d, finrank ℤ_[2] (N i) = finrank ℤ_[2] (N' i))
    (hodd : ∀ i ∈ Finset.Icc c d, ¬∀ v ∈ N i, 2 * 2 ^ i ∣ B v v)
    (hodd' : ∀ i ∈ Finset.Icc c d, ¬∀ v ∈ N' i, 2 * 2 ^ i ∣ B' v v)
    (hT : ∑ i ∈ Finset.Icc c d,
        (h.constituentOddity hB i + if Odd (d + 1 - i) ∧ h.constituentSign i = -1 then 4 else 0) =
      ∑ i ∈ Finset.Icc c d,
        (h'.constituentOddity hB' i +
          if Odd (d + 1 - i) ∧ h'.constituentSign i = -1 then 4 else 0))
    (hS : ∏ i ∈ Finset.Icc c d, h.constituentSign i = ∏ i ∈ Finset.Icc c d, h'.constituentSign i) :
    ∃ N'' : ℕ → Submodule ℤ_[2] M, ∃ h'' : B.IsJordanSplitting 2 N'',
      (∀ i, i ∉ Finset.Icc c d → N'' i = N i) ∧
      ∀ i ∈ Finset.Icc c d,
        h''.constituentSign i = h'.constituentSign i ∧
        h''.constituentOddity hB i = h'.constituentOddity hB' i := by
  by_cases hcd : c ≤ d
  · set len := d - c
    have hlen : c + len = d := by omega
    have hvalid' : ∀ i ∈ Finset.Icc c (c + len),
        isValidOdd (rankClass (finrank ℤ_[2] (N i))) (signBool h' i)
          (h'.constituentOddity hB' i) = true := fun i hi ↦ by
      rw [hlen] at hi
      rw [hrank i hi]
      exact (isValidOdd_constituent_and_exists_mem h' hB' (hodd' i hi)).1
    have hT' : compT (signBool h) (h.constituentOddity hB) c (c + len) =
        compT (signBool h') (h'.constituentOddity hB') c (c + len) := by
      simpa only [compT, signBool, hlen, decide_eq_true_eq] using hT
    have hS' : compS (signBool h) c (c + len) = compS (signBool h') c (c + len) := by
      have hp1 := h.prod_constituentSign_eq_ite (Finset.Icc c d)
      have hp2 := h'.prod_constituentSign_eq_ite (Finset.Icc c d)
      have h04 : ∀ s : ℕ → Bool, compS s c d = 0 ∨ compS s c d = 4 := by
        intro s
        unfold compS
        induction Finset.Icc c d using Finset.induction_on with
        | empty => left; simp
        | insert a u ha ih =>
          rw [Finset.sum_insert ha]
          have hkey : ∀ x y : ZMod (2 ^ 3), (x = 0 ∨ x = 4) → (y = 0 ∨ y = 4) →
              x + y = 0 ∨ x + y = 4 := by decide
          refine hkey _ _ ?_ ih
          cases s a <;> simp
      rw [hlen]
      change compS (signBool h) c d = compS (signBool h') c d
      rw [hp1, hp2] at hS
      have hsum1 : (∑ i ∈ Finset.Icc c d,
          if h.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) =
          compS (signBool h) c d := by
        simp [compS, signBool]
      have hsum2 : (∑ i ∈ Finset.Icc c d,
          if h'.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) =
          compS (signBool h') c d := by
        simp [compS, signBool]
      rw [hsum1, hsum2] at hS
      rcases h04 (signBool h) with h1 | h1 <;> rcases h04 (signBool h') with h2 | h2
      · exact h1.trans h2.symm
      · simp [h1, h2, show (0 : ZMod (2 ^ 3)) ≠ 4 by decide] at hS
      · simp [h1, h2, show (0 : ZMod (2 ^ 3)) ≠ 4 by decide] at hS
      · exact h1.trans h2.symm
    obtain ⟨N'', h'', hagree, hmatch⟩ := exists_isJordanSplitting_matching_compartment hB
      (signBool h') (h'.constituentOddity hB') len c N h (hlen.symm ▸ hodd) hvalid' hT' hS'
    rw [hlen] at hagree hmatch
    exact ⟨N'', h'', hagree, fun i hi ↦
      ⟨(constituentSign_eq_iff_signBool_eq h'' h' i).mpr (hmatch i hi).1, (hmatch i hi).2⟩⟩
  · refine ⟨N, h, fun _ _ ↦ rfl, fun i hi ↦ ?_⟩
    simp only [Finset.mem_Icc] at hi
    omega

end CompartmentMoves

end LinearMap.BilinForm
