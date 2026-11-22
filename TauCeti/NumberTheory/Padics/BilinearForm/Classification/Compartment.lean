/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import TauCeti.NumberTheory.Padics.BilinearForm.Classification.Invariants
import TauCeti.Algebra.BigOperators.Finset.Erase
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Parity
import TauCeti.LinearAlgebra.BilinearForm.Odd.LocalRing
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.NumberTheory.Padics.BilinearForm.OddUnimodular
import TauCeti.NumberTheory.Padics.BilinearForm.Oddity.Fusion
import TauCeti.NumberTheory.Padics.BilinearForm.SignWalking
import TauCeti.NumberTheory.Padics.DyadicUnits
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.SerreSigns
import TauCeti.Order.Interval.Finset.Basic

/-!
# Compartment normalization for dyadic Jordan splittings

A *compartment* of a dyadic Jordan splitting `N` is a block `Finset.Icc c d` of consecutive type-I
(odd) constituents. Elementary moves supported inside the compartment — adjacent odd-odd sign
walking, adjacent oddity fusion, and distance-two sign walking — preserve the compartment sign
product `∏ i ∈ Finset.Icc c d, h.constituentSign i` and the weighted oddity-sign sum modulo `8`.

This file proves that these two invariants are complete for a compartment
(`LinearMap.BilinForm.IsJordanSplitting.exists_constituentSign_and_oddity_eq_on_Icc`): elementary
moves inside `Finset.Icc c d` normalize the first splitting to match the signs and oddities of the
second at every index in `Finset.Icc c d` without changing any constituent outside `Finset.Icc c d`.

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

private abbrev State := Bool × ZMod (2 ^ 3)
private abbrev PairState := State × State

/-- The sign boolean `decide (h.constituentSign i = -1)` used in finite-state calculations. -/
private noncomputable def signBool {M : Type*} [AddCommGroup M] [Module ℤ_[2] M]
    [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M] {B : BilinForm ℤ_[2] M}
    {N : ℕ → Submodule ℤ_[2] M} (h : B.IsJordanSplitting 2 N) (i : ℕ) : Bool :=
  decide (h.constituentSign i = -1)

private theorem constituentSign_eq_iff_signBool_eq {M M' : Type*} [AddCommGroup M]
    [Module ℤ_[2] M] [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M] [AddCommGroup M']
    [Module ℤ_[2] M'] [Module.Free ℤ_[2] M'] [Module.Finite ℤ_[2] M']
    {B : BilinForm ℤ_[2] M} {N : ℕ → Submodule ℤ_[2] M}
    {B' : BilinForm ℤ_[2] M'} {N' : ℕ → Submodule ℤ_[2] M'}
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N') (i : ℕ) :
    h.constituentSign i = h'.constituentSign i ↔ signBool h i = signBool h' i := by
  unfold signBool
  rcases h.constituentSign_eq_one_or_neg_one i with h1 | h1 <;>
    rcases h'.constituentSign_eq_one_or_neg_one i with h2 | h2 <;> simp [h1, h2]

private def compS (s : ℕ → Bool) (c d : ℕ) : ZMod (2 ^ 3) :=
  ∑ i ∈ Finset.Icc c d, if s i then (4 : ZMod (2 ^ 3)) else 0

private def compT (s : ℕ → Bool) (t : ℕ → ZMod (2 ^ 3)) (c d : ℕ) : ZMod (2 ^ 3) :=
  ∑ i ∈ Finset.Icc c d, (t i + if Odd (d + 1 - i) ∧ s i then 4 else 0)

/-- Classification of the rank `n ≥ 1` of a type-I constituent: `0` (`n = 1`), `1` (`n = 2`),
`2` (`n ≥ 3` odd), `3` (`n ≥ 4` even). -/
private def rankClass (n : ℕ) : Fin 4 :=
  if n = 1 then 0 else if n = 2 then 1 else if n % 2 = 1 then 2 else 3

private def isValidOdd (rc : Fin 4) (s : Bool) (t : ZMod (2 ^ 3)) : Bool :=
  match rc with
  | 0 => (!s && (t == 1 || t == 7)) || (s && (t == 3 || t == 5))
  | 1 => t == 2 || t == 6 || (!s && t == 0) || (s && t == 4)
  | 2 => t == 1 || t == 3 || t == 5 || t == 7
  | 3 => t == 0 || t == 2 || t == 4 || t == 6

private def canRepMod4 (rc : Fin 4) (s : Bool) (t : ZMod (2 ^ 3)) (isThree : Bool) : Bool :=
  match rc with
  | 0 => if isThree then (t == 3 || t == 7) else (t == 1 || t == 5)
  | 1 => t == 0 || t == 4 || (t + (if s then 4 else 0) == if isThree then 6 else 2)
  | 2 => true
  | 3 => true

private theorem four_mul_natCast_zmod_eight (k : ℕ) :
    (4 : ZMod (2 ^ 3)) * k = if k % 2 = 1 then 4 else 0 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.cast_succ, mul_add, mul_one, ih]
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;>
      (rw [Nat.add_mod, hk]; decide)

private theorem χ₈_det_and_characteristic_eq_of_iIsOrtho {M : Type*} {n : ℕ} [AddCommGroup M]
    [Module ℤ_[2] M] {C : BilinForm ℤ_[2] M} (hC : C.IsSymm) (b c : Basis (Fin n) ℤ_[2] M)
    (hc : C.iIsOrtho c) (hcu : ∀ i, IsUnit (C (c i) (c i))) {w : M}
    (hw : C.IsCharacteristic w) :
    χ₈ (PadicInt.toZModPow 3 (C.toMatrix b).det) =
        χ₈ (∏ i, PadicInt.toZModPow 3 (C (c i) (c i))) ∧
      PadicInt.toZModPow 3 (C w w) = ∑ i, PadicInt.toZModPow 3 (C (c i) (c i)) := by
  have : Module.Free ℤ_[2] M := .of_basis c
  have : C.IsPerfPair := c.isPerfPair_of_isUnit_det c C (hc.isUnit_det_toMatrix hcu)
  refine ⟨?_, ?_⟩
  · rw [det_toMatrix_eq_det_sq_mul_det c b, hc.det_toMatrix, map_mul, map_pow, map_mul, map_pow,
      map_prod, (by decide : ∀ x : ZMod (2 ^ 3), x * x = 1 → χ₈ x ^ 2 = 1) _
        (PadicInt.isUnit_iff_toZModPow_three_mul_self.mp
          (Matrix.isUnit_det_of_right_inverse (c.toMatrix_mul_toMatrix_flip b))), one_mul]
  · have h8 := hw.eight_dvd_apply_self_sub_apply_self hC
      (hc.isCharacteristic_sum PadicInt.two_dvd_sq_sub_self)
    rw [hc.apply_sum_sum] at h8
    simpa [map_sum] using PadicInt.eight_dvd_sub_iff_toZModPow_three_eq.mp h8

/-- Every odd unimodular symmetric form over `ℤ_[2]` has valid `(sign, oddity)` in its rank class,
and represents a unit of residue `1` or `3` modulo `4` whenever `canRepMod4` holds. -/
private theorem isValidOdd_and_exists_rep_mod4 {M : Type*} {n : ℕ} [AddCommGroup M]
    [Module ℤ_[2] M] {C : BilinForm ℤ_[2] M} (hC : C.IsSymm) (b : Basis (Fin n) ℤ_[2] M)
    (hdet : IsUnit (C.toMatrix b).det) (hodd : ∃ x, IsUnit (C x x))
    {w : M} (hw : C.IsCharacteristic w) :
    let s := decide (χ₈ (PadicInt.toZModPow 3 (C.toMatrix b).det) = -1)
    let t := PadicInt.toZModPow 3 (C w w)
    isValidOdd (rankClass n) s t = true ∧
      ∀ isThree : Bool, canRepMod4 (rankClass n) s t isThree = true →
        ∃ x : M, IsUnit (C x x) ∧ PadicInt.toZModPow 2 (C x x) = if isThree then 3 else 1 := by
  obtain ⟨c, hc, hcu⟩ :=
    hC.exists_orthogonal_basis_isUnit_of_exists_isUnit_apply_self b hdet hodd
  let u (i : Fin n) : ZMod (2 ^ 3) := PadicInt.toZModPow 3 (C (c i) (c i))
  have hu (i : Fin n) : u i * u i = 1 := PadicInt.isUnit_iff_toZModPow_three_mul_self.mp (hcu i)
  obtain ⟨hdet_eq, ht_eq⟩ := χ₈_det_and_characteristic_eq_of_iIsOrtho hC b c hc hcu hw
  have hmod2 {x : ℤ_[2]} {isThree : Bool}
      (hx : PadicInt.toZModPow 3 x = (if isThree then 3 else 1) ∨
        PadicInt.toZModPow 3 x = (if isThree then 7 else 5)) :
      IsUnit x ∧ PadicInt.toZModPow 2 x = if isThree then 3 else 1 := by
    rw [PadicInt.isUnit_iff_toZModPow_three_mul_self, ← PadicInt.cast_toZModPow 2 3 (by decide) x]
    cases isThree <;> rcases hx with hx | hx <;> rw [hx] <;> decide
  dsimp only; rw [hdet_eq, ht_eq]
  -- Case split on the rank `n` matching the four `rankClass` branches (`0`, `1`, `2`, `≥ 3`).
  obtain rfl | rfl | rfl | ⟨m, rfl⟩ : n = 0 ∨ n = 1 ∨ n = 2 ∨ ∃ m, n = m + 3 :=
    match n with
    | 0 => Or.inl rfl | 1 => Or.inr (Or.inl rfl) | 2 => Or.inr (Or.inr (Or.inl rfl))
    | m + 3 => Or.inr (Or.inr (Or.inr ⟨m, rfl⟩))
  · -- Rank `0`: impossible because `C` represents a unit (`hodd`).
    have : Module.Free ℤ_[2] M := .of_basis c
    have : Module.Finite ℤ_[2] M := .of_basis c
    have : Subsingleton M := (Module.finrank_eq_zero_iff_of_free ℤ_[2] M).mp
      (by rw [finrank_eq_card_basis c, Fintype.card_fin])
    obtain ⟨x, hx⟩ := hodd
    exact absurd (Subsingleton.elim x 0 ▸ hx) (by simp)
  · -- Rank `1`: verify directly on the single diagonal entry `u 0`.
    simp only [rankClass, ↓reduceIte, Fin.prod_univ_one, Fin.sum_univ_one]
    refine ⟨(by decide : ∀ a : ZMod (2 ^ 3), a * a = 1 →
        isValidOdd 0 (decide (χ₈ a = -1)) a = true) (u 0) (hu 0),
      fun isThree hcan ↦ ⟨c 0, hmod2 ?_⟩⟩
    exact (by decide : ∀ (a : ZMod (2 ^ 3)) (b : Bool), a * a = 1 →
      canRepMod4 0 (decide (χ₈ a = -1)) a b = true →
      a = (if b then 3 else 1) ∨ a = (if b then 7 else 5)) (u 0) isThree (hu 0) hcan
  · -- Rank `2`: verify on the two diagonal entries `u 0, u 1`.
    have h21 : (2 : ℕ) ≠ 1 := by decide
    simp only [rankClass, h21, ↓reduceIte, Fin.prod_univ_two, Fin.sum_univ_two]
    refine ⟨(by decide : ∀ a d : ZMod (2 ^ 3), a * a = 1 → d * d = 1 →
        isValidOdd 1 (decide (χ₈ (a * d) = -1)) (a + d) = true) (u 0) (u 1) (hu 0) (hu 1),
      fun isThree hcan ↦ ?_⟩
    rcases (by decide : ∀ (a d : ZMod (2 ^ 3)) (b : Bool), a * a = 1 → d * d = 1 →
        canRepMod4 1 (decide (χ₈ (a * d) = -1)) (a + d) b = true →
        (a = (if b then 3 else 1) ∨ a = (if b then 7 else 5)) ∨
        (d = (if b then 3 else 1) ∨ d = (if b then 7 else 5)))
        (u 0) (u 1) isThree (hu 0) (hu 1) hcan with h0 | h1
    · exact ⟨c 0, hmod2 h0⟩
    · exact ⟨c 1, hmod2 h1⟩
  · -- Rank `≥ 3`: parity of `∑ i, u i` matches `n % 2`, and every unit mod `4` is represented.
    have h4s : 4 * ∑ i, u i = if (m + 3) % 2 = 1 then 4 else 0 := by
      rw [Finset.mul_sum, Finset.sum_congr rfl fun i _ ↦ (by decide : ∀ x : ZMod (2 ^ 3),
        x * x = 1 → 4 * x = 4) (u i) (hu i), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_comm, four_mul_natCast_zmod_eight]
    refine ⟨?_, fun isThree _ ↦ hC.exists_isUnit_apply_self_toZModPow_two_eq_of_three_le b hdet
      hodd (by simp)
      (by cases isThree <;> [exact isUnit_one; exact IsUnit.of_mul_eq_one 3 (by decide)])⟩
    have hm1 : m + 3 ≠ 1 := by omega
    have hm2 : m + 3 ≠ 2 := by omega
    by_cases hmod : (m + 3) % 2 = 1 <;>
      simp only [rankClass, hm1, hm2, hmod, ↓reduceIte] at h4s ⊢
    · exact (by decide : ∀ s (t : ZMod (2 ^ 3)), 4 * t = 4 → isValidOdd 2 s t = true) _ _ h4s
    · exact (by decide : ∀ s (t : ZMod (2 ^ 3)), 4 * t = 0 → isValidOdd 3 s t = true) _ _ h4s

private def pairStep (u : PairState) (a b : Bool) : PairState :=
  let δ : ZMod (2 ^ 3) := if b then 6 else 2
  if a == b then ((!u.1.1, u.1.2 + δ), (!u.2.1, u.2.2 + δ))
  else ((u.1.1, u.1.2 + δ), (u.2.1, u.2.2 - δ))

private def pairCanStep (rc0 rc1 : Fin 4) (u : PairState) (a b : Bool) : Bool :=
  canRepMod4 rc0 u.1.1 u.1.2 a && canRepMod4 rc1 u.2.1 u.2.2 b

private def pairValidPath (rc0 rc1 : Fin 4) :
    PairState → List (Bool × Bool) → PairState → Bool
  | u, [], v => u == v
  | u, (a, b) :: rest, v =>
    pairCanStep rc0 rc1 u a b && pairValidPath rc0 rc1 (pairStep u a b) rest v

private theorem pairStep_inv_and_valid (rc0 rc1 : Fin 4) (u : PairState) (a b : Bool)
    (hv0 : isValidOdd rc0 u.1.1 u.1.2 = true) (hv1 : isValidOdd rc1 u.2.1 u.2.2 = true)
    (hstep : pairCanStep rc0 rc1 u a b = true) :
    pairCanStep rc0 rc1 (pairStep u a b) (!a) (!b) = true ∧
      pairStep (pairStep u a b) (!a) (!b) = u ∧
      isValidOdd rc0 (pairStep u a b).1.1 (pairStep u a b).1.2 = true ∧
      isValidOdd rc1 (pairStep u a b).2.1 (pairStep u a b).2.2 = true := by
  rcases u with ⟨⟨s0, t0⟩, ⟨s1, t1⟩⟩
  revert s0 t0 s1 t1 a b hv0 hv1 hstep; fin_cases rc0 <;> fin_cases rc1 <;> decide

private theorem pairValidPath_append (rc0 rc1 : Fin 4) {u v w : PairState}
    {p q : List (Bool × Bool)} (hp : pairValidPath rc0 rc1 u p v = true)
    (hq : pairValidPath rc0 rc1 v q w = true) : pairValidPath rc0 rc1 u (p ++ q) w = true := by
  induction p generalizing u with
  | nil => simp only [pairValidPath, beq_iff_eq] at hp; simpa [hp]
  | cons s rest ih =>
    simp only [pairValidPath, Bool.and_eq_true, List.cons_append] at hp ⊢
    exact ⟨hp.1, ih hp.2⟩

private theorem pairValidPath_reverse (rc0 rc1 : Fin 4) {u v : PairState} {p : List (Bool × Bool)}
    (hu0 : isValidOdd rc0 u.1.1 u.1.2 = true) (hu1 : isValidOdd rc1 u.2.1 u.2.2 = true)
    (hp : pairValidPath rc0 rc1 u p v = true) :
    pairValidPath rc0 rc1 v (p.reverse.map fun s ↦ (!s.1, !s.2)) u = true := by
  induction p generalizing u with
  | nil => simp only [pairValidPath, beq_iff_eq] at hp; simp [pairValidPath, hp]
  | cons s rest ih =>
    simp only [pairValidPath, Bool.and_eq_true] at hp
    obtain ⟨hinv, heq, hv0, hv1⟩ := pairStep_inv_and_valid rc0 rc1 u s.1 s.2 hu0 hu1 hp.1
    rw [List.reverse_cons, List.map_append, List.map_singleton]
    exact pairValidPath_append rc0 rc1 (ih hv0 hv1 hp.2) (by simp [pairValidPath, hinv, heq])

private def pairInv (u : PairState) : ZMod (2 ^ 3) × Bool :=
  (u.1.2 + u.2.2 + (if u.2.1 then 4 else 0), xor u.1.1 u.2.1)

private def allStates : List State :=
  [false, true].flatMap fun s ↦
    ([0, 1, 2, 3, 4, 5, 6, 7] : List (ZMod (2 ^ 3))).map fun t ↦ (s, t)

private def pairCanon (rc0 rc1 : Fin 4) (inv : ZMod (2 ^ 3) × Bool) : PairState :=
  let v0 := allStates.filter fun p ↦ isValidOdd rc0 p.1 p.2
  let v1 := allStates.filter fun q ↦ isValidOdd rc1 q.1 q.2
  ((v0.flatMap fun p ↦ v1.map fun q ↦ (p, q)).find? fun u ↦ pairInv u == inv).getD
    ((false, 0), (false, 0))

private def pairPath2 (rc0 rc1 : Fin 4) (u v : PairState) : List (Bool × Bool) :=
  let steps : List (Bool × Bool) := [(false, false), (false, true), (true, false), (true, true)]
  let paths := [[]] ++ steps.map (fun s ↦ [s]) ++
    steps.flatMap fun s1 ↦ steps.map fun s2 ↦ [s1, s2]
  (paths.find? fun p ↦ pairValidPath rc0 rc1 u p v).getD []

private theorem pairValidPath_pairCanon (rc0 rc1 : Fin 4) (u : PairState)
    (hv0 : isValidOdd rc0 u.1.1 u.1.2 = true) (hv1 : isValidOdd rc1 u.2.1 u.2.2 = true) :
    pairValidPath rc0 rc1 u (pairPath2 rc0 rc1 u (pairCanon rc0 rc1 (pairInv u)))
      (pairCanon rc0 rc1 (pairInv u)) = true := by
  rcases u with ⟨⟨s0, t0⟩, ⟨s1, t1⟩⟩
  revert s0 t0 s1 t1 hv0 hv1; fin_cases rc0 <;> fin_cases rc1 <;> decide

private theorem exists_canRepMod4 (rc : Fin 4) (s : Bool) (t : ZMod (2 ^ 3))
    (hv : isValidOdd rc s t = true) : ∃ b : Bool, canRepMod4 rc s t b = true := by
  revert rc s t hv; decide

private def stateJ (s : Bool) (t : ZMod (2 ^ 3)) : ZMod (2 ^ 3) :=
  t + if s then 4 else 0

private theorem stateJ_pairStep_fst (u : PairState) (a b : Bool) :
    stateJ (pairStep u a b).1.1 (pairStep u a b).1.2 =
      stateJ u.1.1 u.1.2 + if a then 2 else 6 := by
  rcases u with ⟨⟨s0, t0⟩, ⟨s1, t1⟩⟩; revert s0 t0 s1 t1 a b; decide

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
  revert s t s' t' hv hv'; fin_cases rc <;> decide

private theorem eq_or_flip_of_stateJ_eq {s s' : Bool} {t t' : ZMod (2 ^ 3)}
    (h : stateJ s t = stateJ s' t') : (s = s' ∧ t = t') ∨ ((!s) = s' ∧ t + 4 = t') := by
  revert s s' t t' h; decide

private theorem compT_and_compS_eq_of_outside_two {s s' : ℕ → Bool}
    {t t' : ℕ → ZMod (2 ^ 3)} {c d a b : ℕ}
    (ha : a ∈ Finset.Icc c d) (hb : b ∈ Finset.Icc c d) (hab : a ≠ b)
    (hout : ∀ i, i ≠ a → i ≠ b → s' i = s i ∧ t' i = t i)
    (hT : (t' a + if Odd (d + 1 - a) ∧ s' a then 4 else 0) +
        (t' b + if Odd (d + 1 - b) ∧ s' b then 4 else 0) =
      (t a + if Odd (d + 1 - a) ∧ s a then 4 else 0) +
        (t b + if Odd (d + 1 - b) ∧ s b then 4 else 0))
    (hS : (if s' a then (4 : ZMod (2 ^ 3)) else 0) + (if s' b then 4 else 0) =
      (if s a then 4 else 0) + (if s b then 4 else 0)) :
    compT s' t' c d = compT s t c d ∧ compS s' c d = compS s c d :=
  ⟨Finset.sum_eq_of_eq_outside_two ha hb hab
    (fun i _ h1 h2 ↦ by rw [(hout i h1 h2).1, (hout i h1 h2).2]) hT,
   Finset.sum_eq_of_eq_outside_two ha hb hab (fun i _ h1 h2 ↦ by rw [(hout i h1 h2).1]) hS⟩

private theorem pairInv_eq_of_compT_compS {s s' : ℕ → Bool} {t t' : ℕ → ZMod (2 ^ 3)}
    {c : ℕ} (hT : compT s t c (c + 1) = compT s' t' c (c + 1))
    (hS : compS s c (c + 1) = compS s' c (c + 1)) :
    pairInv ((s c, t c), (s (c + 1), t (c + 1))) =
      pairInv ((s' c, t' c), (s' (c + 1), t' (c + 1))) := by
  have hne : c ≠ c + 1 := Nat.ne_of_lt (Nat.lt_succ_self c)
  have hd0 : c + 1 + 1 - c = 2 := by omega
  have hd1 : c + 1 + 1 - (c + 1) = 1 := by omega
  have hnotOdd2 : ¬Odd 2 := by decide
  simp only [compT, compS, Finset.Icc_self_add_one, Finset.sum_pair hne, hd0, hd1, hnotOdd2,
    odd_one, false_and, true_and, ↓reduceIte, add_zero] at hT hS
  refine Prod.ext (by simpa [pairInv, add_assoc] using hT) ?_
  exact (by decide : ∀ a b e f : Bool,
    (if a then (4 : ZMod (2 ^ 3)) else 0) + (if b then 4 else 0) =
      (if e then 4 else 0) + (if f then 4 else 0) → xor a b = xor e f) _ _ _ _ hS

private theorem compT_and_compS_eq_of_pairStep {s s' : ℕ → Bool} {t t' : ℕ → ZMod (2 ^ 3)}
    {c d k : ℕ} (hck : c ≤ k) (hkd : k + 1 ≤ d)
    (hagree : ∀ i, i ≠ k → i ≠ k + 1 → s' i = s i ∧ t' i = t i) {a b : Bool}
    (hpair : ((s' k, t' k), (s' (k + 1), t' (k + 1))) =
      pairStep ((s k, t k), (s (k + 1), t (k + 1))) a b) :
    compT s' t' c d = compT s t c d ∧ compS s' c d = compS s c d := by
  have hp1 := Prod.mk.injEq .. ▸ congrArg Prod.fst hpair
  have hp2 := Prod.mk.injEq .. ▸ congrArg Prod.snd hpair
  have hsub : d + 1 - k = (d + 1 - (k + 1)) + 1 := by omega
  have hpar : Odd (d + 1 - k) ↔ ¬Odd (d + 1 - (k + 1)) := by
    rw [hsub, Nat.odd_add_one]
  have hkey : ∀ (s0 s1 a b p : Bool) (t0 t1 : ZMod (2 ^ 3)),
      let q := pairStep ((s0, t0), (s1, t1)) a b
      ((q.1.2 + if !p && q.1.1 then 4 else 0) + (q.2.2 + if p && q.2.1 then 4 else 0) =
        (t0 + if !p && s0 then 4 else 0) + (t1 + if p && s1 then 4 else 0)) ∧
      ((if q.1.1 then (4 : ZMod (2 ^ 3)) else 0) + (if q.2.1 then 4 else 0) =
        (if s0 then 4 else 0) + (if s1 then 4 else 0)) := by decide
  have hdec := hkey (s k) (s (k + 1)) a b (decide (Odd (d + 1 - (k + 1)))) (t k) (t (k + 1))
  refine compT_and_compS_eq_of_outside_two (Finset.mem_Icc.mpr ⟨hck, by omega⟩)
    (Finset.mem_Icc.mpr ⟨by omega, hkd⟩) (by omega) hagree ?_
    (by rw [hp1.1, hp2.1]; exact hdec.2)
  rw [hp1.1, hp1.2, hp2.1, hp2.2]
  simpa only [hpar, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] using hdec.1

private theorem compT_and_compS_eq_of_flip_add_two {s s' : ℕ → Bool}
    {t t' : ℕ → ZMod (2 ^ 3)} {c d k : ℕ} (hck : c ≤ k) (hkd : k + 2 ≤ d)
    (hagree : ∀ i, i ≠ k → i ≠ k + 2 → s' i = s i ∧ t' i = t i)
    (hsk : s' k = !s k) (htk : t' k = t k + 4)
    (hsl : s' (k + 2) = !s (k + 2)) (htl : t' (k + 2) = t (k + 2) + 4) :
    compT s' t' c d = compT s t c d ∧ compS s' c d = compS s c d := by
  have hsub : d + 1 - k = (d + 1 - (k + 2)) + 2 := by omega
  have hpar : Odd (d + 1 - k) ↔ Odd (d + 1 - (k + 2)) := by
    rw [hsub]
    simp [Nat.odd_add]
  have hkey : ∀ (s0 s2 p : Bool) (t0 t2 : ZMod (2 ^ 3)),
      ((t0 + 4 + if p && !s0 then 4 else 0) + (t2 + 4 + if p && !s2 then 4 else 0) =
        (t0 + if p && s0 then 4 else 0) + (t2 + if p && s2 then 4 else 0)) ∧
      ((if !s0 then (4 : ZMod (2 ^ 3)) else 0) + (if !s2 then 4 else 0) =
        (if s0 then 4 else 0) + (if s2 then 4 else 0)) := by decide
  have hdec := hkey (s k) (s (k + 2)) (decide (Odd (d + 1 - (k + 2)))) (t k) (t (k + 2))
  refine compT_and_compS_eq_of_outside_two (Finset.mem_Icc.mpr ⟨hck, by omega⟩)
    (Finset.mem_Icc.mpr ⟨by omega, hkd⟩) (by omega) hagree ?_ (by rw [hsk, hsl]; exact hdec.2)
  rw [hsk, htk, hsl, htl]
  simpa only [hpar, Bool.and_eq_true, decide_eq_true_eq] using hdec.1

end CompartmentState

/-! ### Realizing compartment moves on Jordan splittings -/

section CompartmentMoves

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] [Module.Free ℤ_[2] M]
  [Module.Finite ℤ_[2] M] {B : BilinForm ℤ_[2] M} {N : ℕ → Submodule ℤ_[2] M}

private noncomputable def state (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) (k : ℕ) : State :=
  (signBool h k, h.constituentOddity hB k)

private noncomputable def pairState (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) (k : ℕ) :
    PairState :=
  (state h hB k, state h hB (k + 1))

private theorem state_of_pairState_eq (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {k : ℕ}
    {s0 s1 : Bool} {t0 t1 : ZMod (2 ^ 3)} (hp : pairState h hB k = ((s0, t0), (s1, t1))) :
    (signBool h k = s0 ∧ h.constituentOddity hB k = t0) ∧
      (signBool h (k + 1) = s1 ∧ h.constituentOddity hB (k + 1) = t1) := by
  have h1 := congrArg Prod.fst hp
  have h2 := congrArg Prod.snd hp
  simp only [pairState, state, Prod.mk.injEq] at h1 h2
  exact ⟨h1, h2⟩

private theorem signBool_eq_decide (h : B.IsJordanSplitting 2 N) {i : ℕ}
    {C : BilinForm ℤ_[2] (N i)} (hC : (2 : ℤ_[2]) ^ i • C = B.restrict (N i))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (d : Basis ι ℤ_[2] (N i)) :
    signBool h i = decide (χ₈ (PadicInt.toZModPow 3 (C.toMatrix d).det) = -1) := by
  simp only [signBool, h.constituentSign_eq hC d]

private theorem isValidOdd_constituent_and_exists_mem (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm)
    {k : ℕ} (hodd : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x) :
    isValidOdd (rankClass (finrank ℤ_[2] (N k))) (signBool h k)
      (h.constituentOddity hB k) = true ∧
    ∀ isThree : Bool,
      canRepMod4 (rankClass (finrank ℤ_[2] (N k))) (signBool h k) (h.constituentOddity hB k)
        isThree = true →
      ∃ x ∈ N k, ∃ a : ℤ_[2], IsUnit a ∧ B x x = 2 ^ k * a ∧
        PadicInt.toZModPow 2 a = if isThree then 3 else 1 := by
  have := h.free k; have := h.finite k
  let C := h.constituentForm k
  have hC := h.two_pow_smul_constituentForm k
  have h2k := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k (two_ne_zero (α := ℤ_[2])))
  let d := Module.finBasis ℤ_[2] (N k)
  have hCodd : ∃ x : N k, IsUnit (C x x) := by
    obtain ⟨x, hx, a, ha, hxx⟩ := h.exists_mem_apply_self_eq_two_pow_mul hodd
    have hBC : (2 : ℤ_[2]) ^ k * C ⟨x, hx⟩ ⟨x, hx⟩ = B x x := by
      simpa using LinearMap.congr_fun₂ hC ⟨x, hx⟩ ⟨x, hx⟩
    exact ⟨⟨x, hx⟩, ((mul_cancel_left_mem_nonZeroDivisors h2k).mp (hBC.trans hxx)) ▸ ha⟩
  have hres := isValidOdd_and_exists_rep_mod4 (h.isSymm_constituentForm hB k) d
    (d.isUnit_det_of_isPerfPair d C (h.isPerfPair_constituentForm k)) hCodd
    (h.isCharacteristic_constituentCharVec hB k)
  rw [signBool_eq_decide h hC d,
    h.constituentOddity_eq hB hC (h.isCharacteristic_constituentCharVec hB k)]
  refine ⟨hres.1, fun isThree hcan ↦ ?_⟩
  obtain ⟨x, hx, hmod⟩ := hres.2 isThree hcan
  exact ⟨x.val, x.property, C x x, hx, Eq.symm (by simpa using LinearMap.congr_fun₂ hC x x), hmod⟩

private theorem signBool_eq_not_of_constituentSign_eq_neg {N' : ℕ → Submodule ℤ_[2] M}
    (h : B.IsJordanSplitting 2 N) (h' : B.IsJordanSplitting 2 N') {k : ℕ}
    (hneg : h'.constituentSign k = -h.constituentSign k) : signBool h' k = !signBool h k := by
  unfold signBool
  rcases h.constituentSign_eq_one_or_neg_one k with hk | hk <;> simp [hneg, hk]

private theorem exists_move_odd_odd (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {k : ℕ}
    (hodd0 : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x)
    (hodd1 : ¬∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x) (a b : Bool)
    (ha : canRepMod4 (rankClass (finrank ℤ_[2] (N k))) (signBool h k)
      (h.constituentOddity hB k) a = true)
    (hb : canRepMod4 (rankClass (finrank ℤ_[2] (N (k + 1)))) (signBool h (k + 1))
      (h.constituentOddity hB (k + 1)) b = true) :
    ∃ N' : ℕ → Submodule ℤ_[2] M, ∃ h' : B.IsJordanSplitting 2 N',
      (∀ i, i ≠ k → i ≠ k + 1 → N' i = N i) ∧
      pairState h' hB k = pairStep (pairState h hB k) a b := by
  obtain ⟨x, hx, u, hu, hxx, humod⟩ := (isValidOdd_constituent_and_exists_mem h hB hodd0).2 a ha
  obtain ⟨y, hy, v, hv, hyy, hvmod⟩ := (isValidOdd_constituent_and_exists_mem h hB hodd1).2 b hb
  have h2v : PadicInt.toZModPow 3 (2 * v) = if b then 6 else 2 := by
    obtain ⟨r, hr⟩ := PadicInt.four_dvd_sub_iff_toZModPow_two_eq.mpr
      (by cases b <;> simpa [map_ofNat] using hvmod.symm :
        PadicInt.toZModPow 2 (if b then 3 else 1) = PadicInt.toZModPow 2 v)
    have h8 : (8 : ℤ_[2]) ∣ 2 * v - (if b then 6 else 2) :=
      ⟨r, by cases b <;> simp only [↓reduceIte, Bool.false_eq_true] at hr ⊢ <;>
        linear_combination 2 * hr⟩
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
    exact ⟨N', h', hagree, by
      simp [pairState, state, pairStep, hab,
        signBool_eq_not_of_constituentSign_eq_neg h h' hsk,
        signBool_eq_not_of_constituentSign_eq_neg h h' hsl,
        h.constituentOddity_eq_add_of_eight_dvd h' hB (δ := 2 * v) hok,
        h.constituentOddity_eq_add_of_eight_dvd h' hB (δ := 2 * v) hol, h2v]⟩
  · have huv : (4 : ℤ_[2]) ∣ u + v := by
      rw [← sub_neg_eq_add, PadicInt.four_dvd_sub_iff_toZModPow_two_eq, map_neg, humod, hvmod]
      cases a <;> cases b <;>
        first | exact absurd rfl hab | (simp only [↓reduceIte, Bool.false_eq_true]; decide)
    obtain ⟨N', h', hagree, hdk, hdl, hok, hol⟩ :=
      h.exists_oddityFusion_succ hB hx hy hu hv hxx hyy huv
    have hχm1 : χ₈ (PadicInt.toZModPow 3 (-1 : ℤ_[2])) = 1 := by rw [map_neg, map_one]; decide
    have hsk := h.constituentSign_eq_mul_of_isSquare_det h' isUnit_one.neg
      (fun n d d' ↦ by simpa using hdk n d d')
    have hsl := h.constituentSign_eq_mul_of_isSquare_det h' isUnit_one.neg
      (fun n d d' ↦ by simpa using hdl n d d')
    rw [hχm1, one_mul] at hsk hsl
    have htl := h.constituentOddity_eq_add_of_eight_dvd h' hB (δ := -(2 * v))
      (fun C C' w w' hC hC' hw hw' ↦ by convert hol C C' w w' hC hC' hw hw' using 1; ring)
    rw [map_neg, h2v, ← sub_eq_add_neg] at htl
    exact ⟨N', h', hagree, by
      simp [pairState, state, pairStep, beq_false_of_ne hab, htl,
        h.constituentOddity_eq_add_of_eight_dvd h' hB (δ := 2 * v) hok, h2v,
        (constituentSign_eq_iff_signBool_eq h' h k).mp hsk,
        (constituentSign_eq_iff_signBool_eq h' h (k + 1)).mp hsl]⟩

private theorem exists_isJordanSplitting_of_pairValidPath (hB : B.IsSymm) {k : ℕ}
    (p : List (Bool × Bool)) {v : PairState} :
    ∀ {N : ℕ → Submodule ℤ_[2] M} (h : B.IsJordanSplitting 2 N),
      (¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x) →
      (¬∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x) →
      pairValidPath (rankClass (finrank ℤ_[2] (N k))) (rankClass (finrank ℤ_[2] (N (k + 1))))
        (pairState h hB k) p v = true →
      ∃ N' : ℕ → Submodule ℤ_[2] M, ∃ h' : B.IsJordanSplitting 2 N',
        (∀ i, i ≠ k → i ≠ k + 1 → N' i = N i) ∧ pairState h' hB k = v := by
  induction p with
  | nil =>
    intro N h _ _ hp
    simp only [pairValidPath, beq_iff_eq] at hp
    exact ⟨N, h, fun _ _ _ ↦ rfl, hp⟩
  | cons s rest ih =>
    intro N h hodd0 hodd1 hp
    simp only [pairValidPath, pairCanStep, Bool.and_eq_true] at hp
    obtain ⟨N1, h1, hagree1, hu1⟩ := exists_move_odd_odd h hB hodd0 hodd1 s.1 s.2 hp.1.1 hp.1.2
    have hrank (i) := h1.finrank_eq h two_ne_zero PadicInt.not_isUnit_two i
    have hpar (i) := h1.forall_two_mul_pow_dvd_iff_of_isJordanSplitting h
      (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl i
    obtain ⟨N2, h2, hagree2, hu2⟩ := ih h1 (by rwa [hpar k]) (by rwa [hpar (k + 1)])
      (by rw [hrank k, hrank (k + 1), hu1]; exact hp.2)
    exact ⟨N2, h2, fun i h1' h2' ↦ (hagree2 i h1' h2').trans (hagree1 i h1' h2'), hu2⟩

private theorem exists_move_stateJ_step (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm)
    {c d : ℕ} (hcd : c + 1 ≤ d) (a : Bool)
    (hodd0 : ¬∀ x ∈ N c, 2 * 2 ^ c ∣ B x x)
    (hodd1 : ¬∀ x ∈ N (c + 1), 2 * 2 ^ (c + 1) ∣ B x x)
    (ha : canRepMod4 (rankClass (finrank ℤ_[2] (N c))) (signBool h c)
      (h.constituentOddity hB c) a = true) :
    ∃ N1 : ℕ → Submodule ℤ_[2] M, ∃ h1 : B.IsJordanSplitting 2 N1,
      (∀ i, i ≠ c → i ≠ c + 1 → N1 i = N i) ∧
      stateJ (signBool h1 c) (h1.constituentOddity hB c) =
        stateJ (signBool h c) (h.constituentOddity hB c) + (if a then 2 else 6) ∧
      compT (signBool h1) (h1.constituentOddity hB) c d =
        compT (signBool h) (h.constituentOddity hB) c d ∧
      compS (signBool h1) c d = compS (signBool h) c d := by
  obtain ⟨b, hb⟩ := exists_canRepMod4 _ _ _ (isValidOdd_constituent_and_exists_mem h hB hodd1).1
  obtain ⟨N1, h1, hagree1, hu1⟩ := exists_move_odd_odd h hB hodd0 hodd1 a b ha hb
  have hTS := compT_and_compS_eq_of_pairStep (c := c) (d := d) (k := c) le_rfl hcd
    (fun i h1' h2' ↦ ⟨(constituentSign_eq_iff_signBool_eq h1 h i).mp
      (h.constituentSign_eq_of_eq h1 (hagree1 i h1' h2')),
      h.constituentOddity_eq_of_eq h1 hB (hagree1 i h1' h2')⟩) hu1
  have hf := congrArg (fun p ↦ stateJ p.1.1 p.1.2) hu1
  rw [stateJ_pairStep_fst] at hf
  exact ⟨N1, h1, hagree1, hf, hTS.1, hTS.2⟩

/-- Match `stateJ` at the left endpoint `c` using at most two elementary moves on `(c, c + 1)`,
preserving the compartment invariants `compT` and `compS` on `[c, d]`. -/
private theorem exists_match_stateJ_at_left (hB : B.IsSymm) {N : ℕ → Submodule ℤ_[2] M}
    (h : B.IsJordanSplitting 2 N) {s' : ℕ → Bool} {t' : ℕ → ZMod (2 ^ 3)} {c d : ℕ}
    (hcd : c + 2 ≤ d) (hodd0 : ¬∀ x ∈ N c, 2 * 2 ^ c ∣ B x x)
    (hodd1 : ¬∀ x ∈ N (c + 1), 2 * 2 ^ (c + 1) ∣ B x x)
    (hvalid' : isValidOdd (rankClass (finrank ℤ_[2] (N c))) (s' c) (t' c) = true) :
    ∃ N1 : ℕ → Submodule ℤ_[2] M, ∃ h1 : B.IsJordanSplitting 2 N1,
      (∀ i, i ≠ c → i ≠ c + 1 → N1 i = N i) ∧
      stateJ (signBool h1 c) (h1.constituentOddity hB c) = stateJ (s' c) (t' c) ∧
      compT (signBool h1) (h1.constituentOddity hB) c d =
        compT (signBool h) (h.constituentOddity hB) c d ∧
      compS (signBool h1) c d = compS (signBool h) c d := by
  have h2nz : (2 : ℤ_[2]) ∈ nonZeroDivisors ℤ_[2] := mem_nonZeroDivisors_of_ne_zero two_ne_zero
  rcases exists_steps_stateJ (rankClass (finrank ℤ_[2] (N c))) (signBool h c)
      (h.constituentOddity hB c) (s' c) (t' c)
      (isValidOdd_constituent_and_exists_mem h hB hodd0).1 hvalid' with
    hJ0 | ⟨a, ha, hJ1⟩ | ⟨a1, a2, ha1, ha2, hJ2⟩
  · exact ⟨N, h, fun _ _ _ ↦ rfl, hJ0, rfl, rfl⟩
  · obtain ⟨N1, h1, hagree1, hf1, hT1, hS1⟩ :=
      exists_move_stateJ_step h hB (d := d) (by omega) a hodd0 hodd1 ha
    exact ⟨N1, h1, hagree1, hf1.trans hJ1, hT1, hS1⟩
  · obtain ⟨N1, h1, hagree1, hf1, hT1, hS1⟩ :=
      exists_move_stateJ_step h hB (d := d) (by omega) a1 hodd0 hodd1 ha1
    have hrank1 := h1.finrank_eq h two_ne_zero PadicInt.not_isUnit_two c
    have hpar1 (i) := h1.forall_two_mul_pow_dvd_iff_of_isJordanSplitting h h2nz dvd_rfl i
    have hodd0' : ¬∀ x ∈ N1 c, 2 * 2 ^ c ∣ B x x := by rwa [hpar1 c]
    obtain ⟨N2, h2, hagree2, hf2, hT2, hS2⟩ :=
      exists_move_stateJ_step h1 hB (d := d) (by omega) a2 hodd0' (by rwa [hpar1 (c + 1)])
        (by rw [hrank1]; exact ha2 _ _
              (hrank1 ▸ (isValidOdd_constituent_and_exists_mem h1 hB hodd0').1) hf1)
    exact ⟨N2, h2, fun i h1' h2' ↦ (hagree2 i h1' h2').trans (hagree1 i h1' h2'),
      (hf2.trans (by rw [hf1])).trans hJ2, hT2.trans hT1, hS2.trans hS1⟩

/-- Given a match in `stateJ` at `c`, match `(signBool, constituentOddity)` at `c` by a
distance-two sign walk on `(c, c + 2)` if needed, preserving `compT` and `compS` on `[c, d]`. -/
private theorem exists_match_state_at_left_of_stateJ_eq (hB : B.IsSymm)
    {N1 : ℕ → Submodule ℤ_[2] M} (h1 : B.IsJordanSplitting 2 N1) {s' : ℕ → Bool}
    {t' : ℕ → ZMod (2 ^ 3)} {c d : ℕ} (hcd : c + 2 ≤ d)
    (hodd0 : ¬∀ x ∈ N1 c, 2 * 2 ^ c ∣ B x x)
    (hodd2 : ¬∀ x ∈ N1 (c + 2), 2 * 2 ^ (c + 2) ∣ B x x)
    (hJ1 : stateJ (signBool h1 c) (h1.constituentOddity hB c) = stateJ (s' c) (t' c)) :
    ∃ N2 : ℕ → Submodule ℤ_[2] M, ∃ h2 : B.IsJordanSplitting 2 N2,
      (∀ i, i ∉ Finset.Icc c d → N2 i = N1 i) ∧
      signBool h2 c = s' c ∧ h2.constituentOddity hB c = t' c ∧
      compT (signBool h2) (h2.constituentOddity hB) c d =
        compT (signBool h1) (h1.constituentOddity hB) c d ∧
      compS (signBool h2) c d = compS (signBool h1) c d := by
  rcases eq_or_flip_of_stateJ_eq hJ1 with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact ⟨N1, h1, fun _ _ ↦ rfl, hs, ht, rfl, rfl⟩
  · obtain ⟨N2, h2, hagree2, hdk, hdl, hok, hol⟩ :=
      h1.exists_signWalk_add_two_of_odd_of_odd hB hodd0 hodd2
    obtain ⟨hsk, htc⟩ :=
      h1.constituentSign_eq_neg_and_oddity_eq_add_four_of_isSquare_five h2 hB hdk hok
    obtain ⟨hslk, htl⟩ :=
      h1.constituentSign_eq_neg_and_oddity_eq_add_four_of_isSquare_five h2 hB hdl hol
    have hsc := signBool_eq_not_of_constituentSign_eq_neg h1 h2 hsk
    have hsl := signBool_eq_not_of_constituentSign_eq_neg h1 h2 hslk
    have hTS2 := compT_and_compS_eq_of_flip_add_two (c := c) (d := d) (k := c) le_rfl hcd
      (fun i h1' h2' ↦ ⟨(constituentSign_eq_iff_signBool_eq h2 h1 i).mp
        (h1.constituentSign_eq_of_eq h2 (hagree2 i h1' h2')),
        h1.constituentOddity_eq_of_eq h2 hB (hagree2 i h1' h2')⟩) hsc htc hsl htl
    exact ⟨N2, h2, fun i hi ↦ by
        simp only [Finset.mem_Icc] at hi
        exact hagree2 i (by omega) (by omega),
      hsc.trans hs, htc.trans ht, hTS2.1, hTS2.2⟩

/-- Internal induction for compartment normalization on `[c, c + len]`. -/
private theorem exists_isJordanSplitting_matching_compartment (hB : B.IsSymm) (s' : ℕ → Bool)
    (t' : ℕ → ZMod (2 ^ 3)) :
    ∀ (len c : ℕ) (N : ℕ → Submodule ℤ_[2] M) (h : B.IsJordanSplitting 2 N),
      (∀ i ∈ Finset.Icc c (c + len), ¬∀ x ∈ N i, 2 * 2 ^ i ∣ B x x) →
      (∀ i ∈ Finset.Icc c (c + len),
        isValidOdd (rankClass (finrank ℤ_[2] (N i))) (s' i) (t' i) = true) →
      compT (signBool h) (h.constituentOddity hB) c (c + len) = compT s' t' c (c + len) →
      compS (signBool h) c (c + len) = compS s' c (c + len) →
      ∃ N' : ℕ → Submodule ℤ_[2] M, ∃ h' : B.IsJordanSplitting 2 N',
        (∀ i, i ∉ Finset.Icc c (c + len) → N' i = N i) ∧
        ∀ i ∈ Finset.Icc c (c + len), signBool h' i = s' i ∧ h'.constituentOddity hB i = t' i
  | 0, c, N, h, _, _, hT, hS => by
    refine ⟨N, h, fun _ _ ↦ rfl, fun i hi ↦ ?_⟩
    obtain rfl : i = c := by simp only [add_zero, Finset.mem_Icc] at hi; omega
    simp only [compS, compT, add_zero, Finset.Icc_self, Finset.sum_singleton,
      Nat.add_sub_cancel_left, odd_one, true_and] at hS hT
    have hs : signBool h i = s' i := (by decide : ∀ a b : Bool,
      (if a then (4 : ZMod (2 ^ 3)) else 0) = (if b then 4 else 0) → a = b) _ _ hS
    rw [hs] at hT; exact ⟨hs, add_right_cancel hT⟩
  | 1, c, N, h, hodd, hvalid', hT, hS => by
    have hodd0 := hodd c (by simp); have hodd1 := hodd (c + 1) (by simp)
    set u := pairState h hB c
    set v : PairState := ((s' c, t' c), (s' (c + 1), t' (c + 1)))
    have hinv : pairInv u = pairInv v := pairInv_eq_of_compT_compS hT hS
    set rc0 := rankClass (finrank ℤ_[2] (N c)); set rc1 := rankClass (finrank ℤ_[2] (N (c + 1)))
    have hp1 := pairValidPath_pairCanon rc0 rc1 u
      (isValidOdd_constituent_and_exists_mem h hB hodd0).1
      (isValidOdd_constituent_and_exists_mem h hB hodd1).1
    have hp2 := pairValidPath_reverse rc0 rc1 (hvalid' c (by simp)) (hvalid' (c + 1) (by simp))
      (hinv.symm ▸ pairValidPath_pairCanon rc0 rc1 v
        (hvalid' c (by simp)) (hvalid' (c + 1) (by simp)))
    obtain ⟨N', h', hagree, hu'⟩ := exists_isJordanSplitting_of_pairValidPath hB
      (_ ++ _) h hodd0 hodd1 (pairValidPath_append rc0 rc1 hp1 hp2)
    have hproj := state_of_pairState_eq h' hB hu'
    refine ⟨N', h', fun i hi ↦ hagree i (by simp only [Finset.mem_Icc] at hi; omega)
        (by simp only [Finset.mem_Icc] at hi; omega), fun i hi ↦ ?_⟩
    rw [Finset.Icc_self_add_one, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hproj.1
    · exact hproj.2
  | len + 2, c, N, h, hodd, hvalid', hT, hS => by
    set d := c + (len + 2)
    have h2nz : (2 : ℤ_[2]) ∈ nonZeroDivisors ℤ_[2] := mem_nonZeroDivisors_of_ne_zero two_ne_zero
    -- Step 1: match `stateJ` at index `c` using at most `2` moves on `(c, c + 1)`.
    obtain ⟨N1, h1, hagree1, hJ1, hT1, hS1⟩ :=
      exists_match_stateJ_at_left hB h (c := c) (d := d) (by omega)
        (hodd c (by simp [d])) (hodd (c + 1) (by simp [d])) (hvalid' c (by simp [d]))
    -- Step 2: if `(s c, t c) ≠ (s' c, t' c)`, flip `(c, c + 2)` by a distance-2 sign walk.
    have hpar1 (i) := h1.forall_two_mul_pow_dvd_iff_of_isJordanSplitting h h2nz dvd_rfl i
    obtain ⟨N2, h2, hagree2, hsc2, htc2, hT2, hS2⟩ :=
      exists_match_state_at_left_of_stateJ_eq hB h1 (c := c) (d := d) (by omega)
        (by rw [hpar1 c]; exact hodd c (by simp [d]))
        (by rw [hpar1 (c + 2)]; exact hodd (c + 2) (by simp [d])) hJ1
    -- Step 3: peel off index `c` and apply the induction hypothesis to `[c + 1, d]`.
    have hcd : c ≤ d := by omega
    have hd : d = (c + 1) + (len + 1) := by omega
    have hIcc_split : Finset.Icc c d = insert c (Finset.Icc (c + 1) ((c + 1) + (len + 1))) := by
      rw [← Finset.insert_Icc_succ_left_eq_Icc hcd, hd, Order.succ_eq_add_one]
    have hc_notMem : c ∉ Finset.Icc (c + 1) ((c + 1) + (len + 1)) := by
      simp only [Finset.mem_Icc]; omega
    obtain ⟨N3, h3, hagree3, hmatch3⟩ := exists_isJordanSplitting_matching_compartment hB s' t'
      (len + 1) (c + 1) N2 h2
      (fun i hi ↦ by
        rw [h2.forall_two_mul_pow_dvd_iff_of_isJordanSplitting h h2nz dvd_rfl i]
        exact hodd i (hIcc_split ▸ Finset.mem_insert_of_mem hi))
      (fun i hi ↦ by
        rw [h2.finrank_eq h two_ne_zero PadicInt.not_isUnit_two i]
        exact hvalid' i (hIcc_split ▸ Finset.mem_insert_of_mem hi))
      (by
        have hT2' := hT2.trans (hT1.trans hT)
        unfold compT at hT2' ⊢
        rw [hIcc_split, Finset.sum_insert hc_notMem, Finset.sum_insert hc_notMem, hsc2, htc2]
          at hT2'
        simpa only [hd] using add_left_cancel hT2')
      (by
        have hS2' := hS2.trans (hS1.trans hS)
        unfold compS at hS2' ⊢
        rw [hIcc_split, Finset.sum_insert hc_notMem, Finset.sum_insert hc_notMem, hsc2] at hS2'
        exact add_left_cancel hS2')
    refine ⟨N3, h3, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · have hi1 : i ≠ c ∧ i ≠ c + 1 := by simp only [Finset.mem_Icc] at hi; omega
      exact (hagree3 i fun hm ↦ hi (hIcc_split ▸ Finset.mem_insert_of_mem hm)).trans
        ((hagree2 i hi).trans (hagree1 i hi1.1 hi1.2))
    · rw [hIcc_split, Finset.mem_insert] at hi
      rcases hi with rfl | hi'
      · exact ⟨((constituentSign_eq_iff_signBool_eq h3 h2 i).mp
            (h2.constituentSign_eq_of_eq h3 (hagree3 i hc_notMem))).trans hsc2,
          (h2.constituentOddity_eq_of_eq h3 hB (hagree3 i hc_notMem)).trans htc2⟩
      · exact hmatch3 i hi'

/-- **Compartment normalization for dyadic Jordan splittings.** Let `B` and `B'` be symmetric
bilinear forms on finite free `ℤ_[2]`-modules with Jordan splittings `N` and `N'` with respect to
`2`. Suppose that on a closed interval `Finset.Icc c d`, every constituent of `N` and `N'` is of
type I, `N i` and `N' i` have equal rank, the compartment sign products agree, and the weighted
compartment oddity-sign sums agree modulo `8`. Then `B` admits a Jordan splitting `N''` agreeing
with `N` outside `Finset.Icc c d` whose constituent signs and oddities match those of `N'` on all
of `Finset.Icc c d`. -/
theorem IsJordanSplitting.exists_constituentSign_and_oddity_eq_on_Icc
    {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M']
    [Module.Finite ℤ_[2] M'] {B' : BilinForm ℤ_[2] M'} {N' : ℕ → Submodule ℤ_[2] M'}
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
    (hS : ∏ i ∈ Finset.Icc c d, h.constituentSign i =
      ∏ i ∈ Finset.Icc c d, h'.constituentSign i) :
    ∃ N'' : ℕ → Submodule ℤ_[2] M, ∃ h'' : B.IsJordanSplitting 2 N'',
      (∀ i, i ∉ Finset.Icc c d → N'' i = N i) ∧
      ∀ i ∈ Finset.Icc c d,
        h''.constituentSign i = h'.constituentSign i ∧
        h''.constituentOddity hB i = h'.constituentOddity hB' i := by
  by_cases hcd : c ≤ d
  · obtain ⟨len, rfl⟩ : ∃ len, d = c + len := ⟨d - c, by omega⟩
    have hvalid' : ∀ i ∈ Finset.Icc c (c + len),
        isValidOdd (rankClass (finrank ℤ_[2] (N i))) (signBool h' i)
          (h'.constituentOddity hB' i) = true := fun i hi ↦ by
      rw [hrank i hi]
      exact (isValidOdd_constituent_and_exists_mem h' hB' (hodd' i hi)).1
    have hT' : compT (signBool h) (h.constituentOddity hB) c (c + len) =
        compT (signBool h') (h'.constituentOddity hB') c (c + len) := by
      simpa only [compT, signBool, decide_eq_true_eq] using hT
    have hS' : compS (signBool h) c (c + len) = compS (signBool h') c (c + len) := by
      simp only [compS, signBool, decide_eq_true_eq,
        h.sum_if_constituentSign_eq_neg_one, h'.sum_if_constituentSign_eq_neg_one, hS]
    obtain ⟨N'', h'', hagree, hmatch⟩ := exists_isJordanSplitting_matching_compartment hB
      (signBool h') (h'.constituentOddity hB') len c N h hodd hvalid' hT' hS'
    exact ⟨N'', h'', hagree, fun i hi ↦
      ⟨(constituentSign_eq_iff_signBool_eq h'' h' i).mpr (hmatch i hi).1, (hmatch i hi).2⟩⟩
  · exact ⟨N, h, fun _ _ ↦ rfl, fun i hi ↦ by simp only [Finset.mem_Icc] at hi; omega⟩

end CompartmentMoves

end LinearMap.BilinForm
