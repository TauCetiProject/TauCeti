/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Interval.Set.Defs

import Mathlib.Data.Sym.Sym2
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Serre's weight table on classified local data

Let `ρ : G_p → GL₂(F)` be a continuous representation of the absolute Galois group of `ℚ_p` over
an algebraic closure `F` of `𝔽_p`, let `χ` be the mod `p` cyclotomic character and
let `ψ, ψ' = ψ ^ p` be the fundamental characters of niveau two of tame inertia, so that
`ψ ^ (p + 1) = χ` on inertia. Serre attaches to `ρ` a weight `k(ρ)` which depends only on the
restriction of `ρ` to inertia `I_p`, through one of three kinds of normalised data:

* *tame, niveau one*: wild inertia acts trivially and `I_p` acts through `χ ^ a ⊕ χ ^ b` with
  `0 ≤ a ≤ b ≤ p - 2`;
* *tame, niveau two*: wild inertia acts trivially and `I_p` acts through the conjugate pair
  `ψ ^ (a + p * b) ⊕ ψ' ^ (a + p * b)` with `0 ≤ a < b ≤ p - 1`;
* *wild*: wild inertia acts nontrivially, so the line `D` it fixes is stable, and `I_p` acts on
  the quotient by `χ ^ α` and on `D` by `χ ^ β`, with `0 ≤ α ≤ p - 2` and `1 ≤ β ≤ p - 1`. When
  `β = α + 1` the extension is either *peu ramifiée* or *très ramifiée*; for other exponents the
  distinction is not defined.

`TauCeti.SerreWeightData p` records exactly these data, including the order of the wild exponents
and the très ramifiée flag, which may be set only when `β = α + 1`. On it this file defines

* `SerreWeightData.weight`: Serre's weight, `1 + p * a + b` on tame data except that
  unramified data have weight `p`, `1 + p * min α β + max α β` on wild data except that très
  ramifiée data have weight `(α + 1) * (p + 1)`, or `4` when `p = 2`;
* `SerreWeightData.edixhovenWeight`: Edixhoven's variant, `1 + p * a + b` on all tame data and
  `1 + p * min α β + max α β`, plus `p - 1` when très ramifiée, on wild data;
* `SerreWeightData.detExponent`: the exponent `e` with `det ρ = χ ^ e` on inertia;
* `SerreWeightData.twist`: the renormalised data of the cyclotomic twist `ρ ⊗ χ`.

Its main results are the determinant congruence `k ≡ e + 1 [MOD p - 1]`
(`SerreWeightData.weight_modEq_detExponent`), the bound `2 ≤ k`, Serre's twist formula in niveau
two, the excess `p - 1` of the très ramifiée weight over the peu ramifiée one for `p ≠ 2`, the
dyadic dichotomy `k ∈ {2, 4}`, the comparison of the two weights, the effect `e ↦ e + 2` of a
twist on the determinant exponent, the period `p - 1` of twisting
(`SerreWeightData.twist_iterate_sub_one`), and the fact that for `p > 2` some cyclotomic twist has
weight in `[2, p + 1]` (`SerreWeightData.exists_weight_twist_iterate_mem_Icc`).

Producing these data from an actual local Galois representation, which needs the fundamental
characters of tame inertia and the Kummer-theoretic peu/très ramifiée test, is not done here.

## References

* J.-P. Serre, *Sur les représentations modulaires de degré 2 de Gal(ℚ^alg/ℚ)*, Duke Math. J. 54
  (1987), §§2.2–2.4 and 2.8.
* B. Edixhoven, *The weight in Serre's conjectures on modular forms*, Invent. Math. 109 (1992),
  Definition 4.3 and Remark 4.4.
* C. Khare and J.-P. Wintenberger, *Serre's modularity conjecture (I)*, Invent. Math. 178 (2009),
  §1, for the twist into weights `2 ≤ k ≤ p + 1`.
-/

public section

namespace TauCeti

/-- Serre's normalised inertial data at a prime `p` of a two-dimensional mod `p` representation
of the absolute Galois group of `ℚ_p`: tame data of niveau one or two, or ordered wild exponents
together with the très ramifiée flag, which is only allowed for adjacent exponents `β = α + 1`. -/
inductive SerreWeightData (p : ℕ) : Type
  /-- Tame data of niveau one: inertia acts through `χ ^ a ⊕ χ ^ b`, `0 ≤ a ≤ b ≤ p - 2`. -/
  | niveauOne (a b : ℕ) (hab : a ≤ b) (hb : b ≤ p - 2)
  /-- Tame data of niveau two: inertia acts through `ψ ^ (a + p * b) ⊕ ψ' ^ (a + p * b)`, for the
  fundamental characters `ψ, ψ'` of niveau two and `0 ≤ a < b ≤ p - 1`. -/
  | niveauTwo (a b : ℕ) (hab : a < b) (hb : b ≤ p - 1)
  /-- Wild data: inertia acts by `χ ^ α` on the quotient by the line fixed by wild inertia and
  by `χ ^ β` on that line; `tres` records that the extension is très ramifiée. -/
  | wild (α β : ℕ) (hα : α ≤ p - 2) (hβ : 1 ≤ β) (hβp : β ≤ p - 1) (tres : Bool)
      (htres : tres = true → β = α + 1)
  deriving DecidableEq

namespace SerreWeightData

variable {p : ℕ}

/-! ### The data and their projections -/

/-- The data of an unramified representation: niveau one with exponents `(0, 0)`. -/
def unramified (p : ℕ) : SerreWeightData p :=
  niveauOne 0 0 le_rfl (Nat.zero_le _)

lemma unramified_def : unramified p = niveauOne 0 0 le_rfl (Nat.zero_le _) := (rfl)

@[simp]
lemma niveauOne_eq_unramified_iff {a b : ℕ} {hab : a ≤ b} {hb : b ≤ p - 2} :
    niveauOne a b hab hb = unramified p ↔ b = 0 := by
  simp only [unramified, niveauOne.injEq]
  omega

@[simp]
lemma niveauTwo_ne_unramified {a b : ℕ} {hab : a < b} {hb : b ≤ p - 1} :
    niveauTwo a b hab hb ≠ unramified p := by
  simp [unramified_def]

@[simp]
lemma wild_ne_unramified {α β : ℕ} {hα : α ≤ p - 2} {hβ : 1 ≤ β} {hβp : β ≤ p - 1} {tres : Bool}
    {htres : tres = true → β = α + 1} : wild α β hα hβ hβp tres htres ≠ unramified p := by
  simp [unramified_def]

/-- Wild data are *très ramifiée* when their flag is set; tame data never are. -/
def IsTresRamifiee : SerreWeightData p → Prop
  | wild _ _ _ _ _ tres _ => tres = true
  | _ => False

@[simp]
lemma isTresRamifiee_wild {α β : ℕ} {hα : α ≤ p - 2} {hβ : 1 ≤ β} {hβp : β ≤ p - 1} {tres : Bool}
    {htres : tres = true → β = α + 1} :
    (wild α β hα hβ hβp tres htres).IsTresRamifiee ↔ tres = true := (Iff.rfl)

@[simp]
lemma not_isTresRamifiee_niveauOne {a b : ℕ} {hab : a ≤ b} {hb : b ≤ p - 2} :
    ¬ (niveauOne a b hab hb).IsTresRamifiee := not_false

@[simp]
lemma not_isTresRamifiee_niveauTwo {a b : ℕ} {hab : a < b} {hb : b ≤ p - 1} :
    ¬ (niveauTwo a b hab hb).IsTresRamifiee := not_false

instance : DecidablePred (IsTresRamifiee (p := p))
  | niveauOne .. => isFalse not_isTresRamifiee_niveauOne
  | niveauTwo .. => isFalse not_isTresRamifiee_niveauTwo
  | wild _ _ _ _ _ tres _ => decidable_of_iff (tres = true) isTresRamifiee_wild.symm

/-- The tame exponents `(a, b)` of tame data of either niveau; `none` on wild data. -/
def tameExponents : SerreWeightData p → Option (ℕ × ℕ)
  | niveauOne a b _ _ => some (a, b)
  | niveauTwo a b _ _ => some (a, b)
  | wild .. => none

/-- The ordered wild exponents `(α, β)` of wild data, `α` on the quotient and `β` on the line
fixed by wild inertia; `none` on tame data. -/
def wildExponents : SerreWeightData p → Option (ℕ × ℕ)
  | wild α β .. => some (α, β)
  | _ => none

@[simp]
lemma tameExponents_niveauOne {a b : ℕ} {hab : a ≤ b} {hb : b ≤ p - 2} :
    (niveauOne a b hab hb).tameExponents = some (a, b) := (rfl)

@[simp]
lemma tameExponents_niveauTwo {a b : ℕ} {hab : a < b} {hb : b ≤ p - 1} :
    (niveauTwo a b hab hb).tameExponents = some (a, b) := (rfl)

@[simp]
lemma tameExponents_wild {α β : ℕ} {hα : α ≤ p - 2} {hβ : 1 ≤ β} {hβp : β ≤ p - 1} {tres : Bool}
    {htres : tres = true → β = α + 1} : (wild α β hα hβ hβp tres htres).tameExponents = none :=
  (rfl)

@[simp]
lemma wildExponents_niveauOne {a b : ℕ} {hab : a ≤ b} {hb : b ≤ p - 2} :
    (niveauOne a b hab hb).wildExponents = none := (rfl)

@[simp]
lemma wildExponents_niveauTwo {a b : ℕ} {hab : a < b} {hb : b ≤ p - 1} :
    (niveauTwo a b hab hb).wildExponents = none := (rfl)

@[simp]
lemma wildExponents_wild {α β : ℕ} {hα : α ≤ p - 2} {hβ : 1 ≤ β} {hβp : β ≤ p - 1} {tres : Bool}
    {htres : tres = true → β = α + 1} :
    (wild α β hα hβ hβp tres htres).wildExponents = some (α, β) := (rfl)

@[simp]
lemma tameExponents_unramified : (unramified p).tameExponents = some (0, 0) := (rfl)

@[simp]
lemma wildExponents_unramified : (unramified p).wildExponents = none := (rfl)

/-- Exactly one of the two projections is defined. -/
lemma tameExponents_eq_none_iff (d : SerreWeightData p) :
    d.tameExponents = none ↔ d.wildExponents ≠ none := by
  cases d <;> simp

/-- The exponent `e` with `det ρ = χ ^ e` on inertia: `a + b` on tame data (in niveau two because
`ψ ^ (p + 1) = χ`) and `α + β` on wild data. -/
def detExponent : SerreWeightData p → ℕ
  | niveauOne a b _ _ => a + b
  | niveauTwo a b _ _ => a + b
  | wild α β .. => α + β

@[simp]
lemma detExponent_niveauOne {a b : ℕ} {hab : a ≤ b} {hb : b ≤ p - 2} :
    (niveauOne a b hab hb).detExponent = a + b := (rfl)

@[simp]
lemma detExponent_niveauTwo {a b : ℕ} {hab : a < b} {hb : b ≤ p - 1} :
    (niveauTwo a b hab hb).detExponent = a + b := (rfl)

@[simp]
lemma detExponent_wild {α β : ℕ} {hα : α ≤ p - 2} {hβ : 1 ≤ β} {hβp : β ≤ p - 1} {tres : Bool}
    {htres : tres = true → β = α + 1} : (wild α β hα hβ hβp tres htres).detExponent = α + β :=
  (rfl)

/-! ### Serre's weight and Edixhoven's weight -/

/-- Serre's weight `k(ρ)` of the data, following Serre (1987), §§2.2–2.4: `1 + p * a + b` on tame
data, except `p` on unramified data; `1 + p * min α β + max α β` on wild data, except
`(α + 1) * (p + 1)` on très ramifiée data, and `4` on très ramifiée data when `p = 2`. -/
def weight : SerreWeightData p → ℕ
  | niveauOne a b _ _ => if b = 0 then p else 1 + p * a + b
  | niveauTwo a b _ _ => 1 + p * a + b
  | wild α β _ _ _ tres _ =>
      if tres then (if p = 2 then 4 else (α + 1) * (p + 1)) else 1 + p * min α β + max α β

@[simp]
lemma weight_niveauOne {a b : ℕ} {hab : a ≤ b} {hb : b ≤ p - 2} :
    (niveauOne a b hab hb).weight = if b = 0 then p else 1 + p * a + b := (rfl)

@[simp]
lemma weight_niveauTwo {a b : ℕ} {hab : a < b} {hb : b ≤ p - 1} :
    (niveauTwo a b hab hb).weight = 1 + p * a + b := (rfl)

@[simp]
lemma weight_wild {α β : ℕ} {hα : α ≤ p - 2} {hβ : 1 ≤ β} {hβp : β ≤ p - 1} {tres : Bool}
    {htres : tres = true → β = α + 1} :
    (wild α β hα hβ hβp tres htres).weight =
      if tres then (if p = 2 then 4 else (α + 1) * (p + 1)) else 1 + p * min α β + max α β :=
  (rfl)

/-- Unramified data have Serre weight `p`. -/
@[simp]
lemma weight_unramified : (unramified p).weight = p := (rfl)

/-- Edixhoven's weight of the data (Edixhoven 1992, Definition 4.3): `1 + p * a + b` on all tame
data and `1 + p * min α β + max α β`, increased by `p - 1` when très ramifiée, on wild data. -/
def edixhovenWeight : SerreWeightData p → ℕ
  | niveauOne a b _ _ => 1 + p * a + b
  | niveauTwo a b _ _ => 1 + p * a + b
  | wild α β _ _ _ tres _ => 1 + p * min α β + max α β + if tres then p - 1 else 0

@[simp]
lemma edixhovenWeight_niveauOne {a b : ℕ} {hab : a ≤ b} {hb : b ≤ p - 2} :
    (niveauOne a b hab hb).edixhovenWeight = 1 + p * a + b := (rfl)

@[simp]
lemma edixhovenWeight_niveauTwo {a b : ℕ} {hab : a < b} {hb : b ≤ p - 1} :
    (niveauTwo a b hab hb).edixhovenWeight = 1 + p * a + b := (rfl)

@[simp]
lemma edixhovenWeight_wild {α β : ℕ} {hα : α ≤ p - 2} {hβ : 1 ≤ β} {hβp : β ≤ p - 1}
    {tres : Bool} {htres : tres = true → β = α + 1} :
    (wild α β hα hβ hβp tres htres).edixhovenWeight =
      1 + p * min α β + max α β + if tres then p - 1 else 0 := (rfl)

/-- Unramified data have Edixhoven weight `1`. -/
@[simp]
lemma edixhovenWeight_unramified : (unramified p).edixhovenWeight = 1 := by
  simp [unramified_def]

/-! ### Properties of the weight -/

private lemma one_add_mul_add_modEq (q a b : ℕ) : 1 + (q + 1) * a + b ≡ a + b + 1 [MOD q] := by
  rw [show 1 + (q + 1) * a + b = a + b + 1 + q * a by ring]
  exact Nat.add_modulus_mul_modEq_iff.2 rfl

/-- The très ramifiée weight `(α + 1) * (p + 1)` at `p = q + 1` is the peu ramifiée weight
`1 + p * α + (α + 1)` plus `p - 1 = q`. -/
private lemma add_one_mul_eq (q α : ℕ) :
    (α + 1) * (q + 1 + 1) = 1 + (q + 1) * α + (α + 1) + q := by
  ring

/-- At adjacent wild exponents and `p ≠ 2`, the très ramifiée weight exceeds the peu ramifiée
weight by `p - 1`. -/
theorem weight_wild_true_eq_add {α β : ℕ} (hp : p ≠ 2) {hα : α ≤ p - 2} {hβ : 1 ≤ β}
    {hβp : β ≤ p - 1} (h : β = α + 1) :
    (wild α β hα hβ hβp true fun _ => h).weight =
      (wild α β hα hβ hβp false fun h' => absurd h' Bool.false_ne_true).weight + (p - 1) := by
  subst h
  simp only [weight_wild, ↓reduceIte, hp, Bool.false_eq_true,
    min_eq_left (Nat.le_add_right α 1), max_eq_right (Nat.le_add_right α 1)]
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ p by omega)
  rw [Nat.add_sub_cancel_left, add_comm 1 q, add_one_mul_eq]

/-- Serre's weight and Edixhoven's weight agree away from unramified data and dyadic très
ramifiée data. -/
theorem edixhovenWeight_eq_weight {d : SerreWeightData p} (hd : d ≠ unramified p)
    (hd₂ : p = 2 → ¬ d.IsTresRamifiee) : d.edixhovenWeight = d.weight := by
  cases d with
  | niveauOne a b hab hb => simp_all
  | niveauTwo a b hab hb => simp
  | wild α β hα hβ hβp tres htres =>
    cases tres
    · simp
    · rw [weight_wild_true_eq_add (fun h => hd₂ h rfl) (htres rfl)]
      simp

/-- Dyadic très ramifiée data have Edixhoven weight `3`, against Serre weight `4`. -/
theorem edixhovenWeight_eq_three {d : SerreWeightData 2} (hd : d.IsTresRamifiee) :
    d.edixhovenWeight = 3 := by
  cases d with
  | niveauOne => exact hd.elim
  | niveauTwo => exact hd.elim
  | wild α β hα hβ hβp tres htres =>
    simp only [isTresRamifiee_wild] at hd
    subst hd
    simp only [edixhovenWeight_wild, ↓reduceIte]
    omega

/-- The determinant congruence: `det ρ = χ ^ (k - 1)` on inertia, that is, the Serre weight is
congruent to `e + 1` modulo `p - 1`, where `χ ^ e` is the determinant on inertia. -/
theorem weight_modEq_detExponent (hp : p ≠ 0) (d : SerreWeightData p) :
    d.weight ≡ d.detExponent + 1 [MOD p - 1] := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  cases d with
  | niveauOne a b hab hb =>
    simp only [weight_niveauOne, detExponent_niveauOne]
    split_ifs with hb0
    · obtain rfl : a = 0 := by omega
      subst hb0
      exact Nat.add_modEq_left
    · exact one_add_mul_add_modEq q a b
  | niveauTwo a b hab hb => exact one_add_mul_add_modEq q a b
  | wild α β hα hβ hβp tres htres =>
    simp only [weight_wild, detExponent_wild]
    split_ifs with ht hq
    · obtain rfl : q = 1 := by omega
      exact Nat.modEq_one
    · obtain rfl := htres ht
      rw [add_one_mul_eq]
      exact Nat.add_modEq_right.trans (one_add_mul_add_modEq q α (α + 1))
    · rw [← min_add_max α β]
      exact one_add_mul_add_modEq q _ _

/-- The same determinant congruence holds for Edixhoven's weight. -/
theorem edixhovenWeight_modEq_detExponent (d : SerreWeightData p) :
    d.edixhovenWeight ≡ d.detExponent + 1 [MOD p - 1] := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · cases d with
    | niveauOne a b hab hb =>
      obtain rfl : b = 0 := by omega
      obtain rfl : a = 0 := by omega
      rfl
    | niveauTwo a b hab hb => omega
    | wild α β hα hβ hβp tres htres => omega
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  cases d with
  | niveauOne a b hab hb => exact one_add_mul_add_modEq q a b
  | niveauTwo a b hab hb => exact one_add_mul_add_modEq q a b
  | wild α β hα hβ hβp tres htres =>
    simp only [edixhovenWeight_wild, detExponent_wild, Nat.add_sub_cancel]
    rw [← min_add_max α β]
    split_ifs
    · exact Nat.add_modEq_right.trans (one_add_mul_add_modEq q _ _)
    · exact one_add_mul_add_modEq q _ _

/-- Every normalised datum has Serre weight at least `2`. -/
theorem two_le_weight (hp : 2 ≤ p) (d : SerreWeightData p) : 2 ≤ d.weight := by
  cases d with
  | niveauOne a b hab hb =>
    simp only [weight_niveauOne]
    split_ifs <;> omega
  | niveauTwo a b hab hb =>
    simp only [weight_niveauTwo]
    omega
  | wild α β hα hβ hβp tres htres =>
    simp only [weight_wild]
    split_ifs
    · omega
    · nlinarith
    · omega

/-- Serre's twist formula (2.2.5) in niveau two: `k(χ ^ a ⊗ ρ') = k(ρ') + a * (p + 1)`, where `ρ'`
has the niveau-two data `(0, b - a)`. -/
theorem weight_niveauTwo_eq_add {a b : ℕ} (hab : a < b) (hb : b ≤ p - 1) :
    (niveauTwo a b hab hb).weight =
      (niveauTwo 0 (b - a) (Nat.sub_pos_of_lt hab) (by omega) : SerreWeightData p).weight +
        a * (p + 1) := by
  simp only [weight_niveauTwo]
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hab
  rw [show a + c + 1 - a = c + 1 by omega]
  ring

/-- Exchanging non-adjacent wild exponents does not change the weight. -/
theorem weight_wild_comm {α β : ℕ} (hβα : β ≠ α + 1) (hαβ : α ≠ β + 1) {hα : α ≤ p - 2}
    {hβ : 1 ≤ β} {hβp : β ≤ p - 1} {tres : Bool} {htres : tres = true → β = α + 1}
    {hα' : β ≤ p - 2} {hβ' : 1 ≤ α} {hβp' : α ≤ p - 1} {tres' : Bool}
    {htres' : tres' = true → α = β + 1} :
    (wild α β hα hβ hβp tres htres).weight = (wild β α hα' hβ' hβp' tres' htres').weight := by
  have ht : tres = false := by cases tres <;> simp_all
  have ht' : tres' = false := by cases tres' <;> simp_all
  subst ht ht'
  simp [min_comm, max_comm]

/-- At `p = 2` the Serre weight is `2` or `4`. -/
theorem weight_eq_two_or_four (d : SerreWeightData 2) : d.weight = 2 ∨ d.weight = 4 := by
  cases d with
  | niveauOne a b hab hb =>
    simp only [weight_niveauOne]
    split_ifs <;> omega
  | niveauTwo a b hab hb =>
    simp only [weight_niveauTwo]
    omega
  | wild α β hα hβ hβp tres htres =>
    simp only [weight_wild]
    split_ifs <;> omega

/-- At `p = 2` the Serre weight is `4` exactly on très ramifiée data. -/
theorem weight_eq_four_iff (d : SerreWeightData 2) : d.weight = 4 ↔ d.IsTresRamifiee := by
  cases d with
  | niveauOne a b hab hb =>
    simp only [weight_niveauOne, not_isTresRamifiee_niveauOne, iff_false]
    split_ifs <;> omega
  | niveauTwo a b hab hb =>
    simp only [weight_niveauTwo, not_isTresRamifiee_niveauTwo, iff_false]
    omega
  | wild α β hα hβ hβp tres htres =>
    cases tres
    · simp only [weight_wild, isTresRamifiee_wild, Bool.false_eq_true, ↓reduceIte, iff_false]
      omega
    · simp

/-! ### Cyclotomic twists -/

/-- The renormalised data of the cyclotomic twist `ρ ⊗ χ`. On niveau one the exponents
`(a, b)` become `(a + 1, b + 1)`, read modulo `p - 1` and reordered. On niveau two the character
`ψ ^ (a + p * b)` is multiplied by `χ = ψ ^ (p + 1)`, and the exponents are renormalised using
`ψ ^ (p ^ 2 - 1) = 1` and the conjugation `ψ ↦ ψ ^ p`. On wild data both exponents increase by `1`
modulo `p - 1`, keeping `α ≤ p - 2` and `1 ≤ β ≤ p - 1`, and the extension type is unchanged. -/
def twist : SerreWeightData p → SerreWeightData p
  | niveauOne a b _ _ =>
      if h : b + 1 ≤ p - 2 then niveauOne (a + 1) (b + 1) (by omega) h
      else if h' : a + 1 ≤ p - 2 then niveauOne 0 (a + 1) (Nat.zero_le _) h'
      else unramified p
  | niveauTwo a b hab hb =>
      if h : b + 1 ≤ p - 1 then niveauTwo (a + 1) (b + 1) (by omega) h
      else if h' : a + 2 ≤ p - 1 then niveauTwo 0 (a + 2) (by omega) h'
      else niveauTwo 0 1 Nat.one_pos (by omega)
  | wild α β hα hβ hβp tres htres =>
      wild (if α + 1 ≤ p - 2 then α + 1 else 0) (if β + 1 ≤ p - 1 then β + 1 else 1)
        (by split_ifs <;> omega) (by split_ifs <;> omega) (by split_ifs <;> omega) tres
        (fun h => by have := htres h; split_ifs <;> omega)

lemma twist_niveauOne {a b : ℕ} {hab : a ≤ b} {hb : b ≤ p - 2} :
    (niveauOne a b hab hb).twist =
      if h : b + 1 ≤ p - 2 then niveauOne (a + 1) (b + 1) (by omega) h
      else if h' : a + 1 ≤ p - 2 then niveauOne 0 (a + 1) (Nat.zero_le _) h'
      else unramified p := (rfl)

lemma twist_niveauTwo {a b : ℕ} {hab : a < b} {hb : b ≤ p - 1} :
    (niveauTwo a b hab hb).twist =
      if h : b + 1 ≤ p - 1 then niveauTwo (a + 1) (b + 1) (by omega) h
      else if h' : a + 2 ≤ p - 1 then niveauTwo 0 (a + 2) (by omega) h'
      else niveauTwo 0 1 Nat.one_pos (by omega) := (rfl)

lemma twist_wild {α β : ℕ} {hα : α ≤ p - 2} {hβ : 1 ≤ β} {hβp : β ≤ p - 1} {tres : Bool}
    {htres : tres = true → β = α + 1} :
    (wild α β hα hβ hβp tres htres).twist =
      wild (if α + 1 ≤ p - 2 then α + 1 else 0) (if β + 1 ≤ p - 1 then β + 1 else 1)
        (by split_ifs <;> omega) (by split_ifs <;> omega) (by split_ifs <;> omega) tres
        (fun h => by have := htres h; split_ifs <;> omega) := (rfl)

/-- Twisting preserves the extension type. -/
@[simp]
lemma isTresRamifiee_twist (d : SerreWeightData p) :
    d.twist.IsTresRamifiee ↔ d.IsTresRamifiee := by
  cases d with
  | niveauOne a b hab hb =>
    simp only [twist_niveauOne, unramified_def]
    split_ifs <;> simp
  | niveauTwo a b hab hb =>
    simp only [twist_niveauTwo]
    split_ifs <;> simp
  | wild => simp [twist_wild]

/-- Twisting by `χ` multiplies the determinant by `χ ^ 2`. -/
theorem detExponent_twist (hp : 2 ≤ p) (d : SerreWeightData p) :
    d.twist.detExponent ≡ d.detExponent + 2 [MOD p - 1] := by
  cases d with
  | niveauOne a b hab hb =>
    simp only [twist_niveauOne, unramified_def]
    split_ifs <;> simp only [detExponent_niveauOne]
    · exact (Nat.modEq_iff_dvd' (by omega)).2 ⟨0, by omega⟩
    · exact (Nat.modEq_iff_dvd' (by omega)).2 ⟨1, by omega⟩
    · exact (Nat.modEq_iff_dvd' (by omega)).2 ⟨2, by omega⟩
  | niveauTwo a b hab hb =>
    simp only [twist_niveauTwo]
    split_ifs <;> simp only [detExponent_niveauTwo]
    · exact (Nat.modEq_iff_dvd' (by omega)).2 ⟨0, by omega⟩
    · exact (Nat.modEq_iff_dvd' (by omega)).2 ⟨1, by omega⟩
    · exact (Nat.modEq_iff_dvd' (by omega)).2 ⟨2, by omega⟩
  | wild α β hα hβ hβp tres htres =>
    simp only [twist_wild, detExponent_wild]
    split_ifs
    · exact (Nat.modEq_iff_dvd' (by omega)).2 ⟨0, by omega⟩
    · exact (Nat.modEq_iff_dvd' (by omega)).2 ⟨1, by omega⟩
    · exact (Nat.modEq_iff_dvd' (by omega)).2 ⟨1, by omega⟩
    · exact (Nat.modEq_iff_dvd' (by omega)).2 ⟨2, by omega⟩

/-- At `p = 2` the mod `2` cyclotomic character is trivial, so twisting changes nothing. -/
@[simp]
theorem twist_eq_self_of_two (d : SerreWeightData 2) : d.twist = d := by
  cases d with
  | niveauOne a b hab hb =>
    have hb0 : b = 0 := by omega
    have ha0 : a = 0 := by omega
    subst hb0 ha0
    rfl
  | niveauTwo a b hab hb =>
    have hb1 : b = 1 := by omega
    have ha0 : a = 0 := by omega
    subst hb1 ha0
    rfl
  | wild α β hα hβ hβp tres htres =>
    have hα0 : α = 0 := by omega
    have hβ1 : β = 1 := by omega
    subst hα0 hβ1
    rfl

/-- The exponents of the inertial characters: the unordered pair of powers of `χ` on niveau one,
the conjugate pair of powers of `ψ` on niveau two, and on wild data the powers `α` and `β - 1` of
`χ` together with the flag. -/
private abbrev CharExponents (p : ℕ) : Type :=
  Sym2 (ZMod (p - 1)) ⊕ Sym2 (ZMod (p ^ 2 - 1)) ⊕ ZMod (p - 1) × ZMod (p - 1) × Bool

private def charExponents : SerreWeightData p → CharExponents p
  | niveauOne a b _ _ => .inl s(a, b)
  | niveauTwo a b _ _ => .inr (.inl s((a + p * b : ℕ), (b + p * a : ℕ)))
  | wild α β _ _ _ tres _ => .inr (.inr (α, (β - 1 : ℕ), tres))

/-- The effect of `n` twists by `χ = ψ ^ (p + 1)` on the exponents. -/
private def twistCharExponents (p n : ℕ) : CharExponents p → CharExponents p :=
  Sum.map (Sym2.map (· + n)) (Sum.map (Sym2.map (· + n * (p + 1)))
    (Prod.map (· + n) (Prod.map (· + n) id)))

private lemma natCast_injective_of_lt {n a b : ℕ} (ha : a < n) (hb : b < n)
    (h : (a : ZMod n) = b) : a = b := by
  rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h

/-- The base `p` expansion `x + p * y` of a niveau-two exponent stays below `p ^ 2 - 1`. -/
private lemma add_mul_lt (hp : 2 ≤ p) {x y : ℕ} (hx : x ≤ p - 1) (hy : y ≤ p - 1)
    (hxy : x + y < 2 * (p - 1)) : x + p * y < p ^ 2 - 1 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  have hsq : (q + 2) ^ 2 = (q + 2) * q + 2 * q + 4 := by ring
  rcases (show y = q + 1 ∨ y ≤ q by omega) with rfl | hy'
  · have : (q + 2) * (q + 1) = (q + 2) * q + (q + 2) := by ring
    omega
  · have := Nat.mul_le_mul_left (q + 2) hy'
    omega

private lemma charExponents_injective (hp : 2 ≤ p) :
    Function.Injective (charExponents (p := p)) := by
  intro d d' h
  cases d <;> cases d' <;> simp only [charExponents, Sum.inl.injEq, Sum.inr.injEq,
    reduceCtorEq, Prod.mk.injEq, Sym2.eq_iff, niveauOne.injEq, niveauTwo.injEq, wild.injEq] at h ⊢
  · rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
      have h₁ := natCast_injective_of_lt (by omega) (by omega) h₁ <;>
      have h₂ := natCast_injective_of_lt (by omega) (by omega) h₂ <;> omega
  · rename_i a b hab hb a' b' hab' hb'
    have hp0 : 0 < p := by omega
    have digits {x y x' y' : ℕ} (hx : x < p) (hx' : x' < p) (h : x + p * y = x' + p * y') :
        x = x' ∧ y = y' := by
      have h₁ := (Nat.div_mod_unique (a := x + p * y) hp0).2 ⟨rfl, hx⟩
      have h₂ := (Nat.div_mod_unique (a := x + p * y) hp0).2 ⟨h.symm, hx'⟩
      omega
    rcases h with ⟨h₁, -⟩ | ⟨h₁, -⟩ <;>
      have h₁ := digits (by omega) (by omega) <|
        natCast_injective_of_lt (add_mul_lt hp (by omega) (by omega) (by omega))
          (add_mul_lt hp (by omega) (by omega) (by omega)) h₁ <;> omega
  · obtain ⟨h₁, h₂, h₃⟩ := h
    have h₁ := natCast_injective_of_lt (by omega) (by omega) h₁
    have h₂ := natCast_injective_of_lt (by omega) (by omega) h₂
    exact ⟨h₁, by omega, h₃⟩

private lemma charExponents_twist (hp : 2 ≤ p) (d : SerreWeightData p) :
    charExponents d.twist = twistCharExponents p 1 (charExponents d) := by
  have key (n : ℕ) (h : n + 1 = p - 1) : (n : ZMod (p - 1)) + 1 = 0 := by
    rw [← Nat.cast_add_one, h, ZMod.natCast_self]
  cases d with
  | niveauOne a b hab hb =>
    simp only [twist_niveauOne, unramified_def]
    split_ifs
    · simp [charExponents, twistCharExponents]
    · simp [charExponents, twistCharExponents, key b (by omega), Sym2.eq_swap]
    · simp [charExponents, twistCharExponents, key a (by omega), key b (by omega)]
  | niveauTwo a b hab hb =>
    have hsq : ((p : ZMod (p ^ 2 - 1))) ^ 2 = 1 := by
      have := ZMod.natCast_self (p ^ 2 - 1)
      rwa [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one,
        sub_eq_zero] at this
    simp only [twist_niveauTwo]
    split_ifs
    · simp only [charExponents, twistCharExponents, Sum.map_inr, Sum.map_inl, Sym2.map_mk]
      push_cast
      exact congrArg (Sum.inr ∘ Sum.inl) (Sym2.eq_iff.2 (.inl ⟨by ring, by ring⟩))
    · obtain rfl : p = b + 1 := by omega
      simp only [charExponents, twistCharExponents, Sum.map_inr, Sum.map_inl, Sym2.map_mk]
      push_cast at hsq ⊢
      exact congrArg (Sum.inr ∘ Sum.inl)
        (Sym2.eq_iff.2 (.inr ⟨by ring, by linear_combination -hsq⟩))
    · obtain rfl : b = a + 1 := by omega
      obtain rfl : p = a + 2 := by omega
      simp only [charExponents, twistCharExponents, Sum.map_inr, Sum.map_inl, Sym2.map_mk]
      push_cast at hsq ⊢
      exact congrArg (Sum.inr ∘ Sum.inl)
        (Sym2.eq_iff.2 (.inl ⟨by linear_combination -hsq, by linear_combination -hsq⟩))
  | wild α β hα hβ hβp tres htres =>
    obtain ⟨c, rfl⟩ : ∃ c, β = c + 1 := ⟨β - 1, by omega⟩
    simp only [twist_wild]
    split_ifs
    · simp [charExponents, twistCharExponents]
    · simp [charExponents, twistCharExponents, key c (by omega)]
    · simp [charExponents, twistCharExponents, key α (by omega)]
    · simp [charExponents, twistCharExponents, key α (by omega), key c (by omega)]

private lemma twistCharExponents_iterate (p n : ℕ) :
    (twistCharExponents p 1)^[n] = twistCharExponents p n := by
  induction n with
  | zero => ext x; rcases x with x | x | ⟨x, y, t⟩ <;> simp [twistCharExponents]
  | succ n ih =>
    ext x
    rw [Function.iterate_succ_apply', ih]
    rcases x with x | x | ⟨x, y, t⟩ <;>
      simp [twistCharExponents, Sym2.map_map, add_assoc, add_mul]

private lemma twistCharExponents_sub_one (p : ℕ) (x : CharExponents p) :
    twistCharExponents p (p - 1) x = x := by
  have h₂ : ((p - 1 : ℕ) : ZMod (p ^ 2 - 1)) * (p + 1) = 0 := by
    have : (p - 1) * (p + 1) = p ^ 2 - 1 := by
      rcases p with _ | q
      · rfl
      · rw [Nat.add_sub_cancel]
        have : (q + 1) ^ 2 = q * (q + 1 + 1) + 1 := by ring
        omega
    rw [← ZMod.natCast_self (p ^ 2 - 1), ← this]
    push_cast
    rfl
  rcases x with x | x | ⟨x, y, t⟩ <;> simp [twistCharExponents, h₂]

/-- Twisting `p - 1` times by `χ` returns the original data, as `χ ^ (p - 1) = 1`. -/
theorem twist_iterate_sub_one (d : SerreWeightData p) : twist^[p - 1] d = d := by
  rcases lt_or_ge p 2 with hp | hp
  · rw [show p - 1 = 0 by omega, Function.iterate_zero_apply]
  · apply charExponents_injective hp
    rw [(Function.Semiconj.iterate_right (charExponents_twist hp) (p - 1)).eq,
      twistCharExponents_iterate, twistCharExponents_sub_one]

/-- The exponent moved by twisting: `a` on tame data, `α` on wild data. -/
private def firstExponent : SerreWeightData p → ℕ
  | niveauOne a .. => a
  | niveauTwo a .. => a
  | wild α .. => α

private lemma firstExponent_le (d : SerreWeightData p) : firstExponent d ≤ p - 2 := by
  cases d <;> simp only [firstExponent] <;> omega

private lemma firstExponent_twist (d : SerreWeightData p) :
    firstExponent d.twist = firstExponent d + 1 ∨ firstExponent d.twist = 0 := by
  cases d with
  | niveauOne a b hab hb =>
    simp only [twist_niveauOne, unramified_def]
    split_ifs <;> simp [firstExponent]
  | niveauTwo a b hab hb =>
    simp only [twist_niveauTwo]
    split_ifs <;> simp [firstExponent]
  | wild α β hα hβ hβp tres htres =>
    simp only [twist_wild, firstExponent]
    split_ifs <;> simp

private lemma weight_mem_Icc_of_firstExponent_eq_zero (hp : 2 < p) {d : SerreWeightData p}
    (hd : firstExponent d = 0) : d.weight ∈ Set.Icc 2 (p + 1) := by
  refine ⟨two_le_weight hp.le d, ?_⟩
  cases d with
  | niveauOne a b hab hb =>
    simp only [firstExponent] at hd
    subst hd
    simp only [weight_niveauOne]
    split_ifs <;> omega
  | niveauTwo a b hab hb =>
    simp only [firstExponent] at hd
    subst hd
    simp only [weight_niveauTwo]
    omega
  | wild α β hα hβ hβp tres htres =>
    simp only [firstExponent] at hd
    subst hd
    simp only [weight_wild, min_eq_left (Nat.zero_le β), max_eq_right (Nat.zero_le β)]
    split_ifs <;> omega

/-- For `p > 2`, some cyclotomic twist of any datum has Serre weight in `[2, p + 1]`. -/
theorem exists_weight_twist_iterate_mem_Icc (hp : 2 < p) (d : SerreWeightData p) :
    ∃ n, (twist^[n] d).weight ∈ Set.Icc 2 (p + 1) := by
  induction h : p - 2 - firstExponent d using Nat.strong_induction_on generalizing d with
  | _ m ih =>
    by_cases hd : firstExponent d = 0
    · exact ⟨0, weight_mem_Icc_of_firstExponent_eq_zero hp hd⟩
    rcases firstExponent_twist d with h' | h'
    · have hle := firstExponent_le d.twist
      obtain ⟨n, hn⟩ := ih _ (by omega) d.twist rfl
      exact ⟨n + 1, by rwa [Function.iterate_succ_apply]⟩
    · exact ⟨1, weight_mem_Icc_of_firstExponent_eq_zero hp h'⟩

end SerreWeightData

end TauCeti
