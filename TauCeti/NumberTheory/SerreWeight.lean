/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Interval.Set.Defs

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
dyadic dichotomy `k ∈ {2, 4}`, the comparison of the two weights, and the fact that for `p > 2`
some cyclotomic twist has weight in `[2, p + 1]`
(`SerreWeightData.exists_weight_twist_iterate_mem_Icc`).

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
    · have hp : p ≠ 2 := fun h => hd₂ h rfl
      have hβα := htres rfl
      subst hβα
      simp only [edixhovenWeight_wild, weight_wild, ↓reduceIte, hp,
        min_eq_left (Nat.le_add_right α 1), max_eq_right (Nat.le_add_right α 1)]
      have : 1 ≤ p := by omega
      obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le this
      simp only [Nat.add_sub_cancel_left]
      ring

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

/-! ### Properties of the weight -/

private lemma one_add_mul_add_modEq (q a b : ℕ) : 1 + (q + 1) * a + b ≡ a + b + 1 [MOD q] := by
  rw [show 1 + (q + 1) * a + b = a + b + 1 + q * a by ring]
  exact Nat.add_modulus_mul_modEq_iff.2 rfl

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
      rw [show (α + 1) * (q + 1 + 1) = 1 + (q + 1) * α + (α + 1) + q by ring]
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

/-- At adjacent wild exponents and `p ≠ 2`, the très ramifiée weight exceeds the peu ramifiée
weight by `p - 1`. -/
theorem weight_wild_true_eq_add {α β : ℕ} (hp : p ≠ 2) (hα : α ≤ p - 2) (hβ : 1 ≤ β)
    (hβp : β ≤ p - 1) (h₁ : true = true → β = α + 1) (h₂ : false = true → β = α + 1) :
    (wild α β hα hβ hβp true h₁).weight = (wild α β hα hβ hβp false h₂).weight + (p - 1) := by
  have hβα := h₁ rfl
  subst hβα
  simp only [weight_wild, ↓reduceIte, hp, Bool.false_eq_true,
    min_eq_left (Nat.le_add_right α 1), max_eq_right (Nat.le_add_right α 1)]
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ p by omega)
  simp only [Nat.add_sub_cancel_left]
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
