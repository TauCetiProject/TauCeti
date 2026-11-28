/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Defs
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.KDominant
public import TauCeti.RepresentationTheory.DiscreteSeries.BlockRule
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.Finset.Basic

/-!
# Doubled Harish-Chandra parameters of `U(p, q)`: `ρ`, the lowest `K`-type and the Casimir value

Let `ι` be a finite index set of size `n` with signs `ε` (for `U(p, q)`, the signs of the
hermitian form `diag ε`). A discrete series of `U(p, q)` is labelled by its Harish-Chandra
parameter `λ`, stored doubled as an integer vector `l = 2λ : ι → ℤ`; with a gap between the
entries of different signs (`TauCeti.DiscreteSeries.HasGap`) its entries are distinct and of the
parity of `n - 1`. The root `e_a - e_b` is positive for `l` when `l b < l a`. This file attaches to
`l` the data that the discrete series of parameter `λ` is described by:

* `2ρ(o)_a = #{b | o b < o a} - #{b | o a < o b}`, twice the half-sum of the positive roots of the
  order given by any `o` (`TauCeti.DiscreteSeries.twoRho`), and its compact analogue `2ρ_c`, where
  only the indices of the sign of `a` count (`TauCeti.DiscreteSeries.twoRhoCompact`);
* `λ + ρ = (l + 2ρ) / 2` (`TauCeti.DiscreteSeries.paramAddRho`), an integer vector by the parity
  condition (`TauCeti.DiscreteSeries.two_mul_paramAddRho`);
* the **lowest `K`-type** `Λ = λ + ρ - 2ρ_c` (`TauCeti.DiscreteSeries.lowestKType`), which is
  `K`-dominant for `-l` (`TauCeti.DiscreteSeries.isKDominant_lowestKType`), so that the products of
  principal minors `m_Λ` transform under block diagonal triangular matrices; for all signs equal
  it is `λ - ρ` (`TauCeti.DiscreteSeries.lowestKType_of_forall_eq`);
* the **Casimir value** `κ_λ = |λ|² - |ρ|² = ∑_a (l_a² - (2ρ_a)²) / 4`
  (`TauCeti.DiscreteSeries.casimirValue`), an integer by the parity condition;
* the **Weyl dimension polynomial** `dim(λ) = ∏_{l b < l a} (λ_a - λ_b) / ∏_{i < n} i!`
  (`TauCeti.DiscreteSeries.weylDimensionPoly`), which is positive;
* the **root cone** of `l`, the integer vectors `β` with `o ⬝ᵥ β ≤ 0` for every `o` whose order
  reverses that of `l` (`TauCeti.DiscreteSeries.rootCone`). It contains the positive roots, and its
  elements have coordinate sum zero.

A parameter has **large gap `A`** if it has gap `500 n³ + A`
(`TauCeti.DiscreteSeries.HasLargeGap`); every sign vector carries parameters of every large gap
(`TauCeti.DiscreteSeries.exists_hasLargeGap`).

## Main definitions

* `TauCeti.DiscreteSeries.twoRho`, `TauCeti.DiscreteSeries.twoRhoCompact`: `2ρ` and `2ρ_c`.
* `TauCeti.DiscreteSeries.paramAddRho`: `λ + ρ`.
* `TauCeti.DiscreteSeries.lowestKType`: the lowest `K`-type `Λ = λ + ρ - 2ρ_c`.
* `TauCeti.DiscreteSeries.casimirValue`: `κ_λ = |λ|² - |ρ|²`.
* `TauCeti.DiscreteSeries.weylDimensionPoly`: `dim(λ)`.
* `TauCeti.DiscreteSeries.rootCone`: the root cone of `l`.
* `TauCeti.DiscreteSeries.HasLargeGap`: the parameter has gap `500 n³ + A`.

## Main results

* `TauCeti.DiscreteSeries.twoRho_lt_twoRho`, `TauCeti.DiscreteSeries.abs_twoRho_lt`,
  `TauCeti.DiscreteSeries.sum_twoRho`, `TauCeti.DiscreteSeries.twoRho_eq_two_mul_card_sub`:
  `2ρ` is strictly monotone along `o`, bounded by `n`, of sum zero, and of the parity of `n - 1`
  when `o` is injective.
* `TauCeti.DiscreteSeries.two_mul_paramAddRho`, `TauCeti.DiscreteSeries.two_mul_lowestKType`: the
  doubled forms of `λ + ρ` and `Λ`.
* `TauCeti.DiscreteSeries.isKDominant_lowestKType`: `Λ` is `K`-dominant for `-l`.
* `TauCeti.DiscreteSeries.four_mul_casimirValue`,
  `TauCeti.DiscreteSeries.casimirValue_eq_sum_div`: `κ_λ = ∑_a (l_a² - (2ρ_a)²) / 4`.
* `TauCeti.DiscreteSeries.weylDimensionPoly_pos`: `dim(λ) > 0`.
* `TauCeti.DiscreteSeries.single_sub_single_mem_rootCone`,
  `TauCeti.DiscreteSeries.sum_eq_zero_of_mem_rootCone`: the positive roots lie in the root cone,
  and so do only vectors of coordinate sum zero.

## References

* A. W. Knapp, *Representation Theory of Semisimple Groups*, Princeton University Press (1986),
  Chapter IX (Harish-Chandra parameters of discrete series and their lowest `K`-types).
* R. Parthasarathy, *Dirac operator and the discrete series*, Ann. of Math. 96 (1972), 1–30.
* The shorter formal proof of the Riemann hypothesis for Dirichlet `L`-functions,
  <https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh>
  (Apache 2.0): the definitions follow `New.paramAddRho`, `New.HCParam.HasLargeGap`,
  `New.HCParam.lowestKType`, `New.HCParam.casimirValue` and `New.weylDimensionPoly` in
  `src/Lib/DiscreteSeries/FlenstedJensen/Defs.lean`, and `New.HCParam.rootCone` in
  `src/Lib/DiscreteSeries/Rigidity/RepresentationsAndCasimirs.lean`.
-/

public section

open Finset Fintype

namespace TauCeti.DiscreteSeries

variable {ι : Type*} [Fintype ι]

/-! ### Twice the half-sum of the positive roots -/

section TwoRho

variable {α : Type*} [LinearOrder α] {o : ι → α}

/-- **Twice the half-sum of the positive roots** for the order given by `o`, at the index `a`:
`2ρ(o)_a = #{b | o b < o a} - #{b | o a < o b}`. The root `e_a - e_b` is positive for `o` when
`o b < o a`, and `2ρ(o)` is the sum of the positive roots. -/
def twoRho (o : ι → α) (a : ι) : ℤ :=
  #{b | o b < o a} - #{b | o a < o b}

theorem twoRho_def (o : ι → α) (a : ι) :
    twoRho o a = #{b | o b < o a} - #{b | o a < o b} :=
  (rfl)

/-- `2ρ(o)` is strictly monotone along `o`. -/
theorem twoRho_lt_twoRho {a b : ι} (h : o a < o b) : twoRho o a < twoRho o b := by
  have h₁ : #{c | o c < o a} < #{c | o c < o b} := by
    refine card_lt_card ((ssubset_iff_of_subset fun c hc ↦ ?_).2 ⟨a, by simp [h], by simp⟩)
    simp only [mem_filter, mem_univ, true_and] at hc ⊢
    exact hc.trans h
  have h₂ : #{c | o b < o c} < #{c | o a < o c} := by
    refine card_lt_card ((ssubset_iff_of_subset fun c hc ↦ ?_).2 ⟨b, by simp [h], by simp⟩)
    simp only [mem_filter, mem_univ, true_and] at hc ⊢
    exact h.trans hc
  rw [twoRho_def, twoRho_def]
  omega

/-- The entries of `2ρ(o)` are less than `n` in absolute value. -/
theorem abs_twoRho_lt (o : ι → α) (a : ι) : |twoRho o a| < card ι := by
  have h₁ : #{b | o b < o a} < card ι := card_lt_univ_of_notMem (x := a) (by simp)
  have h₂ : #{b | o a < o b} < card ι := card_lt_univ_of_notMem (x := a) (by simp)
  rw [twoRho_def, abs_lt]
  omega

/-- The entries of `2ρ(o)` sum to zero: each positive root `e_a - e_b` contributes `1` at `a` and
`-1` at `b`. -/
theorem sum_twoRho (o : ι → α) : ∑ a, twoRho o a = 0 := by
  simp only [twoRho_def, sum_sub_distrib, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  rw [sum_comm (f := fun a b ↦ if o a < o b then (1 : ℤ) else 0), sub_self]

omit [Fintype ι] in
/-- On a finset containing `a` on which `o` is injective, the indices below and above `a` make up
everything but `a`. -/
private theorem card_filter_lt_add_card_filter_gt {s : Finset ι} (ho : Set.InjOn o s) {a : ι}
    (ha : a ∈ s) : #{b ∈ s | o b < o a} + #{b ∈ s | o a < o b} + 1 = #s := by
  classical
  have h := card_filter_lt_add_card_filter_gt_add_one (mem_image_of_mem o ha)
  rwa [filter_image, filter_image, card_image_of_injOn (ho.mono (filter_subset _ _)),
    card_image_of_injOn (ho.mono (filter_subset _ _)), card_image_of_injOn ho] at h

/-- For injective `o`, `2ρ(o)_a = 2 #{b | o b < o a} - (n - 1)`. -/
theorem twoRho_eq_two_mul_card_sub (ho : o.Injective) (a : ι) :
    twoRho o a = 2 * #{b | o b < o a} - (card ι - 1) := by
  have h := card_filter_lt_add_card_filter_gt (s := univ) (ho.injOn) (mem_univ a)
  rw [card_univ] at h
  rw [twoRho_def]
  omega

/-- For injective `o`, the entries of `2ρ(o)` have the parity of `n - 1`. -/
theorem even_twoRho_add_card_sub_one (ho : o.Injective) (a : ι) :
    Even (twoRho o a + card ι - 1) := by
  rw [twoRho_eq_two_mul_card_sub ho]
  exact ⟨#{b | o b < o a}, by ring⟩

/-- Reversing the order reverses `2ρ`. -/
theorem twoRho_neg {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (o : ι → G) : twoRho (-o) = -twoRho o := by
  ext a
  simp only [twoRho_def, Pi.neg_apply, neg_lt_neg_iff, neg_sub]

variable {β : Type*} [DecidableEq β]

/-- **Twice the half-sum of the compact positive roots** for the signs `ε` and the order given by
`o`, at the index `a`: the count of `2ρ(o)_a` taken over the indices `b` of the sign of `a`,
`2ρ_c(o)_a = #{b | ε b = ε a ∧ o b < o a} - #{b | ε b = ε a ∧ o a < o b}`. -/
def twoRhoCompact (ε : ι → β) (o : ι → α) (a : ι) : ℤ :=
  #{b | ε b = ε a ∧ o b < o a} - #{b | ε b = ε a ∧ o a < o b}

theorem twoRhoCompact_def (ε : ι → β) (o : ι → α) (a : ι) :
    twoRhoCompact ε o a = #{b | ε b = ε a ∧ o b < o a} - #{b | ε b = ε a ∧ o a < o b} :=
  (rfl)

/-- For signs that are all equal, `2ρ_c = 2ρ`. -/
theorem twoRhoCompact_of_forall_eq {ε : ι → β} (hε : ∀ a b, ε a = ε b) (o : ι → α) :
    twoRhoCompact ε o = twoRho o := by
  ext a
  simp [twoRhoCompact_def, twoRho_def, hε _ a]

/-- For injective `o`, `2ρ_c(o)_a = 2 #{b | ε b = ε a ∧ o b < o a} - (#{b | ε b = ε a} - 1)`. -/
theorem twoRhoCompact_eq_two_mul_card_sub {ε : ι → β} (ho : o.Injective) (a : ι) :
    twoRhoCompact ε o a =
      2 * #{b | ε b = ε a ∧ o b < o a} - (#{b | ε b = ε a} - 1) := by
  have h := card_filter_lt_add_card_filter_gt (s := {b | ε b = ε a}) (ho.injOn)
    (a := a) (by simp)
  rw [filter_filter, filter_filter] at h
  rw [twoRhoCompact_def]
  omega

end TwoRho

/-! ### The parameter shifted by `ρ` and the lowest `K`-type -/

variable {l : ι → ℤ}

/-- **The parameter shifted by `ρ`**, `λ + ρ = (l + 2ρ) / 2` for the doubled parameter `l = 2λ`
and the order of `l`. When the entries of `l` are distinct and of the parity of `n - 1`, so are
those of `2ρ(l)`, and the division is exact (`TauCeti.DiscreteSeries.two_mul_paramAddRho`). -/
def paramAddRho (l : ι → ℤ) (a : ι) : ℤ :=
  (l a + twoRho l a) / 2

theorem paramAddRho_def (l : ι → ℤ) (a : ι) : paramAddRho l a = (l a + twoRho l a) / 2 :=
  (rfl)

/-- For a doubled parameter with distinct entries of the parity of `n - 1`,
`2 (λ + ρ) = l + 2ρ`. -/
theorem two_mul_paramAddRho (hl : l.Injective) (hpar : ∀ a, Even (l a + card ι - 1)) (a : ι) :
    2 * paramAddRho l a = l a + twoRho l a := by
  obtain ⟨r, hr⟩ := hpar a
  obtain ⟨s, hs⟩ := even_twoRho_add_card_sub_one hl a
  rw [paramAddRho_def]
  omega

variable {β : Type*} [DecidableEq β] {ε : ι → β}

/-- **The lowest `K`-type** `Λ = λ + ρ - 2ρ_c` of the doubled parameter `l = 2λ` for the signs `ε`,
with `ρ` and `ρ_c` taken for the order of `l`. -/
def lowestKType (ε : ι → β) (l : ι → ℤ) (a : ι) : ℤ :=
  paramAddRho l a - twoRhoCompact ε l a

theorem lowestKType_def (ε : ι → β) (l : ι → ℤ) (a : ι) :
    lowestKType ε l a = paramAddRho l a - twoRhoCompact ε l a :=
  (rfl)

/-- For a doubled parameter with distinct entries of the parity of `n - 1`,
`2Λ = l + 2ρ - 2 · 2ρ_c`. -/
theorem two_mul_lowestKType (hl : l.Injective) (hpar : ∀ a, Even (l a + card ι - 1)) (a : ι) :
    2 * lowestKType ε l a = l a + twoRho l a - 2 * twoRhoCompact ε l a := by
  rw [lowestKType_def, mul_sub, two_mul_paramAddRho hl hpar]

/-- For signs that are all equal (the compact form), the lowest `K`-type is `λ - ρ`. -/
theorem lowestKType_of_forall_eq (hε : ∀ a b, ε a = ε b) (l : ι → ℤ) (a : ι) :
    lowestKType ε l a = paramAddRho l a - twoRho l a := by
  rw [lowestKType_def, twoRhoCompact_of_forall_eq hε]

omit [Fintype ι] in
/-- A finset of indices on which `l` is injective, with values in `[x, y)` all congruent to `x`
modulo `2`, has at most `(y - x) / 2` elements when `y - x` is even and nonnegative. -/
private theorem two_mul_card_le {s : Finset ι} (hl : Set.InjOn l s) {x y : ℤ} (hle : x ≤ y)
    (hxy : Even (y - x)) (hs : ∀ c ∈ s, x ≤ l c ∧ l c < y ∧ Even (l c - x)) :
    2 * (#s : ℤ) ≤ y - x := by
  obtain ⟨r, hr⟩ := hxy
  -- Halving `l c - x` maps `s` injectively into `[0, (y - x) / 2)`.
  have hcard : #s ≤ #(Ico 0 r) := by
    refine card_le_card_of_injOn (fun c ↦ (l c - x) / 2) (fun c hc ↦ ?_) fun c hc c' hc' h ↦ ?_
    · obtain ⟨h₁, h₂, k, hk⟩ := hs c hc
      simp only [coe_Ico, Set.mem_Ico]
      omega
    · obtain ⟨-, -, k, hk⟩ := hs c hc
      obtain ⟨-, -, k', hk'⟩ := hs c' hc'
      exact hl hc hc' (by simp only at h; omega)
  rw [Int.card_Ico] at hcard
  omega

/-- **The lowest `K`-type is `K`-dominant for `-l`**: for a doubled parameter with distinct entries
of the parity of `n - 1`, `Λ_b ≤ Λ_a` whenever `ε a = ε b` and `l b < l a`. -/
theorem isKDominant_lowestKType (hl : l.Injective) (hpar : ∀ a, Even (l a + card ι - 1)) :
    IsKDominant ε (-l) (lowestKType ε l) := by
  rw [isKDominant_iff]
  intro a b hε hab
  simp only [Pi.neg_apply, neg_lt_neg_iff] at hab
  -- The indices `c` with `l b ≤ l c < l a`, and those among them of the sign of `a`.
  set D : Finset ι := {c | l b ≤ l c ∧ l c < l a}
  set Dc : Finset ι := {c | ε c = ε a ∧ (l b ≤ l c ∧ l c < l a)}
  have hlt : #{c | l c < l a} = #{c | l c < l b} + #D := by
    rw [← card_filter_add_card_filter_not (s := {c | l c < l a}) (fun c ↦ l c < l b),
      filter_filter, filter_filter]
    congr 2
    · ext c
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.trans hab, h⟩⟩
    · ext c
      simp only [mem_filter, mem_univ, true_and, not_lt, D]
      exact and_comm
  have hltc : #{c | ε c = ε a ∧ l c < l a} = #{c | ε c = ε b ∧ l c < l b} + #Dc := by
    rw [← card_filter_add_card_filter_not (s := {c | ε c = ε a ∧ l c < l a})
      (fun c ↦ l c < l b), filter_filter, filter_filter]
    congr 2
    · ext c
      simp only [mem_filter, mem_univ, true_and, hε]
      exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2.trans hab⟩, h.2⟩⟩
    · ext c
      simp only [mem_filter, mem_univ, true_and, not_lt, Dc]
      exact ⟨fun h ↦ ⟨h.1.1, h.2, h.1.2⟩, fun h ↦ ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩
  have hDc : #Dc ≤ #D := card_le_card fun c hc ↦ by
    simp only [mem_filter, mem_univ, true_and, Dc, D] at hc ⊢
    exact hc.2
  have hD : 2 * (#D : ℤ) ≤ l a - l b := by
    refine two_mul_card_le hl.injOn hab.le ?_ fun c hc ↦ ?_
    · obtain ⟨r, hr⟩ := hpar a
      obtain ⟨s, hs⟩ := hpar b
      exact ⟨r - s, by omega⟩
    · simp only [mem_filter, mem_univ, true_and, D] at hc
      obtain ⟨r, hr⟩ := hpar c
      obtain ⟨s, hs⟩ := hpar b
      exact ⟨hc.1, hc.2, r - s, by omega⟩
  have hεab : #{c | ε c = ε a} = #{c | ε c = ε b} := by rw [hε]
  have h₁ := two_mul_lowestKType (ε := ε) hl hpar a
  have h₂ := two_mul_lowestKType (ε := ε) hl hpar b
  rw [twoRho_eq_two_mul_card_sub hl, twoRhoCompact_eq_two_mul_card_sub hl] at h₁ h₂
  omega

/-! ### The Casimir value -/

/-- **The Casimir value** `κ_λ = |λ|² - |ρ|² = ∑_a (λ + ρ)_a (λ - ρ)_a` of the doubled parameter
`l = 2λ`, with `ρ` taken for the order of `l`. When the entries of `l` are distinct and of the
parity of `n - 1` it is `∑_a (l_a² - (2ρ_a)²) / 4`
(`TauCeti.DiscreteSeries.casimirValue_eq_sum_div`), the eigenvalue of the Casimir operator on a
discrete series of parameter `λ`. -/
def casimirValue (l : ι → ℤ) : ℤ :=
  ∑ a, paramAddRho l a * (paramAddRho l a - twoRho l a)

theorem casimirValue_def (l : ι → ℤ) :
    casimirValue l = ∑ a, paramAddRho l a * (paramAddRho l a - twoRho l a) :=
  (rfl)

/-- For a doubled parameter with distinct entries of the parity of `n - 1`,
`4 κ_λ = ∑_a (l_a² - (2ρ_a)²)`. -/
theorem four_mul_casimirValue (hl : l.Injective) (hpar : ∀ a, Even (l a + card ι - 1)) :
    4 * casimirValue l = ∑ a, (l a ^ 2 - twoRho l a ^ 2) := by
  rw [casimirValue_def, mul_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  linear_combination (2 * paramAddRho l a + l a - twoRho l a) * two_mul_paramAddRho hl hpar a

/-- For a doubled parameter with distinct entries of the parity of `n - 1`,
`κ_λ = |λ|² - |ρ|² = ∑_a (l_a² - (2ρ_a)²) / 4` in any field of characteristic not `2`. -/
theorem casimirValue_eq_sum_div (K : Type*) [Field K] [NeZero (2 : K)] (hl : l.Injective)
    (hpar : ∀ a, Even (l a + card ι - 1)) :
    (casimirValue l : K) = ∑ a, ((l a : K) ^ 2 - (twoRho l a : K) ^ 2) / 4 := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero two_ne_zero two_ne_zero
  have h := congrArg (fun x : ℤ ↦ (x : K)) (four_mul_casimirValue hl hpar)
  push_cast at h
  rw [← sum_div, eq_div_iff h4, mul_comm, h]

/-! ### The Weyl dimension polynomial -/

/-- **The Weyl dimension polynomial** at the parameter `λ = l / 2`,
`dim(λ) = ∏_{l b < l a} (λ_a - λ_b) / ∏_{i < n} i!`, the product taken over the positive roots
`e_a - e_b` of `l`: the polynomial of Weyl's dimension formula for `U(n)`, evaluated at `λ`. -/
def weylDimensionPoly (l : ι → ℤ) : ℚ :=
  (∏ a, ∏ b ∈ {b | l b < l a}, ((l a - l b : ℚ) / 2)) / ∏ i ∈ range (card ι), (i.factorial : ℚ)

theorem weylDimensionPoly_def (l : ι → ℤ) :
    weylDimensionPoly l =
      (∏ a, ∏ b ∈ {b | l b < l a}, ((l a - l b : ℚ) / 2)) /
        ∏ i ∈ range (card ι), (i.factorial : ℚ) :=
  (rfl)

/-- The Weyl dimension polynomial is positive at every parameter: each factor `λ_a - λ_b` is
positive. -/
theorem weylDimensionPoly_pos (l : ι → ℤ) : 0 < weylDimensionPoly l := by
  rw [weylDimensionPoly_def]
  refine div_pos (prod_pos fun a _ ↦ prod_pos fun b hb ↦ ?_)
    (prod_pos fun i _ ↦ by exact_mod_cast i.factorial_pos)
  simp only [mem_filter, mem_univ, true_and] at hb
  have : (l b : ℚ) < l a := by exact_mod_cast hb
  linarith

theorem weylDimensionPoly_ne_zero (l : ι → ℤ) : weylDimensionPoly l ≠ 0 :=
  (weylDimensionPoly_pos l).ne'

/-! ### The root cone -/

section RootCone

variable {α : Type*} [LinearOrder α]

/-- **The root cone** of `l`: the integer vectors `β` with `o ⬝ᵥ β ≤ 0` for every `o : ι → ℤ`
whose order reverses that of `l` (`o a < o b` whenever `l b < l a`). It is the cone of the vectors
that are nonnegative on the dual of the positive roots `e_a - e_b`, `l b < l a`. -/
def rootCone (l : ι → α) : AddSubmonoid (ι → ℤ) where
  carrier := {β | ∀ o : ι → ℤ, (∀ a b, l b < l a → o a < o b) → o ⬝ᵥ β ≤ 0}
  add_mem' {β β'} hβ hβ' o ho := by
    rw [dotProduct_add]
    exact add_nonpos (hβ o ho) (hβ' o ho)
  zero_mem' o _ := by simp

theorem mem_rootCone {l : ι → α} {β : ι → ℤ} :
    β ∈ rootCone l ↔ ∀ o : ι → ℤ, (∀ a b, l b < l a → o a < o b) → o ⬝ᵥ β ≤ 0 :=
  Iff.rfl

/-- The positive roots `e_a - e_b`, `l b < l a`, lie in the root cone of `l`. -/
theorem single_sub_single_mem_rootCone [DecidableEq ι] {l : ι → α} {a b : ι} (h : l b < l a) :
    Pi.single a 1 - Pi.single b 1 ∈ rootCone l := by
  intro o ho
  rw [dotProduct_sub, dotProduct_single, dotProduct_single, mul_one, mul_one, sub_nonpos]
  exact (ho a b h).le

/-- The vectors of the root cone have coordinate sum zero. -/
theorem sum_eq_zero_of_mem_rootCone {l : ι → α} {β : ι → ℤ} (hβ : β ∈ rootCone l) :
    ∑ a, β a = 0 := by
  -- `-2ρ(l)`, shifted by any constant `t`, reverses the order of `l`.
  have key (t : ℤ) : -(twoRho l ⬝ᵥ β) + t * ∑ a, β a ≤ 0 := by
    have := hβ (fun a ↦ -twoRho l a + t) fun a b h ↦ by
      have := twoRho_lt_twoRho h
      omega
    simpa only [dotProduct, add_mul, neg_mul, sum_add_distrib, sum_neg_distrib, mul_sum]
      using this
  have h₁ := key (|twoRho l ⬝ᵥ β| + 1)
  have h₂ := key (-(|twoRho l ⬝ᵥ β| + 1))
  have h₃ := neg_abs_le (twoRho l ⬝ᵥ β)
  have h₄ := le_abs_self (twoRho l ⬝ᵥ β)
  rcases lt_trichotomy (∑ a, β a) 0 with h | h | h
  · nlinarith
  · exact h
  · nlinarith

end RootCone

/-! ### Large gaps -/

/-- A doubled parameter `l` for the signs `s` has **large gap `A`** if it has gap `500 n³ + A`,
`n` the number of indices. -/
def HasLargeGap (A : ℕ) (s : ι → ℤˣ) (l : ι → ℤ) : Prop :=
  HasGap (500 * card ι ^ 3 + A) s l

theorem hasLargeGap_iff {A : ℕ} {s : ι → ℤˣ} :
    HasLargeGap A s l ↔ HasGap (500 * card ι ^ 3 + A) s l :=
  Iff.rfl

theorem HasLargeGap.hasGap {A : ℕ} {s : ι → ℤˣ} (h : HasLargeGap A s l) :
    HasGap (500 * card ι ^ 3 + A) s l :=
  h

/-- A parameter with large gap `A` has every smaller large gap. -/
theorem HasLargeGap.mono {A A' : ℕ} {s : ι → ℤˣ} (h : HasLargeGap A s l) (hle : A' ≤ A) :
    HasLargeGap A' s l :=
  HasGap.mono h (by omega)

/-- Every sign vector carries doubled parameters of every large gap: list the indices as
`0, 1, …, n - 1` and space them `2 (500 n³ + A + 1)` apart. -/
theorem exists_hasLargeGap (A : ℕ) (s : ι → ℤˣ) : ∃ l : ι → ℤ, HasLargeGap A s l := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ, g = 500 * card ι ^ 3 + A := ⟨_, rfl⟩
  have hpos : (0 : ℤ) < 2 * (g + 1) := by positivity
  let e := equivFin ι
  refine ⟨fun a ↦ 2 * (g + 1) * ((e a : ℕ) : ℤ) + (card ι - 1), ?_⟩
  rw [hasLargeGap_iff, ← hg]
  refine ⟨fun a b hab ↦ ?_, fun a ↦ ⟨(g + 1) * ((e a : ℕ) : ℤ) + (card ι - 1), by ring⟩,
    fun a b hab ↦ ?_⟩
  · have : ((e a : ℕ) : ℤ) = (e b : ℕ) := mul_left_cancel₀ hpos.ne' (by linarith)
    exact e.injective (Fin.ext (by exact_mod_cast this))
  · have hne : (e a : ℕ) ≠ e b := fun h ↦ hab (by rw [e.injective (Fin.ext h)])
    have h₁ : (1 : ℤ) ≤ |((e a : ℕ) : ℤ) - (e b : ℕ)| := Int.one_le_abs (by omega)
    rw [add_sub_add_right_eq_sub, ← mul_sub, abs_mul, abs_of_pos hpos]
    nlinarith

end TauCeti.DiscreteSeries
