/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import TauCeti.Algebra.TemperleyLieb.NormalForm
import Mathlib.LinearAlgebra.Dimension.Constructions
-- Supplies `CommSemiring.strongRankCondition_of_nontrivial` for `rank_span_le` and `finrank`.
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import TauCeti.Combinatorics.PlanarMatching.HalfDiagram

/-!
# Catalan dimension bound and bases for Temperley–Lieb algebras

Building on the Jones normal form developed in `TauCeti.Algebra.TemperleyLieb.NormalForm`, this
file counts the Jones reduced words `JonesWord n` on `n` strands by a ballot bijection matching
`TauCeti.halfCount`, showing `Fintype.card (JonesWord n) = catalan n`, and deduces module
finiteness and the Catalan rank/`finrank` upper bound for `TemperleyLieb R δ n` and its quotients
over any commutative semiring `R` — without diagram bases, cell modules, or Gram determinants.

Two immediate structural consequences accompany the upper bound:

* Over any field, `TemperleyLieb R δ n` and all of its quotients by `A`-submodules (in particular
  quotients by `R`-submodules or by left, right, or two-sided ideals such as trace radicals) are
  finite-dimensional of dimension at most `catalan n`.
* Over any commutative semiring `R`, linear independence of the reduced-word evaluations promotes
  them to a free `R`-basis (`basisJonesWord`), and any `R`-linear map out of `TemperleyLieb R δ n`
  whose range has `finrank` at least `catalan n` pins `Module.finrank R (TemperleyLieb R δ n)` to
  `catalan n` (`finrank_eq_catalan_of_catalan_le_finrank_range`). Over any commutative semiring
  satisfying `OrzechProperty` (including every commutative ring and every field), the lower bound
  `catalan n ≤ Module.finrank R (TemperleyLieb R δ n)` forces linear independence of the
  reduced-word evaluations (`linearIndependent_jonesWord_eval_of_catalan_le_finrank`), and any
  `R`-linear map whose range has `finrank` at least `catalan n` is automatically injective
  (`injective_of_catalan_le_finrank_range`).

## Main definitions

* `TauCeti.TemperleyLieb.basisJonesWord`: free `R`-basis of reduced words given linear independence
  of `JonesWord.eval δ`.

## Main results

* `TauCeti.TemperleyLieb.card_jonesWord`: `Fintype.card (JonesWord n) = catalan n`.
* `TauCeti.TemperleyLieb.span_range_comp_jonesWord_eval_of_surjective`: reduced words span any
  surjective `R`-linear image of `TemperleyLieb R δ n`.
* `TauCeti.TemperleyLieb.rank_le_catalan`, `TauCeti.TemperleyLieb.finrank_le_catalan`,
  `TauCeti.TemperleyLieb.rank_le_catalan_of_surjective`,
  `TauCeti.TemperleyLieb.finrank_le_catalan_of_surjective`,
  `TauCeti.TemperleyLieb.rank_quotient_le_catalan`,
  `TauCeti.TemperleyLieb.finrank_quotient_le_catalan`: the `R`-rank and `finrank` of
  `TemperleyLieb R δ n`, of any surjective `R`-linear image, and of any submodule or ideal quotient
  are at most `catalan n`.
* `TauCeti.TemperleyLieb.finrank_eq_catalan_of_catalan_le_finrank_range`,
  `TauCeti.TemperleyLieb.linearIndependent_jonesWord_eval_of_catalan_le_finrank`, and
  `TauCeti.TemperleyLieb.injective_of_catalan_le_finrank_range`: exact Catalan `finrank`, Orzech
  linear independence of reduced words, and the representation faithfulness criterion.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25, §4.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989, §2.8.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, Exercises 4.1.2–4.1.3.
-/

public section

namespace TauCeti.TemperleyLieb

/-! ### Catalan enumeration of Jones reduced words -/

section CatalanCount

open Finset

/-- Reduced words on `n` strands whose block start indices are `< m` and end indices are `< b`. -/
private def jonesWordsBounded (n m b : ℕ) : Finset (JonesWord n) :=
  {w : JonesWord n | ∀ p ∈ w.blocks, p.1.val < m ∧ p.2.val < b}

private theorem mem_jonesWordsBounded {n m b : ℕ} {w : JonesWord n} :
    w ∈ jonesWordsBounded n m b ↔ ∀ p ∈ w.blocks, p.1.val < m ∧ p.2.val < b :=
  Finset.mem_filter_univ w

private theorem jonesWordsBounded_top (n : ℕ) :
    jonesWordsBounded n (n - 1) (n - 1) = Finset.univ := by
  ext w
  simp [mem_jonesWordsBounded, Fin.is_lt]

private theorem jonesWordsBounded_zero_right (n m : ℕ) :
    jonesWordsBounded n m 0 = {JonesWord.empty} := by
  ext w
  rw [mem_jonesWordsBounded, Finset.mem_singleton]
  constructor
  · intro hw
    ext1
    cases h : w.blocks with
    | nil => simp
    | cons p _ => exact absurd (hw p (h ▸ List.mem_cons_self)).2 (Nat.not_lt_zero _)
  · rintro rfl
    simp

private theorem jonesWordsBounded_eq_self_of_le {n m b : ℕ} (h : m ≤ b) :
    jonesWordsBounded n m b = jonesWordsBounded n m m := by
  ext w
  simp only [mem_jonesWordsBounded]
  refine forall₂_congr fun p hp ↦ ?_
  have hle : p.2.val ≤ p.1.val := w.snd_le_fst p hp
  exact ⟨fun hp' ↦ ⟨hp'.1, lt_of_le_of_lt hle hp'.1⟩,
    fun hp' ↦ ⟨hp'.1, lt_of_lt_of_le hp'.2 h⟩⟩

private theorem jonesWordsBounded_zero_left (n b : ℕ) :
    jonesWordsBounded n 0 b = {JonesWord.empty} :=
  (jonesWordsBounded_eq_self_of_le (Nat.zero_le b)).trans (jonesWordsBounded_zero_right n 0)

/-- Forward map of the ballot bijection: send `u ∈ jonesWordsBounded n m (b + 1)` either to
`u.snoc m b` (when all block ends in `u` are `< b`) or to `u` itself (when `u` already has a block
ending at `b`). -/
private def ballotForward {n m b : ℕ} (hm : m < n - 1) (hbm : b ≤ m) (u : JonesWord n) :
    JonesWord n :=
  if h : (∀ p ∈ u.blocks, p.1.val < m) ∧ (∀ p ∈ u.blocks, p.2.val < b) then
    u.snoc ⟨m, hm⟩ ⟨b, lt_of_le_of_lt hbm hm⟩ hbm h.1 h.2
  else
    u

/-- Inverse map of the ballot bijection: keep `w` if all block starts are `< m`, otherwise drop its
final block `(m, b)`. -/
private def ballotBackward {n : ℕ} (m : ℕ) (w : JonesWord n) : JonesWord n :=
  if ∀ p ∈ w.blocks, p.1.val < m then w else w.dropLast

private theorem ballotBackward_ballotForward {n m b : ℕ} (hm : m < n - 1) (hbm : b ≤ m)
    {u : JonesWord n} (hu : u ∈ jonesWordsBounded n m (b + 1)) :
    ballotBackward m (ballotForward hm hbm u) = u := by
  rw [mem_jonesWordsBounded] at hu
  have hu₁ : ∀ p ∈ u.blocks, p.1.val < m := fun p hp ↦ (hu p hp).1
  by_cases hu₂ : ∀ p ∈ u.blocks, p.2.val < b
  · have hnot : ¬ ∀ p ∈ (u.snoc ⟨m, hm⟩ ⟨b, lt_of_le_of_lt hbm hm⟩ hbm hu₁ hu₂).blocks,
        p.1.val < m :=
      fun hall ↦ (lt_irrefl m) (hall (⟨m, hm⟩, ⟨b, lt_of_le_of_lt hbm hm⟩) (by simp))
    rw [ballotForward, dite_eq_left ⟨hu₁, hu₂⟩, ballotBackward, ite_eq_right hnot]
    ext1
    simp
  · rw [ballotForward, dite_eq_right fun h ↦ hu₂ h.2, ballotBackward, ite_eq_left hu₁]

/-- If `w ∈ jonesWordsBounded n (m + 1) (b + 1)` has a block start `≥ m` and a block end `≥ b`,
strict monotonicity of both coordinates forces its last block to be `(m, b)`. -/
private theorem eq_snoc_of_mem_jonesWordsBounded {n m b : ℕ} (hm : m < n - 1) (hbm : b ≤ m)
    {w : JonesWord n} (hw : w ∈ jonesWordsBounded n (m + 1) (b + 1))
    (hw₁ : ¬ ∀ p ∈ w.blocks, p.1.val < m) (hnot : ¬ ∀ p ∈ w.blocks, p.2.val < b) :
    ∃ (w₀ : JonesWord n) (hi : ∀ p ∈ w₀.blocks, p.1 < ⟨m, hm⟩)
      (hj : ∀ p ∈ w₀.blocks, p.2 < ⟨b, lt_of_le_of_lt hbm hm⟩),
      w = w₀.snoc ⟨m, hm⟩ ⟨b, lt_of_le_of_lt hbm hm⟩ hbm hi hj := by
  rw [mem_jonesWordsBounded] at hw
  induction w using JonesWord.snoc_induction_on with
  | empty => exact absurd (by simp) hw₁
  | snoc w₀ i j hji hi hj _ =>
    have him : i.val = m := by
      by_contra hne
      have hilt : i.val < m :=
        lt_of_le_of_ne (Nat.lt_succ_iff.1 (hw (i, j) (by simp)).1) hne
      exact hw₁ fun _ hp ↦ lt_of_le_of_lt (JonesWord.fst_le_of_mem_blocks_snoc hp) hilt
    have hjb : j.val = b := by
      by_contra hne
      have hjlt : j.val < b :=
        lt_of_le_of_ne (Nat.lt_succ_iff.1 (hw (i, j) (by simp)).2) hne
      exact hnot fun _ hp ↦ lt_of_le_of_lt (JonesWord.snd_le_of_mem_blocks_snoc hp) hjlt
    have hi_eq : i = ⟨m, hm⟩ := Fin.ext him
    have hj_eq : j = ⟨b, lt_of_le_of_lt hbm hm⟩ := Fin.ext hjb
    subst hi_eq hj_eq
    exact ⟨w₀, hi, hj, rfl⟩

private theorem ballotForward_ballotBackward {n m b : ℕ} (hm : m < n - 1) (hbm : b ≤ m)
    {w : JonesWord n} (hw : w ∈ jonesWordsBounded n (m + 1) (b + 1))
    (hnot : ¬ ∀ p ∈ w.blocks, p.2.val < b) :
    ballotBackward m w ∈ jonesWordsBounded n m (b + 1) ∧
      ballotForward hm hbm (ballotBackward m w) = w := by
  by_cases hw₁ : ∀ p ∈ w.blocks, p.1.val < m
  · rw [mem_jonesWordsBounded] at hw
    have hmem : w ∈ jonesWordsBounded n m (b + 1) :=
      mem_jonesWordsBounded.2 fun p hp ↦ ⟨hw₁ p hp, (hw p hp).2⟩
    rw [ballotBackward, ite_eq_left hw₁]
    exact ⟨hmem, by rw [ballotForward, dite_eq_right fun h ↦ hnot h.2]⟩
  · obtain ⟨w₀, hi, hj, rfl⟩ := eq_snoc_of_mem_jonesWordsBounded hm hbm hw hw₁ hnot
    rw [ballotBackward, ite_eq_right hw₁, JonesWord.dropLast_snoc]
    exact ⟨mem_jonesWordsBounded.2 fun p hp ↦
      ⟨hi p hp, Nat.lt_trans (hj p hp) (Nat.lt_succ_self b)⟩,
      by rw [ballotForward, dite_eq_left ⟨hi, hj⟩]⟩

/-- The ballot recurrence on `jonesWordsBounded`. -/
private theorem card_jonesWordsBounded_succ_succ {n m b : ℕ} (hm : m < n - 1) (hbm : b ≤ m) :
    #(jonesWordsBounded n (m + 1) (b + 1)) =
      #(jonesWordsBounded n (m + 1) b) + #(jonesWordsBounded n m (b + 1)) := by
  let S := jonesWordsBounded n (m + 1) (b + 1)
  let P : JonesWord n → Prop := fun w ↦ ∀ p ∈ w.blocks, p.2.val < b
  rw [← Finset.card_filter_add_card_filter_not P (s := S)]
  congr 1
  · congr 1
    ext w
    simp only [S, P, Finset.mem_filter, mem_jonesWordsBounded]
    exact ⟨fun ⟨h1, h2⟩ p hp ↦ ⟨(h1 p hp).1, h2 p hp⟩,
      fun h ↦ ⟨fun p hp ↦ ⟨(h p hp).1, (h p hp).2.trans (Nat.lt_succ_self b)⟩,
        fun p hp ↦ (h p hp).2⟩⟩
  · refine Finset.card_bij' (fun w _ ↦ ballotBackward m w) (fun u _ ↦ ballotForward hm hbm u)
      ?_ ?_ ?_ ?_
    · intro w hw
      rw [Finset.mem_filter] at hw
      exact (ballotForward_ballotBackward hm hbm hw.1 hw.2).1
    · intro u hu
      rw [Finset.mem_filter]
      rw [mem_jonesWordsBounded] at hu
      have hu₁ : ∀ p ∈ u.blocks, p.1.val < m := fun p hp ↦ (hu p hp).1
      dsimp only [ballotForward]
      split_ifs with h
      · refine ⟨mem_jonesWordsBounded.2 fun _ hp ↦
          ⟨lt_of_le_of_lt (JonesWord.fst_le_of_mem_blocks_snoc hp) (Nat.lt_succ_self m),
            lt_of_le_of_lt (JonesWord.snd_le_of_mem_blocks_snoc hp) (Nat.lt_succ_self b)⟩,
          fun hall ↦ (lt_irrefl b) (hall (⟨m, hm⟩, ⟨b, lt_of_le_of_lt hbm hm⟩) (by simp))⟩
      · exact ⟨mem_jonesWordsBounded.2 fun p hp ↦
          ⟨(hu₁ p hp).trans (Nat.lt_succ_self m), (hu p hp).2⟩, fun hu₂ ↦ h ⟨hu₁, hu₂⟩⟩
    · intro w hw
      rw [Finset.mem_filter] at hw
      exact (ballotForward_ballotBackward hm hbm hw.1 hw.2).2
    · intro u hu
      exact ballotBackward_ballotForward hm hbm hu

/-- Closed count of `jonesWordsBounded n m b` in terms of `TauCeti.halfCount`. -/
private theorem card_jonesWordsBounded_eq_halfCount {n m b : ℕ} (hm : m ≤ n - 1)
    (hbm : b ≤ m + 1) :
    #(jonesWordsBounded n m b) = halfCount (m + 1 + b) (m + 1 - b) := by
  induction m generalizing b with
  | zero =>
    rw [jonesWordsBounded_zero_left, Finset.card_singleton]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hbm with rfl | rfl
    · simp [halfCount_self]
    · simpa using (halfCount_two_mul_zero 1).symm
  | succ m ihm =>
    induction b with
    | zero =>
      rw [jonesWordsBounded_zero_right, Finset.card_singleton]
      simp [halfCount_self]
    | succ b ihb =>
      rcases le_or_gt b m with hbm' | hmb
      · rw [card_jonesWordsBounded_succ_succ (by omega) hbm', ihb (by omega),
          ihm (by omega) (Nat.succ_le_succ hbm'), add_comm]
        have h₁ : m + 1 + (b + 1) = m + b + 2 := by omega
        have h₂ : m + 1 - (b + 1) = m - b := by omega
        have h₃ : m + 1 + 1 + b = m + b + 2 := by omega
        have h₄ : m + 1 + 1 - b = m - b + 2 := by omega
        have h₅ : m + 1 + 1 + (b + 1) = m + b + 2 + 1 := by omega
        have h₆ : m + 1 + 1 - (b + 1) = m - b + 1 := by omega
        rw [h₁, h₂, h₃, h₄, h₅, h₆]
        exact (halfCount_succ_succ (m + b + 2) (m - b)).symm
      · have hbeq : b = m + 1 := by omega
        subst hbeq
        rw [jonesWordsBounded_eq_self_of_le (Nat.le_succ (m + 1)), ihb (Nat.le_succ (m + 1)),
          Nat.sub_self, ← Nat.add_assoc (m + 1 + 1) (m + 1) 1, halfCount_succ_zero,
          Nat.add_sub_cancel_left]

/-- **The Catalan count of Jones reduced words.** On `n` strands there are `catalan n` Jones
reduced words. -/
@[simp]
theorem card_jonesWord (n : ℕ) : Fintype.card (JonesWord n) = catalan n := by
  rw [← Finset.card_univ, ← jonesWordsBounded_top n]
  cases n with
  | zero =>
    rw [Nat.zero_sub, jonesWordsBounded_zero_left, Finset.card_singleton, catalan_zero]
  | succ k =>
    rw [Nat.succ_sub_one,
      card_jonesWordsBounded_eq_halfCount (n := k + 1) (m := k) (b := k) le_rfl (Nat.le_succ k),
      ← halfCount_two_mul_zero, two_mul, ← Nat.add_assoc (k + 1) k 1, halfCount_succ_zero,
      Nat.add_sub_cancel_left]

end CatalanCount

/-! ### Module finiteness, rank bounds, and bases -/

section Dimension

variable {R : Type*} [CommSemiring R]

/-- Over any commutative semiring `R`, the Temperley–Lieb algebra `TemperleyLieb R δ n` is finitely
generated as an `R`-module. In particular, over any field it is finite-dimensional, and so is every
quotient of it by an `A`-submodule (including any `R`-submodule or left, right, or two-sided
ideal). -/
instance (δ : R) (n : ℕ) : Module.Finite R (TemperleyLieb R δ n) := by
  have : Module.Finite R (JonesWord n →₀ R) := Module.Finite.of_basis Finsupp.basisSingleOne
  refine Module.Finite.of_surjective (Finsupp.linearCombination R (JonesWord.eval δ)) ?_
  rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, span_range_jonesWord_eval]

/-- Under any surjective `R`-linear map out of `TemperleyLieb R δ n`, the images of the
reduced-word evaluations span the target module. -/
theorem span_range_comp_jonesWord_eval_of_surjective {M : Type*} [AddCommMonoid M] [Module R M]
    {δ : R} {n : ℕ} (f : TemperleyLieb R δ n →ₗ[R] M) (hf : Function.Surjective f) :
    Submodule.span R (Set.range (f ∘ JonesWord.eval δ)) = ⊤ := by
  rw [Set.range_comp, ← Submodule.map_span, span_range_jonesWord_eval, Submodule.map_top,
    LinearMap.range_eq_top.2 hf]

/-- Any `R`-module admitting a surjective `R`-linear map from `TemperleyLieb R δ n` has `R`-rank
at most `(catalan n : Cardinal)`. -/
theorem rank_le_catalan_of_surjective {M : Type*} [AddCommMonoid M] [Module R M]
    {δ : R} {n : ℕ} (f : TemperleyLieb R δ n →ₗ[R] M) (hf : Function.Surjective f) :
    Module.rank R M ≤ catalan n := by
  by_cases hR : Nontrivial R
  · rw [← rank_top R M, ← span_range_comp_jonesWord_eval_of_surjective f hf]
    refine (rank_span_le _).trans ?_
    simpa [card_jonesWord] using Cardinal.mk_range_le_lift (f := f ∘ JonesWord.eval δ)
  · have : Subsingleton R := not_nontrivial_iff_subsingleton.1 hR
    rw [rank_subsingleton, ← card_jonesWord n]
    exact_mod_cast Nat.succ_le_of_lt Fintype.card_pos

/-- **Catalan rank bound.** Over any commutative semiring `R`, the `R`-rank of
`TemperleyLieb R δ n` is at most `(catalan n : Cardinal)`. -/
theorem rank_le_catalan (δ : R) (n : ℕ) :
    Module.rank R (TemperleyLieb R δ n) ≤ catalan n :=
  rank_le_catalan_of_surjective LinearMap.id Function.surjective_id

/-- Any `R`-module admitting a surjective `R`-linear map from `TemperleyLieb R δ n` has `finrank`
at most `catalan n`. When `R` is a commutative ring, this applies in particular to every quotient of
`TemperleyLieb R δ n` by an `A`-submodule (including any `R`-submodule or left, right, or two-sided
ideal). -/
theorem finrank_le_catalan_of_surjective {M : Type*} [AddCommMonoid M] [Module R M]
    {δ : R} {n : ℕ} (f : TemperleyLieb R δ n →ₗ[R] M) (hf : Function.Surjective f) :
    Module.finrank R M ≤ catalan n :=
  Module.finrank_le_of_rank_le (rank_le_catalan_of_surjective f hf)

/-- **Catalan `finrank` bound.** Over any commutative semiring `R`, the `finrank` of
`TemperleyLieb R δ n` is at most `catalan n`. -/
theorem finrank_le_catalan (δ : R) (n : ℕ) :
    Module.finrank R (TemperleyLieb R δ n) ≤ catalan n :=
  finrank_le_catalan_of_surjective LinearMap.id Function.surjective_id

/-- Any quotient of `TemperleyLieb S δ n` by an `A`-submodule (in particular by an `S`-submodule
or by any left, right, or two-sided ideal) has `S`-rank at most `(catalan n : Cardinal)`. -/
theorem rank_quotient_le_catalan {S A : Type*} [CommRing S] [Ring A] {δ : S} {n : ℕ}
    [Module A (TemperleyLieb S δ n)] [SMul S A] [IsScalarTower S A (TemperleyLieb S δ n)]
    (p : Submodule A (TemperleyLieb S δ n)) :
    Module.rank S (TemperleyLieb S δ n ⧸ p) ≤ catalan n :=
  rank_le_catalan_of_surjective (p.mkQ.restrictScalars S) p.mkQ_surjective

/-- Any quotient of `TemperleyLieb S δ n` by an `A`-submodule (in particular by an `S`-submodule
or by any left, right, or two-sided ideal) has `finrank` at most `catalan n`. -/
theorem finrank_quotient_le_catalan {S A : Type*} [CommRing S] [Ring A] {δ : S} {n : ℕ}
    [Module A (TemperleyLieb S δ n)] [SMul S A] [IsScalarTower S A (TemperleyLieb S δ n)]
    (p : Submodule A (TemperleyLieb S δ n)) :
    Module.finrank S (TemperleyLieb S δ n ⧸ p) ≤ catalan n :=
  finrank_le_catalan_of_surjective (p.mkQ.restrictScalars S) p.mkQ_surjective

/-- When an `R`-linear map out of `TemperleyLieb R δ n` has range of `finrank` at least
`catalan n`, the `finrank` of `TemperleyLieb R δ n` equals `catalan n`. -/
theorem finrank_eq_catalan_of_catalan_le_finrank_range
    {M : Type*} [AddCommMonoid M] [Module R M] {δ : R} {n : ℕ}
    (f : TemperleyLieb R δ n →ₗ[R] M) (hf : catalan n ≤ Module.finrank R (LinearMap.range f)) :
    Module.finrank R (TemperleyLieb R δ n) = catalan n :=
  le_antisymm (finrank_le_catalan δ n) <| hf.trans <|
    Module.finrank_le_finrank_of_rank_le_rank (lift_rank_range_le f)
      ((rank_le_catalan δ n).trans_lt Cardinal.natCast_lt_aleph0)

/-- Free `R`-basis of `TemperleyLieb R δ n` indexed by `JonesWord n`, given linear independence of
the reduced-word evaluations `JonesWord.eval δ`. -/
noncomputable def basisJonesWord {δ : R} {n : ℕ}
    (h : LinearIndependent R (JonesWord.eval (R := R) δ (n := n))) :
    Module.Basis (JonesWord n) R (TemperleyLieb R δ n) :=
  Module.Basis.mk h (span_range_jonesWord_eval δ n).ge

/-- Basis vector of `basisJonesWord h` at `w` is `w.eval δ`. -/
@[simp]
theorem basisJonesWord_apply {δ : R} {n : ℕ}
    (h : LinearIndependent R (JonesWord.eval (R := R) δ (n := n))) (w : JonesWord n) :
    basisJonesWord h w = w.eval δ :=
  Module.Basis.mk_apply _ _ w

section Orzech

variable [OrzechProperty R] {δ : R} {n : ℕ}

/-- Over a commutative semiring satisfying the Orzech property (in particular over any commutative
ring or field), if `TemperleyLieb R δ n` has `finrank` at least `catalan n`, then the evaluations
`JonesWord.eval δ` are `R`-linearly independent. -/
theorem linearIndependent_jonesWord_eval_of_catalan_le_finrank
    (h : catalan n ≤ Module.finrank R (TemperleyLieb R δ n)) :
    LinearIndependent R (JonesWord.eval (R := R) δ (n := n)) :=
  linearIndependent_of_top_le_span_of_card_le_finrank
    (span_range_jonesWord_eval δ n).ge ((card_jonesWord n).trans_le h)

/-- **Representation faithfulness criterion.** Over a commutative semiring with the Orzech property
(including every commutative ring and field), any `R`-linear map out of `TemperleyLieb R δ n` whose
range has `finrank` at least `catalan n` is injective. -/
theorem injective_of_catalan_le_finrank_range {M : Type*} [AddCommMonoid M] [Module R M]
    (f : TemperleyLieb R δ n →ₗ[R] M) (hf : catalan n ≤ Module.finrank R (LinearMap.range f)) :
    Function.Injective f := by
  let B := basisJonesWord (linearIndependent_jonesWord_eval_of_catalan_le_finrank
    (finrank_eq_catalan_of_catalan_le_finrank_range f hf).ge)
  have h : B.constr ℕ (f.rangeRestrict ∘ JonesWord.eval δ) = f.rangeRestrict :=
    B.constr_eq ℕ fun w ↦ by simp [B]
  have hli : LinearIndependent R (f.rangeRestrict ∘ JonesWord.eval (R := R) δ (n := n)) :=
    linearIndependent_of_top_le_span_of_card_le_finrank
      (span_range_comp_jonesWord_eval_of_surjective f.rangeRestrict f.surjective_rangeRestrict).ge
      ((card_jonesWord n).trans_le hf)
  exact f.injective_rangeRestrict_iff.1 <|
    h ▸ B.injective_constr_of_linearIndependent (R₂ := ℕ) hli

end Orzech

end Dimension

end TauCeti.TemperleyLieb
