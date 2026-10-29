/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Order.WellFoundedSet

/-!
# Colexicographic order on exponents of bounded degree

This file studies the colexicographic order `Colex (α →₀ ℕ)` through the largest index of the
support.

## Main declarations

* `Finsupp.max'_lt_or_of_toColex_lt`: a colexicographic comparison of nonzero exponents compares
  their largest support indices, then the exponents there, then the remainders after erasing them.
* `Finsupp.wellFoundedOn_setOf_degree_le_toColex_gt`: when `α` has no infinite ascending chains,
  there is no infinite strictly increasing colexicographic chain of exponents of bounded degree.
  The bound on the degree is necessary, since `single a 1, single a 2, …` is colexicographically
  increasing.
-/

public section

namespace Finsupp

variable {α : Type*} [LinearOrder α]

/-- If `toColex y < toColex x` for nonzero `y`, compare the largest indices `mx`, `my` of the
supports: either `my < mx`, or they agree and then either `y my < x mx`, or these exponents
also agree and the comparison persists after erasing that index. -/
theorem max'_lt_or_of_toColex_lt {x y : α →₀ ℕ} (hx : x.support.Nonempty)
    (hy : y.support.Nonempty) (h : toColex y < toColex x) :
    y.support.max' hy < x.support.max' hx ∨ y.support.max' hy = x.support.max' hx ∧
      (y (y.support.max' hy) < x (x.support.max' hx) ∨
        y (y.support.max' hy) = x (x.support.max' hx) ∧
          toColex (y.erase (y.support.max' hy)) < toColex (x.erase (x.support.max' hx))) := by
  -- `Colex (α →₀ ℕ)` is a type synonym and Mathlib has no evaluation lemma for `toColex` on
  -- `Finsupp`, so `Colex.lt_iff` evaluates `toColex f` through the coercion of `α →₀ ℕ`, which
  -- is definitionally `f`. We restate its components, and the goals below, at `α →₀ ℕ`.
  obtain ⟨i, hi, hlt⟩ := Colex.lt_iff.1 h
  have hi : ∀ j, i < j → y j = x j := hi
  have hlt : y i < x i := hlt
  have hix : i ≤ x.support.max' hx := x.support.le_max' i (mem_support_iff.2 (by omega))
  rcases lt_trichotomy (y.support.max' hy) (x.support.max' hx) with hm | hm | hm
  · exact Or.inl hm
  · refine Or.inr ⟨hm, ?_⟩
    rw [hm]
    rcases hix.lt_or_eq with hix | hix
    · refine Or.inr ⟨hi _ hix, Colex.lt_iff.2 ⟨i, fun j hj ↦ ?_, ?_⟩⟩
      · change (y.erase _) j = (x.erase _) j
        by_cases hjm : j = x.support.max' hx
        · simp [hjm]
        · simp [erase_ne hjm, hi j hj]
      · change (y.erase _) i < (x.erase _) i
        simpa [erase_ne hix.ne] using hlt
    · exact Or.inl (hix ▸ hlt)
  · exfalso
    have hxm : x (y.support.max' hy) = 0 :=
      notMem_support_iff.1 fun h ↦ (x.support.le_max' _ h).not_gt hm
    exact mem_support_iff.1 (y.support.max'_mem hy) ((hi _ (hix.trans_lt hm)).trans hxm)

/-- When `α` has no infinite ascending chains, the colexicographic order on exponents of degree
at most `n` has no infinite ascending chains either. -/
theorem wellFoundedOn_setOf_degree_le_toColex_gt [WellFoundedGT α] (n : ℕ) :
    {a : α →₀ ℕ | a.degree ≤ n}.WellFoundedOn (fun a b ↦ toColex b < toColex a) := by
  induction n with
  | zero =>
    refine Set.Subsingleton.wellFoundedOn fun a ha b hb ↦ ?_
    simp only [Set.mem_ofPred_eq, nonpos_iff_eq_zero, degree_eq_zero_iff] at ha hb
    rw [ha, hb]
  | succ n ih =>
    rw [Set.wellFoundedOn_iff] at ih ⊢
    -- A nonzero exponent is recorded by its largest index `m`, the exponent at `m`, and the
    -- remaining exponent of smaller degree; colex ascents increase this triple lexicographically.
    let F : {x : α →₀ ℕ // x ≠ 0} → α × ℕ × (α →₀ ℕ) := fun x ↦
      (x.1.support.max' (support_nonempty_iff.2 x.2),
        x.1 (x.1.support.max' (support_nonempty_iff.2 x.2)),
        x.1.erase (x.1.support.max' (support_nonempty_iff.2 x.2)))
    have hbdd : WellFounded fun e e' : ℕ ↦ e' < e ∧ e ≤ n + 1 :=
      (wellFounded_lt.onFun (f := fun e : ℕ ↦ n + 1 - e)).mono fun e e' h ↦ by
        simp only [Function.onFun]; omega
    have hwf := InvImage.wf F ((wellFounded_gt (α := α)).prod_lex (hbdd.prod_lex ih))
    have hdeg (x : α →₀ ℕ) (m : α) (hm : m ∈ x.support) :
        (x.erase m).degree + 1 ≤ x.degree := by
      have h := congr_arg degree (single_add_erase m x)
      rw [map_add, degree_single] at h
      have := mem_support_iff.1 hm
      omega
    have hacc (y : {x : α →₀ ℕ // x ≠ 0}) :
        Acc (fun a b ↦ toColex b < toColex a ∧ a ∈ {a : α →₀ ℕ | a.degree ≤ n + 1} ∧
          b ∈ {a : α →₀ ℕ | a.degree ≤ n + 1}) y.1 := by
      induction y using hwf.induction with
      | _ y ihy =>
        refine ⟨_, fun x ⟨hxy, hx, hy⟩ ↦ ?_⟩
        have hx0 : x ≠ 0 := by rintro rfl; exact (bot_le.not_gt hxy : _)
        refine ihy ⟨x, hx0⟩ ?_
        simp only [Set.mem_ofPred_eq] at hx hy
        have hxm := x.support.max'_mem (support_nonempty_iff.2 hx0)
        have hym := y.1.support.max'_mem (support_nonempty_iff.2 y.2)
        rcases max'_lt_or_of_toColex_lt _ _ hxy with hm | ⟨hm, he | ⟨he, hr⟩⟩
        · exact Prod.Lex.left _ _ hm
        · simp only [InvImage, F, hm]
          refine Prod.Lex.right _ (Prod.Lex.left _ _ ⟨hm ▸ he, ?_⟩)
          exact (le_degree _ _).trans hx
        · have hdx := hdeg x _ hxm
          have hdy := hdeg y.1 _ hym
          rw [hm] at he hr hdy
          simp only [InvImage, F, hm, he]
          exact Prod.Lex.right _ (Prod.Lex.right _ ⟨hr, by simp only [Set.mem_ofPred_eq]; omega,
            by simp only [Set.mem_ofPred_eq]; omega⟩)
    refine ⟨fun y ↦ ⟨_, fun x ⟨hxy, hx, hy⟩ ↦ ?_⟩⟩
    have hx0 : x ≠ 0 := by rintro rfl; exact (bot_le.not_gt hxy : _)
    exact hacc ⟨x, hx0⟩

end Finsupp

end
