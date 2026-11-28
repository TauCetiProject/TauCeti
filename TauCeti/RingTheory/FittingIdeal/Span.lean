/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.RingTheory.FittingIdeal.Basic

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Prod

/-!
# Minors ideals and generating families

Let `F` be a module over a commutative ring `R`. This file relates the ideals of minors
`Submodule.minorsIdeal` to explicit generating families:

* Adjoining a finite family of `m` generators to a submodule `N` shifts its minors ideals by at
  most `m`: `(N ⊔ span R (range v)).minorsIdeal (p + Nat.card ι) ≤ N.minorsIdeal p`
  (`Submodule.minorsIdeal_sup_span_range_add_le`), proved directly from
  `Submodule.minorsIdeal_prod_top` and `Submodule.minorsIdeal_map_le` via the surjection
  `N × (ι → R) → N ⊔ span R (range v)`. Specializing to a single generator gives
  `(N ⊔ R ∙ x).minorsIdeal (p + 1) ≤ N.minorsIdeal p`
  (`Submodule.minorsIdeal_sup_span_singleton_succ_le`).
* Taking `N = ⊥` shows that if a submodule is contained in the span of fewer than `p` vectors, its
  `p × p` minors ideal vanishes (`Submodule.minorsIdeal_span_range_eq_bot_of_lt`,
  `Submodule.minorsIdeal_eq_bot_of_le_span_range`).
* Adjoining a generator `x` costs a factor from the colon ideal `N : x`, without shift:
  `N.colon {x} * (N ⊔ R ∙ x).minorsIdeal p ≤ N.minorsIdeal p`
  (`Submodule.colon_mul_minorsIdeal_sup_span_singleton_le`), and generators adjoined one at a
  time cost the product of the successive colon ideals
  (`Submodule.prod_colon_mul_minorsIdeal_sup_span_image_le`).

These span-cardinality and single-generator shift bounds control `Module.Grassmannian.rankLocus` on
bounded-rank quotients and across flag steps, enabling the full-flag reduction of Schubert rank
ideals to their jump conditions (`Module.Grassmannian.iSup_rankLocus_flag_succ_eq`).

## Main results

* `Submodule.minorsIdeal_sup_span_range_add_le`: adjoining a finite family of `m` generators shifts
  the minors ideals by at most `m`.
* `Submodule.minorsIdeal_sup_span_singleton_succ_le`: adjoining one generator shifts the minors
  ideals by at most one.
* `Submodule.colon_mul_minorsIdeal_sup_span_singleton_le`: the colon ideal `N : x` multiplies the
  minors of `N ⊔ R ∙ x` into those of `N`.
* `Submodule.prod_colon_mul_minorsIdeal_sup_span_image_le`: adjoining generators `w j` one at a
  time along a linear order, the product of the successive colon ideals multiplies the minors of
  the result into those of `N`.
* `Submodule.minorsIdeal_span_range_eq_bot_of_lt`: the `p × p` minors ideal of the span of fewer
  than `p` vectors vanishes.
* `Submodule.minorsIdeal_eq_bot_of_le_span_range`: the `p × p` minors ideal of a submodule
  contained in the span of fewer than `p` vectors vanishes.

## References

* [Stacks Project, Tag 07Z6](https://stacks.math.columbia.edu/tag/07Z6)
-/

public section

open Module

namespace Submodule

variable {R F : Type*} [CommRing R] [AddCommGroup F] [Module R F]

/-- Adjoining a finite family `v : ι → F` of generators to a submodule `N` shifts its minors ideals
by at most `Nat.card ι`. -/
theorem minorsIdeal_sup_span_range_add_le {ι : Type*} [Finite ι] (N : Submodule R F) (v : ι → F)
    (p : ℕ) :
    (N ⊔ Submodule.span R (Set.range v)).minorsIdeal (p + Nat.card ι) ≤ N.minorsIdeal p := by
  nontriviality R
  cases nonempty_fintype ι
  have hmap : (N.prod (⊤ : Submodule R (ι → R))).map
      (LinearMap.id.coprod (Fintype.linearCombination R v)) =
      N ⊔ Submodule.span R (Set.range v) := by
    rw [LinearMap.map_coprod_prod, Submodule.map_id, Submodule.map_top,
      Fintype.range_linearCombination]
  rw [← hmap, Nat.card_eq_fintype_card, ← Module.finrank_fintype_fun_eq_card R]
  exact (Submodule.minorsIdeal_map_le _ _ _).trans_eq (Submodule.minorsIdeal_prod_top N p)

/-- Adjoining a single generator `x` to a submodule `N` shifts its minors ideals by at most one:
every `(p + 1) × (p + 1)` minor of `N ⊔ R ∙ x` lies in `N.minorsIdeal p`. -/
theorem minorsIdeal_sup_span_singleton_succ_le (N : Submodule R F) (x : F) (p : ℕ) :
    (N ⊔ R ∙ x).minorsIdeal (p + 1) ≤ N.minorsIdeal p := by
  simpa [Set.range_const] using minorsIdeal_sup_span_range_add_le N (fun _ : Unit ↦ x) p

/-- The `p × p` minors ideal of the span of fewer than `p` vectors vanishes. -/
theorem minorsIdeal_span_range_eq_bot_of_lt {ι : Type*} [Finite ι] {p : ℕ}
    (h : Nat.card ι < p) (v : ι → F) :
    (Submodule.span R (Set.range v)).minorsIdeal p = ⊥ := by
  obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt h)
  have hp : (q + 1) + Nat.card ι = p := by omega
  refine le_bot_iff.mp ?_
  calc (Submodule.span R (Set.range v)).minorsIdeal p
      = (⊥ ⊔ Submodule.span R (Set.range v)).minorsIdeal ((q + 1) + Nat.card ι) := by
          rw [bot_sup_eq, hp]
    _ ≤ (⊥ : Submodule R F).minorsIdeal (q + 1) := minorsIdeal_sup_span_range_add_le ⊥ v (q + 1)
    _ = ⊥ := minorsIdeal_bot q

/-- If a submodule `N` is contained in the span of fewer than `p` vectors, its `p × p` minors ideal
vanishes. -/
theorem minorsIdeal_eq_bot_of_le_span_range {ι : Type*} [Finite ι] {N : Submodule R F} {p : ℕ}
    {v : ι → F} (hN : N ≤ Submodule.span R (Set.range v)) (hp : Nat.card ι < p) :
    N.minorsIdeal p = ⊥ :=
  le_bot_iff.mp <| (minorsIdeal_mono hN p).trans_eq (minorsIdeal_span_range_eq_bot_of_lt hp v)

/-- A determinant `det (f j (w i))` whose rows lie in `N` except for rows equal to `x` lies in the
colon ideal `N.minorsIdeal p : a` as soon as `a • x ∈ N`. -/
private theorem det_mem_colon_of_mem_insert {N : Submodule R F} {x : F} {a : R} (hax : a • x ∈ N)
    {p : ℕ} (f : Fin p → Module.Dual R F) {w : Fin p → F} (hw : ∀ i, w i ∈ insert x (N : Set F)) :
    (Matrix.of fun i j ↦ f j (w i)).det ∈ (N.minorsIdeal p).colon {a} := by
  rw [mem_colon_singleton, smul_eq_mul, mul_comm]
  by_cases hx : ∃ i₀, w i₀ = x
  · obtain ⟨i₀, hi₀⟩ := hx
    by_cases h' : ∃ i, i ≠ i₀ ∧ w i = x
    · -- Two rows equal to `x` make the determinant vanish.
      obtain ⟨i, hi, hwi⟩ := h'
      rw [Matrix.det_zero_of_row_eq hi (by ext j; simp [hwi, hi₀]), mul_zero]
      exact zero_mem _
    · -- Multiplying the row `x` by `a` gives a matrix with all its rows in `N`.
      push Not at h'
      set M := Matrix.of fun i j ↦ f j (w i)
      have hrow : (Matrix.of fun i j ↦ f j (Function.update w i₀ (a • x) i)) =
          M.updateRow i₀ (a • M i₀) := by
        ext i j
        rcases eq_or_ne i i₀ with rfl | hi
        · simp [M, hi₀]
        · simp [M, hi]
      rw [← Matrix.updateRow_eq_self M i₀, ← Matrix.det_updateRow_smul, ← hrow]
      refine det_mem_minorsIdeal f fun i ↦ ?_
      rcases eq_or_ne i i₀ with rfl | hi
      · simpa using hax
      · simpa [hi] using (hw i).resolve_left (h' i hi)
  · -- All rows lie in `N`.
    push Not at hx
    exact Ideal.mul_mem_left _ _ (det_mem_minorsIdeal f fun i ↦ (hw i).resolve_left (hx i))

/-- **Adjoining one generator.** The colon ideal `N : x` multiplies the minors of `N ⊔ R ∙ x` into
those of `N`. -/
theorem colon_mul_minorsIdeal_sup_span_singleton_le (N : Submodule R F) (x : F) (p : ℕ) :
    N.colon {x} * (N ⊔ R ∙ x).minorsIdeal p ≤ N.minorsIdeal p := by
  -- By multilinearity, a minor of `N ⊔ R ∙ x` is a combination of minors whose rows lie in `N` or
  -- equal `x`; two rows equal to `x` give a vanishing determinant, and an element of `N : x`
  -- turns a single such row into a row of `N`.
  refine Submodule.mul_le.2 fun a ha d hd ↦ ?_
  suffices h : (N ⊔ R ∙ x).minorsIdeal p ≤ (N.minorsIdeal p).colon {a} by
    simpa [smul_eq_mul, mul_comm] using mem_colon_singleton.1 (h hd)
  have hspan : N ⊔ R ∙ x = span R (insert x (N : Set F)) := by
    rw [span_insert, span_eq, sup_comm]
  exact minorsIdeal_le_iff.2 fun f v hv ↦ TauCeti.det_mem_of_mem_span f (fun i ↦ hspan ▸ hv i)
    fun _ hw ↦ det_mem_colon_of_mem_insert (mem_colon_singleton.1 ha) f hw

/-- **Adjoining generators in a triangle.** Let `I` be a finite subset of a linear order and `w` a
family of vectors. Adjoin the `w j`, `j ∈ I`, to `N` one at a time in increasing order of `j`: the
product over `j ∈ I` of the colon ideals at `w j` of the submodules reached before `w j` multiplies
the minors of `N ⊔ span R (w '' I)` into those of `N`. -/
theorem prod_colon_mul_minorsIdeal_sup_span_image_le {J : Type*} [LinearOrder J]
    (N : Submodule R F) (w : J → F) (I : Finset J) (p : ℕ) :
    (∏ j ∈ I, (N ⊔ span R (w '' {i | i ∈ I ∧ i < j})).colon {w j}) *
        (N ⊔ span R (w '' I)).minorsIdeal p ≤ N.minorsIdeal p := by
  induction I using Finset.induction_on_max with
  | empty => simp
  | insert a s has ih =>
    have ha : a ∉ s := fun h ↦ lt_irrefl a (has a h)
    have hlt_a : {i | i ∈ insert a s ∧ i < a} = (s : Set J) := by
      ext i
      simp only [Finset.mem_insert, Set.mem_ofPred_eq, Finset.mem_coe]
      exact ⟨fun ⟨h, hi⟩ ↦ h.resolve_left (ne_of_lt hi), fun h ↦ ⟨Or.inr h, has i h⟩⟩
    have hlt (j : J) (hj : j ∈ s) : {i | i ∈ insert a s ∧ i < j} = {i | i ∈ s ∧ i < j} := by
      ext i
      simp only [Finset.mem_insert, Set.mem_ofPred_eq]
      refine ⟨fun ⟨h, hi⟩ ↦ ⟨h.resolve_left ?_, hi⟩, fun ⟨h, hi⟩ ↦ ⟨Or.inr h, hi⟩⟩
      rintro rfl
      exact lt_asymm hi (has j hj)
    have hsup : N ⊔ span R (w '' ↑(insert a s)) = (N ⊔ span R (w '' s)) ⊔ R ∙ w a := by
      rw [Finset.coe_insert, Set.image_insert_eq, span_insert, sup_comm (R ∙ w a), sup_assoc]
    rw [Finset.prod_insert ha, hlt_a, Finset.prod_congr rfl fun j hj ↦ by rw [hlt j hj], hsup,
      mul_comm ((N ⊔ span R (w '' s)).colon {w a}), mul_assoc]
    exact (Ideal.mul_mono_right (colon_mul_minorsIdeal_sup_span_singleton_le _ _ p)).trans ih

end Submodule
