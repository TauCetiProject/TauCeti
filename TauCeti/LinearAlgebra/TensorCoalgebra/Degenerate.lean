/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.CoalgHom

/-!
# Tensor words containing a distinguished element

The degenerate words associated to an element `e` are the span of the nonempty pure tensor
words with at least one letter equal to `e`. For a unit, these are the words discarded by
normalization of the bar construction. A coalgebra morphism preserves this submodule if its
linear component preserves the distinguished element and its higher Taylor components vanish
on words containing it.

A Taylor map vanishing on higher degenerate words agrees there with its linear component
composed with the letter projection. These two facts let one prove closure of normalized
Taylor maps under coalgebra composition without choosing a formula indexed by partitions.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

open scoped TensorProduct

namespace TauCeti.ReducedTensorWords

universe uR uM uN

variable (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The span of nonempty pure tensor words containing the distinguished element `e`.
The one-letter word `e` is included. -/
noncomputable def degenerateWords (e : M) : Submodule R (ReducedTensorWords R M) :=
  Submodule.span R {z | ∃ (n : {n : ℕ // 0 < n}) (x : Fin n.1 → M),
    (∃ i, x i = e) ∧ z = of R M n (PiTensorProduct.tprod R x)}

variable {R M}

/-- A submodule contains all degenerate words exactly when it contains each pure tensor word
with a distinguished letter. This is the universal property of their span. -/
@[simp]
theorem degenerateWords_le_iff {e : M} {S : Submodule R (ReducedTensorWords R M)} :
    degenerateWords R M e ≤ S ↔ ∀ (n : {n : ℕ // 0 < n}) (x : Fin n.1 → M),
      (∃ i, x i = e) → of R M n (PiTensorProduct.tprod R x) ∈ S := by
  rw [degenerateWords, Submodule.span_le]
  constructor
  · intro h n x hx
    exact h ⟨n, x, hx, rfl⟩
  · intro h z hz
    obtain ⟨n, x, hx, rfl⟩ := hz
    exact h n x hx

/-- A pure tensor word containing `e` is degenerate. -/
theorem of_tprod_mem_degenerateWords {e : M} (n : {n : ℕ // 0 < n})
    (x : Fin n.1 → M) (hx : ∃ i, x i = e) :
    of R M n (PiTensorProduct.tprod R x) ∈ degenerateWords R M e :=
  Submodule.subset_span ⟨n, x, hx, rfl⟩

/-- A block containing `e` is degenerate. -/
theorem subword_mem_degenerateWords {e : M} {n : ℕ} (x : Fin n → M) {a b : ℕ}
    (hab : a + b ≤ n) (hx : ∃ i : Fin n, a ≤ i.1 ∧ i.1 < a + b ∧ x i = e) :
    subword R x a b ∈ degenerateWords R M e := by
  obtain ⟨i, hai, hib, hi⟩ := hx
  have hb : 0 < b := by omega
  rw [subword_eq_of_tprod R x hb hab]
  apply of_tprod_mem_degenerateWords
  have hj : i.1 - a < b := by omega
  refine ⟨⟨i.1 - a, hj⟩, ?_⟩
  convert hi using 1
  congr 1
  apply Fin.ext
  simp only [Nat.add_sub_of_le hai]

/-- The one-letter word `e` is degenerate. -/
theorem ofLetter_mem_degenerateWords (e : M) :
    ofLetter R M e ∈ degenerateWords R M e := by
  rw [← subword_one R M (fun _ : Fin 1 ↦ e) Nat.one_pos]
  exact subword_mem_degenerateWords _ (by omega) ⟨0, by omega, by omega, rfl⟩

/-- Prepending an arbitrary letter preserves degeneracy. -/
theorem prepend_mem_degenerateWords {e : M} (a : M) {z : ReducedTensorWords R M}
    (hz : z ∈ degenerateWords R M e) :
    prepend R M a z ∈ degenerateWords R M e := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨n, x, ⟨i, hi⟩, rfl⟩ := hz
    rw [prepend_of_tprod]
    exact of_tprod_mem_degenerateWords _ _ ⟨i.succ, by simpa using hi⟩
  | zero => simp
  | add x y _ _ hx hy => simpa using (degenerateWords R M e).add_mem hx hy
  | smul c x _ hx => simpa using (degenerateWords R M e).smul_mem c hx

/-- Prepending the distinguished element makes every reduced tensor word degenerate. -/
theorem prepend_distinguished_mem_degenerateWords (e : M) (z : ReducedTensorWords R M) :
    prepend R M e z ∈ degenerateWords R M e := by
  have hle : (⊤ : Submodule R (ReducedTensorWords R M)) ≤
      (degenerateWords R M e).comap (prepend R M e) := by
    rw [← iSup_range_of R M, iSup_le_iff]
    intro n
    rw [LinearMap.range_le_iff_comap]
    apply top_unique
    intro t ht
    clear ht
    induction t using PiTensorProduct.induction_on with
    | smul_tprod c x =>
      simp only [map_smul, Submodule.mem_comap]
      apply Submodule.smul_mem
      rw [prepend_of_tprod]
      exact of_tprod_mem_degenerateWords _ _ ⟨0, rfl⟩
    | add t u ht hu => simpa using Submodule.add_mem _ ht hu
  exact hle (Submodule.mem_top)

variable {N : Type uN} [AddCommMonoid N] [Module R N]

/-- On degenerate words, a Taylor map that vanishes in higher arities is its linear component
composed with the letter projection. -/
theorem apply_eq_comp_letter_of_mem_degenerateWords
    (f : ReducedTensorWords R M →ₗ[R] N) {e : M}
    (hf : ∀ (n : {n : ℕ // 0 < n}), n.1 ≠ 1 → ∀ x : Fin n.1 → M,
      (∃ i, x i = e) → f (of R M n (PiTensorProduct.tprod R x)) = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ degenerateWords R M e) :
    f z = f (ofLetter R M (letter R M z)) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨n, x, hx, rfl⟩ := hz
    by_cases hn : n.1 = 1
    · obtain ⟨k, hk⟩ := n
      simp only at hn
      subst k
      rw [of_tprod_eq_subword R hk, subword_one R M x (by omega), letter_ofLetter]
    · rw [hf n hn x hx, of_tprod_eq_subword R n.2,
        letter_subword_of_ne_one R M x 0 hn, map_zero, map_zero]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx => simp only [map_smul, hx]

/-- The Taylor expansion of a block containing the distinguished element is degenerate. -/
theorem coalgHom_subword_mem_degenerateWords (f : ReducedTensorWords R M →ₗ[R] N)
    {e : M} {e' : N} (he : f (ofLetter R M e) = e')
    (hf : ∀ (n : {n : ℕ // 0 < n}), n.1 ≠ 1 → ∀ x : Fin n.1 → M,
      (∃ i, x i = e) → f (of R M n (PiTensorProduct.tprod R x)) = 0)
    {n : ℕ} (x : Fin n → M) {a b : ℕ} (hab : a + b ≤ n)
    (hx : ∃ i : Fin n, a ≤ i.1 ∧ i.1 < a + b ∧ x i = e) :
    coalgHom R f (subword R x a b) ∈ degenerateWords R N e' := by
  suffices hblock : ∀ b (a n : ℕ) (x : Fin n → M), a + b ≤ n →
      (∃ i : Fin n, a ≤ i.1 ∧ i.1 < a + b ∧ x i = e) →
      coalgHom R f (subword R x a b) ∈ degenerateWords R N e' from hblock b a n x hab hx
  intro b
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro a n x hab hx
    obtain ⟨i, hai, hib, hi⟩ := hx
    have hb : 0 < b := by omega
    have hvanish : ∀ c, 1 < c → a + c ≤ n → i.1 < a + c →
        f (subword R x a c) = 0 := by
      intro c hc hac hic
      rw [apply_eq_comp_letter_of_mem_degenerateWords f hf
        (subword_mem_degenerateWords x hac ⟨i, hai, hic, hi⟩),
        letter_subword_of_ne_one R M x a (by omega), map_zero, map_zero]
    -- The recursion separates the single-letter output from the proper cuts.
    rw [coalgHom_subword]
    apply Submodule.add_mem
    · by_cases hb1 : b = 1
      · have hie : i.1 = a := by omega
        have hsingle : subword R x a b = ofLetter R M e := by
          rw [hb1, subword_one R M x (by omega)]
          congr 1
          convert hi using 1
          congr 1
          exact Fin.ext hie.symm
        rw [hsingle, he]
        exact ofLetter_mem_degenerateWords e'
      · rw [hvanish b (by omega) hab hib, map_zero]
        exact Submodule.zero_mem _
    · apply Submodule.sum_mem
      intro d hd
      have hdlt : d < b := Finset.mem_range.mp hd
      -- A distinguished letter in the first block survives only in a singleton block.
      by_cases hid : i.1 < a + d
      · by_cases hd1 : d = 1
        · have hie : i.1 = a := by omega
          rw [hd1, subword_one R M x (by omega)]
          have hea : x ⟨a, by omega⟩ = e := by
            convert hi using 1
            congr 1
            exact Fin.ext hie.symm
          rw [hea, he]
          exact prepend_distinguished_mem_degenerateWords _ _
        · rw [hvanish d (by omega) (by omega) hid, LinearMap.map_zero]
          exact Submodule.zero_mem _
      · by_cases hd0 : d = 0
        · simp only [hd0, subword_length_zero, map_zero, LinearMap.zero_apply,
            Submodule.zero_mem]
        -- Otherwise the distinguished letter lies in the shorter tail.
        · apply prepend_mem_degenerateWords
          apply ih (b - d) (by omega) (a + d) n x (by omega)
          exact ⟨i, by omega, by omega, hi⟩

/-- A coalgebra Taylor expansion preserves degenerate words when its linear component carries
`e` to `e'` and every higher component vanishes on words containing `e`. -/
theorem coalgHom_mem_degenerateWords (f : ReducedTensorWords R M →ₗ[R] N)
    {e : M} {e' : N} (he : f (ofLetter R M e) = e')
    (hf : ∀ (n : {n : ℕ // 0 < n}), n.1 ≠ 1 → ∀ x : Fin n.1 → M,
      (∃ i, x i = e) → f (of R M n (PiTensorProduct.tprod R x)) = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ degenerateWords R M e) :
    coalgHom R f z ∈ degenerateWords R N e' := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨n, x, hx, rfl⟩ := hz
    rw [of_tprod_eq_subword R n.2]
    apply coalgHom_subword_mem_degenerateWords f he hf x (by omega)
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, by omega, by simp, hi⟩
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

end TauCeti.ReducedTensorWords
