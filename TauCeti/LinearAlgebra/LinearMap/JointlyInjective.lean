/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Jointly injective finite subfamilies of a detecting family of linear maps

Let `H` be a finite-dimensional vector space over a division ring `k` and `f i : H →ₗ[k] M i` a
family of linear maps. Call a set `P` of indices *detecting* if every nonzero `c : H` satisfies
`f i c ≠ 0` for infinitely many `i ∈ P`. Then, for every finite set `B` of indices to avoid and
every `q ≥ dim H`, there is a set `Q ⊆ P` of exactly `q` indices outside `B` on which the joint map
`c ↦ (f i c)_{i ∈ Q}` is injective, provided `P` is infinite (which detection only forces when
`H ≠ 0`).

The indices are chosen one at a time: a nonzero vector of the current joint kernel is detected by
an index that has not been used or excluded, and adding that index cuts the kernel down strictly,
so at most `dim H` indices are needed; the rest of `Q` is padding from `P`.

This is the linear algebra in the selection of Taylor–Wiles auxiliary primes, where `H` is a dual
Selmer group, the indices are the primes of a number field, `f` are the localization maps and
detection comes from the Chebotarev density theorem.

## Main results

* `LinearMap.exists_finset_card_eq_injective`: a detecting infinite set of indices contains, outside
  any finite set, exactly `q ≥ dim H` indices whose joint map is injective.

## References

* P. B. Allen, F. Calegari, A. Caraiani, T. Gee, D. Helm, B. V. Le Hung, J. Newton, P. Scholze,
  R. Taylor and J. A. Thorne, *Potential automorphy over CM fields*, Ann. of Math. 197 (2023),
  897–1113, proof of Lemma 6.2.32.
-/

public section

namespace LinearMap

variable {k H ι : Type*} [DivisionRing k] [AddCommGroup H] [Module k H] [FiniteDimensional k H]
  {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]

/-- Starting from `Q₀ ⊆ P` disjoint from `B` whose joint kernel has dimension at most `n`, at most
`n` further detecting indices from `P` outside `B` make the joint kernel zero. -/
private theorem exists_finset_superset_iInf_ker_eq_bot (f : ∀ i, H →ₗ[k] M i) {P : Set ι}
    (hP : ∀ c : H, c ≠ 0 → {i ∈ P | f i c ≠ 0}.Infinite) (B : Finset ι) (n : ℕ) :
    ∀ Q₀ : Finset ι, ↑Q₀ ⊆ P → Disjoint Q₀ B →
      Module.finrank k ↥(⨅ i ∈ Q₀, ker (f i)) ≤ n →
      ∃ Q : Finset ι, Q.card ≤ Q₀.card + n ∧ ↑Q ⊆ P ∧ Disjoint Q B ∧
        ⨅ i ∈ Q, ker (f i) = ⊥ := by
  classical
  induction n with
  | zero =>
    intro Q₀ hQP hQB hn
    exact ⟨Q₀, by simp, hQP, hQB, Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hn)⟩
  | succ n ih =>
    intro Q₀ hQP hQB hn
    by_cases hbot : ⨅ i ∈ Q₀, ker (f i) = ⊥
    · exact ⟨Q₀, by omega, hQP, hQB, hbot⟩
    -- a nonzero vector of the joint kernel is detected by an index outside `B ∪ Q₀`
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨i, ⟨hiP, hic⟩, hiBQ⟩ := ((hP c hc0).sdiff (B ∪ Q₀).finite_toSet).nonempty
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hiBQ
    have hlt : ⨅ j ∈ insert i Q₀, ker (f j) < ⨅ j ∈ Q₀, ker (f j) := by
      refine lt_of_le_of_ne (biInf_mono fun j hj ↦ Finset.mem_insert_of_mem hj) fun h ↦ hic ?_
      rw [← h] at hc
      simp only [Submodule.mem_iInf, mem_ker] at hc
      exact hc i (Finset.mem_insert_self i Q₀)
    obtain ⟨Q, hcard, hQP', hQB', hQ⟩ := ih (insert i Q₀)
      (by rw [Finset.coe_insert]; exact Set.insert_subset hiP hQP)
      (Finset.disjoint_insert_left.mpr ⟨hiBQ.1, hQB⟩)
      (by have := Submodule.finrank_lt_finrank_of_lt hlt; omega)
    rw [Finset.card_insert_of_notMem hiBQ.2] at hcard
    exact ⟨Q, by omega, hQP', hQB', hQ⟩

/-- **Jointly injective subfamilies of a detecting family.** Let `f i : H →ₗ[k] M i` be linear maps
out of a finite-dimensional space and `P` an infinite set of indices such that every nonzero
`c : H` has `f i c ≠ 0` for infinitely many `i ∈ P`. Then for every finite set `B` and every
`q ≥ dim H` there are exactly `q` indices in `P` outside `B` whose joint map
`c ↦ (f i c)_{i ∈ Q}` is injective. -/
theorem exists_finset_card_eq_injective (f : ∀ i, H →ₗ[k] M i) {P : Set ι} (hP : P.Infinite)
    (hdetect : ∀ c : H, c ≠ 0 → {i ∈ P | f i c ≠ 0}.Infinite) (B : Finset ι) {q : ℕ}
    (hq : Module.finrank k H ≤ q) :
    ∃ Q : Finset ι, Q.card = q ∧ Disjoint Q B ∧ ↑Q ⊆ P ∧
      Function.Injective fun c : H ↦ fun i : Q ↦ f i c := by
  classical
  obtain ⟨Q₀, hcard, hQP, hQB, hQ⟩ :=
    exists_finset_superset_iInf_ker_eq_bot f hdetect B (Module.finrank k H) ∅ (by simp) (by simp)
      (Submodule.finrank_le _)
  -- pad with `q - #Q₀` further indices of `P` outside `B ∪ Q₀`
  obtain ⟨R, hRP, hRcard⟩ :=
    (hP.sdiff (B ∪ Q₀).finite_toSet).exists_subset_card_eq (q - Q₀.card)
  have hR : Disjoint R (B ∪ Q₀) :=
    Finset.disjoint_left.mpr fun i hi ↦ by simpa using (hRP hi).2
  rw [Finset.disjoint_union_right] at hR
  refine ⟨Q₀ ∪ R, ?_, Finset.disjoint_union_left.mpr ⟨hQB, hR.1⟩, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hR.2.symm, hRcard]
    rw [Finset.card_empty, zero_add] at hcard
    omega
  · rw [Finset.coe_union]
    exact Set.union_subset hQP fun i hi ↦ (hRP hi).1
  · intro c c' h
    rw [← sub_eq_zero, ← Submodule.mem_bot k, ← hQ]
    simp only [Submodule.mem_iInf, mem_ker, map_sub, sub_eq_zero]
    exact fun i hi ↦ congrFun h ⟨i, Finset.mem_union_left R hi⟩

end LinearMap
