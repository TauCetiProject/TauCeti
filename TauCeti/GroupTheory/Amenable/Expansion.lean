/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Additive.Expansion
public import TauCeti.GroupTheory.Amenable.Average

/-!
# Expansion in groups without Følner sets

If a group `G` has no Følner sets, some finite set `S ⊆ G` expands every finite subset of `G` by
a fixed factor `c > 1`:

```text
c · |F| ≤ |S • F|        for every finite F ⊆ G.
```

Indeed, the failure of the finite-test Følner condition gives a finite `K ⊆ G` and `ε > 0` such
that every finite nonempty `F` has some `g ∈ K` with `|gF △ F| ≥ ε |F|`. Since
`|gF △ F| = 2 |gF \ F|`, the set `S = {1} ∪ K` satisfies `|S • F| ≥ |F ∪ gF| ≥ (1 + ε/2) |F|`.
Iterating, a pointwise power of `S` expands every finite set by any prescribed natural factor
`k`, and Hall's marriage theorem turns expansion by `k` into an injection
`j : G × Fin k → G` with `j (x, i) = d * x` for `d` in a fixed finite set.

By the averaging criterion `TauCeti.Amenable.of_hasFoelnerSets`, a nonamenable group has no
Følner sets, for any group topology. For `k = 2` the injection exhibits two disjoint subsets of
`G`, each the image of `G` under finitely many left translations of pieces; this is the
combinatorial core of the proof that a nonamenable discrete group is paradoxical (the hard
direction of Tarski's alternative).

## Main results

* `TauCeti.exists_mul_card_le_card_smul_of_not_hasFoelnerSets`: a group without Følner sets has,
  for each natural `k`, a finite set `D` with `k · |F| ≤ |D • F|` for all finite `F`.
* `TauCeti.exists_injective_mul_of_not_hasFoelnerSets`: a group without Følner sets has, for each
  natural `k`, a finite set `D` and an injection `j : G × Fin k → G` with `j (x, i) = d * x`
  for some `d ∈ D`.
* `TauCeti.exists_injective_mul_of_not_amenable`: the same for a nonamenable topological group.

## References

* A. Garrido, *An introduction to amenable groups*, proof of Theorem 1.11 and Theorem 1.15.
* T. Ceccherini-Silberstein, R. Grigorchuk, P. de la Harpe, *Amenability and paradoxical
  decompositions for pseudogroups and for discrete metric spaces*, Theorems 7 and 35.
-/

public section

open Finset Function
open scoped Pointwise symmDiff

namespace TauCeti

variable {G : Type*} [Group G]

/-- A group without Følner sets has a finite set expanding every finite set by a factor `c > 1`.
The set is `{1} ∪ K` for a finite test set `K` that no finite set passes with tolerance `ε`, and
the factor is `1 + ε / 2`. -/
private theorem exists_one_lt_mul_card_le_card_smul_of_not_hasFoelnerSets [DecidableEq G]
    (h : ¬HasFoelnerSets G) :
    ∃ S : Finset G, ∃ c : ℝ, 1 < c ∧ ∀ F : Finset G, c * #F ≤ #(S • F) := by
  rw [hasFoelnerSets_iff] at h
  push Not at h
  obtain ⟨K, ε, hε, hK⟩ := h
  refine ⟨insert 1 K, 1 + ε / 2, by linarith, fun F => ?_⟩
  obtain rfl | hF := F.eq_empty_or_nonempty
  · simp
  obtain ⟨g, hg, hgF⟩ := hK F hF
  -- Both `F = 1 • F` and `g • F` lie in `({1} ∪ K) • F`.
  have hsub : g • F ∪ F ⊆ insert 1 K • F :=
    union_subset (smul_finset_subset_smul (mem_insert_of_mem hg))
      (by simpa using smul_finset_subset_smul (t := F) (mem_insert_self 1 K))
  have hcard : (#(g • F \ F) : ℝ) + #F ≤ #(insert 1 K • F) := by
    exact_mod_cast (card_sdiff_add_card _ _).trans_le (card_le_card hsub)
  have hsd : ((#((g • F) ∆ F) : ℕ) : ℝ) = 2 * #(g • F \ F) := by
    exact_mod_cast card_smul_finset_symmDiff g F
  rw [hsd] at hgF
  linarith

/-- A group without Følner sets has, for every natural number `k`, a finite set `D` expanding
every finite set by the factor `k`: `k · |F| ≤ |D • F|`. -/
theorem exists_mul_card_le_card_smul_of_not_hasFoelnerSets [DecidableEq G]
    (h : ¬HasFoelnerSets G) (k : ℕ) : ∃ D : Finset G, ∀ F : Finset G, k * #F ≤ #(D • F) := by
  obtain ⟨S, c, hc, hS⟩ := exists_one_lt_mul_card_le_card_smul_of_not_hasFoelnerSets h
  -- Iterate the expansion by `c > 1` until the factor `c ^ n` exceeds `k`.
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (k : ℝ) hc
  refine ⟨S ^ n, fun F => ?_⟩
  have := pow_mul_card_le_card_pow_smul (zero_le_one.trans hc.le) hS n F
  exact_mod_cast (mul_le_mul_of_nonneg_right hn.le (Nat.cast_nonneg _)).trans this

/-- A group without Følner sets has, for every natural number `k`, a finite set `D` and an
injective map `j : G × Fin k → G` such that each `j (x, i)` is `d * x` for some `d ∈ D`. -/
theorem exists_injective_mul_of_not_hasFoelnerSets (h : ¬HasFoelnerSets G) (k : ℕ) :
    ∃ D : Finset G, ∃ j : G × Fin k → G, Injective j ∧ ∀ p, ∃ d ∈ D, d * p.1 = j p := by
  classical
  obtain ⟨D, hD⟩ := exists_mul_card_le_card_smul_of_not_hasFoelnerSets h k
  simpa only [smul_eq_mul] using ⟨D, exists_injective_of_mul_card_le_card_smul hD⟩

/-- A nonamenable topological group has, for every natural number `k`, a finite set `D` and an
injective map `j : G × Fin k → G` such that each `j (x, i)` is `d * x` for some `d ∈ D`. -/
theorem exists_injective_mul_of_not_amenable [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ¬Amenable G) (k : ℕ) :
    ∃ D : Finset G, ∃ j : G × Fin k → G, Injective j ∧ ∀ p, ∃ d ∈ D, d * p.1 = j p :=
  exists_injective_mul_of_not_hasFoelnerSets (mt Amenable.of_hasFoelnerSets h) k

end TauCeti
