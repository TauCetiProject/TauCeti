/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.FieldTheory.Finite.FrobeniusFixed

/-!
# Splitting criterion over a finite field via Frobenius fixed points

Let `k` be a finite field of cardinality `q = |k|` and `K` an integral domain that is a
`k`-algebra. Because the elements of `K` fixed by `x ↦ x ^ q` are precisely the elements of `k`
(`TauCeti.FiniteField.pow_natCard_eq_self_iff_mem_range_algebraMap`), a polynomial `p : k[X]`
that splits in `K` splits already over `k` if every root of `p` in `K` satisfies `x ^ q = x`.
For nonzero `p`, this is an equivalence. Since a finite field is perfect, every polynomial over
`k` splits in any separably closed extension field `K`, so the splitting hypothesis on `K` is
automatic under `[Field K] [IsSepClosed K]`.

## Main results

* `TauCeti.FiniteField.splits_of_forall_aeval_eq_zero_pow_natCard_eq`: if `p : k[X]` splits in
  an integral domain `K` over `k` and every root `x : K` of `p` satisfies `x ^ |k| = x`, then `p`
  splits over `k`.
* `TauCeti.FiniteField.splits_iff_forall_aeval_eq_zero_pow_natCard_eq`: for nonzero `p : k[X]`
  splitting in an integral domain `K` over `k`, `p` splits over `k` if and only if every root
  `x : K` of `p` satisfies `x ^ |k| = x`.
* `TauCeti.FiniteField.splits_of_isSepClosed_of_forall_aeval_eq_zero_pow_natCard_eq`: the
  criterion in a separably closed extension field `K` of `k`.

## Provenance

Adapted from grh-lean
(https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207,
Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/LocalGL/Green/LabelCharacters.lean` (`New.splits_of_forall_root_pow_card_eq`).
-/

public section

open Polynomial

namespace TauCeti.FiniteField

/-- If `p : k[X]` splits in an integral domain `K` over a finite field `k` and every root `x : K`
of `p` satisfies `x ^ |k| = x`, then `p` splits over `k`. -/
theorem splits_of_forall_aeval_eq_zero_pow_natCard_eq {k K : Type*} [Field k] [Finite k]
    [CommRing K] [IsDomain K] [Algebra k K] {p : k[X]} (hp : (p.map (algebraMap k K)).Splits)
    (h_roots : ∀ x : K, aeval x p = 0 → x ^ Nat.card k = x) : p.Splits := by
  refine Splits.of_splits_map_of_injective (algebraMap k K).injective hp fun x hx ↦ ?_
  have hroot : aeval x p = 0 := (mem_aroots.mp hx).right
  exact (pow_natCard_eq_self_iff_mem_range_algebraMap x).mp (h_roots x hroot)

/-- For a nonzero polynomial `p : k[X]` over a finite field `k` that splits in an integral domain
`K` over `k`, `p` splits over `k` if and only if every root `x : K` of `p` satisfies
`x ^ |k| = x`. -/
theorem splits_iff_forall_aeval_eq_zero_pow_natCard_eq {k K : Type*} [Field k] [Finite k]
    [CommRing K] [IsDomain K] [Algebra k K] {p : k[X]} (hp0 : p ≠ 0)
    (hp : (p.map (algebraMap k K)).Splits) :
    p.Splits ↔ ∀ x : K, aeval x p = 0 → x ^ Nat.card k = x := by
  refine ⟨fun hs x hx ↦ ?_, splits_of_forall_aeval_eq_zero_pow_natCard_eq hp⟩
  have hmem : x ∈ (algebraMap k K).range := hs.mem_range_of_isRoot hp0
    (by simpa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using hx)
  exact (pow_natCard_eq_self_iff_mem_range_algebraMap x).mpr hmem

/-- A polynomial `p : k[X]` over a finite field `k` splits over `k` if every root of `p` in a
separably closed extension field `K` satisfies `x ^ |k| = x`. -/
theorem splits_of_isSepClosed_of_forall_aeval_eq_zero_pow_natCard_eq {k K : Type*} [Field k]
    [Finite k] [Field K] [Algebra k K] [IsSepClosed K] {p : k[X]}
    (h_roots : ∀ x : K, aeval x p = 0 → x ^ Nat.card k = x) : p.Splits := by
  refine splits_of_forall_aeval_eq_zero_pow_natCard_eq ?_ h_roots
  let _ : Fintype k := Fintype.ofFinite k
  by_cases hp0 : p = 0
  · simp [hp0]
  · refine UniqueFactorizationMonoid.induction_on_prime p (fun h ↦ (h rfl).elim)
      (fun u hu _ ↦ by
        rw [Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit hu),
          Polynomial.map_C]
        exact Splits.C _)
      (fun a q ha hq ih _ ↦ ?_) hp0
    rw [Polynomial.map_mul]
    exact Splits.mul
      (IsSepClosed.splits_codomain _ (PerfectField.separable_of_irreducible hq.irreducible))
      (ih ha)

end TauCeti.FiniteField
