/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import TauCeti.Algebra.Module.Torsion.Basic

/-!
# The exponents of the cyclic factors of a finite abelian `p`-group

A finite abelian `p`-group is a product `∏ᵢ ℤ/p^{kᵢ}` of cyclic groups
(`AddCommGroup.equiv_directSum_zmod_of_finite`). The decomposition itself is not unique, but the
exponents are: for every `m ≥ 1` the number of factors of order `p^m` is an invariant of the
group. This is the uniqueness half of the structure theorem, and it is what makes the exponents of
a decomposition usable as invariants, for instance in the classification of finite quadratic
forms, where an orthogonal sum of cyclic forms is only determined up to the order of its
summands.

The proof counts torsion. The `p^j`-torsion subgroup of `ℤ/p^k` has `p^{min(k, j)}` elements, so
the `p^j`-torsion subgroup of `∏ᵢ ℤ/p^{kᵢ}` has `p^{∑ᵢ min(kᵢ, j)}` elements. The differences
`∑ᵢ min(kᵢ, j + 1) - ∑ᵢ min(kᵢ, j)` count the factors with `kᵢ > j`, and hence the factors with
`kᵢ = m` for every `m ≥ 1`. Factors with `kᵢ = 0` are trivial and are not counted.

## Main results

* `TauCeti.AddCommGroup.natCard_torsionBy_pi_zmod_pow`: the `p^j`-torsion subgroup of
  `∏ᵢ ℤ/p^{kᵢ}` has `p^{∑ᵢ min(kᵢ, j)}` elements.
* `TauCeti.AddCommGroup.card_filter_eq_of_addEquiv_pi_zmod_pow`: if `∏ᵢ ℤ/p^{kᵢ}` and
  `∏ⱼ ℤ/p^{lⱼ}` are isomorphic, they have the same number of factors of order `p^m` for every
  `m ≥ 1`.

## References

* S. Lang, *Algebra*, Chapter I, §8.
-/

public section

open Finset

namespace TauCeti.AddCommGroup

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ℕ}

/-- The `p^j`-torsion subgroup of `∏ᵢ ℤ/p^{kᵢ}` has `p^{∑ᵢ min(kᵢ, j)}` elements. -/
theorem natCard_torsionBy_pi_zmod_pow [NeZero p] (k : ι → ℕ) (j : ℕ) :
    Nat.card (AddSubgroup.torsionBy (∀ i, ZMod (p ^ k i)) ((p ^ j : ℕ) : ℤ)) =
      p ^ ∑ i, min (k i) j := by
  rw [Nat.card_congr (TauCeti.AddSubgroup.torsionByPiEquiv _ _).toEquiv, Nat.card_pi,
    ← prod_pow_eq_pow_sum]
  refine prod_congr rfl fun i _ ↦ ?_
  -- The `p^j`-torsion of a cyclic group is the kernel of multiplication by `p^j`.
  have hker : AddSubgroup.torsionBy (ZMod (p ^ k i)) ((p ^ j : ℕ) : ℤ) =
      (nsmulAddMonoidHom (p ^ j) : ZMod (p ^ k i) →+ ZMod (p ^ k i)).ker := by
    ext x
    rw [AddSubgroup.torsionBy.nsmul_iff, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
  rw [hker, IsAddCyclic.card_nsmulAddMonoidHom_ker, Nat.card_zmod]
  rcases le_total (k i) j with h | h
  · rw [min_eq_left h, Nat.gcd_eq_left (Nat.pow_dvd_pow p h)]
  · rw [min_eq_right h, Nat.gcd_eq_right (Nat.pow_dvd_pow p h)]

/-- The sum `∑ᵢ min(kᵢ, j + 1)` exceeds `∑ᵢ min(kᵢ, j)` by the number of `i` with `kᵢ > j`. -/
private theorem sum_min_succ (k : ι → ℕ) (j : ℕ) :
    ∑ i, min (k i) (j + 1) = ∑ i, min (k i) j + #{i | j < k i} := by
  rw [card_filter, ← sum_add_distrib]
  exact sum_congr rfl fun i _ ↦ by split_ifs <;> omega

/-- For `m ≥ 1`, the `i` with `kᵢ > m - 1` are those with `kᵢ = m` and those with `kᵢ > m`. -/
private theorem card_filter_pred_lt {m : ℕ} (hm : m ≠ 0) (k : ι → ℕ) :
    #{i | m - 1 < k i} = #{i | k i = m} + #{i | m < k i} := by
  simp only [card_filter, ← sum_add_distrib]
  exact sum_congr rfl fun i _ ↦ by split_ifs <;> omega

/-- **The exponents of the cyclic factors of a finite abelian `p`-group are invariants.** If
`∏ᵢ ℤ/p^{kᵢ}` and `∏ⱼ ℤ/p^{lⱼ}` are isomorphic, then for every `m ≥ 1` they have the same number of
factors of order `p^m`. Factors of order `p^0 = 1` are trivial, and their number is not
determined. -/
theorem card_filter_eq_of_addEquiv_pi_zmod_pow (hp : 1 < p) {k : ι → ℕ} {l : κ → ℕ}
    (e : (∀ i, ZMod (p ^ k i)) ≃+ ∀ j, ZMod (p ^ l j)) {m : ℕ} (hm : m ≠ 0) :
    #{i | k i = m} = #{j | l j = m} := by
  have : NeZero p := ⟨by omega⟩
  -- The torsion counts give `∑ᵢ min(kᵢ, j) = ∑ⱼ min(lⱼ, j)` for every `j`.
  have hsum (j : ℕ) : ∑ i, min (k i) j = ∑ x, min (l x) j := by
    refine Nat.pow_right_injective hp ?_
    simp only [← natCard_torsionBy_pi_zmod_pow]
    exact Nat.card_congr (e.torsionByCongr _).toEquiv
  have hlt (j : ℕ) : #{i | j < k i} = #{x | j < l x} := by
    have h := hsum (j + 1)
    rw [sum_min_succ, sum_min_succ, hsum j] at h
    omega
  have h := hlt (m - 1)
  rw [card_filter_pred_lt hm, card_filter_pred_lt hm, hlt m] at h
  omega

end TauCeti.AddCommGroup
