/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# The stabilizer-chain order formula

Let a group `M` act on a type `α`, let `H` be a subgroup of `M`, and let `b : Fin k → α` be a
sequence of points. Write `H₍ᵢ₎ = H ⊓ fixingSubgroup M (b '' Set.Iio i)` for the pointwise
stabilizer in `H` of the points before `b i`, so that `H₍₀₎ = H`, and call the orbit
`H₍ᵢ₎ • b i` the `i`-th *basic orbit*. Each `H₍ᵢ₊₁₎` is the stabilizer of `b i` in `H₍ᵢ₎`, so
iterating the orbit–stabilizer theorem gives

  `Nat.card H = (∏ i, (orbit H₍ᵢ₎ (b i)).ncard) * Nat.card (H ⊓ fixingSubgroup M (Set.range b))`.

When the points form a *base*, that is the pointwise stabilizer of all of them in `H` is trivial,
the order of `H` is the product of the lengths of the basic orbits. This is the formula by which
the order of a permutation group is computed from a stabilizer chain.

Neither side needs a finiteness hypothesis: `Set.ncard` and `Nat.card` both take the junk value
`0` on infinite sets, and the identity holds with these values. For instance, for the shift
`x ↦ x + 1` generating a subgroup of `Equiv.Perm ℤ` and the base `0`, both sides are `0`.

For a `k`-transitive action and `k` distinct points, the basic orbits are as large as possible:
the `i`-th one is the complement of the first `i` points, of size `Nat.card α - i`.

## Main results

* `Subgroup.card_eq_ncard_orbit_mul_card_inf_stabilizer`: orbit–stabilizer for a subgroup `H`,
  with the stabilizer formed in the ambient group and intersected with `H`.
* `Subgroup.card_eq_prod_ncard_orbit_mul_card_inf_fixingSubgroup`: the stabilizer-chain order
  formula.
* `Subgroup.card_eq_prod_ncard_orbit_of_inf_fixingSubgroup_eq_bot`: the order of `H` is the
  product of the lengths of the basic orbits of a base.
* `Subgroup.orbit_inf_fixingSubgroup_image_Iio_eq_compl` and
  `Subgroup.ncard_orbit_inf_fixingSubgroup_image_Iio`: the basic orbits of `k` distinct points
  under a `k`-transitive subgroup.

## References

* J. D. Dixon and B. Mortimer, *Permutation Groups*, Graduate Texts in Mathematics 163,
  Springer, 1996, §1.4, Theorem 1.4A (the orbit–stabilizer step).
* Á. Seress, *Permutation Group Algorithms*, Cambridge Tracts in Mathematics 152, Cambridge
  University Press, 2003, §4.1 (bases, stabilizer chains and the order formula).
-/

public section

open MulAction

namespace Subgroup

variable {M α : Type*} [Group M] [MulAction M α]

/-- **Orbit–stabilizer for a subgroup.** The order of a subgroup `H` is the length of the orbit
of `x` under `H` times the order of the stabilizer of `x` in `H`, written as the intersection of
`H` with the stabilizer of `x` in the ambient group. No finiteness is assumed: when `H` is
infinite both sides are `0`. -/
theorem card_eq_ncard_orbit_mul_card_inf_stabilizer (H : Subgroup M) (x : α) :
    Nat.card H = (orbit H x).ncard * Nat.card ↥(H ⊓ stabilizer M x) := by
  rw [← index_stabilizer, ← stabilizer_subgroupOf, ← relIndex, inf_comm, relIndex_mul_card]

/-- **The stabilizer-chain order formula.** For a subgroup `H` and points `b 0, …, b (k - 1)`,
the order of `H` is the product of the lengths of the basic orbits, the orbits of `b i` under
the pointwise stabilizer `H ⊓ fixingSubgroup M (b '' Set.Iio i)` of the earlier points, times the
order of the pointwise stabilizer of all the points. No finiteness is assumed: when `H` is
infinite both sides are `0`. -/
theorem card_eq_prod_ncard_orbit_mul_card_inf_fixingSubgroup (H : Subgroup M) {k : ℕ}
    (b : Fin k → α) :
    Nat.card H = (∏ i : Fin k, (orbit ↥(H ⊓ fixingSubgroup M (b '' Set.Iio i)) (b i)).ncard) *
      Nat.card ↥(H ⊓ fixingSubgroup M (Set.range b)) := by
  induction k with
  | zero => simp [fixingSubgroup_empty]
  | succ k ih =>
    have himage (i : Fin k) : (b ∘ Fin.castSucc) '' Set.Iio i = b '' Set.Iio i.castSucc := by
      rw [Set.image_comp, Fin.image_castSucc_Iio]
    have hrange : Set.range (b ∘ Fin.castSucc) = b '' Set.Iio (Fin.last k) := by
      rw [Set.range_comp]
      congr 1
      ext i
      simp only [Set.mem_range, Fin.exists_castSucc_eq, Set.mem_Iio, Fin.lt_last_iff_ne_last]
    -- fixing all `k + 1` points means fixing the first `k` and stabilizing the last one
    have hfix : fixingSubgroup M (Set.range b) =
        fixingSubgroup M (Set.range (b ∘ Fin.castSucc)) ⊓ stabilizer M (b (Fin.last k)) := by
      ext g
      simp only [mem_inf, mem_fixingSubgroup_iff, Set.forall_mem_range, mem_stabilizer_iff,
        Fin.forall_fin_succ', Function.comp_apply]
    rw [ih (b ∘ Fin.castSucc), Fin.prod_univ_castSucc, mul_assoc,
      card_eq_ncard_orbit_mul_card_inf_stabilizer _ (b (Fin.last k)), inf_assoc, ← hfix, hrange]
    congr 1
    exact Finset.prod_congr rfl fun i _ ↦ by rw [himage, Function.comp_apply]

/-- **The order of a group from a base.** If the pointwise stabilizer in `H` of the points
`b 0, …, b (k - 1)` is trivial, the order of `H` is the product of the lengths of the basic
orbits, the orbits of `b i` under the pointwise stabilizer in `H` of the earlier points. -/
theorem card_eq_prod_ncard_orbit_of_inf_fixingSubgroup_eq_bot (H : Subgroup M) {k : ℕ}
    {b : Fin k → α} (hb : H ⊓ fixingSubgroup M (Set.range b) = ⊥) :
    Nat.card H = ∏ i : Fin k, (orbit ↥(H ⊓ fixingSubgroup M (b '' Set.Iio i)) (b i)).ncard := by
  rw [card_eq_prod_ncard_orbit_mul_card_inf_fixingSubgroup H b, hb, card_bot, mul_one]

/-- For `k` distinct points under a `k`-transitive subgroup `H`, the `i`-th basic orbit, the
orbit of `b i` under the pointwise stabilizer in `H` of the earlier points, is the complement of
the set of earlier points. -/
theorem orbit_inf_fixingSubgroup_image_Iio_eq_compl {k : ℕ} (H : Subgroup M)
    [IsMultiplyPretransitive H α k] {b : Fin k → α} (hb : Function.Injective b) (i : Fin k) :
    orbit ↥(H ⊓ fixingSubgroup M (b '' Set.Iio i)) (b i) = (b '' Set.Iio i)ᶜ := by
  set s := b '' Set.Iio i with hs
  have hbi : b i ∉ s := fun ⟨j, hj, hji⟩ ↦ (Set.mem_Iio.mp hj).ne (hb hji)
  ext y
  constructor
  · intro hy ⟨j, hj, hjy⟩
    obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hy
    refine hbi ⟨j, hj, ?_⟩
    have hgj : (g : M) • b j = b j :=
      (mem_fixingSubgroup_iff M).mp (mem_inf.mp g.2).2 (b j) ⟨j, hj, rfl⟩
    rw [Subgroup.smul_def] at hjy
    exact smul_left_cancel _ (hgj.trans hjy)
  · intro hy
    have hsk : s.ncard + 1 ≤ k := by
      simp [hs, Set.ncard_image_of_injective _ hb, Set.ncard_eq_toFinset_card']
    have hkα : (k : ℕ∞) ≤ ENat.card α := by
      simpa using ENat.card_le_card_of_injective hb
    have : IsPretransitive (fixingSubgroup H s) (SubMulAction.ofFixingSubgroup H s) :=
      is_one_pretransitive_iff.mp
        (SubMulAction.ofFixingSubgroup.isMultiplyPretransitive' s hsk hkα)
    obtain ⟨g, hg⟩ := exists_smul_eq (fixingSubgroup H s)
      (⟨b i, hbi⟩ : SubMulAction.ofFixingSubgroup H s) ⟨y, hy⟩
    have hgs : ((g : H) : M) ∈ fixingSubgroup M s := (mem_fixingSubgroup_iff M).mpr fun x hx ↦
      (mem_fixingSubgroup_iff H).mp g.2 x hx
    exact ⟨⟨(g : H), (g : H).2, hgs⟩, congrArg Subtype.val hg⟩

/-- For `k` distinct points under a `k`-transitive subgroup `H`, the `i`-th basic orbit has
`Nat.card α - i` points, so the first `k` basic orbits have lengths `n, n - 1, …, n - k + 1`
where `n = Nat.card α`. -/
theorem ncard_orbit_inf_fixingSubgroup_image_Iio {k : ℕ} (H : Subgroup M)
    [IsMultiplyPretransitive H α k] {b : Fin k → α} (hb : Function.Injective b) (i : Fin k) :
    (orbit ↥(H ⊓ fixingSubgroup M (b '' Set.Iio i)) (b i)).ncard = Nat.card α - i := by
  rw [orbit_inf_fixingSubgroup_image_Iio_eq_compl H hb i, Set.ncard_compl _ (Set.toFinite _)]
  simp [Set.ncard_image_of_injective _ hb, Set.ncard_eq_toFinset_card']

end Subgroup
