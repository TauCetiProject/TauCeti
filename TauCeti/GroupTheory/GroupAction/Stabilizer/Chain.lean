/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.Index

/-!
# Stabilizer chains

Let a group `G` act on `α`, let `H` be a subgroup of `G` and let `b 0, b 1, …` be points of `α`.
The *stabilizer chain* of `H` along these points is the descending sequence of subgroups
`H.stabilizerChain b i`, the elements of `H` fixing each of `b 0, …, b (i - 1)`; each member is
the stabilizer of `b i` in the previous one. Its *basic orbits* are the orbits
`orbit (H.stabilizerChain b i) (b i)`, and the points `b 0, …, b (k - 1)` form a *base* when the
`k`-th member is trivial.

These are the two basic facts that make a stabilizer chain a description of `H`:

* the order formula: `Nat.card H` is the product of the first `k` basic-orbit lengths times
  `Nat.card (H.stabilizerChain b k)`, and the product of the basic-orbit lengths when the points
  form a base. Neither side needs a finiteness hypothesis: when `H` is infinite both are `0`.
* the membership criterion by sifting: if `R i` is a subset of the `i`-th member whose images of
  `b i` exhaust the `i`-th basic orbit, then `g ∈ H` exactly when one can choose successively
  `r i ∈ R i` sending `b i` to the image of `b i` under the residue
  `(r 0 * ⋯ * r (i - 1))⁻¹ * g`, with final residue in the `k`-th member. Every admissible choice
  ends in the `k`-th member when `g ∈ H`, so a single sift decides membership; over a base the
  final condition reads `g = r 0 * ⋯ * r (k - 1)`.

Applied to a subgroup of `Equiv.Perm (Fin n)`, these reduce the order of a permutation group and
membership in it to computations of orbits of explicit permutations.

## Main declarations

* `Subgroup.stabilizerChain`: the stabilizer chain of a subgroup along a sequence of points.
* `Subgroup.prod_ncard_orbit_mul_card_stabilizerChain`: the stabilizer-chain order formula.
* `Subgroup.prod_ncard_orbit_stabilizerChain_eq_card`: the order formula along a base.
* `Subgroup.mem_iff_inv_mul_mem_stabilizerChain`: any sift decides membership.
* `Subgroup.mem_iff_exists_inv_mul_mem_stabilizerChain`: the membership criterion.
* `Subgroup.mem_iff_exists_prod_eq`: the membership criterion along a base.

## References

* J. D. Dixon and B. Mortimer, *Permutation Groups*, Graduate Texts in Mathematics 163,
  Springer, 1996, §1.4, Theorem 1.4A.
* Á. Seress, *Permutation Group Algorithms*, Cambridge Tracts in Mathematics 152, Cambridge
  University Press, 2003, §4.1.
-/

public section

open MulAction

namespace Subgroup

variable {G α : Type*} [Group G] [MulAction G α]

/-- The stabilizer chain of `H` along the points `b 0, b 1, …`: its `i`-th member consists of the
elements of `H` that fix each of `b 0, …, b (i - 1)`. -/
def stabilizerChain (H : Subgroup G) (b : ℕ → α) (i : ℕ) : Subgroup G :=
  H ⊓ fixingSubgroup G (b '' Set.Iio i)

variable (H : Subgroup G) (b : ℕ → α)

theorem stabilizerChain_def (i : ℕ) :
    H.stabilizerChain b i = H ⊓ fixingSubgroup G (b '' Set.Iio i) :=
  (rfl)

@[simp]
theorem mem_stabilizerChain_iff {i : ℕ} {g : G} :
    g ∈ H.stabilizerChain b i ↔ g ∈ H ∧ ∀ j < i, g • b j = b j := by
  simp [stabilizerChain_def, mem_fixingSubgroup_iff]

@[simp]
theorem stabilizerChain_zero : H.stabilizerChain b 0 = H := by
  ext g
  simp

/-- Each member of a stabilizer chain is the stabilizer of the next point in the previous
member. -/
theorem stabilizerChain_succ (i : ℕ) :
    H.stabilizerChain b (i + 1) = H.stabilizerChain b i ⊓ stabilizer G (b i) := by
  ext g
  simp only [mem_stabilizerChain_iff, mem_inf, mem_stabilizer_iff, Nat.lt_succ_iff_lt_or_eq]
  grind

theorem stabilizerChain_le (i : ℕ) : H.stabilizerChain b i ≤ H :=
  inf_le_left

theorem stabilizerChain_antitone : Antitone (H.stabilizerChain b) := fun _ _ hij ↦
  inf_le_inf_left H <| fixingSubgroup_antitone G α <| Set.image_mono <| Set.Iio_subset_Iio hij

/-! ### The order formula -/

/-- **Orbit–stabilizer along a stabilizer chain.** The order of the `i`-th member of the chain is
the length of the `i`-th basic orbit times the order of the next member. -/
theorem ncard_orbit_mul_card_stabilizerChain_succ (i : ℕ) :
    (orbit (H.stabilizerChain b i) (b i)).ncard * Nat.card (H.stabilizerChain b (i + 1)) =
      Nat.card (H.stabilizerChain b i) := by
  have h := relIndex_mul_card (stabilizer G (b i)) (H.stabilizerChain b i)
  rwa [relIndex, stabilizer_subgroupOf, index_stabilizer, inf_comm, ← stabilizerChain_succ] at h

/-- **The stabilizer-chain order formula.** The order of `H` is the product of the lengths of the
first `k` basic orbits times the order of the `k`-th member of the chain. No finiteness is
needed: when `H` is infinite, both sides are `0`. -/
theorem prod_ncard_orbit_mul_card_stabilizerChain (k : ℕ) :
    (∏ i ∈ Finset.range k, (orbit (H.stabilizerChain b i) (b i)).ncard) *
        Nat.card (H.stabilizerChain b k) = Nat.card H := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, mul_assoc, ncard_orbit_mul_card_stabilizerChain_succ, ih]

/-- **The order formula along a base.** If no element of `H` other than `1` fixes all of
`b 0, …, b (k - 1)`, the order of `H` is the product of the lengths of the first `k` basic
orbits. -/
theorem prod_ncard_orbit_stabilizerChain_eq_card {k : ℕ} (hk : H.stabilizerChain b k = ⊥) :
    ∏ i ∈ Finset.range k, (orbit (H.stabilizerChain b i) (b i)).ncard = Nat.card H := by
  simpa [hk] using H.prod_ncard_orbit_mul_card_stabilizerChain b k

/-! ### Membership by sifting -/

variable {H b}

/-- **The sifting step.** If `r` lies in the `i`-th member of the chain and sends `b i` where `h`
does, then `r⁻¹ * h` lies in the next member exactly when `h` lies in the `i`-th member. -/
theorem inv_mul_mem_stabilizerChain_succ_iff {i : ℕ} {r h : G}
    (hr : r ∈ H.stabilizerChain b i) (hrh : r • b i = h • b i) :
    r⁻¹ * h ∈ H.stabilizerChain b (i + 1) ↔ h ∈ H.stabilizerChain b i := by
  rw [stabilizerChain_succ, mem_inf, mem_stabilizer_iff, mul_smul, ← hrh, inv_smul_smul,
    and_iff_left rfl]
  exact ⟨fun hh ↦ by simpa using mul_mem hr hh, fun hh ↦ mul_mem (inv_mem hr) hh⟩

/-- **A sift decides membership.** Let `r 0, …, r (k - 1)` be chosen successively, `r i` in the
`i`-th member of the chain and sending `b i` to the image of `b i` under the residue
`(r 0 * ⋯ * r (i - 1))⁻¹ * g`. Then `g ∈ H` exactly when the final residue
`(r 0 * ⋯ * r (k - 1))⁻¹ * g` lies in the `k`-th member. -/
theorem mem_iff_inv_mul_mem_stabilizerChain {k : ℕ} {r : ℕ → G} {g : G}
    (hr : ∀ i < k, r i ∈ H.stabilizerChain b i ∧
      r i • b i = ((List.range i).map r).prod⁻¹ • g • b i) :
    g ∈ H ↔ ((List.range k).map r).prod⁻¹ * g ∈ H.stabilizerChain b k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨hrk, hrkb⟩ := hr k k.lt_succ_self
    rw [ih fun i hi ↦ hr i (hi.trans k.lt_succ_self), List.prod_range_succ, mul_inv_rev, mul_assoc,
      inv_mul_mem_stabilizerChain_succ_iff hrk (by rw [hrkb, mul_smul])]

/-- If `g ∈ H` and each `R i` is a subset of the `i`-th member of the chain whose images of `b i`
exhaust the `i`-th basic orbit, then a sift of `g` through the `R i` exists. -/
private theorem exists_sift {k : ℕ} {R : ℕ → Set G}
    (hRle : ∀ i < k, R i ⊆ H.stabilizerChain b i)
    (hRorbit : ∀ i < k, orbit (H.stabilizerChain b i) (b i) ⊆ (· • b i) '' R i)
    {g : G} (hg : g ∈ H) :
    ∃ r : ℕ → G, ∀ i < k, r i ∈ R i ∧ r i • b i = ((List.range i).map r).prod⁻¹ • g • b i := by
  induction k with
  | zero => exact ⟨1, fun i hi ↦ absurd hi i.not_lt_zero⟩
  | succ k ih =>
    obtain ⟨r, hr⟩ := ih (fun i hi ↦ hRle i (hi.trans k.lt_succ_self))
      (fun i hi ↦ hRorbit i (hi.trans k.lt_succ_self))
    -- The residue after `k` steps lies in the `k`-th member, so its image of `b k` lies in the
    -- `k`-th basic orbit and some `s ∈ R k` realizes it.
    have hres := (mem_iff_inv_mul_mem_stabilizerChain fun i hi ↦
      ⟨hRle i (hi.trans k.lt_succ_self) (hr i hi).1, (hr i hi).2⟩).1 hg
    obtain ⟨s, hs, hsb⟩ := hRorbit k k.lt_succ_self (mem_orbit (b k) ⟨_, hres⟩)
    have hprefix : ∀ i ≤ k, (List.range i).map (Function.update r k s) = (List.range i).map r :=
      fun i hi ↦ List.map_congr_left fun j hj ↦
        Function.update_of_ne (by grind) _ _
    refine ⟨Function.update r k s, fun i hi ↦ ?_⟩
    rcases (Nat.lt_succ_iff_lt_or_eq.1 hi) with hi | rfl
    · rw [Function.update_of_ne hi.ne, hprefix i hi.le]
      exact hr i hi
    · rw [Function.update_self, hprefix i le_rfl, ← mul_smul]
      exact ⟨hs, hsb⟩

/-- **The membership criterion along a stabilizer chain.** Let each `R i`, `i < k`, be a subset of
the `i`-th member of the chain whose images of `b i` exhaust the `i`-th basic orbit. Then `g ∈ H`
exactly when there are `r i ∈ R i` with `r i • b i = (r 0 * ⋯ * r (i - 1))⁻¹ • g • b i` for every
`i < k` and with `(r 0 * ⋯ * r (k - 1))⁻¹ * g` in the `k`-th member. -/
theorem mem_iff_exists_inv_mul_mem_stabilizerChain {k : ℕ} {R : ℕ → Set G}
    (hRle : ∀ i < k, R i ⊆ H.stabilizerChain b i)
    (hRorbit : ∀ i < k, orbit (H.stabilizerChain b i) (b i) ⊆ (· • b i) '' R i) {g : G} :
    g ∈ H ↔ ∃ r : ℕ → G,
      (∀ i < k, r i ∈ R i ∧ r i • b i = ((List.range i).map r).prod⁻¹ • g • b i) ∧
        ((List.range k).map r).prod⁻¹ * g ∈ H.stabilizerChain b k := by
  refine ⟨fun hg ↦ ?_, fun ⟨r, hr, hres⟩ ↦ ?_⟩
  · obtain ⟨r, hr⟩ := exists_sift hRle hRorbit hg
    exact ⟨r, hr, (mem_iff_inv_mul_mem_stabilizerChain fun i hi ↦
      ⟨hRle i hi (hr i hi).1, (hr i hi).2⟩).1 hg⟩
  · exact (mem_iff_inv_mul_mem_stabilizerChain fun i hi ↦
      ⟨hRle i hi (hr i hi).1, (hr i hi).2⟩).2 hres

/-- **The membership criterion along a base.** If no element of `H` other than `1` fixes all of
`b 0, …, b (k - 1)`, and each `R i`, `i < k`, is a subset of the `i`-th member of the chain whose
images of `b i` exhaust the `i`-th basic orbit, then `g ∈ H` exactly when
`g = r 0 * ⋯ * r (k - 1)` for some `r i ∈ R i` with
`r i • b i = (r 0 * ⋯ * r (i - 1))⁻¹ • g • b i` for every `i < k`. -/
theorem mem_iff_exists_prod_eq {k : ℕ} (hk : H.stabilizerChain b k = ⊥) {R : ℕ → Set G}
    (hRle : ∀ i < k, R i ⊆ H.stabilizerChain b i)
    (hRorbit : ∀ i < k, orbit (H.stabilizerChain b i) (b i) ⊆ (· • b i) '' R i) {g : G} :
    g ∈ H ↔ ∃ r : ℕ → G,
      (∀ i < k, r i ∈ R i ∧ r i • b i = ((List.range i).map r).prod⁻¹ • g • b i) ∧
        ((List.range k).map r).prod = g := by
  simp_rw [mem_iff_exists_inv_mul_mem_stabilizerChain hRle hRorbit, hk, mem_bot, inv_mul_eq_one]

end Subgroup
