/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Parabolic
public import TauCeti.GroupTheory.Perm.Poincare
public import TauCeti.RepresentationTheory.Symmetric.YoungSubgroup.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import TauCeti.Data.Fin.Basic

/-!
# Young subgroups as standard parabolic subgroups of `Sₙ`

For a partition `μ` of `n`, the decreasing parts `μ₁ ≥ μ₂ ≥ ⋯` partition `Fin n` into consecutive
blocks recorded by `TauCeti.youngBlock μ`. Let `TauCeti.youngParabolicSet μ` be the set of simple
reflection indices `i : Fin (n - 1)` whose adjacent strands `i` and `i + 1` lie in the same block
of `μ`.

This file identifies the standard parabolic subgroup `(permCoxeterSystem n).parabolic
(youngParabolicSet μ)` of the type-`A` Coxeter system on `Equiv.Perm (Fin n)` with the Young
subgroup `TauCeti.youngSubgroup μ`, shows that Coxeter length on `youngSubgroup μ` splits additively
across the block decomposition `TauCeti.youngSubgroupMulEquiv`, evaluates the parabolic length
generating function as the product of the quantum factorials of the parts of `μ`, and characterizes
minimal left-coset representatives as the permutations strictly increasing on every `μ`-block.

## Main definitions

* `TauCeti.youngParabolicSet`: the set of simple reflection indices `i : Fin (n - 1)` whose
  strands `i` and `i + 1` belong to the same consecutive block of `μ`.

## Main results

* `TauCeti.youngBlock_mono`: `youngBlock μ` is monotone on `Fin n`.
* `TauCeti.parabolic_youngParabolicSet_eq_youngSubgroup`: the standard parabolic subgroup of
  `youngParabolicSet μ` in `permCoxeterSystem n` is `youngSubgroup μ`.
* `TauCeti.length_coe_youngSubgroup`: the Coxeter length of an element of `youngSubgroup μ` is the
  sum of the Coxeter lengths of its block components.
* `TauCeti.sum_pow_length_youngSubgroup` and
  `TauCeti.sum_pow_length_parabolic_youngParabolicSet`: the length generating function of a Young
  subgroup is the product of the quantum factorials of the parts of `μ`.
* `TauCeti.isMinimalCosetRep_youngParabolicSet_iff`: `d` is a minimal left-coset representative for
  `youngParabolicSet μ` if and only if `d` is strictly increasing on each block of `μ`.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 2.4.
* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999), Sections 1.3 and 3.1.
-/

public section

namespace TauCeti

open BraidGroup

/-- `youngBlocksEquiv μ` orders block coordinates lexicographically: first by block index, then by
position within the block. -/
theorem youngBlocksEquiv_lt_youngBlocksEquiv_iff {n : ℕ} (μ : n.Partition)
    {x y : Σ i : Fin (μ.parts.sort (· ≥ ·)).length, Fin ((μ.parts.sort (· ≥ ·)).get i)} :
    youngBlocksEquiv μ x < youngBlocksEquiv μ y ↔
      x.1 < y.1 ∨ x.1 = y.1 ∧ (x.2 : ℕ) < y.2 := by
  rw [Fin.lt_def, youngBlocksEquiv_apply, youngBlocksEquiv_apply,
    ← finSigmaFinEquiv_apply (n := fun i => (μ.parts.sort (· ≥ ·)).get i),
    ← finSigmaFinEquiv_apply (n := fun i => (μ.parts.sort (· ≥ ·)).get i),
    ← Fin.lt_def, finSigmaFinEquiv_lt_finSigmaFinEquiv_iff]

/-- **The consecutive-block label `youngBlock μ` is monotone.** -/
theorem youngBlock_mono {n : ℕ} (μ : n.Partition) : Monotone (youngBlock μ) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := (youngBlocksEquiv μ).surjective a
  obtain ⟨y, rfl⟩ := (youngBlocksEquiv μ).surjective b
  rw [youngBlock_youngBlocksEquiv, youngBlock_youngBlocksEquiv]
  rcases hab.eq_or_lt with h | h
  · rw [(youngBlocksEquiv μ).injective h]
  · rcases (youngBlocksEquiv_lt_youngBlocksEquiv_iff μ).mp h with hlt | ⟨heq, -⟩
    · exact hlt.le
    · exact heq.le

/-- **The parabolic index set of a partition `μ` of `n`:** the simple reflection indices
`i : Fin (n - 1)` whose adjacent strands `strand i` and `strandSucc i` lie in the same consecutive
block of `μ`. -/
def youngParabolicSet {n : ℕ} (μ : n.Partition) : Set (Fin (n - 1)) :=
  {i | youngBlock μ (strand i) = youngBlock μ (strandSucc i)}

/-- Membership in `youngParabolicSet μ` means that strands `i` and `i + 1` share a `μ`-block. -/
@[simp]
theorem mem_youngParabolicSet_iff {n : ℕ} (μ : n.Partition) (i : Fin (n - 1)) :
    i ∈ youngParabolicSet μ ↔ youngBlock μ (strand i) = youngBlock μ (strandSucc i) :=
  (Iff.rfl)

/-- An adjacent transposition belongs to `youngSubgroup μ` if and only if its index lies in
`youngParabolicSet μ`. -/
theorem transposition_mem_youngSubgroup_iff {n : ℕ} (μ : n.Partition) (i : Fin (n - 1)) :
    transposition i ∈ youngSubgroup μ ↔ i ∈ youngParabolicSet μ := by
  rw [mem_youngSubgroup_iff, mem_youngParabolicSet_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hi := congrFun h (strand i)
    rwa [Function.comp_apply, transposition_apply_strand, eq_comm] at hi
  · ext x
    rw [Function.comp_apply, transposition_eq_swap]
    rcases eq_or_ne x (strand i) with rfl | hx₁
    · rw [Equiv.swap_apply_left, h]
    · rcases eq_or_ne x (strandSucc i) with rfl | hx₂
      · rw [Equiv.swap_apply_right, h]
      · rw [Equiv.swap_apply_of_ne_of_ne hx₁ hx₂]

/-- The parabolic index set of the single-row partition `(n)` is the full generator set. -/
@[simp]
theorem youngParabolicSet_indiscrete (n : ℕ) :
    youngParabolicSet (Nat.Partition.indiscrete n) = Set.univ := by
  ext i
  rw [← transposition_mem_youngSubgroup_iff, youngSubgroup_indiscrete]
  simp

/-- The parabolic index set of the single-column partition `(1ⁿ)` is empty. -/
@[simp]
theorem youngParabolicSet_ones (n : ℕ) :
    youngParabolicSet (Nat.Partition.ones n) = ∅ := by
  ext i
  rw [← transposition_mem_youngSubgroup_iff, youngSubgroup_ones, Subgroup.mem_bot,
    Set.mem_empty_iff_false, iff_false]
  intro h
  have hi := Equiv.Perm.congr_fun h (strand i)
  rw [transposition_apply_strand, Equiv.Perm.one_apply] at hi
  exact strand_ne_strandSucc i hi.symm

/-- **The Young subgroup of `μ` is the standard parabolic subgroup of `youngParabolicSet μ` in
`permCoxeterSystem n`.** -/
theorem parabolic_youngParabolicSet_eq_youngSubgroup {n : ℕ} (μ : n.Partition) :
    (permCoxeterSystem n).parabolic (youngParabolicSet μ) = youngSubgroup μ := by
  refine le_antisymm ?_ fun σ hσ => ?_
  · rw [CoxeterSystem.parabolic_le_iff]
    intro i hi
    rwa [permCoxeterSystem_simple, transposition_mem_youngSubgroup_iff]
  · induction hk : (permCoxeterSystem n).length σ generalizing σ with
    | zero =>
      rw [(permCoxeterSystem n).length_eq_zero_iff.mp hk]
      exact one_mem _
    | succ k ih =>
      have hne : σ ≠ 1 := fun h => by simp [h] at hk
      obtain ⟨i, hdesc⟩ := (permCoxeterSystem n).exists_rightDescent_of_ne_one hne
      have hlt : σ (strandSucc i) < σ (strand i) :=
        isRightDescent_permCoxeterSystem_iff.mp hdesc
      have hσblk : ∀ x, youngBlock μ (σ x) = youngBlock μ x :=
        congrFun ((mem_youngSubgroup_iff μ σ).mp hσ)
      have hi : i ∈ youngParabolicSet μ := by
        rw [mem_youngParabolicSet_iff]
        refine le_antisymm (youngBlock_mono μ (Fin.lt_def.mpr (by simp)).le) ?_
        rw [← hσblk (strandSucc i), ← hσblk (strand i)]
        exact youngBlock_mono μ hlt.le
      have hsi_par : transposition i ∈ (permCoxeterSystem n).parabolic (youngParabolicSet μ) := by
        rw [← permCoxeterSystem_simple]
        exact (permCoxeterSystem n).simple_mem_parabolic hi
      have hsi_young : transposition i ∈ youngSubgroup μ :=
        (transposition_mem_youngSubgroup_iff μ i).mpr hi
      have hlen : (permCoxeterSystem n).length (σ * transposition i) = k := by
        have h1 := (permCoxeterSystem n).isRightDescent_iff.mp hdesc
        rw [permCoxeterSystem_simple, hk] at h1
        omega
      have hmul := ih (σ * transposition i) (mul_mem hσ hsi_young) hlen
      simpa only [mul_assoc, transposition_mul_self, mul_one] using mul_mem hmul hsi_par

/-! ### Coxeter length and Poincaré polynomial on a Young subgroup -/

/-- Applying a Young-subgroup element in block coordinates acts independently on each block. -/
theorem coe_youngSubgroup_youngBlocksEquiv {n : ℕ} (μ : n.Partition) (σ : youngSubgroup μ)
    (i : Fin (μ.parts.sort (· ≥ ·)).length) (a : Fin ((μ.parts.sort (· ≥ ·)).get i)) :
    (σ : Equiv.Perm (Fin n)) (youngBlocksEquiv μ ⟨i, a⟩) =
      youngBlocksEquiv μ ⟨i, youngSubgroupMulEquiv μ σ i a⟩ := by
  apply (youngBlocksEquiv μ).symm.injective
  rw [youngSubgroupMulEquiv_apply_youngBlocksEquiv, Equiv.symm_apply_apply]

/-- **Coxeter length on a Young subgroup is the sum of the Coxeter lengths on its blocks.** -/
theorem length_coe_youngSubgroup {n : ℕ} (μ : n.Partition) (σ : youngSubgroup μ) :
    (permCoxeterSystem n).length (σ : Equiv.Perm (Fin n)) =
      ∑ i, (permCoxeterSystem ((μ.parts.sort (· ≥ ·)).get i)).length
        (youngSubgroupMulEquiv μ σ i) := by
  classical
  simp_rw [permCoxeterSystem_length_eq_card_inversion]
  rw [← Finset.card_sigma]
  symm
  refine Finset.card_bij
    (fun s _ => (youngBlocksEquiv μ ⟨s.1, s.2.1⟩, youngBlocksEquiv μ ⟨s.1, s.2.2⟩))
    (fun ⟨i, a, b⟩ hs => ?_) (fun ⟨i, a, b⟩ _ ⟨j, c, e⟩ _ h => ?_) (fun ⟨p, q⟩ hpq => ?_)
  · simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hs ⊢
    rw [coe_youngSubgroup_youngBlocksEquiv, coe_youngSubgroup_youngBlocksEquiv,
      youngBlocksEquiv_lt_youngBlocksEquiv_iff, youngBlocksEquiv_lt_youngBlocksEquiv_iff]
    exact ⟨Or.inr ⟨rfl, Fin.lt_def.mp hs.1⟩, Or.inr ⟨rfl, Fin.lt_def.mp hs.2⟩⟩
  · rw [Prod.mk.injEq] at h
    have h₁ := (youngBlocksEquiv μ).injective h.1
    have h₂ := (youngBlocksEquiv μ).injective h.2
    cases h₁
    cases h₂
    rfl
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpq
    obtain ⟨⟨i, a⟩, rfl⟩ := (youngBlocksEquiv μ).surjective p
    obtain ⟨⟨j, b⟩, rfl⟩ := (youngBlocksEquiv μ).surjective q
    rw [coe_youngSubgroup_youngBlocksEquiv, coe_youngSubgroup_youngBlocksEquiv,
      youngBlocksEquiv_lt_youngBlocksEquiv_iff, youngBlocksEquiv_lt_youngBlocksEquiv_iff] at hpq
    rcases hpq with ⟨hij | ⟨hij, hab⟩, hji | ⟨hji, hba⟩⟩
    · exact absurd hji hij.not_gt
    · exact absurd hji.symm hij.ne
    · subst hij
      exact absurd hji (lt_irrefl _)
    · subst hij
      refine ⟨⟨i, (a, b)⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and]
      exact ⟨Fin.lt_def.mpr hab, Fin.lt_def.mpr hba⟩

/-- **The length generating function of `youngSubgroup μ` is the product of the quantum factorials
of the parts of `μ`.** -/
theorem sum_pow_length_youngSubgroup {R : Type*} [CommSemiring R] (x : R) {n : ℕ}
    (μ : n.Partition) [Fintype (youngSubgroup μ)] :
    (∑ σ : youngSubgroup μ, x ^ (permCoxeterSystem n).length (σ : Equiv.Perm (Fin n))) =
      (μ.parts.map fun p => ∏ d ∈ Finset.Icc 1 p, ∑ j ∈ Finset.range d, x ^ j).prod := by
  set L := μ.parts.sort (· ≥ ·)
  set f : ℕ → R := fun p => ∏ d ∈ Finset.Icc 1 p, ∑ j ∈ Finset.range d, x ^ j
  calc
    (∑ σ : youngSubgroup μ, x ^ (permCoxeterSystem n).length (σ : Equiv.Perm (Fin n)))
        = ∑ σ : youngSubgroup μ,
            ∏ i : Fin L.length,
              x ^ (permCoxeterSystem (L.get i)).length (youngSubgroupMulEquiv μ σ i) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [length_coe_youngSubgroup, Finset.prod_pow_eq_pow_sum]
    _ = ∑ p : (∀ i : Fin L.length, Equiv.Perm (Fin (L.get i))),
          ∏ i : Fin L.length, x ^ (permCoxeterSystem (L.get i)).length (p i) :=
          (youngSubgroupMulEquiv μ).toEquiv.sum_comp fun p =>
            ∏ i : Fin L.length, x ^ (permCoxeterSystem (L.get i)).length (p i)
    _ = ∏ i : Fin L.length,
          ∑ τ : Equiv.Perm (Fin (L.get i)), x ^ (permCoxeterSystem (L.get i)).length τ :=
          (Fintype.prod_sum fun (i : Fin L.length) (τ : Equiv.Perm (Fin (L.get i))) =>
            x ^ (permCoxeterSystem (L.get i)).length τ).symm
    _ = ∏ i : Fin L.length, f (L.get i) :=
          Finset.prod_congr rfl fun i _ => sum_pow_permCoxeterSystem_length x _
    _ = (μ.parts.map f).prod := by
          simp_rw [List.get_eq_getElem]
          rw [Fin.prod_univ_fun_getElem L f, ← Multiset.prod_coe, ← Multiset.map_coe]
          simp [L]

/-- **The length generating function of the standard parabolic subgroup
`(permCoxeterSystem n).parabolic (youngParabolicSet μ)` is the product of the quantum factorials of
the parts of `μ`.** -/
theorem sum_pow_length_parabolic_youngParabolicSet {R : Type*} [CommSemiring R] (x : R) {n : ℕ}
    (μ : n.Partition)
    [Fintype ((permCoxeterSystem n).parabolic (youngParabolicSet μ))] :
    (∑ σ : (permCoxeterSystem n).parabolic (youngParabolicSet μ),
        x ^ (permCoxeterSystem n).length (σ : Equiv.Perm (Fin n))) =
      (μ.parts.map fun p => ∏ d ∈ Finset.Icc 1 p, ∑ j ∈ Finset.range d, x ^ j).prod := by
  classical
  let e : (permCoxeterSystem n).parabolic (youngParabolicSet μ) ≃ youngSubgroup μ :=
    Equiv.subtypeEquivRight fun σ => by rw [parabolic_youngParabolicSet_eq_youngSubgroup]
  rw [Fintype.sum_equiv e
    (fun σ => x ^ (permCoxeterSystem n).length (σ : Equiv.Perm (Fin n)))
    (fun σ => x ^ (permCoxeterSystem n).length (σ : Equiv.Perm (Fin n)))
    (fun _ => rfl)]
  exact sum_pow_length_youngSubgroup x μ

/-! ### Minimal left-coset representatives -/

/-- **A permutation `d` is a minimal left-coset representative for `youngParabolicSet μ` if and
only if `d` is strictly increasing on each `μ`-block.** -/
theorem isMinimalCosetRep_youngParabolicSet_iff {n : ℕ} (μ : n.Partition)
    (d : Equiv.Perm (Fin n)) :
    (permCoxeterSystem n).IsMinimalCosetRep (youngParabolicSet μ) d ↔
      ∀ ⦃x y : Fin n⦄, youngBlock μ x = youngBlock μ y → x < y → d x < d y := by
  rw [(permCoxeterSystem n).isMinimalCosetRep_iff]
  simp only [mem_youngParabolicSet_iff, isRightDescent_permCoxeterSystem_iff, not_lt]
  refine ⟨fun h x y hblk hxy => ?_, fun h i hi =>
    (h hi (Fin.lt_def.mpr (by simp))).le⟩
  obtain ⟨yv, hy⟩ := y
  induction yv with
  | zero => exact absurd (Fin.lt_def.mp hxy) (Nat.not_lt_zero _)
  | succ y' ih =>
    let i : Fin (n - 1) := ⟨y', by omega⟩
    have hz : strand i = ⟨y', Nat.lt_of_succ_lt hy⟩ := Fin.ext (val_strand i)
    have hsy : strandSucc i = ⟨y' + 1, hy⟩ := Fin.ext (val_strandSucc i)
    have hxz : x ≤ strand i := by
      rw [Fin.le_iff_val_le_val, val_strand]
      exact Nat.le_of_lt_succ (Fin.lt_def.mp hxy)
    have hzy : strand i ≤ strandSucc i := by
      rw [Fin.le_iff_val_le_val, val_strand, val_strandSucc]
      exact Nat.le_succ y'
    rw [← hsy] at hblk ⊢
    have hblk_i : youngBlock μ (strand i) = youngBlock μ (strandSucc i) :=
      le_antisymm (youngBlock_mono μ hzy) (hblk ▸ youngBlock_mono μ hxz)
    have hdz : d (strand i) < d (strandSucc i) := lt_of_le_of_ne (h i hblk_i)
      (d.injective.ne (strand_ne_strandSucc i))
    rcases hxz.eq_or_lt with hxeq | hlt
    · rwa [hxeq]
    · rw [hz] at hblk_i hlt hdz
      exact (ih (Nat.lt_of_succ_lt hy) (hblk.trans hblk_i.symm) hlt).trans hdz

end TauCeti
