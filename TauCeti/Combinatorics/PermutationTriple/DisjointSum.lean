/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.CycleData
public import TauCeti.GroupTheory.Perm.SumCongr

/-!
# Disjoint sums of permutation triples

Two covers of the thrice-punctured sphere may be laid side by side, and the resulting cover has
the disjoint union of their sheets. On the combinatorial side this is the juxtaposition of two
permutation triples: `TauCeti.PermutationTriple.disjointSum` takes a triple of degree `m` and one
of degree `n` to a triple of degree `m + n`, acting through `finSumFinEquiv` by the first triple
on the first `m` labels and by the second on the last `n`.

## Main results

* `TauCeti.PermutationTriple.disjointSum`: the construction, componentwise
  `Equiv.Perm.finSumPerm`.
* `TauCeti.PermutationTriple.cycleData_disjointSum`,
  `TauCeti.PermutationTriple.cycleCounts_disjointSum`: the cycle data of a disjoint sum is the
  concatenation of the cycle data of its summands, and the cycle counts add.
* `TauCeti.PermutationTriple.monodromyGroup_disjointSum_le`: the monodromy group of a disjoint
  sum consists of relabelings acting separately on the two blocks, and each of the two components
  lies in the monodromy group of the corresponding summand. The inclusion is strict in general —
  the monodromy group of the disjoint sum of a triple with itself is the diagonal, not the whole
  product.
* `TauCeti.PermutationTriple.not_isConnected_disjointSum`: a disjoint sum of two triples of
  nonzero degree is disconnected.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.5.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

namespace PermutationTriple

variable {m n : ℕ}

/-- The disjoint sum of two permutation triples: the triple of degree `m + n` whose components
act by those of `s` on the first `m` labels and by those of `t` on the last `n`. It is the
combinatorial shadow of laying two covers of the thrice-punctured sphere side by side. -/
def disjointSum (s : PermutationTriple m) (t : PermutationTriple n) :
    PermutationTriple (m + n) where
  σ0 := finSumPerm s.σ0 t.σ0
  σ1 := finSumPerm s.σ1 t.σ1
  σinf := finSumPerm s.σinf t.σinf
  product_eq_one := by
    rw [finSumPerm_mul, finSumPerm_mul, s.product_eq_one, t.product_eq_one, finSumPerm_one]

variable (s : PermutationTriple m) (t : PermutationTriple n)

@[simp] theorem disjointSum_σ0 : (s.disjointSum t).σ0 = finSumPerm s.σ0 t.σ0 := (rfl)

@[simp] theorem disjointSum_σ1 : (s.disjointSum t).σ1 = finSumPerm s.σ1 t.σ1 := (rfl)

@[simp] theorem disjointSum_σinf : (s.disjointSum t).σinf = finSumPerm s.σinf t.σinf := (rfl)

/-- The disjoint sum of two trivial triples is trivial. -/
@[simp] theorem disjointSum_one_one :
    (1 : PermutationTriple m).disjointSum (1 : PermutationTriple n) = 1 :=
  ext_of_two (by simp) (by simp)

/-- Relabeling the two summands separately relabels their disjoint sum. -/
theorem disjointSum_smul (τ : Perm (Fin m)) (υ : Perm (Fin n)) :
    (τ • s).disjointSum (υ • t) = finSumPerm τ υ • s.disjointSum t :=
  ext_of_two (by simp [finSumPerm_mul]) (by simp [finSumPerm_mul])

/-! ### Cycle data -/

/-- The full cycle partitions of a disjoint sum are the concatenations of those of the two
summands, branch point by branch point. -/
@[simp]
theorem cycleData_disjointSum :
    (s.disjointSum t).cycleData =
      (s.cycleData.1 + t.cycleData.1, s.cycleData.2.1 + t.cycleData.2.1,
        s.cycleData.2.2 + t.cycleData.2.2) := by
  have h0 : (s.disjointSum t).cycleData.1 = s.cycleData.1 + t.cycleData.1 := by simp
  have h1 : (s.disjointSum t).cycleData.2.1 = s.cycleData.2.1 + t.cycleData.2.1 := by simp
  have h2 : (s.disjointSum t).cycleData.2.2 = s.cycleData.2.2 + t.cycleData.2.2 := by simp
  rw [← h0, ← h1, ← h2]

/-- The cycle counts of a disjoint sum are the sums of the cycle counts of the two summands,
branch point by branch point. -/
@[simp]
theorem cycleCounts_disjointSum :
    (s.disjointSum t).cycleCounts =
      (s.cycleCounts.1 + t.cycleCounts.1, s.cycleCounts.2.1 + t.cycleCounts.2.1,
        s.cycleCounts.2.2 + t.cycleCounts.2.2) := by
  have h0 : (s.disjointSum t).cycleCounts.1 = s.cycleCounts.1 + t.cycleCounts.1 := by simp
  have h1 : (s.disjointSum t).cycleCounts.2.1 = s.cycleCounts.2.1 + t.cycleCounts.2.1 := by simp
  have h2 : (s.disjointSum t).cycleCounts.2.2 = s.cycleCounts.2.2 + t.cycleCounts.2.2 := by simp
  rw [← h0, ← h1, ← h2]

/-! ### Monodromy and connectedness -/

/-- The monodromy group of a disjoint sum acts separately on the two blocks of labels, through
the monodromy groups of the two summands. The inclusion is not an equality in general: the
disjoint sum of a triple with itself has diagonal monodromy. -/
theorem monodromyGroup_disjointSum_le :
    (s.disjointSum t).monodromyGroup ≤
      (s.monodromyGroup.prod t.monodromyGroup).map (finSumPermHom m n) := by
  rw [← closure_triple_eq_monodromyGroup (s.disjointSum t)]
  refine (Subgroup.closure_le _).mpr ?_
  rintro g (rfl | rfl | rfl)
  · exact Subgroup.mem_map.mpr
      ⟨(s.σ0, t.σ0), Subgroup.mem_prod.mpr ⟨s.σ0_mem_monodromyGroup, t.σ0_mem_monodromyGroup⟩,
        by simp⟩
  · exact Subgroup.mem_map.mpr
      ⟨(s.σ1, t.σ1), Subgroup.mem_prod.mpr ⟨s.σ1_mem_monodromyGroup, t.σ1_mem_monodromyGroup⟩,
        by simp⟩
  · exact Subgroup.mem_map.mpr
      ⟨(s.σinf, t.σinf),
        Subgroup.mem_prod.mpr ⟨s.σinf_mem_monodromyGroup, t.σinf_mem_monodromyGroup⟩, by simp⟩

/-- Every element of the monodromy group of a disjoint sum preserves the first block of labels,
which is the reason the sum is disconnected. -/
theorem apply_castAdd_mem_range_castAdd_of_mem_monodromyGroup {g : Perm (Fin (m + n))}
    (hg : g ∈ (s.disjointSum t).monodromyGroup) (i : Fin m) :
    g (Fin.castAdd n i) ∈ Set.range (Fin.castAdd n : Fin m → Fin (m + n)) := by
  obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp (monodromyGroup_disjointSum_le s t hg)
  exact ⟨p.1 i, by simp⟩

/-- A disjoint sum of two triples of nonzero degree is disconnected: no relabeling in its
monodromy group carries a label of the first block to one of the second. -/
theorem not_isConnected_disjointSum (hm : m ≠ 0) (hn : n ≠ 0) :
    ¬ (s.disjointSum t).IsConnected := by
  intro hc
  have htrans := hc.isPretransitive
  obtain ⟨i⟩ : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hm)
  obtain ⟨j⟩ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  obtain ⟨g, hg⟩ := htrans.exists_smul_eq (Fin.castAdd n i) (Fin.natAdd m j)
  obtain ⟨i', hi'⟩ :=
    apply_castAdd_mem_range_castAdd_of_mem_monodromyGroup s t g.2 i
  have hval : (Fin.castAdd n i' : Fin (m + n)).val = (Fin.natAdd m j : Fin (m + n)).val := by
    rw [hi']
    exact congrArg Fin.val (hg : (g : Perm (Fin (m + n))) (Fin.castAdd n i) = Fin.natAdd m j)
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
  omega

end PermutationTriple

end TauCeti
