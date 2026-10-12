/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.OrbitCount.Basic

/-!
# Cycle partitions of permutations on dependent sums

A permutation acting separately on the fibres of a dependent sum has the cycles of all
its fibre permutations, including their fixed points. This gives the cycle partitions and
cycle counts used when a finite cover is decomposed into its connected components.

The partition calculation uses `Equiv.Perm.fullCycleType_eq_sum_subtypePerm`, the
invariant-fibre decomposition theorem, and `Equiv.sigmaSubtype` to identify each fibre.
-/

public section

namespace Equiv.Perm

variable {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, Fintype (α i)]
  [DecidableEq ι] [∀ i, DecidableEq (α i)]

/-- The full cycle partition of a permutation on a dependent sum is the sum of the full
cycle partitions on the fibres. Fixed points contribute parts equal to one. -/
@[simp]
theorem parts_partition_sigmaCongrRight (σ : ∀ i, Perm (α i)) :
    (sigmaCongrRight σ).partition.parts = ∑ i, (σ i).partition.parts := by
  classical
  rw [← fullCycleType_def, fullCycleType_eq_sum_subtypePerm _ Sigma.fst (fun _ => rfl)]
  apply Finset.sum_congr rfl
  intro i _
  let τ := (sigmaCongrRight σ).subtypePerm (p := fun x => x.1 = i) (fun _ => Iff.rfl)
  have hτ : (Equiv.sigmaSubtype i).permCongr τ = σ i := by
    ext x
    -- `sigmaSubtype` inserts the index `i` in its inverse and removes it in its forward
    -- map. Restricting `sigmaCongrRight σ` to this fibre therefore acts exactly by `σ i`.
    rfl
  rw [← fullCycleType_def, ← hτ, fullCycleType_permCongr]
  -- The fibre has two inferred enumerations, both instances of the subsingleton `Fintype`.
  congr 1
  exact Subsingleton.elim _ _

omit [∀ i, Fintype (α i)] [DecidableEq ι] [∀ i, DecidableEq (α i)] in
/-- The number of cycles of a permutation on a dependent sum is the sum of the cycle
counts on its fibres. Empty fibres and an empty index type are allowed. -/
@[simp]
theorem orbitCount_sigmaCongrRight [∀ i, Finite (α i)] (σ : ∀ i, Perm (α i)) :
    TauCeti.orbitCount (sigmaCongrRight σ) = ∑ i, TauCeti.orbitCount (σ i) := by
  classical
  let _ (i : ι) : Fintype (α i) := Fintype.ofFinite (α i)
  simp only [orbitCount_eq_card_parts_partition, parts_partition_sigmaCongrRight,
    Multiset.card_sum]

end Equiv.Perm
