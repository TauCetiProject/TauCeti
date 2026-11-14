/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations.Basic
import TauCeti.GroupTheory.Perm.Fin
import TauCeti.LinearAlgebra.Matrix.Cartan.Basic

/-!
# Rigidity of the numbered B and C diagrams

A permutation preserving the oriented Cartan matrix of `Bₙ` or `Cₙ` fixes every node.
For rank at least two, the unique entry `-2` pins the last edge with its orientation;
the remaining nodes are then determined successively along the chain. Transposition
identifies the two rigidity problems. The statements include ranks zero and one.

These results distinguish ordinary diagram automorphisms from length-exchanging
permutations, and are used to exclude nontrivial based actions on nonsimply-laced
irreducible root systems.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, plates II and III.
-/

public section

namespace TauCeti.DynkinType

/-- Every permutation preserving the oriented Cartan matrix of `Bₙ` is the identity,
including in ranks zero and one. -/
theorem eq_one_of_cartanMatrix_B {n : ℕ} {ρ : Equiv.Perm (Fin n)}
    (h : ∀ i j, (B n).cartanMatrix (ρ i) (ρ j) = (B n).cartanMatrix i j) : ρ = 1 := by
  simp only [cartanMatrix_B] at h
  by_cases hn : 2 ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    apply Equiv.Perm.eq_one_of_adjacent_of_apply_last
    · intro i j hij
      apply (CartanMatrix.B_apply_neg_iff _ _).mp
      rw [h]
      exact (CartanMatrix.B_apply_neg_iff _ _).mpr (Or.inl hij)
    · let a : Fin (m + 1) := ⟨m - 1, by omega⟩
      have haz : CartanMatrix.B (m + 1) a (Fin.last m) = -2 :=
        (CartanMatrix.B_apply_eq_neg_two_iff _ _).mpr (by dsimp [a]; omega)
      have he := (CartanMatrix.B_apply_eq_neg_two_iff _ _).mp
        ((h a (Fin.last m)).trans haz)
      apply Fin.ext
      simp only [Fin.val_last]
      omega
  · apply Equiv.ext
    intro i
    apply Fin.ext
    have := i.isLt
    have := (ρ i).isLt
    simp only [Equiv.Perm.one_apply]
    omega

/-- Every permutation preserving the oriented Cartan matrix of `Cₙ` is the identity.
The assertion is the transpose of the type-B assertion and includes all ranks. -/
theorem eq_one_of_cartanMatrix_C {n : ℕ} {ρ : Equiv.Perm (Fin n)}
    (h : ∀ i j, (C n).cartanMatrix (ρ i) (ρ j) = (C n).cartanMatrix i j) : ρ = 1 := by
  apply eq_one_of_cartanMatrix_B
  intro i j
  simpa only [cartanMatrix_C, cartanMatrix_B, ← CartanMatrix.B_transpose,
    Matrix.transpose_apply] using h j i

/-- The numbered type-B diagram has trivial symmetry group, including in ranks zero and one. -/
@[simp] theorem diagramSymmetry_B_eq_bot (n : ℕ) : (B n).diagramSymmetry = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).mpr fun _ h ↦
    eq_one_of_cartanMatrix_B (mem_diagramSymmetry_iff.mp h)

/-- The numbered type-C diagram has trivial symmetry group, including in ranks zero and one. -/
@[simp] theorem diagramSymmetry_C_eq_bot (n : ℕ) : (C n).diagramSymmetry = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).mpr fun _ h ↦
    eq_one_of_cartanMatrix_C (mem_diagramSymmetry_iff.mp h)

end TauCeti.DynkinType
