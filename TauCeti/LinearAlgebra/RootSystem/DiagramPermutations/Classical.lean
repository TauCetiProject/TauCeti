/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations.Basic

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
  · have htwo (i j : Fin n) :
        CartanMatrix.B n i j = -2 ↔ i.val + 2 = n ∧ j.val + 1 = n := by
      simp only [CartanMatrix.B, Matrix.of_apply]
      split_ifs <;> simp_all <;> omega
    let a : Fin n := ⟨n - 2, by omega⟩
    let z : Fin n := ⟨n - 1, by omega⟩
    have haz : CartanMatrix.B n a z = -2 := (htwo a z).mpr (by dsimp [a, z]; omega)
    have hz : ρ z = z := by
      have he := (htwo (ρ a) (ρ z)).mp ((h a z).trans haz)
      apply Fin.ext
      dsimp only [z, Fin.val_mk] at he ⊢
      omega
    -- Propagate fixedness backwards from the pinned end of the chain.
    have hfix : ∀ k : ℕ, ∀ j : Fin n, n - 1 - j.val ≤ k → ρ j = j := by
      intro k
      induction k with
      | zero =>
          intro j hj
          have hjz : j = z := by apply Fin.ext; dsimp [z]; omega
          simpa [hjz] using hz
      | succ k ih =>
          intro j hj
          by_cases hj' : n - 1 - j.val ≤ k
          · exact ih j hj'
          have hjn : j.val + 1 < n := by omega
          let s : Fin n := ⟨j.val + 1, hjn⟩
          have hs : ρ s = s := ih s (by dsimp only [s, Fin.val_mk]; omega)
          have hneg : CartanMatrix.B n (ρ j) s < 0 := by
            rw [← hs, h]
            have hjs : j ≠ s := by
              intro he
              have := congrArg Fin.val he
              dsimp only [s, Fin.val_mk] at this
              omega
            simp only [CartanMatrix.B, Matrix.of_apply, hjs, ↓reduceIte, s]
            split_ifs <;> norm_num
          have hne : (ρ j).val ≠ j.val + 2 := by
            intro he
            have hfixed := ih (ρ j) (by omega)
            have hjfix : ρ j = j := ρ.injective hfixed
            have := congrArg Fin.val hjfix
            omega
          apply Fin.ext
          simp only [CartanMatrix.B, Matrix.of_apply] at hneg
          split_ifs at hneg <;> dsimp [s] at * <;> omega
    exact Equiv.ext fun j ↦ hfix (n - 1 - j.val) j le_rfl
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

end TauCeti.DynkinType
