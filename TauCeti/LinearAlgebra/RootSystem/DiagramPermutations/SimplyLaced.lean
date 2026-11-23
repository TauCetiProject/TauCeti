/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations.Basic
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.GroupTheory.Perm.Fin
import TauCeti.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.Matrix.MulVec

/-!
# Classification and cycle orthogonality of simply-laced diagram symmetries

`TauCeti.DynkinType.diagramSymmetry` is the group of permutations of the Bourbaki-numbered simple
roots preserving the standard Cartan matrix of a `TauCeti.DynkinType`. The individual graph
permutations `TauCeti.graphPermA`, `TauCeti.graphPermD`, `TauCeti.graphPermE6`, and
`TauCeti.trialityPermD4` are defined in
`TauCeti.LinearAlgebra.RootSystem.DiagramPermutations.Basic`, together with triviality of the
symmetry group for `E₈`, while triviality for the non-simply-laced types `Bₙ`, `Cₙ`, `F₄`, and `G₂`
is proved in `TauCeti.LinearAlgebra.RootSystem.DiagramPermutations.NonSimplyLaced`. This file
completes the classification of `diagramSymmetry` across all simply-laced Dynkin types and derives
the cycle-orthogonality dichotomy that governs diagram folding of irreducible root systems:

* **Type `E₇`**: `E₇` has trivial diagram symmetry group
  (`TauCeti.DynkinType.diagramSymmetry_E7_eq_bot`).
* **Type `Aₙ`**: a permutation preserves `CartanMatrix.A n` if and only if it is `1` or the chain
  reversal `TauCeti.graphPermA n` (`TauCeti.DynkinType.mem_diagramSymmetry_A_iff`).
* **Type `D₄`**: a permutation preserves `CartanMatrix.D 4` if and only if it fixes the central
  node `1` (`TauCeti.DynkinType.mem_diagramSymmetry_D4_iff`), giving the full symmetric group `S₃`
  on the three outer nodes `{0, 2, 3}`.
* **Type `Dₙ` (`5 ≤ n`)**: a permutation preserves `CartanMatrix.D n` if and only if it is `1` or
  the fork swap `TauCeti.graphPermD n` (`TauCeti.DynkinType.mem_diagramSymmetry_D_iff_of_five_le`).
* **Type `E₆`**: a permutation preserves `CartanMatrix.E 6` if and only if it is `1` or
  `TauCeti.graphPermE6` (`TauCeti.DynkinType.mem_diagramSymmetry_E6_iff`).
* **Cycle orthogonality**: for any valid simply-laced type `t` and `σ ∈ t.diagramSymmetry`, either
  distinct nodes in the same `σ`-cycle have zero Cartan pairing, or `t = A (2 * m)` (`1 ≤ m`) and
  `σ = graphPermA (2 * m)`, in which case `{m - 1, m}` is the unique non-orthogonal `σ`-orbit
  (`TauCeti.DynkinType.cartanMatrix_eq_zero_of_sameCycle_or_eq_A_even`,
  `TauCeti.DynkinType.cartanMatrix_A_even_graphPermA_eq_zero_iff`).

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §4, Plates I--IX.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §12.2, Table 1.
* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, p. 1, condition (1).
-/

public section

namespace TauCeti.DynkinType

/-! ### Type `Aₙ` -/

/-- A diagram symmetry of `Aₙ` fixing node `0` fixes every node along the chain. -/
private theorem eq_one_of_mem_diagramSymmetry_A_of_apply_zero {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ (A n).diagramSymmetry) (h0 : ∀ h : 0 < n, (σ ⟨0, h⟩ : ℕ) = 0) : σ = 1 := by
  cases n with
  | zero => exact Subsingleton.elim σ 1
  | succ m =>
    let r := graphPermA (m + 1)
    let τ := r * σ * r
    have hτ : τ ∈ (A (m + 1)).diagramSymmetry :=
      (A (m + 1)).diagramSymmetry.mul_mem
        ((A (m + 1)).diagramSymmetry.mul_mem (graphPermA_mem_diagramSymmetry _) hσ)
        (graphPermA_mem_diagramSymmetry _)
    have hmat (i j : Fin (m + 1)) :
        CartanMatrix.A (m + 1) (τ i) (τ j) = CartanMatrix.A (m + 1) i j :=
      congrFun₂ (cartanMatrix_A (m + 1) ▸ mem_diagramSymmetry_iff_submatrix.mp hτ) i j
    have hadj (i j : Fin (m + 1)) (hij : i.val + 1 = j.val) :
        (τ i).val + 1 = (τ j).val ∨ (τ j).val + 1 = (τ i).val :=
      (CartanMatrix.A_apply_eq_neg_one_iff (τ i) (τ j)).mp
        ((hmat i j).trans ((CartanMatrix.A_apply_eq_neg_one_iff i j).mpr (Or.inl hij)))
    have hlast : τ (Fin.last m) = Fin.last m := by
      have hr_last : r (Fin.last m) = ⟨0, Nat.succ_pos m⟩ := by
        ext; simp [r, graphPermA_apply]
      have hσ0 : σ ⟨0, Nat.succ_pos m⟩ = ⟨0, Nat.succ_pos m⟩ := Fin.ext (h0 (Nat.succ_pos m))
      have hr0 : r ⟨0, Nat.succ_pos m⟩ = Fin.last m := by
        ext; simp [r, graphPermA_apply]
      simp only [τ, Equiv.Perm.mul_apply, hr_last, hσ0, hr0]
    have hτ1 : τ = 1 := Equiv.Perm.eq_one_of_adjacent_of_apply_last_eq_self hadj hlast
    refine Equiv.ext fun i ↦ ?_
    have hi := congrArg (fun ρ : Equiv.Perm (Fin (m + 1)) ↦ r (ρ (r i))) hτ1
    simpa [τ, r, Equiv.Perm.mul_apply] using hi

/-- A diagram symmetry of `Aₙ` (`2 ≤ n`) sends node `0` to one of the two endpoints `0` or
`n - 1`, since interior nodes have two neighbours of entry `-1` while node `0` has only one. -/
private theorem apply_zero_eq_zero_or_sub_one_of_mem_diagramSymmetry_A {n : ℕ} (hn : 2 ≤ n)
    {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ (A n).diagramSymmetry) :
    (σ ⟨0, by omega⟩ : ℕ) = 0 ∨ (σ ⟨0, by omega⟩ : ℕ) = n - 1 := by
  have hmat (i j : Fin n) : CartanMatrix.A n (σ i) (σ j) = CartanMatrix.A n i j :=
    congrFun₂ (cartanMatrix_A n ▸ mem_diagramSymmetry_iff_submatrix.mp hσ) i j
  by_contra h
  have hlt := (σ ⟨0, by omega⟩).isLt
  let u : Fin n := ⟨(σ ⟨0, by omega⟩ : ℕ) - 1, by omega⟩
  let v : Fin n := ⟨(σ ⟨0, by omega⟩ : ℕ) + 1, by omega⟩
  have hu : CartanMatrix.A n ⟨0, by omega⟩ (σ.symm u) = -1 := by
    rw [← hmat, Equiv.apply_symm_apply, CartanMatrix.A_apply_eq_neg_one_iff]
    right; simp [u]; omega
  have hv : CartanMatrix.A n ⟨0, by omega⟩ (σ.symm v) = -1 := by
    rw [← hmat, Equiv.apply_symm_apply, CartanMatrix.A_apply_eq_neg_one_iff]
    left; simp [v]
  rw [CartanMatrix.A_apply_eq_neg_one_iff] at hu hv
  simp only at hu hv
  have huv : σ.symm u = σ.symm v := Fin.ext (by omega)
  have : (u : ℕ) = (v : ℕ) := congrArg Fin.val (σ.symm.injective huv)
  simp only [u, v] at this
  omega

/-- **Classification of diagram symmetries of `Aₙ`**: a node permutation preserves the type-`Aₙ`
Cartan matrix if and only if it is the identity or the chain reversal `TauCeti.graphPermA n`. -/
theorem mem_diagramSymmetry_A_iff {n : ℕ} {σ : Equiv.Perm (Fin n)} :
    σ ∈ (A n).diagramSymmetry ↔ σ = 1 ∨ σ = graphPermA n := by
  refine ⟨fun hσ ↦ ?_, ?_⟩
  · rcases le_or_gt n 1 with hn | hn
    · have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn
      exact Or.inl (Subsingleton.elim σ 1)
    · rcases apply_zero_eq_zero_or_sub_one_of_mem_diagramSymmetry_A hn hσ with h0 | hlast
      · exact Or.inl (eq_one_of_mem_diagramSymmetry_A_of_apply_zero hσ fun _ ↦ h0)
      · right
        have hmul : graphPermA n * σ ∈ (A n).diagramSymmetry :=
          (A n).diagramSymmetry.mul_mem (graphPermA_mem_diagramSymmetry n) hσ
        have hmul0 : ∀ h : 0 < n, ((graphPermA n * σ) ⟨0, h⟩ : ℕ) = 0 := fun _ ↦ by
          rw [Equiv.Perm.mul_apply, graphPermA_apply, Fin.val_rev, hlast]
          omega
        have hone := eq_one_of_mem_diagramSymmetry_A_of_apply_zero hmul hmul0
        refine Equiv.ext fun i ↦ ?_
        have hi := congrArg (fun ρ : Equiv.Perm (Fin n) ↦ graphPermA n (ρ i)) hone
        simpa [Equiv.Perm.mul_apply] using hi
  · rintro (rfl | rfl)
    · exact (A n).diagramSymmetry.one_mem
    · exact graphPermA_mem_diagramSymmetry n

/-! ### Types `D₄` and `Dₙ` (`5 ≤ n`) -/

/-- **Classification of diagram symmetries of `D₄`**: a permutation of `Fin 4` preserves the
`D₄` Cartan matrix if and only if it fixes the central node `1`. -/
theorem mem_diagramSymmetry_D4_iff {σ : Equiv.Perm (Fin 4)} :
    σ ∈ (D 4).diagramSymmetry ↔ σ 1 = 1 := by
  have hD4 : ∀ i j : Fin 4,
      CartanMatrix.D 4 i j = if i = j then 2 else if i = 1 ∨ j = 1 then -1 else 0 := by
    intro i j; fin_cases i <;> fin_cases j <;> decide
  refine ⟨fun hσ ↦ ?_, fun h1 ↦ ?_⟩
  · have hmat (i j : Fin 4) : CartanMatrix.D 4 (σ i) (σ j) = CartanMatrix.D 4 i j :=
      congrFun₂ (cartanMatrix_D 4 ▸ mem_diagramSymmetry_iff_submatrix.mp hσ) i j
    by_contra hne
    have h0 : σ 0 = 1 := by
      have h10 := (hmat 1 0).trans (by decide : CartanMatrix.D 4 1 0 = -1)
      rw [hD4] at h10
      have hne10 : σ 1 ≠ σ 0 := σ.injective.ne (by decide)
      simp only [hne10, ↓reduceIte, hne, false_or] at h10
      split_ifs at h10 with h01
      exact h01
    have h2 : σ 2 = 1 := by
      have h12 := (hmat 1 2).trans (by decide : CartanMatrix.D 4 1 2 = -1)
      rw [hD4] at h12
      have hne12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
      simp only [hne12, ↓reduceIte, hne, false_or] at h12
      split_ifs at h12 with h21
      exact h21
    exact absurd (σ.injective (h0.trans h2.symm)) (by decide)
  · have hrev (i j : Fin 4) : (D 4).cartanMatrix (σ i) (σ j) = (D 4).cartanMatrix i j := by
      have hi1 : σ i = 1 ↔ i = 1 := ⟨fun h ↦ σ.injective (h.trans h1.symm), fun h ↦ h ▸ h1⟩
      have hj1 : σ j = 1 ↔ j = 1 := ⟨fun h ↦ σ.injective (h.trans h1.symm), fun h ↦ h ▸ h1⟩
      simp only [cartanMatrix_D, hD4, σ.injective.eq_iff, hi1, hj1]
    exact mem_diagramSymmetry_iff.mpr hrev

/-- Every diagram symmetry of `Dₙ` (`4 ≤ n`) fixes the unique branch node `n - 3`, which is the
only node with three neighbours of entry `-1`. -/
private theorem apply_branch_eq_of_mem_diagramSymmetry_D {n : ℕ} (hn : 4 ≤ n)
    {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ (D n).diagramSymmetry) :
    σ ⟨n - 3, by omega⟩ = ⟨n - 3, by omega⟩ := by
  have hmat (i j : Fin n) : CartanMatrix.D n (σ i) (σ j) = CartanMatrix.D n i j :=
    congrFun₂ (cartanMatrix_D n ▸ mem_diagramSymmetry_iff_submatrix.mp hσ) i j
  let u₁ : Fin n := ⟨n - 4, by omega⟩
  let u₂ : Fin n := ⟨n - 2, by omega⟩
  let u₃ : Fin n := ⟨n - 1, by omega⟩
  have hc₁ : CartanMatrix.D n (σ ⟨n - 3, by omega⟩) (σ u₁) = -1 := by
    rw [hmat, CartanMatrix.D_apply_eq_neg_one_iff]; right; left; simp [u₁]; omega
  have hc₂ : CartanMatrix.D n (σ ⟨n - 3, by omega⟩) (σ u₂) = -1 := by
    rw [hmat, CartanMatrix.D_apply_eq_neg_one_iff]; right; right; left; simp [u₂]; omega
  have hc₃ : CartanMatrix.D n (σ ⟨n - 3, by omega⟩) (σ u₃) = -1 := by
    rw [hmat, CartanMatrix.D_apply_eq_neg_one_iff]; right; right; left; simp [u₃]; omega
  rw [CartanMatrix.D_apply_eq_neg_one_iff] at hc₁ hc₂ hc₃
  have h12 : (σ u₁ : ℕ) ≠ (σ u₂ : ℕ) := fun h ↦ by
    have := congrArg Fin.val (σ.injective (Fin.ext h)); simp only [u₁, u₂] at this; omega
  have h13 : (σ u₁ : ℕ) ≠ (σ u₃ : ℕ) := fun h ↦ by
    have := congrArg Fin.val (σ.injective (Fin.ext h)); simp only [u₁, u₃] at this; omega
  have h23 : (σ u₂ : ℕ) ≠ (σ u₃ : ℕ) := fun h ↦ by
    have := congrArg Fin.val (σ.injective (Fin.ext h)); simp only [u₂, u₃] at this; omega
  have := (σ ⟨n - 3, by omega⟩).isLt
  have := (σ u₁).isLt
  have := (σ u₂).isLt
  have := (σ u₃).isLt
  exact Fin.ext (by simp only; omega)

/-- For `5 ≤ n`, every diagram symmetry of `Dₙ` fixes node `n - 4`: it is adjacent to `n - 5`,
whereas the fork leaves `n - 2` and `n - 1` meet only the branch node `n - 3`. -/
private theorem apply_sub_four_eq_of_mem_diagramSymmetry_D {n : ℕ} (hn : 5 ≤ n)
    {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ (D n).diagramSymmetry) :
    σ ⟨n - 4, by omega⟩ = ⟨n - 4, by omega⟩ := by
  have hmat (i j : Fin n) : CartanMatrix.D n (σ i) (σ j) = CartanMatrix.D n i j :=
    congrFun₂ (cartanMatrix_D n ▸ mem_diagramSymmetry_iff_submatrix.mp hσ) i j
  have hbranch := apply_branch_eq_of_mem_diagramSymmetry_D (by omega) hσ
  have hadj : CartanMatrix.D n (σ ⟨n - 3, by omega⟩) (σ ⟨n - 4, by omega⟩) = -1 := by
    rw [hmat, CartanMatrix.D_apply_eq_neg_one_iff]; right; left; simp; omega
  rw [hbranch, CartanMatrix.D_apply_eq_neg_one_iff] at hadj
  simp only at hadj
  have hlt := (σ ⟨n - 4, by omega⟩).isLt
  rcases (by omega : (σ ⟨n - 4, by omega⟩ : ℕ) = n - 4 ∨
      (σ ⟨n - 4, by omega⟩ : ℕ) = n - 2 ∨ (σ ⟨n - 4, by omega⟩ : ℕ) = n - 1) with h4 | hfork
  · exact Fin.ext (by simp only [h4])
  · exfalso
    let z : Fin n := σ ⟨n - 4, by omega⟩
    have h45 : CartanMatrix.D n ⟨n - 4, by omega⟩ ⟨n - 5, by omega⟩ = -1 := by
      rw [CartanMatrix.D_apply_eq_neg_one_iff]; right; left; simp; omega
    have hz5 : CartanMatrix.D n z (σ ⟨n - 5, by omega⟩) = -1 := by
      simpa only [z] using (hmat ⟨n - 4, by omega⟩ ⟨n - 5, by omega⟩).trans h45
    rw [CartanMatrix.D_apply_eq_neg_one_iff] at hz5
    have := (σ ⟨n - 5, by omega⟩).isLt
    have h5br : σ ⟨n - 5, by omega⟩ = σ ⟨n - 3, by omega⟩ := by
      rw [hbranch]; exact Fin.ext (by simp only [z] at hz5 ⊢; omega)
    have := congrArg Fin.val (σ.injective h5br)
    simp only at this
    omega

/-- For `5 ≤ n`, every diagram symmetry of `Dₙ` fixes every stem node `0, …, n - 3` by downward
two-step induction from `n - 3` and `n - 4`. -/
private theorem apply_stem_eq_of_mem_diagramSymmetry_D {n : ℕ} (hn : 5 ≤ n)
    {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ (D n).diagramSymmetry) :
    ∀ d (_ : d ≤ n - 3), σ ⟨n - 3 - d, by omega⟩ = ⟨n - 3 - d, by omega⟩ := by
  have hmat (i j : Fin n) : CartanMatrix.D n (σ i) (σ j) = CartanMatrix.D n i j :=
    congrFun₂ (cartanMatrix_D n ▸ mem_diagramSymmetry_iff_submatrix.mp hσ) i j
  intro d
  induction d using Nat.twoStepInduction with
  | zero => intro _; exact apply_branch_eq_of_mem_diagramSymmetry_D (by omega) hσ
  | one => intro _; simpa only [Nat.sub_sub] using apply_sub_four_eq_of_mem_diagramSymmetry_D hn hσ
  | more d ih0 ih1 =>
    intro hd
    have ih0' := ih0 (by omega)
    have ih1' := ih1 (by omega)
    have hadj : CartanMatrix.D n (σ ⟨n - 3 - (d + 1), by omega⟩)
        (σ ⟨n - 3 - (d + 2), by omega⟩) = -1 := by
      rw [hmat, CartanMatrix.D_apply_eq_neg_one_iff]; right; left; simp; omega
    rw [ih1', CartanMatrix.D_apply_eq_neg_one_iff] at hadj
    simp only at hadj
    have := (σ ⟨n - 3 - (d + 2), by omega⟩).isLt
    have hne : (σ ⟨n - 3 - (d + 2), by omega⟩ : ℕ) ≠ n - 3 - d := fun heq ↦ by
      have ih0_val : (σ ⟨n - 3 - d, by omega⟩ : ℕ) = n - 3 - d := by
        simpa only using congrArg Fin.val ih0'
      have h1 : σ ⟨n - 3 - (d + 2), by omega⟩ = σ ⟨n - 3 - d, by omega⟩ :=
        Fin.ext (heq.trans ih0_val.symm)
      have := congrArg Fin.val (σ.injective h1)
      simp only at this
      omega
    exact Fin.ext (by simp only; omega)

/-- A permutation of `Fin n` (`4 ≤ n`) fixing `0, …, n - 3` and `n - 2` also fixes `n - 1`. -/
private theorem eq_one_of_apply_le_sub_three_and_sub_two {n : ℕ} (hn : 4 ≤ n)
    {τ : Equiv.Perm (Fin n)} (hstem : ∀ i : Fin n, (i : ℕ) ≤ n - 3 → τ i = i)
    (h2 : τ ⟨n - 2, by omega⟩ = ⟨n - 2, by omega⟩) : τ = 1 :=
  τ.eq_one_of_forall_ne_apply_eq_self ⟨n - 1, by omega⟩ fun i hi ↦ by
    rcases le_or_gt (i : ℕ) (n - 3) with hle | hgt
    · exact hstem i hle
    · have hi_eq : i = ⟨n - 2, by omega⟩ :=
        Fin.ext (by have := i.isLt; have := Fin.val_ne_of_ne hi; simp only at this ⊢; omega)
      simpa only [hi_eq] using h2

/-- **Classification of diagram symmetries of `Dₙ` for `5 ≤ n`**: a node permutation preserves the
type-`Dₙ` Cartan matrix if and only if it is the identity or the fork swap
`TauCeti.graphPermD n`. -/
theorem mem_diagramSymmetry_D_iff_of_five_le {n : ℕ} (hn : 5 ≤ n) {σ : Equiv.Perm (Fin n)} :
    σ ∈ (D n).diagramSymmetry ↔ σ = 1 ∨ σ = graphPermD n (by omega) := by
  refine ⟨fun hσ ↦ ?_, ?_⟩
  · have hstem (i : Fin n) (hi : (i : ℕ) ≤ n - 3) : σ i = i := by
      have hd := apply_stem_eq_of_mem_diagramSymmetry_D hn hσ (n - 3 - i) (by omega)
      have hsub : (⟨n - 3 - (n - 3 - i), by omega⟩ : Fin n) = i := Fin.ext (by simp only; omega)
      simpa only [hsub] using hd
    have hfork : (σ ⟨n - 2, by omega⟩ : ℕ) = n - 2 ∨ (σ ⟨n - 2, by omega⟩ : ℕ) = n - 1 := by
      by_contra h
      have hlt := (σ ⟨n - 2, by omega⟩).isLt
      have hinj := σ.injective (hstem (σ ⟨n - 2, by omega⟩) (by omega))
      have := congrArg Fin.val hinj
      simp only at this
      omega
    rcases hfork with h2 | h2
    · exact Or.inl (eq_one_of_apply_le_sub_three_and_sub_two (by omega) hstem
        (Fin.ext (by simp only [h2])))
    · right
      have hmul_stem (i : Fin n) (hi : (i : ℕ) ≤ n - 3) :
          (graphPermD n (by omega) * σ) i = i := by
        rw [Equiv.Perm.mul_apply, hstem i hi]
        exact graphPermD_apply_of_ne_of_ne n (by omega) i (by omega) (by omega)
      have hmul_2 : (graphPermD n (by omega) * σ) ⟨n - 2, by omega⟩ = ⟨n - 2, by omega⟩ := by
        have hσ2 : σ ⟨n - 2, by omega⟩ = ⟨n - 1, by omega⟩ := Fin.ext (by simp only [h2])
        rw [Equiv.Perm.mul_apply, hσ2, graphPermD_apply_right]
      have hone := eq_one_of_apply_le_sub_three_and_sub_two (by omega) hmul_stem hmul_2
      refine Equiv.ext fun i ↦ ?_
      have hi := congrArg (fun ρ : Equiv.Perm (Fin n) ↦ graphPermD n (by omega) (ρ i)) hone
      simpa [Equiv.Perm.mul_apply] using hi
  · rintro (rfl | rfl)
    · exact (D n).diagramSymmetry.one_mem
    · exact graphPermD_mem_diagramSymmetry (by omega)

/-! ### Exceptional types `E₆` and `E₇` -/

open _root_.Matrix in
/-- **The Dynkin diagram of `E₇` has no nontrivial symmetry.** Three multiplications of the
all-ones vector by `CartanMatrix.E 7` produce `(4, 9, 1, -10, 6, -5, 5)`, whose entries are
pairwise distinct. -/
@[simp]
theorem diagramSymmetry_E7_eq_bot : E7.diagramSymmetry = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun σ hσ ↦ ?_
  have hsub : (CartanMatrix.E 7).submatrix σ σ = CartanMatrix.E 7 :=
    cartanMatrix_E7 ▸ mem_diagramSymmetry_iff_submatrix.mp hσ
  have hfix := mulVec_comp_of_submatrix_eq hsub
    (mulVec_comp_of_submatrix_eq hsub (mulVec_comp_of_submatrix_eq hsub (v := fun _ ↦ 1) rfl))
  have hinj : Function.Injective (CartanMatrix.E 7 *ᵥ
      (CartanMatrix.E 7 *ᵥ (CartanMatrix.E 7 *ᵥ fun _ ↦ (1 : ℤ)))) := by decide
  ext i
  exact congrArg Fin.val (hinj (congrFun hfix i))

open _root_.Matrix in
/-- A diagram symmetry of `E₆` fixing node `0` is the identity. -/
private theorem eq_one_of_mem_diagramSymmetry_E6_of_apply_zero {σ : Equiv.Perm (Fin 6)}
    (hσ : σ ∈ E6.diagramSymmetry) (h0 : σ 0 = 0) : σ = 1 := by
  have hsub : (CartanMatrix.E 6).submatrix σ σ = CartanMatrix.E 6 :=
    cartanMatrix_E6 ▸ mem_diagramSymmetry_iff_submatrix.mp hσ
  have hmat (i j : Fin 6) : CartanMatrix.E 6 (σ i) (σ j) = CartanMatrix.E 6 i j :=
    congrFun₂ hsub i j
  -- Two multiplications of `1` give `(2, 3, 0, -3, 0, 2)`, pinning `1`, `3`, and `{0, 5}`.
  let w := CartanMatrix.E 6 *ᵥ (CartanMatrix.E 6 *ᵥ fun _ ↦ (1 : ℤ))
  have hfix : w ∘ σ = w :=
    mulVec_comp_of_submatrix_eq hsub (mulVec_comp_of_submatrix_eq hsub (v := fun _ ↦ 1) rfl)
  have hw1 : ∀ x : Fin 6, w x = 3 → x = 1 := by decide
  have hw3 : ∀ x : Fin 6, w x = -3 → x = 3 := by decide
  have hw5 : ∀ x : Fin 6, w x = 2 → x = 0 ∨ x = 5 := by decide
  have h1 : σ 1 = 1 := hw1 (σ 1) (by simpa [w] using (congrFun hfix 1).trans (by decide))
  have h3 : σ 3 = 3 := hw3 (σ 3) (by simpa [w] using (congrFun hfix 3).trans (by decide))
  have h5 : σ 5 = 5 := by
    rcases hw5 (σ 5) (by simpa [w] using (congrFun hfix 5).trans (by decide)) with h50 | h55
    · exact absurd (σ.injective (h50.trans h0.symm)) (by decide)
    · exact h55
  have h2 : σ 2 = 2 := by
    have h02 : CartanMatrix.E 6 0 (σ 2) = -1 := by
      rw [← h0]; exact (hmat 0 2).trans (by decide)
    have hcol : ∀ x : Fin 6, CartanMatrix.E 6 0 x = -1 → x = 2 := by decide
    exact hcol (σ 2) h02
  have h4 : σ 4 = 4 := by
    have h54 : CartanMatrix.E 6 5 (σ 4) = -1 := by
      rw [← h5]; exact (hmat 5 4).trans (by decide)
    have hcol : ∀ x : Fin 6, CartanMatrix.E 6 5 x = -1 → x = 4 := by decide
    exact hcol (σ 4) h54
  refine Equiv.ext fun i ↦ ?_
  fin_cases i
  exacts [h0, h1, h2, h3, h4, h5]

open _root_.Matrix in
/-- **Classification of diagram symmetries of `E₆`**: a node permutation preserves the `E₆` Cartan
matrix if and only if it is the identity or `TauCeti.graphPermE6`. -/
theorem mem_diagramSymmetry_E6_iff {σ : Equiv.Perm (Fin 6)} :
    σ ∈ E6.diagramSymmetry ↔ σ = 1 ∨ σ = graphPermE6 := by
  refine ⟨fun hσ ↦ ?_, ?_⟩
  · have hsub : (CartanMatrix.E 6).submatrix σ σ = CartanMatrix.E 6 :=
      cartanMatrix_E6 ▸ mem_diagramSymmetry_iff_submatrix.mp hσ
    let w := CartanMatrix.E 6 *ᵥ (CartanMatrix.E 6 *ᵥ fun _ ↦ (1 : ℤ))
    have hfix : w ∘ σ = w :=
      mulVec_comp_of_submatrix_eq hsub (mulVec_comp_of_submatrix_eq hsub (v := fun _ ↦ 1) rfl)
    have hw0 : ∀ x : Fin 6, w x = 2 → x = 0 ∨ x = 5 := by decide
    rcases hw0 (σ 0) (by simpa [w] using (congrFun hfix 0).trans (by decide)) with h0 | h0
    · exact Or.inl (eq_one_of_mem_diagramSymmetry_E6_of_apply_zero hσ h0)
    · right
      have hmul : graphPermE6 * σ ∈ E6.diagramSymmetry :=
        E6.diagramSymmetry.mul_mem graphPermE6_mem_diagramSymmetry hσ
      have hmul0 : (graphPermE6 * σ) 0 = 0 := by
        rw [Equiv.Perm.mul_apply, h0, graphPermE6_apply_five]
      have hone := eq_one_of_mem_diagramSymmetry_E6_of_apply_zero hmul hmul0
      have hinv : ∀ x : Fin 6, graphPermE6 (graphPermE6 x) = x := fun x ↦ by
        simpa [sq, Equiv.Perm.mul_apply] using congrArg (· x) graphPermE6_sq
      refine Equiv.ext fun i ↦ ?_
      have hi := congrArg (fun ρ : Equiv.Perm (Fin 6) ↦ graphPermE6 (ρ i)) hone
      simpa [Equiv.Perm.mul_apply, hinv] using hi
  · rintro (rfl | rfl)
    · exact E6.diagramSymmetry.one_mem
    · exact graphPermE6_mem_diagramSymmetry

/-! ### Cycle orthogonality of simply-laced diagram symmetries -/

/-- For odd `n`, every diagram symmetry of `Aₙ` has pairwise orthogonal cycles: distinct reversed
nodes `i` and `i.rev` have indices of the same parity, so they cannot be consecutive. -/
theorem cartanMatrix_A_eq_zero_of_sameCycle_of_odd {n : ℕ} (hn : Odd n)
    {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ (A n).diagramSymmetry) {i j : Fin n}
    (hcycle : σ.SameCycle i j) (hne : i ≠ j) : (A n).cartanMatrix i j = 0 := by
  rcases mem_diagramSymmetry_A_iff.mp hσ with rfl | rfl
  · exact absurd (Equiv.Perm.sameCycle_one.mp hcycle) hne
  · have hinv : Function.Involutive (graphPermA n) := graphPermA_graphPermA n
    rcases (hinv.sameCycle_iff i j).mp hcycle with rfl | hij
    · exact absurd rfl hne
    · obtain ⟨k, rfl⟩ := hn
      rw [graphPermA_apply] at hij
      subst hij
      have hne' : (j.rev : ℕ) ≠ j := Fin.val_ne_of_ne hne
      rw [Fin.val_rev] at hne'
      simp only [cartanMatrix_A, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_rev]
      have := j.isLt
      (split_ifs <;> simp_all); omega

/-- Under chain reversal of `A₂ₙ` (`1 ≤ n`), the middle pair `(n - 1, n)` has Cartan pairing
`-1`. -/
theorem cartanMatrix_A_even_mid {n : ℕ} (hn : 1 ≤ n) :
    (A (2 * n)).cartanMatrix (⟨n - 1, by omega⟩ : Fin (2 * n))
      (⟨n, by omega⟩ : Fin (2 * n)) = -1 := by
  have h : CartanMatrix.A (2 * n) ⟨n - 1, by omega⟩ ⟨n, by omega⟩ = -1 := by
    rw [CartanMatrix.A_apply_eq_neg_one_iff]
    left; simp; omega
  simpa only [cartanMatrix_A] using h

/-- Under chain reversal of `A₂ₙ`, two distinct nodes in the same orbit have zero Cartan pairing
if and only if they do not form the adjacent middle orbit `{n - 1, n}`. -/
theorem cartanMatrix_A_even_graphPermA_eq_zero_iff {n : ℕ} {i j : Fin (2 * n)}
    (hcycle : (graphPermA (2 * n)).SameCycle i j) (hne : i ≠ j) :
    (A (2 * n)).cartanMatrix i j = 0 ↔ (i : ℕ) ≠ n - 1 ∧ (j : ℕ) ≠ n - 1 := by
  have hinv : Function.Involutive (graphPermA (2 * n)) := graphPermA_graphPermA (2 * n)
  rcases (hinv.sameCycle_iff i j).mp hcycle with rfl | hij
  · exact absurd rfl hne
  · rw [graphPermA_apply] at hij
    subst hij
    have hne' : (j.rev : ℕ) ≠ j := Fin.val_ne_of_ne hne
    rw [Fin.val_rev] at hne'
    simp only [cartanMatrix_A, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_rev]
    have := j.isLt
    split_ifs <;> simp_all <;> omega

/-- Every diagram symmetry of `Dₙ` (`4 ≤ n`) has pairwise orthogonal cycles: in `D₄` the central
node `1` is fixed and the three outer nodes `{0, 2, 3}` are mutually orthogonal, while for `5 ≤ n`
only the two orthogonal fork leaves `n - 2` and `n - 1` can be exchanged. -/
theorem cartanMatrix_D_eq_zero_of_sameCycle {n : ℕ} (hn : 4 ≤ n)
    {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ (D n).diagramSymmetry) {i j : Fin n}
    (hcycle : σ.SameCycle i j) (hne : i ≠ j) : (D n).cartanMatrix i j = 0 := by
  rcases eq_or_lt_of_le hn with rfl | hn5
  · have h1 : σ 1 = 1 := mem_diagramSymmetry_D4_iff.mp hσ
    have hi1 : i ≠ 1 := fun hi ↦ hne (hcycle.eq_of_left (hi.symm ▸ h1))
    have hj1 : j ≠ 1 := fun hj ↦ hne (hcycle.eq_of_right (hj.symm ▸ h1))
    fin_cases i <;> fin_cases j <;> simp_all [cartanMatrix_D, CartanMatrix.D]
  · rcases (mem_diagramSymmetry_D_iff_of_five_le hn5).mp hσ with rfl | rfl
    · exact absurd (Equiv.Perm.sameCycle_one.mp hcycle) hne
    · have hinv : Function.Involutive (graphPermD n (by omega)) := graphPermD_apply_apply n _
      rcases (hinv.sameCycle_iff i j).mp hcycle with rfl | hij
      · exact absurd rfl hne
      · have hjfork : (j : ℕ) = n - 2 ∨ (j : ℕ) = n - 1 := by
          by_contra hnot
          exact hne (hij.trans (graphPermD_apply_of_ne_of_ne n (by omega) j
            (fun h ↦ hnot (Or.inl h)) (fun h ↦ hnot (Or.inr h))))
        have hifork : (i : ℕ) = n - 2 ∨ (i : ℕ) = n - 1 := by
          rcases hjfork with hj2 | hj1
          · have hj_eq : j = ⟨n - 2, by omega⟩ := Fin.ext hj2
            rw [hij, hj_eq, graphPermD_apply_left]; right; rfl
          · have hj_eq : j = ⟨n - 1, by omega⟩ := Fin.ext hj1
            rw [hij, hj_eq, graphPermD_apply_right]; left; rfl
        have hne' : (i : ℕ) ≠ j := Fin.val_ne_of_ne hne
        simp only [cartanMatrix_D, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
        split_ifs <;> simp_all <;> omega

/-- Every diagram symmetry of `E₆` has pairwise orthogonal cycles, since `0` is orthogonal to `5`
and `2` is orthogonal to `4`. -/
theorem cartanMatrix_E6_eq_zero_of_sameCycle {σ : Equiv.Perm (Fin 6)}
    (hσ : σ ∈ E6.diagramSymmetry) {i j : Fin 6}
    (hcycle : σ.SameCycle i j) (hne : i ≠ j) : E6.cartanMatrix i j = 0 := by
  rcases mem_diagramSymmetry_E6_iff.mp hσ with rfl | rfl
  · exact absurd (Equiv.Perm.sameCycle_one.mp hcycle) hne
  · have hinv : Function.Involutive graphPermE6 := fun x ↦ by
      simpa [sq, Equiv.Perm.mul_apply] using congrArg (· x) graphPermE6_sq
    rcases (hinv.sameCycle_iff i j).mp hcycle with rfl | rfl
    · exact absurd rfl hne
    · fin_cases j <;> simp_all [cartanMatrix_E6, CartanMatrix.E]

/-- **Cycle-orthogonality dichotomy for valid simply-laced Dynkin types.** For any valid
simply-laced Dynkin type `t` and diagram symmetry `σ ∈ t.diagramSymmetry`, either distinct nodes in
every `σ`-cycle have zero Cartan pairing, or `t = A (2 * n)` (`1 ≤ n`) and `σ` reverses the
numbered nodes. -/
theorem cartanMatrix_eq_zero_of_sameCycle_or_eq_A_even {t : DynkinType} (ht : t.Valid)
    (hsl : t.IsSimplyLaced) {σ : Equiv.Perm (Fin t.rank)} (hσ : σ ∈ t.diagramSymmetry) :
    (∀ i j : Fin t.rank, σ.SameCycle i j → i ≠ j → t.cartanMatrix i j = 0) ∨
      ∃ n : ℕ, 1 ≤ n ∧ t = A (2 * n) ∧ ∀ i : Fin t.rank, σ i = i.rev := by
  revert σ
  cases t with
  | B _ | C _ | F4 | G2 => exact absurd hsl (by simp)
  | E7 =>
    intro σ hσ
    rw [diagramSymmetry_E7_eq_bot, Subgroup.mem_bot] at hσ
    subst hσ
    exact Or.inl fun i j hcycle hne ↦ absurd (Equiv.Perm.sameCycle_one.mp hcycle) hne
  | E8 =>
    intro σ hσ
    rw [diagramSymmetry_E8_eq_bot, Subgroup.mem_bot] at hσ
    subst hσ
    exact Or.inl fun i j hcycle hne ↦ absurd (Equiv.Perm.sameCycle_one.mp hcycle) hne
  | E6 =>
    intro σ hσ
    exact Or.inl fun i j hcycle hne ↦ cartanMatrix_E6_eq_zero_of_sameCycle hσ hcycle hne
  | D n =>
    intro σ hσ
    exact Or.inl fun i j hcycle hne ↦
      cartanMatrix_D_eq_zero_of_sameCycle (valid_D.mp ht) hσ hcycle hne
  | A n =>
    intro σ hσ
    rcases mem_diagramSymmetry_A_iff.mp hσ with rfl | rfl
    · exact Or.inl fun i j hcycle hne ↦ absurd (Equiv.Perm.sameCycle_one.mp hcycle) hne
    · rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
      · have h1 : 1 ≤ n := valid_A.mp ht
        have hm_eq : n = 2 * m := by omega
        subst hm_eq
        exact Or.inr ⟨m, by omega, rfl, fun i ↦ graphPermA_apply (2 * m) i⟩
      · exact Or.inl fun i j hcycle hne ↦
          cartanMatrix_A_eq_zero_of_sameCycle_of_odd hodd (graphPermA_mem_diagramSymmetry n)
            hcycle hne

end TauCeti.DynkinType
