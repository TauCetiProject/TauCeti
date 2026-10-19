/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic

/-!
# A Nakayama lemma with weighted generators

Let `M` be a module over a commutative ring `R`, spanned by a finite family `b`, and let `I` be an
ideal. Mathlib's `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul` says that if
`M = I • M`, some `r ≡ 1 (mod I)` kills `M`. This file proves the weighted form: if `e i • b i`
lies in `I • M` for each `i`, then some `r ≡ ∏ᵢ e i (mod I)` kills `M`
(`Submodule.exists_sub_prod_mem_and_smul_eq_zero`). The case `e = 1` recovers Nakayama's lemma for
a finite spanning family.

The proof is the determinant trick: writing `e i • b i = ∑ⱼ θ i j • b j` with `θ i j ∈ I`, the
determinant of `diag e - θ` kills every `b k`, and it is `∏ᵢ e i` modulo `I`.

This is the commutative-algebra step of the proof, due to Artin and Tate, that the transfer of a
finite group into its commutator subgroup is trivial: there `R` is the integral group ring of a
finite abelian group, `I` its augmentation ideal and `e i` the orders of a basis of the group.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIII.
* D. Ferrand, *La démonstration par Artin–Tate du théorème de l'idéal principal* (2011), §2.
-/

public section

namespace Submodule

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]

/-- **Nakayama's lemma with weighted generators.** If `b` spans `M` and `e i • b i ∈ I • M` for
every `i`, then some `r ≡ ∏ᵢ e i (mod I)` kills `M`. -/
theorem exists_sub_prod_mem_and_smul_eq_zero (I : Ideal R) {b : ι → M}
    (hb : span R (Set.range b) = ⊤) (e : ι → R)
    (he : ∀ i, e i • b i ∈ I • (⊤ : Submodule R M)) :
    ∃ r : R, r - ∏ i, e i ∈ I ∧ ∀ m : M, r • m = 0 := by
  classical
  rw [← hb] at he
  choose θ hθI hθ using fun i ↦ (mem_ideal_smul_span_iff_exists_sum I b _).1 (he i)
  let A : Matrix ι ι R := Matrix.diagonal e - Matrix.of fun i j ↦ θ i j
  have hA : ∀ i, ∑ j, A i j • b j = 0 := fun i ↦ by
    simp only [A, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.of_apply, sub_smul, ite_smul,
      zero_smul, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [sub_eq_zero, ← hθ i]
    exact Finsupp.sum_fintype _ _ fun _ ↦ zero_smul R _
  refine ⟨A.det, ?_, fun m ↦ ?_⟩
  · -- Modulo `I`, the matrix `A` is the diagonal matrix of the weights.
    have hmap : (Ideal.Quotient.mk I).mapMatrix A = Matrix.diagonal (Ideal.Quotient.mk I ∘ e) := by
      ext i j
      by_cases h : i = j
      · subst h
        simp [A, (Ideal.Quotient.eq_zero_iff_mem).2 (hθI i i)]
      · simp [A, h, (Ideal.Quotient.eq_zero_iff_mem).2 (hθI i j)]
    rw [← Ideal.Quotient.eq, RingHom.map_det, hmap, Matrix.det_diagonal, map_prod]
    rfl
  · have hm : m ∈ span R (Set.range b) := hb ▸ mem_top
    induction hm using span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact A.det_smul_eq_zero_of_sum_smul_eq_zero hA k
    | zero => exact smul_zero _
    | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_comm, hx, smul_zero]

end Submodule
