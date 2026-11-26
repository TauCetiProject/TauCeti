/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Commutator
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Basic

/-!
# Commutators of pseudodifferential operators between bundles with multiplication operators

Let `P : Γ(E) → Γ(F)` be a classical pseudodifferential operator of order `m` between smooth
complex vector bundles over a manifold modelled on `ℝⁿ`
(`TauCeti.sectionClassicalPseudodifferentialOperators`), and `g` a complex-valued smooth function
on the base. Multiplication by `g` acts on the sections of both bundles, and the commutator

`[P, g] s = P (g s) - g P s`

(`TauCeti.smulCommutator`) has order `m - 1`
(`TauCeti.smulCommutator_mem_sectionClassicalPseudodifferentialOperators`). A matrix entry of an
operator between bundles (`TauCeti.sectionEntry`) is its frame coefficient applied to a cut-off
frame section multiplied by a scalar function, so the entries of `[P, g]` are the commutators of
the entries of `P` with multiplication by `g` (`TauCeti.sectionEntry_smulCommutator`). The scalar
theorem `TauCeti.smulCommutator_mem_classicalPseudodifferentialOperators` applies to each entry.
Multiplication by `g` acts by the scalar `g(x)` on each fibre, which is what lowers the order;
a commutator with a bundle endomorphism need not lose an order.

For smooth functions `gᵢ` with `∑ᵢ gᵢ² = 1`, the operator `s ↦ ∑ᵢ gᵢ P (gᵢ s)` is `P` up to order
`m - 2` (`TauCeti.sum_smul_comp_smul_sub_mem_sectionClassicalPseudodifferentialOperators`), since
it differs from `P` by `-½ ∑ᵢ [[P, gᵢ], gᵢ]` (`TauCeti.sub_sum_smul_comp_lsmul_eq`).
This is the bundle form of
`TauCeti.sum_mulLeft_comp_comp_mulLeft_sub_mem_classicalPseudodifferentialOperators`: localizing an
operator between bundles symmetrically over a square partition of unity changes it only at order
`m - 2`, and the commutators `[P, ψ]` with the cutoffs of a patching construction have order
`m - 1`.

## Main results

* `TauCeti.sectionEntry_smulCommutator`: the entries of `[P, g]` are the commutators of the
  entries of `P` with multiplication by `g`.
* `TauCeti.smulCommutator_mem_sectionClassicalPseudodifferentialOperators`: `[P, g]` has order
  `m - 1`.
* `TauCeti.sum_smul_comp_smul_sub_mem_sectionClassicalPseudodifferentialOperators`: square
  partitions of unity reproduce `P` up to order `m - 2`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, Theorem 18.1.8
  (the principal symbol of a commutator).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  [VectorBundle ℝ V E] [VectorBundle ℂ V E]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F]
  [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]

/-- **Entries of a commutator.** The matrix entry of the commutator `s ↦ P (g s) - g P s` of an
operator `P` between bundles with multiplication by a complex-valued smooth function `g` is the
commutator of the matrix entry of `P` with multiplication by `g`. -/
theorem sectionEntry_smulCommutator (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
    (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : V)
    (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']
    (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hχ : tsupport χ ⊆ t'.baseSet) (ℓ : W →L[ℂ] ℂ)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯)
    (P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯) :
    sectionEntry t ψ hψ v t' χ hχ ℓ (smulCommutator ℂ g P) =
      smulCommutator ℂ g (sectionEntry t ψ hψ v t' χ hχ ℓ P) := by
  ext f x
  simp [mul_smul]
  ring

variable [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℝ}
  {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}

/-- **Commutators with multiplication operators lose one order.** If `P` is a classical
pseudodifferential operator of order `m` between bundles and `g` a complex-valued smooth function
on the base, the commutator `s ↦ P (g s) - g P s` is a classical pseudodifferential operator of
order `m - 1`. -/
theorem smulCommutator_mem_sectionClassicalPseudodifferentialOperators
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    smulCommutator ℂ g P ∈ sectionClassicalPseudodifferentialOperators (m - 1) := by
  have hsub : smulCommutator ℂ g P = P ∘ₗ (g • LinearMap.id) - g • P := by
    ext s x
    simp
  refine mem_sectionClassicalPseudodifferentialOperators_iff.2
    ⟨?_, fun t _ ψ hψ v t' _ χ hχ ℓ ↦ ?_⟩
  · -- Proper support: `[P, g]` is the difference of two operators of order `m`.
    rw [hsub]
    exact (mem_sectionClassicalPseudodifferentialOperators_iff.1
      (sub_mem (comp_smul_mem_sectionClassicalPseudodifferentialOperators hP g)
        (smul_mem_sectionClassicalPseudodifferentialOperators hP g))).1
  · rw [sectionEntry_smulCommutator]
    exact smulCommutator_mem_classicalPseudodifferentialOperators
      ((mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).2 t ψ hψ v t' χ hχ ℓ) g

/-- **Square partitions reproduce an operator modulo order `m - 2`.** If `P` is a classical
pseudodifferential operator of order `m` between bundles and the complex-valued smooth functions
`gᵢ` satisfy `∑ᵢ gᵢ² = 1`, then `s ↦ ∑ᵢ gᵢ P (gᵢ s)` differs from `P` by an operator of order
`m - 2`, not only `m - 1`. -/
theorem sum_smul_comp_smul_sub_mem_sectionClassicalPseudodifferentialOperators
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) {ι : Type*} {s : Finset ι}
    {g : ι → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} (hg : ∑ i ∈ s, g i ^ 2 = 1) :
    ∑ i ∈ s, g i • (P ∘ₗ (g i • LinearMap.id)) - P ∈
      sectionClassicalPseudodifferentialOperators (m - 2) := by
  -- The difference is `-½ ∑ᵢ [[P, gᵢ], gᵢ]`, and each double commutator has order `m - 2`.
  have hmem : ∑ i ∈ s, smulCommutator ℂ (g i) (smulCommutator ℂ (g i) P) ∈
      sectionClassicalPseudodifferentialOperators (m - 2) :=
    Submodule.sum_mem _ fun i _ ↦ by
      simpa [sub_sub, one_add_one_eq_two] using
        smulCommutator_mem_sectionClassicalPseudodifferentialOperators
          (smulCommutator_mem_sectionClassicalPseudodifferentialOperators hP (g i)) (g i)
  -- Multiplication by `gᵢ` on sections is `Algebra.lsmul ℂ ℂ _ gᵢ`.
  have hcomp : ∑ i ∈ s, g i • (P ∘ₗ (g i • LinearMap.id)) =
      ∑ i ∈ s, g i • P ∘ₗ Algebra.lsmul ℂ ℂ _ (g i) := by
    simp only [Algebra.lsmul_eq_smul_one, Module.End.one_eq_id]
  rw [hcomp, ← neg_mem_iff, neg_sub, sub_sum_smul_comp_lsmul_eq hg]
  exact Submodule.smul_mem _ _ hmem

end TauCeti
