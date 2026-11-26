/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Prod
public import TauCeti.Analysis.Normed.Lp.PiLp
public import TauCeti.Topology.Algebra.Module.Equiv.Fin
public import TauCeti.Topology.Algebra.Module.Equiv.Pi

/-!
# Finite products of Fredholm operators

For a finite family of operators `T i : E i →L[𝕜] F i`, the coordinatewise operator
`ContinuousLinearMap.piMap T : (∀ i, E i) →L[𝕜] ∀ i, F i` is Fredholm exactly when every `T i` is.
The index type may be empty, in which case the product operator acts on zero spaces and is
Fredholm. A factor of a Fredholm product over any index type is Fredholm. The index of a finite
product with finite free kernels and cokernels, in particular of a finite product of Fredholm
operators, is the sum of the indices of the factors (`ContinuousLinearMap.index_piMap`).

The same holds for the block-diagonal operator `PiLp.piMap p T` on the `Lᵖ` products
`PiLp p E →L[𝕜] PiLp p F`, which is `ContinuousLinearMap.piMap T` transported along
`PiLp.continuousLinearEquiv`. For `p = 2` and Hilbert spaces `E i = F i` this is the orthogonal
direct sum `T₁ ⊕ ⋯ ⊕ Tᵣ` of operators on a finite Hilbert sum. For instance, a block operator
that is diagonal on a Hilbert sum of `r` spaces, with Fredholm diagonal blocks, is Fredholm and
has index the sum of the indices of its `r` diagonal blocks.

The binary case is `ContinuousLinearMap.isFredholm_prodMap_iff`. Splitting off the first
coordinate with `Fin.consEquivL` reduces a product over `Fin (n + 1)` to a binary product
(`ContinuousLinearMap.consEquivL_symm_comp_piMap`), and a finite index type is reindexed by
some `Fin n` (`ContinuousLinearMap.piCongrLeft_symm_comp_piMap`). As in the binary case, the
domains need only be topological additive groups and the scalars any nontrivially normed field;
the spaces need not be finite-dimensional or complete.

## Main declarations

* `ContinuousLinearMap.isFredholm_piMap_iff`: a finite product of operators is Fredholm if and
  only if every factor is.
* `ContinuousLinearMap.IsFredholm.of_piMap`: every factor of a Fredholm product is Fredholm.
* `PiLp.isFredholm_piMap_iff` and `PiLp.index_piMap`: the Fredholm criterion and the index
  formula for the block-diagonal operators `PiLp.piMap p T` on `Lᵖ` products, in particular on
  finite Hilbert sums.
-/

public section

open scoped ENNReal

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- A product over `Fin n` is Fredholm exactly when every factor is. -/
private theorem isFredholm_piMap_fin_iff {n : ℕ} {E F : Fin n → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, Module 𝕜 (E i)]
    [∀ i, IsTopologicalAddGroup (E i)]
    [∀ i, AddCommGroup (F i)] [∀ i, TopologicalSpace (F i)] [∀ i, Module 𝕜 (F i)]
    (T : ∀ i, E i →L[𝕜] F i) : IsFredholm (piMap T) ↔ ∀ i, IsFredholm (T i) := by
  induction n with
  | zero =>
    simpa [piMap_eq_of_isEmpty] using ContinuousLinearEquiv.isFredholm _
  | succ n ih =>
    rw [isFredholm_iff_of_comp_eq _ _ (consEquivL_symm_comp_piMap T), isFredholm_prodMap_iff, ih,
      Fin.forall_fin_succ]

variable {ι : Type*} {E F : ι → Type*}
variable [∀ i, AddCommGroup (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, Module 𝕜 (E i)]
variable [∀ i, IsTopologicalAddGroup (E i)]
variable [∀ i, AddCommGroup (F i)] [∀ i, TopologicalSpace (F i)] [∀ i, Module 𝕜 (F i)]

/-- A finite product of operators is Fredholm if and only if every factor is. -/
@[simp]
theorem isFredholm_piMap_iff [Finite ι] (T : ∀ i, E i →L[𝕜] F i) :
    IsFredholm (piMap T) ↔ ∀ i, IsFredholm (T i) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  rw [isFredholm_iff_of_comp_eq _ _ (piCongrLeft_symm_comp_piMap e.symm T),
    isFredholm_piMap_fin_iff]
  exact ⟨fun h i ↦ e.symm_apply_apply i ▸ h (e i), fun h k ↦ h _⟩

/-- A finite product of Fredholm operators is Fredholm. -/
theorem IsFredholm.piMap [Finite ι] {T : ∀ i, E i →L[𝕜] F i} (hT : ∀ i, IsFredholm (T i)) :
    IsFredholm (ContinuousLinearMap.piMap T) :=
  (isFredholm_piMap_iff T).2 hT

/-- If a product of operators is Fredholm, so is each factor. The index type may be infinite. -/
theorem IsFredholm.of_piMap {T : ∀ i, E i →L[𝕜] F i}
    (h : IsFredholm (ContinuousLinearMap.piMap T))
    (i : ι) : IsFredholm (T i) := by
  classical
  -- split the product into the coordinate `i` and the remaining coordinates
  let eE : (∀ j, E j) ≃L[𝕜] (∀ j : {j // j = i}, E j) × ∀ j : {j // ¬j = i}, E j :=
    (ContinuousLinearEquiv.piCongrLeft 𝕜 E (Equiv.sumCompl (· = i))).symm.trans
      (ContinuousLinearEquiv.sumPiEquivProdPi 𝕜 _ _ _)
  let eF : (∀ j, F j) ≃L[𝕜] (∀ j : {j // j = i}, F j) × ∀ j : {j // ¬j = i}, F j :=
    (ContinuousLinearEquiv.piCongrLeft 𝕜 F (Equiv.sumCompl (· = i))).symm.trans
      (ContinuousLinearEquiv.sumPiEquivProdPi 𝕜 _ _ _)
  have hcomm : (eF : (∀ j, F j) →L[𝕜] _) ∘L ContinuousLinearMap.piMap T =
      ((ContinuousLinearMap.piMap fun j : {j // j = i} ↦ T j).prodMap
        (ContinuousLinearMap.piMap fun j : {j // ¬j = i} ↦ T j)) ∘L (eE : (∀ j, E j) →L[𝕜] _) := by
    -- reindexing along `Equiv.sumCompl` commutes with `piMap`; `sumPiEquivProdPi` then reads the
    -- coordinates at `Sum.inl j` and `Sum.inr j` (`ContinuousLinearEquiv.sumPiEquivProdPi_apply`)
    have h := piCongrLeft_symm_comp_piMap (Equiv.sumCompl (· = i)) T
    ext x j
    exacts [congr($h x (.inl j)), congr($h x (.inr j))]
  exact (isFredholm_piMap_iff _).1 ((isFredholm_iff_of_comp_eq _ _ hcomm).1 h).of_prodMap_left
    ⟨i, rfl⟩

end ContinuousLinearMap

namespace PiLp

open ContinuousLinearMap

variable {𝕜 ι : Type*} {E F : ι → Type*} (p : ℝ≥0∞)

section Fredholm

variable [NontriviallyNormedField 𝕜]
variable [∀ i, AddCommGroup (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, Module 𝕜 (E i)]
variable [∀ i, IsTopologicalAddGroup (E i)]
variable [∀ i, AddCommGroup (F i)] [∀ i, TopologicalSpace (F i)] [∀ i, Module 𝕜 (F i)]

/-- A block-diagonal operator on finite `Lᵖ` products is Fredholm if and only if every block
is. -/
@[simp]
theorem isFredholm_piMap_iff [Finite ι] (T : ∀ i, E i →L[𝕜] F i) :
    IsFredholm (piMap p T) ↔ ∀ i, IsFredholm (T i) :=
  (isFredholm_iff_of_comp_eq _ _ (continuousLinearEquiv_comp_piMap p T)).trans
    (ContinuousLinearMap.isFredholm_piMap_iff T)

end Fredholm

variable [Ring 𝕜] [StrongRankCondition 𝕜] [Fintype ι]
variable [∀ i, AddCommGroup (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, Module 𝕜 (E i)]
variable [∀ i, AddCommGroup (F i)] [∀ i, TopologicalSpace (F i)] [∀ i, Module 𝕜 (F i)]

/-- The index of a block-diagonal operator on finite `Lᵖ` products whose blocks have finite free
kernels and cokernels, in particular whose blocks are Fredholm, is the sum of the indices of the
blocks. -/
@[simp]
theorem index_piMap (T : ∀ i, E i →L[𝕜] F i) [∀ i, Module.Free 𝕜 (T i).ker]
    [∀ i, Module.Finite 𝕜 (T i).ker] [∀ i, Module.Free 𝕜 (F i ⧸ (T i).range)]
    [∀ i, Module.Finite 𝕜 (F i ⧸ (T i).range)] :
    (piMap p T).index = ∑ i, (T i).index := by
  rw [← index_equiv_comp (piMap p T) (PiLp.continuousLinearEquiv p 𝕜 F),
    continuousLinearEquiv_comp_piMap, index_comp_equiv, ContinuousLinearMap.index_piMap]

end PiLp
