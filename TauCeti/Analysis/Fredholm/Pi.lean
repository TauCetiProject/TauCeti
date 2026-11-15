/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Prod
public import TauCeti.Analysis.Normed.Lp.PiLp
public import TauCeti.Topology.Algebra.Module.Equiv.Pi

/-!
# Finite products of Fredholm operators

For a finite family of operators `T i : E i →L[𝕜] F i`, the coordinatewise operator
`ContinuousLinearMap.piMap T : (∀ i, E i) →L[𝕜] ∀ i, F i` is Fredholm exactly when every `T i` is,
and then its index is the sum of the indices of the `T i`. The index type may be empty, in which
case the product operator acts on zero spaces, is Fredholm and has index `0`.

The same holds for the block-diagonal operator `PiLp.piMap p T` on the `Lᵖ` products
`PiLp p E →L[𝕜] PiLp p F`, which is `ContinuousLinearMap.piMap T` transported along
`PiLp.continuousLinearEquiv`. For `p = 2` and Hilbert spaces `E i = F i` this is the orthogonal
direct sum `T₁ ⊕ ⋯ ⊕ Tᵣ` of operators on a finite Hilbert sum. For instance, a block operator
that is diagonal on a Hilbert sum of `r` spaces has index the sum of the indices of its `r`
diagonal blocks.

The binary case is `ContinuousLinearMap.isFredholm_prodMap_iff` and
`ContinuousLinearMap.index_prodMap`. Splitting off the first coordinate with `Fin.consEquivL`
reduces a product over `Fin (n + 1)` to a binary product
(`ContinuousLinearMap.consEquivL_symm_comp_piMap`), and a finite index type is reindexed by
some `Fin n` (`ContinuousLinearMap.piCongrLeft_symm_comp_piMap`). As in the binary case, the
domains need only be topological additive groups and the scalars any nontrivially normed field;
the spaces need not be finite-dimensional or complete.

## Main declarations

* `ContinuousLinearMap.isFredholm_piMap_iff`: a finite product of operators is Fredholm if and
  only if every factor is.
* `ContinuousLinearMap.index_piMap`: the index of a finite product of Fredholm operators is the
  sum of their indices.
* `PiLp.isFredholm_piMap_iff` and `PiLp.index_piMap`: the same statements for the
  block-diagonal operators `PiLp.piMap p T` on `Lᵖ` products, in particular on finite Hilbert
  sums.
-/

public section

open scoped ENNReal

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section IsEmpty

variable {ι : Type*} [IsEmpty ι] {E F : ι → Type*}
variable [∀ i, AddCommGroup (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, Module 𝕜 (E i)]
variable [∀ i, AddCommGroup (F i)] [∀ i, TopologicalSpace (F i)] [∀ i, Module 𝕜 (F i)]

/-- Over an empty index type the product operator is the unique map between zero spaces, which
is a continuous linear equivalence. -/
private lemma piMap_eq_of_isEmpty (T : ∀ i, E i →L[𝕜] F i) :
    piMap T = ((ContinuousLinearEquiv.piCongrRight fun i ↦ isEmptyElim i :
      (∀ i, E i) ≃L[𝕜] ∀ i, F i) : (∀ i, E i) →L[𝕜] ∀ i, F i) := by
  ext x i
  exact isEmptyElim i

end IsEmpty

section Fredholm

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

/-- The index of a product over `Fin n` of Fredholm operators is the sum of their indices. -/
private theorem index_piMap_fin {n : ℕ} {E F : Fin n → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, Module 𝕜 (E i)]
    [∀ i, IsTopologicalAddGroup (E i)]
    [∀ i, AddCommGroup (F i)] [∀ i, TopologicalSpace (F i)] [∀ i, Module 𝕜 (F i)]
    {T : ∀ i, E i →L[𝕜] F i} (hT : ∀ i, IsFredholm (T i)) :
    (piMap T).index = ∑ i, (T i).index := by
  induction n with
  | zero => simp [piMap_eq_of_isEmpty]
  | succ n ih =>
    have hS : IsFredholm (piMap fun i : Fin n ↦ T i.succ) :=
      (isFredholm_piMap_fin_iff _).2 fun i ↦ hT i.succ
    have := (hT 0).finite_ker
    have := (hT 0).finite_coker
    have := hS.finite_ker
    have := hS.finite_coker
    rw [← index_equiv_comp (piMap T) (Fin.consEquivL 𝕜 F).symm, consEquivL_symm_comp_piMap,
      index_comp_equiv, index_prodMap, ih fun i ↦ hT i.succ, Fin.sum_univ_succ]

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

/-- If a finite product of operators is Fredholm, so is each factor. -/
theorem IsFredholm.of_piMap [Finite ι] {T : ∀ i, E i →L[𝕜] F i}
    (h : IsFredholm (ContinuousLinearMap.piMap T))
    (i : ι) : IsFredholm (T i) :=
  (isFredholm_piMap_iff T).1 h i

/-- The index of a finite product of Fredholm operators is the sum of their indices. -/
theorem index_piMap [Fintype ι] {T : ∀ i, E i →L[𝕜] F i} (hT : ∀ i, IsFredholm (T i)) :
    (piMap T).index = ∑ i, (T i).index := by
  let e := Fintype.equivFin ι
  rw [← index_equiv_comp (piMap T) (ContinuousLinearEquiv.piCongrLeft 𝕜 F e.symm).symm,
    piCongrLeft_symm_comp_piMap, index_comp_equiv, index_piMap_fin fun i ↦ hT _,
    e.symm.sum_comp fun i ↦ (T i).index]

end Fredholm

end ContinuousLinearMap

namespace PiLp

open ContinuousLinearMap

variable {𝕜 ι : Type*} {E F : ι → Type*} (p : ℝ≥0∞) [NontriviallyNormedField 𝕜]
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

/-- The index of a block-diagonal operator with Fredholm blocks on finite `Lᵖ` products is the
sum of the indices of the blocks. -/
theorem index_piMap [Fintype ι] {T : ∀ i, E i →L[𝕜] F i} (hT : ∀ i, IsFredholm (T i)) :
    (piMap p T).index = ∑ i, (T i).index := by
  rw [← index_equiv_comp (piMap p T) (PiLp.continuousLinearEquiv p 𝕜 F),
    continuousLinearEquiv_comp_piMap, index_comp_equiv, ContinuousLinearMap.index_piMap hT]

end PiLp
