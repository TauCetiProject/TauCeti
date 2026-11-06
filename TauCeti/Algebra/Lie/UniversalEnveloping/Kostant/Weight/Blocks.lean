/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.Order
public import TauCeti.LinearAlgebra.Matrix.LDU

/-!
# Weight-space blocks of Kostant root matrices

The block decomposition used in a Chevalley group's big cell is by distinct weights, not by
individual basis vectors or by their degrees. Equal-degree weights can be different, and a
weight space can have dimension greater than one. `orderedWeightBlock` numbers the distinct
weights by decreasing degree and assigns each basis vector the number of its weight. Its fibres
are exactly the weight spaces' basis indices.

A root of positive degree acts by block upper unitriangular matrices for this ranking: every
positive divided power moves to an earlier weight block, and the constant term acts as the
identity on each entire diagonal block. Negative-degree roots are block lower unitriangular.
These statements hold over every commutative ring and use `Matrix.BlockUnitriangular`, so that
the block `LDU` factorization and its leading-minor criteria apply to these actual weight blocks.
No faithfulness after reduction or generation of all points is assumed.

The numbering reuses `orderedWeightIndexEquiv`, now on the finite set of distinct weights.
The exponential calculation reuses the finite divided-power expansion of
`kostantRootSubgroupMatrix_eq_sum`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 5, Theorem 7.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

section Blocks

variable {κ η D : Type*} [Finite η]
variable [AddCommGroup D] [LinearOrder D]

private noncomputable def weightBlockEquiv (degree : (κ → ℤ) →+ D)
    (wt : η → κ → ℤ) : Set.range wt ≃ Fin (Nat.card (Set.range wt)) := by
  classical
  letI := Fintype.ofFinite (Set.range wt)
  exact (orderedWeightIndexEquiv degree (fun μ : Set.range wt => μ.val)).trans
    (finCongr (Nat.card_eq_fintype_card (α := Set.range wt)).symm)

/-- The weight-space block containing a basis index, with distinct weights numbered by decreasing
`degree`. Weights of equal degree are ordered by an arbitrary finite numbering. -/
noncomputable def orderedWeightBlock (degree : (κ → ℤ) →+ D) (wt : η → κ → ℤ)
    (x : η) : Fin (Nat.card (Set.range wt)) :=
  weightBlockEquiv degree wt ⟨wt x, ⟨x, rfl⟩⟩

/-- Two basis indices belong to the same weight block exactly when their weights are equal. -/
@[simp]
theorem orderedWeightBlock_eq_iff (degree : (κ → ℤ) →+ D) (wt : η → κ → ℤ) {r s : η} :
    orderedWeightBlock degree wt r = orderedWeightBlock degree wt s ↔ wt r = wt s := by
  constructor
  · intro hrs
    exact congrArg Subtype.val ((weightBlockEquiv degree wt).injective hrs)
  · intro hrs
    exact congrArg (weightBlockEquiv degree wt) (Subtype.ext hrs)

/-- Every numbered weight block contains a basis index. This includes the empty-family case,
where both the index type and the type of block numbers are empty. -/
theorem orderedWeightBlock_surjective (degree : (κ → ℤ) →+ D) (wt : η → κ → ℤ) :
    Function.Surjective (orderedWeightBlock degree wt) := by
  intro k
  obtain ⟨μ, hμ⟩ := (weightBlockEquiv degree wt).surjective k
  obtain ⟨x, hx⟩ := μ.property
  exact ⟨x, (congrArg (weightBlockEquiv degree wt) (Subtype.ext hx)).trans hμ⟩

/-- The cardinality cast in the block numbering preserves the underlying natural number. -/
private theorem orderedWeightBlock_val (degree : (κ → ℤ) →+ D) (wt : η → κ → ℤ)
    (x : η) :
    (orderedWeightBlock degree wt x).val =
      letI := Fintype.ofFinite (Set.range wt)
      (orderedWeightIndexEquiv degree (fun μ : Set.range wt => μ.val) ⟨wt x, x, rfl⟩).val := by
  classical
  simp only [orderedWeightBlock, weightBlockEquiv, Equiv.trans_apply, finCongr_apply_coe]

/-- A strictly larger degree places a weight space strictly earlier in the block ranking. -/
theorem orderedWeightBlock_lt_of_degree_lt (degree : (κ → ℤ) →+ D) (wt : η → κ → ℤ)
    {r s : η} (hrs : degree (wt s) < degree (wt r)) :
    orderedWeightBlock degree wt r < orderedWeightBlock degree wt s := by
  classical
  let _ := Fintype.ofFinite (Set.range wt)
  rw [Fin.lt_def, orderedWeightBlock_val, orderedWeightBlock_val]
  exact Fin.lt_def.mp (orderedWeightIndexEquiv_lt_of_degree_lt degree
    (fun μ : Set.range wt => μ.val) (r := ⟨wt r, r, rfl⟩) (s := ⟨wt s, s, rfl⟩) hrs)

variable [IsOrderedAddMonoid D]

/-- Adding a positive multiple of a positive-degree root moves to an earlier weight block. -/
theorem orderedWeightBlock_lt_of_eq_add_nsmul (degree : (κ → ℤ) →+ D) (wt : η → κ → ℤ)
    {α : κ → ℤ} (hα : 0 < degree α) {r s : η} {n : ℕ} (hn : 0 < n)
    (hrs : wt r = wt s + n • α) :
    orderedWeightBlock degree wt r < orderedWeightBlock degree wt s := by
  apply orderedWeightBlock_lt_of_degree_lt degree wt
  rw [hrs, map_add, map_nsmul]
  exact lt_add_of_pos_right _ (nsmul_pos hα hn.ne')

end Blocks

section RootMatrices

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ η : Type*} [Fintype η] [DecidableEq η]
variable {V : Type v} [AddCommGroup V] [Module ℚ V]
variable {D : Type*} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
variable (b : Module.Basis η ℤ M) (wt : η → κ → ℤ) (degree : (κ → ℤ) →+ D)
variable (i : ι) (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {α : κ → ℤ}
variable (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
variable (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)

include hwt hα in
/-- A positive-degree root subgroup is upper unitriangular in its weight-space blocks over every
commutative ring. The blocks are indexed by distinct weights even when some have equal degree. -/
theorem blockUnitriangular_kostantRootSubgroupMatrix {A : Type*} [CommRing A]
    (hdegree : 0 < degree α) (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ((kostantRootSubgroupMatrix e h ρ M hM i hnil b f : Matrix η η A)).BlockUnitriangular
      (orderedWeightBlock degree wt) := by
  apply Matrix.blockUnitriangular_of_apply_eq_one_apply_of_not_lt
  intro r s hrs
  exact kostantRootSubgroupMatrix_apply_eq_one_apply_of_forall_weight_ne
    e h ρ M hM b wt i hnil hwt hα f fun n hn heq =>
      hrs (orderedWeightBlock_lt_of_eq_add_nsmul degree wt hdegree hn heq)

include hwt hα in
/-- A negative-degree root subgroup is lower unitriangular for the same weight-space blocks used
by the positive roots. Reversing the ranking does not renumber the blocks or change their fibres. -/
theorem blockUnitriangular_toDual_kostantRootSubgroupMatrix {A : Type*} [CommRing A]
    (hdegree : degree α < 0) (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ((kostantRootSubgroupMatrix e h ρ M hM i hnil b f : Matrix η η A)).BlockUnitriangular
      (OrderDual.toDual ∘ orderedWeightBlock degree wt) := by
  apply Matrix.blockUnitriangular_of_apply_eq_one_apply_of_not_lt
  intro r s hrs
  exact kostantRootSubgroupMatrix_apply_eq_one_apply_of_forall_weight_ne
    e h ρ M hM b wt i hnil hwt hα f fun n hn heq =>
      hrs (by
        simp only [Function.comp_apply, OrderDual.toDual_lt_toDual]
        exact orderedWeightBlock_lt_of_eq_add_nsmul degree wt
          (α := -α) (by simpa using neg_pos.mpr hdegree) (r := s) (s := r) hn
          (by simp [heq]))

end RootMatrices

end TauCeti.UniversalEnvelopingAlgebra
