/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
import TauCeti.Algebra.Group.Subgroup.Cover

/-!
# Primitive actions from blocks and chains of blocks

For a transitive group action, the blocks containing a chosen point are order-isomorphic to the
subgroups containing its stabilizer. This file applies that correspondence at the two ends of the
block lattice, and then along a chain of blocks.

A minimal non-singleton block gives a primitive action of its setwise stabilizer on the block.
A maximal proper block gives a maximal subgroup of the original group, and hence a primitive
action of the original group on the translates of the block. These are different actions: the
first resolves the action inside one block, while the second passes to the induced block system.

Both are ends of one statement. Covering relations among blocks containing `a` are exactly the
covering relations among their stabilizers, so the maximal chains of blocks `{a} = B₀ ⋖ ⋯ ⋖ Bₖ = X`
correspond to the maximal chains of subgroups from the stabilizer of `a` to `G` (as flags, this is
`Flag.map (MulAction.block_stabilizerOrderIso G a)`). At a step `Bᵢ ⋖ Bᵢ₊₁` the stabilizer of
`Bᵢ₊₁` acts primitively on the translates of `Bᵢ` contained in `Bᵢ₊₁`, and the cardinality of
`X` is the product of the degrees of these primitive actions. This is the chain of imprimitivity
along which a transitive group is built from primitive pieces.

## Main results

* `MulAction.IsBlock.isAtom_iff_stabilizer_covBy`: atomicity of a block is equivalent to its
  stabilizer covering the point stabilizer.
* `MulAction.IsBlock.isPreprimitive_stabilizer_of_isAtom`: the stabilizer of an atomic block acts
  primitively on that block.
* `MulAction.IsBlock.isCoatom_iff_isCoatom_stabilizer`: a block is coatomic exactly when its
  stabilizer is a maximal subgroup.
* `MulAction.IsBlock.isPreprimitive_orbit_of_isCoatom`: the action on the translates of a
  coatomic block is primitive.
* `MulAction.BlockMem.covBy_iff_stabilizer_covBy`: a block covers another exactly when its
  stabilizer covers the other's.
* `MulAction.IsBlock.mem_orbit_stabilizer_iff`: the translates of `B` by the stabilizer of a block
  `C ⊇ B` are the translates of `B` contained in `C`.
* `MulAction.BlockMem.isPreprimitive_stabilizer_orbit_of_covBy`: for blocks `B₁ ⋖ B₂`, the
  stabilizer of `B₂` acts primitively on the translates of `B₁` that it contains.
* `MulAction.BlockMem.natCard_eq_prod_ncard_orbit_stabilizer`: along a chain of blocks from `{a}`
  to `X`, the cardinality of `X` is the product of the numbers of translates at each step.

## References

* H. Wielandt, *Finite Permutation Groups*, Theorem 7.5.
* J. D. Dixon and B. Mortimer, *Permutation Groups*, Theorem 1.5A.
-/

public section

namespace TauCeti

open scoped Pointwise

open MulAction

variable {G X : Type*} [Group G] [MulAction G X] [IsPretransitive G X]
  {B : Set X} {a : X}

/-- For a transitive action, every point lies in exactly one translate of a nonempty block. -/
theorem _root_.MulAction.IsBlock.existsUnique_mem_orbit (hB : IsBlock G B) (hBne : B.Nonempty)
    (x : X) : ∃! C : orbit G B, x ∈ (C : Set X) := by
  obtain ⟨C, ⟨hC, hxC⟩, huniq⟩ := (hB.isBlockSystem hBne).1.2 x
  exact ⟨⟨C, hC⟩, hxC, fun D hxD ↦ Subtype.ext (huniq D ⟨D.2, hxD⟩)⟩

/-- A block `B` containing `a` is an atom in the block lattice exactly when its setwise stabilizer
covers the point stabilizer of `a`. -/
theorem _root_.MulAction.IsBlock.isAtom_iff_stabilizer_covBy
    (hB : IsBlock G B) (ha : a ∈ B) :
    IsAtom (⟨B, ha, hB⟩ : BlockMem G a) ↔
      stabilizer G a ⋖ stabilizer G B := by
  rw [covBy_iff_atom_Ici (hB.stabilizer_le ha)]
  exact (OrderIso.isAtom_iff (block_stabilizerOrderIso G a) ⟨B, ha, hB⟩).symm

/-- If `B` is a minimal non-singleton block containing `a`, then the setwise stabilizer of `B`
acts primitively on `B`.

Minimality is expressed by saying that `B` is an atom of `MulAction.BlockMem G a`. The bottom
element of this order is the singleton `{a}`, so atomicity also supplies the nontriviality of the
type `B` required by the point-stabilizer criterion for primitivity. -/
theorem _root_.MulAction.IsBlock.isPreprimitive_stabilizer_of_isAtom
    (hB : IsBlock G B) (ha : a ∈ B)
    (hmin : IsAtom (⟨B, ha, hB⟩ : BlockMem G a)) :
    IsPreprimitive (stabilizer G B) B := by
  have hcover : stabilizer G a ⋖ stabilizer G B :=
    (hB.isAtom_iff_stabilizer_covBy ha).mp hmin
  have hcoatom : IsCoatom ((stabilizer G a).subgroupOf (stabilizer G B)) :=
    hcover.isCoatom_subgroupOf
  have hB_ne : B ≠ {a} := by
    intro h
    apply hmin.ne_bot
    apply Subtype.ext
    rw [BlockMem.coe_bot]
    exact h
  let _ : Nontrivial B :=
    Set.Nontrivial.coe_sort ((Set.nontrivial_iff_ne_singleton ha).2 hB_ne)
  -- `B` is the orbit of `a` under `stabilizer G B`, so the action on `B` is transitive because
  -- the action on an orbit is; the two carriers differ only by the identification of the sets.
  let f : orbit (stabilizer G B) a →[stabilizer G B] (B : Set X) :=
    { toFun := fun x ↦ ⟨x, (hB.orbit_stabilizer_eq ha).subset x.2⟩
      map_smul' := fun _ _ ↦ rfl }
  let _ : IsPretransitive (stabilizer G B) B :=
    IsPretransitive.of_surjective_map (f := f)
      (fun y ↦ ⟨⟨y, (hB.orbit_stabilizer_eq ha).symm.subset y.2⟩, rfl⟩) inferInstance
  rw [← isCoatom_stabilizer_iff_preprimitive (stabilizer G B) ⟨a, ha⟩]
  convert hcoatom using 1
  ext g
  rw [mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_stabilizer_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- A block `B` containing `a` is a coatom in the block lattice exactly when its setwise
stabilizer is a maximal subgroup of `G`. -/
theorem _root_.MulAction.IsBlock.isCoatom_iff_isCoatom_stabilizer
    (hB : IsBlock G B) (ha : a ∈ B) :
    IsCoatom (⟨B, ha, hB⟩ : BlockMem G a) ↔
      IsCoatom (stabilizer G B) := by
  constructor
  · intro hmax
    have himage : IsCoatom
        (block_stabilizerOrderIso G a ⟨B, ha, hB⟩) :=
      (OrderIso.isCoatom_iff (block_stabilizerOrderIso G a) _).mpr hmax
    exact IsCoatom.of_isCoatom_coe_Ici himage
  · intro hmax
    apply (OrderIso.isCoatom_iff (block_stabilizerOrderIso G a) _).mp
    exact hmax.Ici (hB.stabilizer_le ha)

/-- If `B` is a maximal proper block containing `a`, then `G` acts primitively on the block
system formed by the translates of `B`.

The carrier of this action is the orbit of `B` for the pointwise action of `G` on `Set X`; its
elements are exactly the sets `g • B`. -/
theorem _root_.MulAction.IsBlock.isPreprimitive_orbit_of_isCoatom
    (hB : IsBlock G B) (ha : a ∈ B)
    (hmax : IsCoatom (⟨B, ha, hB⟩ : BlockMem G a)) :
    IsPreprimitive G (orbit G B) := by
  let b : orbit G B := ⟨B, mem_orbit_self B⟩
  have hcoatom : IsCoatom (stabilizer G B) :=
    (hB.isCoatom_iff_isCoatom_stabilizer ha).mp hmax
  have horbit_nontrivial : (orbit G B).Nontrivial := by
    rw [← Set.not_subsingleton_iff]
    intro hsub
    apply hcoatom.ne_top
    rw [eq_top_iff]
    intro g _
    rw [mem_stabilizer_iff]
    exact (subsingleton_orbit_iff_mem_fixedPoints.mp hsub) g
  let _ : Nontrivial (orbit G B) :=
    Set.Nontrivial.coe_sort horbit_nontrivial
  rw [← isCoatom_stabilizer_iff_preprimitive G b]
  convert hcoatom using 1
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-! ### Chains of blocks

Between the two extremal cases sits the general step. If `B ⋖ C` in the lattice of blocks
containing `a`, the setwise stabilizer of `C` permutes the translates of `B` contained in `C`, and
this action is primitive. Iterating along a chain `{a} = B 0 ⋖ B 1 ⋖ ⋯ ⋖ B k = X` of blocks
resolves the action into a tower of primitive actions, and the degree of the action is the product
of their degrees. -/

/-- A block covers another in the lattice of blocks containing `a` exactly when the setwise
stabilizer of the first covers that of the second in the subgroup lattice. -/
theorem _root_.MulAction.BlockMem.covBy_iff_stabilizer_covBy {B₁ B₂ : BlockMem G a} :
    B₁ ⋖ B₂ ↔ stabilizer G (B₁ : Set X) ⋖ stabilizer G (B₂ : Set X) := by
  rw [← apply_covBy_apply_iff (block_stabilizerOrderIso G a)]
  obtain ⟨B₁, ha₁, hB₁⟩ := B₁
  obtain ⟨B₂, ha₂, hB₂⟩ := B₂
  exact (Set.OrdConnected.apply_covBy_apply_iff
    (OrderEmbedding.subtype fun H : Subgroup G => stabilizer G a ≤ H)
    (by simpa only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype] using!
      Set.ordConnected_Ici)).symm

omit [IsPretransitive G X] in
/-- Let `B` be a subset of a block `C`. A set is a translate of `B` by the setwise stabilizer of
`C` exactly when it is a translate of `B` contained in `C`. -/
theorem _root_.MulAction.IsBlock.mem_orbit_stabilizer_iff {C D : Set X} (hC : IsBlock G C)
    (hBC : B ⊆ C) :
    D ∈ orbit (stabilizer G C) B ↔ D ∈ orbit G B ∧ D ⊆ C := by
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    refine ⟨⟨g, rfl⟩, ?_⟩
    beta_reduce
    rw [Subgroup.mk_smul, ← mem_stabilizer_iff.mp hg]
    exact Set.smul_set_mono hBC
  · rintro ⟨⟨g, rfl⟩, hgC⟩
    rcases B.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
    · exact ⟨1, by simp⟩
    have hg : g ∈ stabilizer G C :=
      hC.smul_eq_of_mem (hBC hb) (hgC (Set.smul_mem_smul_set hb))
    exact ⟨⟨g, hg⟩, rfl⟩

/-- If `B₁ ≤ B₂` are blocks containing `a`, then `B₂` is the disjoint union of the translates of
`B₁` by its setwise stabilizer, so its cardinality is that of `B₁` times their number. -/
theorem _root_.MulAction.BlockMem.ncard_mul_ncard_orbit_stabilizer_eq {B₁ B₂ : BlockMem G a}
    (h : B₁ ≤ B₂) :
    (B₁ : Set X).ncard * (orbit (stabilizer G (B₂ : Set X)) (B₁ : Set X)).ncard =
      (B₂ : Set X).ncard := by
  have hle : stabilizer G (B₁ : Set X) ≤ stabilizer G (B₂ : Set X) :=
    (block_stabilizerOrderIso G a).monotone h
  obtain ⟨B₁, ha₁, hB₁⟩ := B₁
  obtain ⟨B₂, ha₂, hB₂⟩ := B₂
  have key : (stabilizer G B₁).subgroupOf (stabilizer G B₂) =
      stabilizer (stabilizer G B₂) B₁ := by
    ext g
    rw [Subgroup.mem_subgroupOf, mem_stabilizer_iff, mem_stabilizer_iff, Subgroup.smul_def]
  rw [hB₁.ncard_block_eq_relIndex ha₁, hB₂.ncard_block_eq_relIndex ha₂, ← index_stabilizer,
    ← key, ← Subgroup.relIndex, Subgroup.relIndex_mul_relIndex _ _ _ (hB₁.stabilizer_le ha₁) hle]

/-- **The step of a chain of imprimitivity.** If `B₁ ⋖ B₂` in the lattice of blocks containing
`a`, then the setwise stabilizer of `B₂` acts primitively on the translates of `B₁` by its elements,
which are the translates of `B₁` contained in `B₂`
(`MulAction.IsBlock.mem_orbit_stabilizer_iff`).

For `B₁ = {a}` this is the primitive action of the stabilizer of an atomic block on that block,
`MulAction.IsBlock.isPreprimitive_stabilizer_of_isAtom`, read on singletons; for `B₂ = Set.univ`
it is the primitive action on the block system of a coatomic block,
`MulAction.IsBlock.isPreprimitive_orbit_of_isCoatom`. -/
theorem _root_.MulAction.BlockMem.isPreprimitive_stabilizer_orbit_of_covBy
    {B₁ B₂ : BlockMem G a} (h : B₁ ⋖ B₂) :
    IsPreprimitive (stabilizer G (B₂ : Set X))
      (orbit (stabilizer G (B₂ : Set X)) (B₁ : Set X)) := by
  have hcov := BlockMem.covBy_iff_stabilizer_covBy.mp h
  let b : orbit (stabilizer G (B₂ : Set X)) (B₁ : Set X) := ⟨B₁, mem_orbit_self _⟩
  have hnt : (orbit (stabilizer G (B₂ : Set X)) (B₁ : Set X)).Nontrivial := by
    rw [← Set.not_subsingleton_iff]
    intro hsub
    refine hcov.lt.not_ge fun g hg ↦ ?_
    exact (subsingleton_orbit_iff_mem_fixedPoints.mp hsub) ⟨g, hg⟩
  let _ : Nontrivial (orbit (stabilizer G (B₂ : Set X)) (B₁ : Set X)) := hnt.coe_sort
  rw [← isCoatom_stabilizer_iff_preprimitive (stabilizer G (B₂ : Set X)) b]
  convert hcov.isCoatom_subgroupOf using 1
  ext g
  rw [mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_stabilizer_iff]
  exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩

/-- Along a chain `B 0 ≤ B 1 ≤ ⋯ ≤ B k` of blocks containing `a`, the cardinality of the last
block is that of the first times the number of translates of `B i` by the stabilizer of `B (i + 1)`,
taken over all steps. -/
theorem _root_.MulAction.BlockMem.ncard_last_eq_mul_prod_ncard_orbit_stabilizer {k : ℕ}
    (B : Fin (k + 1) → BlockMem G a) (hB : Monotone B) :
    (B (Fin.last k) : Set X).ncard = (B 0 : Set X).ncard *
      ∏ i : Fin k, (orbit (stabilizer G (B i.succ : Set X)) (B i.castSucc : Set X)).ncard := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.prod_univ_castSucc, ← mul_assoc]
    simp only [Fin.succ_castSucc]
    have := ih (fun i ↦ B i.castSucc) (hB.comp Fin.strictMono_castSucc.monotone)
    simp only [Fin.castSucc_zero] at this
    rw [← this, Fin.succ_last]
    exact (BlockMem.ncard_mul_ncard_orbit_stabilizer_eq (hB (Fin.last k).castSucc_le_succ)).symm

/-- **The degree along a chain of imprimitivity.** For a chain
`{a} = B 0 ≤ B 1 ≤ ⋯ ≤ B k = X` of blocks containing `a`, the cardinality of `X` is the product
over the steps of the number of translates of `B i` by the stabilizer of `B (i + 1)`. When every
step is a cover these are the degrees of the primitive actions of
`MulAction.BlockMem.isPreprimitive_stabilizer_orbit_of_covBy`. -/
theorem _root_.MulAction.BlockMem.natCard_eq_prod_ncard_orbit_stabilizer {k : ℕ}
    (B : Fin (k + 1) → BlockMem G a) (hB : Monotone B) (h0 : B 0 = ⊥)
    (hk : B (Fin.last k) = ⊤) :
    Nat.card X =
      ∏ i : Fin k, (orbit (stabilizer G (B i.succ : Set X)) (B i.castSucc : Set X)).ncard := by
  have h := BlockMem.ncard_last_eq_mul_prod_ncard_orbit_stabilizer B hB
  rwa [h0, hk, BlockMem.coe_top, BlockMem.coe_bot, Set.ncard_univ, Set.ncard_singleton,
    one_mul] at h

end TauCeti
