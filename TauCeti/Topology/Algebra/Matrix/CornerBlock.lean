/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.CornerBlock

/-!
# Topology of block-diagonal matrices `diag(c, B)` and unitary corner blocks

For a topological space `α` with zero, the block-diagonal map
`(c, B) ↦ Matrix.cornerBlockSucc c B = diag(c, B)` from `α × Matrix (Fin m) (Fin m) α` to
`Matrix (Fin (m + 1)) (Fin (m + 1)) α` is continuous and has a continuous left inverse reading off
the `(0, 0)` corner and the `Fin.succ × Fin.succ` block, so it is a topological embedding
(`Matrix.isEmbedding_cornerBlockSucc`). When `α` is `T₁`, its image is cut out by the vanishing of
the off-diagonal entries in row `0` and column `0`, hence is closed
(`Matrix.isClosedEmbedding_cornerBlockSucc`).

Restricting to unitary elements over any topological star semiring `α` makes both
`Matrix.unitaryProdBlockSucc` (`(c, B) ↦ diag(c, B)`) and `Matrix.unitaryOneBlockSucc`
(`B ↦ diag(1, B)`) topological embeddings (`Matrix.isEmbedding_unitaryProdBlockSucc`,
`Matrix.isEmbedding_unitaryOneBlockSucc`), without any separation or compactness hypothesis on `α`.
In particular `Matrix.unitaryOneBlockSuccEquivRange` identifies `unitary (Matrix (Fin m) (Fin m) α)`
as a topological group with its image `(Matrix.unitaryOneBlockSucc α m).range`, the stabilizer of
`e₀`.

## Main definitions

* `Matrix.unitaryOneBlockSuccEquivRange`: the isomorphism of topological groups from
  `unitary (Matrix (Fin m) (Fin m) α)` onto `(Matrix.unitaryOneBlockSucc α m).range`.

## Main results

* `Continuous.matrix_cornerBlockSucc`, `ContinuousOn.matrix_cornerBlockSucc`: continuity of
  `diag(c x, B x)` in the entrywise matrix topology.
* `Matrix.isEmbedding_cornerBlockSucc`, `Matrix.isClosedEmbedding_cornerBlockSucc`: the map
  `(c, B) ↦ diag(c, B)` is an embedding, and a closed embedding when `α` is `T₁`.
* `Matrix.continuous_unitaryProdBlockSucc`, `Matrix.isEmbedding_unitaryProdBlockSucc`,
  `Matrix.continuous_unitaryOneBlockSucc`, `Matrix.isEmbedding_unitaryOneBlockSucc`: continuity and
  topological embedding properties of the unitary block-diagonal homomorphisms.
-/

public section

open Topology
open scoped Matrix

section CornerBlockContinuity

variable {X α : Type*} {m : ℕ} [TopologicalSpace X] [TopologicalSpace α] [Zero α]

/-- Entrywise continuity of the block-diagonal matrix `diag(c x, B x)`. -/
@[fun_prop]
theorem Continuous.matrix_cornerBlockSucc {c : X → α} {B : X → Matrix (Fin m) (Fin m) α}
    (hc : Continuous c) (hB : Continuous B) :
    Continuous fun x ↦ Matrix.cornerBlockSucc (c x) (B x) := by
  simp_rw [Matrix.cornerBlockSucc_def]
  exact ((hc.finCons continuous_const).finCons
    (continuous_pi fun i ↦ continuous_const.finCons ((continuous_apply i).comp hB))).matrixOf

/-- Continuity on a set of the block-diagonal matrix `diag(c x, B x)`. -/
theorem ContinuousOn.matrix_cornerBlockSucc {c : X → α} {B : X → Matrix (Fin m) (Fin m) α}
    {s : Set X} (hc : ContinuousOn c s) (hB : ContinuousOn B s) :
    ContinuousOn (fun x ↦ Matrix.cornerBlockSucc (c x) (B x)) s := by
  rw [continuousOn_iff_continuous_domRestrict] at hc hB ⊢
  exact hc.matrix_cornerBlockSucc hB

end CornerBlockContinuity

namespace Matrix

section Zero

variable {α : Type*} {m : ℕ} [TopologicalSpace α] [Zero α]

/-- The uncurried block-diagonal map `(c, B) ↦ diag(c, B)` is continuous. -/
@[fun_prop]
theorem continuous_cornerBlockSucc :
    Continuous fun p : α × Matrix (Fin m) (Fin m) α ↦ cornerBlockSucc p.1 p.2 :=
  continuous_fst.matrix_cornerBlockSucc continuous_snd

/-- The block-diagonal map `(c, B) ↦ diag(c, B)` is a topological embedding: reading off the
`(0, 0)` corner and the `Fin.succ × Fin.succ` block is a continuous left inverse. -/
theorem isEmbedding_cornerBlockSucc :
    IsEmbedding fun p : α × Matrix (Fin m) (Fin m) α ↦ cornerBlockSucc p.1 p.2 := by
  let r : Matrix (Fin (m + 1)) (Fin (m + 1)) α → α × Matrix (Fin m) (Fin m) α :=
    fun M ↦ (M 0 0, fun i j ↦ M i.succ j.succ)
  have hr : Continuous r :=
    ((continuous_apply 0).comp (continuous_apply 0)).prodMk
      (continuous_pi fun i ↦ continuous_pi fun j ↦
        (continuous_apply j.succ).comp (continuous_apply i.succ))
  have hleft : Function.LeftInverse r fun p : α × Matrix (Fin m) (Fin m) α ↦
      cornerBlockSucc p.1 p.2 :=
    fun ⟨c, B⟩ ↦ Prod.ext (cornerBlockSucc_zero_zero c B)
      (Matrix.ext fun i j ↦ cornerBlockSucc_succ_succ c B i j)
  exact hleft.isEmbedding hr continuous_cornerBlockSucc

/-- Over a `T₁` space, `(c, B) ↦ diag(c, B)` is a closed embedding: its image is cut out by the
vanishing of the off-diagonal entries in row `0` and column `0`. -/
theorem isClosedEmbedding_cornerBlockSucc [T1Space α] :
    IsClosedEmbedding fun p : α × Matrix (Fin m) (Fin m) α ↦ cornerBlockSucc p.1 p.2 := by
  refine ⟨isEmbedding_cornerBlockSucc, ?_⟩
  have hrange :
      (Set.range fun p : α × Matrix (Fin m) (Fin m) α ↦ cornerBlockSucc p.1 p.2) =
        (⋂ j : Fin m, (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) α ↦ M 0 j.succ) ⁻¹' {0}) ∩
          ⋂ i : Fin m, (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) α ↦ M i.succ 0) ⁻¹' {0} := by
    ext M
    simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      Set.mem_singleton_iff]
    refine ⟨?_, fun ⟨hrow, hcol⟩ ↦ ?_⟩
    · rintro ⟨⟨c, B⟩, rfl⟩
      exact ⟨cornerBlockSucc_zero_succ c B, cornerBlockSucc_succ_zero c B⟩
    · let B : Matrix (Fin m) (Fin m) α := fun i j ↦ M i.succ j.succ
      refine ⟨(M 0 0, B), (ext_fin_succ (cornerBlockSucc_zero_zero _ B).symm ?_ ?_
        fun i j ↦ (cornerBlockSucc_succ_succ _ B i j).symm).symm⟩
      · intro j
        exact (hrow j).trans (cornerBlockSucc_zero_succ _ B j).symm
      · intro i
        exact (hcol i).trans (cornerBlockSucc_succ_zero _ B i).symm
  rw [hrange]
  refine IsClosed.inter ?_ ?_
  · exact isClosed_iInter fun j ↦
      isClosed_singleton.preimage ((continuous_apply j.succ).comp (continuous_apply 0))
  · exact isClosed_iInter fun i ↦
      isClosed_singleton.preimage ((continuous_apply 0).comp (continuous_apply i.succ))

end Zero

section UnitaryBlock

variable {α : Type*} {m : ℕ} [Semiring α] [StarRing α] [TopologicalSpace α]

/-- The block-diagonal embedding `(c, B) ↦ diag(c, B)` on unitary elements is continuous. -/
@[fun_prop]
theorem continuous_unitaryProdBlockSucc : Continuous (unitaryProdBlockSucc α m) := by
  refine continuous_induced_rng.2 ?_
  have hcomp : Subtype.val ∘ unitaryProdBlockSucc α m =
      fun cB : unitary α × unitary (Matrix (Fin m) (Fin m) α) ↦
        cornerBlockSucc (cB.1 : α) cB.2.1 :=
    funext coe_unitaryProdBlockSucc
  rw [hcomp]
  exact (continuous_subtype_val.comp continuous_fst).matrix_cornerBlockSucc
    (continuous_subtype_val.comp continuous_snd)

/-- The block-diagonal embedding `(c, B) ↦ diag(c, B)` on unitary elements is a topological
embedding. -/
theorem isEmbedding_unitaryProdBlockSucc : IsEmbedding (unitaryProdBlockSucc α m) := by
  have hind : IsInducing (Subtype.val ∘ unitaryProdBlockSucc α m) := by
    have hcomp : Subtype.val ∘ unitaryProdBlockSucc α m =
        (fun p : α × Matrix (Fin m) (Fin m) α ↦ cornerBlockSucc p.1 p.2) ∘
          Prod.map Subtype.val Subtype.val :=
      funext coe_unitaryProdBlockSucc
    rw [hcomp]
    exact isEmbedding_cornerBlockSucc.isInducing.comp
      (IsInducing.subtypeVal.prodMap IsInducing.subtypeVal)
  exact ⟨IsInducing.subtypeVal.of_comp_iff.1 hind, unitaryProdBlockSucc_injective⟩

/-- The block-diagonal embedding `B ↦ diag(1, B)` on unitary matrices is continuous. -/
@[fun_prop]
theorem continuous_unitaryOneBlockSucc : Continuous (unitaryOneBlockSucc α m) := by
  have hcomp : ⇑(unitaryOneBlockSucc α m) = unitaryProdBlockSucc α m ∘ Prod.mk 1 :=
    funext unitaryOneBlockSucc_eq_unitaryProdBlockSucc
  rw [hcomp]
  exact continuous_unitaryProdBlockSucc.comp (continuous_const.prodMk continuous_id)

/-- The block-diagonal embedding `B ↦ diag(1, B)` on unitary matrices is a topological
embedding. -/
theorem isEmbedding_unitaryOneBlockSucc : IsEmbedding (unitaryOneBlockSucc α m) := by
  have hcomp : ⇑(unitaryOneBlockSucc α m) = unitaryProdBlockSucc α m ∘ Prod.mk 1 :=
    funext unitaryOneBlockSucc_eq_unitaryProdBlockSucc
  rw [hcomp]
  exact isEmbedding_unitaryProdBlockSucc.comp (isEmbedding_prodMkRight 1)

variable (α m) in
/-- **The block-diagonal embedding `B ↦ diag(1, B)` is an isomorphism of topological groups onto
its image**: `unitary (Matrix (Fin m) (Fin m) α)` is homeomorphically and multiplicatively
identified with `(Matrix.unitaryOneBlockSucc α m).range`. -/
noncomputable def unitaryOneBlockSuccEquivRange :
    unitary (Matrix (Fin m) (Fin m) α) ≃ₜ* (unitaryOneBlockSucc α m).range :=
  let e := MonoidHom.ofInjective (unitaryOneBlockSucc_injective (α := α) (m := m))
  ContinuousMulEquiv.mk'
    (e.toEquiv.toHomeomorphOfIsInducing
      ((isEmbedding_unitaryOneBlockSucc (α := α) (m := m)).isInducing.of_comp
        (continuous_unitaryOneBlockSucc.subtype_mk _) continuous_subtype_val))
    e.map_mul

@[simp]
theorem coe_unitaryOneBlockSuccEquivRange_apply (B : unitary (Matrix (Fin m) (Fin m) α)) :
    (unitaryOneBlockSuccEquivRange α m B : unitary (Matrix (Fin (m + 1)) (Fin (m + 1)) α)) =
      unitaryOneBlockSucc α m B := by
  simp [unitaryOneBlockSuccEquivRange, ContinuousMulEquiv.coe_mk',
    ← Homeomorph.coe_toEquiv, MonoidHom.ofInjective_apply]

@[simp]
theorem unitaryOneBlockSucc_unitaryOneBlockSuccEquivRange_symm_apply
    (A : (unitaryOneBlockSucc α m).range) :
    unitaryOneBlockSucc α m ((unitaryOneBlockSuccEquivRange α m).symm A) = A := by
  rw [← coe_unitaryOneBlockSuccEquivRange_apply, ContinuousMulEquiv.apply_symm_apply]

end UnitaryBlock

end Matrix
