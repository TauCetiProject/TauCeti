/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup
public import TauCeti.LinearAlgebra.Matrix.Unique

/-!
# Continuous equivalences of unitary matrices

Over any topological star semiring `α`:
* reindexing rows and columns along an equivalence `e : m ≃ n` induces an isomorphism of
  topological groups `Matrix.unitaryReindexContinuousMulEquiv` between `unitary (Matrix m m α)` and
  `unitary (Matrix n n α)`;
* for a singleton index type `m` (`[Unique m]`), reading off the unique entry via
  `Matrix.uniqueStarRingEquiv` induces an isomorphism of topological groups
  `Matrix.unitaryUniqueContinuousMulEquiv` between `unitary (Matrix m m α)` and `unitary α`.

Conjugation by a fixed unitary matrix and by its inverse are continuous for the
entrywise topology, giving a continuous linear equivalence on the matrix space.

Over a Hausdorff topological ring with continuous star, the unitary group
`Matrix.unitaryGroupOf A` of a Gram matrix `A`, the invertible matrices `g` with
`star g * A * g = A`, is a closed subgroup of the general linear group with the topology of units
(`Matrix.isClosed_unitaryGroupOf`). For invertible `A` it is also a closed subset of the matrices,
with the subspace topology (`Matrix.unitaryGroupOf.isClosedEmbedding_val`), since its inverse
`A⁻¹ * star g * A` is a continuous function of `g`.

## Main definitions

* `Matrix.unitaryReindexContinuousMulEquiv`: the isomorphism of topological groups
  `unitary (Matrix m m α) ≃ₜ* unitary (Matrix n n α)` induced by `e : m ≃ n`.
* `Matrix.unitaryUniqueContinuousMulEquiv`: the isomorphism of topological groups
  `unitary (Matrix m m α) ≃ₜ* unitary α` for `[Unique m]`.
* `Matrix.UnitaryGroup.conjStarAlgAutCLE`: the continuous linear equivalence induced by
  unitary conjugation on the matrix space.

## Main results

* `Matrix.isClosed_unitaryGroupOf`: `unitaryGroupOf A` is closed in `GL n R`.
* `Matrix.unitaryGroupOf.isClosedEmbedding_val`: for invertible `A`, the coercion of
  `unitaryGroupOf A` to the matrices is a closed embedding.
-/

public section

namespace Matrix

section Reindex

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (α : Type*) [Semiring α] [StarRing α] [TopologicalSpace α]

/-- Reindexing rows and columns along an equivalence `e : m ≃ n` induces an isomorphism of
topological groups between `unitary (Matrix m m α)` and `unitary (Matrix n n α)`. -/
def unitaryReindexContinuousMulEquiv (e : m ≃ n) :
    unitary (Matrix m m α) ≃ₜ* unitary (Matrix n n α) where
  __ := (Unitary.mapEquiv (.ofClass (reindexStarAlgEquiv ℕ α e))).toMulEquiv
  continuous_toFun := continuous_induced_rng.2 <|
    (continuous_subtypeVal.matrix_reindex e e).congr fun _ ↦ by
      simp
  continuous_invFun := continuous_induced_rng.2 <|
    (continuous_subtypeVal.matrix_reindex e.symm e.symm).congr fun _ ↦ by
      simp [← StarMulEquiv.toMulEquiv_symm]

variable {α} in
@[simp]
theorem coe_unitaryReindexContinuousMulEquiv_apply (e : m ≃ n) (A : unitary (Matrix m m α)) :
    (unitaryReindexContinuousMulEquiv α e A : Matrix n n α) = reindex e e A.val := by
  simp [unitaryReindexContinuousMulEquiv]

variable {α} in
@[simp]
theorem symm_unitaryReindexContinuousMulEquiv (e : m ≃ n) :
    (unitaryReindexContinuousMulEquiv α e).symm = unitaryReindexContinuousMulEquiv α e.symm :=
  ContinuousMulEquiv.ext fun _ ↦ (ContinuousMulEquiv.symm_apply_eq _).2 (Subtype.ext (by simp))

variable {α} in
@[simp]
theorem unitaryReindexContinuousMulEquiv_refl :
    unitaryReindexContinuousMulEquiv α (.refl m) = .refl _ :=
  ContinuousMulEquiv.ext fun _ ↦ Subtype.ext (by simp)

variable {α} in
@[simp]
theorem unitaryReindexContinuousMulEquiv_trans_unitaryReindexContinuousMulEquiv
    {o : Type*} [Fintype o] [DecidableEq o] (e : m ≃ n) (e' : n ≃ o) :
    (unitaryReindexContinuousMulEquiv α e).trans (unitaryReindexContinuousMulEquiv α e') =
      unitaryReindexContinuousMulEquiv α (e.trans e') :=
  ContinuousMulEquiv.ext fun _ ↦ Subtype.ext (by simp)

end Reindex

section Unique

variable (m α : Type*) [Fintype m] [DecidableEq m] [Unique m]
  [Semiring α] [StarRing α] [TopologicalSpace α]

/-- Reading off the unique entry identifies `1 × 1` unitary matrices over `α` with `unitary α` as
topological groups. -/
def unitaryUniqueContinuousMulEquiv : unitary (Matrix m m α) ≃ₜ* unitary α where
  __ := (Unitary.mapEquiv (.ofClass (uniqueStarRingEquiv (m := m) (A := α)))).toMulEquiv
  continuous_toFun := continuous_induced_rng.2 <| by
    have h : Continuous fun A : unitary (Matrix m m α) ↦ A.val default default :=
      (continuous_apply default).comp ((continuous_apply default).comp continuous_subtypeVal)
    exact h.congr fun _ ↦ by simp
  continuous_invFun := continuous_induced_rng.2 <| by
    have h : Continuous fun u : unitary α ↦ Matrix.of fun _ _ : m ↦ (u : α) :=
      continuous_pi fun _ ↦ continuous_pi fun _ ↦ continuous_subtypeVal
    exact h.congr fun _ ↦ by simp [← StarMulEquiv.toMulEquiv_symm]

variable {m α} in
@[simp]
theorem coe_unitaryUniqueContinuousMulEquiv_apply (A : unitary (Matrix m m α)) :
    (unitaryUniqueContinuousMulEquiv m α A : α) = A.val default default := by
  simp [unitaryUniqueContinuousMulEquiv]

variable {m α} in
@[simp]
theorem coe_unitaryUniqueContinuousMulEquiv_symm_apply (u : unitary α) :
    ((unitaryUniqueContinuousMulEquiv m α).symm u : Matrix m m α) =
      Matrix.of fun _ _ ↦ (u : α) := by
  ext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default,
    ← coe_unitaryUniqueContinuousMulEquiv_apply, ContinuousMulEquiv.apply_symm_apply,
    Matrix.of_apply]

end Unique

end Matrix

namespace Matrix.UnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommSemiring R] [StarRing R] [TopologicalSpace R]
  [ContinuousAdd R] [ContinuousMul R]

/-- Conjugation by a unitary matrix, as a continuous linear equivalence of the matrix space. -/
def conjStarAlgAutCLE (U : unitary (Matrix n n R)) :
    Matrix n n R ≃L[R] Matrix n n R where
  toLinearEquiv := (Unitary.conjStarAlgAut R _ U).toAlgEquiv.toLinearEquiv
  continuous_toFun := by
    -- The forgetful maps to a linear equivalence preserve the forward function.
    change Continuous fun A ↦ Unitary.conjStarAlgAut R _ U A
    simp only [Unitary.conjStarAlgAut_apply]
    exact (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun := by
    -- The forgetful maps also preserve the inverse function.
    change Continuous fun A ↦ (Unitary.conjStarAlgAut R _ U).symm A
    simp only [Unitary.conjStarAlgAut_symm_apply]
    exact (continuous_const.mul continuous_id).mul continuous_const

/-- The linear part of the continuous equivalence is the unitary conjugation automorphism. -/
theorem conjStarAlgAutCLE_toLinearEquiv (U : unitary (Matrix n n R)) :
    (conjStarAlgAutCLE U).toLinearEquiv = (Unitary.conjStarAlgAut R _ U).toAlgEquiv.toLinearEquiv :=
  (rfl)

/-- The continuous linear equivalence acts by unitary conjugation. -/
@[simp] theorem conjStarAlgAutCLE_apply (U : unitary (Matrix n n R))
    (A : Matrix n n R) : conjStarAlgAutCLE U A = Unitary.conjStarAlgAut R _ U A :=
  (rfl)

/-- Conjugation by the identity unitary is the identity continuous linear equivalence. -/
@[simp] theorem conjStarAlgAutCLE_one :
    conjStarAlgAutCLE (1 : unitary (Matrix n n R)) = ContinuousLinearEquiv.refl R _ := by
  apply ContinuousLinearEquiv.ext
  funext A
  simp only [conjStarAlgAutCLE_apply, map_one, StarAlgEquiv.one_apply,
    ContinuousLinearEquiv.refl_apply]

/-- Conjugating first by `U` and then by `V` is conjugation by `V * U`. -/
theorem conjStarAlgAutCLE_trans (U V : unitary (Matrix n n R)) :
    (conjStarAlgAutCLE U).trans (conjStarAlgAutCLE V) = conjStarAlgAutCLE (V * U) := by
  apply ContinuousLinearEquiv.ext
  funext A
  simp only [ContinuousLinearEquiv.trans_apply, conjStarAlgAutCLE_apply,
    Unitary.conjStarAlgAut_mul_apply]

/-- The inverse continuous linear equivalence is conjugation by the inverse unitary. -/
@[simp] theorem conjStarAlgAutCLE_symm (U : unitary (Matrix n n R)) :
    (conjStarAlgAutCLE U).symm = conjStarAlgAutCLE U⁻¹ := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  simp only [ContinuousLinearEquiv.toLinearEquiv_symm, conjStarAlgAutCLE_toLinearEquiv,
    ← AlgEquiv.toLinearEquiv_symm, ← StarAlgEquiv.toAlgEquiv_symm, Unitary.conjStarAlgAut_symm,
    Unitary.star_eq_inv]

end Matrix.UnitaryGroup

namespace Matrix

section UnitaryGroupOf

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `unitaryGroupOf A` is a closed subgroup of `GL n R`: it is cut out by the continuous equation
`star g * A * g = A`. -/
theorem isClosed_unitaryGroupOf {R : Type*} [CommRing R] [StarRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [ContinuousStar R] [T2Space R] (A : Matrix n n R) :
    IsClosed (unitaryGroupOf A : Set (GL n R)) := by
  have h : (unitaryGroupOf A : Set (GL n R)) =
      {g : GL n R | star (g : Matrix n n R) * A * g = A} :=
    Set.ext fun _ => mem_unitaryGroupOf_iff
  rw [h]
  exact isClosed_eq (((Units.continuous_val.star).matrix_mul continuous_const).matrix_mul
    Units.continuous_val) continuous_const

/-- **`unitaryGroupOf A` is a closed subset of the matrices**, for invertible `A`: the coercion to
matrices is a closed embedding. The topology of `GL n R` is that of the pair `(g, g⁻¹)`, and on
`unitaryGroupOf A` the inverse `A⁻¹ * star g * A` is a continuous function of `g`; the image is
cut out by the continuous equation `star M * A * M = A`, every solution of which is invertible. -/
theorem unitaryGroupOf.isClosedEmbedding_val {R : Type*} [CommRing R] [StarRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [ContinuousStar R] [T2Space R] {A : Matrix n n R}
    (hA : IsUnit A) :
    Topology.IsClosedEmbedding fun g : unitaryGroupOf A => ((g : GL n R) : Matrix n n R) := by
  have hc : Continuous fun g : unitaryGroupOf A => ((g : GL n R) : Matrix n n R) :=
    Units.continuous_val.comp continuous_subtypeVal
  have hrange : Set.range (fun g : unitaryGroupOf A => ((g : GL n R) : Matrix n n R)) =
      {M | star M * A * M = A} :=
    Set.ext fun M => ⟨fun ⟨g, hg⟩ => hg ▸ mem_unitaryGroupOf_iff.mp g.property,
      fun hM => ⟨ofMatrix hA M hM, val_ofMatrix hA M hM⟩⟩
  refine ⟨⟨Topology.IsInducing.of_comp hc
      (g := fun M : Matrix n n R => (M, MulOpposite.op (A⁻¹ * star M * A)))
      (continuous_id.prodMk (MulOpposite.continuous_op.comp
        ((continuous_const.matrix_mul continuous_id.star).matrix_mul continuous_const))) ?_,
    fun g h hgh => unitaryGroupOf.ext hgh⟩, ?_⟩
  · -- The composite is `g ↦ (g, g⁻¹)`, the inducing map defining the topology of `GL n R`.
    convert Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal using 1
    funext g
    simp [Units.embedProduct_apply, val_inv_of_mem_unitaryGroupOf hA g.property]
  · rw [hrange]
    exact isClosed_eq ((continuous_id.star.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const

end UnitaryGroupOf

end Matrix
