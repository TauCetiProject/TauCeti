/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.LinearDisjoint

/-!
# Split towers of fields

An intermediate field `E` splits a tower `L / M / K` if it is linearly disjoint from `M`
over `K` and their compositum is `L`. For algebraic towers this gives a multiplication
isomorphism `E ⊗[K] M ≃ₐ[M] L`. Conversely, such an isomorphism gives a splitting when
it extends the inclusion of `E` in `L`. The inclusion of `M` is built into the
`M`-algebra structure via the right tensor factor.

This is the split tower of Temkin, *Tame distillation and desingularization by p-alterations*,
Annals of Mathematics 186 (2017), §2.1.2. The multiplication isomorphism uses Mathlib's
`Subalgebra.LinearDisjoint.mulMapLeftOfSupEqTop`.
-/

public section

open scoped TensorProduct

namespace IntermediateField

variable {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
variable {E M : IntermediateField K L}

/-- An intermediate field `E` splits `L / M / K` if it is linearly disjoint from `M`
over `K` and the two generate `L` as a field. -/
@[mk_iff]
structure IsTowerSplitting (E M : IntermediateField K L) : Prop where
  /-- The complement `E` and the middle field `M` are linearly disjoint over `K`. -/
  linearDisjoint : E.LinearDisjoint M
  /-- The compositum of the complement and the middle field is the ambient field. -/
  sup_eq_top : E ⊔ M = ⊤

/-- The tower `L / M / K` is split if it has a splitting inside `L`. -/
def IsSplitTower (M : IntermediateField K L) : Prop :=
  ∃ E : IntermediateField K L, E.IsTowerSplitting M

/-- A tower is split exactly when some intermediate field is linearly disjoint from its
middle field over the base and their compositum is the ambient field. -/
theorem isSplitTower_iff :
    M.IsSplitTower ↔ ∃ E : IntermediateField K L, E.LinearDisjoint M ∧ E ⊔ M = ⊤ := by
  simp only [IsSplitTower, isTowerSplitting_iff]

/-- A tower with ambient field equal to its middle field splits over the bottom field. -/
@[simp]
theorem isSplitTower_top : (⊤ : IntermediateField K L).IsSplitTower :=
  ⟨⊥, .mk (LinearDisjoint.bot_left K L _) (bot_sup_eq _)⟩

/-- A `K`-algebra isomorphism of ambient fields transports a splitting to the image tower. -/
theorem IsTowerSplitting.map (h : E.IsTowerSplitting M) (f : L ≃ₐ[K] L') :
    (E.map f.toAlgHom).IsTowerSplitting (M.map f.toAlgHom) where
  linearDisjoint := h.linearDisjoint.map f.toAlgHom
  sup_eq_top := by
    rw [← map_sup, h.sup_eq_top, map_top]
    exact f.fieldRange_eq_top

/-- An isomorphism identifying the middle fields preserves and reflects split towers. -/
theorem isSplitTower_map_iff (f : L ≃ₐ[K] L') :
    (M.map f.toAlgHom).IsSplitTower ↔ M.IsSplitTower := by
  refine ⟨fun ⟨E', h⟩ ↦ ⟨E'.map f.symm.toAlgHom, ?_⟩, fun ⟨E, h⟩ ↦ ⟨_, h.map f⟩⟩
  simpa [map_map, map_id] using h.map f.symm

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open Algebra.TensorProduct

/-- A splitting gives the multiplication isomorphism over the middle field, provided at least
one factor is algebraic over the base. Here the middle field acts on the right tensor factor. -/
noncomputable def IsTowerSplitting.tensorProductAlgEquiv (h : E.IsTowerSplitting M)
    (halg : Algebra.IsAlgebraic K E ∨ Algebra.IsAlgebraic K M) : E ⊗[K] M ≃ₐ[M] L := by
  have hdisj := (linearDisjoint_iff'.1 h.linearDisjoint).symm
  have hsup : M.toSubalgebra ⊔ E.toSubalgebra = ⊤ := by
    rw [sup_comm, ← sup_toSubalgebra_of_isAlgebraic E M halg, h.sup_eq_top,
      top_toSubalgebra]
  exact (commRight K M E).symm.trans (hdisj.mulMapLeftOfSupEqTop hsup)

/-- The isomorphism of a split tower sends a pure tensor to the product of its factors. -/
@[simp]
theorem IsTowerSplitting.tensorProductAlgEquiv_tmul (h : E.IsTowerSplitting M)
    (halg : Algebra.IsAlgebraic K E ∨ Algebra.IsAlgebraic K M) (x : E) (y : M) :
    h.tensorProductAlgEquiv halg (x ⊗ₜ[K] y) = (x : L) * (y : L) := by
  rw [tensorProductAlgEquiv, AlgEquiv.trans_apply, commRight_symm_tmul,
    Subalgebra.LinearDisjoint.mulMapLeftOfSupEqTop_tmul, mul_comm]

/-- Restricting the multiplication isomorphism to the left factor gives its inclusion. -/
@[simp]
theorem IsTowerSplitting.tensorProductAlgEquiv_comp_includeLeft (h : E.IsTowerSplitting M)
    (halg : Algebra.IsAlgebraic K E ∨ Algebra.IsAlgebraic K M) :
    ((h.tensorProductAlgEquiv halg).toAlgHom.restrictScalars K).comp includeLeft = E.val := by
  ext x
  simp

/-- An isomorphism over the middle field that extends the inclusion of the left factor
exhibits that factor as a splitting. -/
theorem IsTowerSplitting.of_tensorProductAlgEquiv (e : E ⊗[K] M ≃ₐ[M] L)
    (he : (e.toAlgHom.restrictScalars K).comp includeLeft = E.val) :
    E.IsTowerSplitting M := by
  have hmul : e.toAlgHom.restrictScalars K = productMap E.val M.val := by
    apply Algebra.TensorProduct.ext'
    intro x y
    have hx : e (x ⊗ₜ[K] (1 : M)) = (x : L) := AlgHom.congr_fun he x
    have hy : e ((1 : E) ⊗ₜ[K] y) = (y : L) := by
      rw [← Algebra.TensorProduct.right_algebraMap_apply, e.commutes,
        IntermediateField.algebraMap_apply]
    calc
      e (x ⊗ₜ[K] y) = e ((x ⊗ₜ[K] 1) * (1 ⊗ₜ[K] y)) := by simp
      _ = _ := by
        rw [map_mul, hx, hy, productMap_apply_tmul, coe_val, coe_val]
  refine ⟨.of_isField (e.toMulEquiv.isField (Field.toIsField L)), ?_⟩
  have hrange : E.toSubalgebra ⊔ M.toSubalgebra = ⊤ := by
    rw [← E.range_val, ← M.range_val, ← productMap_range, ← hmul, AlgHom.range_eq_top]
    exact e.surjective
  apply toSubalgebra_injective
  exact top_unique (hrange ▸ le_sup_toSubalgebra E M)

/-- If the middle field is algebraic over the base, the tower splits exactly when the tensor
product of some intermediate field with the middle field is isomorphic to the ambient field
as an algebra over the middle field, with the left factor embedded by its given inclusion. -/
theorem isSplitTower_iff_exists_tensorProductAlgEquiv [Algebra.IsAlgebraic K M] :
    M.IsSplitTower ↔
      ∃ (E : IntermediateField K L) (e : E ⊗[K] M ≃ₐ[M] L),
        (e.toAlgHom.restrictScalars K).comp includeLeft = E.val := by
  exact ⟨fun ⟨E, h⟩ ↦ ⟨E, _, h.tensorProductAlgEquiv_comp_includeLeft (.inr inferInstance)⟩,
    fun ⟨E, e, he⟩ ↦ ⟨E, .of_tensorProductAlgEquiv e he⟩⟩

end IntermediateField
