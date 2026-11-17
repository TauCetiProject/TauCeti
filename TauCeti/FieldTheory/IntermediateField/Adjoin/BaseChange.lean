/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.SeparableClosure
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.FieldTheory.IntermediateField.ScalarTower

/-!
# Scalar extension of a simple algebraic field extension

For fields `K ⊆ L ⊆ Ω`, the inclusion `K(α) → L(α)` makes `L(α)` a field quotient of
`K(α) ⊗[K] L` when `α` is algebraic over `L`. This is the compositum description used to
base-change an extension while adjoining the same root to both fields. Regardless of whether `α` is
algebraic over `L`, `L(α)` is generated over `K(α)` by the image of `L`, the inclusion is
compatible with any common base ring `A` acting on `K`, `L`, and `Ω`, and finiteness and
separability of `L / K` pass to `L(α) / K(α)`.
-/

public section

open scoped TensorProduct

namespace TauCeti.IntermediateField

open _root_.IntermediateField

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]

/-- The canonical inclusion `K(α) → L(α)` induced by extending the coefficient field. -/
def adjoinBaseChange (α : Ω) : K⟮α⟯ →ₐ[K] L⟮α⟯ :=
  inclusion (adjoin_simple_le_iff.mpr (mem_adjoin_simple_self L α) :
    K⟮α⟯ ≤ (L⟮α⟯).restrictScalars K)

/-- Extending the coefficient field does not change the element of the ambient field. -/
@[simp]
theorem coe_adjoinBaseChange (α : Ω) (x : K⟮α⟯) :
    (adjoinBaseChange K L α x : Ω) = x :=
  (rfl)

/-- The canonical inclusion sends the distinguished generator to the distinguished generator. -/
@[simp]
theorem adjoinBaseChange_gen (α : Ω) :
    adjoinBaseChange K L α (AdjoinSimple.gen K α) = AdjoinSimple.gen L α :=
  (rfl)

/-- The canonical inclusion `K(α) → L(α)` is compatible with any base ring `A` forming scalar
towers `A → K → Ω` and `A → L → Ω`. -/
theorem isScalarTower_adjoinBaseChange (A : Type*) [CommSemiring A] [SMul A K] [SMul A L]
    [Algebra A Ω] [IsScalarTower A K Ω] [IsScalarTower A L Ω] (α : Ω) :
    letI := (adjoinBaseChange K L α).toAlgebra
    IsScalarTower A K⟮α⟯ L⟮α⟯ := by
  let := (adjoinBaseChange K L α).toAlgebra
  refine .of_algebraMap_eq fun a ↦ Subtype.ext ?_
  calc (algebraMap A L⟮α⟯ a : Ω)
      = algebraMap A Ω a := by
        rw [← IntermediateField.algebraMap_apply, ← IsScalarTower.algebraMap_apply A L⟮α⟯ Ω]
    _ = (algebraMap A K⟮α⟯ a : Ω) := by
        rw [← IntermediateField.algebraMap_apply, ← IsScalarTower.algebraMap_apply A K⟮α⟯ Ω]
    _ = (algebraMap K⟮α⟯ L⟮α⟯ (algebraMap A K⟮α⟯ a) : Ω) := by
        simp [RingHom.algebraMap_toAlgebra]

/-- Multiplication into the compositum, with its `K(α)`-algebra structure induced by the
canonical inclusion. -/
def adjoinBaseChangeTensorLift (α : Ω) :
    letI := (adjoinBaseChange K L α).toAlgebra
    K⟮α⟯ ⊗[K] L →ₐ[K⟮α⟯] L⟮α⟯ :=
  letI := (adjoinBaseChange K L α).toAlgebra
  Algebra.TensorProduct.lift (Algebra.ofId K⟮α⟯ L⟮α⟯)
    (IsScalarTower.toAlgHom K L L⟮α⟯) (fun _ _ ↦ Commute.all _ _)

/-- The compositum multiplication map sends a pure tensor to the product of its factors. -/
@[simp]
theorem adjoinBaseChangeTensorLift_tmul (α : Ω) (x : K⟮α⟯) (l : L) :
    adjoinBaseChangeTensorLift K L α (x ⊗ₜ[K] l) =
      adjoinBaseChange K L α x * algebraMap L L⟮α⟯ l := by
  let := (adjoinBaseChange K L α).toAlgebra
  exact Algebra.TensorProduct.lift_tmul _ _ _ x l

/-- If `α` is algebraic over `L`, multiplication maps `K(α) ⊗[K] L` onto `L(α)`. -/
theorem surjective_adjoinBaseChange_tensorProduct {α : Ω} (hα : IsIntegral L α) :
    Function.Surjective (adjoinBaseChangeTensorLift K L α) := by
  let := (adjoinBaseChange K L α).toAlgebra
  let φ := adjoinBaseChangeTensorLift K L α
  -- Regard the tensor-product image as an `L`-subalgebra, so the power basis applies.
  let S : Subalgebra L L⟮α⟯ :=
    { φ.range.toSubring with
      algebraMap_mem' := fun l ↦ ⟨1 ⊗ₜ[K] l, by simp [φ]⟩ }
  have hgen : AdjoinSimple.gen L α ∈ S :=
    ⟨AdjoinSimple.gen K α ⊗ₜ[K] 1, by simp [φ]⟩
  have htop : S = ⊤ := by
    apply top_unique
    rw [← (adjoin.powerBasis hα).adjoin_gen_eq_top,
      adjoin.powerBasis_gen]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hgen)
  intro x
  have hx : x ∈ S := htop ▸ Algebra.mem_top
  -- `S` retains the carrier of `φ.range`; only its coefficient algebra was changed.
  exact (AlgHom.mem_range φ).mp hx

/-- `L(α)` is generated over `K(α)` by the image of `L`. -/
theorem adjoin_range_algebraMap_adjoinBaseChange_eq_top (α : Ω) :
    letI := (adjoinBaseChange K L α).toAlgebra
    adjoin K⟮α⟯ (Set.range (algebraMap L L⟮α⟯)) = ⊤ := by
  let := (adjoinBaseChange K L α).toAlgebra
  let E : IntermediateField L L⟮α⟯ :=
    (adjoin K⟮α⟯ (Set.range (algebraMap L L⟮α⟯))).toSubfield.toIntermediateField fun l ↦
      (IntermediateField.mem_toSubfield _ _).mpr (subset_adjoin _ _ ⟨l, rfl⟩)
  have hgen : AdjoinSimple.gen L α ∈ E := by
    rw [← IntermediateField.mem_toSubfield, Subfield.toIntermediateField_toSubfield,
      IntermediateField.mem_toSubfield, ← adjoinBaseChange_gen K L α]
    exact IntermediateField.algebraMap_mem _ (AdjoinSimple.gen K α)
  have hE : E = ⊤ :=
    top_unique ((adjoin_adjoinSimple_gen_eq_top (F := L) α) ▸ adjoin_simple_le_iff.mpr hgen)
  refine IntermediateField.toSubfield_injective ?_
  calc (adjoin K⟮α⟯ (Set.range (algebraMap L L⟮α⟯))).toSubfield
      = E.toSubfield := (Subfield.toIntermediateField_toSubfield _ _).symm
    _ = ⊤ := by rw [hE, IntermediateField.top_toSubfield]
    _ = (⊤ : IntermediateField K⟮α⟯ L⟮α⟯).toSubfield := IntermediateField.top_toSubfield.symm

/-- If `L / K` is finite, then `L(α) / K(α)` is finite for any `α` in an overfield `Ω` of `L`. -/
theorem finiteDimensional_adjoinBaseChange [FiniteDimensional K L] (α : Ω) :
    letI := (adjoinBaseChange K L α).toAlgebra
    FiniteDimensional K⟮α⟯ L⟮α⟯ := by
  let := (adjoinBaseChange K L α).toAlgebra
  let φ := adjoinBaseChangeTensorLift K L α
  have : Module.Finite K⟮α⟯ φ.range :=
    Module.Finite.of_surjective φ.rangeRestrict.toLinearMap φ.rangeRestrict_surjective
  let E := φ.range.toIntermediateField'
    (isField_of_isIntegral_of_isField' (Field.toIsField K⟮α⟯))
  have htop : E = ⊤ :=
    top_unique <| adjoin_range_algebraMap_adjoinBaseChange_eq_top K L α ▸ adjoin_le_iff.mpr (by
      rintro _ ⟨l, rfl⟩
      rw [SetLike.mem_coe, ← IntermediateField.mem_toSubalgebra, toSubalgebra_toIntermediateField']
      exact (AlgHom.mem_range φ).mpr ⟨1 ⊗ₜ[K] l, by simp [φ]⟩)
  refine Module.Finite.of_surjective φ.toLinearMap fun x ↦ ?_
  have hx : x ∈ E := htop ▸ mem_top
  rw [← IntermediateField.mem_toSubalgebra, toSubalgebra_toIntermediateField'] at hx
  exact (AlgHom.mem_range φ).mp hx

/-- If `L / K` is separable, then `L(α) / K(α)` is separable for any `α` in an overfield `Ω` of
`L`. -/
theorem isSeparable_adjoinBaseChange [Algebra.IsSeparable K L] (α : Ω) :
    letI := (adjoinBaseChange K L α).toAlgebra
    Algebra.IsSeparable K⟮α⟯ L⟮α⟯ := by
  let := (adjoinBaseChange K L α).toAlgebra
  rw [← separableClosure.eq_top_iff]
  refine top_unique <| adjoin_range_algebraMap_adjoinBaseChange_eq_top K L α ▸ adjoin_le_iff.mpr ?_
  rintro _ ⟨l, rfl⟩
  exact mem_separableClosure_iff.mpr <|
    ((Algebra.IsSeparable.isSeparable K l).map (IsScalarTower.toAlgHom K L L⟮α⟯)
      (algebraMap L L⟮α⟯).injective).tower_top K⟮α⟯

end TauCeti.IntermediateField
