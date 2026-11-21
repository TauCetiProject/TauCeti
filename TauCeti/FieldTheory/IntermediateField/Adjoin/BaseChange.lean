/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop

/-!
# Scalar extension of a generated field extension

For a tower `K → K₁ → E` and `K → L → E`, if `E` is generated over `L` by the image of a set
`s ⊆ K₁` of elements algebraic over `L`, then the canonical multiplication homomorphism
`K₁ ⊗[K] L →ₐ[K₁] E` is surjective
(`TauCeti.IntermediateField.surjective_productLeftAlgHom_of_adjoin_image_eq_top`). Conversely,
if a surjective `K₁`-algebra homomorphism `K₁ ⊗[K] L →ₐ[K₁] E` restricts to `algebraMap L E` on
`1 ⊗ l` and `s` generates `K₁` over `K`, then the image of `s` generates `E` over `L`
(`TauCeti.IntermediateField.adjoin_image_eq_top_of_surjective_tensorProduct`).

In particular, for fields `K ⊆ L ⊆ Ω`, the canonical inclusion `K(α) → L(α)` makes `L(α)` a field
quotient of `K(α) ⊗[K] L` whenever `α` is algebraic over `L`
(`TauCeti.IntermediateField.surjective_adjoinBaseChange_tensorProduct`).
-/

public section

open scoped TensorProduct

namespace TauCeti.IntermediateField

open _root_.IntermediateField

/-- If `E` is generated over `L` by the image of a set `s ⊆ K₁` whose elements are algebraic over
`L`, then the canonical multiplication homomorphism `K₁ ⊗[K] L →ₐ[K₁] E` is surjective. -/
theorem surjective_productLeftAlgHom_of_adjoin_image_eq_top (K : Type*) {K₁ L E : Type*}
    [CommSemiring K] [CommSemiring K₁] [Field L] [Field E]
    [Algebra K K₁] [Algebra K L] [Algebra K E] [Algebra K₁ E] [Algebra L E]
    [IsScalarTower K K₁ E] [IsScalarTower K L E]
    {s : Set K₁} (hs : ∀ x ∈ s, IsAlgebraic L (algebraMap K₁ E x))
    (hgen : IntermediateField.adjoin L (algebraMap K₁ E '' s) = ⊤) :
    Function.Surjective
      (Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K₁ E)
        (IsScalarTower.toAlgHom K L E)) := by
  let ψ := Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K₁ E)
    (IsScalarTower.toAlgHom K L E)
  -- Regard the range of `ψ` as an `L`-subalgebra containing `algebraMap K₁ E '' s`.
  let S : Subalgebra L E :=
    { ψ.range.toSubsemiring with
      algebraMap_mem' := fun l ↦ ⟨1 ⊗ₜ[K] l, by simp [ψ]⟩ }
  have hsub : algebraMap K₁ E '' s ⊆ S := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x ⊗ₜ[K] 1, by simp [ψ]⟩
  have hadj : Algebra.adjoin L (algebraMap K₁ E '' s) = ⊤ := by
    have h := congrArg IntermediateField.toSubalgebra hgen
    rwa [adjoin_toSubalgebra_of_isAlgebraic
      (by rintro _ ⟨x, hx, rfl⟩; exact hs x hx), IntermediateField.top_toSubalgebra] at h
  have htop : S = ⊤ := top_unique (hadj ▸ Algebra.adjoin_le hsub)
  intro x
  have hx : x ∈ S := htop ▸ Algebra.mem_top
  exact (AlgHom.mem_range ψ).mp hx

/-- If `φ : K₁ ⊗[K] L →ₐ[K₁] E` is a surjective `K₁`-algebra homomorphism sending `1 ⊗ l` to
`algebraMap L E l`, and `s` generates `K₁` over `K`, then the image of `s` generates `E` over
`L`. -/
theorem adjoin_image_eq_top_of_surjective_tensorProduct {K K₁ L E : Type*}
    [Field K] [Field K₁] [Field L] [Field E]
    [Algebra K K₁] [Algebra K L] [Algebra K E] [Algebra K₁ E] [Algebra L E]
    [IsScalarTower K K₁ E] [IsScalarTower K L E]
    (φ : K₁ ⊗[K] L →ₐ[K₁] E) (hφ : Function.Surjective φ)
    (hφL : ∀ l : L, φ (1 ⊗ₜ[K] l) = algebraMap L E l)
    {s : Set K₁} (hs : IntermediateField.adjoin K s = ⊤) :
    IntermediateField.adjoin L (algebraMap K₁ E '' s) = ⊤ := by
  have htop : IntermediateField.adjoin L (Set.range (IsScalarTower.toAlgHom K K₁ E)) = ⊤ := by
    refine eq_top_iff.mpr fun y _ ↦ ?_
    obtain ⟨t, rfl⟩ := hφ y
    refine TensorProduct.inductionOn t (fun k₁ l ↦ ?_)
      (fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy)
    rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, Algebra.smul_def, hφL]
    exact mul_mem (subset_adjoin L _ ⟨k₁, rfl⟩) (_root_.algebraMap_mem _ l)
  simpa [IsScalarTower.coe_toAlgHom'] using
    ((IsScalarTower.toAlgHom K K₁ E).adjoin_range_eq_adjoin_image (F := L) hs).symm.trans htop

section AdjoinBaseChange

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

/-- The `K(α)`-algebra structure on `L(α)` induced by `adjoinBaseChange` is compatible with the
inclusions into `Ω`. -/
theorem isScalarTower_adjoinBaseChange (α : Ω) :
    letI := (adjoinBaseChange K L α).toAlgebra
    IsScalarTower K⟮α⟯ L⟮α⟯ Ω :=
  letI := (adjoinBaseChange K L α).toAlgebra
  .of_algebraMap_eq fun _ ↦ by
    simp [RingHom.algebraMap_toAlgebra]

/-- Multiplication into the compositum, with its `K(α)`-algebra structure induced by the
canonical inclusion. -/
def adjoinBaseChangeTensorLift (α : Ω) :
    letI := (adjoinBaseChange K L α).toAlgebra
    K⟮α⟯ ⊗[K] L →ₐ[K⟮α⟯] L⟮α⟯ :=
  letI := (adjoinBaseChange K L α).toAlgebra
  Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K⟮α⟯ L⟮α⟯)
    (IsScalarTower.toAlgHom K L L⟮α⟯)

/-- The compositum multiplication map sends a pure tensor to the product of its factors. -/
@[simp]
theorem adjoinBaseChangeTensorLift_tmul (α : Ω) (x : K⟮α⟯) (l : L) :
    adjoinBaseChangeTensorLift K L α (x ⊗ₜ[K] l) =
      adjoinBaseChange K L α x * algebraMap L L⟮α⟯ l := by
  let := (adjoinBaseChange K L α).toAlgebra
  exact Algebra.TensorProduct.lift_tmul _ _ (fun _ _ ↦ .all _ _) x l

/-- If `α` is algebraic over `L`, multiplication maps `K(α) ⊗[K] L` onto `L(α)`. -/
theorem surjective_adjoinBaseChange_tensorProduct {α : Ω} (hα : IsAlgebraic L α) :
    Function.Surjective (adjoinBaseChangeTensorLift K L α) := by
  let := (adjoinBaseChange K L α).toAlgebra
  have : IsScalarTower K K⟮α⟯ L⟮α⟯ := IsScalarTower.of_algHom (adjoinBaseChange K L α)
  have hα' : IsAlgebraic L (AdjoinSimple.gen L α) :=
    ((AdjoinSimple.isIntegral_gen L α).mpr hα.isIntegral).isAlgebraic
  exact surjective_productLeftAlgHom_of_adjoin_image_eq_top K
    (K₁ := K⟮α⟯) (L := L) (E := L⟮α⟯) (s := {AdjoinSimple.gen K α})
    (by simpa [RingHom.algebraMap_toAlgebra] using hα')
    (by simp [RingHom.algebraMap_toAlgebra])

end AdjoinBaseChange

end TauCeti.IntermediateField
