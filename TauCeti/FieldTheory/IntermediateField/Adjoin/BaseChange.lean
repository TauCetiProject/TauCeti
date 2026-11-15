/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Separable
import TauCeti.RingTheory.Unramified.Field

/-!
# Scalar extension of a simple algebraic field extension

For fields `K ⊆ L ⊆ Ω`, the inclusion `K(α) → L(α)` makes `L(α)` a field quotient of
`K(α) ⊗[K] L` when `α` is algebraic over `L`. This is the compositum description used to
base-change an extension while adjoining the same root to both fields; more generally, if `E` is
generated over `L` by the image of an element of `K₁` algebraic over `L` and `L / K` is finite and
separable, then `E / K₁` is finite and separable.

More generally, if an intermediate field `E` of `Ω / L` carries a compatible `F`-algebra structure
and contains `x`, then `F(x)` embeds in `E` as an `F`-algebra
(`TauCeti.IntermediateField.exists_adjoinSimple_algHom`), and in a tower `A → K → Ω` the generator
of `K(α)` is integral over `A` if and only if `α` is
(`TauCeti.IntermediateField.isIntegral_adjoinSimple_gen_iff`, specialized to `n`-th roots in
`TauCeti.IntermediateField.isIntegral_adjoinSimple_gen_of_pow_eq`).
-/

public section

open scoped TensorProduct

namespace TauCeti.IntermediateField

open _root_.IntermediateField

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

end AdjoinBaseChange

/-- If an intermediate field `E` of `Ω / L` carries an `F`-algebra structure compatible with `Ω` and
contains `x`, there is an `F`-algebra homomorphism `F⟮x⟯ →ₐ[F] E` preserving underlying elements of
`Ω`. -/
theorem exists_adjoinSimple_algHom
    {F L Ω : Type*} [Field F] [Field L] [Field Ω] [Algebra F Ω] [Algebra L Ω]
    {E : IntermediateField L Ω} [Algebra F E] [IsScalarTower F E Ω]
    {x : Ω} (hx : x ∈ E) :
    ∃ ι : F⟮x⟯ →ₐ[F] E, ∀ z : F⟮x⟯, (ι z : Ω) = z := by
  let EF : IntermediateField F Ω :=
    { E.toSubfield with
      algebraMap_mem' := fun c ↦ by
        rw [IsScalarTower.algebraMap_apply F E Ω]
        exact (algebraMap F E c).2 }
  have hle : F⟮x⟯ ≤ EF := adjoin_simple_le_iff.mpr hx
  refine ⟨{ toFun := fun z ↦ ⟨z.1, hle z.2⟩
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl
            commutes' := fun c ↦ Subtype.ext <| by
              simpa using IsScalarTower.algebraMap_apply F E Ω c },
    fun _ ↦ rfl⟩

/-- In a scalar tower `A → K → Ω` with `K` and `Ω` fields, the distinguished generator of `K⟮α⟯` is
integral over `A` if and only if `α` is integral over `A`. -/
@[simp]
theorem isIntegral_adjoinSimple_gen_iff
    {A K Ω : Type*} [CommRing A] [Field K] [Field Ω] [Algebra A K]
    [Algebra A Ω] [Algebra K Ω] [IsScalarTower A K Ω] (α : Ω) :
    IsIntegral A (AdjoinSimple.gen K α) ↔ IsIntegral A α := by
  have : IsScalarTower A K⟮α⟯ Ω := IsScalarTower.to₁₃₄ A K K⟮α⟯ Ω
  rw [← isIntegral_algebraMap_iff (A := K⟮α⟯) (B := Ω), AdjoinSimple.algebraMap_gen]

/-- If `α ^ n = algebraMap A Ω x` with `0 < n` in a tower `A → K → Ω`, then the generator of `K⟮α⟯`
is integral over `A`. -/
theorem isIntegral_adjoinSimple_gen_of_pow_eq
    {A K Ω : Type*} [CommRing A] [Field K] [Field Ω] [Algebra A K]
    [Algebra A Ω] [Algebra K Ω] [IsScalarTower A K Ω]
    {α : Ω} {n : ℕ} (hn : 0 < n) {x : A} (hα : α ^ n = algebraMap A Ω x) :
    IsIntegral A (AdjoinSimple.gen K α) :=
  (isIntegral_adjoinSimple_gen_iff (K := K) α).mpr
    (IsIntegral.of_pow hn (hα ▸ isIntegral_algebraMap (R := A)))

/-- If `E` is generated over `L` by the image of an element `α₀ : K₁` algebraic over `L`, then `E`
receives a surjective `K₁`-algebra homomorphism from `K₁ ⊗[K] L`. -/
theorem exists_surjective_tensorProduct_of_adjoin_eq_top
    {K K₁ L E : Type*} [Field K] [Field K₁] [Field L] [Field E]
    [Algebra K K₁] [Algebra K L] [Algebra K E] [Algebra K₁ E] [Algebra L E]
    [IsScalarTower K K₁ E] [IsScalarTower K L E]
    {α₀ : K₁} (hα : IsAlgebraic L (algebraMap K₁ E α₀))
    (hgen : L⟮algebraMap K₁ E α₀⟯ = ⊤) :
    ∃ ψ : K₁ ⊗[K] L →ₐ[K₁] E, Function.Surjective ψ := by
  let ψ : K₁ ⊗[K] L →ₐ[K₁] E :=
    Algebra.TensorProduct.lift (Algebra.ofId K₁ E) (IsScalarTower.toAlgHom K L E)
      fun _ _ ↦ .all _ _
  refine ⟨ψ, ?_⟩
  let S : Subalgebra L E :=
    { ψ.range.toSubring with
      algebraMap_mem' := fun l ↦ ⟨1 ⊗ₜ[K] l, by simp [ψ]⟩ }
  have hmem : algebraMap K₁ E α₀ ∈ S := ⟨α₀ ⊗ₜ[K] 1, by simp [ψ]⟩
  have hadj : Algebra.adjoin L ({algebraMap K₁ E α₀} : Set E) = ⊤ :=
    (adjoin_simple_eq_top_iff_of_isAlgebraic hα).mp hgen
  have htop : S = ⊤ := top_unique (hadj ▸ Algebra.adjoin_le (Set.singleton_subset_iff.mpr hmem))
  intro x
  have hx : x ∈ S := htop ▸ Algebra.mem_top
  exact (AlgHom.mem_range ψ).mp hx

/-- If `E` is generated over `L` by the image of an element `α₀ : K₁` algebraic over `L` and
`L / K` is finite and separable, then `E` is a finite separable extension of `K₁`. -/
theorem finiteDimensional_and_isSeparable_of_adjoin_eq_top
    {K K₁ L E : Type*} [Field K] [Field K₁] [Field L] [Field E]
    [Algebra K K₁] [Algebra K L] [Algebra K E] [Algebra K₁ E] [Algebra L E]
    [IsScalarTower K K₁ E] [IsScalarTower K L E]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {α₀ : K₁} (hα : IsAlgebraic L (algebraMap K₁ E α₀))
    (hgen : L⟮algebraMap K₁ E α₀⟯ = ⊤) :
    FiniteDimensional K₁ E ∧ Algebra.IsSeparable K₁ E := by
  obtain ⟨ψ, hψ⟩ := exists_surjective_tensorProduct_of_adjoin_eq_top (K := K) hα hgen
  exact ψ.finiteDimensional_and_isSeparable_of_surjective_of_isSeparable hψ

end TauCeti.IntermediateField
