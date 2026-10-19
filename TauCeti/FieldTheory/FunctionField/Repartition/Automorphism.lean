/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.FieldTheory.FunctionField.Divisor.Automorphism
public import TauCeti.FieldTheory.FunctionField.Repartition.Basic

/-!
# The automorphism group acting on repartitions

Let `F' / F` be an extension of fields and `k` a subfield of `F`. An `F`-automorphism `σ` of
`F'` permutes the places of `F' / k` (`TauCeti.Place.instMulActionAlgEquiv`) and moves functions,
so it moves families of functions indexed by the places: the family `a` goes to

`(σ • a) Q = σ (a (σ⁻¹ • Q))`,

whose entry at `σ • P` is `σ (a P)`. This is a `k`-linear representation of `F' ≃ₐ[F] F'` on
`Place k F' → F'`. Because `σ` carries the valuation at `P` to the valuation at `σ • P`, it is
compatible with every piece of structure from which Weil differentials are built: it preserves the
repartition space `A_F`, carries the filtration step `A_F(D)` onto `A_F(σ • D)`, preserves the
diagonal copy of `F'`, is semilinear for multiplication by functions, and moves the repartition
`ι_P x` supported at one place to `ι_{σ • P} (σ x)`.

The restriction to `A_F` is the representation whose dual gives the action of the automorphism
group on Weil differentials, in
`TauCeti.FieldTheory.FunctionField.Differential.Automorphism`.

## Main definitions

* `TauCeti.placeFamilyRepresentation`: the representation of `F' ≃ₐ[F] F'` on the families
  `Place k F' → F'`, `(σ • a) Q = σ (a (σ⁻¹ • Q))`.
* `TauCeti.repartitionRepresentation`: its restriction to the repartition space `A_F`.

## Main results

* `TauCeti.placeFamilyRepresentation_mem_repartitionSpace_iff`: the action preserves `A_F`.
* `TauCeti.placeFamilyRepresentation_mem_adeleFiltration_smul_iff`: it carries `A_F(D)` onto
  `A_F(σ • D)`.
* `TauCeti.placeFamilyRepresentation_mem_diagonalRepartitions_iff` and
  `TauCeti.placeFamilyRepresentation_const`: it preserves the constant families, acting on their
  value by `σ`.
* `TauCeti.placeFamilyRepresentation_smul` and `TauCeti.repartitionRepresentation_repartitionMul`:
  it is `σ`-semilinear for multiplication by a function.
* `TauCeti.repartitionRepresentation_singleRepartition`: `σ • ι_P x = ι_{σ • P} (σ x)`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.5 for repartitions and Section III.5 for the automorphism action on places.
-/

public section

namespace TauCeti

open AlgebraicGeometry

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']

/-! ### The action on families indexed by the places -/

variable (k F F') in
/-- **The automorphism group acting on families indexed by the places**: `σ` sends a family `a`
to the family whose entry at `Q` is `σ (a (σ⁻¹ • Q))`, so the entry `a P` is moved by `σ` to the
place `σ • P`. It is `k`-linear because `σ` fixes `F`, hence `k`, pointwise. -/
noncomputable def placeFamilyRepresentation :
    Representation k (F' ≃ₐ[F] F') (Place k F' → F') where
  toFun σ := LinearMap.pi fun Q ↦ (σ.restrictScalars k).toLinearMap ∘ₗ LinearMap.proj (σ⁻¹ • Q)
  map_one' := LinearMap.ext fun a ↦ funext fun Q ↦ by simp
  map_mul' σ τ := LinearMap.ext fun a ↦ funext fun Q ↦ by simp [mul_smul]

variable (σ : F' ≃ₐ[F] F')

/-- The defining formula `(σ • a) Q = σ (a (σ⁻¹ • Q))` of the action on families. -/
@[simp]
theorem placeFamilyRepresentation_apply (a : Place k F' → F') (Q : Place k F') :
    placeFamilyRepresentation k F F' σ a Q = σ (a (σ⁻¹ • Q)) :=
  (rfl)

/-- **The action carries `A_F(D)` onto `A_F(σ • D)`**: `σ` moves the valuation at a place to the
valuation at the moved place, where the bound imposed by `σ • D` is the one `D` imposed before. -/
@[simp high]
theorem placeFamilyRepresentation_mem_adeleFiltration_smul_iff {D : Divisor k F'}
    {a : Place k F' → F'} :
    placeFamilyRepresentation k F F' σ a ∈ adeleFiltration (σ • D) ↔ a ∈ adeleFiltration D := by
  simp only [mem_adeleFiltration_iff, placeFamilyRepresentation_apply, WeilDivisor.coeff_smul]
  constructor
  · intro h P
    simpa using h (σ • P)
  · intro h Q
    have hQ := h (σ⁻¹ • Q)
    rwa [Place.valuation_smul, AlgEquiv.aut_inv, AlgEquiv.symm_symm] at hQ

/-- **The action preserves the repartition space**: a family is integral at all but finitely many
places exactly when its image is, because both are bounded by some divisor and the action moves
the bounding divisor.

This is not `@[simp]`: `TauCeti.mem_repartitionSpace_iff` is, and it rewrites this left-hand side
first. -/
theorem placeFamilyRepresentation_mem_repartitionSpace_iff {a : Place k F' → F'} :
    placeFamilyRepresentation k F F' σ a ∈ repartitionSpace k F' ↔ a ∈ repartitionSpace k F' := by
  constructor
  · intro h
    obtain ⟨D, hD⟩ := exists_mem_adeleFiltration h
    rw [← smul_inv_smul σ D, placeFamilyRepresentation_mem_adeleFiltration_smul_iff] at hD
    exact adeleFiltration_le_repartitionSpace _ hD
  · intro h
    obtain ⟨D, hD⟩ := exists_mem_adeleFiltration h
    exact adeleFiltration_le_repartitionSpace _
      ((placeFamilyRepresentation_mem_adeleFiltration_smul_iff σ).mpr hD)

/-- The action on a constant family applies `σ` to its value. -/
@[simp]
theorem placeFamilyRepresentation_const (f : F') :
    placeFamilyRepresentation k F F' σ (Function.const (Place k F') f) =
      Function.const (Place k F') (σ f) :=
  funext fun _ ↦ by simp

/-- **The action preserves the diagonal copy of `F'`**: a family is constant exactly when its image
is. -/
@[simp]
theorem placeFamilyRepresentation_mem_diagonalRepartitions_iff {a : Place k F' → F'} :
    placeFamilyRepresentation k F F' σ a ∈ diagonalRepartitions k F' ↔
      a ∈ diagonalRepartitions k F' := by
  simp only [mem_diagonalRepartitions_iff]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨σ⁻¹ f, ?_⟩
    rw [← placeFamilyRepresentation_const, hf, Representation.inv_self_apply]
  · rintro ⟨f, rfl⟩
    exact ⟨σ f, (placeFamilyRepresentation_const σ f).symm⟩

/-- **The action is `σ`-semilinear for multiplication by a function**: `σ • (f • a)` is
`σ f • (σ • a)`. -/
theorem placeFamilyRepresentation_smul (f : F') (a : Place k F' → F') :
    placeFamilyRepresentation k F F' σ (f • a) = σ f • placeFamilyRepresentation k F F' σ a :=
  funext fun _ ↦ by simp

/-! ### The action on repartitions -/

variable (k F F') in
/-- **The automorphism group acting on the repartition space** `A_F` of `F' / k`: the restriction
of `TauCeti.placeFamilyRepresentation` to the stable subspace `A_F`. -/
noncomputable def repartitionRepresentation :
    Representation k (F' ≃ₐ[F] F') ↥(repartitionSpace k F') :=
  (placeFamilyRepresentation k F F').subrepresentation (repartitionSpace k F') fun σ _ ha ↦
    (placeFamilyRepresentation_mem_repartitionSpace_iff σ).mpr ha

/-- The action on repartitions is the action on the underlying families. -/
@[simp]
theorem coe_repartitionRepresentation_apply (a : ↥(repartitionSpace k F')) :
    ((repartitionRepresentation k F F' σ a : ↥(repartitionSpace k F')) : Place k F' → F') =
      placeFamilyRepresentation k F F' σ a :=
  (rfl)

/-- **The action on repartitions is `σ`-semilinear**: `σ • (f · a) = σ f · (σ • a)`. -/
theorem repartitionRepresentation_repartitionMul (hF : IsFunctionField k F') (f : F')
    (a : ↥(repartitionSpace k F')) :
    repartitionRepresentation k F F' σ (repartitionMul hF f a) =
      repartitionMul hF (σ f) (repartitionRepresentation k F F' σ a) :=
  Subtype.ext <| by
    simp only [coe_repartitionRepresentation_apply, coe_repartitionMul_apply,
      placeFamilyRepresentation_smul]

/-- **The action moves the repartition supported at a place to the moved place**:
`σ • ι_P x = ι_{σ • P} (σ x)`. -/
@[simp]
theorem repartitionRepresentation_singleRepartition (P : Place k F') (x : F') :
    repartitionRepresentation k F F' σ (singleRepartition P x) = singleRepartition (σ • P) (σ x) :=
  Subtype.ext <| funext fun Q ↦ by
    rcases eq_or_ne Q (σ • P) with rfl | hQ
    · simp
    · have hQ' : σ⁻¹ • Q ≠ P := fun h ↦ hQ (by rw [← h, smul_inv_smul])
      simp [singleRepartition_of_ne hQ, singleRepartition_of_ne hQ']

end TauCeti
