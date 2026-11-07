/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Equiv
public import TauCeti.FieldTheory.FunctionField.Repartition.Basic

/-!
# Repartitions and repartition cokernels under semilinear field isomorphisms

Let `τ : F ≃+* F'` be a field isomorphism carrying a constant subfield `k` onto `k'` along
`σ : k ≃+* k'`. Composing valuations with `τ⁻¹` identifies the places (`Place.equivOfRingEquiv`)
and hence the divisors (`Finsupp.domCongr`).

Entrywise application of `τ` along that bijection of places gives a `σ`-semilinear isomorphism of
repartition spaces `A_F ≃ₛₗ[σ] A_{F'}` (`TauCeti.repartitionSpaceEquivOfRingEquiv`). It moves single
repartitions with the places, intertwines multiplication by functions, and carries both the divisor
filtration `A_F(D)` and the diagonal copy of `F` onto their counterparts in `F'`, descending to a
`σ`-semilinear isomorphism of repartition cokernels `A_F ⧸ (A_F(D) + F) ≃ₛₗ[σ]
A_{F'} ⧸ (A_{F'}(τ_* D) + F')` (`TauCeti.repartitionQuotientEquivOfRingEquiv`).

No exact-constant or function-field hypothesis is needed to construct the repartition and cokernel
equivalences.

## Main definitions

* `TauCeti.repartitionSpaceEquivOfRingEquiv`: the `σ`-semilinear isomorphism `A_F ≃ₛₗ[σ] A_{F'}`.
* `TauCeti.repartitionQuotientEquivOfRingEquiv`: the induced isomorphism of repartition cokernels
  `A_F ⧸ (A_F(D) + F) ≃ₛₗ[σ] A_{F'} ⧸ (A_{F'}(τ_* D) + F')`.

## Main results

* `TauCeti.repartitionSpaceEquivOfRingEquiv_singleRepartition`: transport moves `ι_P x` to
  `ι_{τ_* P} (τ x)`.
* `TauCeti.repartitionSpaceEquivOfRingEquiv_repartitionMul`: transport is `τ`-semilinear for
  multiplication by functions.
* `TauCeti.repartitionQuotientEquivOfRingEquiv_mk`: the cokernel isomorphism sends the class of `a`
  to the class of its transport.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.5.
-/

public section

namespace TauCeti

open AlgebraicGeometry

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k' F']
variable (σ : k ≃+* k') (τ : F ≃+* F')
  (h : ∀ c, τ (algebraMap k F c) = algebraMap k' F' (σ c))

/-! ### Semilinear transport of repartitions -/

private noncomputable def placeFamilyEquivOfRingEquiv :
    (Place k F → F) ≃ₛₗ[(σ : k →+* k')] (Place k' F' → F') where
  toFun a Q := τ (a ((Place.equivOfRingEquiv σ τ h).symm Q))
  invFun b P := τ.symm (b (Place.equivOfRingEquiv σ τ h P))
  left_inv a := funext fun P ↦ by simp
  right_inv b := funext fun Q ↦ by simp
  map_add' a b := funext fun Q ↦ map_add τ _ _
  map_smul' c a := funext fun Q ↦ by
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, h, RingEquiv.coe_toRingHom]

private theorem placeFamilyEquivOfRingEquiv_mem_repartitionSpace_iff (a : Place k F → F) :
    placeFamilyEquivOfRingEquiv σ τ h a ∈ repartitionSpace k' F' ↔
      a ∈ repartitionSpace k F := by
  rw [mem_repartitionSpace_iff_finite, mem_repartitionSpace_iff_finite]
  let e := Place.equivOfRingEquiv σ τ h
  have hset₁ : {Q : Place k' F' | ¬Q.valuation (placeFamilyEquivOfRingEquiv σ τ h a Q) ≤ 1} =
      e.symm ⁻¹' {P : Place k F | ¬P.valuation (a P) ≤ 1} := by
    ext Q
    simp [placeFamilyEquivOfRingEquiv, e]
  rw [hset₁]
  refine ⟨fun hfin ↦ ?_, fun hfin ↦ hfin.preimage e.symm.injective.injOn⟩
  have hset₂ : {P : Place k F | ¬P.valuation (a P) ≤ 1} =
      e ⁻¹' (e.symm ⁻¹' {P : Place k F | ¬P.valuation (a P) ≤ 1}) := by
    ext P
    simp
  rw [hset₂]
  exact hfin.preimage e.injective.injOn

private theorem placeFamilyEquivOfRingEquiv_mem_adeleFiltration_iff (D : Divisor k F)
    (a : Place k F → F) :
    placeFamilyEquivOfRingEquiv σ τ h a ∈
        adeleFiltration (Finsupp.domCongr (Place.equivOfRingEquiv σ τ h) D) ↔
      a ∈ adeleFiltration D := by
  simp only [mem_adeleFiltration_iff, WeilDivisor.coeff, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_apply]
  refine ⟨fun ha P ↦ ?_, fun ha Q ↦ ?_⟩
  · simpa [placeFamilyEquivOfRingEquiv] using ha (Place.equivOfRingEquiv σ τ h P)
  · obtain ⟨P, rfl⟩ := (Place.equivOfRingEquiv σ τ h).surjective Q
    simpa [placeFamilyEquivOfRingEquiv] using ha P

private theorem placeFamilyEquivOfRingEquiv_mem_diagonalRepartitions_iff (a : Place k F → F) :
    placeFamilyEquivOfRingEquiv σ τ h a ∈ diagonalRepartitions k' F' ↔
      a ∈ diagonalRepartitions k F := by
  simp only [mem_diagonalRepartitions_iff]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨τ.symm g, funext fun P ↦ τ.injective ?_⟩
    simpa [placeFamilyEquivOfRingEquiv] using
      congrFun hg (Place.equivOfRingEquiv σ τ h P)
  · rintro ⟨f, rfl⟩
    exact ⟨τ f, funext fun Q ↦ rfl⟩

/-- **Semilinear transport of the repartition space**: an isomorphism `τ : F ≃+* F'` carrying `k`
onto `k'` along `σ` induces `A_F ≃ₛₗ[σ] A_{F'}` by `(τ_* a)_Q = τ (a_{τ^* Q})`. -/
noncomputable def repartitionSpaceEquivOfRingEquiv :
    ↥(repartitionSpace k F) ≃ₛₗ[(σ : k →+* k')] ↥(repartitionSpace k' F') :=
  (placeFamilyEquivOfRingEquiv σ τ h).ofSubmodules (repartitionSpace k F)
    (repartitionSpace k' F') <| by
      ext b
      obtain ⟨a, rfl⟩ := (placeFamilyEquivOfRingEquiv σ τ h).surjective b
      rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
        placeFamilyEquivOfRingEquiv_mem_repartitionSpace_iff]

/-- Entrywise formula for `repartitionSpaceEquivOfRingEquiv`. -/
@[simp]
theorem coe_repartitionSpaceEquivOfRingEquiv_apply (a : ↥(repartitionSpace k F))
    (Q : Place k' F') :
    (repartitionSpaceEquivOfRingEquiv σ τ h a : Place k' F' → F') Q =
      τ ((a : Place k F → F) ((Place.equivOfRingEquiv σ τ h).symm Q)) :=
  (rfl)

/-- Entrywise formula for the inverse of `repartitionSpaceEquivOfRingEquiv`. -/
@[simp]
theorem coe_repartitionSpaceEquivOfRingEquiv_symm_apply (b : ↥(repartitionSpace k' F'))
    (P : Place k F) :
    ((repartitionSpaceEquivOfRingEquiv σ τ h).symm b : Place k F → F) P =
      τ.symm ((b : Place k' F' → F') (Place.equivOfRingEquiv σ τ h P)) :=
  (rfl)

/-- `repartitionSpaceEquivOfRingEquiv` moves a single-place repartition `ι_P x` to
`ι_{τ_* P} (τ x)`. -/
@[simp]
theorem repartitionSpaceEquivOfRingEquiv_singleRepartition (P : Place k F) (x : F) :
    repartitionSpaceEquivOfRingEquiv σ τ h (singleRepartition P x) =
      singleRepartition (Place.equivOfRingEquiv σ τ h P) (τ x) :=
  Subtype.ext <| funext fun Q ↦ by
    rcases eq_or_ne Q (Place.equivOfRingEquiv σ τ h P) with rfl | hQ
    · simp
    · have hQ' : (Place.equivOfRingEquiv σ τ h).symm Q ≠ P :=
        fun heq ↦ hQ (by rw [← heq, Equiv.apply_symm_apply])
      simp [singleRepartition_of_ne hQ, singleRepartition_of_ne hQ']

/-- `repartitionSpaceEquivOfRingEquiv` is `τ`-semilinear for multiplication by functions. -/
@[simp]
theorem repartitionSpaceEquivOfRingEquiv_repartitionMul (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') (z : F) (a : ↥(repartitionSpace k F)) :
    repartitionSpaceEquivOfRingEquiv σ τ h (repartitionMul hF z a) =
      repartitionMul hF' (τ z) (repartitionSpaceEquivOfRingEquiv σ τ h a) := by
  ext Q
  simp [smul_eq_mul]

-- Transport rules run before `Finsupp.domCongr_apply` expands the divisor reindexing.
/-- `repartitionSpaceEquivOfRingEquiv` carries `(A_F(D) + F) ∩ A_F` onto
`(A_{F'}(τ_* D) + F') ∩ A_{F'}`. -/
@[simp↓]
theorem repartitionSpaceEquivOfRingEquiv_mem_submoduleOfAdeleFiltrationSupDiagonalRepartitions_iff
    (D : Divisor k F) (a : ↥(repartitionSpace k F)) :
    repartitionSpaceEquivOfRingEquiv σ τ h a ∈
        submoduleOfAdeleFiltrationSupDiagonalRepartitions
          (Finsupp.domCongr (Place.equivOfRingEquiv σ τ h) D) ↔
      a ∈ submoduleOfAdeleFiltrationSupDiagonalRepartitions D := by
  rw [mem_submoduleOfAdeleFiltrationSupDiagonalRepartitions_iff,
    mem_submoduleOfAdeleFiltrationSupDiagonalRepartitions_iff, Submodule.mem_sup, Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, hyz⟩
    refine ⟨(placeFamilyEquivOfRingEquiv σ τ h).symm y,
      (placeFamilyEquivOfRingEquiv_mem_adeleFiltration_iff σ τ h D _).mp (by simpa using hy),
      (placeFamilyEquivOfRingEquiv σ τ h).symm z,
      (placeFamilyEquivOfRingEquiv_mem_diagonalRepartitions_iff σ τ h _).mp (by simpa using hz),
      funext fun P ↦ ?_⟩
    simpa [placeFamilyEquivOfRingEquiv] using
      congrArg τ.symm (congrFun hyz (Place.equivOfRingEquiv σ τ h P))
  · rintro ⟨y, hy, z, hz, hyz⟩
    refine ⟨placeFamilyEquivOfRingEquiv σ τ h y,
      (placeFamilyEquivOfRingEquiv_mem_adeleFiltration_iff σ τ h D y).mpr hy,
      placeFamilyEquivOfRingEquiv σ τ h z,
      (placeFamilyEquivOfRingEquiv_mem_diagonalRepartitions_iff σ τ h z).mpr hz,
      funext fun Q ↦ ?_⟩
    simpa [placeFamilyEquivOfRingEquiv] using
      congrArg τ (congrFun hyz ((Place.equivOfRingEquiv σ τ h).symm Q))

/-- **Semilinear transport of repartition cokernels**: `A_F ⧸ (A_F(D) + F)` is `σ`-semilinearly
isomorphic to `A_{F'} ⧸ (A_{F'}(τ_* D) + F')`. -/
noncomputable def repartitionQuotientEquivOfRingEquiv (D : Divisor k F) :
    (↥(repartitionSpace k F) ⧸ submoduleOfAdeleFiltrationSupDiagonalRepartitions D) ≃ₛₗ[
      (σ : k →+* k')]
      (↥(repartitionSpace k' F') ⧸
        submoduleOfAdeleFiltrationSupDiagonalRepartitions
          (Finsupp.domCongr (Place.equivOfRingEquiv σ τ h) D)) :=
  Submodule.Quotient.equiv
    (submoduleOfAdeleFiltrationSupDiagonalRepartitions D)
    (submoduleOfAdeleFiltrationSupDiagonalRepartitions
      (Finsupp.domCongr (Place.equivOfRingEquiv σ τ h) D))
    (repartitionSpaceEquivOfRingEquiv σ τ h) <| by
      ext b
      obtain ⟨a, rfl⟩ := (repartitionSpaceEquivOfRingEquiv σ τ h).surjective b
      simp [Submodule.mem_map_equiv]

/-- `repartitionQuotientEquivOfRingEquiv` sends the class of `a` to the class of its transport. -/
@[simp]
theorem repartitionQuotientEquivOfRingEquiv_mk (D : Divisor k F) (a : ↥(repartitionSpace k F)) :
    repartitionQuotientEquivOfRingEquiv σ τ h D (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (repartitionSpaceEquivOfRingEquiv σ τ h a) :=
  (rfl)

/-- The inverse of `repartitionQuotientEquivOfRingEquiv` sends the class of `b` to the class of
its inverse transport. -/
@[simp]
theorem repartitionQuotientEquivOfRingEquiv_symm_mk (D : Divisor k F)
    (b : ↥(repartitionSpace k' F')) :
    (repartitionQuotientEquivOfRingEquiv σ τ h D).symm (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk ((repartitionSpaceEquivOfRingEquiv σ τ h).symm b) :=
  (rfl)

end TauCeti
