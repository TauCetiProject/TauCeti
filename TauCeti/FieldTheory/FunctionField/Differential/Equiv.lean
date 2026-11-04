/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.CanonicalDivisor
public import TauCeti.FieldTheory.FunctionField.Divisor.Equiv
public import TauCeti.FieldTheory.FunctionField.Repartition.Equiv

/-!
# Weil differentials and the canonical class under semilinear field isomorphisms

Let `τ : F ≃+* F'` be a field isomorphism carrying a constant subfield `k` onto `k'` along
`σ : k ≃+* k'`. Dualizing the repartition transport `TauCeti.repartitionSpaceEquivOfRingEquiv`
(`A_F ≃ₛₗ[σ] A_{F'}`) sends a `k`-linear form `ω` on `A_F` to `b ↦ σ (ω (τ⁻¹ b))` on `A_{F'}`.

Because `repartitionSpaceEquivOfRingEquiv` carries `(A_F(D) + F) ∩ A_F` onto
`(A_{F'}(τ_* D) + F') ∩ A_{F'}`, this contragredient isomorphism carries `Ω_F(D)` onto
`Ω_{F'}(τ_* D)` and `Ω_F` onto `Ω_{F'}` without any assumption on the constant fields. For
function fields with exact constant fields, it carries the divisor `(ω)` of a nonzero Weil
differential to `τ_* (ω)`, so the divisor-class isomorphism `Divisor.classGroupEquivOfRingEquiv`
carries `TauCeti.canonicalClass` to `TauCeti.canonicalClass`.

## Main definitions

* `TauCeti.repartitionDualEquivOfRingEquiv`: the contragredient `σ`-semilinear isomorphism between
  linear forms on `A_F` and linear forms on `A_{F'}`.
* `TauCeti.weilDifferentialFiltrationEquivOfRingEquiv` and
  `TauCeti.weilDifferentialSpaceEquivOfRingEquiv`: its restrictions `Ω_F(D) ≃ₛₗ[σ] Ω_{F'}(τ_* D)`
  and `Ω_F ≃ₛₗ[σ] Ω_{F'}`.

## Main results

* `TauCeti.weilDifferentialDivisor_repartitionDualEquivOfRingEquiv`: transport carries the divisor
  of a nonzero Weil differential to the reindexed divisor.
* `TauCeti.Divisor.classGroupEquivOfRingEquiv_canonicalClass`: `Cl(F) ≃+ Cl(F')` carries the
  canonical class of `F` to the canonical class of `F'`.

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

/-- **Contragredient semilinear transport of linear forms on repartitions**: `ω` on `A_F` goes to
`b ↦ σ (ω (τ⁻¹ b))` on `A_{F'}`. -/
noncomputable def repartitionDualEquivOfRingEquiv :
    Module.Dual k ↥(repartitionSpace k F) ≃ₛₗ[(σ : k →+* k')]
      Module.Dual k' ↥(repartitionSpace k' F') :=
  (repartitionSpaceEquivOfRingEquiv σ τ h).arrowCongr σ.toSemilinearEquiv

/-- Evaluation formula for a transported linear form on repartitions. -/
@[simp]
theorem repartitionDualEquivOfRingEquiv_apply_apply
    (ω : Module.Dual k ↥(repartitionSpace k F)) (b : ↥(repartitionSpace k' F')) :
    repartitionDualEquivOfRingEquiv σ τ h ω b =
      σ (ω ((repartitionSpaceEquivOfRingEquiv σ τ h).symm b)) :=
  (rfl)

/-- Evaluation formula for the inverse transport of a linear form on repartitions. -/
@[simp]
theorem repartitionDualEquivOfRingEquiv_symm_apply_apply
    (η : Module.Dual k' ↥(repartitionSpace k' F')) (a : ↥(repartitionSpace k F)) :
    (repartitionDualEquivOfRingEquiv σ τ h).symm η a =
      σ.symm (η (repartitionSpaceEquivOfRingEquiv σ τ h a)) :=
  (rfl)

/-- `repartitionDualEquivOfRingEquiv` is `τ`-semilinear for multiplication of forms by functions. -/
@[simp]
theorem repartitionDualEquivOfRingEquiv_repartitionDualMul (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') (z : F) (ω : Module.Dual k ↥(repartitionSpace k F)) :
    repartitionDualEquivOfRingEquiv σ τ h (repartitionDualMul hF z ω) =
      repartitionDualMul hF' (τ z) (repartitionDualEquivOfRingEquiv σ τ h ω) := by
  ext b
  obtain ⟨a, rfl⟩ := (repartitionSpaceEquivOfRingEquiv σ τ h).surjective b
  simp [repartitionDualMul_apply_apply,
    ← repartitionSpaceEquivOfRingEquiv_repartitionMul σ τ h hF hF']

-- Transport rules run before `Finsupp.domCongr_apply` expands the divisor reindexing.
/-- `repartitionDualEquivOfRingEquiv` carries `Ω_F(D)` onto `Ω_{F'}(τ_* D)`. -/
@[simp↓]
theorem repartitionDualEquivOfRingEquiv_mem_weilDifferentialFiltration_iff (D : Divisor k F)
    (ω : Module.Dual k ↥(repartitionSpace k F)) :
    repartitionDualEquivOfRingEquiv σ τ h ω ∈
        weilDifferentialFiltration (Finsupp.domCongr (Place.equivOfRingEquiv σ τ h) D) ↔
      ω ∈ weilDifferentialFiltration D := by
  rw [mem_weilDifferentialFiltration_iff, mem_weilDifferentialFiltration_iff]
  constructor
  · intro hω a ha
    have h0 := hω (repartitionSpaceEquivOfRingEquiv σ τ h a)
      ((repartitionSpaceEquivOfRingEquiv_mem_submoduleOfAdeleFiltrationSupDiagonalRepartitions_iff
        σ τ h D a).mpr ha)
    simpa using h0
  · intro hω b hb
    obtain ⟨a, rfl⟩ := (repartitionSpaceEquivOfRingEquiv σ τ h).surjective b
    have ha :=
      (repartitionSpaceEquivOfRingEquiv_mem_submoduleOfAdeleFiltrationSupDiagonalRepartitions_iff
        σ τ h D a).mp hb
    simp [hω a ha]

/-- **Semilinear transport of the Weil-differential filtration**: `Ω_F(D) ≃ₛₗ[σ] Ω_{F'}(τ_* D)`. -/
noncomputable def weilDifferentialFiltrationEquivOfRingEquiv (D : Divisor k F) :
    ↥(weilDifferentialFiltration D) ≃ₛₗ[(σ : k →+* k')]
      ↥(weilDifferentialFiltration (Finsupp.domCongr (Place.equivOfRingEquiv σ τ h) D)) :=
  (repartitionDualEquivOfRingEquiv σ τ h).ofSubmodules (weilDifferentialFiltration D)
    (weilDifferentialFiltration (Finsupp.domCongr (Place.equivOfRingEquiv σ τ h) D)) <| by
      ext η
      obtain ⟨ω, rfl⟩ := (repartitionDualEquivOfRingEquiv σ τ h).surjective η
      rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
        repartitionDualEquivOfRingEquiv_mem_weilDifferentialFiltration_iff]

/-- `weilDifferentialFiltrationEquivOfRingEquiv` is the restriction of
`repartitionDualEquivOfRingEquiv`. -/
@[simp]
theorem coe_weilDifferentialFiltrationEquivOfRingEquiv_apply (D : Divisor k F)
    (ω : ↥(weilDifferentialFiltration D)) :
    (weilDifferentialFiltrationEquivOfRingEquiv σ τ h D ω :
        Module.Dual k' ↥(repartitionSpace k' F')) =
      repartitionDualEquivOfRingEquiv σ τ h ω :=
  (rfl)

/-- The inverse of `weilDifferentialFiltrationEquivOfRingEquiv` is the restriction of the inverse
of `repartitionDualEquivOfRingEquiv`. -/
@[simp]
theorem coe_weilDifferentialFiltrationEquivOfRingEquiv_symm_apply (D : Divisor k F)
    (η : ↥(weilDifferentialFiltration (Finsupp.domCongr (Place.equivOfRingEquiv σ τ h) D))) :
    ((weilDifferentialFiltrationEquivOfRingEquiv σ τ h D).symm η :
        Module.Dual k ↥(repartitionSpace k F)) =
      (repartitionDualEquivOfRingEquiv σ τ h).symm η :=
  (rfl)

/-- `repartitionDualEquivOfRingEquiv` preserves the space of Weil differentials. -/
@[simp]
theorem repartitionDualEquivOfRingEquiv_mem_weilDifferentialSpace_iff
    (ω : Module.Dual k ↥(repartitionSpace k F)) :
    repartitionDualEquivOfRingEquiv σ τ h ω ∈ weilDifferentialSpace k' F' ↔
      ω ∈ weilDifferentialSpace k F := by
  rw [mem_weilDifferentialSpace_iff, mem_weilDifferentialSpace_iff]
  constructor
  · rintro ⟨D', hD'⟩
    obtain ⟨D, rfl⟩ := (Finsupp.domCongr (Place.equivOfRingEquiv σ τ h)).surjective D'
    exact ⟨D, (repartitionDualEquivOfRingEquiv_mem_weilDifferentialFiltration_iff σ τ h D ω).mp hD'⟩
  · rintro ⟨D, hD⟩
    exact ⟨Finsupp.domCongr (Place.equivOfRingEquiv σ τ h) D,
      (repartitionDualEquivOfRingEquiv_mem_weilDifferentialFiltration_iff σ τ h D ω).mpr hD⟩

/-- **Semilinear transport of the space of Weil differentials**: `Ω_F ≃ₛₗ[σ] Ω_{F'}`. -/
noncomputable def weilDifferentialSpaceEquivOfRingEquiv :
    ↥(weilDifferentialSpace k F) ≃ₛₗ[(σ : k →+* k')] ↥(weilDifferentialSpace k' F') :=
  (repartitionDualEquivOfRingEquiv σ τ h).ofSubmodules (weilDifferentialSpace k F)
    (weilDifferentialSpace k' F') <| by
      ext η
      obtain ⟨ω, rfl⟩ := (repartitionDualEquivOfRingEquiv σ τ h).surjective η
      rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
        repartitionDualEquivOfRingEquiv_mem_weilDifferentialSpace_iff]

/-- `weilDifferentialSpaceEquivOfRingEquiv` is the restriction of
`repartitionDualEquivOfRingEquiv`. -/
@[simp]
theorem coe_weilDifferentialSpaceEquivOfRingEquiv_apply (ω : ↥(weilDifferentialSpace k F)) :
    (weilDifferentialSpaceEquivOfRingEquiv σ τ h ω : Module.Dual k' ↥(repartitionSpace k' F')) =
      repartitionDualEquivOfRingEquiv σ τ h ω :=
  (rfl)

/-- The inverse of `weilDifferentialSpaceEquivOfRingEquiv` is the restriction of the inverse of
`repartitionDualEquivOfRingEquiv`. -/
@[simp]
theorem coe_weilDifferentialSpaceEquivOfRingEquiv_symm_apply
    (η : ↥(weilDifferentialSpace k' F')) :
    ((weilDifferentialSpaceEquivOfRingEquiv σ τ h).symm η :
        Module.Dual k ↥(repartitionSpace k F)) =
      (repartitionDualEquivOfRingEquiv σ τ h).symm η :=
  (rfl)

/-- `repartitionDualEquivOfRingEquiv` transports greatest bounding divisors of linear forms on
repartitions along `Place.equivOfRingEquiv`. -/
theorem isGreatest_weilDifferentialFiltration_repartitionDualEquivOfRingEquiv_iff
    (ω : Module.Dual k ↥(repartitionSpace k F)) (W : Divisor k F) :
    IsGreatest {E' : Divisor k' F' |
        repartitionDualEquivOfRingEquiv σ τ h ω ∈ weilDifferentialFiltration E'}
      (Finsupp.domCongr (Place.equivOfRingEquiv σ τ h) W) ↔
      IsGreatest {E : Divisor k F | ω ∈ weilDifferentialFiltration E} W := by
  constructor
  · rintro ⟨hmem, hmax⟩
    refine ⟨(repartitionDualEquivOfRingEquiv_mem_weilDifferentialFiltration_iff σ τ h W ω).mp hmem,
      fun D hD ↦ ?_⟩
    have hD' := hmax ((repartitionDualEquivOfRingEquiv_mem_weilDifferentialFiltration_iff
      σ τ h D ω).mpr hD)
    simpa only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
      Finsupp.mapDomain_le_mapDomain_iff_le (Place.equivOfRingEquiv σ τ h).injective] using hD'
  · rintro ⟨hmem, hmax⟩
    refine ⟨(repartitionDualEquivOfRingEquiv_mem_weilDifferentialFiltration_iff σ τ h W ω).mpr hmem,
      fun D' hD' ↦ ?_⟩
    obtain ⟨D, rfl⟩ := (Finsupp.domCongr (Place.equivOfRingEquiv σ τ h)).surjective D'
    have hD :=
      (repartitionDualEquivOfRingEquiv_mem_weilDifferentialFiltration_iff σ τ h D ω).mp hD'
    simpa only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain] using
      Finsupp.mapDomain_mono (hmax hD)

/-- **Transport of the divisor of a Weil differential**: transporting a nonzero Weil differential
along `(σ, τ)` reindexes its divisor along `Place.equivOfRingEquiv σ τ h`. -/
@[simp]
theorem weilDifferentialDivisor_repartitionDualEquivOfRingEquiv
    (hF : IsFunctionField k F) (hF' : IsFunctionField k' F')
    (hex : IsIntegrallyClosedIn k F) (hex' : IsIntegrallyClosedIn k' F')
    {ω : Module.Dual k ↥(repartitionSpace k F)} (hmem : ω ∈ weilDifferentialSpace k F)
    (hω : ω ≠ 0) :
    weilDifferentialDivisor hF' hex'
        ((repartitionDualEquivOfRingEquiv_mem_weilDifferentialSpace_iff σ τ h ω).mpr hmem)
        ((map_ne_zero_iff (repartitionDualEquivOfRingEquiv σ τ h)
          (repartitionDualEquivOfRingEquiv σ τ h).injective).mpr hω) =
      Finsupp.domCongr (Place.equivOfRingEquiv σ τ h)
        (weilDifferentialDivisor hF hex hmem hω) :=
  (isGreatest_weilDifferentialDivisor hF' hex'
    ((repartitionDualEquivOfRingEquiv_mem_weilDifferentialSpace_iff σ τ h ω).mpr hmem)
    ((map_ne_zero_iff (repartitionDualEquivOfRingEquiv σ τ h)
      (repartitionDualEquivOfRingEquiv σ τ h).injective).mpr hω)).unique
    ((isGreatest_weilDifferentialFiltration_repartitionDualEquivOfRingEquiv_iff σ τ h ω _).mpr
      (isGreatest_weilDifferentialDivisor hF hex hmem hω))

/-- **The divisor-class isomorphism `Cl(F) ≃+ Cl(F')` carries the canonical class to the canonical
class.** -/
@[simp]
theorem Divisor.classGroupEquivOfRingEquiv_canonicalClass
    (hF : IsFunctionField k F) (hF' : IsFunctionField k' F')
    (hex : IsIntegrallyClosedIn k F) (hex' : IsIntegrallyClosedIn k' F') :
    Divisor.classGroupEquivOfRingEquiv σ τ h hF hF' (canonicalClass hF hex) =
      canonicalClass hF' hex' := by
  obtain ⟨ω, hmem, hω⟩ := (Submodule.ne_bot_iff _).mp (weilDifferentialSpace_ne_bot hF hex)
  have hmem' : repartitionDualEquivOfRingEquiv σ τ h ω ∈ weilDifferentialSpace k' F' := by
    simpa only [coe_weilDifferentialSpaceEquivOfRingEquiv_apply] using
      (weilDifferentialSpaceEquivOfRingEquiv σ τ h ⟨ω, hmem⟩).2
  have hω' : repartitionDualEquivOfRingEquiv σ τ h ω ≠ 0 :=
    (map_ne_zero_iff (repartitionDualEquivOfRingEquiv σ τ h)
      (repartitionDualEquivOfRingEquiv σ τ h).injective).mpr hω
  rw [← divisorClass_weilDifferentialDivisor hF hex hmem hω,
    Divisor.classGroupEquivOfRingEquiv_divisorClass,
    ← weilDifferentialDivisor_repartitionDualEquivOfRingEquiv σ τ h hF hF' hex hex' hmem hω,
    divisorClass_weilDifferentialDivisor hF' hex' hmem' hω']

end TauCeti
