/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.RingTheory.Kaehler.MapSemilinear
public import TauCeti.RingTheory.LaurentSeries.Puiseux.KaehlerDifferential.Basic
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Residue
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Substitution

/-!
# Pullback of continuous Puiseux differentials

A continuous coefficient-field algebra endomorphism `ρ` of the Puiseux field acts on continuous
one-forms by `f dt ↦ ρ(f) d(ρ(t))`. This agrees with the algebraic map
`KaehlerDifferential.mapSemilinear ρ` on the quotient defining continuous differentials.
Thus pullback commutes with the universal differential, not just with its coordinate expression.

Pullback is continuous and functorial. A bicontinuous algebra automorphism induces a semilinear
equivalence of one-forms, with inverse the pullback along its inverse. The comparison with forms
on a ramified level intertwines any compatible Laurent substitution with Puiseux pullback.
Residues are multiplied by the order of `ρ(t)`, so order-one changes preserve them.

Combined with the levelwise substitution theory of
`TauCeti.RingTheory.LaurentSeries.Puiseux.Substitution`, any lift of a Laurent substitution
`f ↦ f (φ)` intertwines level-`1` one-forms with `subst φ`, acts on every ramified level `n` by
substitution with an order-`ord φ` power series, and multiplies Puiseux residues by
`φ.order.toNat`. Any lift of a formal coordinate acts on every ramified level by a
formal-coordinate equivalence `substEquiv ψ` and preserves Puiseux residues.
-/

public section

open scoped LaurentSeries PowerSeries

namespace TauCeti.puiseuxField.ContinuousKaehlerDifferential

variable {K : Type*} [Field K] [CharZero K]

/-- Pullback along a continuous Puiseux endomorphism: `f dt ↦ ρ(f) d(ρ(t))`.
It is semilinear over `ρ` and agrees with the algebraic Kähler map on the continuous quotient. -/
noncomputable def pullback (ρ : puiseuxField K →A[K] puiseuxField K) :
    ContinuousKaehlerDifferential K →ₛₗ[ρ.toAlgHom.toRingHom]
      ContinuousKaehlerDifferential K where
  toFun ω := (equivPuiseuxField K).symm
    (ρ (equivPuiseuxField K ω) * derivation K (ρ (single K 1 1)))
  map_add' ω η := by simp only [map_add, add_mul]
  map_smul' f ω := by
    simp only [map_smul, smul_eq_mul, map_mul, mul_assoc]
    rw [← smul_eq_mul, map_smul]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ContinuousAlgHom.coe_coe]

/-- In the frame `dt`, pullback includes the Jacobian `d(ρ(t))/dt`. -/
@[simp]
theorem equivPuiseuxField_pullback (ρ : puiseuxField K →A[K] puiseuxField K)
    (ω : ContinuousKaehlerDifferential K) :
    equivPuiseuxField K (pullback ρ ω) =
      ρ (equivPuiseuxField K ω) * derivation K (ρ (single K 1 1)) :=
  (equivPuiseuxField K).apply_symm_apply _

/-- Pullback commutes with the universal continuous differential. -/
@[simp]
theorem pullback_D (ρ : puiseuxField K →A[K] puiseuxField K) (x : puiseuxField K) :
    pullback ρ (D K x) = D K (ρ x) := by
  apply (equivPuiseuxField K).injective
  rw [equivPuiseuxField_pullback, equivPuiseuxField_D, equivPuiseuxField_D]
  exact (derivation_algHom_apply ρ.toAlgHom ρ.continuous x).symm

/-- Pullback on the continuous quotient is induced by pullback of algebraic differentials. -/
@[simp]
theorem pullback_mk (ρ : puiseuxField K →A[K] puiseuxField K)
    (ω : Ω[puiseuxField K⁄K]) :
    pullback ρ (mk K ω) = mk K (KaehlerDifferential.mapSemilinear ρ.toAlgHom ω) := by
  have h : (pullback ρ).comp (mk K) =
      (mk K).comp (KaehlerDifferential.mapSemilinear ρ.toAlgHom) := by
    apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation K (puiseuxField K))
    intro x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← D_apply, pullback_D,
      KaehlerDifferential.mapSemilinear_D, D_apply]
    simp only [ContinuousAlgHom.coe_coe]
  simpa only [LinearMap.comp_apply] using LinearMap.congr_fun h ω

/-- Pullback is characterized among semilinear maps by sending `dt` to `d(ρ(t))`. -/
theorem eq_pullback_of_apply_D_single_one (ρ : puiseuxField K →A[K] puiseuxField K)
    (ℓ : ContinuousKaehlerDifferential K →ₛₗ[ρ.toAlgHom.toRingHom]
      ContinuousKaehlerDifferential K)
    (h : ℓ (D K (single K 1 1)) = D K (ρ (single K 1 1))) : ℓ = pullback ρ :=
  hom_ext (h.trans (pullback_D ρ _).symm)

/-- A continuous Puiseux field embedding induces an injection on continuous one-forms. -/
theorem pullback_injective (ρ : puiseuxField K →A[K] puiseuxField K) :
    Function.Injective (pullback ρ) := by
  have hJac : derivation K (ρ (single K 1 1)) ≠ 0 := by
    simpa only [ContinuousAlgHom.coe_coe] using derivation_map_single_one_ne_zero ρ.toAlgHom
  intro ω η h
  have hc := congrArg (equivPuiseuxField K) h
  rw [equivPuiseuxField_pullback, equivPuiseuxField_pullback,
    mul_left_inj' hJac] at hc
  exact (equivPuiseuxField K).injective (ρ.toAlgHom.injective hc)

/-- Pullback is continuous for the transported valuation topology on one-forms. -/
@[fun_prop]
theorem continuous_pullback (ρ : puiseuxField K →A[K] puiseuxField K) :
    Continuous (pullback ρ) :=
  IsModuleTopology.continuous_of_linearMapₛₗ ρ.continuous (pullback ρ)

/-- The identity endomorphism fixes every continuous one-form. -/
@[simp]
theorem pullback_id (ω : ContinuousKaehlerDifferential K) :
    pullback (ContinuousAlgHom.id K (puiseuxField K)) ω = ω := by
  apply (equivPuiseuxField K).injective
  simp only [equivPuiseuxField_pullback, ContinuousAlgHom.id_apply, derivation_single_one,
    mul_one]

/-- Pullback is functorial in continuous Puiseux endomorphisms. -/
theorem pullback_comp (ρ σ : puiseuxField K →A[K] puiseuxField K)
    (ω : ContinuousKaehlerDifferential K) :
    pullback (ρ.comp σ) ω = pullback ρ (pullback σ ω) := by
  apply (equivPuiseuxField K).injective
  simp only [equivPuiseuxField_pullback, ContinuousAlgHom.comp_apply, map_mul, mul_assoc]
  exact congrArg (fun z ↦ ρ (σ (equivPuiseuxField K ω)) * z)
    (derivation_algHom_apply ρ.toAlgHom ρ.continuous (σ (single K 1 1)))

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Bicontinuous Puiseux automorphisms act invertibly on continuous one-forms. -/
noncomputable def pullbackEquiv (ρ : puiseuxField K ≃A[K] puiseuxField K) :
    ContinuousKaehlerDifferential K
      ≃ₛₗ[(ρ.toAlgEquiv.toRingEquiv : puiseuxField K →+* puiseuxField K)]
        ContinuousKaehlerDifferential K where
  toFun := pullback ρ.toContinuousAlgHom
  invFun := pullback ρ.symm.toContinuousAlgHom
  map_add' := map_add _
  map_smul' := (pullback ρ.toContinuousAlgHom).map_smul'
  left_inv ω := by
    obtain ⟨ω, rfl⟩ := mk_surjective K ω
    rw [pullback_mk, pullback_mk]
    exact congrArg (mk K) (KaehlerDifferential.mapSemilinear_symm_apply_apply ρ.toAlgEquiv ω)
  right_inv ω := by
    obtain ⟨ω, rfl⟩ := mk_surjective K ω
    rw [pullback_mk, pullback_mk]
    exact congrArg (mk K) (KaehlerDifferential.mapSemilinear_apply_symm_apply ρ.toAlgEquiv ω)

/-- The semilinear equivalence evaluates as pullback. -/
@[simp]
theorem pullbackEquiv_apply (ρ : puiseuxField K ≃A[K] puiseuxField K)
    (ω : ContinuousKaehlerDifferential K) :
    pullbackEquiv ρ ω = pullback ρ.toContinuousAlgHom ω :=
  (rfl)

/-- The inverse equivalence is pullback along the inverse automorphism. -/
@[simp]
theorem pullbackEquiv_symm_apply (ρ : puiseuxField K ≃A[K] puiseuxField K)
    (ω : ContinuousKaehlerDifferential K) :
    (pullbackEquiv ρ).symm ω = pullback ρ.symm.toContinuousAlgHom ω :=
  (rfl)

/-- The equivalence on one-forms is continuous. Its inverse is continuous by the same theorem
applied to the inverse automorphism. -/
@[fun_prop]
theorem continuous_pullbackEquiv (ρ : puiseuxField K ≃A[K] puiseuxField K) :
    Continuous (pullbackEquiv ρ) :=
  continuous_pullback ρ.toContinuousAlgHom

/-- Pullback agrees with Laurent substitution on any compatible pair of ramified levels.
The hypothesis describes the field maps; the conclusion includes their Jacobian factors. -/
theorem pullback_levelMap_subst (ρ : puiseuxField K →A[K] puiseuxField K)
    (n m : ℕ+) {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (h : ∀ f, ρ (levelEmbedding K n f) =
      levelEmbedding K m (LaurentSeries.substAlgHom hφ hφ₀ f))
    (ω : TauCeti.ContinuousKaehlerDifferential K) :
    pullback ρ (levelMap K n ω) =
      levelMap K m (TauCeti.ContinuousKaehlerDifferential.subst hφ hφ₀ ω) := by
  rw [← TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_smul_D_single_one K ω]
  simp only [map_smulₛₗ, levelMap_D, pullback_D,
    TauCeti.ContinuousKaehlerDifferential.subst_D]
  simp only [AlgHom.toRingHom_eq_coe, ContinuousAlgHom.coe_coe, RingHom.coe_coe, h]

/-- Pullback multiplies the residue by the rational order of the image of the parameter. -/
theorem residue_equivPuiseuxField_pullback (ρ : puiseuxField K →A[K] puiseuxField K)
    (ω : ContinuousKaehlerDifferential K) :
    residue K (equivPuiseuxField K (pullback ρ ω)) =
      ((ρ (single K 1 1) : HahnSeries ℚ K).order : K) *
        residue K (equivPuiseuxField K ω) := by
  rw [equivPuiseuxField_pullback]
  exact residue_map_mul_derivation_eq_mul ρ.toAlgHom ρ.continuous _

/-- An order-one change of parameter preserves the residue of a continuous Puiseux one-form. -/
theorem residue_equivPuiseuxField_pullback_of_order_eq_one
    (ρ : puiseuxField K →A[K] puiseuxField K)
    (h : (ρ (single K 1 1) : HahnSeries ℚ K).order = 1)
    (ω : ContinuousKaehlerDifferential K) :
    residue K (equivPuiseuxField K (pullback ρ ω)) = residue K (equivPuiseuxField K ω) := by
  rw [equivPuiseuxField_pullback]
  exact residue_map_mul_derivation ρ.toAlgHom ρ.continuous h _

/-! ### Lifts of Laurent substitutions and formal coordinates -/

/-- Pullback along a continuous lift of `LaurentSeries.substAlgHom hφ hφ₀` intertwines level-`1`
continuous one-forms with `TauCeti.ContinuousKaehlerDifferential.subst hφ hφ₀`. -/
theorem pullback_levelMap_one_of_apply_algebraMap_substAlgHom {φ : K⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    {ρ : puiseuxField K →A[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (ω : TauCeti.ContinuousKaehlerDifferential K) :
    pullback ρ (levelMap K 1 ω) =
      levelMap K 1 (TauCeti.ContinuousKaehlerDifferential.subst hφ hφ₀ ω) :=
  pullback_levelMap_subst ρ 1 1 hφ hφ₀ hρ ω

/-- Pullback along a continuous lift of `LaurentSeries.substAlgHom hφ hφ₀` acts on every ramified
level `n` as substitution by a power series `ψ ∈ X K⟦X⟧` of the same order as `φ`. -/
theorem exists_pullback_levelMap_eq_subst {φ : K⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    {ρ : puiseuxField K →A[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (n : ℕ+) :
    ∃ (ψ : K⟦X⟧) (hψ : PowerSeries.constantCoeff ψ = 0) (hψ₀ : ψ ≠ 0),
      ψ.order = φ.order ∧
      ∀ ω, pullback ρ (levelMap K n ω) =
        levelMap K n (TauCeti.ContinuousKaehlerDifferential.subst hψ hψ₀ ω) := by
  obtain ⟨ψ, hψ, hψ₀, hψord, hlevel⟩ :=
    exists_levelEmbedding_eq_substAlgHom hφ hφ₀ (ρ := ρ.toAlgHom) hρ n
  exact ⟨ψ, hψ, hψ₀, hψord, fun ω ↦ pullback_levelMap_subst ρ n n hψ hψ₀ hlevel ω⟩

/-- Pullback along a continuous lift of `LaurentSeries.substAlgHom hφ hφ₀` multiplies Puiseux
residues by `φ.order.toNat`. -/
theorem residue_equivPuiseuxField_pullback_of_apply_algebraMap_substAlgHom {φ : K⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    {ρ : puiseuxField K →A[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (ω : ContinuousKaehlerDifferential K) :
    residue K (equivPuiseuxField K (pullback ρ ω)) =
      φ.order.toNat • residue K (equivPuiseuxField K ω) := by
  have hord : (ρ (single K 1 1) : HahnSeries ℚ K).order = φ.order.toNat := by
    simpa only [ContinuousAlgHom.coe_coe, coe_single, HahnSeries.order_single one_ne_zero,
      mul_one] using
      order_apply_of_apply_algebraMap_substAlgHom hφ hφ₀ (ρ := ρ.toAlgHom) hρ (single K 1 1)
  rw [residue_equivPuiseuxField_pullback, hord, Rat.cast_natCast, nsmul_eq_mul]

/-- Pullback along a bicontinuous lift of `LaurentSeries.substAlgEquiv φ` intertwines level-`1`
continuous one-forms with `TauCeti.ContinuousKaehlerDifferential.substEquiv φ`. -/
theorem pullbackEquiv_levelMap_one_of_apply_algebraMap_substAlgEquiv (φ : FormalCoordinate K)
    {ρ : puiseuxField K ≃A[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (ω : TauCeti.ContinuousKaehlerDifferential K) :
    pullbackEquiv ρ (levelMap K 1 ω) =
      levelMap K 1 (TauCeti.ContinuousKaehlerDifferential.substEquiv φ ω) := by
  rw [pullbackEquiv_apply, TauCeti.ContinuousKaehlerDifferential.substEquiv_apply]
  exact pullback_levelMap_one_of_apply_algebraMap_substAlgHom
    φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero
    (fun f ↦ by
      simpa only [ContinuousAlgEquiv.coe_coe, LaurentSeries.coe_substAlgEquiv] using hρ f) ω

/-- Pullback along a bicontinuous lift of `LaurentSeries.substAlgEquiv φ` acts on every ramified
level `n` as `TauCeti.ContinuousKaehlerDifferential.substEquiv ψ` for a formal coordinate `ψ`. -/
theorem exists_pullbackEquiv_levelMap_eq_substEquiv (φ : FormalCoordinate K)
    {ρ : puiseuxField K ≃A[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (n : ℕ+) :
    ∃ ψ : FormalCoordinate K, ∀ ω,
      pullbackEquiv ρ (levelMap K n ω) =
        levelMap K n (TauCeti.ContinuousKaehlerDifferential.substEquiv ψ ω) := by
  obtain ⟨ψ, hψ⟩ := exists_levelEmbedding_eq_substAlgEquiv φ (ρ := ρ.toAlgEquiv.toAlgHom) hρ n
  refine ⟨ψ, fun ω ↦ ?_⟩
  rw [pullbackEquiv_apply, TauCeti.ContinuousKaehlerDifferential.substEquiv_apply]
  exact pullback_levelMap_subst ρ.toContinuousAlgHom n n
    ψ.constantCoeff_toPowerSeries ψ.toPowerSeries_ne_zero
    (fun f ↦ by
      simpa only [ContinuousAlgEquiv.coe_coe, AlgEquiv.coe_toAlgHom,
        ContinuousAlgEquiv.coe_toAlgEquiv, LaurentSeries.coe_substAlgEquiv] using hψ f) ω

/-- Pullback along a continuous lift of a formal coordinate preserves Puiseux residues. -/
theorem residue_equivPuiseuxField_pullback_of_apply_algebraMap_substAlgEquiv
    (φ : FormalCoordinate K) {ρ : puiseuxField K →A[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (ω : ContinuousKaehlerDifferential K) :
    residue K (equivPuiseuxField K (pullback ρ ω)) =
      residue K (equivPuiseuxField K ω) := by
  have hρ' : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K)
        (LaurentSeries.substAlgHom φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero f) :=
    fun f ↦ by simpa only [LaurentSeries.coe_substAlgEquiv] using hρ f
  rw [residue_equivPuiseuxField_pullback_of_apply_algebraMap_substAlgHom _ _ hρ',
    FormalCoordinate.order_toPowerSeries, ENat.toNat_one, one_smul]

end TauCeti.puiseuxField.ContinuousKaehlerDifferential
