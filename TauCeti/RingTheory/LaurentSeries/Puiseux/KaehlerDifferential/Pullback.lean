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
    rfl

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
  induction (KaehlerDifferential.span_range_derivation K (puiseuxField K) ▸ Submodule.mem_top :
      ω ∈ Submodule.span (puiseuxField K) (Set.range (KaehlerDifferential.D K (puiseuxField K))))
      using Submodule.span_induction with
  | mem ω hω =>
    obtain ⟨x, rfl⟩ := hω
    rw [← D_apply, pullback_D, KaehlerDifferential.mapSemilinear_D, D_apply]
    rfl
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add ω η _ _ hω hη => simp only [map_add, hω, hη]
  | smul a ω _ hω => simp only [map_smul, map_smulₛₗ, hω]

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
    intro hzero
    obtain ⟨a, ha⟩ := derivation_eq_zero_iff.mp hzero
    have ht : algebraMap K (puiseuxField K) a = single K 1 1 :=
      ρ.toAlgHom.injective ((ρ.commutes a).trans ha)
    have hd := congrArg (derivation K) ht
    rw [Derivation.map_algebraMap, derivation_single_one] at hd
    exact zero_ne_one hd
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
  rw [residue_equivPuiseuxField_pullback, h, Rat.cast_one, one_mul]

end TauCeti.puiseuxField.ContinuousKaehlerDifferential
