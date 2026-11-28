/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CompletedIdeal
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Residue
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

/-!
# Squarefree congruences on integral finite adeles

Reduction of an integral adele at a place has kernel the completion of the corresponding prime
ideal. Thus congruence modulo a squarefree product of primes can be tested in the individual
residue fields. For integral ideles this is compatible with `integralUnitsReduction`.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

open FiniteAdeleRing

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The component of an integral adele lies in the completed valuation ring. -/
noncomputable def integralAdelesProj (v : HeightOneSpectrum R) :
    integralAdeles R K →+* v.adicCompletionIntegers K :=
  (((FiniteAdeleRing.proj K v).toRingHom).comp (integralAdeles R K).val.toRingHom).codRestrict
    (v.adicCompletionIntegers K).toSubring fun x ↦ by
      simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        ContinuousAlgHom.coe_coe, Subalgebra.val_apply, FiniteAdeleRing.proj_apply,
        ValuationSubring.mem_toSubring] using
        mem_integralAdeles.mp x.property v

/-- Projection of an integral adele agrees with its component in the completion. -/
@[simp] theorem coe_integralAdelesProj (v : HeightOneSpectrum R) (x : integralAdeles R K) :
    (v.integralAdelesProj x : v.adicCompletion K) = (x : FiniteAdeleRing R K) v := by
  exact FiniteAdeleRing.proj_apply v (x : FiniteAdeleRing R K)

/-- An integral adele lies in the completed prime ideal precisely when its local residue is zero. -/
theorem residue_integralAdelesProj_eq_zero_iff (v : HeightOneSpectrum R) (x : integralAdeles R K) :
    IsLocalRing.residue _ (v.integralAdelesProj x) = 0 ↔ x ∈ completedIdeal K v.asIdeal := by
  have hzero (y : integralAdeles R K) (hy : y ∈ completedIdeal K v.asIdeal) :
      IsLocalRing.residue _ (v.integralAdelesProj y) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, ← pow_one (IsLocalRing.maximalIdeal _),
      v.mem_maximalIdeal_pow_iff, coe_integralAdelesProj]
    exact valued_le_of_mem_completedIdeal (by rw [pow_one]) hy
  refine ⟨fun hx ↦ ?_, hzero x⟩
  -- Replace the adele modulo the completed ideal by a diagonal integer, whose residue is known.
  obtain ⟨r, hr⟩ := exists_sub_mem_completedIdeal v.ne_bot x
  have he := hzero _ hr
  rw [map_sub, map_sub, hx, zero_sub, neg_eq_zero] at he
  have hdiag : v.integralAdelesProj (algebraMap R (integralAdeles R K) r) =
      algebraMap R (v.adicCompletionIntegers K) r := by
    apply Subtype.ext
    rw [coe_integralAdelesProj, Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply R K,
      FiniteAdeleRing.algebraMap_apply]
    rfl
  have he' : v.residueFieldEquivAdicCompletionIntegers (K := K)
      (Ideal.Quotient.mk v.asIdeal r) = 0 := by
    rw [v.residueFieldEquivAdicCompletionIntegers_apply_mk]
    exact hdiag ▸ he
  have hr' : r ∈ v.asIdeal := Ideal.Quotient.eq_zero_iff_mem.mp <|
    (v.residueFieldEquivAdicCompletionIntegers (K := K)).injective (he'.trans (map_zero _).symm)
  simpa using add_mem hr (algebraMap_mem_completedIdeal (K := K) hr')

/-- Reducing the projection of an integral adelic unit gives the residue unit of the
corresponding integral idele. -/
theorem residue_integralAdelesProj_units (v : HeightOneSpectrum R)
    (u : (integralAdeles R K)ˣ) (x : integralUnits R K)
    (hx : Units.map (integralAdeles R K).val.toRingHom u = (x : (FiniteAdeleRing R K)ˣ)) :
    IsLocalRing.residue _ (v.integralAdelesProj (u : integralAdeles R K)) =
      (v.integralUnitsReduction x : IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  let t := Units.map (v.integralAdelesProj (K := K)).toMonoidHom u
  let s := (v.adicCompletionIntegers K).unitGroupMulEquiv.symm t
  have hp : unitsProj K v x = (s : (v.adicCompletion K)ˣ) := by
    rw [← hx]
    apply Units.ext
    simp [s, t, coe_unitsProj_apply]
  rw [v.integralUnitsReduction_eq_of_unitsProj_eq x s hp,
    ValuationSubring.coe_unitGroupToResidueFieldUnits_apply, MulEquiv.apply_symm_apply]
  rfl

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.FiniteAdeleRing

open scoped Function

/-- An integral adele belongs to the completion of a squarefree product of prime ideals
if and only if its residue at each specified place is zero. -/
theorem mem_completedIdeal_prod_asIdeal_iff {R K : Type*} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (S : Finset (HeightOneSpectrum R))
    (x : integralAdeles R K) :
    x ∈ completedIdeal K (∏ v ∈ S, v.asIdeal) ↔
      ∀ v ∈ S, IsLocalRing.residue _ (v.integralAdelesProj x) = 0 := by
  have hc : (S : Set (HeightOneSpectrum R)).Pairwise
      (IsCoprime on fun v ↦ completedIdeal K v.asIdeal) := by
    intro v _ w _ hvw
    have h := Ideal.isCoprime_iff_sup_eq.mp (v.isCoprime_of_ne w hvw)
    apply Ideal.isCoprime_iff_sup_eq.mpr
    simp only [completedIdeal_def, ← Ideal.map_sup, h, Ideal.map_top]
  rw [completedIdeal_def, ← Ideal.mapHom_apply, map_prod]
  simp only [Ideal.mapHom_apply, ← completedIdeal_def, Ideal.prod_eq_iInf_of_pairwise_isCoprime hc,
    Submodule.mem_iInf, HeightOneSpectrum.residue_integralAdelesProj_eq_zero_iff]

end IsDedekindDomain.FiniteAdeleRing
