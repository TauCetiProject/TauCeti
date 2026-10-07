/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
public import TauCeti.NumberTheory.LocalField.Herbrand.HasseArf
public import TauCeti.NumberTheory.LocalField.Herbrand.UpperQuotient
public import Mathlib.FieldTheory.Galois.Abelian
import TauCeti.GroupTheory.FiniteAbelian.Quotient
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Detecting abelian ramification breaks in cyclic subextensions

Every upper break of a finite abelian extension of local fields is an upper break of a cyclic
subextension. In fact, the subextension can be chosen so that every upper ramification group
strictly after the break is trivial. Thus integrality of all abelian upper breaks reduces to
integrality for cyclic extensions.

For an elementary abelian Galois group, the detecting cyclic subextension has prime degree.
The prime-degree case of Hasse--Arf therefore proves integrality of every upper break of the
original extension, regardless of its degree.

The break detection uses the integer indexing of lower breaks, cyclic quotients separating
subgroups of a finite abelian group, and Herbrand's upper-numbering quotient theorem.

## Main results

* `TauCeti.LocalFieldsRamification.upperJump_iff_exists_isCyclic_intermediateField`: an upper
  break is detected in a cyclic intermediate field, with no later nontrivial ramification.
* `TauCeti.LocalFieldsRamification.UpperJump.exists_eq_intCast_of_exponent_prime`: Hasse--Arf
  for elementary abelian extensions.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §3, and Chapter V, §7.
-/

public section
noncomputable section

open IntermediateField
open scoped IsMulCommutative

namespace TauCeti.LocalFieldsRamification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L] [IsAbelianGalois K L]

private theorem UpperJump.exists_cyclic_quotient {u : RamificationIndexDomain}
    (hu : UpperJump K L u) :
    ∃ H : Subgroup (L ≃ₐ[K] L), IsCyclic ((L ≃ₐ[K] L) ⧸ H) ∧
      ¬upperRamificationGroup K L u ≤ H ∧
      ∀ v, u < v → upperRamificationGroup K L v ≤ H := by
  obtain ⟨i, hi, hψ⟩ := lowerJump_eq_intCast K L
    ((lowerJump_inverseHerbrand_iff K L u).2 hu)
  have hbreak : lowerRamificationGroup K L (i + 1) < lowerRamificationGroup K L i := by
    apply (lowerJump_intCast_iff K L hi).1
    rw [← hψ]
    exact (lowerJump_inverseHerbrand_iff K L u).2 hu
  obtain ⟨H, hsucc, hnot, hcyc⟩ := exists_isCyclic_quotient_of_lt hbreak
  refine ⟨H, hcyc, ?_, fun v huv ↦ ?_⟩
  · simpa only [upperRamificationGroup_def, hψ, Subtype.coe_mk,
      lowerRamificationGroupReal_intCast] using hnot
  · have hreal : (i : ℝ) < (inverseHerbrand K L v : ℝ) := by
      have hlt := inverseHerbrand_strictMono K L huv
      rw [hψ] at hlt
      exact hlt
    have hceil : i + 1 ≤ ⌈(inverseHerbrand K L v : ℝ)⌉ := by
      have := Int.lt_ceil.2 hreal
      omega
    rw [upperRamificationGroup_def, lowerRamificationGroupReal_def]
    exact (lowerRamificationGroup_antitone K L hceil).trans hsucc

/-- An upper break of a finite abelian extension is detected in a cyclic subextension. The
subextension can be chosen with trivial upper ramification groups at every later index, so the
specified break is its last break. Its local-field structures are the canonical ones induced
from the base field. -/
theorem upperJump_iff_exists_isCyclic_intermediateField (u : RamificationIndexDomain) :
    UpperJump K L u ↔ ∃ F : IntermediateField K L, IsCyclic (F ≃ₐ[K] F) ∧
      letI := finiteIntermediateFieldValuativeRel K L F
      letI := finiteIntermediateFieldTopology K L F
      haveI := finiteIntermediateField_isNonarchimedeanLocalField K L F
      haveI := finiteIntermediateField_valuativeExtension K L F
      UpperJump K F u ∧ ∀ v, u < v → upperRamificationGroup K F v = ⊥ := by
  constructor
  · intro hu
    obtain ⟨H, hcyc, hnot, hlater⟩ := hu.exists_cyclic_quotient K L
    let F := fixedField H
    let _ := finiteIntermediateFieldValuativeRel K L F
    let _ := finiteIntermediateFieldTopology K L F
    have := finiteIntermediateField_isNonarchimedeanLocalField K L F
    have := finiteIntermediateField_valuativeExtension K L F
    have := hcyc
    have hFcyc : IsCyclic (F ≃ₐ[K] F) :=
      isCyclic_of_surjective (IsGalois.normalAutEquivQuotient H).toMonoidHom
        (IsGalois.normalAutEquivQuotient H).surjective
    have hker : (AlgEquiv.restrictNormalHom F : (L ≃ₐ[K] L) →* (F ≃ₐ[K] F)).ker = H := by
      have hval : IsScalarTower.toAlgHom K F L = F.val :=
        AlgHom.ext fun x ↦ IntermediateField.algebraMap_apply F x
      rw [AlgEquiv.ker_restrictNormalHom, hval, fieldRange_val, fixingSubgroup_fixedField]
    have hnontrivial : upperRamificationGroup K F u ≠ ⊥ := by
      intro hbot
      apply hnot
      rw [← hker]
      apply (Subgroup.map_eq_bot_iff (upperRamificationGroup K L u)).1
      rwa [map_restrictNormalHom_upperRamificationGroup K F L]
    have htrivial (v : RamificationIndexDomain) (huv : u < v) :
        upperRamificationGroup K F v = ⊥ := by
      rw [← map_restrictNormalHom_upperRamificationGroup K F L, Subgroup.map_eq_bot_iff, hker]
      exact hlater v huv
    refine ⟨F, hFcyc, ?_, htrivial⟩
    exact (upperJump_iff K F u).2 fun v huv ↦ by
      rw [htrivial v huv]
      exact bot_lt_iff_ne_bot.2 hnontrivial
  · rintro ⟨F, _, hF, _⟩
    let _ := finiteIntermediateFieldValuativeRel K L F
    let _ := finiteIntermediateFieldTopology K L F
    have := finiteIntermediateField_isNonarchimedeanLocalField K L F
    have := finiteIntermediateField_valuativeExtension K L F
    exact hF.of_tower

variable {K L} in
/-- **Hasse--Arf for elementary abelian extensions.** If the exponent of the abelian Galois
group is prime, every upper ramification break is integral. This includes groups of arbitrary
prime-power order, not just prime-degree extensions. -/
theorem UpperJump.exists_eq_intCast_of_exponent_prime {u : RamificationIndexDomain}
    (hu : UpperJump K L u) (hp : (Monoid.exponent (L ≃ₐ[K] L)).Prime) :
    ∃ z : ℤ, (u : ℝ) = (z : ℝ) := by
  obtain ⟨F, hcyc, hF, _⟩ := (upperJump_iff_exists_isCyclic_intermediateField K L u).1 hu
  let _ := finiteIntermediateFieldValuativeRel K L F
  let _ := finiteIntermediateFieldTopology K L F
  have := finiteIntermediateField_isNonarchimedeanLocalField K L F
  have := finiteIntermediateField_valuativeExtension K L F
  have := hcyc
  have hdvd : Module.finrank K F ∣ Monoid.exponent (L ≃ₐ[K] L) := by
    rw [← IsGalois.card_aut_eq_finrank K F, ← IsCyclic.exponent_eq_card]
    exact MonoidHom.exponent_dvd (AlgEquiv.restrictNormalHom_surjective L)
  have hne : Module.finrank K F ≠ 1 := by
    intro hone
    have hcard : Nat.card (F ≃ₐ[K] F) = 1 := (IsGalois.card_aut_eq_finrank K F).trans hone
    have : Subsingleton (F ≃ₐ[K] F) := (Nat.card_eq_one_iff_unique.1 hcard).1
    have hdrop := (upperJump_iff K F u).1 hF
      ⟨(u : ℝ) + 1, u.property.trans (by linarith)⟩
      (Subtype.mk_lt_mk.2 (by linarith))
    exact hdrop.ne (Subsingleton.elim _ _)
  have hdegree : (Module.finrank K F).Prime :=
    (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left hne ▸ hp
  exact hF.exists_eq_intCast_of_finrank_prime hdegree

end TauCeti.LocalFieldsRamification
