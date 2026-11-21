/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.IntegralClosure
public import TauCeti.RingTheory.Valuation.ValuationSubring
public import TauCeti.RingTheory.Valuation.RamificationGroup
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Unique prolongation of a henselian discrete valuation

A valuation subring of an algebraic extension of a henselian discretely valued field is
uniquely determined by its restriction to the base. Its elements are exactly those integral
over the base valuation ring. No separability or condition on the residue field is needed.
In particular, this applies to complete discrete valuation rings.

The finite-extension argument uses the discrete valuation ring structure on the integral
closure from `TauCeti/RingTheory/DiscreteValuationRing/IntegralClosure.lean`. The general
algebraic case is detected on simple finite subextensions. Uniqueness here means equality
of valuation subrings, or equivalently equivalence of valuations, not equality of valuations
with arbitrary value groups or normalizations.

## References

* J.-P. Serre, *Local Fields*, Chapter II, §2, Proposition 3.
-/

public section

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private theorem toSubring_eq_integralClosure_of_finite (A : ValuationSubring K)
    [IsDiscreteValuationRing A] [HenselianRing A (IsLocalRing.maximalIdeal A)]
    [FiniteDimensional K L] (B : ValuationSubring L)
    (hB : B.comap (algebraMap K L) = A) :
    B.toSubring = (integralClosure A L).toSubring := by
  let C := integralClosure A L
  have : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K L C
  have : IsDiscreteValuationRing C :=
    TauCeti.integralClosure.isDiscreteValuationRing A K L
  let V := ((IsDiscreteValuationRing.maximalIdeal C).valuation L).valuationSubring
  have hV : V.toSubring = C.toSubring := by
    rw [← IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring]
    ext x
    simp
  have : IsDiscreteValuationRing V :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (IsDiscreteValuationRing.equivValuationSubring (A := C) (K := L))
  have : IsIntegrallyClosedIn B.toSubring L := inferInstanceAs (IsIntegrallyClosedIn B L)
  have hclosure : C.toSubring ≤ B.toSubring :=
    Subring.integralClosure_le_iff.mpr fun a ↦ hB.symm ▸ a.property
  have hle : V ≤ B := fun x hx ↦ hclosure (hV ▸ hx)
  have hne : B ≠ ⊤ := by
    intro h
    have hA : A = ⊤ := by
      rw [← hB, h]
      ext
      simp [mem_comap]
    subst hA
    exact IsDiscreteValuationRing.not_isField (⊤ : ValuationSubring K)
      (Field.toIsField _)
  exact (congrArg toSubring (eq_of_le_of_ne_top V hle hne)).symm.trans hV

/-- In an algebraic extension of a henselian discretely valued field, an element belongs to
any prolongation of the valuation ring exactly when it is integral over the base ring. -/
theorem mem_iff_isIntegral_of_comap_eq (A : ValuationSubring K)
    [IsDiscreteValuationRing A] [HenselianRing A (IsLocalRing.maximalIdeal A)]
    [Algebra.IsAlgebraic K L] (B : ValuationSubring L)
    (hB : B.comap (algebraMap K L) = A) (x : L) : x ∈ B ↔ IsIntegral A x := by
  constructor
  · intro hx
    let E := IntermediateField.adjoin K {x}
    have : FiniteDimensional K E := IntermediateField.finiteDimensional_adjoin
      fun y _ ↦ (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
    have hE : (B.comap (algebraMap E L)).comap (algebraMap K E) = A := by
      rw [comap_comap, ← IsScalarTower.algebraMap_eq]
      exact hB
    let y : E := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
    have hy : IsIntegral A y := by
      rw [← mem_integralClosure_iff, ← Subalgebra.mem_toSubring,
        ← toSubring_eq_integralClosure_of_finite A (B.comap (algebraMap E L)) hE]
      exact hx
    exact hy.map (IsScalarTower.toAlgHom A E L)
  · intro hx
    have : IsIntegrallyClosedIn B.toSubring L := inferInstanceAs (IsIntegrallyClosedIn B L)
    exact (Subring.integralClosure_le_iff (R := A) (T := B.toSubring)).mpr
      (fun a ↦ hB.symm ▸ a.property) hx

/-- The unique prolonged valuation ring in an algebraic extension is the integral closure of
the henselian discrete valuation ring on the base. -/
theorem toSubring_eq_integralClosure_of_comap_eq (A : ValuationSubring K)
    [IsDiscreteValuationRing A] [HenselianRing A (IsLocalRing.maximalIdeal A)]
    [Algebra.IsAlgebraic K L] (B : ValuationSubring L)
    (hB : B.comap (algebraMap K L) = A) :
    B.toSubring = (integralClosure A L).toSubring :=
  Subring.ext fun x ↦ mem_iff_isIntegral_of_comap_eq A B hB x

/-- A henselian discrete valuation ring has a unique prolongation to every algebraic field
extension. Uniqueness is equality of valuation subrings, hence is independent of normalization. -/
theorem existsUnique_comap_eq_of_henselian (A : ValuationSubring K)
    [IsDiscreteValuationRing A] [HenselianRing A (IsLocalRing.maximalIdeal A)]
    [Algebra.IsAlgebraic K L] :
    ∃! B : ValuationSubring L, B.comap (algebraMap K L) = A := by
  obtain ⟨B, hmem, hnon⟩ :=
    (algebraMap A L).exists_valuationSubring_mem_and_image_subset_nonunits
      (IsLocalRing.maximalIdeal.isMaximal A).ne_top (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective A L)]
        exact bot_le)
  have hB : B.comap (algebraMap K L) = A :=
    comap_eq_of_map_maximalIdeal_le (RingHom.id A) (algebraMap A L)
      (by simp) hmem hnon (algebraMap K L) (by
        intro a
        exact (IsScalarTower.algebraMap_apply A K L a).symm)
  refine ⟨B, hB, fun C hC ↦ ext _ _ fun x ↦ ?_⟩
  rw [mem_iff_isIntegral_of_comap_eq A C hC, mem_iff_isIntegral_of_comap_eq A B hB]

/-- Every base-field automorphism of an algebraic extension preserves the unique prolongation
of a henselian discrete valuation ring. Thus its decomposition group is the whole group. -/
theorem decompositionSubgroup_eq_top_of_henselian (A : ValuationSubring K)
    [IsDiscreteValuationRing A] [HenselianRing A (IsLocalRing.maximalIdeal A)]
    [Algebra.IsAlgebraic K L] (B : ValuationSubring L)
    (hB : B.comap (algebraMap K L) = A) : B.decompositionSubgroup K = ⊤ := by
  apply (Subgroup.eq_top_iff' _).mpr
  intro σ
  rw [mem_decompositionSubgroup_iff]
  intro x
  rw [mem_iff_isIntegral_of_comap_eq A B hB, mem_iff_isIntegral_of_comap_eq A B hB]
  exact isIntegral_algEquiv (σ.restrictScalars A)

end ValuationSubring
