/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Coefficients
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteCyclic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.DegreeTwoDescent
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.FieldTheory.Finite.GaloisField
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison

/-!
# Degree-two Galois cohomology over a finite field

For a Galois extension `L/K` of a finite field, `H²(Gal(L/K), Lˣ)` vanishes when `Lˣ`
is given the discrete topology. In particular, the cohomological Brauer group of a finite
field vanishes.

At every open normal subgroup, the fixed field is finite and its Galois group is cyclic.
Mathlib's `FiniteField.unitsMap_norm_surjective` kills the norm quotient in
`TauCeti.ContCohomology.explicitH2CyclicEquiv`. The general result then follows from
`TauCeti.ContCohomology.exists_explicitInfl2_eq`.

The finite-layer fixed-field transport follows
`TauCeti.isCoboundary₁_of_isCocycle₁_of_quotient_to_fixedPoints`.

## References

* J.-P. Serre, *Local Fields*, Chapter VIII, §4, for the norm-quotient computation of
  degree-two cyclic cohomology.
-/

public section

namespace TauCeti

open ContCohomology

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] [Finite K]

private theorem invariants_mem_range_groupNorm {U : OpenNormalSubgroup Gal(L/K)}
    (m : H0 (Gal(L/K) ⧸ U.toSubgroup)
      (FixedPoints.addSubgroup U.toSubgroup (Additive Lˣ))) :
    let := Fintype.ofFinite (Gal(L/K) ⧸ U.toSubgroup)
    (m : FixedPoints.addSubgroup U.toSubgroup (Additive Lˣ)) ∈
      (groupNorm (Gal(L/K) ⧸ U.toSubgroup)
        (FixedPoints.addSubgroup U.toSubgroup (Additive Lˣ))).range := by
  classical
  let := Fintype.ofFinite (Gal(L/K) ⧸ U.toSubgroup)
  let H : ClosedSubgroup Gal(L/K) := ⟨U.toSubgroup, U.toOpenSubgroup.isClosed⟩
  let F := IntermediateField.fixedField U.toSubgroup
  have : FiniteDimensional K F := by
    refine (InfiniteGalois.isOpen_iff_finite F).1 ?_
    rw [InfiniteGalois.fixingSubgroup_fixedField H]
    exact U.isOpen
  let e : Gal(L/K) ⧸ U.toSubgroup ≃* Gal(F/K) := InfiniteGalois.normalAutEquivQuotient H
  have he (σ : Gal(L/K)) (x : F) : ((e σ x : F) : L) = σ x := by
    rw [InfiniteGalois.normalAutEquivQuotient_apply]
    exact AlgEquiv.restrictNormal_commutes σ F x
  have : Finite F := Finite.of_injective _ (Module.finBasis K F).equivFun.injective
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_bot_iff_fixed (k := K)
    (((m : FixedPoints.addSubgroup U.toSubgroup (Additive Lˣ)) : Additive Lˣ).toMul : L)).2
      fun σ => by
        simpa [AlgEquiv.smul_units_def] using
          congrArg (fun v : FixedPoints.addSubgroup U.toSubgroup (Additive Lˣ) =>
            ((v : Additive Lˣ).toMul : L)) (m.2 (σ : Gal(L/K) ⧸ U.toSubgroup))
  have ha0 : a ≠ 0 := by
    intro h
    exact ((m : FixedPoints.addSubgroup U.toSubgroup (Additive Lˣ)) : Additive Lˣ).toMul.ne_zero
      (ha.symm.trans (by simp [h]))
  obtain ⟨b, hb⟩ := FiniteField.unitsMap_norm_surjective K F (Units.mk0 a ha0)
  let c : FixedPoints.addSubgroup U.toSubgroup (Additive Lˣ) :=
    ⟨Additive.ofMul (Units.map (F.val : F →* L) b), fun σ => by
      refine Additive.toMul.injective (Units.ext ?_)
      simpa [Subgroup.smul_def, AlgEquiv.smul_units_def] using
        (IntermediateField.mem_fixedField_iff _ _).1 (b : F).2 σ σ.2⟩
  refine ⟨c, Subtype.ext (Additive.toMul.injective (Units.ext ?_))⟩
  have hc (q : Gal(L/K) ⧸ U.toSubgroup) :
      (((q • c : FixedPoints.addSubgroup U.toSubgroup (Additive Lˣ)) :
        Additive Lˣ).toMul : L) = ((e q (b : F) : F) : L) := by
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective q
    simp [c, AlgEquiv.smul_units_def, he]
  simp only [groupNorm_apply, AddSubmonoidClass.coe_finsetSum, toMul_sum, Units.coe_prod]
  simp_rw [hc]
  trans ∏ τ : Gal(F/K), ((τ (b : F) : F) : L)
  · exact e.toEquiv.prod_comp (fun τ : Gal(F/K) => ((τ (b : F) : F) : L))
  trans ((∏ τ : Gal(F/K), τ (b : F) : F) : L)
  · exact (map_prod F.val (fun τ : Gal(F/K) => τ (b : F)) Finset.univ).symm
  rw [← Algebra.norm_eq_prod_automorphisms]
  exact (congrArg (algebraMap K L) (congrArg (fun v : Kˣ => (v : K)) hb)).trans ha

variable [TopologicalSpace (Additive Lˣ)] [DiscreteTopology (Additive Lˣ)]

/-- For a Galois extension of a finite field, degree-two cohomology vanishes at every finite
quotient, with coefficients in the invariant units. -/
theorem subsingleton_H2_quotient_additive_units_of_finite {U : OpenNormalSubgroup Gal(L/K)} :
    Subsingleton (H2 (Gal(L/K) ⧸ U.toSubgroup)
      (FixedPoints.addSubgroup U.toSubgroup (Additive Lˣ))) := by
  classical
  let H : ClosedSubgroup Gal(L/K) := ⟨U.toSubgroup, U.toOpenSubgroup.isClosed⟩
  let F := IntermediateField.fixedField U.toSubgroup
  have : FiniteDimensional K F := by
    refine (InfiniteGalois.isOpen_iff_finite F).1 ?_
    rw [InfiniteGalois.fixingSubgroup_fixedField H]
    exact U.isOpen
  let e : Gal(L/K) ⧸ U.toSubgroup ≃* Gal(F/K) := InfiniteGalois.normalAutEquivQuotient H
  have : Finite F := Finite.of_injective _ (Module.finBasis K F).equivFun.injective
  have : IsCyclic (Gal(L/K) ⧸ U.toSubgroup) := e.isCyclic.mpr inferInstance
  let := Fintype.ofFinite (Gal(L/K) ⧸ U.toSubgroup)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K) ⧸ U.toSubgroup)
  apply (explicitH2CyclicEquiv _ _ g hg).toEquiv.subsingleton_congr.mpr
  apply QuotientAddGroup.subsingleton_iff.mpr
  apply top_unique
  intro m _
  exact invariants_mem_range_groupNorm (U := U) m

/-- **Degree-two vanishing over a finite field.** For any Galois extension `L/K` of a finite
field, `H²(Gal(L/K), Lˣ) = 0`, with discrete unit coefficients. Continuity of the action
is automatic and is an instance argument because `H²` is formed under it. -/
theorem subsingleton_H2_additive_units_of_finite
    [ContinuousSMul Gal(L/K) (Additive Lˣ)] :
    Subsingleton (H2 Gal(L/K) (Additive Lˣ)) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨U, y, rfl⟩ := exists_explicitInfl2_eq x
  have := subsingleton_H2_quotient_additive_units_of_finite (U := U)
  rw [Subsingleton.elim y 0, map_zero]

variable (K) in
/-- **The cohomological Brauer group of a finite field vanishes.** -/
instance subsingleton_H2_unitsCoeff_of_finite :
    Subsingleton (H2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :=
  subsingleton_H2_additive_units_of_finite

variable (K) in
/-- **The cohomological Brauer group of a finite field vanishes**, stated for Mathlib's
canonical continuous cohomology: `H²(G_K, (Kˢ)ˣ) = 0`. -/
theorem isZero_continuousCohomology_two_unitsCoeff_of_finite :
    CategoryTheory.Limits.IsZero (continuousCohomology 2
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K))) := by
  let h : Subsingleton (DiscreteH2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :=
    (discreteH2Equiv (AbsoluteGaloisGroup K) (UnitsCoeff K)).toEquiv.subsingleton_congr.mpr
      inferInstance
  rw [← (explicitH2IsoContinuousCohomology
    (AbsoluteGaloisGroup K) (UnitsCoeff K)).isZero_iff]
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
  ext x
  exact h.elim _ _

end TauCeti
