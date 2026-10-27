/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
import Mathlib.Topology.WithTopology

/-!
# The coefficient model of module-valued restricted series

At unit polyradius, a restricted family with coefficients in a seminormed additive group `E`
is precisely a null family on the discrete exponent set. Taking coefficients identifies the
native carrier `IsRestrictedFamily.addSubgroup E (fun _ ↦ 1)` with
`C₀(WithDiscreteTopology (σ →₀ ℕ), E)`. We transport the sup seminorm along this additive
equivalence. It is a norm when the coefficient seminorm is a norm, and it is complete when
the coefficient space is complete.

The coefficient comparison is linearly isometric for every bounded coefficient-module action.
Finite-support inclusions preserve single-coordinate norms, and every restricted family is
the unconditional sum of its single coefficients. Consequently finite-support families are
dense. For ring-valued coefficients this norm agrees with the existing unit Gauss norm.

The construction extends the scalar coefficient comparison in
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Coefficients`, using the coordinate expansion and
completeness of `ZeroAtInftyContinuousMap` rather than constructing another sup norm.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

open Filter
open scoped Topology ZeroAtInfty

namespace TauCeti.MvPowerSeries

variable {σ E : Type*} [SeminormedAddCommGroup E]

/-- At unit polyradius, restricted families are exactly the null coefficient families. -/
theorem isRestrictedFamily_one_iff {a : (σ →₀ ℕ) → E} :
    IsRestrictedFamily (fun _ ↦ 1) a ↔ Tendsto a cofinite (𝓝 0) := by
  simpa [isRestrictedFamily_iff] using
    (tendsto_zero_iff_norm_tendsto_zero (f := a) (a := cofinite)).symm

namespace IsRestrictedFamily

/-- Taking coefficients identifies unit-radius restricted families with discrete null families. -/
noncomputable def coeffAddEquiv :
    IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1) ≃+ C₀(WithDiscreteTopology (σ →₀ ℕ), E) where
  toFun a := ZeroAtInftyContinuousMap.mkOfDiscrete (fun t ↦ a.1 t.ofTopology)
    ((isRestrictedFamily_one_iff.mp (mem_addSubgroup.mp a.2)).comp
      (WithTopology.ofTopology_injective ⊥).tendsto_cofinite)
  invFun f := ⟨fun t ↦ f (.toTopology ⊥ t),
    mem_addSubgroup.mpr (isRestrictedFamily_one_iff.mpr (f.tendsto_cofinite.comp
      (WithTopology.toTopology_injective ⊥).tendsto_cofinite))⟩
  left_inv a := by
    apply Subtype.ext
    funext t
    simp only [ZeroAtInftyContinuousMap.coe_mkOfDiscrete]
  right_inv f := by
    ext t
    simp only [ZeroAtInftyContinuousMap.coe_mkOfDiscrete]
  map_add' a b := by
    ext t
    simp only [ZeroAtInftyContinuousMap.coe_mkOfDiscrete, ZeroAtInftyContinuousMap.add_apply]
    rfl

/-- The additive coefficient comparison evaluates by taking the indicated coefficient. -/
@[simp]
theorem coeffAddEquiv_apply (a : IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1)) (t : σ →₀ ℕ) :
    coeffAddEquiv a (.toTopology ⊥ t) = a.1 t := by
  simp [coeffAddEquiv, ZeroAtInftyContinuousMap.coe_mkOfDiscrete]

/-- The inverse additive comparison has the prescribed coefficients. -/
@[simp]
theorem coeffAddEquiv_symm_apply (f : C₀(WithDiscreteTopology (σ →₀ ℕ), E))
    (t : σ →₀ ℕ) : (coeffAddEquiv.symm f).1 t = f (.toTopology ⊥ t) := (rfl)

/-- The sup seminorm of the coefficients on unit-radius restricted families. -/
noncomputable instance instSeminormedAddCommGroup :
    SeminormedAddCommGroup (IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1)) :=
  SeminormedAddCommGroup.induced _ _ coeffAddEquiv.toAddMonoidHom

/-- Unit-radius restricted families are normed when their coefficients are normed. -/
noncomputable instance instNormedAddCommGroup {F : Type*} [NormedAddCommGroup F] :
    NormedAddCommGroup (IsRestrictedFamily.addSubgroup F (fun _ : σ ↦ 1)) :=
  NormedAddCommGroup.induced _ _ coeffAddEquiv.toAddMonoidHom coeffAddEquiv.injective

/-- The Gauss uniformity, induced by the sup metric on null coefficient families. -/
noncomputable instance uniformSpace :
    UniformSpace (IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1)) :=
  instSeminormedAddCommGroup.toUniformSpace

/-- The Gauss topology, induced by the sup metric on null coefficient families. -/
noncomputable instance topologicalSpace :
    TopologicalSpace (IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1)) :=
  instSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace

/-- Taking coefficients preserves the unit Gauss seminorm. -/
@[simp]
theorem norm_coeffAddEquiv (a : IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1)) :
    ‖coeffAddEquiv a‖ = ‖a‖ := (rfl)

/-- Taking coefficients preserves the unit Gauss seminorm distance. -/
theorem isometry_coeffAddEquiv : Isometry (coeffAddEquiv (σ := σ) (E := E)) :=
  AddMonoidHomClass.isometry_of_norm coeffAddEquiv fun _ ↦ rfl

/-- Every coefficient is bounded by the unit Gauss seminorm. -/
theorem norm_coeff_le (a : IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1))
    (t : σ →₀ ℕ) : ‖a.1 t‖ ≤ ‖a‖ :=
  by
    rw [← norm_coeffAddEquiv, ← coeffAddEquiv_apply]
    exact ZeroAtInftyContinuousMap.norm_coe_le_norm _ _

/-- A nonnegative bound on the unit Gauss seminorm is equivalent to all coefficient bounds. -/
theorem norm_le_iff {a : IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1)} {C : ℝ} (hC : 0 ≤ C) :
    ‖a‖ ≤ C ↔ ∀ t, ‖a.1 t‖ ≤ C := by
  constructor
  · exact fun h t ↦ (norm_coeff_le a t).trans h
  · intro h
    rw [← norm_coeffAddEquiv]
    exact (ZeroAtInftyContinuousMap.norm_le (f := coeffAddEquiv a) hC).2 fun t ↦ by
      rcases t with ⟨t⟩
      simpa only [coeffAddEquiv_apply] using h t

/-- The unit Gauss seminorm inherits the ultrametric inequality from its coefficients. -/
instance [IsUltrametricDist E] :
    IsUltrametricDist (IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1)) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun a b ↦
    (norm_le_iff (le_max_of_le_left (norm_nonneg a))).2 fun t ↦ by
      simpa only [AddSubgroup.coe_add, Pi.add_apply] using
        (IsUltrametricDist.isNonarchimedean_norm (a.1 t) (b.1 t)).trans
          (max_le_max (norm_coeff_le a t) (norm_coeff_le b t))

/-- The unit Gauss seminorm is attained by a coefficient, including for the zero family. -/
theorem exists_norm_coeff_eq_norm (a : IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1)) :
    ∃ t, ‖a.1 t‖ = ‖a‖ := by
  obtain ⟨t, ht⟩ := ZeroAtInftyContinuousMap.exists_norm_coe_eq_norm (coeffAddEquiv a)
  rcases t with ⟨t⟩
  exact ⟨t, by simpa only [coeffAddEquiv_apply, norm_coeffAddEquiv] using ht⟩

/-- Complete coefficient spaces give complete unit-radius restricted families. -/
instance [CompleteSpace E] :
    CompleteSpace (IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1)) :=
  by
    let e : IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1) ≃ᵢ
        C₀(WithDiscreteTopology (σ →₀ ℕ), E) :=
      { coeffAddEquiv.toEquiv with isometry_toFun := isometry_coeffAddEquiv }
    exact e.completeSpace

section Module

variable (R : Type*) [SeminormedRing R] [Module R E] [IsBoundedSMul R E]

/-- Taking coefficients identifies unit-radius restricted families with the discrete `c₀`
model, preserving the scalar action and the sup seminorm. -/
noncomputable def coeffLinearIsometryEquiv :
    IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1) ≃ₗᵢ[R]
      C₀(WithDiscreteTopology (σ →₀ ℕ), E) where
  toLinearEquiv :=
    { coeffAddEquiv with
      map_smul' := fun r a ↦ by
        ext t
        rcases t with ⟨t⟩
        simp [coeffAddEquiv_apply, coe_smul] }
  norm_map' _ := rfl

/-- The coefficient comparison evaluates at each exponent by taking that coefficient. -/
@[simp]
theorem coeffLinearIsometryEquiv_apply (a : IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1))
    (t : σ →₀ ℕ) :
    coeffLinearIsometryEquiv (σ := σ) (E := E) R a (.toTopology ⊥ t) = a.1 t :=
  coeffAddEquiv_apply a t

/-- The inverse coefficient comparison has the prescribed coefficients. -/
@[simp]
theorem coeffLinearIsometryEquiv_symm_apply (f : C₀(WithDiscreteTopology (σ →₀ ℕ), E))
    (t : σ →₀ ℕ) :
    ((coeffLinearIsometryEquiv (σ := σ) (E := E) R).symm f).1 t = f (.toTopology ⊥ t) :=
  coeffAddEquiv_symm_apply f t

/-- The coefficientwise scalar action is bounded for the unit Gauss seminorm. -/
instance : IsBoundedSMul R (IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1)) :=
  .of_norm_smul_le fun r a ↦ by
    simpa only [← (coeffLinearIsometryEquiv (σ := σ) (E := E) R).norm_map, map_smul] using
      norm_smul_le r (coeffLinearIsometryEquiv (σ := σ) (E := E) R a)

variable [DecidableEq (WithDiscreteTopology (σ →₀ ℕ))]

/-- A single coefficient becomes the corresponding coordinate vector. The equality decision
is a parameter because the coordinate vector occurs in the public statement. -/
@[simp]
theorem coeffLinearIsometryEquiv_ofFinsupp_single (t : σ →₀ ℕ) (e : E) :
    coeffLinearIsometryEquiv (σ := σ) (E := E) R (ofFinsupp R (fun _ ↦ 1) (Finsupp.single t e)) =
      ZeroAtInftyContinuousMap.single (.toTopology ⊥ t) e := by
  classical
  ext s
  rcases s with ⟨s⟩
  by_cases h : s = t
  · subst s
    simp [coeffLinearIsometryEquiv_apply, coe_ofFinsupp]
  · simp [coeffLinearIsometryEquiv_apply, coe_ofFinsupp,
      ZeroAtInftyContinuousMap.single_apply, h]

omit [DecidableEq (WithDiscreteTopology (σ →₀ ℕ))] in
/-- A single-coefficient family has the norm of its coefficient. -/
@[simp]
theorem norm_ofFinsupp_single (t : σ →₀ ℕ) (e : E) :
    ‖ofFinsupp R (fun _ : σ ↦ 1) (Finsupp.single t e)‖ = ‖e‖ := by
  classical
  rw [← (coeffLinearIsometryEquiv (σ := σ) (E := E) R).norm_map,
    coeffLinearIsometryEquiv_ofFinsupp_single,
    ZeroAtInftyContinuousMap.norm_single]

omit [DecidableEq (WithDiscreteTopology (σ →₀ ℕ))] in
/-- A unit-radius restricted family is the unconditional sum of its single coefficients. -/
theorem hasSum_ofFinsupp_single (a : IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1)) :
    HasSum (fun t ↦ ofFinsupp R (fun _ ↦ 1) (Finsupp.single t (a.1 t))) a := by
  classical
  apply (coeffLinearIsometryEquiv (σ := σ) (E := E) R).toContinuousLinearEquiv.hasSum'.mp
  have h := (WithTopology.equiv (σ →₀ ℕ) ⊥).symm.hasSum_iff.mpr
    (ZeroAtInftyContinuousMap.hasSum_single
      (coeffLinearIsometryEquiv (σ := σ) (E := E) R a))
  simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    coeffLinearIsometryEquiv_ofFinsupp_single, Function.comp_def, WithTopology.equiv,
    Equiv.coe_fn_symm_mk, coeffLinearIsometryEquiv_apply] using h

omit [DecidableEq (WithDiscreteTopology (σ →₀ ℕ))] in
/-- Finite-support coefficient families are dense in the unit Gauss topology. -/
theorem denseRange_ofFinsupp : DenseRange (ofFinsupp (σ := σ) R (fun _ ↦ 1) (E := E)) := by
  classical
  intro a
  exact mem_closure_of_tendsto (hasSum_ofFinsupp_single R a) <|
    .of_forall fun s ↦ ⟨∑ t ∈ s, Finsupp.single t (a.1 t), by simp⟩

end Module

/-- A normed coefficient-module action makes unit-radius restricted families a normed space. -/
instance {K : Type*} [NormedField K] [NormedSpace K E] :
    NormedSpace K (IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1)) where
  norm_smul_le := norm_smul_le

section Ring

variable {R : Type*} [NormedRing R] [IsUltrametricDist R]

/-- For ring-valued coefficients the family norm agrees with the native unit Gauss norm. -/
@[simp]
theorem norm_subringLinearEquiv
    (f : _root_.MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    ‖subringLinearEquiv f‖ = ‖f‖ := by
  apply le_antisymm
  · exact (norm_le_iff (norm_nonneg f)).2 fun t ↦
      by simpa only [coe_subringLinearEquiv] using
        _root_.MvPowerSeries.norm_coeff_le_norm f t
  · exact (_root_.MvPowerSeries.norm_le_iff (norm_nonneg _)).2 fun t ↦ by
      simpa only [Finsupp.prod, one_pow, Finset.prod_const_one, mul_one,
        coe_subringLinearEquiv] using
        norm_coeff_le (subringLinearEquiv f) t

end Ring

end IsRestrictedFamily
end TauCeti.MvPowerSeries
