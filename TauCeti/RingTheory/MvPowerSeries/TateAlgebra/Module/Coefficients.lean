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
carrier `IsRestrictedFamily.UnitRadius σ E` with
`C₀(WithDiscreteTopology (σ →₀ ℕ), E)`. We transport the sup seminorm along this additive
equivalence. It is a norm when the coefficient seminorm is a norm, and it is complete when
the coefficient space is complete.

The coefficient comparison is linearly isometric for every bounded coefficient-module action.
Finite-support inclusions preserve single-coordinate norms, and every restricted family is
the unconditional sum of its single coefficients. Consequently finite-support families are
dense. For ring-valued coefficients this norm agrees with the existing unit Gauss norm.

The scalar coefficient comparison in
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Coefficients` specializes this construction;
`IsRestrictedFamily.UnitRadius.norm_subringLinearEquiv` identifies its norm with the scalar
Gauss norm. The construction uses the coordinate expansion and completeness of
`ZeroAtInftyContinuousMap` rather than constructing another sup norm.

The one-field wrapper retains the existing algebraic restricted-family carrier, but its Gauss
topology is distinct from the subgroup's inherited pointwise topology. Only the additive and
module structures are transported from that subgroup.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

open Filter
open scoped Topology ZeroAtInfty

namespace TauCeti.MvPowerSeries

variable {σ E : Type*} [SeminormedAddCommGroup E]

namespace IsRestrictedFamily

/-- Unit-radius restricted coefficient families with their Gauss topology. The wrapper keeps
this topology separate from the pointwise topology inherited by the algebraic subgroup. -/
structure UnitRadius (σ E : Type*) [SeminormedAddCommGroup E] where
  /-- Regard an algebraic unit-radius restricted family as a Gauss-topological family. -/
  ofAddSubgroup ::
  /-- The underlying algebraic restricted family. -/
  toAddSubgroup : IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1)

namespace UnitRadius

instance : CoeFun (UnitRadius σ E) (fun _ ↦ (σ →₀ ℕ) → E) :=
  ⟨fun a ↦ a.toAddSubgroup⟩

/-- Unit-radius families are determined by their coefficients. -/
@[ext]
theorem ext {a b : UnitRadius σ E} (h : ∀ t, a t = b t) : a = b := by
  cases a
  cases b
  congr 1
  exact IsRestrictedFamily.ext h

@[simp]
theorem toAddSubgroup_ofAddSubgroup (a : IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1)) :
    (ofAddSubgroup a).toAddSubgroup = a := (rfl)

@[simp]
theorem ofAddSubgroup_toAddSubgroup (a : UnitRadius σ E) :
    ofAddSubgroup a.toAddSubgroup = a := (rfl)

@[simp]
theorem ofAddSubgroup_apply (a : IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1))
    (t : σ →₀ ℕ) : ofAddSubgroup a t = a.1 t := (rfl)

noncomputable instance : AddCommGroup (UnitRadius σ E) :=
  Equiv.addCommGroup
    { toFun := toAddSubgroup
      invFun := ofAddSubgroup
      left_inv := ofAddSubgroup_toAddSubgroup
      right_inv := toAddSubgroup_ofAddSubgroup }

@[simp]
theorem toAddSubgroup_add (a b : UnitRadius σ E) :
    (a + b).toAddSubgroup = a.toAddSubgroup + b.toAddSubgroup := (rfl)

@[simp]
theorem zero_apply (t : σ →₀ ℕ) : (0 : UnitRadius σ E) t = 0 := (rfl)

@[simp]
theorem neg_apply (a : UnitRadius σ E) (t : σ →₀ ℕ) : (-a) t = -a t := (rfl)

@[simp]
theorem sub_apply (a b : UnitRadius σ E) (t : σ →₀ ℕ) : (a - b) t = a t - b t := (rfl)

theorem add_apply (a b : UnitRadius σ E) (t : σ →₀ ℕ) : (a + b) t = a t + b t := by
  simpa only [AddSubgroup.coe_add, Pi.add_apply] using
    congrArg (fun f : IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1) ↦
      (f : (σ →₀ ℕ) → E) t) (toAddSubgroup_add a b)

/-- The Gauss-topological family and the existing algebraic subgroup have the same addition. -/
noncomputable def toAddSubgroupAddEquiv :
    UnitRadius σ E ≃+ IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1) where
  toFun := toAddSubgroup
  invFun := ofAddSubgroup
  left_inv := ofAddSubgroup_toAddSubgroup
  right_inv := toAddSubgroup_ofAddSubgroup
  map_add' := toAddSubgroup_add

@[simp]
theorem toAddSubgroupAddEquiv_apply (a : UnitRadius σ E) :
    toAddSubgroupAddEquiv a = a.toAddSubgroup := (rfl)

@[simp]
theorem toAddSubgroupAddEquiv_symm_apply
    (a : IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1)) :
    toAddSubgroupAddEquiv.symm a = ofAddSubgroup a := (rfl)

/-- Taking coefficients identifies unit-radius restricted families with discrete null families. -/
noncomputable def coeffAddEquiv :
    UnitRadius σ E ≃+ C₀(WithDiscreteTopology (σ →₀ ℕ), E) where
  toFun a := ZeroAtInftyContinuousMap.mkOfDiscrete (fun t ↦ a t.ofTopology)
    ((isRestrictedFamily_one_iff.mp (mem_addSubgroup.mp a.toAddSubgroup.2)).comp
      (WithTopology.ofTopology_injective ⊥).tendsto_cofinite)
  invFun f := ofAddSubgroup ⟨fun t ↦ f (.toTopology ⊥ t),
    mem_addSubgroup.mpr (isRestrictedFamily_one_iff.mpr (f.tendsto_cofinite.comp
      (WithTopology.toTopology_injective ⊥).tendsto_cofinite))⟩
  left_inv a := by
    apply ext
    intro t
    simp only [ZeroAtInftyContinuousMap.coe_mkOfDiscrete]
  right_inv f := by
    ext t
    simp only [ZeroAtInftyContinuousMap.coe_mkOfDiscrete]
  map_add' a b := by
    ext t
    simp only [ZeroAtInftyContinuousMap.coe_mkOfDiscrete, ZeroAtInftyContinuousMap.add_apply,
      add_apply]

/-- The additive coefficient comparison evaluates by taking the indicated coefficient. -/
@[simp]
theorem coeffAddEquiv_apply (a : UnitRadius σ E) (t : σ →₀ ℕ) :
    coeffAddEquiv a (.toTopology ⊥ t) = a t := by
  simp [coeffAddEquiv, ZeroAtInftyContinuousMap.coe_mkOfDiscrete]

/-- The inverse additive comparison has the prescribed coefficients. -/
@[simp]
theorem coeffAddEquiv_symm_apply (f : C₀(WithDiscreteTopology (σ →₀ ℕ), E))
    (t : σ →₀ ℕ) : (coeffAddEquiv.symm f) t = f (.toTopology ⊥ t) := (rfl)

/-- The sup seminorm of the coefficients on unit-radius restricted families. -/
noncomputable instance instSeminormedAddCommGroup :
    SeminormedAddCommGroup (UnitRadius σ E) :=
  SeminormedAddCommGroup.induced _ _ coeffAddEquiv.toAddMonoidHom

/-- Unit-radius restricted families are normed when their coefficients are normed. -/
noncomputable instance instNormedAddCommGroup {F : Type*} [NormedAddCommGroup F] :
    NormedAddCommGroup (UnitRadius σ F) :=
  NormedAddCommGroup.induced _ _ coeffAddEquiv.toAddMonoidHom coeffAddEquiv.injective

/-- Taking coefficients preserves the unit Gauss seminorm. -/
@[simp]
theorem norm_coeffAddEquiv (a : UnitRadius σ E) :
    ‖coeffAddEquiv a‖ = ‖a‖ := (rfl)

/-- Taking coefficients preserves the unit Gauss seminorm distance. -/
theorem isometry_coeffAddEquiv : Isometry (coeffAddEquiv (σ := σ) (E := E)) :=
  AddMonoidHomClass.isometry_of_norm coeffAddEquiv fun _ ↦ rfl

/-- Every coefficient is bounded by the unit Gauss seminorm. -/
theorem norm_coeff_le_norm (a : UnitRadius σ E)
    (t : σ →₀ ℕ) : ‖a t‖ ≤ ‖a‖ :=
  by
    rw [← norm_coeffAddEquiv, ← coeffAddEquiv_apply]
    exact ZeroAtInftyContinuousMap.norm_coe_le_norm _ _

/-- A nonnegative bound on the unit Gauss seminorm is equivalent to all coefficient bounds. -/
theorem norm_le_iff {a : UnitRadius σ E} {C : ℝ} (hC : 0 ≤ C) :
    ‖a‖ ≤ C ↔ ∀ t, ‖a t‖ ≤ C := by
  constructor
  · exact fun h t ↦ (norm_coeff_le_norm a t).trans h
  · intro h
    rw [← norm_coeffAddEquiv]
    exact (ZeroAtInftyContinuousMap.norm_le (f := coeffAddEquiv a) hC).2 fun t ↦ by
      rcases t with ⟨t⟩
      simpa only [coeffAddEquiv_apply] using h t

/-- The unit Gauss seminorm inherits the ultrametric inequality from its coefficients. -/
instance [IsUltrametricDist E] :
    IsUltrametricDist (UnitRadius σ E) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun a b ↦
    (norm_le_iff (le_max_of_le_left (norm_nonneg a))).2 fun t ↦ by
      simpa only [add_apply] using
        (IsUltrametricDist.isNonarchimedean_norm (a t) (b t)).trans
          (max_le_max (norm_coeff_le_norm a t) (norm_coeff_le_norm b t))

/-- The unit Gauss seminorm is attained by a coefficient, including for the zero family. -/
theorem exists_norm_coeff_eq_norm (a : UnitRadius σ E) :
    ∃ t, ‖a t‖ = ‖a‖ := by
  obtain ⟨t, ht⟩ := ZeroAtInftyContinuousMap.exists_norm_coe_eq_norm (coeffAddEquiv a)
  rcases t with ⟨t⟩
  exact ⟨t, by simpa only [coeffAddEquiv_apply, norm_coeffAddEquiv] using ht⟩

/-- Complete coefficient spaces give complete unit-radius restricted families. -/
instance [CompleteSpace E] :
    CompleteSpace (UnitRadius σ E) :=
  by
    let e : UnitRadius σ E ≃ᵢ
        C₀(WithDiscreteTopology (σ →₀ ℕ), E) :=
      { coeffAddEquiv.toEquiv with isometry_toFun := isometry_coeffAddEquiv }
    exact e.completeSpace

section Module

variable (R : Type*) [SeminormedRing R] [Module R E] [IsBoundedSMul R E]

noncomputable instance : Module R (UnitRadius σ E) :=
  (toAddSubgroupAddEquiv (σ := σ) (E := E)).module R

/-- Forgetting the Gauss topology preserves the coefficient-module action. -/
noncomputable def toAddSubgroupLinearEquiv :
    UnitRadius σ E ≃ₗ[R] IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1) :=
  (toAddSubgroupAddEquiv (σ := σ) (E := E)).linearEquiv R

@[simp]
theorem toAddSubgroupLinearEquiv_apply (a : UnitRadius σ E) :
    toAddSubgroupLinearEquiv R a = a.toAddSubgroup := (rfl)

@[simp]
theorem toAddSubgroupLinearEquiv_symm_apply
    (a : IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1)) :
    (toAddSubgroupLinearEquiv (σ := σ) R).symm a = ofAddSubgroup a := (rfl)

@[simp]
theorem smul_apply (r : R) (a : UnitRadius σ E) (t : σ →₀ ℕ) :
    (r • a) t = r • a t := by
  simpa only [toAddSubgroupLinearEquiv_apply, coe_smul, Pi.smul_apply] using
    congrArg (fun b : IsRestrictedFamily.addSubgroup E (fun _ : σ ↦ 1) ↦ b.1 t)
      ((toAddSubgroupLinearEquiv R).map_smul r a)

/-- Include finite-support coefficient families in the Gauss-topological carrier. -/
noncomputable def ofFinsupp : ((σ →₀ ℕ) →₀ E) →ₗ[R] UnitRadius σ E :=
  (toAddSubgroupLinearEquiv R).symm.toLinearMap.comp
    (IsRestrictedFamily.ofFinsupp R (fun _ ↦ 1))

@[simp]
theorem ofFinsupp_apply (a : (σ →₀ ℕ) →₀ E) (t : σ →₀ ℕ) :
    ofFinsupp R a t = a t := by
  simp only [ofFinsupp, LinearMap.comp_apply, LinearEquiv.coe_coe,
    toAddSubgroupLinearEquiv_symm_apply, coe_ofFinsupp]

/-- Taking coefficients identifies unit-radius restricted families with the discrete `c₀`
model, preserving the scalar action and the sup seminorm. -/
noncomputable def coeffLinearIsometryEquiv :
    UnitRadius σ E ≃ₗᵢ[R]
      C₀(WithDiscreteTopology (σ →₀ ℕ), E) where
  toLinearEquiv :=
    { coeffAddEquiv with
      map_smul' := fun r a ↦ by
        ext t
        rcases t with ⟨t⟩
        simp [coeffAddEquiv_apply] }
  norm_map' _ := rfl

/-- The coefficient comparison evaluates at each exponent by taking that coefficient. -/
@[simp]
theorem coeffLinearIsometryEquiv_apply (a : UnitRadius σ E)
    (t : σ →₀ ℕ) :
    coeffLinearIsometryEquiv (σ := σ) (E := E) R a (.toTopology ⊥ t) = a t :=
  coeffAddEquiv_apply a t

/-- The inverse coefficient comparison has the prescribed coefficients. -/
@[simp]
theorem coeffLinearIsometryEquiv_symm_apply (f : C₀(WithDiscreteTopology (σ →₀ ℕ), E))
    (t : σ →₀ ℕ) :
    ((coeffLinearIsometryEquiv (σ := σ) (E := E) R).symm f) t = f (.toTopology ⊥ t) :=
  coeffAddEquiv_symm_apply f t

/-- The coefficientwise scalar action is bounded for the unit Gauss seminorm. -/
instance : IsBoundedSMul R (UnitRadius σ E) :=
  .of_norm_smul_le fun r a ↦ by
    simpa only [← (coeffLinearIsometryEquiv (σ := σ) (E := E) R).norm_map, map_smul] using
      norm_smul_le r (coeffLinearIsometryEquiv (σ := σ) (E := E) R a)

variable [DecidableEq (WithDiscreteTopology (σ →₀ ℕ))]

/-- A single coefficient becomes the corresponding coordinate vector. The equality decision
is a parameter because the coordinate vector occurs in the public statement. -/
@[simp]
theorem coeffLinearIsometryEquiv_ofFinsupp_single (t : σ →₀ ℕ) (e : E) :
    coeffLinearIsometryEquiv (σ := σ) (E := E) R (ofFinsupp R (Finsupp.single t e)) =
      ZeroAtInftyContinuousMap.single (.toTopology ⊥ t) e := by
  classical
  ext s
  rcases s with ⟨s⟩
  by_cases h : s = t
  · subst s
    simp [coeffLinearIsometryEquiv_apply, ofFinsupp_apply]
  · simp [coeffLinearIsometryEquiv_apply, ofFinsupp_apply,
      ZeroAtInftyContinuousMap.single_apply, h]

omit [DecidableEq (WithDiscreteTopology (σ →₀ ℕ))] in
/-- A single-coefficient family has the norm of its coefficient. -/
@[simp]
theorem norm_ofFinsupp_single (t : σ →₀ ℕ) (e : E) :
    ‖ofFinsupp R (Finsupp.single t e)‖ = ‖e‖ := by
  classical
  rw [← (coeffLinearIsometryEquiv (σ := σ) (E := E) R).norm_map,
    coeffLinearIsometryEquiv_ofFinsupp_single,
    ZeroAtInftyContinuousMap.norm_single]

omit [DecidableEq (WithDiscreteTopology (σ →₀ ℕ))] in
/-- A unit-radius restricted family is the unconditional sum of its single coefficients. -/
theorem hasSum_ofFinsupp_single (a : UnitRadius σ E) :
    HasSum (fun t ↦ ofFinsupp R (Finsupp.single t (a t))) a := by
  classical
  apply (coeffLinearIsometryEquiv (σ := σ) (E := E) R).toContinuousLinearEquiv.hasSum'.mp
  have h := ((WithTopology.toTopology_injective ⊥).hasSum_iff
    (fun t ht ↦ (ht ((WithTopology.toTopology_surjective ⊥) t)).elim)).mpr
    (ZeroAtInftyContinuousMap.hasSum_single
      (coeffLinearIsometryEquiv (σ := σ) (E := E) R a))
  simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    coeffLinearIsometryEquiv_ofFinsupp_single, Function.comp_def,
    coeffLinearIsometryEquiv_apply] using h

omit [DecidableEq (WithDiscreteTopology (σ →₀ ℕ))] in
/-- Finite-support coefficient families are dense in the unit Gauss topology. -/
theorem denseRange_ofFinsupp : DenseRange (ofFinsupp (σ := σ) (E := E) R) := by
  classical
  intro a
  exact mem_closure_of_tendsto (hasSum_ofFinsupp_single R a) <|
    .of_forall fun s ↦ ⟨∑ t ∈ s, Finsupp.single t (a t), by simp⟩

end Module

/-- A normed coefficient-module action makes unit-radius restricted families a normed space. -/
noncomputable instance {K : Type*} [NormedField K] [NormedSpace K E] :
    NormedSpace K (UnitRadius σ E) where
  norm_smul_le := norm_smul_le

section Ring

variable {R : Type*} [NormedRing R] [IsUltrametricDist R]

/-- For ring-valued coefficients the family norm agrees with the native unit Gauss norm. -/
@[simp]
theorem norm_subringLinearEquiv
    (f : _root_.MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    ‖ofAddSubgroup (IsRestrictedFamily.subringLinearEquiv f)‖ = ‖f‖ := by
  apply le_antisymm
  · exact (norm_le_iff (norm_nonneg f)).2 fun t ↦
      by simpa only [ofAddSubgroup_apply, coe_subringLinearEquiv] using
        _root_.MvPowerSeries.norm_coeff_le_norm f t
  · exact (_root_.MvPowerSeries.norm_le_iff (norm_nonneg _)).2 fun t ↦ by
      simpa only [Finsupp.prod, one_pow, Finset.prod_const_one, mul_one,
        ofAddSubgroup_apply, coe_subringLinearEquiv] using
        norm_coeff_le_norm (ofAddSubgroup (IsRestrictedFamily.subringLinearEquiv f)) t

end Ring

end UnitRadius
end IsRestrictedFamily
end TauCeti.MvPowerSeries
