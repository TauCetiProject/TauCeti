/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete

/-!
# The coefficient model of the unit-radius Tate algebra

At unit polyradius, restrictedness says exactly that the coefficient family tends to zero along
the cofinite filter. This identifies the native restricted-series module with the model space
`C₀(WithDiscreteTopology (σ →₀ ℕ), R)`. The identification is linear and isometric for the Gauss
norm, and it sends a restricted monomial to the corresponding coordinate vector.

The discrete-topology wrapper is essential when `σ` is infinite: the exponent type may carry a
different topology from its use here as the discrete index of a null family.

## Main result

* `TauCeti.MvPowerSeries.restrictedCoeffLinearIsometryEquiv`: the coefficient linear isometry
  between unit-radius restricted series and null coefficient families.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

noncomputable section

open Filter
open scoped Topology ZeroAtInfty

namespace MvPowerSeries

variable {σ R : Type*} [NormedCommRing R]

/-- Restrictedness at unit polyradius is convergence of the coefficient norms to zero. -/
theorem isRestricted_one_iff {f : MvPowerSeries σ R} :
    IsRestricted (fun _ ↦ 1) f ↔ Tendsto (fun t ↦ ‖coeff t f‖) cofinite (𝓝 0) := by
  simp [IsRestricted]

end MvPowerSeries

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R]

private noncomputable def toRestrictedCoeff
    (f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    C₀(WithDiscreteTopology (σ →₀ ℕ), R) :=
  ZeroAtInftyContinuousMap.mkOfDiscrete
    (fun t ↦ coeff t.ofTopology (f : _root_.MvPowerSeries σ R)) <|
      tendsto_zero_iff_norm_tendsto_zero.mpr (by
        have hf := isRestricted_one_iff.mp f.2
        have hinj : Function.Injective
            (WithTopology.ofTopology : WithDiscreteTopology (σ →₀ ℕ) → (σ →₀ ℕ)) :=
          fun _ _ h ↦ WithTopology.ext h
        exact hf.comp hinj.tendsto_cofinite)

private theorem toRestrictedCoeff_apply
    (f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) (t : σ →₀ ℕ) :
    toRestrictedCoeff f (WithTopology.toTopology ⊥ t) =
      coeff t (f : _root_.MvPowerSeries σ R) := by
  change ZeroAtInftyContinuousMap.mkOfDiscrete _ _ (WithTopology.toTopology ⊥ t) = _
  rw [congrFun (ZeroAtInftyContinuousMap.coe_mkOfDiscrete _ _)
    (WithTopology.toTopology ⊥ t)]

private noncomputable def ofRestrictedCoeff
    (a : C₀(WithDiscreteTopology (σ →₀ ℕ), R)) :
    IsRestricted.subring (R := R) (fun _ : σ ↦ 1) :=
  ⟨(fun t ↦ a (.toTopology ⊥ t) : _root_.MvPowerSeries σ R), by
    have hinj : Function.Injective
        (WithTopology.toTopology ⊥ : (σ →₀ ℕ) → WithDiscreteTopology (σ →₀ ℕ)) :=
      fun _ _ h ↦ congrArg WithTopology.ofTopology h
    have ha := tendsto_zero_iff_norm_tendsto_zero.mp <|
      a.tendsto_cofinite.comp hinj.tendsto_cofinite
    exact isRestricted_one_iff.mpr ha⟩

private theorem ofRestrictedCoeff_apply
    (a : C₀(WithDiscreteTopology (σ →₀ ℕ), R)) (t : σ →₀ ℕ) :
    coeff t ((ofRestrictedCoeff a : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
      _root_.MvPowerSeries σ R) = a (.toTopology ⊥ t) := by
  rfl

private noncomputable def restrictedCoeffLinearEquiv :
    IsRestricted.subring (R := R) (fun _ : σ ↦ 1) ≃ₗ[R]
      C₀(WithDiscreteTopology (σ →₀ ℕ), R) where
  toFun := toRestrictedCoeff
  invFun := ofRestrictedCoeff
  left_inv f := by
    apply Subtype.ext
    apply _root_.MvPowerSeries.ext
    intro t
    rw [ofRestrictedCoeff_apply, toRestrictedCoeff_apply]
  right_inv a := by
    apply ZeroAtInftyContinuousMap.ext
    intro t
    rcases t with ⟨t⟩
    rw [toRestrictedCoeff_apply, ofRestrictedCoeff_apply]
  map_add' f g := by
    apply ZeroAtInftyContinuousMap.ext
    rintro ⟨t⟩
    simp only [toRestrictedCoeff_apply, ZeroAtInftyContinuousMap.add_apply]
    rfl
  map_smul' r f := by
    apply ZeroAtInftyContinuousMap.ext
    rintro ⟨t⟩
    simp only [toRestrictedCoeff_apply, ZeroAtInftyContinuousMap.smul_apply, RingHom.id_apply]
    rw [Algebra.smul_def]
    change coeff t (C r * (f : _root_.MvPowerSeries σ R)) =
      r * coeff t (f : _root_.MvPowerSeries σ R)
    exact coeff_C_mul t (f : _root_.MvPowerSeries σ R) r

private theorem restrictedCoeffLinearEquiv_apply
    (f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) (t : σ →₀ ℕ) :
    restrictedCoeffLinearEquiv f (.toTopology ⊥ t) =
      coeff t (f : _root_.MvPowerSeries σ R) := by
  exact toRestrictedCoeff_apply f t

private theorem restrictedCoeffLinearEquiv_symm_apply
    (a : C₀(WithDiscreteTopology (σ →₀ ℕ), R)) (t : σ →₀ ℕ) :
    coeff t ((restrictedCoeffLinearEquiv.symm a :
      IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) : _root_.MvPowerSeries σ R) =
      a (.toTopology ⊥ t) := by
  simpa using (restrictedCoeffLinearEquiv_apply (restrictedCoeffLinearEquiv.symm a) t).symm

private theorem norm_restrictedCoeffLinearEquiv
    (f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    ‖restrictedCoeffLinearEquiv f‖ = ‖f‖ := by
  apply le_antisymm
  · exact (ZeroAtInftyContinuousMap.norm_le (norm_nonneg f)).2 fun t ↦ by
      rw [restrictedCoeffLinearEquiv_apply]
      simpa using _root_.MvPowerSeries.norm_coeff_mul_prod_le f t.ofTopology
  · exact (_root_.MvPowerSeries.norm_le_iff (norm_nonneg _)).2 fun t ↦ by
      rw [← restrictedCoeffLinearEquiv_apply]
      simpa using ZeroAtInftyContinuousMap.norm_coe_le_norm
        (restrictedCoeffLinearEquiv f) (.toTopology ⊥ t)

/-- Taking coefficients is a linear isometric equivalence from the unit-radius restricted-series
module to the space of coefficient families vanishing at infinity on the discrete exponent set. -/
noncomputable def restrictedCoeffLinearIsometryEquiv :
    IsRestricted.subring (R := R) (fun _ : σ ↦ 1) ≃ₗᵢ[R]
      C₀(WithDiscreteTopology (σ →₀ ℕ), R) where
  toLinearEquiv := restrictedCoeffLinearEquiv
  norm_map' := norm_restrictedCoeffLinearEquiv

/-- The coefficient isometry evaluates a restricted series at each exponent by taking that
coefficient. -/
@[simp]
theorem restrictedCoeffLinearIsometryEquiv_apply
    (f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) (t : σ →₀ ℕ) :
    restrictedCoeffLinearIsometryEquiv f (.toTopology ⊥ t) =
      coeff t (f : _root_.MvPowerSeries σ R) := by
  exact restrictedCoeffLinearEquiv_apply f t

/-- The inverse coefficient isometry builds the restricted series with the prescribed null
coefficient family. -/
@[simp]
theorem restrictedCoeffLinearIsometryEquiv_symm_apply
    (a : C₀(WithDiscreteTopology (σ →₀ ℕ), R)) (t : σ →₀ ℕ) :
    coeff t ((restrictedCoeffLinearIsometryEquiv.symm a :
      IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) : _root_.MvPowerSeries σ R) =
      a (.toTopology ⊥ t) := by
  exact restrictedCoeffLinearEquiv_symm_apply a t

/-- A classical equality decision procedure for the discrete exponent set, used to form
coordinate vectors. -/
noncomputable local instance restrictedExponentDecidableEq :
    DecidableEq (WithDiscreteTopology (σ →₀ ℕ)) := Classical.decEq _

/-- A classical equality decision procedure for variables, used to compute monomial
coefficients. -/
noncomputable local instance restrictedVariableDecidableEq : DecidableEq σ := Classical.decEq _

/-- A restricted monomial maps to the coordinate vector at its exponent. -/
@[simp]
theorem restrictedCoeffLinearIsometryEquiv_monomial (t : σ →₀ ℕ) (a : R) :
    restrictedCoeffLinearIsometryEquiv
        (⟨monomial t a, isRestricted_monomial _ t a⟩ :
          IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) =
      ZeroAtInftyContinuousMap.single (.toTopology ⊥ t) a := by
  ext s
  rcases s with ⟨s⟩
  rw [restrictedCoeffLinearIsometryEquiv_apply]
  by_cases h : s = t
  · subst t
    simp
  · have hw : WithTopology.toTopology ⊥ s ≠ WithTopology.toTopology ⊥ t :=
      fun hst ↦ h (congrArg WithTopology.ofTopology hst)
    rw [coeff_monomial]
    simp [ZeroAtInftyContinuousMap.single_apply, h, hw]

end TauCeti.MvPowerSeries
