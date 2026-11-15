/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Finsupp.Weight
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Coefficients

/-!
# The coefficient model of the unit-radius Tate algebra

At unit polyradius, restrictedness says exactly that the coefficient family tends to zero along
the cofinite filter; at a constant radius `ρ`, it says that `‖aₜ‖ ρ^|t|` tends to zero. The
unit-radius case identifies the native restricted-series module with the model space
`C₀(WithDiscreteTopology (σ →₀ ℕ), R)`. The identification is linear and isometric for the Gauss
norm, and it sends a restricted monomial to the corresponding coordinate vector.

The construction specializes the module-valued coefficient comparison
`TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss.coeffLinearIsometryEquiv`; the family seminorm
agrees with the Gauss norm on the native restricted-series subring.

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

variable {σ R : Type*} [NormedRing R]

/-- Restrictedness at unit polyradius is convergence of the coefficient norms to zero. -/
theorem isRestricted_one_iff {f : MvPowerSeries σ R} :
    IsRestricted (fun _ ↦ 1) f ↔ Tendsto (fun t ↦ ‖coeff t f‖) cofinite (𝓝 0) := by
  simp [IsRestricted]

/-- Restrictedness at a constant radius `ρ`: the weighted coefficient norms `‖aᵥ‖ ρ^|ν|` tend to
zero. The case `ρ = 1` is `isRestricted_one_iff`. -/
theorem isRestricted_const_iff {f : MvPowerSeries σ R} {ρ : ℝ} :
    IsRestricted (fun _ : σ ↦ ρ) f ↔
      Tendsto (fun t : σ →₀ ℕ ↦ ‖coeff t f‖ * ρ ^ t.degree) cofinite (𝓝 0) := by
  simp only [IsRestricted, Finsupp.prod_pow_eq_pow_degree]

end MvPowerSeries

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- Taking coefficients is a linear isometric equivalence from the unit-radius restricted-series
module to the space of coefficient families vanishing at infinity on the discrete exponent set. -/
noncomputable def restrictedCoeffLinearIsometryEquiv :
    IsRestricted.subring (R := R) (fun _ : σ ↦ 1) ≃ₗᵢ[R]
      C₀(WithDiscreteTopology (σ →₀ ℕ), R) where
  toLinearEquiv := (IsRestrictedFamily.subringLinearEquiv.restrictScalars R).trans
    ((IsRestrictedFamily.Gauss.toAddSubgroupLinearEquiv R).symm.trans
      (IsRestrictedFamily.Gauss.coeffLinearIsometryEquiv (σ := σ) (E := R) R).toLinearEquiv)
  norm_map' f := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      LinearIsometryEquiv.coe_toLinearEquiv,
      IsRestrictedFamily.Gauss.toAddSubgroupLinearEquiv_symm_apply,
      LinearIsometryEquiv.norm_map, IsRestrictedFamily.Gauss.norm_subringLinearEquiv]

/-- The coefficient isometry evaluates a restricted series at each exponent by taking that
coefficient. -/
@[simp]
theorem restrictedCoeffLinearIsometryEquiv_apply
    (f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) (t : σ →₀ ℕ) :
    restrictedCoeffLinearIsometryEquiv f (.toTopology ⊥ t) =
      coeff t (f : _root_.MvPowerSeries σ R) := by
  rw [← LinearIsometryEquiv.coe_toLinearEquiv]
  simp only [restrictedCoeffLinearIsometryEquiv, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, LinearIsometryEquiv.coe_toLinearEquiv,
    IsRestrictedFamily.Gauss.coeffLinearIsometryEquiv_apply,
    IsRestrictedFamily.Gauss.toAddSubgroupLinearEquiv_symm_apply,
    IsRestrictedFamily.coe_subringLinearEquiv]

/-- The inverse coefficient isometry builds the restricted series with the prescribed null
coefficient family. -/
@[simp]
theorem restrictedCoeffLinearIsometryEquiv_symm_apply
    (a : C₀(WithDiscreteTopology (σ →₀ ℕ), R)) (t : σ →₀ ℕ) :
    coeff t ((restrictedCoeffLinearIsometryEquiv.symm a :
      IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) : _root_.MvPowerSeries σ R) =
      a (.toTopology ⊥ t) := by
  simpa using (restrictedCoeffLinearIsometryEquiv_apply
    (restrictedCoeffLinearIsometryEquiv.symm a) t).symm

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
  simp [restrictedCoeffLinearIsometryEquiv_apply, coeff_monomial,
    ZeroAtInftyContinuousMap.single_apply]

end TauCeti.MvPowerSeries
