/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Norm
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
import Mathlib.Topology.WithTopology

/-!
# The coefficient model of module-valued restricted series

At unit polyradius, a restricted family with coefficients in a seminormed additive group `E` is
precisely a null family on the discrete exponent set. Taking coefficients identifies the carrier
`IsRestrictedFamily.Gauss (fun _ : σ ↦ 1) E` with `C₀(WithDiscreteTopology (σ →₀ ℕ), E)`. The
coefficient equivalence preserves the Gauss seminorm defined in `Module.Norm`. It is a norm when
the coefficient seminorm is a norm, and it is complete when the coefficient space is complete.

The coefficient comparison is linearly isometric for every bounded coefficient-module action.
Finite-support inclusions preserve single-coordinate norms, and every restricted family is the
unconditional sum of its single coefficients. Consequently finite-support families are dense.
For ring-valued coefficients this norm agrees with the existing unit Gauss norm.

The scalar coefficient comparison in `TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Coefficients`
specializes this construction; `IsRestrictedFamily.Gauss.norm_subringLinearEquiv` identifies its
norm with the scalar Gauss norm. The coefficient comparison uses the coordinate expansion of
`ZeroAtInftyContinuousMap`.

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

namespace Gauss

/-- Taking coefficients identifies unit-radius restricted families with discrete null families. -/
noncomputable def coeffAddEquiv :
    Gauss (fun _ : σ ↦ 1) E ≃+ C₀(WithDiscreteTopology (σ →₀ ℕ), E) where
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
theorem coeffAddEquiv_apply (a : Gauss (fun _ : σ ↦ 1) E) (t : σ →₀ ℕ) :
    coeffAddEquiv a (.toTopology ⊥ t) = a t := by
  simp [coeffAddEquiv, ZeroAtInftyContinuousMap.coe_mkOfDiscrete]

/-- The inverse additive comparison has the prescribed coefficients. -/
@[simp]
theorem coeffAddEquiv_symm_apply (f : C₀(WithDiscreteTopology (σ →₀ ℕ), E))
    (t : σ →₀ ℕ) : (coeffAddEquiv.symm f) t = f (.toTopology ⊥ t) := (rfl)

/-- Taking coefficients preserves the unit Gauss seminorm. -/
@[simp]
theorem norm_coeffAddEquiv (a : Gauss (fun _ : σ ↦ 1) E) :
    ‖coeffAddEquiv a‖ = ‖a‖ := by
  apply le_antisymm
  · apply (ZeroAtInftyContinuousMap.norm_le (norm_nonneg a)).mpr
    rintro ⟨t⟩
    simpa only [coeffAddEquiv_apply, Finsupp.prod, one_pow, Finset.prod_const_one,
      mul_one] using norm_coeff_mul_prod_le a t
  · apply norm_le_iff.mpr
    intro t
    simpa only [Finsupp.prod, one_pow, Finset.prod_const_one, mul_one,
      ← coeffAddEquiv_apply] using
      ZeroAtInftyContinuousMap.norm_coe_le_norm (coeffAddEquiv a) (.toTopology ⊥ t)

/-- Taking coefficients preserves the unit Gauss seminorm distance. -/
theorem isometry_coeffAddEquiv : Isometry (coeffAddEquiv (σ := σ) (E := E)) :=
  AddMonoidHomClass.isometry_of_norm coeffAddEquiv norm_coeffAddEquiv

/-- The unit Gauss seminorm is attained by a coefficient, including for the zero family. -/
theorem exists_norm_coeff_eq_norm (a : Gauss (fun _ : σ ↦ 1) E) :
    ∃ t, ‖a t‖ = ‖a‖ := by
  obtain ⟨t, ht⟩ := ZeroAtInftyContinuousMap.exists_norm_coe_eq_norm (coeffAddEquiv a)
  rcases t with ⟨t⟩
  exact ⟨t, by simpa only [coeffAddEquiv_apply, norm_coeffAddEquiv] using ht⟩

section Module

variable (R : Type*) [SeminormedRing R] [Module R E] [IsBoundedSMul R E]

/-- Taking coefficients identifies unit-radius restricted families with the discrete `c₀`
model, preserving the scalar action and the sup seminorm. -/
noncomputable def coeffLinearIsometryEquiv :
    Gauss (fun _ : σ ↦ 1) E ≃ₗᵢ[R]
      C₀(WithDiscreteTopology (σ →₀ ℕ), E) where
  toLinearEquiv :=
    { coeffAddEquiv with
      map_smul' := fun r a ↦ by
        ext t
        rcases t with ⟨t⟩
        simp [coeffAddEquiv_apply] }
  norm_map' := norm_coeffAddEquiv

/-- The coefficient comparison evaluates at each exponent by taking that coefficient. -/
@[simp]
theorem coeffLinearIsometryEquiv_apply (a : Gauss (fun _ : σ ↦ 1) E)
    (t : σ →₀ ℕ) :
    coeffLinearIsometryEquiv (σ := σ) (E := E) R a (.toTopology ⊥ t) = a t :=
  coeffAddEquiv_apply a t

/-- The inverse coefficient comparison has the prescribed coefficients. -/
@[simp]
theorem coeffLinearIsometryEquiv_symm_apply (f : C₀(WithDiscreteTopology (σ →₀ ℕ), E))
    (t : σ →₀ ℕ) :
    ((coeffLinearIsometryEquiv (σ := σ) (E := E) R).symm f) t = f (.toTopology ⊥ t) :=
  coeffAddEquiv_symm_apply f t

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
    simp [coeffLinearIsometryEquiv_apply, ofFinsupp_apply]
  · simp [coeffLinearIsometryEquiv_apply, ofFinsupp_apply,
      ZeroAtInftyContinuousMap.single_apply, h]

omit [DecidableEq (WithDiscreteTopology (σ →₀ ℕ))] in
/-- A unit-radius restricted family is the unconditional sum of its single coefficients. -/
theorem hasSum_ofFinsupp_single (a : Gauss (fun _ : σ ↦ 1) E) :
    HasSum (fun t ↦ ofFinsupp R (fun _ ↦ 1) (Finsupp.single t (a t))) a := by
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
theorem denseRange_ofFinsupp : DenseRange (ofFinsupp (σ := σ) (E := E) R (fun _ ↦ 1)) := by
  classical
  intro a
  exact mem_closure_of_tendsto (hasSum_ofFinsupp_single R a) <|
    .of_forall fun s ↦ ⟨∑ t ∈ s, Finsupp.single t (a t), by simp⟩

end Module

end Gauss
end IsRestrictedFamily
end TauCeti.MvPowerSeries
