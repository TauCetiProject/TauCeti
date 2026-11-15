/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Norm
import Mathlib.Data.Finsupp.Indicator

/-!
# Polynomial approximation of module-valued restricted series

Finite-support truncations are contractive projections for the weighted Gauss seminorm,
and converge to a restricted coefficient family at every positive real polyradius. Thus
module-valued restricted series are unconditional sums of their monomials, and finite-support
families are dense. In finitely many variables, truncation by total degree also converges.
These statements do not require complete or ultrametric coefficient spaces, nor scalars
whose norms realise the radii. Truncation commutes with bounded coefficient-module maps.
This extends the scalar approximation of
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Polynomial` to module coefficients.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

noncomputable section

namespace TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss

open Filter Finset
open scoped Topology

variable {σ E F : Type*} [SeminormedAddCommGroup E] {c : σ → ℝ}
variable (R : Type*) [SeminormedRing R] [Module R E] [IsBoundedSMul R E]

/-- Keep the coefficients in a finite set of exponents and set all other coefficients to zero. -/
def truncFinset (s : Finset (σ →₀ ℕ)) : Gauss c E →ₗ[R] Gauss c E where
  toFun a := ofFinsupp R c (Finsupp.indicator s fun t _ ↦ a t)
  map_add' a b := by
    classical
    ext t
    simp only [ofFinsupp_apply, Finsupp.indicator_apply, add_apply]
    split_ifs <;> simp
  map_smul' r a := by
    classical
    ext t
    simp only [ofFinsupp_apply, Finsupp.indicator_apply, smul_apply]
    split_ifs <;> simp

/-- The coefficient formula for finite-support truncation. -/
@[simp]
theorem truncFinset_apply (s : Finset (σ →₀ ℕ)) (a : Gauss c E) (t : σ →₀ ℕ)
    [Decidable (t ∈ s)] : truncFinset R s a t = if t ∈ s then a t else 0 := by
  classical
  simp [truncFinset, ofFinsupp_apply]

/-- Successive truncations keep exactly the intersection of the two sets of exponents. -/
@[simp]
theorem truncFinset_truncFinset [DecidableEq (σ →₀ ℕ)] (s t : Finset (σ →₀ ℕ)) (a : Gauss c E) :
    truncFinset R s (truncFinset R t a) = truncFinset R (s ∩ t) a := by
  classical
  ext u
  simp only [truncFinset_apply, mem_inter]
  split_ifs <;> simp_all

variable {R} in
/-- Bounded coefficient-module maps commute with finite-support truncations. -/
theorem _root_.LinearMap.mapGaussFamily_truncFinset [SeminormedAddCommGroup F]
    [Module R F] [IsBoundedSMul R F] (φ : E →ₗ[R] F) {C : ℝ}
    (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖) (s : Finset (σ →₀ ℕ)) (a : Gauss c E) :
    mapLinearMap φ hφ (truncFinset R s a) = truncFinset R s (mapLinearMap φ hφ a) := by
  classical
  ext t
  simp only [mapLinearMap_apply, truncFinset_apply]
  split_ifs <;> simp

variable [∀ i, Fact (0 < c i)]

/-- Truncation is contractive for the weighted Gauss seminorm. -/
theorem norm_truncFinset_le (s : Finset (σ →₀ ℕ)) (a : Gauss c E) :
    ‖truncFinset R s a‖ ≤ ‖a‖ := by
  classical
  apply norm_le_iff.mpr
  intro t
  by_cases ht : t ∈ s
  · simpa [ht] using norm_coeff_mul_prod_le a t
  · simp [ht, norm_nonneg a]

/-- Finite-support truncation is uniformly continuous for the Gauss topology. -/
theorem uniformContinuous_truncFinset (s : Finset (σ →₀ ℕ)) :
    UniformContinuous (truncFinset (c := c) (E := E) R s) :=
  AddMonoidHomClass.uniformContinuous_of_bound (truncFinset R s) 1
    (fun a ↦ by simpa using norm_truncFinset_le R s a)

/-- A bound on the weighted coefficients omitted by a truncation bounds its error. -/
theorem norm_sub_truncFinset_le (a : Gauss c E) (s : Finset (σ →₀ ℕ))
    {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ t ∉ s, ‖a t‖ * t.prod (c · ^ ·) ≤ ε) :
    ‖a - truncFinset R s a‖ ≤ ε := by
  classical
  apply norm_le_iff.mpr
  intro t
  by_cases ht : t ∈ s
  · simp [ht, hε]
  · simpa [ht] using h t ht

/-- Finite-support truncations converge in the weighted Gauss topology. -/
theorem tendsto_truncFinset_atTop (a : Gauss c E) :
    Tendsto (fun s : Finset (σ →₀ ℕ) ↦ truncFinset R s a) atTop (𝓝 a) := by
  classical
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  have hF : {t | ε / 2 ≤ ‖a t‖ * t.prod (c · ^ ·)}.Finite := by
    simpa [Filter.eventually_cofinite, not_lt] using
      (isRestrictedFamily_iff.mp (mem_addSubgroup.mp a.toAddSubgroup.2)).eventually
        (gt_mem_nhds (half_pos hε))
  refine (eventually_ge_atTop hF.toFinset).mono fun s hs ↦ ?_
  rw [dist_comm, dist_eq_norm]
  refine (norm_sub_truncFinset_le R a s (half_pos hε).le fun t ht ↦ ?_).trans_lt
    (half_lt_self hε)
  exact (not_le.mp fun h ↦ ht (hs (hF.mem_toFinset.mpr h))).le

/-- A restricted family is the unconditional sum of its single coefficients at any positive
polyradius. No completeness assumption on the coefficient module is needed. -/
theorem hasSum_ofFinsupp_single (a : Gauss c E) :
    HasSum (fun t ↦ ofFinsupp R c (Finsupp.single t (a t))) a := by
  classical
  have heq (s : Finset (σ →₀ ℕ)) :
      ∑ t ∈ s, ofFinsupp R c (Finsupp.single t (a t)) = truncFinset R s a := by
    rw [← map_sum]
    exact congrArg (ofFinsupp R c) (by
      ext t
      simp [Finsupp.indicator_apply, Finsupp.single_apply, eq_comm])
  exact (tendsto_truncFinset_atTop R a).congr (fun s ↦ (heq s).symm)

/-- Finite-support families are dense for the Gauss seminorm at every positive polyradius. -/
theorem denseRange_ofFinsupp : DenseRange (ofFinsupp (σ := σ) (E := E) R c) := by
  classical
  intro a
  exact mem_closure_of_tendsto (hasSum_ofFinsupp_single R a) <|
    .of_forall fun s ↦ ⟨∑ t ∈ s, Finsupp.single t (a t), by simp⟩

/-- With finitely many variables, keeping only exponents of total degree less than `n`
approximates every module-valued restricted series in Gauss seminorm. -/
theorem tendsto_truncFinset_totalDegree_atTop [Finite σ] (a : Gauss c E) :
    Tendsto (fun n : ℕ ↦ truncFinset R (Finsupp.finite_of_degree_lt n).toFinset a)
      atTop (𝓝 a) := by
  refine (tendsto_truncFinset_atTop R a).comp
    (tendsto_atTop_finset_of_monotone (fun m n hmn t ht ↦ ?_) fun t ↦ ⟨t.degree + 1, ?_⟩)
  · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at ht ⊢
    exact ht.trans_le hmn
  · simp

end TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss
