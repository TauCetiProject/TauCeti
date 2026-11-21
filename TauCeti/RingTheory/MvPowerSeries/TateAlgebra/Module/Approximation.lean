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

Finite-support truncations are additive projections, contractive for the weighted Gauss
seminorm, and converge to a restricted coefficient family at every positive real polyradius.
In finitely many variables, truncation by total degree also converges. For module coefficients
truncation is linear, the monomials sum unconditionally, and finite-support families are dense.
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

variable {σ E : Type*} [SeminormedAddCommGroup E] {c : σ → ℝ}

/-- Keep the coefficients in a finite set of exponents and set all other coefficients to zero. -/
def truncFinsetAddHom (s : Finset (σ →₀ ℕ)) : Gauss c E →+ Gauss c E where
  toFun a :=
    let b := Finsupp.indicator s (fun t _ ↦ a t)
    ofAddSubgroup ⟨b,
      mem_addSubgroup.mpr (isRestrictedFamily_of_finite_support c b.hasFiniteSupport)⟩
  map_zero' := by
    classical
    ext t
    simp [Finsupp.indicator_apply]
  map_add' a b := by
    classical
    ext t
    simp only [Finsupp.indicator_apply, add_apply]
    split_ifs <;> simp

/-- Truncation preserves coefficients at exponents in the truncation set. -/
@[simp, grind =]
theorem truncFinsetAddHom_apply_of_mem {s : Finset (σ →₀ ℕ)} (a : Gauss c E) {t : σ →₀ ℕ}
    (ht : t ∈ s) : truncFinsetAddHom s a t = a t :=
  Finsupp.indicator_of_mem ht _

/-- Truncation vanishes at exponents outside the truncation set. -/
@[simp, grind =]
theorem truncFinsetAddHom_apply_of_notMem {s : Finset (σ →₀ ℕ)} (a : Gauss c E) {t : σ →₀ ℕ}
    (ht : t ∉ s) : truncFinsetAddHom s a t = 0 :=
  Finsupp.indicator_of_notMem ht _

/-- The coefficient formula for finite-support truncation. -/
theorem truncFinsetAddHom_apply (s : Finset (σ →₀ ℕ)) (a : Gauss c E) (t : σ →₀ ℕ)
    [Decidable (t ∈ s)] : truncFinsetAddHom s a t = if t ∈ s then a t else 0 := by
  by_cases ht : t ∈ s <;> simp [ht]

/-- Successive truncations keep exactly the intersection of the two sets of exponents. -/
@[simp]
theorem truncFinsetAddHom_truncFinsetAddHom [DecidableEq (σ →₀ ℕ)]
    (s t : Finset (σ →₀ ℕ)) (a : Gauss c E) :
    truncFinsetAddHom s (truncFinsetAddHom t a) = truncFinsetAddHom (s ∩ t) a := by
  ext u
  by_cases hs : u ∈ s <;> by_cases ht : u ∈ t <;> simp [hs, ht]

/-- A truncation is unchanged exactly when all the omitted coefficients vanish. -/
theorem truncFinsetAddHom_eq_self_iff (s : Finset (σ →₀ ℕ)) (a : Gauss c E) :
    truncFinsetAddHom s a = a ↔ ∀ t ∉ s, a t = 0 := by
  constructor
  · intro h t ht
    rw [← h]
    exact truncFinsetAddHom_apply_of_notMem a ht
  · intro h
    ext t
    by_cases ht : t ∈ s <;> simp [ht, h]

/-- Truncating to a larger set first does not change the final truncation. -/
theorem truncFinsetAddHom_truncFinsetAddHom_of_subset {s t : Finset (σ →₀ ℕ)} (h : s ⊆ t)
    (a : Gauss c E) : truncFinsetAddHom s (truncFinsetAddHom t a) = truncFinsetAddHom s a := by
  classical
  rw [truncFinsetAddHom_truncFinsetAddHom, inter_eq_left.mpr h]

/-- Truncating twice to the same set is the same as truncating once. -/
@[simp]
theorem truncFinsetAddHom_idem (s : Finset (σ →₀ ℕ)) (a : Gauss c E) :
    truncFinsetAddHom s (truncFinsetAddHom s a) = truncFinsetAddHom s a :=
  truncFinsetAddHom_truncFinsetAddHom_of_subset Subset.rfl a

/-- Truncating to the empty set gives the zero additive map. -/
@[simp]
theorem truncFinsetAddHom_empty : truncFinsetAddHom (c := c) (E := E) ∅ = 0 := by
  ext a t
  exact truncFinsetAddHom_apply_of_notMem a (notMem_empty t)

section Norm

variable [∀ i, Fact (0 < c i)]

/-- Truncation is contractive for the weighted Gauss seminorm. -/
theorem norm_truncFinsetAddHom_le (s : Finset (σ →₀ ℕ)) (a : Gauss c E) :
    ‖truncFinsetAddHom s a‖ ≤ ‖a‖ := by
  classical
  apply norm_le_iff.mpr
  intro t
  by_cases ht : t ∈ s
  · simpa [ht] using norm_coeff_mul_prod_le a t
  · simp [ht, norm_nonneg a]

/-- Finite-support truncation is uniformly continuous for the Gauss topology. -/
theorem uniformContinuous_truncFinsetAddHom (s : Finset (σ →₀ ℕ)) :
    UniformContinuous (truncFinsetAddHom (c := c) (E := E) s) :=
  AddMonoidHomClass.uniformContinuous_of_bound (truncFinsetAddHom s) 1
    (fun a ↦ by simpa using norm_truncFinsetAddHom_le s a)

/-- A bound on the weighted coefficients omitted by a truncation bounds its error. -/
theorem norm_sub_truncFinsetAddHom_le (a : Gauss c E) (s : Finset (σ →₀ ℕ))
    {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ t ∉ s, ‖a t‖ * t.prod (c · ^ ·) ≤ ε) :
    ‖a - truncFinsetAddHom s a‖ ≤ ε := by
  classical
  apply norm_le_iff.mpr
  intro t
  by_cases ht : t ∈ s
  · simp [ht, hε]
  · simpa [ht] using h t ht

/-- Finite-support truncations converge in the weighted Gauss topology. -/
theorem tendsto_truncFinsetAddHom_atTop (a : Gauss c E) :
    Tendsto (fun s : Finset (σ →₀ ℕ) ↦ truncFinsetAddHom s a) atTop (𝓝 a) := by
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  have hF : {t | ε / 2 ≤ ‖a t‖ * t.prod (c · ^ ·)}.Finite := by
    simpa [Filter.eventually_cofinite, not_lt] using
      (isRestrictedFamily_iff.mp (mem_addSubgroup.mp a.toAddSubgroup.2)).eventually
        (gt_mem_nhds (half_pos hε))
  refine (eventually_ge_atTop hF.toFinset).mono fun s hs ↦ ?_
  rw [dist_comm, dist_eq_norm]
  refine (norm_sub_truncFinsetAddHom_le a s (half_pos hε).le fun t ht ↦ ?_).trans_lt
    (half_lt_self hε)
  exact (not_le.mp fun h ↦ ht (hs (hF.mem_toFinset.mpr h))).le

/-- With finitely many variables, keeping only exponents of total degree less than `n`
approximates every restricted family in Gauss seminorm. -/
theorem tendsto_truncFinsetAddHom_finite_of_degree_lt_atTop [Finite σ] (a : Gauss c E) :
    Tendsto (fun n : ℕ ↦ truncFinsetAddHom (Finsupp.finite_of_degree_lt n).toFinset a)
      atTop (𝓝 a) := by
  refine (tendsto_truncFinsetAddHom_atTop a).comp
    (tendsto_atTop_finset_of_monotone (fun m n hmn t ht ↦ ?_) fun t ↦ ⟨t.degree + 1, ?_⟩)
  · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at ht ⊢
    exact ht.trans_le hmn
  · simp

end Norm

section Module

variable (R : Type*) [SeminormedRing R] [Module R E] [IsBoundedSMul R E]

/-- Finite-support truncation as a linear map on Gauss families. -/
def truncFinset (s : Finset (σ →₀ ℕ)) : Gauss c E →ₗ[R] Gauss c E :=
  (ofFinsupp R c).comp (∑ t ∈ s, (Finsupp.lsingle t).comp
    ((IsRestrictedFamily.coeff R t).comp (toAddSubgroupLinearEquiv R).toLinearMap))

/-- A finite-support truncation is the sum of the retained single-coefficient families. -/
theorem truncFinset_eq_sum_ofFinsupp_single (s : Finset (σ →₀ ℕ)) (a : Gauss c E) :
    truncFinset R s a = ∑ t ∈ s, ofFinsupp R c (Finsupp.single t (a t)) := by
  simp [truncFinset]

/-- The linear and additive finite-support truncations agree. -/
@[simp]
theorem truncFinset_apply_eq_truncFinsetAddHom (s : Finset (σ →₀ ℕ)) (a : Gauss c E) :
    truncFinset R s a = truncFinsetAddHom s a := by
  rw [truncFinset_eq_sum_ofFinsupp_single, ← map_sum, ← Finsupp.indicator_eq_sum_single]
  ext t
  exact ofFinsupp_apply R _ t

/-- Truncating to the empty set gives the zero linear map. -/
@[simp]
theorem truncFinset_empty : truncFinset (c := c) (E := E) R ∅ = 0 := by
  simp [truncFinset]

/-- Truncating to a singleton leaves just the coefficient at that exponent. -/
theorem truncFinset_singleton (t : σ →₀ ℕ) (a : Gauss c E) :
    truncFinset R {t} a = ofFinsupp R c (Finsupp.single t (a t)) := by
  rw [truncFinset_eq_sum_ofFinsupp_single, sum_singleton]

/-- Truncation leaves a single-coefficient family unchanged if its exponent is retained. -/
theorem truncFinset_ofFinsupp_single {s : Finset (σ →₀ ℕ)} {t : σ →₀ ℕ} (ht : t ∈ s) (e : E) :
    truncFinset R s (ofFinsupp R c (Finsupp.single t e)) = ofFinsupp R c (Finsupp.single t e) := by
  rw [truncFinset_apply_eq_truncFinsetAddHom, truncFinsetAddHom_eq_self_iff]
  intro u hu
  exact (ofFinsupp_apply R _ _).trans (Finsupp.single_eq_of_ne fun h ↦ hu (h ▸ ht))

variable {R} in
/-- Bounded coefficient-module maps commute with finite-support truncations. -/
theorem mapLinearMap_truncFinset {F : Type*} [SeminormedAddCommGroup F]
    [Module R F] [IsBoundedSMul R F] (φ : E →ₗ[R] F) {C : ℝ}
    (hφ : ∀ e, ‖φ e‖ ≤ C * ‖e‖) (s : Finset (σ →₀ ℕ)) (a : Gauss c E) :
    mapLinearMap φ hφ (truncFinset R s a) = truncFinset R s (mapLinearMap φ hφ a) := by
  ext t
  by_cases ht : t ∈ s <;> simp [ht]

variable [∀ i, Fact (0 < c i)]

/-- A restricted family is the unconditional sum of its single coefficients at any positive
polyradius. No completeness assumption on the coefficient module is needed. -/
theorem hasSum_ofFinsupp_single (a : Gauss c E) :
    HasSum (fun t ↦ ofFinsupp R c (Finsupp.single t (a t))) a :=
  (tendsto_truncFinsetAddHom_atTop a).congr fun s ↦
    (truncFinset_apply_eq_truncFinsetAddHom R s a).symm.trans
      (truncFinset_eq_sum_ofFinsupp_single R s a)

/-- Finite-support families are dense for the Gauss seminorm at every positive polyradius. -/
theorem denseRange_ofFinsupp : DenseRange (ofFinsupp (σ := σ) (E := E) R c) := by
  classical
  intro a
  exact mem_closure_of_tendsto (hasSum_ofFinsupp_single R a) <|
    .of_forall fun s ↦ ⟨∑ t ∈ s, Finsupp.single t (a t), by simp⟩

end Module

end TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss
