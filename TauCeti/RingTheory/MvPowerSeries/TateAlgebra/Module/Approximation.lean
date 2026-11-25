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
In finitely many variables, truncation by total degree also converges. The monomials sum
unconditionally, and finite-support families are dense. For module coefficients truncation is
linear.
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

private theorem truncFinsetAddHom_apply_indicator (s : Finset (σ →₀ ℕ)) (a : Gauss c E)
    (t : σ →₀ ℕ) : truncFinsetAddHom s a t = Finsupp.indicator s (fun u _ ↦ a u) t := by
  simp only [truncFinsetAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

/-- Truncation preserves coefficients at exponents in the truncation set. -/
@[simp, grind =]
theorem truncFinsetAddHom_apply_of_mem {s : Finset (σ →₀ ℕ)} (a : Gauss c E) {t : σ →₀ ℕ}
    (ht : t ∈ s) : truncFinsetAddHom s a t = a t :=
  (truncFinsetAddHom_apply_indicator s a t).trans (Finsupp.indicator_of_mem ht _)

/-- Truncation vanishes at exponents outside the truncation set. -/
@[simp, grind =]
theorem truncFinsetAddHom_apply_of_notMem {s : Finset (σ →₀ ℕ)} (a : Gauss c E) {t : σ →₀ ℕ}
    (ht : t ∉ s) : truncFinsetAddHom s a t = 0 :=
  (truncFinsetAddHom_apply_indicator s a t).trans (Finsupp.indicator_of_notMem ht _)

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

/-- Truncation to `s` leaves `a` unchanged exactly when every coefficient outside `s` vanishes. -/
theorem truncFinsetAddHom_eq_self_iff (s : Finset (σ →₀ ℕ)) (a : Gauss c E) :
    truncFinsetAddHom s a = a ↔ ∀ t ∉ s, a t = 0 := by
  constructor
  · intro h t ht
    rw [← h]
    exact truncFinsetAddHom_apply_of_notMem a ht
  · intro h
    ext t
    by_cases ht : t ∈ s <;> simp [ht, h]

/-- Truncating to the empty set gives the zero additive map. -/
@[simp]
theorem truncFinsetAddHom_empty : truncFinsetAddHom (c := c) (E := E) ∅ = 0 := by
  ext a t
  exact truncFinsetAddHom_apply_of_notMem a (notMem_empty t)

/-- Truncation to a finite set is the sum of the singleton truncations over that set. -/
theorem truncFinsetAddHom_eq_sum_singleton (s : Finset (σ →₀ ℕ)) (a : Gauss c E) :
    truncFinsetAddHom s a = ∑ t ∈ s, truncFinsetAddHom {t} a := by
  ext u
  have h : (∑ t ∈ s, truncFinsetAddHom {t} a) u = ∑ t ∈ s, truncFinsetAddHom {t} a u := by
    simpa only [toAddSubgroupAddEquiv_apply, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
      using congrArg (fun f : IsRestrictedFamily.addSubgroup E c ↦ f.val u)
        (map_sum toAddSubgroupAddEquiv (fun t ↦ truncFinsetAddHom {t} a) s)
  rw [h, truncFinsetAddHom_apply_indicator, Finsupp.indicator_eq_sum_single,
    Finsupp.finsetSum_apply]
  simp only [truncFinsetAddHom_apply_indicator, Finsupp.indicator_singleton]

section Module

variable (R : Type*) [SeminormedRing R] [Module R E] [IsBoundedSMul R E]

private theorem truncFinsetAddHom_eq_ofFinsupp_indicator (s : Finset (σ →₀ ℕ)) (a : Gauss c E) :
    truncFinsetAddHom s a = ofFinsupp R c (Finsupp.indicator s fun t _ ↦ a t) := by
  ext t
  rw [truncFinsetAddHom_apply_indicator, ofFinsupp_apply]

/-- Finite-support truncation as a linear map on Gauss families. -/
def truncFinset (s : Finset (σ →₀ ℕ)) : Gauss c E →ₗ[R] Gauss c E where
  toAddHom := (truncFinsetAddHom s).toAddHom
  map_smul' r a := by
    -- The function of the linear map is the function of its underlying additive map.
    change truncFinsetAddHom s (r • a) = r • truncFinsetAddHom s a
    ext t
    by_cases ht : t ∈ s <;> simp [ht]

/-- The linear truncation acts by the underlying additive truncation. -/
@[simp]
theorem truncFinset_apply_eq_truncFinsetAddHom (s : Finset (σ →₀ ℕ)) (a : Gauss c E) :
    truncFinset R s a = truncFinsetAddHom s a := by
  unfold truncFinset
  rfl

private theorem truncFinsetAddHom_singleton_eq_ofFinsupp_single (t : σ →₀ ℕ) (a : Gauss c E) :
    truncFinsetAddHom {t} a = ofFinsupp R c (Finsupp.single t (a t)) := by
  rw [truncFinsetAddHom_eq_ofFinsupp_indicator R, Finsupp.indicator_singleton]

/-- A finite-support truncation is the sum of the retained single-coefficient families. -/
theorem truncFinset_eq_sum_ofFinsupp_single (s : Finset (σ →₀ ℕ)) (a : Gauss c E) :
    truncFinset R s a = ∑ t ∈ s, ofFinsupp R c (Finsupp.single t (a t)) := by
  rw [truncFinset_apply_eq_truncFinsetAddHom, truncFinsetAddHom_eq_sum_singleton]
  simp only [truncFinsetAddHom_singleton_eq_ofFinsupp_single R]

/-- Truncating to the empty set gives the zero linear map. -/
@[simp]
theorem truncFinset_empty : truncFinset (c := c) (E := E) R ∅ = 0 := by
  ext a
  simp

/-- Truncation leaves a single-coefficient family unchanged if its exponent is retained. -/
theorem truncFinset_ofFinsupp_single_of_mem {s : Finset (σ →₀ ℕ)} {t : σ →₀ ℕ} (ht : t ∈ s)
    (e : E) :
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

end Module

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
      (isRestrictedFamily_iff.mp (mem_addSubgroup.mp a.toAddSubgroup.property)).eventually
        (gt_mem_nhds (half_pos hε))
  refine (eventually_ge_atTop hF.toFinset).mono fun s hs ↦ ?_
  rw [dist_comm, dist_eq_norm]
  refine (norm_sub_truncFinsetAddHom_le a s (half_pos hε).le fun t ht ↦ ?_).trans_lt
    (half_lt_self hε)
  exact (not_le.mp fun h ↦ ht (hs (hF.mem_toFinset.mpr h))).le

/-- With finitely many variables, keeping only exponents of total degree less than `n`
approximates every restricted family in Gauss seminorm. -/
theorem tendsto_truncFinsetAddHom_degree_lt_atTop [Finite σ] (a : Gauss c E) :
    Tendsto (fun n : ℕ ↦ truncFinsetAddHom (Finsupp.finite_of_degree_lt n).toFinset a)
      atTop (𝓝 a) := by
  refine (tendsto_truncFinsetAddHom_atTop a).comp
    (tendsto_atTop_finset_of_monotone (fun m n hmn t ht ↦ ?_) fun t ↦ ⟨t.degree + 1, ?_⟩)
  · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at ht ⊢
    exact ht.trans_le hmn
  · simp

/-- A restricted family is the unconditional sum of its singleton truncations. -/
theorem hasSum_truncFinsetAddHom_singleton (a : Gauss c E) :
    HasSum (fun t ↦ truncFinsetAddHom {t} a) a := by
  rw [HasSum, SummationFilter.unconditional_filter]
  exact (tendsto_truncFinsetAddHom_atTop a).congr (truncFinsetAddHom_eq_sum_singleton · a)

/-- The families fixed by some finite-support truncation are dense. -/
theorem dense_setOf_exists_truncFinsetAddHom_eq_self :
    Dense {a : Gauss c E | ∃ s, truncFinsetAddHom s a = a} := by
  classical
  intro a
  apply mem_closure_of_tendsto (tendsto_truncFinsetAddHom_atTop a)
  exact .of_forall fun s ↦ ⟨s, by simp⟩

variable (R : Type*) [SeminormedRing R] [Module R E] [IsBoundedSMul R E]

/-- A restricted family is the unconditional sum of its single coefficients at any positive
polyradius. No completeness assumption on the coefficient module is needed. -/
theorem hasSum_ofFinsupp_single (a : Gauss c E) :
    HasSum (fun t ↦ ofFinsupp R c (Finsupp.single t (a t))) a :=
  (hasSum_truncFinsetAddHom_singleton a).congr_fun fun t ↦
    (truncFinsetAddHom_singleton_eq_ofFinsupp_single R t a).symm

/-- Finite-support families are dense for the Gauss seminorm at every positive polyradius. -/
theorem denseRange_ofFinsupp : DenseRange (ofFinsupp (σ := σ) (E := E) R c) := by
  refine dense_setOf_exists_truncFinsetAddHom_eq_self.mono ?_
  rintro a ⟨s, hs⟩
  exact ⟨Finsupp.indicator s (fun t _ ↦ a t),
    (truncFinsetAddHom_eq_ofFinsupp_indicator R s a).symm.trans hs⟩

end Norm

end TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss
