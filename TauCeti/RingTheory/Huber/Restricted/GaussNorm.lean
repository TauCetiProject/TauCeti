/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

/-!
# The Gauss norm topology on restricted multivariate series

The trivial-weight Huber restricted-series ring and Mathlib's unit-radius restricted-series
subring have the same underlying power series. Their topologies also agree: the Huber topology
requires every coefficient to lie in a prescribed open additive subgroup, while the Gauss norm
measures the supremum of all coefficient norms.

The comparison below is an algebra equivalence continuous in both directions. Over a complete
base it identifies the completed Huber Tate algebra with the Banach algebra of restricted series.
This allows normed-ring results, including Weierstrass division, to be transported to the completed
topological algebra without changing its topology.

The normed series are Mathlib's `MvPowerSeries.IsRestricted.subring`, with the Gauss norm
constructed using William Coram's `MvPowerSeries.gaussNorm` infrastructure; no second series
type or norm is introduced here.

## Main results

* `TauCeti.Huber.restrictedMvPowerSeriesGaussEquiv`: the identity ring equivalence between
  Huber restricted series and Gauss-normed restricted series, continuous in both directions.
* `TauCeti.Huber.restrictedMvPowerSeriesCompletionGaussEquiv`: the resulting topological
  ring comparison for the Huber completion over a complete coefficient ring.
* `TauCeti.Huber.restrictedMvPowerSeriesGaussAlgEquiv` and
  `TauCeti.Huber.restrictedMvPowerSeriesCompletionGaussAlgEquiv`: the same comparisons as
  coefficient-algebra equivalences.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1 and §5.2.1.
* T. Wedhorn, *Adic Spaces*, §5.6, for the restricted-series topology.
-/

public section

namespace TauCeti.Huber

open Filter
open scoped Topology

section Predicate

variable {n : ℕ} {R : Type*} [NormedRing R]

/-- The topological restrictedness condition is Mathlib's normed restrictedness condition at
unit polyradius. -/
theorem isRestricted_iff_isRestricted_one {f : MvPowerSeries (Fin n) R} :
    IsRestricted f ↔ MvPowerSeries.IsRestricted (fun _ ↦ 1) f := by
  rw [isRestricted_iff_coeff, MvPowerSeries.IsRestricted]
  simp only [one_pow, Finsupp.prod, Finset.prod_const_one, mul_one]
  exact tendsto_zero_iff_norm_tendsto_zero

end Predicate

variable {n : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NonarchimedeanRing R]

/-- The trivial-weight Huber subring is Mathlib's subring of unit-radius restricted series.
This is an equality of subrings; their topological structures are compared separately below. -/
theorem weightedRestrictedSubring_eq_isRestricted_subring :
    weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight =
      MvPowerSeries.IsRestricted.subring (R := R) (fun _ ↦ 1) := by
  rw [weightedRestrictedSubring_one_weight]
  ext f
  rw [mem_restrictedMvPowerSeriesSubring]
  exact isRestricted_iff_isRestricted_one (f := f)

/-- The identity on underlying series identifies the trivial-weight Huber ring with the
Gauss-normed unit-radius restricted-series ring. -/
noncomputable def restrictedMvPowerSeriesGaussEquiv :
    weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight ≃+*
      MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin n ↦ 1) :=
  RingEquiv.subringCongr weightedRestrictedSubring_eq_isRestricted_subring

/-- The Gauss comparison preserves the underlying formal power series. -/
@[simp]
theorem coe_restrictedMvPowerSeriesGaussEquiv
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R))
      isWeightFamily_one_weight) :
    (restrictedMvPowerSeriesGaussEquiv f : MvPowerSeries (Fin n) R) = f :=
  RingEquiv.coe_subringCongr_apply weightedRestrictedSubring_eq_isRestricted_subring f

/-- The inverse Gauss comparison also preserves the underlying formal power series. -/
@[simp]
theorem coe_restrictedMvPowerSeriesGaussEquiv_symm
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin n ↦ 1)) :
    (restrictedMvPowerSeriesGaussEquiv.symm f : MvPowerSeries (Fin n) R) = f :=
  RingEquiv.coe_subringCongr_apply weightedRestrictedSubring_eq_isRestricted_subring.symm f

/-- The identity Gauss comparison also respects the coefficient-algebra structure. -/
noncomputable def restrictedMvPowerSeriesGaussAlgEquiv :
    weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight ≃ₐ[R]
      MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin n ↦ 1) :=
  AlgEquiv.ofRingEquiv (f := restrictedMvPowerSeriesGaussEquiv) fun r ↦
    Subtype.ext (by simp only [coe_restrictedMvPowerSeriesGaussEquiv,
      algebraMap_weightedRestrictedSubring, coe_weightedC,
      MvPowerSeries.coe_algebraMap_isRestrictedSubring])

/-- The algebra Gauss comparison has the same underlying map as the ring comparison. -/
@[simp]
theorem coe_restrictedMvPowerSeriesGaussAlgEquiv :
    ⇑(restrictedMvPowerSeriesGaussAlgEquiv (n := n) (R := R)) =
      ⇑(restrictedMvPowerSeriesGaussEquiv (n := n) (R := R)) := (rfl)

/-- The inverse algebra Gauss comparison has the same map as the inverse ring comparison. -/
@[simp]
theorem coe_restrictedMvPowerSeriesGaussAlgEquiv_symm :
    ⇑(restrictedMvPowerSeriesGaussAlgEquiv (n := n) (R := R)).symm =
      ⇑(restrictedMvPowerSeriesGaussEquiv (n := n) (R := R)).symm := (rfl)

/-- The Huber restricted-series topology makes the comparison to the Gauss topology continuous.
All coefficients in a sufficiently small open subgroup give a uniformly small Gauss norm. -/
theorem continuous_restrictedMvPowerSeriesGaussEquiv :
    Continuous (restrictedMvPowerSeriesGaussEquiv (n := n) (R := R)) := by
  refine continuous_of_continuousAt_zero restrictedMvPowerSeriesGaussEquiv ?_
  rw [ContinuousAt, map_zero, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  let U := IsUltrametricDist.ball_openAddSubgroup R (half_pos hε)
  filter_upwards [(hasBasis_nhds_zero_weightedTopology
    (k := n) (A := R) isWeightFamily_one_weight).mem_of_mem (i := U) trivial] with f hf
  refine lt_of_le_of_lt ((MvPowerSeries.norm_le_iff (half_pos hε).le).mpr ?_)
    (half_lt_self hε)
  intro ν
  have h := mem_weightedNhd.mp hf ν
  rw [weightMul_one_weight] at h
  simpa only [coe_restrictedMvPowerSeriesGaussEquiv, one_pow, Finsupp.prod,
    Finset.prod_const_one, mul_one, dist_zero_right] using (Metric.mem_ball.mp h).le

/-- The inverse comparison is continuous for the Gauss topology. A small Gauss norm places
every coefficient in any prescribed open additive subgroup of the coefficient ring. -/
theorem continuous_restrictedMvPowerSeriesGaussEquiv_symm :
    Continuous (restrictedMvPowerSeriesGaussEquiv (n := n) (R := R)).symm := by
  refine continuous_of_continuousAt_zero restrictedMvPowerSeriesGaussEquiv.symm ?_
  rw [ContinuousAt, map_zero, (hasBasis_nhds_zero_weightedTopology
    (k := n) (A := R) isWeightFamily_one_weight).tendsto_right_iff]
  intro U _
  obtain ⟨ε, hε, hU⟩ := NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp
    (U.isOpen.mem_nhds U.zero_mem)
  filter_upwards [NormedAddGroup.nhds_zero_basis_norm_lt.mem_of_mem hε] with f hf
  rw [SetLike.mem_coe, mem_weightedNhd]
  intro ν
  rw [weightMul_one_weight, coe_restrictedMvPowerSeriesGaussEquiv_symm]
  apply hU
  simpa only [one_pow, Finsupp.prod, Finset.prod_const_one, mul_one, Set.mem_ofPred_eq] using
    (MvPowerSeries.norm_coeff_mul_prod_le f ν).trans_lt hf

section Complete

variable [CompleteSpace R]

/-- Over a complete nonarchimedean normed ring, the completed Huber Tate algebra is the
Gauss-normed ring of unit-radius restricted series. The equivalence is continuous in both
directions by the theorems below. -/
noncomputable def restrictedMvPowerSeriesCompletionGaussEquiv :
    restrictedMvPowerSeriesCompletion n R ≃+*
      MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin n ↦ 1) :=
  (restrictedMvPowerSeriesCompletionEquiv n R).trans restrictedMvPowerSeriesGaussEquiv

/-- Over a complete coefficient ring, the completed Gauss comparison is an algebra equivalence.
It composes the completion's coefficient-algebra comparison with the identity on series. -/
noncomputable def restrictedMvPowerSeriesCompletionGaussAlgEquiv :
    restrictedMvPowerSeriesCompletion n R ≃ₐ[R]
      MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin n ↦ 1) :=
  (restrictedMvPowerSeriesCompletionAlgEquiv n R).trans restrictedMvPowerSeriesGaussAlgEquiv

/-- The completed algebra Gauss comparison has the same map as the completed ring comparison. -/
@[simp]
theorem coe_restrictedMvPowerSeriesCompletionGaussAlgEquiv :
    ⇑(restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := n) (R := R)) =
      ⇑(restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := R)) := by
  simp [restrictedMvPowerSeriesCompletionGaussAlgEquiv,
    restrictedMvPowerSeriesCompletionGaussEquiv, AlgEquiv.coe_trans, RingEquiv.coe_trans]

/-- The inverse completed algebra Gauss comparison agrees with the inverse ring comparison. -/
@[simp]
theorem coe_restrictedMvPowerSeriesCompletionGaussAlgEquiv_symm :
    ⇑(restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := n) (R := R)).symm =
      ⇑(restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := R)).symm := by
  funext f
  simp [restrictedMvPowerSeriesCompletionGaussAlgEquiv,
    restrictedMvPowerSeriesCompletionGaussEquiv]

/-- On a series in the dense subring, the completed comparison is the identity on formal
power series, regarded as a unit-radius restricted series. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionGaussEquiv_coe
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set R))
      isWeightFamily_one_weight) :
    restrictedMvPowerSeriesCompletionGaussEquiv
        (f : restrictedMvPowerSeriesCompletion n R) = restrictedMvPowerSeriesGaussEquiv f := by
  simp [restrictedMvPowerSeriesCompletionGaussEquiv]

/-- The inverse completed comparison takes a Gauss-normed restricted series to its canonical
image in the Huber completion. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionGaussEquiv_symm_apply
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin n ↦ 1)) :
    restrictedMvPowerSeriesCompletionGaussEquiv.symm f =
      (restrictedMvPowerSeriesGaussEquiv.symm f : restrictedMvPowerSeriesCompletion n R) := by
  simp [restrictedMvPowerSeriesCompletionGaussEquiv]

/-- The completed comparison is continuous from the canonical completion topology to the
Gauss norm topology. -/
theorem continuous_restrictedMvPowerSeriesCompletionGaussEquiv :
    Continuous (restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := R)) :=
  continuous_restrictedMvPowerSeriesGaussEquiv.comp
    uniformContinuous_restrictedMvPowerSeriesCompletionEquiv.continuous

/-- The inverse completed comparison is continuous from the Gauss norm topology to the
canonical completion topology. -/
theorem continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm :
    Continuous (restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := R)).symm :=
  uniformContinuous_restrictedMvPowerSeriesCompletionEquiv_symm.continuous.comp
    continuous_restrictedMvPowerSeriesGaussEquiv_symm

end Complete

end TauCeti.Huber
