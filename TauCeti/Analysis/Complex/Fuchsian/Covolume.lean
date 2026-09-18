/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.ProperAction
public import TauCeti.Analysis.Complex.UpperHalfPlane.Measure
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.Analysis.Complex.UpperHalfPlane.Stabilizer
public import TauCeti.MeasureTheory.Group.FundamentalDomain
public import TauCeti.MeasureTheory.Group.ProperlyDiscontinuous
public import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Fundamental domains, covolume, and cofinite Fuchsian groups

Let `Γ ≤ PSL(2, ℝ)` be a discrete subgroup, acting on the upper half-plane `ℍ` with Mathlib's
invariant measure `volume` (density `y⁻² dx dy`). This file shows that `Γ` has a measurable
fundamental domain, so that the covolume `MeasureTheory.covolume Γ ℍ` — the hyperbolic area of
the quotient `Γ \ ℍ` — is the area of any measurable fundamental domain
(`MeasureTheory.IsFundamentalDomain.covolume_eq_volume`), and defines the cofinite Fuchsian
groups as the discrete subgroups of finite covolume.

The fundamental domain comes from the general construction
`TauCeti.exists_isFundamentalDomain_of_properlyDiscontinuousSMul`. Its hypothesis, that the
points with nontrivial stabilizer are null, holds because a nontrivial element of `PSL(2, ℝ)`
fixes at most one point of `ℍ` and a discrete subgroup is countable, so these points form a
countable set.

## Main declarations

* `Subgroup.instCountableOfDiscreteTopology`: a discrete subgroup of `PSL(2, ℝ)` is countable.
* `Subgroup.countable_compl_freeLocus`: the points of `ℍ` with nontrivial stabilizer in a
  countable `Γ` form a countable set.
* `Subgroup.exists_isFundamentalDomain`: a discrete `Γ` has a measurable fundamental domain
  whose translates are pairwise disjoint.
* `Subgroup.covolume_pos`: the covolume of a discrete subgroup is positive.
* `Subgroup.covolume_conjAct_smul`: the covolume is invariant under conjugation.
* `Subgroup.covolume_eq_card_mul_covolume`: for `Δ ≤ Γ`, the covolume of `Δ` is `[Γ : Δ]` times
  that of `Γ`, with the index counted in `ℕ∞`.
* `Subgroup.IsCofinite`: a discrete subgroup of finite covolume.
* `Subgroup.IsCofinite.volume_ne_top`, `Subgroup.IsCofinite.of_isFundamentalDomain`: a discrete
  subgroup is cofinite exactly when one, equivalently every, fundamental domain has finite area.
* `Subgroup.isCofinite_iff_of_le`: a subgroup of a discrete group is cofinite exactly when the
  larger group is cofinite and the index is finite.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §§3.1 and 4.1.
* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §§9.1 and 10.4.
-/

public section

open MeasureTheory MulAction Set UpperHalfPlane TauCeti

open scoped MatrixGroups Pointwise ENNReal

namespace Subgroup

variable (Γ : Subgroup PSL(2, ℝ))

/-- A discrete subgroup of `PSL(2, ℝ)` is countable, since it acts properly discontinuously on
the σ-compact space `ℍ`. -/
instance instCountableOfDiscreteTopology [DiscreteTopology Γ] : Countable Γ :=
  countable_of_properlyDiscontinuousSMul Γ (T := ℍ)

/-- The points of `ℍ` with nontrivial stabilizer in a countable subgroup of `PSL(2, ℝ)` form a
countable set: each nontrivial element fixes at most one point. -/
theorem countable_compl_freeLocus [Countable Γ] : ((freeLocus Γ ℍ : Set ℍ)ᶜ).Countable := by
  refine (countable_iUnion fun g : Γ ↦ countable_iUnion fun _ : g ≠ 1 ↦
    Set.Subsingleton.countable (s := {z : ℍ | g • z = z}) fun z hz w hw ↦ ?_).mono fun z hz ↦ ?_
  · by_contra hwz
    exact ‹g ≠ 1› <| Subtype.ext <|
      Matrix.ProjectiveSpecialLinearGroup.eq_one_of_smul_eq_self_of_smul_eq_self hz hw
        (Ne.symm hwz)
  · obtain ⟨g, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (by simpa using hz)
    exact mem_iUnion₂.mpr ⟨g, fun h ↦ hg1 (Subtype.ext h), g.2⟩

/-- For a countable subgroup of `PSL(2, ℝ)`, the points of `ℍ` with nontrivial stabilizer form a
null set. -/
theorem volume_compl_freeLocus [Countable Γ] :
    volume ((freeLocus Γ ℍ : Set ℍ)ᶜ) = 0 :=
  (countable_compl_freeLocus Γ).measure_zero volume

/-- **A Fuchsian group has a measurable fundamental domain.** For a discrete subgroup
`Γ ≤ PSL(2, ℝ)` there is a measurable fundamental domain for its action on `ℍ` whose translates
by distinct elements of `Γ` are disjoint. -/
theorem exists_isFundamentalDomain [DiscreteTopology Γ] :
    ∃ s : Set ℍ, MeasurableSet s ∧ (Pairwise fun g h : Γ ↦ Disjoint (g • s) (h • s)) ∧
      IsFundamentalDomain Γ s :=
  exists_isFundamentalDomain_of_properlyDiscontinuousSMul volume (volume_compl_freeLocus Γ)

/-- A discrete subgroup of `PSL(2, ℝ)` has a fundamental domain, so that its covolume is the area
of any of its fundamental domains. -/
instance hasFundamentalDomain [DiscreteTopology Γ] : HasFundamentalDomain Γ ℍ :=
  let ⟨_, _, _, hs⟩ := exists_isFundamentalDomain Γ
  hs.hasFundamentalDomain volume

/-- The covolume of a discrete subgroup of `PSL(2, ℝ)` is positive. -/
theorem covolume_pos [DiscreteTopology Γ] : 0 < covolume Γ ℍ := by
  obtain ⟨s, -, -, hs⟩ := exists_isFundamentalDomain Γ
  rw [hs.covolume_eq_volume]
  exact pos_iff_ne_zero.mpr <| hs.measure_ne_zero <|
    (Measure.measure_univ_pos.mp (isOpen_univ.measure_pos volume univ_nonempty))

/-- **Covolume is a conjugacy invariant**: a discrete subgroup of `PSL(2, ℝ)` and its conjugate
`g Γ g⁻¹` have the same covolume. -/
theorem covolume_conjAct_smul [DiscreteTopology Γ] (g : PSL(2, ℝ)) :
    covolume (ConjAct.toConjAct g • Γ : Subgroup PSL(2, ℝ)) ℍ = covolume Γ ℍ := by
  have : Countable (ConjAct.toConjAct g • Γ : Subgroup PSL(2, ℝ)) :=
    (equivSMul (ConjAct.toConjAct g) Γ).symm.injective.countable
  obtain ⟨s, -, -, hs⟩ := exists_isFundamentalDomain Γ
  rw [hs.covolume_eq_volume, (hs.smul_of_eq_conjAct_pointwise_smul
    (measurePreserving_smul g⁻¹ volume).quasiMeasurePreserving rfl).covolume_eq_volume,
    measure_smul]

/-- **Covolume is multiplicative in the index**: for subgroups `Δ ≤ Γ` of `PSL(2, ℝ)` with `Γ`
discrete, the covolume of `Δ` is the index `[Γ : Δ]`, counted in `ℕ∞`, times the covolume of
`Γ`. In particular a subgroup of infinite index has infinite covolume. -/
theorem covolume_eq_card_mul_covolume [DiscreteTopology Γ] {Δ : Subgroup PSL(2, ℝ)}
    (h : Δ ≤ Γ) :
    covolume Δ ℍ = ENat.card (Γ ⧸ Δ.subgroupOf Γ) * covolume Γ ℍ := by
  have : Countable Δ := (inclusion_injective h).countable
  have : Countable (Γ ⧸ Δ.subgroupOf Γ) := QuotientGroup.mk_surjective.countable
  obtain ⟨s, -, -, hs⟩ := exists_isFundamentalDomain Γ
  have ht := (hs.subgroup_iUnion_out_inv_smul (Δ.subgroupOf Γ)).of_subgroupOf
  rw [inf_of_le_left h] at ht
  rw [ht.covolume_eq_volume, hs.covolume_eq_volume, measure_iUnion₀ ?_
    fun q ↦ hs.nullMeasurableSet_smul _]
  · simp_rw [measure_smul]
    exact ENNReal.tsum_const _
  · intro q q' hqq'
    refine hs.aedisjoint fun heq ↦ hqq' ?_
    rw [← q.out_eq', ← q'.out_eq', inv_inj.mp heq]

/-- A subgroup `Γ ≤ PSL(2, ℝ)` is **cofinite** (a lattice) when it is discrete and the quotient
`Γ \ ℍ` has finite hyperbolic area, that is, `Γ` has finite covolume. -/
structure IsCofinite : Prop where
  discreteTopology : DiscreteTopology Γ
  covolume_ne_top : covolume Γ ℍ ≠ ∞

variable {Γ}

/-- A discrete subgroup is cofinite exactly when its covolume is finite. -/
theorem isCofinite_iff_covolume_ne_top [DiscreteTopology Γ] :
    Γ.IsCofinite ↔ covolume Γ ℍ ≠ ∞ :=
  ⟨IsCofinite.covolume_ne_top, fun h ↦ ⟨inferInstance, h⟩⟩

/-- A cofinite subgroup has fundamental domains of finite area. -/
theorem IsCofinite.volume_ne_top (hΓ : Γ.IsCofinite) {s : Set ℍ}
    (hs : IsFundamentalDomain Γ s) : volume s ≠ ∞ := by
  have := hΓ.discreteTopology
  rw [← hs.covolume_eq_volume]
  exact hΓ.covolume_ne_top

/-- A discrete subgroup with a fundamental domain of finite area is cofinite. -/
theorem IsCofinite.of_isFundamentalDomain [DiscreteTopology Γ] {s : Set ℍ}
    (hs : IsFundamentalDomain Γ s) (h : volume s ≠ ∞) : Γ.IsCofinite := by
  rwa [isCofinite_iff_covolume_ne_top, hs.covolume_eq_volume]

/-- **Cofiniteness and finite index**: a subgroup `Δ` of a discrete subgroup `Γ ≤ PSL(2, ℝ)`
is cofinite exactly when `Γ` is cofinite and `Δ` has finite index in `Γ`. -/
theorem isCofinite_iff_of_le [DiscreteTopology Γ] {Δ : Subgroup PSL(2, ℝ)} (h : Δ ≤ Γ) :
    Δ.IsCofinite ↔ Γ.IsCofinite ∧ (Δ.subgroupOf Γ).FiniteIndex := by
  have hΔ : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  have hcard : (ENat.card (Γ ⧸ Δ.subgroupOf Γ) : ℝ≥0∞) ≠ 0 := by simp
  rw [finiteIndex_iff_finite_quotient, ← ENat.card_lt_top]
  constructor
  · rintro ⟨-, hne⟩
    rw [covolume_eq_card_mul_covolume Γ h] at hne
    refine ⟨⟨inferInstance, fun htop ↦ hne (by rw [htop, ENNReal.mul_top hcard])⟩,
      lt_top_iff_ne_top.mpr fun htop ↦ hne ?_⟩
    rw [htop]
    simpa using ENNReal.top_mul (covolume_pos Γ).ne'
  · rintro ⟨hΓ, hfin⟩
    refine ⟨hΔ, ?_⟩
    rw [covolume_eq_card_mul_covolume Γ h]
    exact ENNReal.mul_ne_top (by simpa [lt_top_iff_ne_top] using hfin) hΓ.covolume_ne_top

end Subgroup
