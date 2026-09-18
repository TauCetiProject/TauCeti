/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.ProperAction
public import TauCeti.Analysis.Complex.UpperHalfPlane.Measure
public import TauCeti.Analysis.Complex.UpperHalfPlane.Stabilizer
public import TauCeti.MeasureTheory.Group.FundamentalDomain
public import TauCeti.MeasureTheory.Group.ProperlyDiscontinuous

/-!
# Fundamental domains, covolume, and cofinite Fuchsian groups

Let `Γ ≤ PSL(2, ℝ)` be a discrete subgroup, acting on the upper half-plane `ℍ` with Mathlib's
invariant measure `volume` (density `y⁻² dx dy`). This file shows that `Γ` has a measurable
fundamental domain, so that the covolume `MeasureTheory.covolume Γ ℍ` — the hyperbolic area of
the quotient `Γ \ ℍ` — is the area of any measurable fundamental domain
(`MeasureTheory.IsFundamentalDomain.covolume_eq_volume`), and defines the cofinite Fuchsian
groups as the discrete subgroups of finite covolume.

The fundamental domain comes from the general construction
`MeasureTheory.Measure.exists_isFundamentalDomain_of_properlyDiscontinuousSMul`. Its hypothesis,
that the points with nontrivial stabilizer are null, holds because a nontrivial element of
`PSL(2, ℝ)` fixes at most one point of `ℍ` and a discrete subgroup is countable, so these points
form a countable set.

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

These three are the specializations to `PSL(2, ℝ)` acting on `ℍ` of `MeasureTheory.covolume_pos`,
`MeasureTheory.covolume_conjAct_smul` and `MeasureTheory.covolume_eq_card_mul_covolume`.
* `Subgroup.IsCofinite`: a discrete subgroup of finite covolume.
* `Subgroup.IsCofinite.volume_ne_top`, `Subgroup.IsCofinite.of_isFundamentalDomain`: a discrete
  subgroup is cofinite exactly when one, equivalently every, fundamental domain has finite area.
* `Subgroup.isCofinite_conjAct_smul_iff`: cofiniteness is invariant under conjugation.
* `Subgroup.isCofinite_iff_isCofinite_and_finiteIndex`: a subgroup of a discrete group is
  cofinite exactly when the larger group is cofinite and the index is finite.

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
  volume.exists_isFundamentalDomain_of_properlyDiscontinuousSMul (volume_compl_freeLocus Γ)

/-- A discrete subgroup of `PSL(2, ℝ)` has a fundamental domain, so that its covolume is the area
of any of its fundamental domains. -/
instance hasFundamentalDomain [DiscreteTopology Γ] : HasFundamentalDomain Γ ℍ :=
  let ⟨_, _, _, hs⟩ := exists_isFundamentalDomain Γ
  hs.hasFundamentalDomain volume

/-- The covolume of a discrete subgroup of `PSL(2, ℝ)` is positive. -/
theorem covolume_pos [DiscreteTopology Γ] : 0 < covolume Γ ℍ :=
  MeasureTheory.covolume_pos <|
    Measure.measure_univ_pos.mp (isOpen_univ.measure_pos volume univ_nonempty)

/-- **Covolume is a conjugacy invariant**: a discrete subgroup of `PSL(2, ℝ)` and its conjugate
`g Γ g⁻¹` have the same covolume. -/
theorem covolume_conjAct_smul [DiscreteTopology Γ] (g : PSL(2, ℝ)) :
    covolume (ConjAct.toConjAct g • Γ : Subgroup PSL(2, ℝ)) ℍ = covolume Γ ℍ :=
  MeasureTheory.covolume_conjAct_smul Γ g

/-- **Covolume is multiplicative in the index**: for subgroups `Δ ≤ Γ` of `PSL(2, ℝ)` with `Γ`
discrete, the covolume of `Δ` is the index `[Γ : Δ]`, counted in `ℕ∞`, times the covolume of
`Γ`. In particular a subgroup of infinite index has infinite covolume. -/
theorem covolume_eq_card_mul_covolume [DiscreteTopology Γ] {Δ : Subgroup PSL(2, ℝ)}
    (h : Δ ≤ Γ) :
    covolume Δ ℍ = ENat.card (Γ ⧸ Δ.subgroupOf Γ) * covolume Γ ℍ :=
  MeasureTheory.covolume_eq_card_mul_covolume h

/-- A subgroup `Γ ≤ PSL(2, ℝ)` is **cofinite** (a lattice) when it is discrete and the quotient
`Γ \ ℍ` has finite hyperbolic area, that is, `Γ` has finite covolume. -/
structure IsCofinite : Prop where
  discreteTopology : DiscreteTopology Γ
  covolume_ne_top : covolume Γ ℍ ≠ ∞

variable {Γ}

/-- A discrete subgroup is cofinite exactly when its covolume is finite. -/
@[simp]
theorem isCofinite_iff_covolume_ne_top [DiscreteTopology Γ] :
    Γ.IsCofinite ↔ covolume Γ ℍ ≠ ∞ :=
  ⟨IsCofinite.covolume_ne_top, fun h ↦ ⟨inferInstance, h⟩⟩

/-- A conjugate `g Γ g⁻¹` of a discrete subgroup of `PSL(2, ℝ)` is discrete. -/
instance discreteTopology_conjAct_smul [DiscreteTopology Γ] (g : PSL(2, ℝ)) :
    DiscreteTopology (ConjAct.toConjAct g • Γ : Subgroup PSL(2, ℝ)) :=
  DiscreteTopology.of_continuous_injective (f := (equivSMul (ConjAct.toConjAct g) Γ).symm)
    (by fun_prop) (equivSMul (ConjAct.toConjAct g) Γ).symm.injective

/-- **Cofiniteness is a conjugacy invariant**: a conjugate `g Γ g⁻¹` of a subgroup
`Γ ≤ PSL(2, ℝ)` is cofinite exactly when `Γ` is. -/
@[simp]
theorem isCofinite_conjAct_smul_iff (g : PSL(2, ℝ)) :
    (ConjAct.toConjAct g • Γ : Subgroup PSL(2, ℝ)).IsCofinite ↔ Γ.IsCofinite := by
  suffices h : ∀ (Γ : Subgroup PSL(2, ℝ)) (g : PSL(2, ℝ)), Γ.IsCofinite →
      (ConjAct.toConjAct g • Γ : Subgroup PSL(2, ℝ)).IsCofinite by
    refine ⟨fun hΓ ↦ ?_, h Γ g⟩
    simpa [smul_smul, ← map_mul] using h _ g⁻¹ hΓ
  intro Γ g hΓ
  have := hΓ.discreteTopology
  rw [isCofinite_iff_covolume_ne_top, covolume_conjAct_smul]
  exact hΓ.covolume_ne_top

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
theorem isCofinite_iff_isCofinite_and_finiteIndex [DiscreteTopology Γ] {Δ : Subgroup PSL(2, ℝ)}
    (h : Δ ≤ Γ) :
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
