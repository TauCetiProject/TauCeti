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
import TauCeti.MeasureTheory.Group.Action

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
* `Subgroup.freeLocus_nonempty`: some point of `ℍ` has trivial stabilizer in a countable `Γ`.
* `Subgroup.exists_isFundamentalDomain`: a discrete `Γ` has a measurable fundamental domain
  whose translates are pairwise disjoint.
* `Subgroup.card_mul_volume_ball_le_covolume`: balls in `ℍ` with pairwise disjoint
  `Γ`-translates have total area at most the covolume.
* `Subgroup.IsCofinite`: a discrete subgroup of finite covolume.
* `Subgroup.IsCofinite.volume_ne_top`,
  `MeasureTheory.IsFundamentalDomain.isCofinite_of_volume_ne_top`: a discrete subgroup is
  cofinite exactly when one, equivalently every, fundamental domain has finite area.
* `Subgroup.isCofinite_conjAct_smul_iff`: cofiniteness is invariant under conjugation.
* `Subgroup.isCofinite_iff_isCofinite_and_finiteIndex`: a subgroup of a discrete group is
  cofinite exactly when the larger group is cofinite and the index is finite.

Positivity, conjugation invariance and index multiplicativity of the covolume are the generic
`MeasureTheory.covolume_pos`, `MeasureTheory.covolume_conjAct_smul` and
`MeasureTheory.covolume_eq_card_mul_covolume`, which apply directly to `PSL(2, ℝ)` acting on `ℍ`.

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

/-- A countable subgroup of `PSL(2, ℝ)` has a point of `ℍ` with trivial stabilizer. -/
theorem freeLocus_nonempty [Countable Γ] : (freeLocus Γ ℍ : Set ℍ).Nonempty := by
  by_contra h
  have hnull := volume_compl_freeLocus Γ
  rw [not_nonempty_iff_eq_empty.mp h, compl_empty] at hnull
  exact (isOpen_univ.measure_pos volume univ_nonempty).ne' hnull

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
  rw [isCofinite_iff_covolume_ne_top, MeasureTheory.covolume_conjAct_smul]
  exact hΓ.covolume_ne_top

/-- A cofinite subgroup has fundamental domains of finite area. -/
theorem IsCofinite.volume_ne_top (hΓ : Γ.IsCofinite) {s : Set ℍ}
    (hs : IsFundamentalDomain Γ s) : volume s ≠ ∞ := by
  have := hΓ.discreteTopology
  rw [← hs.covolume_eq_volume]
  exact hΓ.covolume_ne_top

/-- **Packing balls in a fundamental domain.** Let `Γ ≤ PSL(2, ℝ)` be discrete, and let `y i`,
for `i` in a finite set `s`, be centres of balls of radius `r` such that the ball about `y j`
meets the `k`-translate of the ball about `y i`, for `k ∈ Γ`, only when `k = 1` and `i = j`. Then
the balls have pairwise disjoint translates, so their total area is at most the covolume. -/
theorem card_mul_volume_ball_le_covolume [DiscreteTopology Γ] {ι : Type*} (s : Finset ι)
    {y : ι → ℍ} {r : ℝ}
    (h : ∀ k ∈ Γ, ∀ i ∈ s, ∀ j ∈ s, ∀ z : ℍ, dist z (k • y i) < r → dist z (y j) < r →
      k = 1 ∧ i = j) :
    s.card * volume (Metric.ball I r) ≤ covolume Γ ℍ := by
  set t := ⋃ i ∈ s, Metric.ball (y i) r
  obtain ⟨F, -, -, hF⟩ := exists_isFundamentalDomain Γ
  have hvol : volume t = s.card * volume (Metric.ball I r) := by
    rw [measure_biUnion_finset (fun i hi j hj hne ↦ ?_) fun i _ ↦ measurableSet_ball]
    · rw [Finset.sum_congr rfl fun i _ ↦
        measure_ball_eq_measure_ball (G := PSL(2, ℝ)) volume (y i) I r]
      simp
    · rw [Function.onFun, Set.disjoint_left]
      intro z hz₁ hz₂
      exact hne (h 1 Γ.one_mem i hi j hj z (by rwa [one_smul]) hz₂).2
  rw [← hvol, hF.covolume_eq_volume]
  refine hF.measure_le_of_disjoint_smul
    (s.measurableSet_biUnion fun i _ ↦ measurableSet_ball).nullMeasurableSet
    fun k hk ↦ ?_
  simp only [t, smul_set_iUnion₂, disjoint_iUnion₂_left, disjoint_iUnion₂_right]
  intro i hi j hj
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  rw [mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, Metric.mem_ball] at hz₁
  push_cast at hz₁
  -- translating back by `k`, the ball about `y i` meets the `k`-translate of that about `y j`
  exact hk (Subtype.ext (h k k.2 j hj i hi z
    (by rwa [← dist_smul (k : PSL(2, ℝ))⁻¹, inv_smul_smul]) hz₂).1)

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
    rw [MeasureTheory.covolume_eq_card_mul_covolume h] at hne
    refine ⟨⟨inferInstance, fun htop ↦ hne (by rw [htop, ENNReal.mul_top hcard])⟩,
      lt_top_iff_ne_top.mpr fun htop ↦ hne ?_⟩
    rw [htop]
    simpa using ENNReal.top_mul (MeasureTheory.covolume_pos (G := Γ) (α := ℍ) <|
      Measure.measure_univ_pos.mp (isOpen_univ.measure_pos volume univ_nonempty)).ne'
  · rintro ⟨hΓ, hfin⟩
    refine ⟨hΔ, ?_⟩
    rw [MeasureTheory.covolume_eq_card_mul_covolume h]
    exact ENNReal.mul_ne_top (by simpa [lt_top_iff_ne_top] using hfin) hΓ.covolume_ne_top

end Subgroup

namespace MeasureTheory.IsFundamentalDomain

variable {Γ : Subgroup PSL(2, ℝ)}

/-- A discrete subgroup of `PSL(2, ℝ)` with a fundamental domain of finite area is cofinite. -/
theorem isCofinite_of_volume_ne_top [DiscreteTopology Γ] {s : Set ℍ}
    (hs : IsFundamentalDomain Γ s) (h : volume s ≠ ∞) : Γ.IsCofinite := by
  rwa [Subgroup.isCofinite_iff_covolume_ne_top, hs.covolume_eq_volume]

end MeasureTheory.IsFundamentalDomain
