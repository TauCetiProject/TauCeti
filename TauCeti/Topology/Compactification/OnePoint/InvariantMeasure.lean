/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.Geometry.Manifold.Instances.OnePoint.ContinuousSMul
public import TauCeti.GroupTheory.Amenable.Basic

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Metrizable.Urysohn
import TauCeti.GroupTheory.Amenable.Extension
import TauCeti.GroupTheory.Amenable.Finite
import TauCeti.Topology.Algebra.Group.Subgroup
import TauCeti.Topology.Compactification.OnePoint.Amenable

/-!
# Furstenberg's lemma for invariant measures on the projective line

Let `𝕜` be a proper nontrivially normed field (`ℝ`, `ℂ`, or a `p`-adic field) and `Γ` a discrete
subgroup of `PSL(2, 𝕜)` preserving a nonzero finite Borel measure `ν` on the projective line
`OnePoint 𝕜`. Furstenberg's lemma shows that `Γ` is amenable:

1. If `ν` has an atom `ν {x₀} ≠ 0`, every point in the `Γ`-orbit of `x₀` has the same positive
   measure, so finiteness of `ν` forces the orbit to be finite; then
   `OnePoint.amenable_psl_of_finite_orbit` gives amenability of `Γ`
   (`OnePoint.amenable_of_measure_singleton_ne_zero`).
2. If `Γ` is infinite and discrete, it is closed in `PSL(2, 𝕜)`, so any injective sequence in `Γ`
   leaves every compact subset of `PSL(2, 𝕜)`. By
   `OnePoint.exists_tendsto_psl_smul_of_tendsto_cocompact`, a subsequence sends every point
   `x ≠ a` to a single point `b`. If `ν {a} = 0`, dominated convergence of bounded continuous
   functions identifies `ν` with `Measure.map (fun _ ↦ b) ν`, giving `ν {b} = ν Set.univ ≠ 0`
   (`OnePoint.exists_measure_singleton_ne_zero_of_map_smul_eq`).

Consequently, any group acting on `OnePoint 𝕜` through a homomorphism `φ : G →* PSL(2, 𝕜)` with
discrete range and finite kernel and preserving a nonzero finite Borel measure on `OnePoint 𝕜` is
amenable (`OnePoint.amenable_of_discrete_range_of_finite_ker_of_map_smul_eq`).

## Main results

* `OnePoint.amenable_of_measure_singleton_ne_zero`: a subgroup of `PSL(2, 𝕜)` preserving a finite
  Borel measure on `OnePoint 𝕜` with an atom is amenable.
* `OnePoint.exists_measure_singleton_ne_zero_of_map_smul_eq`: an infinite discrete subgroup of
  `PSL(2, 𝕜)` preserving a nonzero finite Borel measure on `OnePoint 𝕜` has an atom.
* `OnePoint.amenable_of_discrete_of_map_smul_eq`: every discrete subgroup of `PSL(2, 𝕜)` preserving
  a nonzero finite Borel measure on `OnePoint 𝕜` is amenable.
* `OnePoint.amenable_of_discrete_range_of_finite_ker_of_map_smul_eq`: a group mapping to `PSL(2, 𝕜)`
  with discrete range and finite kernel and preserving a nonzero finite Borel measure on
  `OnePoint 𝕜` is amenable.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Example 14.2.8.
* B. Bekka, P. de la Harpe, and A. Valette, *Kazhdan's Property (T)*, Theorem 3.2.2.
-/

public section

open Filter Matrix MeasureTheory MulAction Topology
open scoped BoundedContinuousFunction ENNReal MatrixGroups

namespace OnePoint

section Field

variable {K : Type*} [Field K] [DecidableEq K] [MeasurableSpace (OnePoint K)]
  [MeasurableSingletonClass (OnePoint K)]

/-- A subgroup of `PSL(2, K)` preserving a finite measure on `OnePoint K` (with measurable
singletons) that has an atom is amenable for every group topology: every point in the orbit of the
atom has the same positive measure, so the orbit is finite. -/
theorem amenable_of_measure_singleton_ne_zero {Γ : Subgroup PSL(2, K)} [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] {ν : Measure (OnePoint K)} [IsFiniteMeasure ν] {x₀ : OnePoint K}
    (hν : ∀ g : Γ, Measure.map ((g : PSL(2, K)) • ·) ν = ν) (hx₀ : ν {x₀} ≠ 0) :
    TauCeti.Amenable Γ := by
  have horb_eq {y : OnePoint K} (hy : y ∈ orbit Γ x₀) : ν {y} = ν {x₀} := by
    rcases hy with ⟨g, rfl⟩
    change ν {(g : PSL(2, K)) • x₀} = ν {x₀}
    have hm : AEMeasurable ((g : PSL(2, K)) • · : OnePoint K → OnePoint K) ν := by
      by_contra hnm
      have hν0 : ν ≠ 0 := fun h ↦ hx₀ (by simp [h])
      have hdir := (Measure.map_of_not_aemeasurable_of_ne_zero hnm hν0).symm.trans (hν g)
      exact hnm (hdir ▸ aemeasurable_dirac)
    have hpre : ((g : PSL(2, K)) • ·) ⁻¹' {(g : PSL(2, K)) • x₀} = {x₀} := by
      ext z
      simp
    calc ν {(g : PSL(2, K)) • x₀}
      _ = Measure.map ((g : PSL(2, K)) • ·) ν {(g : PSL(2, K)) • x₀} := by rw [hν g]
      _ = ν {x₀} := by rw [Measure.map_apply_of_aemeasurable hm (measurableSet_singleton _), hpre]
  have horb : (orbit Γ x₀).Finite := by
    by_contra hinf
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hx₀ (measure_ne_top ν Set.univ)
    obtain ⟨t, ht, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf n
    have hsum : (n : ℝ≥0∞) * ν {x₀} = ν t := by
      rw [← sum_measure_singleton, Finset.sum_congr rfl fun y hy ↦ horb_eq (ht hy),
        Finset.sum_const, hcard, nsmul_eq_mul]
    exact hn.not_ge ((measure_mono (Set.subset_univ _)).trans_eq' hsum.symm)
  exact amenable_psl_of_finite_orbit horb

end Field

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜] [ProperSpace 𝕜]
  [MeasurableSpace (OnePoint 𝕜)] [BorelSpace (OnePoint 𝕜)]

/-- **Furstenberg's lemma (atom step).** Every infinite discrete subgroup of `PSL(2, 𝕜)` preserving
a nonzero finite Borel measure on `OnePoint 𝕜` has a measure atom: an injective sequence in the
subgroup escapes compact subsets of `PSL(2, 𝕜)`, so a subsequence collapses the complement of a
point `a` to a point `b`, forcing either `ν {a} ≠ 0` or `ν = Measure.map (fun _ ↦ b) ν`. -/
theorem exists_measure_singleton_ne_zero_of_map_smul_eq {Γ : Subgroup PSL(2, 𝕜)}
    [DiscreteTopology Γ] [Infinite Γ] {ν : Measure (OnePoint 𝕜)} [IsFiniteMeasure ν] [NeZero ν]
    (hν : ∀ g : Γ, Measure.map ((g : PSL(2, 𝕜)) • ·) ν = ν) :
    ∃ x₀ : OnePoint 𝕜, ν {x₀} ≠ 0 := by
  let γ : ℕ ↪ Γ := Infinite.natEmbedding Γ
  have hclosed : IsClosed (Γ : Set PSL(2, 𝕜)) :=
    Subgroup.isClosed_of_weaklyLocallyCompactSpace Γ
  have hcoe : Tendsto ((↑) : Γ → PSL(2, 𝕜)) cofinite (cocompact PSL(2, 𝕜)) :=
    tendsto_cofinite_cocompact_of_discrete hclosed.isClosedEmbedding_subtypeVal.tendsto_cocompact
  have hg : Tendsto (fun n ↦ (γ n : PSL(2, 𝕜))) atTop (cocompact PSL(2, 𝕜)) :=
    Nat.cofinite_eq_atTop ▸ hcoe.comp γ.injective.tendsto_cofinite
  obtain ⟨φ, a, b, -, hlim⟩ := exists_tendsto_psl_smul_of_tendsto_cocompact hg
  rcases eq_or_ne (ν {a}) 0 with ha | ha
  · have : SecondCountableTopology (OnePoint 𝕜) :=
      ChartedSpace.secondCountable_of_sigmaCompact 𝕜 (OnePoint 𝕜)
    have : TopologicalSpace.MetrizableSpace (OnePoint 𝕜) :=
      TopologicalSpace.metrizableSpace_of_t3_secondCountable (OnePoint 𝕜)
    have hν_eq : ν = Measure.map (fun _ : OnePoint 𝕜 ↦ b) ν := by
      refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f ↦ ?_
      have hae : ∀ᵐ x ∂ν, Tendsto (fun n ↦ f ((γ (φ n) : PSL(2, 𝕜)) • x)) atTop (𝓝 (f b)) := by
        rw [ae_iff]
        refine measure_mono_null (fun x hx ↦ ?_) ha
        by_contra hxa
        exact hx ((f.continuous.tendsto b).comp (hlim hxa tendsto_const_nhds))
      have hdom := tendsto_integral_of_dominated_convergence (fun _ ↦ ‖f‖)
        (fun n ↦ (f.continuous.comp (continuous_const_smul _)).aestronglyMeasurable)
        (integrable_const ‖f‖) (fun n ↦ .of_forall fun x ↦ f.norm_coe_le_norm _) hae
      have hconst (n : ℕ) : ∫ x, f ((γ (φ n) : PSL(2, 𝕜)) • x) ∂ν = ∫ x, f x ∂ν := by
        have hm : AEMeasurable ((γ (φ n) : PSL(2, 𝕜)) • · : OnePoint 𝕜 → OnePoint 𝕜) ν :=
          (continuous_const_smul _).measurable.aemeasurable
        rw [← integral_map hm f.continuous.aestronglyMeasurable, hν (γ (φ n))]
      rw [integral_map aemeasurable_const f.continuous.aestronglyMeasurable]
      exact tendsto_nhds_unique tendsto_const_nhds (hdom.congr hconst)
    refine ⟨b, ?_⟩
    rw [hν_eq, Measure.map_apply measurable_const (measurableSet_singleton b)]
    simp [NeZero.ne ν]
  · exact ⟨a, ha⟩

/-- **Furstenberg's lemma on the projective line.** Every discrete subgroup of `PSL(2, 𝕜)`
preserving a nonzero finite Borel measure on `OnePoint 𝕜` is amenable. -/
theorem amenable_of_discrete_of_map_smul_eq {Γ : Subgroup PSL(2, 𝕜)} [DiscreteTopology Γ]
    {ν : Measure (OnePoint 𝕜)} [IsFiniteMeasure ν] [NeZero ν]
    (hν : ∀ g : Γ, Measure.map ((g : PSL(2, 𝕜)) • ·) ν = ν) :
    TauCeti.Amenable Γ := by
  rcases finite_or_infinite Γ with hfin | hinf
  · infer_instance
  · obtain ⟨x₀, hx₀⟩ := exists_measure_singleton_ne_zero_of_map_smul_eq hν
    exact amenable_of_measure_singleton_ne_zero hν hx₀

/-- Every group acting on `OnePoint 𝕜` through a homomorphism `φ : G →* PSL(2, 𝕜)` with discrete
range and finite kernel, and preserving a nonzero finite Borel measure on `OnePoint 𝕜`, is amenable
for every group topology: `φ.range` is discrete and preserves `ν`, hence is amenable, and `φ.ker`
is finite, hence amenable. -/
theorem amenable_of_discrete_range_of_finite_ker_of_map_smul_eq {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {φ : G →* PSL(2, 𝕜)} [DiscreteTopology φ.range]
    [Finite φ.ker] {ν : Measure (OnePoint 𝕜)} [IsFiniteMeasure ν] [NeZero ν]
    (hν : ∀ g : G, Measure.map (φ g • ·) ν = ν) :
    TauCeti.Amenable G := by
  apply TauCeti.Amenable.of_discrete
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  have : TauCeti.Amenable φ.range := by
    refine amenable_of_discrete_of_map_smul_eq (ν := ν) fun γ ↦ ?_
    obtain ⟨g, hg⟩ := γ.property
    simpa [← hg] using hν g
  exact TauCeti.Amenable.of_ker_le_range φ.ker.subtype φ.rangeRestrict
    (by simp [MonoidHom.ker_rangeRestrict])

end OnePoint
