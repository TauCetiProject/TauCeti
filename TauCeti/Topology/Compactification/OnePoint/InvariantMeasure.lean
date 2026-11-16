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
import TauCeti.GroupTheory.Amenable.Extension
import TauCeti.GroupTheory.Amenable.Finite
import TauCeti.Topology.Algebra.Group.Subgroup
import TauCeti.Topology.Compactification.OnePoint.Amenable
import TauCeti.Topology.Compactification.OnePoint.Nhds

/-!
# Furstenberg's lemma for invariant measures on the projective line

Furstenberg's lemma converts an invariant finite measure on the projective line `OnePoint 𝕜` into
amenability of the acting discrete group. In particular, in Burger's proof of relative property (T)
for `(ℤ² ⋊ G, ℤ²)` (`TauCeti/GroupTheory/PropertyT/SLTwo.lean`), pushing diagonal spectral measures
along almost invariant vectors and passing to a weak-⋆ limit yields a `G`-invariant Borel
probability measure on `OnePoint ℝ`, and this file supplies the measure-theoretic step forcing `G`
to be amenable.

The argument splits into two parts:

1. Over any field `K` with a measurable space structure on `OnePoint K` making singletons
   measurable, if a subgroup `Γ ≤ PSL(2, K)` preserves a finite measure `ν` with an atom
   `ν {x₀} ≠ 0`, every point in the `Γ`-orbit of `x₀` has the same positive measure, so finiteness
   of `ν` forces the orbit to be finite; then `TauCeti.amenable_psl_of_finite_onePoint_orbit`
   gives amenability of `Γ`
   (`TauCeti.amenable_psl_of_map_onePoint_smul_eq_of_measure_singleton_ne_zero`).
2. Now let `𝕜` be a proper nontrivially normed field (`ℝ`, `ℂ`, or a `p`-adic field) and let `ν` be
   a nonzero finite Borel measure on `OnePoint 𝕜` preserved by an infinite discrete subgroup
   `Γ ≤ PSL(2, 𝕜)`. Since `Γ` is discrete it is closed in `PSL(2, 𝕜)`, so any injective sequence in
   `Γ` leaves every compact subset of `PSL(2, 𝕜)`. By
   `OnePoint.exists_tendsto_psl_smul_of_tendsto_cocompact`, a subsequence sends every point
   `x ≠ a` to a single point `b`. If `ν {a} = 0`, dominated convergence of bounded continuous
   functions identifies `ν` with `Measure.map (fun _ ↦ b) ν`, giving `ν {b} = ν Set.univ ≠ 0`
   (`TauCeti.exists_measure_onePoint_singleton_ne_zero_of_discrete_of_infinite_of_map_psl_smul_eq`).

Combining the two steps over a proper nontrivially normed field `𝕜`, any discrete subgroup of
`PSL(2, 𝕜)` preserving a nonzero finite Borel measure on `OnePoint 𝕜` is amenable, and more
generally any group acting on `OnePoint 𝕜` through a homomorphism `φ : G →* PSL(2, 𝕜)` with
discrete range and finite kernel and preserving a nonzero finite Borel measure on `OnePoint 𝕜` is
amenable (`TauCeti.amenable_of_discrete_psl_range_of_finite_ker_of_map_onePoint_smul_eq`).

## Main results

* `TauCeti.amenable_psl_of_map_onePoint_smul_eq_of_measure_singleton_ne_zero`: over any field `K`
  with measurable singletons on `OnePoint K`, a subgroup of `PSL(2, K)` preserving a finite
  measure on `OnePoint K` with an atom is amenable.
* `TauCeti.exists_measure_onePoint_singleton_ne_zero_of_discrete_of_infinite_of_map_psl_smul_eq`:
  over a proper nontrivially normed field `𝕜`, every nonzero finite Borel measure on `OnePoint 𝕜`
  preserved by an infinite discrete subgroup of `PSL(2, 𝕜)` has an atom.
* `TauCeti.amenable_psl_of_discrete_of_map_onePoint_smul_eq`: over a proper nontrivially normed
  field `𝕜`, every discrete subgroup of `PSL(2, 𝕜)` preserving a nonzero finite Borel measure on
  `OnePoint 𝕜` is amenable.
* `TauCeti.amenable_of_discrete_psl_range_of_finite_ker_of_map_onePoint_smul_eq`: over a proper
  nontrivially normed field `𝕜`, a group mapping to `PSL(2, 𝕜)` with discrete range and finite
  kernel and preserving a nonzero finite Borel measure on `OnePoint 𝕜` is amenable.

## References

* H. Furstenberg, *A Poisson formula for semi-simple Lie groups*, Ann. of Math. (2) 77 (1963),
  335–386.
* H. Furstenberg, *A note on Borel's density theorem*, Proc. Amer. Math. Soc. 55 (1976),
  209–212.
* R. J. Zimmer, *Ergodic Theory and Semisimple Groups*, Birkhäuser (1984), Lemma 3.2.1 and
  Corollary 3.2.2.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Example 14.2.8.
-/

public section

open Filter Matrix MeasureTheory MulAction Topology
open scoped BoundedContinuousFunction ENNReal MatrixGroups

namespace TauCeti

section Field

variable {K : Type*} [Field K] [DecidableEq K] [MeasurableSpace (OnePoint K)]
  [MeasurableSingletonClass (OnePoint K)]

/-- A subgroup of `PSL(2, K)` preserving a finite measure on `OnePoint K` (with measurable
singletons) that has an atom is amenable for every group topology. -/
theorem amenable_psl_of_map_onePoint_smul_eq_of_measure_singleton_ne_zero {Γ : Subgroup PSL(2, K)}
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] {ν : Measure (OnePoint K)} [IsFiniteMeasure ν]
    {x₀ : OnePoint K} (hν : ∀ g : Γ, Measure.map ((g : PSL(2, K)) • ·) ν = ν)
    (hx₀ : ν {x₀} ≠ 0) : Amenable Γ := by
  have horb_eq {y : OnePoint K} (hy : y ∈ orbit Γ x₀) : ν {y} = ν {x₀} := by
    rcases hy with ⟨g, rfl⟩
    simp only [Subgroup.smul_def]
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
  exact amenable_psl_of_finite_onePoint_orbit horb

end Field

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜] [ProperSpace 𝕜]
  [MeasurableSpace (OnePoint 𝕜)] [BorelSpace (OnePoint 𝕜)]

/-- **Furstenberg's lemma (atom step).** Every nonzero finite Borel measure `ν` on `OnePoint 𝕜`
preserved by an infinite discrete subgroup `Γ ≤ PSL(2, 𝕜)` has an atom `x₀` with `ν {x₀} ≠ 0`. -/
theorem exists_measure_onePoint_singleton_ne_zero_of_discrete_of_infinite_of_map_psl_smul_eq
    {Γ : Subgroup PSL(2, 𝕜)} [DiscreteTopology Γ] [Infinite Γ] {ν : Measure (OnePoint 𝕜)}
    [IsFiniteMeasure ν] [NeZero ν]
    (hν : ∀ g : Γ, Measure.map ((g : PSL(2, 𝕜)) • ·) ν = ν) :
    ∃ x₀ : OnePoint 𝕜, ν {x₀} ≠ 0 := by
  let γ : ℕ ↪ Γ := Infinite.natEmbedding Γ
  have hclosed : IsClosed (Γ : Set PSL(2, 𝕜)) :=
    Subgroup.isClosed_of_weaklyLocallyCompactSpace Γ
  have hcoe : Tendsto ((↑) : Γ → PSL(2, 𝕜)) cofinite (cocompact PSL(2, 𝕜)) :=
    tendsto_cofinite_cocompact_of_discrete hclosed.isClosedEmbedding_subtypeVal.tendsto_cocompact
  have hg : Tendsto (fun n ↦ (γ n : PSL(2, 𝕜))) atTop (cocompact PSL(2, 𝕜)) :=
    Nat.cofinite_eq_atTop ▸ hcoe.comp γ.injective.tendsto_cofinite
  obtain ⟨φ, a, b, -, hlim⟩ := OnePoint.exists_tendsto_psl_smul_of_tendsto_cocompact hg
  rcases eq_or_ne (ν {a}) 0 with ha | ha
  · have hν_eq : ν = Measure.map (fun _ : OnePoint 𝕜 ↦ b) ν := by
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
theorem amenable_psl_of_discrete_of_map_onePoint_smul_eq {Γ : Subgroup PSL(2, 𝕜)}
    [DiscreteTopology Γ] {ν : Measure (OnePoint 𝕜)} [IsFiniteMeasure ν] [NeZero ν]
    (hν : ∀ g : Γ, Measure.map ((g : PSL(2, 𝕜)) • ·) ν = ν) : Amenable Γ := by
  rcases finite_or_infinite Γ with hfin | hinf
  · infer_instance
  · obtain ⟨x₀, hx₀⟩ :=
      exists_measure_onePoint_singleton_ne_zero_of_discrete_of_infinite_of_map_psl_smul_eq hν
    exact amenable_psl_of_map_onePoint_smul_eq_of_measure_singleton_ne_zero hν hx₀

/-- Every group acting on `OnePoint 𝕜` through a homomorphism `φ : G →* PSL(2, 𝕜)` with discrete
range and finite kernel, and preserving a nonzero finite Borel measure on `OnePoint 𝕜`, is amenable
for every group topology. -/
theorem amenable_of_discrete_psl_range_of_finite_ker_of_map_onePoint_smul_eq {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {φ : G →* PSL(2, 𝕜)} [DiscreteTopology φ.range]
    [Finite φ.ker] {ν : Measure (OnePoint 𝕜)} [IsFiniteMeasure ν] [NeZero ν]
    (hν : ∀ g : G, Measure.map (φ g • ·) ν = ν) : Amenable G := by
  apply Amenable.of_discrete
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  have : Amenable φ.range := by
    refine amenable_psl_of_discrete_of_map_onePoint_smul_eq (ν := ν) fun γ ↦ ?_
    obtain ⟨g, hg⟩ := γ.property
    simpa [← hg] using hν g
  exact Amenable.of_ker_le_range φ.ker.subtype φ.rangeRestrict
    (by simp [MonoidHom.ker_rangeRestrict])

end TauCeti
