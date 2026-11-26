/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.LocallyFree.Null
public import TauCeti.Geometry.Manifold.Measure.Submersion
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.LocallyFree
public import TauCeti.Geometry.Symplectic.Manifold.DuistermaatHeckman

/-!
# Absolute continuity of the Duistermaat–Heckman measure

Let `σ` be a two-form on a manifold `M` of dimension `2 n`, and let `μ : M → F` be a `C¹` map to a
finite-dimensional real vector space. The Duistermaat–Heckman measure `μ_* |σⁿ / n!|`
(`TauCeti.SmoothTwoForm.duistermaatHeckmanMeasure`) is absolutely continuous with respect to
Lebesgue measure on `F` as soon as the critical points of `μ`, the points where its differential is
not surjective, form a null set
(`TauCeti.SmoothTwoForm.duistermaatHeckmanMeasure_absolutelyContinuous`). Indeed, let `A ⊆ F` be
Lebesgue-null. Near a regular point `μ` is a submersion, so the regular points mapped into `A` form
a null set (`TauCeti.IsNullSet.inter_preimage_of_isSubmersionAt`); together with the critical points
this covers `μ⁻¹(A)`. The Liouville measure, which has a density in every chart, vanishes on null
sets (`TauCeti.RoughForm.measure_eq_zero_of_isNullSet`), so `μ⁻¹(A)` has Liouville measure zero.

For the moment map `μ : M → 𝔤*` of a Lie group action and a nondegenerate `σ`, the critical points
are exactly the points with nontrivial isotropy algebra
(`TauCeti.SmoothTwoForm.IsMomentMap.surjective_mfderiv_toContinuousLinearMap_iff`). For an
effective action of a compact commutative Lie group, such as a torus, on a connected manifold these
points form a null set (`TauCeti.Lie.isNullSet_setOf_isotropy_ne_bot`). Hence **the
Duistermaat–Heckman measure of an effective Hamiltonian torus action on a connected symplectic
manifold is absolutely continuous with respect to Lebesgue measure on `𝔤*`**
(`TauCeti.SmoothTwoForm.IsMomentMap.duistermaatHeckmanMeasure_absolutelyContinuous`). Lebesgue
measure is any additive Haar measure, so the statement covers every normalization, in particular
the one making the weight lattice have covolume one. Neither compactness of `M` nor closedness of
`σ` is used. Effectiveness cannot be dropped: for the trivial action of the circle the moment map
is constant and its Duistermaat–Heckman measure is a point mass
(`TauCeti.SmoothTwoForm.duistermaatHeckmanMeasure_const`).

## Main results

* `TauCeti.SmoothTwoForm.duistermaatHeckmanMeasure_absolutelyContinuous`: a map whose critical
  points form a null set has absolutely continuous Duistermaat–Heckman measure.
* `TauCeti.SmoothTwoForm.IsMomentMap.duistermaatHeckmanMeasure_absolutelyContinuous`: the
  Duistermaat–Heckman measure of an effective action of a compact commutative Lie group on a
  connected manifold with a nondegenerate two-form is absolutely continuous.

## References

* J. J. Duistermaat and G. J. Heckman, *On the variation in the cohomology of the symplectic form
  of the reduced phase space*, Invent. Math. 69 (1982), 259–268.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 30.1 (the Duistermaat–Heckman measure and its density).
-/

public section

open Function MeasureTheory Module Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} [Fact (finrank ℝ E = 2 * n)]
  {σ : SmoothTwoForm I M}

/-- **The Duistermaat–Heckman measure of a map with null critical set is absolutely
continuous.** If the critical points of a `C¹` map `μ : M → F` to a finite-dimensional real vector
space form a null set, then `μ_* |σⁿ / n!|` is absolutely continuous with respect to every
additive Haar measure on `F`. -/
theorem duistermaatHeckmanMeasure_absolutelyContinuous [LindelofSpace M] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] {μ : M → F} (hμ : ContMDiff I 𝓘(ℝ, F) 1 μ)
    (hcrit : IsNullSet I {x | ¬ Surjective (mfderiv I 𝓘(ℝ, F) μ x)}) (ν : Measure F)
    [ν.IsAddHaarMeasure] :
    σ.duistermaatHeckmanMeasure n μ ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hνs ↦ ?_
  rw [duistermaatHeckmanMeasure_apply hμ.continuous.measurable hs, liouvilleMeasure_def]
  -- The regular points mapped into `s` form a null set, since `μ` is a submersion there.
  have hreg : IsNullSet I ({x | Surjective (mfderiv I 𝓘(ℝ, F) μ x)} ∩ μ ⁻¹' s) :=
    ((isNullSet_modelWithCornersSelf_iff ν).2 hνs).inter_preimage_of_isSubmersionAt le_rfl
      fun x hx ↦ (hμ.contMDiffOn.isSubmersionAtOfComplement_of_surjective_mfderiv isOpen_univ
        (mem_univ x) le_rfl hx.1).isSubmersionAt
  refine RoughForm.measure_eq_zero_of_isNullSet _ ((hreg.union hcrit).mono fun x hx ↦ ?_)
  by_cases hx' : Surjective (mfderiv I 𝓘(ℝ, F) μ x)
  · exact Or.inl ⟨hx', hx⟩
  · exact Or.inr hx'

namespace IsMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {EG HG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} [TopologicalSpace G] [ChartedSpace HG G]
  [Group G] [LieGroup IG ∞ G] [MulAction G M] [ContMDiffSMul IG I ∞ G M]
  {μ : M → Module.Dual ℝ (GroupLieAlgebra IG G)}

/-- **The Duistermaat–Heckman measure of an effective torus action is absolutely continuous.**
Let a compact commutative Lie group `G`, such as a torus, act smoothly and effectively on a
connected Hausdorff σ-compact manifold `M` without boundary, with a nondegenerate two-form `σ` and
moment map `μ`. Then the Duistermaat–Heckman measure `μ_* |σⁿ / n!|`, with `μ` read in the
continuous dual `𝔤*`, is absolutely continuous with respect to every additive Haar measure on
`𝔤*`. -/
theorem duistermaatHeckmanMeasure_absolutelyContinuous [T2Space M] [SigmaCompactSpace M]
    [PreconnectedSpace M] [CompactSpace G] [IsMulCommutative G] [FaithfulSMul G M]
    [MeasurableSpace (StrongDual ℝ EG)] [BorelSpace (StrongDual ℝ EG)]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental IG G I M) μ) (hσ : σ.IsNondegenerate)
    (ν : Measure (StrongDual ℝ EG)) [ν.IsAddHaarMeasure] :
    σ.duistermaatHeckmanMeasure n
      (fun x ↦ (LinearMap.toContinuousLinearMap (μ x) : StrongDual ℝ EG)) ≪ ν := by
  refine SmoothTwoForm.duistermaatHeckmanMeasure_absolutelyContinuous
    (h.contMDiff_toContinuousLinearMap.of_le (by simp))
    ((Lie.isNullSet_setOf_isotropy_ne_bot (I := IG) (G := G) (M := M)).mono fun x hx ↦ ?_) ν
  -- A critical point of the moment map has nontrivial isotropy algebra.
  exact mt (h.surjective_mfderiv_toContinuousLinearMap_iff
    (hσ.nondegenerate_bilinFormAt x)).2 hx

end IsMomentMap

end TauCeti.SmoothTwoForm
