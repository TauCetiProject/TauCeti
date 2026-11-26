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
import Mathlib.Analysis.LocallyConvex.HahnBanach
import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.AffineSpan

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
`σ` is used. Effectiveness cannot be dropped from this statement: for the trivial action of the
circle the moment map is constant and its Duistermaat–Heckman measure is a point mass
(`TauCeti.SmoothTwoForm.duistermaatHeckmanMeasure_const`).

For an action that need not be effective, the right reference measure lives on the affine support
of `μ`, the affine span `μ(x₀) + V` of its image. If the differential of a `C¹` map `μ : M → F`
maps onto the direction `V` of that affine span outside a null set, then the Duistermaat–Heckman
measure is absolutely continuous with respect to Lebesgue measure on `μ(x₀) + V`, the image of an
additive Haar measure on `V` under `v ↦ μ(x₀) + v`
(`TauCeti.SmoothTwoForm.duistermaatHeckmanMeasure_absolutelyContinuous_map_add`): read in `V`
after a continuous linear projection, `μ` has a null set of critical points. For a moment map, `V`
is the annihilator of the kernel `𝔨 = {ξ | ξ_M = 0}` of the infinitesimal action
(`TauCeti.SmoothTwoForm.IsMomentMap.vectorSpan_range`) and the image of `dμ_x` is the annihilator
of `𝔤_x`, so `dμ_x` maps onto `V` wherever `𝔤_x = 𝔨`. For a compact commutative Lie group this
holds outside a null set (`TauCeti.Lie.isNullSet_setOf_isotropy_ne_ker`). Hence **the
Duistermaat–Heckman measure of any Hamiltonian torus action on a connected symplectic manifold is
absolutely continuous with respect to Lebesgue measure on its affine support**
(`TauCeti.SmoothTwoForm.IsMomentMap.duistermaatHeckmanMeasure_absolutelyContinuous_map_add`). For
the trivial action `V = 0`, and this is the point mass above.

## Main results

* `TauCeti.SmoothTwoForm.duistermaatHeckmanMeasure_absolutelyContinuous`: a map whose critical
  points form a null set has absolutely continuous Duistermaat–Heckman measure.
* `TauCeti.SmoothTwoForm.duistermaatHeckmanMeasure_absolutelyContinuous_map_add`: a map whose
  differential maps onto the direction of the affine span of its image outside a null set has
  Duistermaat–Heckman measure absolutely continuous with respect to Lebesgue measure on that
  affine span.
* `TauCeti.SmoothTwoForm.IsMomentMap.duistermaatHeckmanMeasure_absolutelyContinuous`: the
  Duistermaat–Heckman measure of an effective action of a compact commutative Lie group on a
  connected manifold with a nondegenerate two-form is absolutely continuous.
* `TauCeti.SmoothTwoForm.IsMomentMap.duistermaatHeckmanMeasure_absolutelyContinuous_map_add`: for
  an action of a compact commutative Lie group that need not be effective, the Duistermaat–Heckman
  measure is absolutely continuous with respect to Lebesgue measure on the affine support of the
  moment map.

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

/-- **The Duistermaat–Heckman measure on the affine support.** Let `μ : M → F` be a `C¹` map to a
finite-dimensional real vector space, and let `V` be the direction of the affine span of its image,
so that `μ` takes values in the affine subspace `μ(x₀) + V` for every `x₀`. If the points where the
differential of `μ` does not map onto `V` form a null set, then `μ_* |σⁿ / n!|` is absolutely
continuous with respect to Lebesgue measure on `μ(x₀) + V`: the image of any additive Haar measure
on `V` under `v ↦ μ(x₀) + v`. -/
theorem duistermaatHeckmanMeasure_absolutelyContinuous_map_add [LindelofSpace M] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] {μ : M → F} (hμ : ContMDiff I 𝓘(ℝ, F) 1 μ)
    (hcrit : IsNullSet I {x | ¬ vectorSpan ℝ (range μ) ≤
      LinearMap.range (mfderiv I 𝓘(ℝ, F) μ x : E →L[ℝ] F).toLinearMap})
    (x₀ : M) (ν : Measure (vectorSpan ℝ (range μ))) [ν.IsAddHaarMeasure] :
    σ.duistermaatHeckmanMeasure n μ ≪ ν.map fun v ↦ μ x₀ + ↑v := by
  -- Write `μ = g ∘ f` for the `C¹` map `f = q ∘ μ` to `V`, where `q` is a continuous projection
  -- onto `V`, and the translation `g v = μ(x₀) + (v - q(μ(x₀)))` back into `F`.
  obtain ⟨p, hp⟩ := Submodule.ClosedComplemented.of_finiteDimensional (vectorSpan ℝ (range μ))
  let q : F →L[ℝ] vectorSpan ℝ (range μ) := p
  have hf : ContMDiff I 𝓘(ℝ, vectorSpan ℝ (range μ)) 1 (q ∘ μ) := q.contDiff.comp_contMDiff hμ
  let g := (fun v : vectorSpan ℝ (range μ) ↦ μ x₀ + ↑v) ∘ (· + -q (μ x₀))
  have hμf : μ = g ∘ (q ∘ μ) := funext fun x ↦ by
    have hmem : μ x - μ x₀ ∈ vectorSpan ℝ (range μ) :=
      vsub_mem_vectorSpan ℝ (mem_range_self x) (mem_range_self x₀)
    have hx : q (μ x) + -q (μ x₀) = ⟨μ x - μ x₀, hmem⟩ := by
      rw [← map_neg, ← map_add, ← sub_eq_add_neg]
      exact hp ⟨μ x - μ x₀, hmem⟩
    simp only [g, Function.comp_apply, hx, add_sub_cancel]
  have hmeas : Measurable fun v : vectorSpan ℝ (range μ) ↦ μ x₀ + ↑v :=
    (continuous_const.add continuous_subtypeVal).measurable
  have hg : Measurable g := hmeas.comp (measurable_add_const _)
  have hν : ν.map g = ν.map fun v ↦ μ x₀ + ↑v := by
    rw [← Measure.map_map hmeas (measurable_add_const _), map_add_right_eq_self]
  rw [(congrArg (σ.duistermaatHeckmanMeasure n) hμf).trans
    (duistermaatHeckmanMeasure_comp hg hf.continuous.measurable), ← hν]
  refine (duistermaatHeckmanMeasure_absolutelyContinuous hf (hcrit.mono fun x hx hV ↦ hx ?_)
    ν).map hg
  -- Where the differential of `μ` maps onto `V`, that of `q ∘ μ` is surjective.
  have hd := (q.hasMFDerivAt.comp x (hμ.mdifferentiableAt one_ne_zero).hasMFDerivAt).mfderiv
  intro v
  obtain ⟨w, hw⟩ := hV v.property
  refine ⟨w, ?_⟩
  rw [hd]
  exact (congrArg q hw).trans (hp v)

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

/-- **The Duistermaat–Heckman measure of a torus action is absolutely continuous on its affine
support.** Let a compact commutative Lie group `G`, such as a torus, act smoothly, not necessarily
effectively, on a connected Hausdorff σ-compact manifold `M` without boundary, with a
nondegenerate two-form `σ` and moment map `μ`, read in the continuous dual `𝔤*`. Let `V` be the
direction of the affine span of the image of `μ`, the annihilator of the kernel
`𝔨 = {ξ | ξ_M = 0}` of the infinitesimal action
(`TauCeti.SmoothTwoForm.IsMomentMap.vectorSpan_range`), so that `μ` takes values in the affine
subspace `μ(x₀) + V` for every `x₀`. Then the Duistermaat–Heckman measure `μ_* |σⁿ / n!|` is
absolutely continuous with respect to Lebesgue measure on this affine support: the image of any
additive Haar measure on `V` under `v ↦ μ(x₀) + v`. -/
theorem duistermaatHeckmanMeasure_absolutelyContinuous_map_add [T2Space M] [SigmaCompactSpace M]
    [PreconnectedSpace M] [CompactSpace G] [IsMulCommutative G]
    [MeasurableSpace (StrongDual ℝ EG)] [BorelSpace (StrongDual ℝ EG)]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental IG G I M) μ) (hσ : σ.IsNondegenerate)
    (x₀ : M) (ν : Measure (vectorSpan ℝ
      (range fun x ↦ (LinearMap.toContinuousLinearMap (μ x) : StrongDual ℝ EG))))
    [ν.IsAddHaarMeasure] :
    σ.duistermaatHeckmanMeasure n
        (fun x ↦ (LinearMap.toContinuousLinearMap (μ x) : StrongDual ℝ EG)) ≪
      ν.map fun v ↦ (LinearMap.toContinuousLinearMap (μ x₀) : StrongDual ℝ EG) + ↑v := by
  have : CompleteSpace EG := FiniteDimensional.completeSpace ℝ EG
  refine SmoothTwoForm.duistermaatHeckmanMeasure_absolutelyContinuous_map_add
    (h.contMDiff_toContinuousLinearMap.of_le (by simp))
    ((Lie.isNullSet_setOf_isotropy_ne_ker (I := IG) (G := G)).mono fun x hx hiso ↦ hx ?_) x₀ ν
  -- Where `𝔤_x = 𝔨`, the image `𝔤_x⁰` of the differential `dμ_x` is the annihilator of `𝔨`, the
  -- direction of the affine span of the image of `μ`.
  rw [vectorSpan_def]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨y, rfl⟩, _, ⟨z, rfl⟩, rfl⟩
  have hyz : μ y - μ z ∈ LinearMap.range (h.differential x) := by
    rw [h.range_differential (hσ.nondegenerate_bilinFormAt x), hiso, ← h.vectorSpan_range hσ]
    exact vsub_mem_vectorSpan ℝ (mem_range_self y) (mem_range_self z)
  obtain ⟨w, hw⟩ := hyz
  exact ⟨w, (h.mfderiv_toContinuousLinearMap_apply x w).trans
    (by rw [hw, map_sub]; exact (vsub_eq_sub _ _).symm)⟩

end IsMomentMap

end TauCeti.SmoothTwoForm
