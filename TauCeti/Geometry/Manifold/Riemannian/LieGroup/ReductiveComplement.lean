/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.LieGroup.HomogeneousSpace

/-!
# Homogeneous metrics from a reductive complement

Let `K` be a closed subgroup of a finite-dimensional Lie group `G`, with projection
`π : G → G ⧸ K` and base point `o = [1]`, and let `𝔪` be a reductive complement: a subspace of
`T_1 G` complementary to `𝔨 = ker dπ_1` and stable under `Ad(K)`. Through
`dπ_1 : 𝔪 ≃ T_o(G ⧸ K)` (`Subgroup.complementEquivOne`), an `Ad(K)`-invariant inner product on
`𝔪` transports to an isotropy-invariant inner product on `T_o(G ⧸ K)`
(`Subgroup.complementForm`), and so (`Subgroup.homogeneousMetric`) to a `G`-invariant Riemannian
metric on `G ⧸ K`. Conversely, given a reductive complement `𝔪`, every `G`-invariant metric on
`G ⧸ K` is the metric of the `Ad(K)`-invariant inner product it induces on `𝔪`. For `𝔪 = 𝔨^⊥` and
the inner product of a Riemannian metric on `G` this is the metric of the horizontal inner product
`Subgroup.horizontalInnerOne`
(`Subgroup.reductiveHomogeneousMetric_orthogonal_eq_homogeneousMetric`).

## Main definitions

* `Subgroup.reductiveHomogeneousMetric`: the `G`-invariant metric on `G ⧸ K` of an
  `Ad(K)`-invariant inner product on a reductive complement.

## Main results

* `Subgroup.reductiveHomogeneousMetric_inner_mfderiv_quotientMk`: at the base point, the metric
  pairs `dπ_1 a` and `dπ_1 c` to `b a c` for `a, c ∈ 𝔪`.
* `Subgroup.eq_reductiveHomogeneousMetric`: given a reductive complement `𝔪`, every `G`-invariant
  metric on `G ⧸ K` is the metric of the `Ad(K)`-invariant inner product it induces on `𝔪`.

## References

* J. Cheeger, D. G. Ebin, *Comparison Theorems in Riemannian Geometry*, North-Holland (1975),
  Chapter 3 (homogeneous spaces and reductive complements).
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Chapter 7 (homogeneous Riemannian
  manifolds and reductive homogeneous spaces).
-/

public section

open Bundle Function Manifold Set TauCeti
open scoped ContDiff Manifold Topology

noncomputable section

namespace Subgroup

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {K : Subgroup G} (hK : IsClosed (K : Set G)) {𝔪 : Submodule ℝ (TangentSpace I (1 : G))}

section Metric

variable {hK}
variable {h𝔪 : letI := quotientChartedSpaceOfIsClosed I hK
  IsCompl 𝔪 (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1).ker}
variable {b : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G) →L[ℝ] ℝ}

variable (hK h𝔪) in
/-- **The homogeneous metric of a reductive complement.** For an `Ad(K)`-stable complement `𝔪` of
`𝔨 = ker dπ_1` and a bilinear form `b` on `T_1 G` that is symmetric, positive definite and
`Ad(K)`-invariant on `𝔪`, the `G`-invariant Riemannian metric on `G ⧸ K` whose inner product at the
base point is `b` transported along `dπ_1 : 𝔪 ≃ T_o(G ⧸ K)`. -/
def reductiveHomogeneousMetric (hsymm : ∀ a ∈ 𝔪, ∀ c ∈ 𝔪, b a c = b c a)
    (hpos : ∀ a ∈ 𝔪, a ≠ 0 → 0 < b a a)
    (hAd : ∀ k ∈ K, ∀ a ∈ 𝔪, Lie.adjointContinuousLinearMap (I := I) k a ∈ 𝔪)
    (hb : ∀ k ∈ K, ∀ a ∈ 𝔪, ∀ c ∈ 𝔪,
      b (Lie.adjointContinuousLinearMap (I := I) k a)
        (Lie.adjointContinuousLinearMap (I := I) k c) = b a c) :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    ContMDiffRiemannianMetric 𝓘(ℝ, QuotientModelSpace I K) ∞ (QuotientModelSpace I K)
      (fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x) :=
  homogeneousMetric hK (complementForm_comm (h𝔪 := h𝔪) hsymm) (complementForm_pos hpos)
    (complementForm_mfderiv_smul hAd hb)

variable {hsymm : ∀ a ∈ 𝔪, ∀ c ∈ 𝔪, b a c = b c a} {hpos : ∀ a ∈ 𝔪, a ≠ 0 → 0 < b a a}
  {hAd : ∀ k ∈ K, ∀ a ∈ 𝔪, Lie.adjointContinuousLinearMap (I := I) k a ∈ 𝔪}
  {hb : ∀ k ∈ K, ∀ a ∈ 𝔪, ∀ c ∈ 𝔪,
      b (Lie.adjointContinuousLinearMap (I := I) k a)
        (Lie.adjointContinuousLinearMap (I := I) k c) = b a c}

/-- At the base point, the homogeneous metric of a reductive complement is the transported form. -/
@[simp]
theorem reductiveHomogeneousMetric_inner_one :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    (reductiveHomogeneousMetric hK h𝔪 hsymm hpos hAd hb).inner ((1 : G) : G ⧸ K) =
      complementForm I K hK h𝔪 b :=
  homogeneousMetric_inner_one

/-- **`dπ_1 : 𝔪 → T_o(G ⧸ K)` is an isometry.** At the base point the homogeneous metric of a
reductive complement pairs `dπ_1 a` and `dπ_1 c` to `b a c`, for `a, c ∈ 𝔪`. -/
theorem reductiveHomogeneousMetric_inner_mfderiv_quotientMk {a c : TangentSpace I (1 : G)}
    (ha : a ∈ 𝔪) (hc : c ∈ 𝔪) :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    (reductiveHomogeneousMetric hK h𝔪 hsymm hpos hAd hb).inner ((1 : G) : G ⧸ K)
        (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 a)
        (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 c) =
      b a c := by
  rw [reductiveHomogeneousMetric_inner_one]
  exact complementForm_mfderiv_quotientMk ha hc

/-- **`G` acts by isometries of the homogeneous metric of a reductive complement.** -/
theorem reductiveHomogeneousMetric_inner_mfderiv_smul (g : G) (x : G ⧸ K) :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    ∀ v w : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x,
    (reductiveHomogeneousMetric hK h𝔪 hsymm hpos hAd hb).inner (g • x)
        (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ g • y) x v)
        (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ g • y) x w) =
      (reductiveHomogeneousMetric hK h𝔪 hsymm hpos hAd hb).inner x v w :=
  homogeneousMetric_inner_mfderiv_smul g x

/-- The form `(a, c) ↦ ⟪dπ_1 a, dπ_1 c⟫_o` that a Riemannian metric on `G ⧸ K` induces on `T_1 G`
is positive definite on a complement `𝔪` of `𝔨 = ker dπ_1`. It is symmetric by
`ContMDiffRiemannianMetric.symm`, and `Ad(K)`-invariant when `G` acts by isometries
(`Subgroup.mfderiv_quotientMk_adjoint_of_mfderiv_smul`). -/
theorem inner_mfderiv_quotientMk_self_pos
    (m : letI := quotientChartedSpaceOfIsClosed I hK
      haveI := isManifold_quotientOfIsClosed (I := I) hK
      ContMDiffRiemannianMetric 𝓘(ℝ, QuotientModelSpace I K) ∞ (QuotientModelSpace I K)
        (fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x))
    (h𝔪 : letI := quotientChartedSpaceOfIsClosed I hK
      Disjoint 𝔪 (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1).ker) :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    ∀ a ∈ 𝔪, a ≠ 0 → 0 < m.inner ((1 : G) : G ⧸ K)
      (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 a)
      (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 a) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  have := isManifold_quotientOfIsClosed (I := I) hK
  intro a ha ha0
  exact m.pos _ _ fun h ↦ ha0 (Submodule.disjoint_def.1 h𝔪 a ha h)

variable (h𝔪) in
/-- **A `G`-invariant metric is the metric of a reductive complement.** Let `𝔪` be an
`Ad(K)`-stable complement of `𝔨`, and `b` a form on `T_1 G` that is symmetric, positive definite
and `Ad(K)`-invariant on `𝔪` and agrees on `𝔪` with the pullback `(a, c) ↦ ⟪dπ_1 a, dπ_1 c⟫_o` of
a Riemannian metric on `G ⧸ K` for which `G` acts by isometries. Then that metric is
`Subgroup.reductiveHomogeneousMetric` of `b`. The pullback itself satisfies these hypotheses
(`ContMDiffRiemannianMetric.symm`, `Subgroup.inner_mfderiv_quotientMk_self_pos` and
`Subgroup.mfderiv_quotientMk_adjoint_of_mfderiv_smul`). -/
theorem eq_reductiveHomogeneousMetric (hsymm : ∀ a ∈ 𝔪, ∀ c ∈ 𝔪, b a c = b c a)
    (hpos : ∀ a ∈ 𝔪, a ≠ 0 → 0 < b a a)
    (hAd : ∀ k ∈ K, ∀ a ∈ 𝔪, Lie.adjointContinuousLinearMap (I := I) k a ∈ 𝔪)
    (hb : ∀ k ∈ K, ∀ a ∈ 𝔪, ∀ c ∈ 𝔪,
      b (Lie.adjointContinuousLinearMap (I := I) k a)
        (Lie.adjointContinuousLinearMap (I := I) k c) = b a c)
    (m : letI := quotientChartedSpaceOfIsClosed I hK
      haveI := isManifold_quotientOfIsClosed (I := I) hK
      ContMDiffRiemannianMetric 𝓘(ℝ, QuotientModelSpace I K) ∞ (QuotientModelSpace I K)
        (fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x))
    (hm : letI := quotientChartedSpaceOfIsClosed I hK
      haveI := isManifold_quotientOfIsClosed (I := I) hK
      ∀ (g : G) (x : G ⧸ K) (v w : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x),
        m.inner (g • x)
          (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
            (fun y : G ⧸ K ↦ g • y) x v)
          (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
            (fun y : G ⧸ K ↦ g • y) x w) = m.inner x v w)
    (hmb : letI := quotientChartedSpaceOfIsClosed I hK
      haveI := isManifold_quotientOfIsClosed (I := I) hK
      ∀ a ∈ 𝔪, ∀ c ∈ 𝔪,
        m.inner ((1 : G) : G ⧸ K)
          (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 a)
          (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 c) =
        b a c) :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    m = reductiveHomogeneousMetric hK h𝔪 hsymm hpos hAd hb := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  have := isManifold_quotientOfIsClosed (I := I) hK
  refine eq_homogeneousMetric _ _ _ m hm ?_
  ext u v
  rw [complementForm_apply, ← hmb _ (complementLiftOne_mem u) _ (complementLiftOne_mem v),
    mfderiv_quotientMk_complementLiftOne, mfderiv_quotientMk_complementLiftOne]

variable [RiemannianBundle (fun g : G ↦ TangentSpace I g)]

/-- **The horizontal homogeneous metric is the metric of the reductive complement `𝔨^⊥`.** If the
inner product at the identity of `G` is `Ad(K)`-invariant, then the homogeneous metric of the
complement `𝔨^⊥` and the inner product at the identity is the homogeneous metric of the horizontal
inner product `Subgroup.horizontalInnerOne`. -/
theorem reductiveHomogeneousMetric_orthogonal_eq_homogeneousMetric
    (hAd : ∀ k ∈ K, ∀ a c : TangentSpace I (1 : G),
      inner ℝ (E := TangentSpace I (1 : G)) (Lie.adjointContinuousLinearMap (I := I) k a)
        (Lie.adjointContinuousLinearMap (I := I) k c) = inner ℝ a c) :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    reductiveHomogeneousMetric hK (mfderiv I 𝓘(ℝ, QuotientModelSpace I K)
        (QuotientGroup.mk : G → G ⧸ K) 1).ker.isCompl_orthogonal.symm
        (b := innerSL ℝ) (fun a _ c _ ↦ real_inner_comm c a)
        (fun _ _ ha ↦ real_inner_self_pos.2 ha)
        (adjointContinuousLinearMap_mem_orthogonal_ker_mfderiv_quotientMk hK hAd)
        (fun k hk a _ c _ ↦ hAd k hk a c) =
      homogeneousMetric hK (horizontalInnerOne_comm (I := I) hK)
        (horizontalInnerOne_pos (I := I) hK) (horizontalInnerOne_mfderiv_smul (I := I) hK hAd) :=
  eq_homogeneousMetric _ _ _ _ (reductiveHomogeneousMetric_inner_mfderiv_smul (I := I) (hK := hK))
    (reductiveHomogeneousMetric_inner_one.trans (horizontalInnerOne_eq_complementForm hK).symm)

end Metric

end Subgroup
