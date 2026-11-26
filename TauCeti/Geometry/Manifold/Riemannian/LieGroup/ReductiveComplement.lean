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
`π : G → G ⧸ K` and base point `o = [1]`. A *reductive complement* is a subspace `𝔪` of the Lie
algebra `T_1 G` complementary to the kernel `𝔨 = ker dπ_1` and stable under `Ad(K)`. The
differential `dπ_1` restricts to a linear equivalence `𝔪 ≃ T_o(G ⧸ K)`, which is equivariant
for `Ad(K)` on `𝔪` and the isotropy action `k ↦ d(k •)_o` of `K` on `T_o(G ⧸ K)`.

Consequently an `Ad(K)`-invariant inner product on `𝔪` transports to an isotropy-invariant inner
product on `T_o(G ⧸ K)`, and so (`Subgroup.homogeneousMetric`) to a `G`-invariant Riemannian
metric on `G ⧸ K`. Conversely, every isotropy-invariant form on `T_o(G ⧸ K)` arises this way
from the `Ad(K)`-invariant form it induces on `𝔪`. For `𝔪 = 𝔨^⊥` and the inner product of a
Riemannian metric on `G` this is the horizontal inner product `Subgroup.horizontalInnerOne`.

Here a form on `𝔪` is given as a continuous bilinear form `b` on `T_1 G` whose symmetry,
positivity and `Ad(K)`-invariance are only required on `𝔪`.

## Main definitions

* `Subgroup.complementEquivOne`: `dπ_1` on a complement `𝔪` of its kernel, as a linear
  equivalence onto `T_o(G ⧸ K)`.
* `Subgroup.complementLiftOne`: its inverse, followed by the inclusion of `𝔪` into `T_1 G`.
* `Subgroup.complementForm`: the form on `T_o(G ⧸ K)` transported from a form on `𝔪`.
* `Subgroup.reductiveHomogeneousMetric`: the `G`-invariant metric on `G ⧸ K` of an
  `Ad(K)`-invariant inner product on a reductive complement.

## Main results

* `Subgroup.complementLiftOne_mfderiv_smul`: for an `Ad(K)`-stable complement, the lift
  intertwines the isotropy action with `Ad(K)`.
* `Subgroup.reductiveHomogeneousMetric_inner_mfderiv_quotientMk`: at the base point, the metric
  pairs `dπ_1 a` and `dπ_1 c` to `b a c` for `a, c ∈ 𝔪`.
* `Subgroup.complementForm_comp_mfderiv_quotientMk`: every form on `T_o(G ⧸ K)` is the transport
  of its pullback along `dπ_1`, and `Subgroup.eq_reductiveHomogeneousMetric`: every `G`-invariant
  metric on `G ⧸ K` is the metric of an `Ad(K)`-invariant inner product on `𝔪`.
* `Subgroup.complementLiftOne_orthogonal`: for `𝔪 = 𝔨^⊥` the lift is the horizontal lift.
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

section Lift

variable (I K) in
/-- **A complement of `𝔨` is `T_o(G ⧸ K)`.** The restriction of `dπ_1` to a complement `𝔪` of
its kernel `𝔨`, as a linear equivalence onto `T_o(G ⧸ K)`: Mathlib's
`LinearMap.kerComplementEquivRange` for `𝔪`, with the range identified with `T_o(G ⧸ K)` because
`dπ_1` is surjective. -/
def complementEquivOne
    (h𝔪 : letI := quotientChartedSpaceOfIsClosed I hK
      IsCompl 𝔪 (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1).ker) :
    letI := quotientChartedSpaceOfIsClosed I hK
    𝔪 ≃ₗ[ℝ] TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) :=
  letI := quotientChartedSpaceOfIsClosed I hK
  ((mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K)
      1).toLinearMap.kerComplementEquivRange h𝔪).trans
    (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2
      ((isSubmersion_quotientMk (I := I) hK).surjective_mfderiv (by simp) 1)))

variable {hK}
variable {h𝔪 : letI := quotientChartedSpaceOfIsClosed I hK
  IsCompl 𝔪 (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1).ker}

/-- The equivalence `𝔪 ≃ T_o(G ⧸ K)` is `dπ_1` on `𝔪`. -/
@[simp]
theorem complementEquivOne_apply :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ a, complementEquivOne I K hK h𝔪 a =
      mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1
        (a : TangentSpace I (1 : G)) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro a
  rw [complementEquivOne, LinearEquiv.trans_apply, LinearEquiv.ofTop_apply,
    LinearMap.kerComplementEquivRange_apply_coe, ContinuousLinearMap.coe_coe]

variable (I K hK h𝔪) in
/-- **The lift through a complement.** The inverse of the restriction of `dπ_1` to a complement
`𝔪` of its kernel, followed by the inclusion of `𝔪` into `T_1 G`. -/
def complementLiftOne :
    letI := quotientChartedSpaceOfIsClosed I hK
    TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ] TangentSpace I (1 : G) :=
  letI := quotientChartedSpaceOfIsClosed I hK
  LinearMap.toContinuousLinearMap (𝔪.subtype ∘ₗ (complementEquivOne I K hK h𝔪).symm.toLinearMap)

/-- The lift through `𝔪` is the inverse of `complementEquivOne`, as a vector of `T_1 G`. -/
theorem complementLiftOne_apply :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K),
      complementLiftOne I K hK h𝔪 u =
        ((complementEquivOne I K hK h𝔪).symm u : TangentSpace I (1 : G)) :=
  fun _ ↦ (rfl)

/-- The lift through `𝔪` takes values in `𝔪`. -/
theorem complementLiftOne_mem :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K),
      complementLiftOne I K hK h𝔪 u ∈ 𝔪 :=
  fun _ ↦ Subtype.property _

/-- The lift through `𝔪` is a right inverse of `dπ_1`. -/
@[simp]
theorem mfderiv_quotientMk_complementLiftOne :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K),
      mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1
        (complementLiftOne I K hK h𝔪 u) = u := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro u
  rw [complementLiftOne_apply, ← complementEquivOne_apply (h𝔪 := h𝔪),
    LinearEquiv.apply_symm_apply]

/-- A vector of `𝔪` is the lift of its image under `dπ_1`. -/
theorem complementLiftOne_mfderiv_quotientMk {a : TangentSpace I (1 : G)} (ha : a ∈ 𝔪) :
    letI := quotientChartedSpaceOfIsClosed I hK
    complementLiftOne I K hK h𝔪
      (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 a) = a := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  rw [complementLiftOne_apply]
  refine congrArg Subtype.val (?_ : _ = Subtype.mk a ha)
  rw [LinearEquiv.symm_apply_eq, complementEquivOne_apply]

/-- **Equivariance of the lift through a reductive complement.** If `𝔪` is `Ad(K)`-stable, then for
`k ∈ K` the lift of the isotropy translate `d(k •)_o u` is `Ad_k` applied to the lift of `u`. -/
theorem complementLiftOne_mfderiv_smul
    (hAd : ∀ k ∈ K, ∀ a ∈ 𝔪, Lie.adjointContinuousLinearMap (I := I) k a ∈ 𝔪)
    {k : G} (hk : k ∈ K) :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u, complementLiftOne I K hK h𝔪
      (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
        (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) u) =
      (Lie.adjointContinuousLinearMap (I := I) k :
          TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G)) (complementLiftOne I K hK h𝔪 u) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro u
  have h := mfderiv_smul_mfderiv_quotientMk_one hK hk (complementLiftOne I K hK h𝔪 u)
  rw [mfderiv_quotientMk_complementLiftOne] at h
  rw [h]
  exact complementLiftOne_mfderiv_quotientMk (hAd k hk _ (complementLiftOne_mem u))

end Lift

section Form

variable {hK}
variable {h𝔪 : letI := quotientChartedSpaceOfIsClosed I hK
  IsCompl 𝔪 (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1).ker}

variable (I K hK h𝔪) in
/-- **The form on `T_o(G ⧸ K)` transported from `𝔪`.** For a bilinear form `b` on `T_1 G`, the
form `(u, v) ↦ b (ℓ u) (ℓ v)` on `T_o(G ⧸ K)`, where `ℓ` is the lift through the complement `𝔪`
(`Subgroup.complementLiftOne`). Only the restriction of `b` to `𝔪` matters. -/
def complementForm (b : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G) →L[ℝ] ℝ) :
    letI := quotientChartedSpaceOfIsClosed I hK
    TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ]
      TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ] ℝ :=
  letI := quotientChartedSpaceOfIsClosed I hK
  (ContinuousLinearMap.precomp ℝ (complementLiftOne I K hK h𝔪)).comp
    (b.comp (complementLiftOne I K hK h𝔪))

variable {b : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G) →L[ℝ] ℝ}

/-- The transported form evaluates `b` on the lifts through `𝔪`. -/
@[simp]
theorem complementForm_apply :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u v : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K),
      complementForm I K hK h𝔪 b u v =
        b (complementLiftOne I K hK h𝔪 u) (complementLiftOne I K hK h𝔪 v) :=
  fun _ _ ↦ rfl

/-- The transported form pairs `dπ_1 a` and `dπ_1 c` to `b a c` for `a, c ∈ 𝔪`. -/
theorem complementForm_mfderiv_quotientMk {a c : TangentSpace I (1 : G)} (ha : a ∈ 𝔪)
    (hc : c ∈ 𝔪) :
    letI := quotientChartedSpaceOfIsClosed I hK
    complementForm I K hK h𝔪 b
        (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 a)
        (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 c) =
      b a c := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  rw [complementForm_apply, complementLiftOne_mfderiv_quotientMk ha,
    complementLiftOne_mfderiv_quotientMk hc]

/-- The transported form is symmetric if `b` is symmetric on `𝔪`. -/
theorem complementForm_comm (hsymm : ∀ a ∈ 𝔪, ∀ c ∈ 𝔪, b a c = b c a) :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u v : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K),
      complementForm I K hK h𝔪 b u v = complementForm I K hK h𝔪 b v u := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro u v
  exact hsymm _ (complementLiftOne_mem u) _ (complementLiftOne_mem v)

/-- The transported form is positive definite if `b` is positive definite on `𝔪`. -/
theorem complementForm_pos (hpos : ∀ a ∈ 𝔪, a ≠ 0 → 0 < b a a) :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K),
      u ≠ 0 → 0 < complementForm I K hK h𝔪 b u u := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro u hu
  refine hpos _ (complementLiftOne_mem u) fun h ↦ hu ?_
  have h' : complementLiftOne I K hK h𝔪 u = 0 := h
  rw [← mfderiv_quotientMk_complementLiftOne (h𝔪 := h𝔪) u, h', map_zero]

/-- **Isotropy invariance of the transported form.** If `𝔪` and the restriction of `b` to `𝔪`
are `Ad(K)`-invariant, the transported form on `T_o(G ⧸ K)` is invariant under the isotropy
action of `K`. -/
theorem complementForm_mfderiv_smul
    (hAd : ∀ k ∈ K, ∀ a ∈ 𝔪, Lie.adjointContinuousLinearMap (I := I) k a ∈ 𝔪)
    (hb : ∀ k ∈ K, ∀ a ∈ 𝔪, ∀ c ∈ 𝔪,
      b (Lie.adjointContinuousLinearMap (I := I) k a)
        (Lie.adjointContinuousLinearMap (I := I) k c) = b a c) :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ k ∈ K, ∀ u v, complementForm I K hK h𝔪 b
        (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) u)
        (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) v) = complementForm I K hK h𝔪 b u v := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro k hk u v
  -- The arguments on the left live in the fibre at `k • o`, the fibre at `o` only up to defeq.
  change b (complementLiftOne I K hK h𝔪 _) (complementLiftOne I K hK h𝔪 _) =
    b (complementLiftOne I K hK h𝔪 u) (complementLiftOne I K hK h𝔪 v)
  rw [complementLiftOne_mfderiv_smul hAd hk, complementLiftOne_mfderiv_smul hAd hk]
  exact hb k hk _ (complementLiftOne_mem u) _ (complementLiftOne_mem v)

/-- **Every form on `T_o(G ⧸ K)` comes from `𝔪`.** A bilinear form `β` on `T_o(G ⧸ K)` is the
transport of its pullback `(a, c) ↦ β (dπ_1 a) (dπ_1 c)` along `dπ_1`, for any complement `𝔪`. -/
theorem complementForm_comp_mfderiv_quotientMk
    (β : letI := quotientChartedSpaceOfIsClosed I hK
      TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ]
        TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ] ℝ) :
    letI := quotientChartedSpaceOfIsClosed I hK
    complementForm I K hK h𝔪 ((ContinuousLinearMap.precomp ℝ
      (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1)).comp
        (β.comp (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1))) =
      β := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  ext u v
  simp only [complementForm_apply, ContinuousLinearMap.coe_comp, comp_apply,
    ContinuousLinearMap.precomp_apply, mfderiv_quotientMk_complementLiftOne]

/-- The pullback along `dπ_1` of an isotropy-invariant form on `T_o(G ⧸ K)` is `Ad(K)`-invariant
on all of `T_1 G`. -/
theorem mfderiv_quotientMk_adjoint_of_mfderiv_smul
    {β : letI := quotientChartedSpaceOfIsClosed I hK
      TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ]
        TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ] ℝ}
    (hβ : letI := quotientChartedSpaceOfIsClosed I hK
      ∀ k ∈ K, ∀ u v, β (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) u)
          (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) v) = β u v)
    {k : G} (hk : k ∈ K) (a c : TangentSpace I (1 : G)) :
    letI := quotientChartedSpaceOfIsClosed I hK
    β (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1
        (Lie.adjointContinuousLinearMap (I := I) k a))
      (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1
        (Lie.adjointContinuousLinearMap (I := I) k c)) =
    β (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 a)
      (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 c) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  rw [← mfderiv_smul_mfderiv_quotientMk_one hK hk, ← mfderiv_smul_mfderiv_quotientMk_one hK hk]
  exact hβ k hk _ _

end Form

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

/-- **Every `G`-invariant metric comes from a reductive complement.** For any complement `𝔪` of
`𝔨`, a Riemannian metric on `G ⧸ K` for which `G` acts by isometries is the homogeneous metric of
the form `(a, c) ↦ ⟪dπ_1 a, dπ_1 c⟫_o` on `𝔪`. That form is symmetric and positive definite on `𝔪`
and `Ad(K)`-invariant on `T_1 G` (`Subgroup.mfderiv_quotientMk_adjoint_of_mfderiv_smul`); when `𝔪`
is `Ad(K)`-stable this exhibits the metric as `Subgroup.reductiveHomogeneousMetric`. -/
theorem eq_reductiveHomogeneousMetric
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
      ∀ a c : TangentSpace I (1 : G),
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
  rw [complementForm_apply, ← hmb, mfderiv_quotientMk_complementLiftOne,
    mfderiv_quotientMk_complementLiftOne]

end Metric

section Horizontal

variable {hK}
variable [RiemannianBundle (fun g : G ↦ TangentSpace I g)]

/-- **The orthogonal complement.** For `𝔪 = 𝔨^⊥`, the lift through `𝔪` is the horizontal lift
`Subgroup.horizontalLiftOne`. -/
theorem complementLiftOne_orthogonal :
    letI := quotientChartedSpaceOfIsClosed I hK
    complementLiftOne I K hK (mfderiv I 𝓘(ℝ, QuotientModelSpace I K)
        (QuotientGroup.mk : G → G ⧸ K) 1).ker.isCompl_orthogonal.symm =
      horizontalLiftOne I K hK := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  ext u
  conv_rhs => rw [← mfderiv_quotientMk_complementLiftOne (h𝔪 := (mfderiv I
    𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1).ker.isCompl_orthogonal.symm) u]
  exact (horizontalLiftOne_mfderiv_quotientMk hK (complementLiftOne_mem u)).symm

/-- For `𝔪 = 𝔨^⊥` and the inner product at the identity, the transported form is the horizontal
inner product `Subgroup.horizontalInnerOne`. -/
theorem complementForm_orthogonal_innerSL :
    letI := quotientChartedSpaceOfIsClosed I hK
    complementForm I K hK (mfderiv I 𝓘(ℝ, QuotientModelSpace I K)
        (QuotientGroup.mk : G → G ⧸ K) 1).ker.isCompl_orthogonal.symm
        (innerSL ℝ : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G) →L[ℝ] ℝ) =
      horizontalInnerOne I K hK := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  ext u v
  rw [complementForm_apply, horizontalInnerOne_apply, complementLiftOne_orthogonal,
    innerSL_apply_apply]

end Horizontal

end Subgroup
