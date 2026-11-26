/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Quotient
public import TauCeti.Geometry.Manifold.Riemannian.Section
public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Homogeneous
public import TauCeti.Topology.Algebra.Group.Quotient.Basic
import TauCeti.GroupTheory.Coset.Basic
import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic

/-!
# Homogeneous and normal homogeneous metrics on `G ⧸ K`

Let `K` be a closed subgroup of a finite-dimensional Lie group `G`, so that the coset space
`G ⧸ K` is a smooth manifold (`Subgroup.quotientChartedSpaceOfIsClosed`) on which `G` acts
smoothly, with base point `o = [1]` and projection `π : G → G ⧸ K`.

A positive-definite symmetric bilinear form `β` on `T_o(G ⧸ K)` that is invariant under the
isotropy action `k ↦ d(k •)_o` of `K` extends to a unique `G`-invariant Riemannian metric on
`G ⧸ K`: at `x = g • o` the inner product evaluates `β` on the translates by `g⁻¹`, and invariance
under `K` makes this independent of the representative `g`. The metric is smooth because near
each point `g` can be chosen as a smooth local section of the submersion `π`. Classically, through
`dπ_1` restricted to an `Ad(K)`-stable complement `𝔪` of the Lie algebra `𝔨` of `K`, these forms
correspond to the `Ad(K)`-invariant inner products on `𝔪`; that correspondence is not formalized
here.

For a Riemannian metric on `G` whose inner product at the identity is `Ad(K)`-invariant, the
horizontal inner product at `o`, transported from `𝔪 = 𝔨^⊥` by the horizontal lift, is
isotropy-invariant. If the metric on `G` is moreover left-invariant, `π` is a Riemannian
submersion onto the resulting homogeneous metric. When the inner product at the identity is
`Ad(G)`-invariant, so that the left-invariant metric on `G` is bi-invariant, this is the *normal
homogeneous metric*.

## Main definitions

* `Subgroup.homogeneousMetric`: the `G`-invariant metric on `G ⧸ K` determined by an
  isotropy-invariant inner product on `T_o(G ⧸ K)`.
* `Subgroup.horizontalEquivOne`: `dπ_1` on `(ker dπ_1)^⊥` as a linear equivalence onto
  `T_o(G ⧸ K)` (through Mathlib's `LinearMap.kerComplementEquivRange` for that complement).
* `Subgroup.horizontalLiftOne`, `Subgroup.horizontalInnerOne`: the inverse of `dπ_1` on
  `(ker dπ_1)^⊥` and the inner product it induces on `T_o(G ⧸ K)`.
* `Subgroup.normalHomogeneousMetric`: the normal homogeneous metric of an `Ad(G)`-invariant inner
  product at the identity of `G`.

## Main results

* `Subgroup.homogeneousMetric_inner_mfderiv_smul`: `G` acts by isometries of the homogeneous
  metric, and `Subgroup.eq_homogeneousMetric`: every `G`-invariant metric is homogeneous.
* `Subgroup.horizontalInnerOne_mfderiv_smul`: the horizontal inner product is isotropy-invariant.
* `Subgroup.isRiemannianSubmersion_quotientMk_homogeneousMetric` and
  `Subgroup.isRiemannianSubmersion_quotientMk_normalHomogeneousMetric`: `G → G ⧸ K` is a
  Riemannian submersion.
* `Subgroup.completeSpace_ofRiemannianMetric_of_inner_mfderiv_smul`: every `G`-invariant metric on
  `G ⧸ K` is complete.

## References

* J. Cheeger, D. G. Ebin, *Comparison Theorems in Riemannian Geometry*, North-Holland (1975),
  Chapter 3 (homogeneous spaces and normal homogeneous metrics).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2 (homogeneous spaces and Riemannian submersions) and Chapter 6 (completeness).
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
  {K : Subgroup G}

section Metric

variable (hK : IsClosed (K : Set G))

variable (I K) in
/-- The pullback of a bilinear form `β` on the tangent space at the base point `o = [1]` of
`G ⧸ K` to the tangent space at `x`, along the translation by the inverse of the chosen
representative `x.out` of `x`. When `β` is invariant under the isotropy action of `K`, this does
not depend on the representative (`homogeneousBilinearForm_apply_of_mk_eq`), and it is the value at
`x` of the `G`-invariant extension of `β`. -/
def homogeneousBilinearForm
    (β : letI := quotientChartedSpaceOfIsClosed I hK
      TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ]
        TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ] ℝ)
    (x : G ⧸ K) :
    letI := quotientChartedSpaceOfIsClosed I hK
    TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x →L[ℝ]
      TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x →L[ℝ] ℝ :=
  letI := quotientChartedSpaceOfIsClosed I hK
  (ContinuousLinearMap.precomp ℝ (mfderiv 𝓘(ℝ, QuotientModelSpace I K)
    𝓘(ℝ, QuotientModelSpace I K) (fun y : G ⧸ K ↦ x.out⁻¹ • y) x)).comp
    (β.comp (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
      (fun y : G ⧸ K ↦ x.out⁻¹ • y) x))

variable {hK}
variable {β : letI := quotientChartedSpaceOfIsClosed I hK
      TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ]
        TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ] ℝ}

/-- `homogeneousBilinearForm` evaluates `β` on the translates to the base point by the inverse of
the chosen representative of `x`; for isotropy-invariant `β` this is the homogeneous extension. -/
@[simp]
theorem homogeneousBilinearForm_apply (x : G ⧸ K) :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ v w : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x,
    homogeneousBilinearForm I K hK β x v w =
      β (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ x.out⁻¹ • y) x v)
        (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ x.out⁻¹ • y) x w) :=
  fun _ _ ↦ rfl

/-- **Independence of the representative.** If `β` is invariant under the isotropy action of
`K` on the tangent space at `o`, then the homogeneous extension of `β` may be computed with any
representative `g` of `x`. -/
theorem homogeneousBilinearForm_apply_of_mk_eq
    (hβ : letI := quotientChartedSpaceOfIsClosed I hK
      ∀ k ∈ K, ∀ u v, β (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) u)
          (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) v) = β u v)
    {g : G} {x : G ⧸ K} (hg : (g : G ⧸ K) = x) :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ v w : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x,
    homogeneousBilinearForm I K hK β x v w =
      β (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ g⁻¹ • y) x v)
        (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ g⁻¹ • y) x w) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro v w
  -- Write `g = x.out * k` with `k ∈ K`; then `g⁻¹ • y = k⁻¹ • x.out⁻¹ • y`.
  have hk : x.out⁻¹ * g ∈ K := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', hg]
  have ho : x.out⁻¹ • x = ((1 : G) : G ⧸ K) := QuotientGroup.out_inv_smul x
  have hmul : (x.out⁻¹ * g)⁻¹ * x.out⁻¹ = g⁻¹ := by group
  have key := mfderiv_smul_quotient_comp (I := I) hK (x.out⁻¹ * g)⁻¹ x.out⁻¹ x ho hmul
  rw [homogeneousBilinearForm_apply, ← key, ← key]
  exact (hβ _ (K.inv_mem hk) _ _).symm

/-- **Smoothness of the homogeneous extension.** If `β` is invariant under the isotropy action of
`K`, then its `G`-invariant extension is a smooth section of the bundle of bilinear forms on the
tangent bundle of `G ⧸ K`. -/
theorem contMDiff_homogeneousBilinearForm
    (hβ : letI := quotientChartedSpaceOfIsClosed I hK
      ∀ k ∈ K, ∀ u v, β (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) u)
          (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) v) = β u v) :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    ContMDiff 𝓘(ℝ, QuotientModelSpace I K)
      (𝓘(ℝ, QuotientModelSpace I K).prod
        𝓘(ℝ, QuotientModelSpace I K →L[ℝ] QuotientModelSpace I K →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (QuotientModelSpace I K →L[ℝ] QuotientModelSpace I K →L[ℝ] ℝ)
        (E := fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x →L[ℝ]
          TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x →L[ℝ] ℝ) x
        (homogeneousBilinearForm I K hK β x)) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  have := isManifold_quotientOfIsClosed (I := I) hK
  have := contMDiffSMul_quotientOfIsClosed (I := I) hK
  intro x₀
  obtain ⟨U, hU, hx₀U, s, hs, hsec⟩ :=
    (isSubmersion_quotientMk (I := I) hK).exists_contMDiffOn_section_of_surjective
      QuotientGroup.mk_surjective x₀
  have hUn : U ∈ 𝓝 x₀ := hU.mem_nhds hx₀U
  have hpt : ∀ x ∈ U, (s x)⁻¹ • x = ((1 : G) : G ⧸ K) := fun x hx ↦
    QuotientGroup.inv_smul_of_mk_eq (hsec x hx)
  have hsmooth : ContMDiffAt (𝓘(ℝ, QuotientModelSpace I K).prod 𝓘(ℝ, QuotientModelSpace I K))
      𝓘(ℝ, QuotientModelSpace I K) ∞ (uncurry fun x y : G ⧸ K ↦ (s x)⁻¹ • y) (x₀, x₀) :=
    ContMDiffAt.smul (I := I) (f := fun p : (G ⧸ K) × (G ⧸ K) ↦ (s p.1)⁻¹) (g := Prod.snd)
      ((contMDiff_inv I ∞).contMDiffAt.comp (x₀, x₀)
        ((hs.contMDiffAt hUn).comp (x₀, x₀) contMDiffAt_fst))
      contMDiffAt_snd
  have hpull := contMDiffAt_bilinearForm_pullback_of_inTangentCoordinates
    (I := 𝓘(ℝ, QuotientModelSpace I K)) (J := 𝓘(ℝ, QuotientModelSpace I K)) (n := ∞)
    (f := fun x : G ⧸ K ↦ (s x)⁻¹ • x) (b := fun _ ↦ β)
    (L := fun x ↦ mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
      (fun y : G ⧸ K ↦ (s x)⁻¹ • y) x) (x₀ := x₀) ?_
    (ContMDiffAt.mfderiv (fun x y : G ⧸ K ↦ (s x)⁻¹ • y) id hsmooth contMDiffAt_id le_rfl)
  · refine hpull.congr_of_eventuallyEq ?_
    filter_upwards [hUn] with x hx
    congr 1
    ext v w
    exact homogeneousBilinearForm_apply_of_mk_eq hβ (hsec x hx) v w
  · refine (contMDiffAt_const (c := TotalSpace.mk'
      (QuotientModelSpace I K →L[ℝ] QuotientModelSpace I K →L[ℝ] ℝ)
        (E := fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x →L[ℝ]
          TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x →L[ℝ] ℝ) ((1 : G) : G ⧸ K)
          β)).congr_of_eventuallyEq ?_
    filter_upwards [hUn] with x hx
    -- The base points agree by `hpt`; the fibres of the bundle of bilinear forms are all the same
    -- model space, so the two forms are the same element of it and `HEq.rfl` closes the goal.
    exact TotalSpace.ext (hpt x hx) HEq.rfl

variable (hK) in
/-- **The `G`-invariant metric on `G ⧸ K` determined by an isotropy-invariant inner product.**
A positive-definite symmetric bilinear form `β` on the tangent space at the base point
`o = [1]`, invariant under the isotropy action `k ↦ d(k •)_o` of `K`, extends uniquely to a
`G`-invariant Riemannian metric on the homogeneous space: at `x`, the inner product evaluates `β`
on the translates to `o` by the inverse of any representative of `x`. -/
def homogeneousMetric (hsymm : ∀ u v, β u v = β v u) (hpos : ∀ u, u ≠ 0 → 0 < β u u)
    (hβ : letI := quotientChartedSpaceOfIsClosed I hK
      ∀ k ∈ K, ∀ u v, β (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) u)
          (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) v) = β u v) :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    ContMDiffRiemannianMetric 𝓘(ℝ, QuotientModelSpace I K) ∞ (QuotientModelSpace I K)
      (fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x) :=
  letI := quotientChartedSpaceOfIsClosed I hK
  haveI := isManifold_quotientOfIsClosed (I := I) hK
  ContMDiffRiemannianMetric.ofPositiveDefiniteSection
    ⟨homogeneousBilinearForm I K hK β, contMDiff_homogeneousBilinearForm hβ⟩
    ((TauCeti.Manifold.mem_positiveDefiniteBilinearSections _).2
      ⟨(TauCeti.Manifold.mem_symmetricBilinearSections _).2 fun _ _ _ ↦ hsymm _ _,
        fun x _ hv ↦ hpos _
          ((map_ne_zero_iff _ (injective_mfderiv_smul_quotient (I := I) hK _ x)).2 hv)⟩)

variable {hsymm : ∀ u v, β u v = β v u} {hpos : ∀ u, u ≠ 0 → 0 < β u u}
  {hβ : letI := quotientChartedSpaceOfIsClosed I hK
      ∀ k ∈ K, ∀ u v, β (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) u)
          (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) v) = β u v}

/-- The homogeneous metric is the homogeneous extension of `β`. -/
@[simp low]
theorem homogeneousMetric_inner (x : G ⧸ K) :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    ∀ v w : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x,
    (homogeneousMetric hK hsymm hpos hβ).inner x v w = homogeneousBilinearForm I K hK β x v w :=
  letI := quotientChartedSpaceOfIsClosed I hK
  haveI := isManifold_quotientOfIsClosed (I := I) hK
  fun v w ↦ ContMDiffRiemannianMetric.ofPositiveDefiniteSection_inner _ _ x v w

/-- The homogeneous metric evaluates `β` on the translates to the base point by the inverse of
any representative. -/
theorem homogeneousMetric_inner_of_mk_eq {g : G} {x : G ⧸ K} (hg : (g : G ⧸ K) = x) :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    ∀ v w : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x,
    (homogeneousMetric hK hsymm hpos hβ).inner x v w =
      β (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ g⁻¹ • y) x v)
        (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ g⁻¹ • y) x w) := fun v w ↦ by
  rw [homogeneousMetric_inner]
  exact homogeneousBilinearForm_apply_of_mk_eq hβ hg v w

/-- At the base point `o = [1]`, the homogeneous metric is `β`. -/
@[simp]
theorem homogeneousMetric_inner_one :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    (homogeneousMetric hK hsymm hpos hβ).inner ((1 : G) : G ⧸ K) = β := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  have := isManifold_quotientOfIsClosed (I := I) hK
  have hid : (fun y : G ⧸ K ↦ (1 : G)⁻¹ • y) = id := by
    funext y
    simp
  ext u v
  rw [homogeneousMetric_inner_of_mk_eq rfl, hid, mfderiv_id]
  -- `ContinuousLinearMap.id` applied to `u`, in the fibre at `(1 : G)⁻¹ • o`, is `u` in the fibre
  -- at `o`: the two fibres coincide only up to defeq, so `simp` cannot rewrite across them.
  rfl

/-- **`G` acts by isometries of the homogeneous metric.** -/
theorem homogeneousMetric_inner_mfderiv_smul (g : G) (x : G ⧸ K) :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    ∀ v w : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x,
    (homogeneousMetric hK hsymm hpos hβ).inner (g • x)
        (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ g • y) x v)
        (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ g • y) x w) =
      (homogeneousMetric hK hsymm hpos hβ).inner x v w := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  have := isManifold_quotientOfIsClosed (I := I) hK
  intro v w
  have hg : ((g * x.out : G) : G ⧸ K) = g • x := by
    rw [← smul_eq_mul, ← MulAction.Quotient.smul_coe, QuotientGroup.out_eq']
  have key := mfderiv_smul_quotient_comp (I := I) hK (g * x.out)⁻¹ g x (c := x.out⁻¹) rfl
    (by group)
  rw [homogeneousMetric_inner_of_mk_eq hg, key, key, homogeneousMetric_inner,
    homogeneousBilinearForm_apply]

variable (hsymm hpos hβ) in
/-- **Uniqueness of `G`-invariant metrics.** A Riemannian metric on `G ⧸ K` for which `G` acts by
isometries is the homogeneous metric of its value at the base point. -/
theorem eq_homogeneousMetric
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
    (hmβ : letI := quotientChartedSpaceOfIsClosed I hK
      haveI := isManifold_quotientOfIsClosed (I := I) hK
      m.inner ((1 : G) : G ⧸ K) = β) :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    m = homogeneousMetric hK hsymm hpos hβ := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  have := isManifold_quotientOfIsClosed (I := I) hK
  have hpt : ∀ (p : G ⧸ K), p = ((1 : G) : G ⧸ K) →
      ∀ a b : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) p,
        m.inner p a b = m.inner ((1 : G) : G ⧸ K) a b := by
    -- The vectors live in the fibre at `p`, which is the fibre at `o` only up to defeq; after
    -- `subst`, both sides are the same expression.
    rintro p rfl a b
    rfl
  ext x v w
  rw [← hm x.out⁻¹ x v w, hpt _ (QuotientGroup.out_inv_smul x), hmβ, homogeneousMetric_inner,
    homogeneousBilinearForm_apply]

end Metric

section Horizontal

variable (hK : IsClosed (K : Set G))


variable [RiemannianBundle (fun g : G ↦ TangentSpace I g)]

variable (I K) in
/-- **The horizontal space at the identity is `T_o(G ⧸ K)`.** The restriction of `dπ_1` to the
orthogonal complement `𝔪 = 𝔨^⊥` of its kernel `𝔨`, for the inner product at the identity, as a
linear equivalence onto `T_o(G ⧸ K)`. This is Mathlib's `LinearMap.kerComplementEquivRange` for the
complement `𝔨^⊥`, with the range identified with `T_o(G ⧸ K)` because `dπ_1` is surjective. -/
def horizontalEquivOne :
    letI := quotientChartedSpaceOfIsClosed I hK
    (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1).kerᗮ ≃ₗ[ℝ]
      TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) :=
  letI := quotientChartedSpaceOfIsClosed I hK
  ((mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K)
      1).toLinearMap.kerComplementEquivRange (mfderiv I 𝓘(ℝ, QuotientModelSpace I K)
        (QuotientGroup.mk : G → G ⧸ K) 1).ker.isCompl_orthogonal.symm).trans
    (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2
      ((isSubmersion_quotientMk (I := I) hK).surjective_mfderiv (by simp) 1)))

/-- The horizontal equivalence at the identity is `dπ_1` on horizontal vectors. -/
@[simp]
theorem horizontalEquivOne_apply :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ a, horizontalEquivOne I K hK a =
      mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1
        (a : TangentSpace I (1 : G)) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro a
  rw [horizontalEquivOne, LinearEquiv.trans_apply, LinearEquiv.ofTop_apply,
    LinearMap.kerComplementEquivRange_apply_coe, ContinuousLinearMap.coe_coe]

variable (I K) in
/-- **The horizontal lift at the identity.** The inverse of the restriction of `dπ_1` to the
orthogonal complement `𝔪 = 𝔨^⊥` of its kernel `𝔨`, where `π` is the projection `G → G ⧸ K`:
the inverse of `Subgroup.horizontalEquivOne` followed by the inclusion of `𝔨^⊥`. -/
def horizontalLiftOne :
    letI := quotientChartedSpaceOfIsClosed I hK
    TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ] TangentSpace I (1 : G) :=
  letI := quotientChartedSpaceOfIsClosed I hK
  LinearMap.toContinuousLinearMap ((mfderiv I 𝓘(ℝ, QuotientModelSpace I K)
    (QuotientGroup.mk : G → G ⧸ K) 1).kerᗮ.subtype ∘ₗ
      (horizontalEquivOne I K hK).symm.toLinearMap)

/-- The horizontal lift at the identity is the inverse of the horizontal equivalence, followed by
the inclusion of `𝔨^⊥`. -/
theorem horizontalLiftOne_apply :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K),
      horizontalLiftOne I K hK u = ((horizontalEquivOne I K hK).symm u : TangentSpace I (1 : G)) :=
  fun _ ↦ (rfl)

/-- The horizontal lift at the identity is horizontal. -/
theorem horizontalLiftOne_mem :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K),
      horizontalLiftOne I K hK u ∈ (mfderiv I 𝓘(ℝ, QuotientModelSpace I K)
      (QuotientGroup.mk : G → G ⧸ K) 1).kerᗮ := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro u
  exact Subtype.property _

/-- The horizontal lift at the identity is a right inverse of `dπ_1`. -/
@[simp]
theorem mfderiv_quotientMk_horizontalLiftOne :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K),
      mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1
        (horizontalLiftOne I K hK u) = u := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro u
  rw [horizontalLiftOne_apply, ← horizontalEquivOne_apply, LinearEquiv.apply_symm_apply]

/-- A horizontal vector at the identity is the horizontal lift of its image. -/
theorem horizontalLiftOne_mfderiv_quotientMk {a : TangentSpace I (1 : G)} :
    letI := quotientChartedSpaceOfIsClosed I hK
    a ∈ (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1).kerᗮ →
    horizontalLiftOne I K hK
      (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 a) = a := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro ha
  rw [horizontalLiftOne_apply]
  refine congrArg Subtype.val (?_ : _ = Subtype.mk a ha)
  rw [LinearEquiv.symm_apply_eq, horizontalEquivOne_apply]

variable (I K) in
/-- **The horizontal inner product at the base point.** The inner product on `T_o(G ⧸ K)` that
makes the horizontal lift at the identity an isometry onto `𝔪 = 𝔨^⊥`. -/
def horizontalInnerOne :
    letI := quotientChartedSpaceOfIsClosed I hK
    TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ]
      TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ] ℝ :=
  letI := quotientChartedSpaceOfIsClosed I hK
  (ContinuousLinearMap.precomp ℝ (horizontalLiftOne I K hK)).comp
    ((innerSL ℝ : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G) →L[ℝ] ℝ).comp
      (horizontalLiftOne I K hK))

/-- The horizontal inner product is the inner product at the identity of the horizontal lifts. -/
@[simp]
theorem horizontalInnerOne_apply :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u v : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K),
      horizontalInnerOne I K hK u v =
      inner ℝ (horizontalLiftOne I K hK u) (horizontalLiftOne I K hK v) :=
  fun _ _ ↦ rfl

/-- **Equivariance of the horizontal lift.** If the inner product at the identity of `G` is
invariant under `Ad(K)`, then for `k ∈ K` the horizontal lift of the isotropy translate
`d(k •)_o u` is `Ad_k` applied to the horizontal lift of `u`. -/
theorem horizontalLiftOne_mfderiv_smul
    (hAd : ∀ k ∈ K, ∀ a c : TangentSpace I (1 : G),
      inner ℝ (E := TangentSpace I (1 : G)) (Lie.adjointContinuousLinearMap (I := I) k a)
        (Lie.adjointContinuousLinearMap (I := I) k c) = inner ℝ a c) {k : G} (hk : k ∈ K) :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u, horizontalLiftOne I K hK
      (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
        (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) u) =
      (Lie.adjointContinuousLinearMap (I := I) k :
          TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G)) (horizontalLiftOne I K hK u) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  set D := mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1
  have hker : ∀ k ∈ K, ∀ w ∈ D.ker, Lie.adjointContinuousLinearMap (I := I) k w ∈ D.ker := by
    intro k hk w hw
    rw [LinearMap.mem_ker] at hw ⊢
    -- `dπ_1 (Ad_k w) = d(k •)_o (dπ_1 w) = d(k •)_o 0 = 0`.
    exact ((mfderiv_smul_mfderiv_quotientMk_one hK hk w).symm.trans
      (congrArg (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
        (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K)) hw)).trans (map_zero _)
  have hperp : ∀ a ∈ D.kerᗮ, (Lie.adjointContinuousLinearMap (I := I) k :
      TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G)) a ∈ D.kerᗮ := by
    intro a ha
    rw [Submodule.mem_orthogonal] at ha
    refine (Submodule.mem_orthogonal (E := TangentSpace I (1 : G)) D.ker _).2 fun w hw ↦ ?_
    rw [← Lie.adjointContinuousLinearMap_adjointContinuousLinearMap_inv k w, hAd k hk]
    exact ha _ (hker k⁻¹ (K.inv_mem hk) w hw)
  intro u
  have h := mfderiv_smul_mfderiv_quotientMk_one hK hk (horizontalLiftOne I K hK u)
  rw [mfderiv_quotientMk_horizontalLiftOne] at h
  rw [h]
  exact horizontalLiftOne_mfderiv_quotientMk hK (hperp _ (horizontalLiftOne_mem hK u))

/-- **Isotropy invariance of the horizontal inner product.** If the inner product at the identity
of `G` is invariant under `Ad(K)`, then the horizontal inner product at the base point of `G ⧸ K`
is invariant under the isotropy action of `K`. -/
theorem horizontalInnerOne_mfderiv_smul
    (hAd : ∀ k ∈ K, ∀ a c : TangentSpace I (1 : G),
      inner ℝ (E := TangentSpace I (1 : G)) (Lie.adjointContinuousLinearMap (I := I) k a)
        (Lie.adjointContinuousLinearMap (I := I) k c) = inner ℝ a c) :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ k ∈ K, ∀ u v, horizontalInnerOne I K hK
        (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) u)
        (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) v) = horizontalInnerOne I K hK u v := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro k hk u v
  -- `rw [horizontalInnerOne_apply]` does not apply on the left: the arguments there live in the
  -- fibre at `k • o`, which is the fibre at `o` only up to defeq.
  change inner ℝ (horizontalLiftOne I K hK _) (horizontalLiftOne I K hK _) =
    inner ℝ (horizontalLiftOne I K hK u) (horizontalLiftOne I K hK v)
  rw [horizontalLiftOne_mfderiv_smul hK hAd hk, horizontalLiftOne_mfderiv_smul hK hAd hk]
  exact hAd k hk _ _

/-- The horizontal inner product at the base point is symmetric. -/
theorem horizontalInnerOne_comm :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u v : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K),
      horizontalInnerOne I K hK u v = horizontalInnerOne I K hK v u := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro u v
  rw [horizontalInnerOne_apply, horizontalInnerOne_apply, real_inner_comm]

/-- The horizontal inner product at the base point is positive definite. -/
theorem horizontalInnerOne_pos :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K),
      u ≠ 0 → 0 < horizontalInnerOne I K hK u u := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro u hu
  rw [horizontalInnerOne_apply]
  refine real_inner_self_pos.2 fun h ↦ hu ?_
  rw [← mfderiv_quotientMk_horizontalLiftOne hK u, h, map_zero]

/-- **`G → G ⧸ K` is a Riemannian submersion.** Let `G` carry a left-invariant Riemannian metric
whose inner product at the identity is invariant under `Ad(K)`. Then the projection onto `G ⧸ K`
is a Riemannian submersion for the `G`-invariant metric `homogeneousMetric` of the horizontal inner
product at the base point. -/
theorem isRiemannianSubmersion_quotientMk_homogeneousMetric
    (hL : ∀ (x : G) (a c : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a x) (mulInvariantVectorField c x) =
        inner ℝ (E := TangentSpace I (1 : G)) a c)
    (hAd : ∀ k ∈ K, ∀ a c : TangentSpace I (1 : G),
      inner ℝ (E := TangentSpace I (1 : G)) (Lie.adjointContinuousLinearMap (I := I) k a)
        (Lie.adjointContinuousLinearMap (I := I) k c) = inner ℝ a c) :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    letI : RiemannianBundle (fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x) :=
      ⟨(homogeneousMetric hK (horizontalInnerOne_comm (I := I) hK)
        (horizontalInnerOne_pos (I := I) hK)
        (horizontalInnerOne_mfderiv_smul (I := I) hK hAd)).toRiemannianMetric⟩
    TauCeti.IsRiemannianSubmersion I 𝓘(ℝ, QuotientModelSpace I K)
      (QuotientGroup.mk : G → G ⧸ K) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  have := isManifold_quotientOfIsClosed (I := I) hK
  let _ : RiemannianBundle (fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x) :=
    ⟨(homogeneousMetric hK (horizontalInnerOne_comm (I := I) hK)
      (horizontalInnerOne_pos (I := I) hK)
      (horizontalInnerOne_mfderiv_smul (I := I) hK hAd)).toRiemannianMetric⟩
  refine ⟨isSubmersion_quotientMk hK, fun g v hv ↦ ?_⟩
  obtain ⟨a, rfl⟩ := exists_mulInvariantVectorField_eq v
  set D := mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1
  have key := mfderiv_smul_inv_mfderiv_quotientMk_mulInvariantVectorField (I := I) hK g
  -- `a` is horizontal at the identity.
  have ha : a ∈ D.kerᗮ := by
    refine (Submodule.mem_orthogonal (E := TangentSpace I (1 : G)) D.ker _).2 fun c hc ↦ ?_
    rw [← hL g]
    refine hv _ (LinearMap.mem_ker.2 ?_)
    refine injective_mfderiv_smul_quotient (I := I) hK g⁻¹ (g : G ⧸ K) ?_
    exact (key c).trans ((LinearMap.mem_ker.1 hc).trans (map_zero _).symm)
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, hL g]
  rw [Bundle.ContMDiffRiemannianMetric.inner_riemannianBundle,
    homogeneousMetric_inner_of_mk_eq rfl, key, horizontalInnerOne_apply,
    horizontalLiftOne_mfderiv_quotientMk hK ha]

/-- **The normal homogeneous metric on `G ⧸ K`.** For a Riemannian metric on `G` whose inner
product at the identity is `Ad(G)`-invariant, the `G`-invariant metric on `G ⧸ K` whose inner
product at the base point makes the horizontal lift an isometry onto `𝔪 = 𝔨^⊥`. Only the inner
product at the identity of `G` is used. -/
def normalHomogeneousMetric
    (hAd : ∀ (g : G) (a c : TangentSpace I (1 : G)),
      inner ℝ (E := TangentSpace I (1 : G)) (Lie.adjointContinuousLinearMap (I := I) g a)
        (Lie.adjointContinuousLinearMap (I := I) g c) = inner ℝ a c) :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    ContMDiffRiemannianMetric 𝓘(ℝ, QuotientModelSpace I K) ∞ (QuotientModelSpace I K)
      (fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x) :=
  homogeneousMetric hK (horizontalInnerOne_comm (I := I) hK) (horizontalInnerOne_pos (I := I) hK)
    (horizontalInnerOne_mfderiv_smul (I := I) hK fun k _ ↦ hAd k)

/-- The normal homogeneous metric is the homogeneous metric of the horizontal inner product. -/
theorem normalHomogeneousMetric_eq
    (hAd : ∀ (g : G) (a c : TangentSpace I (1 : G)),
      inner ℝ (E := TangentSpace I (1 : G)) (Lie.adjointContinuousLinearMap (I := I) g a)
        (Lie.adjointContinuousLinearMap (I := I) g c) = inner ℝ a c) :
    normalHomogeneousMetric hK hAd =
      homogeneousMetric hK (horizontalInnerOne_comm (I := I) hK)
        (horizontalInnerOne_pos (I := I) hK)
        (horizontalInnerOne_mfderiv_smul (I := I) hK fun k _ ↦ hAd k) :=
  (rfl)

/-- **For a bi-invariant metric on `G`, the projection `G → G ⧸ K` is a Riemannian submersion
onto the normal homogeneous metric.** -/
theorem isRiemannianSubmersion_quotientMk_normalHomogeneousMetric
    (hL : ∀ (x : G) (a c : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a x) (mulInvariantVectorField c x) =
        inner ℝ (E := TangentSpace I (1 : G)) a c)
    (hAd : ∀ (g : G) (a c : TangentSpace I (1 : G)),
      inner ℝ (E := TangentSpace I (1 : G)) (Lie.adjointContinuousLinearMap (I := I) g a)
        (Lie.adjointContinuousLinearMap (I := I) g c) = inner ℝ a c) :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    letI : RiemannianBundle (fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x) :=
      ⟨(normalHomogeneousMetric hK hAd).toRiemannianMetric⟩
    TauCeti.IsRiemannianSubmersion I 𝓘(ℝ, QuotientModelSpace I K)
      (QuotientGroup.mk : G → G ⧸ K) :=
  isRiemannianSubmersion_quotientMk_homogeneousMetric hK hL fun k _ ↦ hAd k

end Horizontal

section Completeness

variable (hK : IsClosed (K : Set G))

/-- **`G`-invariant metrics on `G ⧸ K` are complete.** For a continuous Riemannian metric on the
homogeneous space of a closed subgroup for which `G` acts by isometries, the Riemannian distance is
complete. -/
theorem completeSpace_ofRiemannianMetric_of_inner_mfderiv_smul :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    ∀ [RiemannianBundle (fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x)]
      [IsContinuousRiemannianBundle (QuotientModelSpace I K)
        (fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x)],
      (∀ (g : G) (x : G ⧸ K) (v w : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x),
        inner ℝ (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K) (g • ·) x v)
          (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K) (g • ·) x w) =
          inner ℝ v w) →
      letI : EMetricSpace (G ⧸ K) :=
        haveI := topologicalGroup_of_lieGroup I ∞ (G := G)
        haveI : IsClosed (K : Set G) := hK
        EMetricSpace.ofRiemannianMetric 𝓘(ℝ, QuotientModelSpace I K) (G ⧸ K)
      CompleteSpace (G ⧸ K) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  have := isManifold_quotientOfIsClosed (I := I) hK
  intro _ _ hm
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  have : IsClosed (K : Set G) := hK
  have := contMDiffConstSMul_quotientOfIsClosed (I := I) hK
  have : MulAction.IsPretransitive (Isom 𝓘(ℝ, QuotientModelSpace I K) (G ⧸ K)) (G ⧸ K) :=
    .of_smul_eq (RiemannianIsometry.constSMulHom hm) fun {_ _} ↦ by
      rw [RiemannianIsometry.smul_def, RiemannianIsometry.constSMulHom_apply,
        RiemannianIsometry.constSMul_apply]
  exact completeSpace_ofRiemannianMetric_of_isPretransitive_isom (I := 𝓘(ℝ, QuotientModelSpace I K))
    (G ⧸ K)

/-- **Homogeneous metrics are complete.** The `G`-invariant metric on `G ⧸ K` determined by an
isotropy-invariant inner product at the base point is complete for its Riemannian distance. -/
theorem completeSpace_homogeneousMetric
    {β : letI := quotientChartedSpaceOfIsClosed I hK
      TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ]
        TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ] ℝ}
    (hsymm : ∀ u v, β u v = β v u) (hpos : ∀ u, u ≠ 0 → 0 < β u u)
    (hβ : letI := quotientChartedSpaceOfIsClosed I hK
      ∀ k ∈ K, ∀ u v, β (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) u)
          (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) v) = β u v) :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    letI : RiemannianBundle (fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x) :=
      ⟨(homogeneousMetric hK hsymm hpos hβ).toRiemannianMetric⟩
    haveI : IsContinuousRiemannianBundle (QuotientModelSpace I K)
        (fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x) :=
      Bundle.instIsContinuousRiemannianBundle
        (homogeneousMetric hK hsymm hpos hβ).toContinuousRiemannianMetric
    letI : EMetricSpace (G ⧸ K) :=
      haveI := topologicalGroup_of_lieGroup I ∞ (G := G)
      haveI : IsClosed (K : Set G) := hK
      EMetricSpace.ofRiemannianMetric 𝓘(ℝ, QuotientModelSpace I K) (G ⧸ K)
    CompleteSpace (G ⧸ K) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  have := isManifold_quotientOfIsClosed (I := I) hK
  let _ : RiemannianBundle (fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x) :=
    ⟨(homogeneousMetric hK hsymm hpos hβ).toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle (QuotientModelSpace I K)
      (fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x) :=
    Bundle.instIsContinuousRiemannianBundle
      (homogeneousMetric hK hsymm hpos hβ).toContinuousRiemannianMetric
  exact completeSpace_ofRiemannianMetric_of_inner_mfderiv_smul hK
    (homogeneousMetric_inner_mfderiv_smul (hsymm := hsymm) (hpos := hpos) (hβ := hβ))

end Completeness

end Subgroup
