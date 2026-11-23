/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Lie.Subgroup.Quotient
public import TauCeti.Geometry.Manifold.Riemannian.Section
public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Homogeneous
import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# Homogeneous and normal homogeneous metrics on `G ⧸ K`

Let `K` be a closed subgroup of a finite-dimensional Lie group `G`, so that the coset space
`G ⧸ K` is a smooth manifold (`Subgroup.quotientChartedSpaceOfIsClosed`) on which `G` acts
smoothly, with base point `o = [1]` and projection `π : G → G ⧸ K`.

A positive-definite symmetric bilinear form `β` on `T_o(G ⧸ K)` that is invariant under the
isotropy action `k ↦ d(k •)_o` of `K` extends to a unique `G`-invariant Riemannian metric on
`G ⧸ K`: at `x = g • o` the inner product evaluates `β` on the translates by `g⁻¹`, and invariance
under `K` makes this independent of the representative `g`. The metric is smooth because near
each point `g` can be chosen as a smooth local section of the submersion `π`. Through the
isomorphism `dπ_1 : 𝔪 ≃ T_o(G ⧸ K)` for an `Ad(K)`-stable complement `𝔪` of the Lie algebra `𝔨` of
`K`, isotropy-invariant forms on `T_o(G ⧸ K)` are the `Ad(K)`-invariant inner products on a
reductive complement.

For a Riemannian metric on `G` whose inner product at the identity is `Ad(K)`-invariant, the
horizontal inner product at `o`, transported from `𝔪 = 𝔨^⊥` by the horizontal lift, is
isotropy-invariant. If the metric on `G` is moreover left-invariant, `π` is a Riemannian
submersion onto the resulting homogeneous metric. When the inner product at the identity is
`Ad(G)`-invariant, so that the left-invariant metric on `G` is bi-invariant, this is the *normal
homogeneous metric*.

## Main definitions

* `Subgroup.homogeneousMetric`: the `G`-invariant metric on `G ⧸ K` determined by an
  isotropy-invariant inner product on `T_o(G ⧸ K)`.
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
  Riemannian submersion, with horizontal space the left translate of `𝔨^⊥`.
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

section Out

variable {G : Type*} [Group G] {K : Subgroup G}

/-- The inverse of the representative of `x` translates `x` to the base point. -/
theorem _root_.QuotientGroup.out_inv_smul (x : G ⧸ K) : x.out⁻¹ • x = ((1 : G) : G ⧸ K) := by
  calc x.out⁻¹ • x = x.out⁻¹ • ((x.out : G) : G ⧸ K) := by rw [QuotientGroup.out_eq']
    _ = _ := by rw [MulAction.Quotient.smul_coe, smul_eq_mul, inv_mul_cancel]

end Out

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {K : Subgroup G}

section Translation

variable (hK : IsClosed (K : Set G))

include hK in
/-- The differential of a translation of `G ⧸ K` is injective. -/
theorem injective_mfderiv_smul_quotient (g : G) (x : G ⧸ K) :
    letI := quotientChartedSpaceOfIsClosed I hK
    Injective (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
      (fun y : G ⧸ K ↦ g • y) x) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  have := contMDiffSMul_quotientOfIsClosed (I := I) hK
  exact ((Diffeomorph.smul I 𝓘(ℝ, QuotientModelSpace I K) ∞ g).isInvertible_mfderiv
    (by simp) (x := x)).injective

include hK in
/-- **Chain rule for translations of `G ⧸ K`.** -/
theorem mfderiv_smul_quotient_comp (g h : G) (x : G ⧸ K) {y : G ⧸ K} (hy : h • x = y) {c : G}
    (hc : g * h = c) :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ v : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x,
    mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K) (fun z : G ⧸ K ↦ g • z) y
        (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
          (fun z : G ⧸ K ↦ h • z) x v) =
      mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
        (fun z : G ⧸ K ↦ c • z) x v := by
  subst hc
  let _ := quotientChartedSpaceOfIsClosed I hK
  have := contMDiffSMul_quotientOfIsClosed (I := I) hK
  have hd (a : G) := ContMDiffSMul.mdifferentiable_const_smul (I := I)
    (I' := 𝓘(ℝ, QuotientModelSpace I K)) (M := G ⧸ K) (n := ∞) (by simp) a
  have hfun : (fun z : G ⧸ K ↦ (g * h) • z) = (fun z ↦ g • z) ∘ fun z ↦ h • z :=
    funext fun z ↦ mul_smul g h z
  intro v
  rw [hfun]
  exact (mfderiv_comp_apply_of_eq x (hd g y) (hd h x) hy v).symm

end Translation

section Metric

variable (hK : IsClosed (K : Set G))

variable (I K) in
/-- The bilinear form at `x` of the `G`-invariant extension of a bilinear form `β` on the tangent
space at the base point `o = [1]` of `G ⧸ K`: it evaluates `β` on the translates to `o` by the
inverse of the representative `x.out` of `x`. -/
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

/-- The homogeneous extension of `β` evaluates `β` on the translates to the base point by the
inverse of the representative of `x`. -/
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
tangent bundle of `G ⧸ K`. Near each point it is the pullback of the constant form `β` along the
differential of `y ↦ (s x)⁻¹ • y`, for a smooth local section `s` of `G → G ⧸ K`. -/
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
  have hpt : ∀ x ∈ U, (s x)⁻¹ • x = ((1 : G) : G ⧸ K) := fun x hx ↦ by
    calc (s x)⁻¹ • x = (s x)⁻¹ • ((s x : G) : G ⧸ K) := by rw [hsec x hx]
      _ = _ := by rw [MulAction.Quotient.smul_coe, smul_eq_mul, inv_mul_cancel]
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
  ext u v
  rw [homogeneousMetric_inner_of_mk_eq rfl,
    show (fun y : G ⧸ K ↦ (1 : G)⁻¹ • y) = id by funext y; simp, mfderiv_id]
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
  have key := mfderiv_smul_quotient_comp (I := I) hK (g * x.out)⁻¹ g x rfl
    (show (g * x.out)⁻¹ * g = x.out⁻¹ by group)
  rw [homogeneousMetric_inner_of_mk_eq hg, key, key, homogeneousMetric_inner,
    homogeneousBilinearForm_apply]

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
    rintro p rfl a b
    rfl
  ext x v w
  rw [← hm x.out⁻¹ x v w, hpt _ (QuotientGroup.out_inv_smul x), hmβ, homogeneousMetric_inner,
    homogeneousBilinearForm_apply]

end Metric

section Horizontal

variable (hK : IsClosed (K : Set G))

/-- **The projection intertwines conjugation and translation.** For `k ∈ K`, the differential at
the base point of the translation by `k` sends `dπ_1 a` to `dπ_1 (Ad_k a)`, where `π` is the
projection `G → G ⧸ K`. -/
theorem mfderiv_smul_mfderiv_quotientMk_one {k : G} (hk : k ∈ K) (a : GroupLieAlgebra I G) :
    letI := quotientChartedSpaceOfIsClosed I hK
    mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K) (fun y : G ⧸ K ↦ k • y)
        ((1 : G) : G ⧸ K)
        (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 a) =
      mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1
        (Lie.adjointContinuousLinearMap (I := I) k a) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  have := contMDiffSMul_quotientOfIsClosed (I := I) hK
  have hπ : MDifferentiable I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) :=
    (contMDiff_quotientMk (I := I) hK).mdifferentiable (by simp)
  have hτ := ContMDiffSMul.mdifferentiable_const_smul (I := I)
    (I' := 𝓘(ℝ, QuotientModelSpace I K)) (M := G ⧸ K) (n := ∞) (by simp) k
  have hc := (Lie.conjDiffeomorph (I := I) (n := 1) k).mdifferentiable (by simp)
  have hfun : (fun y : G ⧸ K ↦ k • y) ∘ (QuotientGroup.mk : G → G ⧸ K) =
      (QuotientGroup.mk : G → G ⧸ K) ∘ Lie.conjDiffeomorph (I := I) (n := 1) k := by
    funext y
    simp only [comp_apply, Lie.conjDiffeomorph_apply, MulAction.Quotient.smul_coe, smul_eq_mul]
    exact (QuotientGroup.mk_mul_of_mem (k * y) (K.inv_mem hk)).symm
  rw [Lie.adjointContinuousLinearMap_apply,
    ← mfderiv_comp_apply_of_eq 1 (hπ _) (hc 1) (by simp), ← hfun]
  exact (mfderiv_comp_apply_of_eq 1 (hτ _) (hπ 1) rfl a).symm

/-- The horizontal lift of the differential of the projection at the base point, written with
the left-invariant vector field `X_a` at `g`: translating `dπ_g (X_a g)` back to the base point
gives `dπ_1 a`. -/
theorem mfderiv_smul_inv_mfderiv_quotientMk_mulInvariantVectorField (g : G)
    (a : GroupLieAlgebra I G) :
    letI := quotientChartedSpaceOfIsClosed I hK
    mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K) (fun y : G ⧸ K ↦ g⁻¹ • y)
        (g : G ⧸ K)
        (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) g
          (mulInvariantVectorField a g)) =
      mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 a := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  have := contMDiffSMul_quotientOfIsClosed (I := I) hK
  have hπ : MDifferentiable I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) :=
    (contMDiff_quotientMk (I := I) hK).mdifferentiable (by simp)
  have hτ := ContMDiffSMul.mdifferentiable_const_smul (I := I)
    (I' := 𝓘(ℝ, QuotientModelSpace I K)) (M := G ⧸ K) (n := ∞) (by simp) g⁻¹
  have hL : MDifferentiable I I (fun y : G ↦ g * y) :=
    (contMDiff_mul_left (I := I) (n := ∞)).mdifferentiable (by simp)
  have hfun : (fun y : G ⧸ K ↦ g⁻¹ • y) ∘ ((QuotientGroup.mk : G → G ⧸ K) ∘ fun y : G ↦ g * y) =
      (QuotientGroup.mk : G → G ⧸ K) := by
    funext y
    simp
  rw [mulInvariantVectorField, ← mfderiv_comp_apply_of_eq 1 (hπ g) (hL 1) (mul_one g),
    ← mfderiv_comp_apply_of_eq 1 (hτ _) ((hπ (g * 1)).comp 1 (hL 1)) (by simp), hfun]

variable [RiemannianBundle (fun g : G ↦ TangentSpace I g)]

include hK in
/-- The restriction of `dπ_1` to the orthogonal complement of its kernel is bijective. -/
theorem bijective_mfderiv_quotientMk_one_orthogonal :
    letI := quotientChartedSpaceOfIsClosed I hK
    Bijective ((mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K)
      1).toLinearMap ∘ₗ (mfderiv I 𝓘(ℝ, QuotientModelSpace I K)
        (QuotientGroup.mk : G → G ⧸ K) 1).kerᗮ.subtype) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  set D := mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1
  refine ⟨fun a b hab ↦ ?_, fun u ↦ ?_⟩
  · have hmem : (a : TangentSpace I (1 : G)) - b ∈ D.ker := by
      simpa [sub_eq_zero] using hab
    have hmem' : (a : TangentSpace I (1 : G)) - b ∈ D.kerᗮ := D.kerᗮ.sub_mem a.prop b.prop
    exact Subtype.ext (sub_eq_zero.1 ((Submodule.inf_orthogonal_eq_bot D.ker).le ⟨hmem, hmem'⟩))
  · obtain ⟨a, rfl⟩ := (isSubmersion_quotientMk (I := I) hK).surjective_mfderiv (by simp) 1 u
    refine ⟨⟨D.kerᗮ.starProjection a, Submodule.starProjection_apply_mem _ _⟩, ?_⟩
    have h : a - D.kerᗮ.starProjection a ∈ D.ker := by
      simp
    have h' := LinearMap.mem_ker.1 h
    rw [map_sub, sub_eq_zero] at h'
    exact h'.symm

variable (I K) in
/-- **The horizontal lift at the identity.** The inverse of the restriction of `dπ_1` to the
orthogonal complement `𝔪 = 𝔨^⊥` of its kernel `𝔨`, for the inner product at the identity, where
`π` is the projection `G → G ⧸ K`. -/
def horizontalLiftOne :
    letI := quotientChartedSpaceOfIsClosed I hK
    TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ] TangentSpace I (1 : G) :=
  letI := quotientChartedSpaceOfIsClosed I hK
  LinearMap.toContinuousLinearMap ((mfderiv I 𝓘(ℝ, QuotientModelSpace I K)
    (QuotientGroup.mk : G → G ⧸ K) 1).kerᗮ.subtype ∘ₗ
      (LinearEquiv.ofBijective _
        (bijective_mfderiv_quotientMk_one_orthogonal (I := I) hK)).symm.toLinearMap)

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
  exact (LinearEquiv.ofBijective _
    (bijective_mfderiv_quotientMk_one_orthogonal (I := I) hK)).apply_symm_apply u

/-- A horizontal vector at the identity is the horizontal lift of its image. -/
theorem horizontalLiftOne_mfderiv_quotientMk {a : TangentSpace I (1 : G)} :
    letI := quotientChartedSpaceOfIsClosed I hK
    a ∈ (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1).kerᗮ →
    horizontalLiftOne I K hK
      (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1 a) = a := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  intro ha
  have := congrArg Subtype.val
    ((LinearEquiv.ofBijective _
      (bijective_mfderiv_quotientMk_one_orthogonal (I := I) hK)).symm_apply_apply
      ⟨a, ha⟩)
  exact this

variable (I K) in
/-- **The normal inner product at the base point.** The inner product on `T_o(G ⧸ K)` that makes
the horizontal lift at the identity an isometry onto `𝔪 = 𝔨^⊥`. -/
def horizontalInnerOne :
    letI := quotientChartedSpaceOfIsClosed I hK
    TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ]
      TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K) →L[ℝ] ℝ :=
  letI := quotientChartedSpaceOfIsClosed I hK
  (ContinuousLinearMap.precomp ℝ (horizontalLiftOne I K hK)).comp
    ((innerSL ℝ : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G) →L[ℝ] ℝ).comp
      (horizontalLiftOne I K hK))

/-- The horizontal inner product is the inner product at the identity of the horizontal lifts. -/
theorem horizontalInnerOne_apply :
    letI := quotientChartedSpaceOfIsClosed I hK
    ∀ u v : TangentSpace 𝓘(ℝ, QuotientModelSpace I K) ((1 : G) : G ⧸ K),
      horizontalInnerOne I K hK u v =
      inner ℝ (horizontalLiftOne I K hK u) (horizontalLiftOne I K hK v) :=
  fun _ _ ↦ rfl

/-- **Isotropy invariance of the normal inner product.** If the inner product at the identity of
`G` is invariant under `Ad(K)`, then the horizontal inner product at the base point of `G ⧸ K` is
invariant under the isotropy action of `K`: `Ad_k` preserves `𝔨` and hence `𝔪 = 𝔨^⊥`, and `dπ_1`
intertwines `Ad_k` with the differential of the translation by `k`. -/
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
  set D := mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) 1
  intro k hk u v
  have hker : ∀ k ∈ K, ∀ w ∈ D.ker, Lie.adjointContinuousLinearMap (I := I) k w ∈ D.ker := by
    intro k hk w hw
    rw [LinearMap.mem_ker] at hw ⊢
    erw [← mfderiv_smul_mfderiv_quotientMk_one hK hk w, hw, map_zero]
    rfl
  have hperp : ∀ a ∈ D.kerᗮ, (Lie.adjointContinuousLinearMap (I := I) k :
      TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G)) a ∈ D.kerᗮ := by
    intro a ha
    rw [Submodule.mem_orthogonal] at ha
    refine (Submodule.mem_orthogonal (E := TangentSpace I (1 : G)) D.ker _).2 fun w hw ↦ ?_
    rw [← Lie.adjointContinuousLinearMap_adjointContinuousLinearMap_inv k w, hAd k hk]
    exact ha _ (hker k⁻¹ (K.inv_mem hk) w hw)
  have hlift : ∀ u, horizontalLiftOne I K hK
      (mfderiv 𝓘(ℝ, QuotientModelSpace I K) 𝓘(ℝ, QuotientModelSpace I K)
        (fun y : G ⧸ K ↦ k • y) ((1 : G) : G ⧸ K) u) =
      (Lie.adjointContinuousLinearMap (I := I) k :
          TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G)) (horizontalLiftOne I K hK u) := by
    intro u
    have h := mfderiv_smul_mfderiv_quotientMk_one hK hk (horizontalLiftOne I K hK u)
    rw [mfderiv_quotientMk_horizontalLiftOne] at h
    rw [h]
    exact horizontalLiftOne_mfderiv_quotientMk hK (hperp _ (horizontalLiftOne_mem hK u))
  change inner ℝ (horizontalLiftOne I K hK _) (horizontalLiftOne I K hK _) =
    inner ℝ (horizontalLiftOne I K hK u) (horizontalLiftOne I K hK v)
  rw [hlift, hlift]
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
product at the base point: the horizontal space at `g` is the left translate of `𝔪 = 𝔨^⊥`. -/
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
    erw [key, map_zero]
    exact hc
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, hL g]
  change (homogeneousMetric hK (horizontalInnerOne_comm (I := I) hK)
    (horizontalInnerOne_pos (I := I) hK)
    (horizontalInnerOne_mfderiv_smul (I := I) hK hAd)).inner (g : G ⧸ K) _ _ = _
  rw [homogeneousMetric_inner_of_mk_eq rfl, key, horizontalInnerOne_apply,
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

variable (I) in
include I hK in
/-- The homogeneous space of a closed subgroup is regular: it is a Hausdorff manifold modelled on
a finite-dimensional space, hence locally compact. -/
theorem t3Space_quotientOfIsClosed : T3Space (G ⧸ K) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have : IsClosed (K : Set G) := hK
  have := Manifold.locallyCompact_of_finiteDimensional 𝓘(ℝ, QuotientModelSpace I K) (M := G ⧸ K)
  infer_instance

/-- **`G`-invariant metrics on `G ⧸ K` are complete.** For a Riemannian metric on the homogeneous
space of a closed subgroup for which `G` acts by isometries, the Riemannian distance is complete:
the isometry group acts transitively, already through `G`. -/
theorem completeSpace_ofRiemannianMetric_of_inner_mfderiv_smul
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
            (fun y : G ⧸ K ↦ g • y) x w) = m.inner x v w) :
    letI := quotientChartedSpaceOfIsClosed I hK
    haveI := isManifold_quotientOfIsClosed (I := I) hK
    letI : RiemannianBundle (fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x) :=
      ⟨m.toRiemannianMetric⟩
    haveI : IsContinuousRiemannianBundle (QuotientModelSpace I K)
        (fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x) :=
      Bundle.instIsContinuousRiemannianBundle m.toContinuousRiemannianMetric
    letI : EMetricSpace (G ⧸ K) :=
      haveI := t3Space_quotientOfIsClosed I hK
      EMetricSpace.ofRiemannianMetric 𝓘(ℝ, QuotientModelSpace I K) (G ⧸ K)
    CompleteSpace (G ⧸ K) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  have := isManifold_quotientOfIsClosed (I := I) hK
  have := contMDiffSMul_quotientOfIsClosed (I := I) hK
  have := t3Space_quotientOfIsClosed I hK
  let _ : RiemannianBundle (fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x) :=
    ⟨m.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle (QuotientModelSpace I K)
      (fun x : G ⧸ K ↦ TangentSpace 𝓘(ℝ, QuotientModelSpace I K) x) :=
    Bundle.instIsContinuousRiemannianBundle m.toContinuousRiemannianMetric
  -- Each translation is an isometry.
  let Φ : G → Isom 𝓘(ℝ, QuotientModelSpace I K) (G ⧸ K) := fun g ↦
    { toDiffeomorph := Diffeomorph.smul I 𝓘(ℝ, QuotientModelSpace I K) ∞ g
      inner_mfderiv' := hm g }
  have : MulAction.IsPretransitive (Isom 𝓘(ℝ, QuotientModelSpace I K) (G ⧸ K)) (G ⧸ K) := by
    refine ⟨fun x y ↦ ⟨Φ (y.out * x.out⁻¹), ?_⟩⟩
    rw [RiemannianIsometry.smul_def]
    change (y.out * x.out⁻¹) • x = y
    rw [mul_smul, QuotientGroup.out_inv_smul, MulAction.Quotient.smul_coe, smul_eq_mul, mul_one,
      QuotientGroup.out_eq']
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
      haveI := t3Space_quotientOfIsClosed I hK
      EMetricSpace.ofRiemannianMetric 𝓘(ℝ, QuotientModelSpace I K) (G ⧸ K)
    CompleteSpace (G ⧸ K) :=
  completeSpace_ofRiemannianMetric_of_inner_mfderiv_smul hK _
    (homogeneousMetric_inner_mfderiv_smul (hsymm := hsymm) (hpos := hpos) (hβ := hβ))

end Completeness

end Subgroup
