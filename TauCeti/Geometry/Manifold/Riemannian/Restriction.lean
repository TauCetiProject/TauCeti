/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# Restrictions of Riemannian metrics

This file restricts a `C^n` Riemannian metric to an open submanifold. Mathlib models the tangent
space of a manifold on the model vector space itself, so the restricted metric is pointwise the
ambient metric; the content is that this family is `C^n` for the inherited manifold and tangent
bundle structures.

It also restricts a `C^n` metric on `M × ℝ` to the manifold with boundary `M × [a, b]`, as the
pullback along the inclusion, whose differential is invertible also at the boundary.

## Main definitions

* `Bundle.RiemannianMetric.restrictOpenTangentSpace`: restriction of a fibrewise Riemannian metric.
* `Bundle.ContMDiffRiemannianMetric.restrictOpenTangentSpace`: restriction of a `C^n` Riemannian
  metric.
* `Bundle.ContMDiffRiemannianMetric.restrictOpenTangentSpace_eq_of_inner_eq`: metrics that agree
  on an open set have equal restrictions to it.
* `TauCeti.Manifold.contMDiffRiemannianMetricOpen`: the ambient instance metric restricted to an
  open submanifold.
* `TauCeti.Manifold.instRiemannianBundleOpen`,
  `TauCeti.Manifold.instIsContinuousRiemannianBundleOpen`, and
  `TauCeti.Manifold.instIsContMDiffRiemannianBundleOpen`: the corresponding scoped instances.
* `TauCeti.Manifold.pathELength_subtypeVal_comp`: the length of a curve in an open submanifold
  equals the length of its composition with the inclusion into the ambient manifold.
* `TopologicalSpace.Opens.riemannianEDist_le_riemannianEDist_subtype`: restriction to an open
  submanifold cannot decrease Riemannian distance.
* `Bundle.ContMDiffRiemannianMetric.restrictIcc`: the restriction of a metric on `M × ℝ` to
  `M × [a, b]`.

The three instances are in the `TauCeti` scope; use `open scoped TauCeti` to install them. In
particular, under the usual separation hypotheses this makes `EMetricSpace.ofRiemannianMetric`
available on the open submanifold.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 1, §2.
-/

public section

open Bundle Filter Manifold TopologicalSpace
open scoped Bundle ContDiff Manifold Topology

noncomputable section

namespace Bundle.RiemannianMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Restrict a Riemannian metric on a tangent bundle to an open submanifold. -/
noncomputable def restrictOpenTangentSpace
    (g : RiemannianMetric (fun x : M ↦ TangentSpace I x)) (U : Opens M) :
    RiemannianMetric (fun x : U ↦ TangentSpace I x) where
  inner := TauCeti.Manifold.restrictOpenTangentSpaceBilin g.inner U
  symm x v w := by
    rw [TauCeti.Manifold.restrictOpenTangentSpaceBilin_apply,
      TauCeti.Manifold.restrictOpenTangentSpaceBilin_apply]
    exact g.symm x.1 _ _
  pos x v hv := by
    rw [TauCeti.Manifold.restrictOpenTangentSpaceBilin_apply]
    exact g.pos x.1 _
      ((TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x).toLinearEquiv.map_ne_zero_iff.mpr hv)
  continuousAt x := by
    have h : ContinuousAt (fun v : TangentSpace I x ↦
        g.inner x.1 (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x v)
          (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x v)) 0 :=
      (g.continuousAt x.1).comp_of_eq
        (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x).continuousAt (map_zero _)
    simpa only [TauCeti.Manifold.restrictOpenTangentSpaceBilin_apply] using h
  isVonNBounded x := by
    have heq : {v | TauCeti.Manifold.restrictOpenTangentSpaceBilin g.inner U x v v < 1} =
        (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x).symm.toContinuousLinearMap ''
          {v | g.inner x.1 v v < 1} := by
      simp only [TauCeti.Manifold.restrictOpenTangentSpaceBilin_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.image_symm_eq_preimage,
        Set.preimage_ofPred_eq]
    rw [heq]
    exact (g.isVonNBounded x.1).image
      (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x).symm.toContinuousLinearMap

/-- Restricting a Riemannian metric evaluates the ambient metric through the canonical tangent-space
identification. -/
@[simp]
theorem restrictOpenTangentSpace_inner
    (g : RiemannianMetric (fun x : M ↦ TangentSpace I x)) (U : Opens M)
    (x : U) (v w : TangentSpace I x) :
    (g.restrictOpenTangentSpace U).inner x v w =
      g.inner (x : M) (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x v)
        (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x w) :=
  TauCeti.Manifold.restrictOpenTangentSpaceBilin_apply g.inner U x v w

/-- The restricted metric is the pullback of the ambient metric along the differential of the
open-submanifold inclusion. -/
theorem restrictOpenTangentSpace_inner_mfderiv_subtype_val
    (g : RiemannianMetric (fun x : M ↦ TangentSpace I x)) (U : Opens M)
    (x : U) (v w : TangentSpace I x) :
    (g.restrictOpenTangentSpace U).inner x v w =
      g.inner (x : M) (mfderiv I I (Subtype.val : U → M) x v)
        (mfderiv I I (Subtype.val : U → M) x w) := by
  rw [TauCeti.Manifold.mfderiv_subtype_val]
  exact g.restrictOpenTangentSpace_inner U x v w

end Bundle.RiemannianMetric

namespace Bundle.ContMDiffRiemannianMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- Restrict a `C^n` Riemannian metric on a manifold to an open submanifold. -/
noncomputable def restrictOpenTangentSpace
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (U : Opens M) :
    ContMDiffRiemannianMetric I n E (fun x : U ↦ TangentSpace I x) :=
  { g.toRiemannianMetric.restrictOpenTangentSpace U with
  contMDiff x := TauCeti.Manifold.contMDiffAt_restrictOpenTangentSpaceBilin (g.contMDiff x) }

/-- Restricting a `C^n` Riemannian metric evaluates the ambient metric through the canonical
tangent-space identification. -/
@[simp]
theorem restrictOpenTangentSpace_inner
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (U : Opens M)
    (x : U) (v w : TangentSpace I x) :
    (g.restrictOpenTangentSpace U).inner x v w =
      g.inner (x : M) (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x v)
        (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x w) := by
  exact Bundle.RiemannianMetric.restrictOpenTangentSpace_inner g.toRiemannianMetric U x v w

/-- Forgetting `C^n` regularity after restricting a metric gives its fibrewise restriction. -/
@[simp]
theorem restrictOpenTangentSpace_toRiemannianMetric
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (U : Opens M) :
    (g.restrictOpenTangentSpace U).toRiemannianMetric =
      g.toRiemannianMetric.restrictOpenTangentSpace U := by
  rfl

/-- Two `C^n` Riemannian metrics that agree on an open set `U` have equal restrictions to `U`. -/
theorem restrictOpenTangentSpace_eq_of_inner_eq
    {g₁ g₂ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)} (U : Opens M)
    (h : ∀ x ∈ U, g₁.inner x = g₂.inner x) :
    g₁.restrictOpenTangentSpace U = g₂.restrictOpenTangentSpace U := by
  ext x v w
  simp only [restrictOpenTangentSpace_inner, h x x.2]

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The `C^n` Riemannian metric on an open submanifold obtained by restricting the ambient
metric. -/
noncomputable def contMDiffRiemannianMetricOpen
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)] (U : Opens M) :
    ContMDiffRiemannianMetric I n E (fun x : U ↦ TangentSpace I x) :=
  (Bundle.ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := I) (n := n) (F := E) (V := fun x : M ↦ TangentSpace I x)).restrictOpenTangentSpace U

/-- The restricted Riemannian metric is the ambient metric under the canonical identification of
tangent spaces. -/
@[simp]
theorem contMDiffRiemannianMetricOpen_inner
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (U : Opens M) (x : U) (v w : TangentSpace I x) :
    (contMDiffRiemannianMetricOpen (I := I) (n := n) U).inner x v w =
      RiemannianBundle.g.inner (x : M)
        (tangentSpaceOpenEquiv (I := I) x v)
        (tangentSpaceOpenEquiv (I := I) x w) := by
  simpa only [contMDiffRiemannianMetricOpen,
    Bundle.ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner] using
    Bundle.ContMDiffRiemannianMetric.restrictOpenTangentSpace_inner
    (Bundle.ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
      (IB := I) (n := n) (F := E) (V := fun x : M ↦ TangentSpace I x)) U x v w

end TauCeti.Manifold

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- An open submanifold inherits the ambient Riemannian bundle (fibrewise inner product). -/
@[instance_reducible]
noncomputable def Manifold.instRiemannianBundleOpen
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (U : Opens M) :
  RiemannianBundle (fun x : U ↦ TangentSpace I x) :=
  ⟨RiemannianBundle.g.restrictOpenTangentSpace U⟩

scoped[TauCeti] attribute [instance] Manifold.instRiemannianBundleOpen

section IsManifold

variable {n : ℕ∞ω} [IsManifold I 1 M]

/-- The restricted Riemannian bundle is continuous whenever the ambient bundle is continuous. -/
theorem Manifold.instIsContinuousRiemannianBundleOpen
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] (U : Opens M) :
    IsContinuousRiemannianBundle E (fun x : U ↦ TangentSpace I x) := by
  let _ : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  let g := Manifold.contMDiffRiemannianMetricOpen (I := I) (n := 0) U
  exact ⟨g.inner, g.contMDiff.continuous, by
    intro x v w
    exact (Bundle.RiemannianMetric.restrictOpenTangentSpace_inner
      RiemannianBundle.g U x v w).trans
        (Manifold.contMDiffRiemannianMetricOpen_inner (I := I) (n := 0) U x v w).symm⟩

scoped[TauCeti] attribute [instance] Manifold.instIsContinuousRiemannianBundleOpen

/-- The restricted Riemannian bundle is as `C^n` as the ambient one. -/
theorem Manifold.instIsContMDiffRiemannianBundleOpen
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)] (U : Opens M) :
    IsContMDiffRiemannianBundle I n E (fun x : U ↦ TangentSpace I x) := by
  let g := Manifold.contMDiffRiemannianMetricOpen (I := I) (n := n) U
  exact ⟨g.inner, g.contMDiff, by
    intro x v w
    exact (Bundle.RiemannianMetric.restrictOpenTangentSpace_inner
      RiemannianBundle.g U x v w).trans
        (Manifold.contMDiffRiemannianMetricOpen_inner (I := I) (n := n) U x v w).symm⟩

scoped[TauCeti] attribute [instance] Manifold.instIsContMDiffRiemannianBundleOpen

end IsManifold

namespace Manifold

/-- The metric installed on an open submanifold is the fibrewise restriction of the ambient
metric. -/
@[simp]
theorem riemannianBundleOpen_g
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] (U : Opens M) :
    letI := instRiemannianBundleOpen (I := I) U
    RiemannianBundle.g (E := fun x : U ↦ TangentSpace I x) =
      (RiemannianBundle.g (E := fun x : M ↦ TangentSpace I x)).restrictOpenTangentSpace U := by
  rfl

/-- The inner product installed on an open submanifold is the ambient inner product under the
canonical tangent-space identification. -/
@[simp]
theorem inner_tangentSpace_open
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] (U : Opens M)
    (x : U) (v w : TangentSpace I x) :
    letI := instRiemannianBundleOpen (I := I) U
    inner ℝ v w = RiemannianBundle.g.inner (x : M)
      (tangentSpaceOpenEquiv (I := I) x v) (tangentSpaceOpenEquiv (I := I) x w) := by
  exact Bundle.RiemannianMetric.restrictOpenTangentSpace_inner RiemannianBundle.g U x v w

/-- The norm installed on an open submanifold is the ambient Riemannian norm under the canonical
tangent-space identification. -/
@[simp]
theorem norm_tangentSpace_open
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] (U : Opens M)
    (x : U) (v : TangentSpace I x) :
    letI := instRiemannianBundleOpen (I := I) U
    ‖v‖ = ‖tangentSpaceOpenEquiv (I := I) x v‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_tangentSpace_open]
  congr 1

/-- The extended norm installed on an open submanifold is the ambient Riemannian extended norm
under the canonical tangent-space identification. -/
@[simp]
theorem enorm_tangentSpace_open
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] (U : Opens M)
    (x : U) (v : TangentSpace I x) :
    letI := instRiemannianBundleOpen (I := I) U
    ‖v‖ₑ = ‖tangentSpaceOpenEquiv (I := I) x v‖ₑ := by
  simp only [enorm, nnnorm, norm_tangentSpace_open]

end Manifold

end TauCeti

namespace TauCeti.Manifold

open Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {U : Opens M}

/-- Path length is intrinsic: restricting the metric of `M` to an open submanifold `U` does not
change the length of a `C¹` curve read in `U`. -/
@[simp]
theorem pathELength_subtypeVal_comp {γ : ℝ → U} {a b : ℝ}
    (hγ : CMDiff[Icc a b] 1 γ) :
    pathELength I γ a b = pathELength I ((Subtype.val : U → M) ∘ γ) a b := by
  rw [pathELength_eq_lintegral_mfderiv_Icc, pathELength_eq_lintegral_mfderiv_Icc,
    ← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
  refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
  have hd : ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t :=
    (hγ t (Set.Ioo_subset_Icc_self ht)).contMDiffAt (Icc_mem_nhds ht.1 ht.2)
  have hval : ContMDiffAt I I 1 (Subtype.val : U → M) (γ t) :=
    contMDiff_subtype_val (γ t)
  have hv' : MDiffAt (Subtype.val : U → M) (γ t) := hval.mdifferentiableAt one_ne_zero
  have hd' : MDiffAt γ t := hd.mdifferentiableAt one_ne_zero
  rw [(HasMFDerivAt.comp t hv'.hasMFDerivAt hd'.hasMFDerivAt).mfderiv, mfderiv_subtype_val]
  simp

end TauCeti.Manifold

namespace TopologicalSpace.Opens

open scoped TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- Restricting the Riemannian metric to an open submanifold cannot decrease distance: every
curve in the submanifold is an ambient curve of the same length. -/
theorem riemannianEDist_le_riemannianEDist_subtype (U : Opens M) (x y : U) :
    riemannianEDist I (x : M) (y : M) ≤ riemannianEDist I x y := by
  refine TauCeti.Manifold.le_riemannianEDist_of_forall_le_pathELength (M := U)
    (I := I) fun γ h0 h1 hγ ↦ ?_
  rw [TauCeti.Manifold.pathELength_subtypeVal_comp hγ]
  exact Manifold.riemannianEDist_le_pathELength
    (contMDiff_subtype_val.comp_contMDiffOn hγ)
    (congrArg Subtype.val h0) (congrArg Subtype.val h1) zero_le_one

end TopologicalSpace.Opens

namespace Bundle.ContMDiffRiemannianMetric

open Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {a b : ℝ} [Fact (a < b)]
  (G : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) n (E × ℝ)
    (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p))

variable (a b) in
/-- The restriction of a metric `G` on `M × ℝ` to the manifold with boundary `M × [a, b]`: the
pullback of `G` along the inclusion. -/
noncomputable def restrictIcc :
    ContMDiffRiemannianMetric (I.prod (𝓡∂ 1)) n (E × EuclideanSpace ℝ (Fin 1))
      (fun p : M × Icc a b ↦ TangentSpace (I.prod (𝓡∂ 1)) p) :=
  G.pullback (Prod.map id Subtype.val) (contMDiff_id.prodMap contMDiff_subtypeVal_Icc)
    fun p ↦ (TauCeti.Manifold.isInvertible_mfderiv_prodMap_id_subtypeVal_Icc p).injective

/-- The restriction of `G` to `M × [a, b]` is the pullback of `G` along the inclusion. -/
theorem restrictIcc_eq_pullback :
    G.restrictIcc a b =
      G.pullback (Prod.map id Subtype.val) (contMDiff_id.prodMap contMDiff_subtypeVal_Icc)
        fun p ↦ (TauCeti.Manifold.isInvertible_mfderiv_prodMap_id_subtypeVal_Icc p).injective :=
  (rfl)

/-- The restriction of `G` to `M × [a, b]` at `(x, t)` is `G` at `(x, t)`, evaluated on the images
of the tangent vectors under the differential of the inclusion. -/
@[simp]
theorem restrictIcc_inner (p : M × Icc a b) (v w : TangentSpace (I.prod (𝓡∂ 1)) p) :
    (G.restrictIcc a b).inner p v w =
      G.inner (p.1, p.2)
        (mfderiv (I.prod (𝓡∂ 1)) (I.prod 𝓘(ℝ)) (Prod.map id Subtype.val) p v)
        (mfderiv (I.prod (𝓡∂ 1)) (I.prod 𝓘(ℝ)) (Prod.map id Subtype.val) p w) :=
  G.pullback_inner _ _ _ p v w

variable {G} in
/-- The restriction of `G` to `M × [a, b]` at `(x, t)` only depends on `G` at `(x, t)`. -/
theorem restrictIcc_inner_congr
    {G' : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) n (E × ℝ)
      (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p)} {p : M × Icc a b}
    (h : G.inner (p.1, p.2) = G'.inner (p.1, p.2)) :
    (G.restrictIcc a b).inner p = (G'.restrictIcc a b).inner p := by
  ext v w
  rw [restrictIcc_inner, restrictIcc_inner, h]

end Bundle.ContMDiffRiemannianMetric
