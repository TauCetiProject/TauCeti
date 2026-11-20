/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Flat
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ConformallyFlat.Basic
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension

/-!
# Local conformal factors and conformal Euclidean coordinate charts

`Bundle.ContMDiffRiemannianMetric.IsLocallyConformallyFlat` (and its pointwise counterpart
`Bundle.ContMDiffRiemannianMetric.IsLocallyConformallyFlatAt`) requires around each point `x` a
globally smooth positive conformal factor `f : M → ℝ` making `f g` flat near `x`. Classically,
local conformal flatness is phrased either using a positive factor defined only on an open
neighbourhood of `x`, or using a smooth coordinate chart onto an open Euclidean ball in which `g`
is a positive smooth multiple of the Euclidean metric. This file proves that the first two
descriptions agree on any smooth manifold with corners, while all three agree at interior points
and on boundaryless manifolds, with no dimension bound.

First, for an arbitrary smooth manifold with corners `M`:
* a locally defined smooth positive factor `φ : W → ℝ` on an open neighbourhood `W` of `x` extends
  via `ContMDiff.exists_contMDiffMap_pos_eventuallyEq_comp_subtype_val` to a globally smooth
  positive `f : M → ℝ` agreeing with `φ` near `x`, so flatness of `f g` near `x` is equivalent to
  existence of an open neighbourhood `W` of `x` and a local positive factor making `φ (g|_W)` flat
  on `W` (`eventually_curvatureTensor_rescale_eq_zero_iff_of_eventuallyEq_opens`,
  `isLocallyConformallyFlatAt_iff_exists_opens_curvatureTensor_rescale_eq_zero`,
  `isLocallyConformallyFlat_iff_forall_exists_opens_curvatureTensor_rescale_eq_zero`);
* restricting a locally conformally flat metric to an open submanifold preserves local conformal
  flatness, and local conformal flatness can be tested on any open cover
  (`IsLocallyConformallyFlatAt.restrictOpenTangentSpace`,
  `IsLocallyConformallyFlat.restrictOpenTangentSpace`,
  `isLocallyConformallyFlat_iff_forall_exists_opens_isLocallyConformallyFlat`).

Second, combining the local-factor characterization with the local Euclidean-isometry
characterization of flat metrics (`TauCeti.Geometry.Manifold.Riemannian.Isometry.Flat`), local
conformal flatness at an interior point `x₀` is equivalent both to a `RiemannianIsometry` from
`(W, φ (g|_W))` onto an open Euclidean ball centred at the origin and to a smooth diffeomorphism
`Ψ : W ≃ₘ^∞ Metric.ball 0 r` sending `x₀` to `0` under which `g|_W` is `ψ` times the pullback of
the Euclidean inner product
(`isLocallyConformallyFlatAt_iff_exists_riemannianIsometry_ball_of_isInteriorPoint`,
`isLocallyConformallyFlatAt_iff_exists_diffeomorph_ball_inner_eq_of_isInteriorPoint`). On a
boundaryless manifold this characterizes `g.IsLocallyConformallyFlat` by conformal Euclidean
coordinate charts (`isLocallyConformallyFlat_iff_forall_exists_riemannianIsometry_ball`,
`isLocallyConformallyFlat_iff_forall_exists_diffeomorph_ball_inner_eq`). Conversely, a conformal
local Riemannian isometry from an open neighbourhood of `x₀` into any real inner-product space `F`
gives local conformal flatness at `x₀` without any boundaryless or finite-dimensionality assumption
on `F` (`isLocallyConformallyFlatAt_of_isLocalRiemannianIsometry`,
`isLocallyConformallyFlat_of_forall_exists_isLocalRiemannianIsometry`).

## Main results

In `Bundle.ContMDiffRiemannianMetric`:

* `eventually_curvatureTensor_rescale_eq_zero_iff_of_eventuallyEq_opens`,
  `isLocallyConformallyFlatAt_iff_exists_opens_curvatureTensor_rescale_eq_zero`, and
  `isLocallyConformallyFlat_iff_forall_exists_opens_curvatureTensor_rescale_eq_zero`: equivalence
  between global and open-neighbourhood conformal factors.
* `IsLocallyConformallyFlatAt.restrictOpenTangentSpace`,
  `IsLocallyConformallyFlat.restrictOpenTangentSpace`, and
  `isLocallyConformallyFlat_iff_forall_exists_opens_isLocallyConformallyFlat`: open-submanifold
  locality of local conformal flatness.
* `isLocallyConformallyFlatAt_of_isLocalRiemannianIsometry` and
  `isLocallyConformallyFlat_of_forall_exists_isLocalRiemannianIsometry`: pointwise and global
  sufficient conditions from conformal local Riemannian isometries into a real inner-product space.
* `isLocallyConformallyFlatAt_iff_exists_riemannianIsometry_ball_of_isInteriorPoint` and
  `isLocallyConformallyFlatAt_iff_exists_diffeomorph_ball_inner_eq_of_isInteriorPoint`:
  interior-point characterizations by conformal Euclidean ball charts.
* `isLocallyConformallyFlat_iff_forall_exists_riemannianIsometry_ball` and
  `isLocallyConformallyFlat_iff_forall_exists_diffeomorph_ball_inner_eq`: global characterizations
  on boundaryless manifolds.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), Section 2.
-/

public section

open Bundle Filter Set TopologicalSpace TauCeti.Manifold
open scoped ContDiff Manifold Topology TauCeti

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

section DiffeomorphEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- On an open submanifold `W`, existence of a smooth positive conformal factor `φ` and a
`RiemannianIsometry` from `(W, φ (g|_W))` onto an open subset `V` of a real inner-product space `F`
sending `x₀W` to `v₀` is equivalent to existence of a smooth diffeomorphism `Ψ : W ≃ₘ^∞ V` sending
`x₀W` to `v₀` and a smooth positive `ψ : W → ℝ` expressing `g|_W` as `ψ` times the pullback of the
inner product of `F` along `(↑) ∘ Ψ`. -/
private theorem exists_riemannianIsometry_opens_iff_exists_diffeomorph_inner_eq [IsManifold I ∞ M]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (W : Opens M) (x₀W : W) (V : Opens F) (v₀ : F) :
    (∃ (φ : W → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) (hφ_pos : ∀ y, 0 < φ y),
      letI : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
        ⟨((g.restrictOpenTangentSpace W).rescale φ hφ hφ_pos).toRiemannianMetric⟩
      ∃ Ψ : TauCeti.RiemannianIsometry I 𝓘(ℝ, F) W V, (Ψ x₀W : F) = v₀) ↔
    ∃ (Ψ : W ≃ₘ^∞⟮I, 𝓘(ℝ, F)⟯ V) (ψ : W → ℝ),
      ContMDiff I 𝓘(ℝ) ∞ ψ ∧ (∀ y, 0 < ψ y) ∧ (Ψ x₀W : F) = v₀ ∧
      ∀ (y : W) (u v : TangentSpace I y),
        (g.restrictOpenTangentSpace W).inner y u v =
          ψ y * Inner.inner ℝ (mfderiv I 𝓘(ℝ, F) ((Subtype.val : V → F) ∘ Ψ) y u)
            (mfderiv I 𝓘(ℝ, F) ((Subtype.val : V → F) ∘ Ψ) y v) := by
  have hιV := TauCeti.IsLocalRiemannianIsometry.subtype_val (I := 𝓘(ℝ, F)) V
  constructor
  · rintro ⟨φ, hφ, hφ_pos, Ψ, hΨ₀⟩
    let _ : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
      ⟨((g.restrictOpenTangentSpace W).rescale φ hφ hφ_pos).toRiemannianMetric⟩
    refine ⟨Ψ.toDiffeomorph, fun y ↦ (φ y)⁻¹, hφ.inv₀ fun y ↦ (hφ_pos y).ne',
      fun y ↦ inv_pos.2 (hφ_pos y), hΨ₀, fun y u v ↦ ?_⟩
    have hdf (w : TangentSpace I y) :
        mfderiv I 𝓘(ℝ, F) ((Subtype.val : V → F) ∘ Ψ.toDiffeomorph) y w =
          mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (Subtype.val : V → F) (Ψ y)
            (mfderiv I 𝓘(ℝ, F) Ψ.toDiffeomorph y w) :=
      mfderiv_comp_apply y (hιV.mdifferentiableAt (Ψ y))
        (Ψ.toDiffeomorph.contMDiff.mdifferentiableAt (by simp)) w
    rw [hdf u, hdf v, hιV.inner_mfderiv (Ψ y)]
    have hΨ_inner := Ψ.inner_mfderiv y u v
    rw [inner_riemannianBundle ((g.restrictOpenTangentSpace W).rescale φ hφ hφ_pos) y u v,
      rescale_inner] at hΨ_inner
    rw [Ψ.coe_toDiffeomorph, hΨ_inner, inv_mul_cancel_left₀ (hφ_pos y).ne']
  · rintro ⟨d, ψ, hψ, hψ_pos, hd₀, hinner⟩
    have hφ : ContMDiff I 𝓘(ℝ) ∞ (fun y : W ↦ (ψ y)⁻¹) := hψ.inv₀ fun y ↦ (hψ_pos y).ne'
    have hφ_pos (y : W) : 0 < (ψ y)⁻¹ := inv_pos.2 (hψ_pos y)
    let _ : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
      ⟨((g.restrictOpenTangentSpace W).rescale (fun y ↦ (ψ y)⁻¹) hφ hφ_pos).toRiemannianMetric⟩
    refine ⟨fun y ↦ (ψ y)⁻¹, hφ, hφ_pos,
      { toDiffeomorph := d
        inner_mfderiv' := fun y u v ↦ ?_ }, hd₀⟩
    have hdf (w : TangentSpace I y) :
        mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (Subtype.val : V → F) (d y) (mfderiv I 𝓘(ℝ, F) d y w) =
          mfderiv I 𝓘(ℝ, F) ((Subtype.val : V → F) ∘ d) y w :=
      (mfderiv_comp_apply y (hιV.mdifferentiableAt (d y))
        (d.contMDiff.mdifferentiableAt (by simp)) w).symm
    rw [← hιV.inner_mfderiv (d y), hdf u, hdf v,
      inner_riemannianBundle ((g.restrictOpenTangentSpace W).rescale _ hφ hφ_pos) y u v,
      rescale_inner, hinner y u v, inv_mul_cancel_left₀ (hψ_pos y).ne']

end DiffeomorphEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-! ### Local conformal factors and open submanifolds -/

/-- If a globally smooth positive factor `f : M → ℝ` agrees near `xW : W` on an open submanifold `W`
with a smooth positive factor `φ : W → ℝ`, then `f g` is flat near `(xW : M)` if and only if
`φ (g|_W)` is flat near `xW`. -/
theorem eventually_curvatureTensor_rescale_eq_zero_iff_of_eventuallyEq_opens
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {W : Opens M} (xW : W) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ z, 0 < f z)
    {φ : W → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) (hφ_pos : ∀ y, 0 < φ y)
    (hf_eq : (f ∘ (Subtype.val : W → M)) =ᶠ[𝓝 xW] φ) :
    (∀ᶠ y in 𝓝 (xW : M), (letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0) ↔
    ∀ᶠ y : W in 𝓝 xW, (letI : RiemannianBundle (fun z : W ↦ TangentSpace I z) :=
        ⟨((g.restrictOpenTangentSpace W).rescale φ hφ hφ_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I W).curvatureTensor y) = 0 := by
  have hinner : ∀ᶠ y : W in 𝓝 xW,
      ((g.rescale f hf hf_pos).restrictOpenTangentSpace W).inner y =
        ((g.restrictOpenTangentSpace W).rescale φ hφ hφ_pos).inner y :=
    hf_eq.mono fun y hy ↦ by
      ext u v
      simp only [restrictOpenTangentSpace_inner, rescale_inner]
      rw [← hy, Function.comp_apply]
  have hpt : ∀ᶠ y : W in 𝓝 xW,
      ((letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor (y : M)) = 0) ↔
      ((letI : RiemannianBundle (fun z : W ↦ TangentSpace I z) :=
          ⟨((g.restrictOpenTangentSpace W).rescale φ hφ hφ_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I W).curvatureTensor y) = 0) :=
    hinner.eventually_nhds.mono fun y hy ↦ by
      rw [← curvatureTensor_leviCivitaConnection_restrictOpenTangentSpace_eq_zero_iff
        (g.rescale f hf hf_pos) W y,
        curvatureTensor_leviCivitaConnection_eq_of_eventually_inner_eq hy]
  constructor
  · intro hflat
    filter_upwards [(continuous_subtypeVal.tendsto xW).eventually hflat, hpt] with y hy hyiff
    exact hyiff.1 hy
  · intro hflat
    have hWflat : ∀ᶠ y : W in 𝓝 xW,
        (letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
            ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).curvatureTensor (y : M)) = 0 := by
      filter_upwards [hflat, hpt] with y hy hyiff
      exact hyiff.2 hy
    refine eventually_of_mem (W.isOpen.isOpenEmbedding_subtypeVal.image_mem_nhds.2 hWflat) ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hy

/-- If an open neighbourhood `W` of `x` carries a smooth positive factor `φ : W → ℝ` making
`φ (g|_W)` flat near `⟨x, hxW⟩`, then `g` is locally conformally flat at `x`. -/
private theorem isLocallyConformallyFlatAt_of_opens
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {W : Opens M} {x : M} (hxW : x ∈ W) {φ : W → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_pos : ∀ y, 0 < φ y)
    (hflat : ∀ᶠ y : W in 𝓝 ⟨x, hxW⟩,
      (letI : RiemannianBundle (fun z : W ↦ TangentSpace I z) :=
          ⟨((g.restrictOpenTangentSpace W).rescale φ hφ hφ_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I W).curvatureTensor y) = 0) :
    g.IsLocallyConformallyFlatAt x := by
  obtain ⟨G, hG_pos, hG_eq⟩ :=
    (hφ.of_le (by simp : (⊤ : ℕ∞) ≤ ∞)).exists_contMDiffMap_pos_eventuallyEq_comp_subtype_val
      (x := ⟨x, hxW⟩) hφ_pos
  exact g.isLocallyConformallyFlatAt_iff.2 ⟨G, G.contMDiff, hG_pos,
    (g.eventually_curvatureTensor_rescale_eq_zero_iff_of_eventuallyEq_opens ⟨x, hxW⟩
      G.contMDiff hG_pos hφ hφ_pos hG_eq).2 hflat⟩

/-- **Global versus open-neighbourhood conformal factors at a point.** A smooth metric `g` is
locally conformally flat at `x` if and only if `x` has an open neighbourhood `W` with a smooth
positive factor `φ : W → ℝ` making `φ (g|_W)` flat on `W`. -/
theorem isLocallyConformallyFlatAt_iff_exists_opens_curvatureTensor_rescale_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {x : M} :
    g.IsLocallyConformallyFlatAt x ↔
      ∃ (W : Opens M) (_ : x ∈ W) (φ : W → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
        (hφ_pos : ∀ y, 0 < φ y),
        ∀ y : W, (letI : RiemannianBundle (fun z : W ↦ TangentSpace I z) :=
            ⟨((g.restrictOpenTangentSpace W).rescale φ hφ hφ_pos).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I W).curvatureTensor y) = 0 := by
  constructor
  · intro hg
    obtain ⟨f, hf, hf_pos, hflat⟩ := g.isLocallyConformallyFlatAt_iff.1 hg
    obtain ⟨U, hUflat, hUopen, hxU⟩ := eventually_nhds_iff.1 hflat
    let W : Opens M := ⟨U, hUopen⟩
    have hEq := g.restrictOpenTangentSpace_rescale W f hf hf_pos
    refine ⟨W, hxU, f ∘ Subtype.val, hf.comp contMDiff_subtypeVal, fun y ↦ hf_pos y.val, fun y ↦ ?_⟩
    let _ : RiemannianBundle (fun z : W ↦ TangentSpace I z) :=
      ⟨((g.rescale f hf hf_pos).restrictOpenTangentSpace W).toRiemannianMetric⟩
    rw [curvatureTensor_leviCivitaConnection_eq_of_riemannianBundle_eq
      (congrArg ContMDiffRiemannianMetric.toRiemannianMetric hEq) y]
    exact (curvatureTensor_leviCivitaConnection_restrictOpenTangentSpace_eq_zero_iff
      (g.rescale f hf hf_pos) W y).2 (hUflat y.val y.property)
  · rintro ⟨W, hxW, φ, hφ, hφ_pos, hflat⟩
    exact g.isLocallyConformallyFlatAt_of_opens hxW hφ hφ_pos (Eventually.of_forall hflat)

/-- **Local conformal flatness via local conformal factors.** A smooth metric `g` is locally
conformally flat if and only if every point `x` has an open neighbourhood `W` and a smooth positive
function `φ : W → ℝ` such that `φ (g|_W)` has vanishing curvature tensor on `W`. -/
theorem isLocallyConformallyFlat_iff_forall_exists_opens_curvatureTensor_rescale_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    g.IsLocallyConformallyFlat ↔
      ∀ x : M, ∃ (W : Opens M) (_ : x ∈ W) (φ : W → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
        (hφ_pos : ∀ y, 0 < φ y),
        ∀ y : W, (letI : RiemannianBundle (fun z : W ↦ TangentSpace I z) :=
            ⟨((g.restrictOpenTangentSpace W).rescale φ hφ hφ_pos).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I W).curvatureTensor y) = 0 :=
  g.isLocallyConformallyFlat_iff_forall_isLocallyConformallyFlatAt.trans
    (forall_congr' fun _ ↦
      g.isLocallyConformallyFlatAt_iff_exists_opens_curvatureTensor_rescale_eq_zero)

/-- Restricting a metric that is locally conformally flat at `(x : M)` to an open submanifold `U`
containing `x` preserves local conformal flatness at `x`. -/
theorem IsLocallyConformallyFlatAt.restrictOpenTangentSpace
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {U : Opens M} {x : U}
    (hg : g.IsLocallyConformallyFlatAt (x : M)) :
    (g.restrictOpenTangentSpace U).IsLocallyConformallyFlatAt x := by
  obtain ⟨f, hf, hf_pos, hflat⟩ := g.isLocallyConformallyFlatAt_iff.1 hg
  exact (g.restrictOpenTangentSpace U).isLocallyConformallyFlatAt_iff.2
    ⟨f ∘ Subtype.val, hf.comp contMDiff_subtypeVal, fun y ↦ hf_pos y.val,
      (g.eventually_curvatureTensor_rescale_eq_zero_iff_of_eventuallyEq_opens x hf hf_pos
        (hf.comp contMDiff_subtypeVal) (fun y ↦ hf_pos y.val) EventuallyEq.rfl).1 hflat⟩

/-- Restricting a locally conformally flat metric to an open submanifold yields a locally
conformally flat metric. -/
theorem IsLocallyConformallyFlat.restrictOpenTangentSpace
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsLocallyConformallyFlat) (U : Opens M) :
    (g.restrictOpenTangentSpace U).IsLocallyConformallyFlat :=
  (g.restrictOpenTangentSpace U).isLocallyConformallyFlat_iff_forall_isLocallyConformallyFlatAt.2
    fun x ↦ (hg.isLocallyConformallyFlatAt x.val).restrictOpenTangentSpace

/-- **Locality of `IsLocallyConformallyFlat`.** A smooth metric `g` is locally conformally flat if
and only if every point has an open neighbourhood on which the restricted metric is locally
conformally flat. -/
theorem isLocallyConformallyFlat_iff_forall_exists_opens_isLocallyConformallyFlat
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    g.IsLocallyConformallyFlat ↔
      ∀ x : M, ∃ W : Opens M, x ∈ W ∧ (g.restrictOpenTangentSpace W).IsLocallyConformallyFlat := by
  refine ⟨fun hg x ↦ ⟨⊤, trivial, hg.restrictOpenTangentSpace ⊤⟩,
    fun h ↦ g.isLocallyConformallyFlat_iff_forall_isLocallyConformallyFlatAt.2 fun x ↦ ?_⟩
  obtain ⟨W, hxW, hW⟩ := h x
  obtain ⟨φ, hφ, hφ_pos, hflat⟩ :=
    (g.restrictOpenTangentSpace W).isLocallyConformallyFlatAt_iff.1
      (hW.isLocallyConformallyFlatAt ⟨x, hxW⟩)
  exact g.isLocallyConformallyFlatAt_of_opens hxW hφ hφ_pos hflat

/-! ### Comparison with conformal Euclidean coordinate charts -/

/-- **Pointwise sufficient condition from a conformal local Riemannian isometry.** If `x₀` lies in
an open neighbourhood `W` carrying a smooth positive factor `φ : W → ℝ` and a
`TauCeti.IsLocalRiemannianIsometry` from `(W, φ (g|_W))` into a real inner-product space `F`, then
`g` is locally conformally flat at `x₀`. Finite-dimensionality of `F` is derived automatically from
invertibility of the differential, and no boundaryless assumption is needed. -/
theorem isLocallyConformallyFlatAt_of_isLocalRiemannianIsometry
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {W : Opens M} {x₀ : M} (hx₀W : x₀ ∈ W) {φ : W → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_pos : ∀ y, 0 < φ y) {Φ : W → F}
    (hΦ : letI : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
        ⟨((g.restrictOpenTangentSpace W).rescale φ hφ hφ_pos).toRiemannianMetric⟩;
      TauCeti.IsLocalRiemannianIsometry I 𝓘(ℝ, F) Φ) :
    g.IsLocallyConformallyFlatAt x₀ := by
  let gW := (g.restrictOpenTangentSpace W).rescale φ hφ hφ_pos
  let _ : RiemannianBundle (fun y : W ↦ TangentSpace I y) := ⟨gW.toRiemannianMetric⟩
  let _ := Bundle.instIsContMDiffRiemannianBundle gW
  obtain ⟨A, -⟩ := hΦ.isInvertible_mfderiv ⟨x₀, hx₀W⟩
  have : FiniteDimensional ℝ (TangentSpace I (⟨x₀, hx₀W⟩ : W)) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) (⟨x₀, hx₀W⟩ : W)
  have : FiniteDimensional ℝ F :=
    (A.trans (NormedSpace.fromTangentSpace (Φ ⟨x₀, hx₀W⟩))).toLinearEquiv.finiteDimensional
  refine g.isLocallyConformallyFlatAt_of_opens hx₀W hφ hφ_pos (Eventually.of_forall fun y ↦ ?_)
  exact (hΦ.curvatureTensor_eq_zero_iff y).1 (curvatureTensor_leviCivitaConnection_model_space _)

/-- **Sufficient criterion for local conformal flatness from conformal local Riemannian
isometries.** If every point `x` has an open neighbourhood `W` carrying a smooth positive factor
`φ : W → ℝ` and a `TauCeti.IsLocalRiemannianIsometry` from `(W, φ (g|_W))` into a real inner-product
space `F`, then `g` is locally conformally flat. Finite-dimensionality of `F` is derived
automatically from invertibility of the differential, and no boundaryless assumption is needed. -/
theorem isLocallyConformallyFlat_of_forall_exists_isLocalRiemannianIsometry
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (h : ∀ x : M, ∃ (W : Opens M) (_ : x ∈ W) (φ : W → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
      (hφ_pos : ∀ y, 0 < φ y) (Φ : W → F),
      letI : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
        ⟨((g.restrictOpenTangentSpace W).rescale φ hφ hφ_pos).toRiemannianMetric⟩
      TauCeti.IsLocalRiemannianIsometry I 𝓘(ℝ, F) Φ) :
    g.IsLocallyConformallyFlat :=
  g.isLocallyConformallyFlat_iff_forall_isLocallyConformallyFlatAt.2 fun x ↦ by
    obtain ⟨W, hxW, φ, hφ, hφ_pos, Φ, hΦ⟩ := h x
    exact g.isLocallyConformallyFlatAt_of_isLocalRiemannianIsometry hxW hφ hφ_pos hΦ

/-- **Interior-point characterization by a conformal Riemannian isometry onto a Euclidean ball.**
At an interior point `x₀`, `g` is locally conformally flat at `x₀` if and only if there exist an
open neighbourhood `W` of `x₀`, a smooth positive `φ : W → ℝ`, and a `RiemannianIsometry` from
`(W, φ (g|_W))` onto `Metric.ball 0 r` sending `x₀` to `0`. -/
theorem isLocallyConformallyFlatAt_iff_exists_riemannianIsometry_ball_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) :
    g.IsLocallyConformallyFlatAt x₀ ↔
      ∃ (W : Opens M) (hx₀W : x₀ ∈ W) (r : ℝ) (_ : 0 < r)
        (φ : W → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) (hφ_pos : ∀ y, 0 < φ y),
        letI : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
          ⟨((g.restrictOpenTangentSpace W).rescale φ hφ hφ_pos).toRiemannianMetric⟩
        ∃ Ψ : TauCeti.RiemannianIsometry I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) W
            (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
              Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))),
          (Ψ ⟨x₀, hx₀W⟩ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0 := by
  constructor
  · intro hg
    obtain ⟨f, hf, hf_pos, hflat⟩ := g.isLocallyConformallyFlatAt_iff.1 hg
    obtain ⟨W, hx₀W, r, hr, Ψ, hΨ₀⟩ :=
      (eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff_of_isInteriorPoint
        (g.rescale f hf hf_pos) hx₀).1 hflat
    have hEq := congrArg ContMDiffRiemannianMetric.toRiemannianMetric
      (g.restrictOpenTangentSpace_rescale W f hf hf_pos)
    exact ⟨W, hx₀W, r, hr, f ∘ Subtype.val, hf.comp contMDiff_subtypeVal, fun y ↦ hf_pos y.val,
      hEq ▸ ⟨Ψ, hΨ₀⟩⟩
  · rintro ⟨W, hx₀W, r, -, φ, hφ, hφ_pos, Ψ, -⟩
    let _ : RiemannianBundle (fun z : W ↦ TangentSpace I z) :=
      ⟨((g.restrictOpenTangentSpace W).rescale φ hφ hφ_pos).toRiemannianMetric⟩
    exact g.isLocallyConformallyFlatAt_of_isLocalRiemannianIsometry hx₀W hφ hφ_pos
      ((TauCeti.IsLocalRiemannianIsometry.subtype_val
        (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
          Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))).comp Ψ.isLocalRiemannianIsometry)

/-- **Interior-point characterization by a conformal Euclidean coordinate chart.** At an interior
point `x₀`, `g` is locally conformally flat at `x₀` if and only if there exist an open
neighbourhood `W` of `x₀`, a smooth diffeomorphism `Ψ` of `W` onto an open Euclidean ball centred
at `0` sending `x₀` to `0`, and a smooth positive function `ψ : W → ℝ` such that `g|_W` is `ψ`
times the pullback of the Euclidean inner product along `Ψ`. -/
theorem isLocallyConformallyFlatAt_iff_exists_diffeomorph_ball_inner_eq_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) :
    g.IsLocallyConformallyFlatAt x₀ ↔
      ∃ (W : Opens M) (hx₀W : x₀ ∈ W) (r : ℝ) (_ : 0 < r)
        (Ψ : W ≃ₘ^∞⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))⟯
          (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
            Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))))
        (ψ : W → ℝ),
        ContMDiff I 𝓘(ℝ) ∞ ψ ∧ (∀ y, 0 < ψ y) ∧
        (Ψ ⟨x₀, hx₀W⟩ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0 ∧
        ∀ (y : W) (u v : TangentSpace I y),
          (g.restrictOpenTangentSpace W).inner y u v =
            ψ y * Inner.inner ℝ
              (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
                ((Subtype.val : _ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∘ Ψ) y u)
              (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
                ((Subtype.val : _ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∘ Ψ) y v) := by
  rw [g.isLocallyConformallyFlatAt_iff_exists_riemannianIsometry_ball_of_isInteriorPoint hx₀]
  exact exists_congr fun W ↦ exists_congr fun hx₀W ↦ exists_congr fun r ↦ exists_congr fun _ ↦
    exists_riemannianIsometry_opens_iff_exists_diffeomorph_inner_eq g W ⟨x₀, hx₀W⟩
      ⟨Metric.ball 0 r, Metric.isOpen_ball⟩ 0

section Boundaryless

variable [BoundarylessManifold I M]

/-- **Conformal Euclidean ball-isometry characterization of local conformal flatness.** On a
boundaryless manifold, `g` is locally conformally flat if and only if every point `x` admits an open
neighbourhood `W`, a smooth positive `φ : W → ℝ`, and a `RiemannianIsometry` from `(W, φ (g|_W))`
onto an open Euclidean ball sending `x` to `0`. -/
theorem isLocallyConformallyFlat_iff_forall_exists_riemannianIsometry_ball
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    g.IsLocallyConformallyFlat ↔
      ∀ x : M, ∃ (W : Opens M) (hxW : x ∈ W) (r : ℝ) (_ : 0 < r)
        (φ : W → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) (hφ_pos : ∀ y, 0 < φ y),
        letI : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
          ⟨((g.restrictOpenTangentSpace W).rescale φ hφ hφ_pos).toRiemannianMetric⟩
        ∃ Ψ : TauCeti.RiemannianIsometry I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) W
            (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
              Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))),
          (Ψ ⟨x, hxW⟩ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0 :=
  g.isLocallyConformallyFlat_iff_forall_isLocallyConformallyFlatAt.trans <| forall_congr' fun _ ↦
    g.isLocallyConformallyFlatAt_iff_exists_riemannianIsometry_ball_of_isInteriorPoint
      BoundarylessManifold.isInteriorPoint

/-- **Conformal Euclidean coordinate-chart characterization of local conformal flatness.** On a
boundaryless manifold, `g` is locally conformally flat if and only if every point `x` admits an open
neighbourhood `W`, a smooth diffeomorphism `Ψ` of `W` onto an open Euclidean ball sending `x` to
`0`, and a smooth positive function `ψ : W → ℝ` such that `g|_W` is `ψ` times the pullback of the
Euclidean inner product along `Ψ`. -/
theorem isLocallyConformallyFlat_iff_forall_exists_diffeomorph_ball_inner_eq
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    g.IsLocallyConformallyFlat ↔
      ∀ x : M, ∃ (W : Opens M) (hxW : x ∈ W) (r : ℝ) (_ : 0 < r)
        (Ψ : W ≃ₘ^∞⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))⟯
          (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
            Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))))
        (ψ : W → ℝ),
        ContMDiff I 𝓘(ℝ) ∞ ψ ∧ (∀ y, 0 < ψ y) ∧
        (Ψ ⟨x, hxW⟩ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0 ∧
        ∀ (y : W) (u v : TangentSpace I y),
          (g.restrictOpenTangentSpace W).inner y u v =
            ψ y * Inner.inner ℝ
              (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
                ((Subtype.val : _ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∘ Ψ) y u)
              (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
                ((Subtype.val : _ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∘ Ψ) y v) :=
  g.isLocallyConformallyFlat_iff_forall_isLocallyConformallyFlatAt.trans <| forall_congr' fun _ ↦
    g.isLocallyConformallyFlatAt_iff_exists_diffeomorph_ball_inner_eq_of_isInteriorPoint
      BoundarylessManifold.isInteriorPoint

end Boundaryless

end Bundle.ContMDiffRiemannianMetric
