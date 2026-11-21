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
import TauCeti.Geometry.Manifold.ContMDiff.Log
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Rescale

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

/-! ### Further results -/

public section

open Bundle Filter Function Set TopologicalSpace TauCeti.Manifold
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-! ### Locality and pullback invariance of `IsLocallyConformallyFlat` -/

open scoped TauCeti in
/-- **Transporting conformal flatness along a local Riemannian isometry.** If an open neighbourhood
`(W, g|_W)` of `x` admits a local Riemannian isometry `f : W → N` into `(N, g_N)` and `g_N` is
locally conformally flat, then `g` admits a globally smooth positive factor `c : M → ℝ` whose
rescaling `c g` is flat near `x`. -/
theorem exists_eventually_curvatureTensor_rescale_eq_zero_of_isLocalRiemannianIsometry
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N] [IsManifold J ∞ N]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {W : Opens M} {x : M} (hxW : x ∈ W)
    (gN : ContMDiffRiemannianMetric J ∞ F (fun z : N ↦ TangentSpace J z))
    (hgN : gN.IsLocallyConformallyFlat) {f : W → N}
    (hf : letI : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
            ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
          letI : RiemannianBundle (fun z : N ↦ TangentSpace J z) := ⟨gN.toRiemannianMetric⟩
          TauCeti.IsLocalRiemannianIsometry I J f) :
    ∃ (c : M → ℝ) (hc : ContMDiff I 𝓘(ℝ) ∞ c) (hc_pos : ∀ y, 0 < c y),
      ∀ᶠ y in 𝓝 x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale c hc hc_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 := by
  have hf_smooth : ContMDiff I J ∞ f :=
    letI : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
      ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
    letI : RiemannianBundle (fun z : N ↦ TangentSpace J z) := ⟨gN.toRiemannianMetric⟩
    hf.contMDiff
  obtain ⟨h, hh, hh_pos, hflat_N⟩ := (gN.isLocallyConformallyFlat_iff).1 hgN (f ⟨x, hxW⟩)
  let lW : W → ℝ := fun y ↦ Real.log (h (f y))
  have hlW : ContMDiff I 𝓘(ℝ) ∞ lW := (hh.comp hf_smooth).log fun y ↦ (hh_pos (f y)).ne'
  obtain ⟨G, hG_eq⟩ :=
    (ContMDiffMap.contMDiffOn_extend W ⟨lW, hlW⟩ 0).exists_contMDiffMap_eventuallyEq
      (n := (⊤ : ℕ∞)) (W.isOpen.mem_nhds hxW)
  let c (y : M) : ℝ := Real.exp (G y)
  have hc : ContMDiff I 𝓘(ℝ) ∞ c := Real.contDiff_exp.comp_contMDiff G.contMDiff
  have hc_pos (y : M) : 0 < c y := Real.exp_pos _
  obtain ⟨U_W, hUW_flat, hUW_open, hxUW⟩ :=
    eventually_nhds_iff.1 (hf_smooth.continuous.continuousAt.eventually hflat_N)
  have hU_M : Subtype.val '' U_W ∈ 𝓝 x :=
    (W.isOpen.isOpenMap_subtypeVal U_W hUW_open).mem_nhds ⟨⟨x, hxW⟩, hxUW, rfl⟩
  obtain ⟨V, hV_sub, hV_open, hxV⟩ :=
    eventually_nhds_iff.1 ((hG_eq.and (W.isOpen.mem_nhds hxW)).and hU_M)
  let W₁ : Opens M := ⟨V, hV_open⟩
  have hW₁W : W₁ ≤ W := fun y hy ↦ (hV_sub y hy).1.2
  let g₁ := g.rescale c hc hc_pos
  let gN₁ := gN.rescale h hh hh_pos
  have hfW₁ :
      letI : RiemannianBundle (fun y : W₁ ↦ TangentSpace I y) :=
        ⟨(g.restrictOpenTangentSpace W₁).toRiemannianMetric⟩
      letI : RiemannianBundle (fun z : N ↦ TangentSpace J z) := ⟨gN.toRiemannianMetric⟩
      TauCeti.IsLocalRiemannianIsometry I J (f ∘ Opens.inclusion hW₁W) := by
    have hinc :
        letI : RiemannianBundle (fun y : W₁ ↦ TangentSpace I y) :=
          ⟨(g.restrictOpenTangentSpace W₁).toRiemannianMetric⟩
        letI : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
          ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
        TauCeti.IsLocalRiemannianIsometry I I (Opens.inclusion hW₁W) := by
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      exact g.riemannianBundle_restrictOpenTangentSpace_eq W₁ ▸
        g.riemannianBundle_restrictOpenTangentSpace_eq W ▸
        TauCeti.IsLocalRiemannianIsometry.inclusion (I := I) hW₁W
    let _ : RiemannianBundle (fun y : W₁ ↦ TangentSpace I y) :=
      ⟨(g.restrictOpenTangentSpace W₁).toRiemannianMetric⟩
    let _ : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
      ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
    let _ : RiemannianBundle (fun z : N ↦ TangentSpace J z) := ⟨gN.toRiemannianMetric⟩
    exact hf.comp hinc
  have hres_W₁ : (g.restrictOpenTangentSpace W₁).rescale (c ∘ Subtype.val)
      (hc.comp contMDiff_subtypeVal) (fun y ↦ hc_pos y.val) =
      g₁.restrictOpenTangentSpace W₁ := by
    ext y v w
    simp only [g₁, Function.comp_apply, rescale_inner, restrictOpenTangentSpace_inner]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    ⟨g₁.inner, g₁.contMDiff, fun _ _ _ ↦ rfl⟩
  let _ : RiemannianBundle (fun y : W₁ ↦ TangentSpace I y) :=
    ⟨(g₁.restrictOpenTangentSpace W₁).toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun y : W₁ ↦ TangentSpace I y) :=
    ⟨(g₁.restrictOpenTangentSpace W₁).inner, (g₁.restrictOpenTangentSpace W₁).contMDiff,
      fun _ _ _ ↦ rfl⟩
  let _ : RiemannianBundle (fun z : N ↦ TangentSpace J z) := ⟨gN₁.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle J ∞ F (fun z : N ↦ TangentSpace J z) :=
    ⟨gN₁.inner, gN₁.contMDiff, fun _ _ _ ↦ rfl⟩
  have hf₁ : TauCeti.IsLocalRiemannianIsometry I J (f ∘ Opens.inclusion hW₁W) := by
    have h := ((g.restrictOpenTangentSpace W₁).isLocalRiemannianIsometry_rescale_iff gN
      (hc.comp contMDiff_subtypeVal) (fun y ↦ hc_pos y.val) hh hh_pos fun y ↦ by
        have hGy : G y.val = extend Subtype.val lW 0 y.val := (hV_sub y.val y.property).1.1
        have hext : extend Subtype.val lW 0 y.val = lW (Opens.inclusion hW₁W y) :=
          Subtype.val_injective.extend_apply lW 0 (Opens.inclusion hW₁W y)
        simp only [Function.comp_apply, c, hGy, hext, lW, Real.exp_log (hh_pos _)]).2 hfW₁
    rw [hres_W₁] at h
    exact h
  refine ⟨c, hc, hc_pos, eventually_of_mem (hV_open.mem_nhds hxV) fun y hy ↦ ?_⟩
  obtain ⟨y', hy'UW, hy'eq⟩ := (hV_sub y hy).2
  have hyW₁ : Opens.inclusion hW₁W ⟨y, hy⟩ ∈ U_W :=
    (Subtype.ext hy'eq : y' = Opens.inclusion hW₁W ⟨y, hy⟩) ▸ hy'UW
  exact ((g₁.isLocalRiemannianIsometry_restrictOpenTangentSpace W₁).curvatureTensor_eq_zero_iff
      ⟨y, hy⟩).2
    ((hf₁.curvatureTensor_eq_zero_iff ⟨y, hy⟩).1 (hUW_flat _ hyW₁))

/-- **Locality of `IsLocallyConformallyFlat` on open covers.** A smooth Riemannian metric `g` is
locally conformally flat if and only if every point belongs to an open subset `W` on which the
restricted metric `g|_W` is locally conformally flat. -/
theorem isLocallyConformallyFlat_iff_forall_exists_opens
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    g.IsLocallyConformallyFlat ↔
      ∀ x : M, ∃ W : Opens M, x ∈ W ∧ (g.restrictOpenTangentSpace W).IsLocallyConformallyFlat := by
  refine ⟨fun hg x ↦ ⟨⊤, trivial, hg.restrictOpenTangentSpace ⊤⟩, fun h ↦ ?_⟩
  rw [g.isLocallyConformallyFlat_iff]
  intro x
  obtain ⟨W, hxW, hgW⟩ := h x
  exact g.exists_eventually_curvatureTensor_rescale_eq_zero_of_isLocalRiemannianIsometry hxW
    (g.restrictOpenTangentSpace W) hgW
    (letI : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
      ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
     TauCeti.IsLocalRiemannianIsometry.id I W)

/-- Pulling back a locally conformally flat metric along a smooth map whose differential is
invertible at every point yields a locally conformally flat metric. -/
theorem IsLocallyConformallyFlat.pullback_of_isInvertible
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N] [IsManifold J ∞ N]
    {gN : ContMDiffRiemannianMetric J ∞ F (fun z : N ↦ TangentSpace J z)}
    (hgN : gN.IsLocallyConformallyFlat) {f : M → N} (hf : ContMDiff I J ∞ f)
    (hinv : ∀ x, (mfderiv I J f x).IsInvertible) :
    (gN.pullback f (by simpa using hf) fun x ↦ (hinv x).injective).IsLocallyConformallyFlat := by
  rw [isLocallyConformallyFlat_iff]
  intro x
  obtain ⟨h, hh, hh_pos, hflat⟩ := (gN.isLocallyConformallyFlat_iff).1 hgN (f x)
  have hhf : ContMDiff I 𝓘(ℝ) ∞ (h ∘ f) := hh.comp hf
  have hhf_pos (y : M) : 0 < (h ∘ f) y := hh_pos (f y)
  have hinj : ∀ y, Injective (mfderiv I J f y) := fun y ↦ (hinv y).injective
  have hpull_eq : (gN.pullback f (by simpa using hf) hinj).rescale (h ∘ f) hhf hhf_pos =
      (gN.rescale h hh hh_pos).pullback f (by simpa using hf) hinj := by
    ext y u v
    simp
  refine ⟨h ∘ f, hhf, hhf_pos, (hf.continuous.continuousAt.eventually hflat).mono fun y hy ↦ ?_⟩
  let gN₁ := gN.rescale h hh hh_pos
  let gM₁ := gN₁.pullback f (by simpa using hf) hinj
  let _ : RiemannianBundle (fun z : N ↦ TangentSpace J z) := ⟨gN₁.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle J ∞ F (fun z : N ↦ TangentSpace J z) :=
    ⟨gN₁.inner, gN₁.contMDiff, fun _ _ _ ↦ rfl⟩
  let _ : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨gM₁.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun z : M ↦ TangentSpace I z) :=
    ⟨gM₁.inner, gM₁.contMDiff, fun _ _ _ ↦ rfl⟩
  have hiso : TauCeti.IsLocalRiemannianIsometry I J f :=
    gN₁.isLocalRiemannianIsometry_pullback_of_isInvertible hf hinv
  exact (curvatureTensor_leviCivitaConnection_eq_of_riemannianBundle_eq
    (by rw [hpull_eq]; rfl) y).trans
    ((hiso.curvatureTensor_eq_zero_iff y).1 hy)

/-- Pulling back a locally conformally flat metric along a diffeomorphism preserves local conformal
flatness. -/
theorem IsLocallyConformallyFlat.pullback
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N] [IsManifold J ∞ N]
    {gN : ContMDiffRiemannianMetric J ∞ F (fun z : N ↦ TangentSpace J z)}
    (hgN : gN.IsLocallyConformallyFlat) (Φ : M ≃ₘ^∞⟮I, J⟯ N) :
    (gN.pullback Φ (by simpa using Φ.contMDiff)
      fun _ ↦ (Φ.isInvertible_mfderiv (by simp)).injective).IsLocallyConformallyFlat :=
  hgN.pullback_of_isInvertible Φ.contMDiff fun _ ↦ Φ.isInvertible_mfderiv (by simp)

/-! ### Conformal Euclidean coordinate charts -/

open scoped TauCeti in
/-- **Conformal Euclidean-ball charts around an interior point.** Let `g` be a locally conformally
flat metric on `M` and `F` a finite-dimensional real inner-product space of the same dimension as
`E`. Then inside any neighbourhood `U ∈ 𝓝 x₀` of an interior point `x₀`, there exist a radius
`r > 0`, a globally smooth positive function `c : M → ℝ`, and a smooth partial diffeomorphism
`e : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞` with `x₀ ∈ e.source`, `e.source ⊆ U`,
`e.target = Metric.ball 0 r`, `e x₀ = 0`, and
`g.inner y u v = c y * ⟪mfderiv I 𝓘(ℝ, F) e y u, mfderiv I 𝓘(ℝ, F) e y v⟫_ℝ` on `e.source`. -/
theorem IsLocallyConformallyFlat.exists_partialDiffeomorph_ball_of_isInteriorPoint
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsLocallyConformallyFlat) (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) {U : Set M} (hU : U ∈ 𝓝 x₀) :
    ∃ (r : ℝ) (_ : 0 < r) (c : M → ℝ) (_ : ContMDiff I 𝓘(ℝ) ∞ c) (_ : ∀ y, 0 < c y)
      (e : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞),
      x₀ ∈ e.source ∧ e.source ⊆ U ∧ e.target = Metric.ball 0 r ∧ e x₀ = 0 ∧
        ∀ y ∈ e.source, ∀ u v : TangentSpace I y,
          g.inner y u v = c y * ⟪mfderiv I 𝓘(ℝ, F) e y u, mfderiv I 𝓘(ℝ, F) e y v⟫_ℝ := by
  obtain ⟨f, hf, hf_pos, hflat⟩ := (g.isLocallyConformallyFlat_iff).1 hg x₀
  let g₁ := g.rescale f hf hf_pos
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    ⟨g₁.inner, g₁.contMDiff, fun _ _ _ ↦ rfl⟩
  let L : TangentSpace I x₀ ≃ₗᵢ[ℝ] F :=
    (stdOrthonormalBasis ℝ (TangentSpace I x₀)).equiv (stdOrthonormalBasis ℝ F)
      (finCongr ((TauCeti.finrank_tangentSpace x₀).trans hdim))
  obtain ⟨W, hx₀W, r, hr, Ψ, hWU, hΨ0, -⟩ :=
    TauCeti.exists_riemannianIsometry_ball_of_eventually_curvatureTensor_eq_zero_of_isInteriorPoint
      hx₀ hflat hU L
  have hW : Nonempty W := ⟨⟨x₀, hx₀W⟩⟩
  have hB : Nonempty (⟨Metric.ball (0 : F) r, Metric.isOpen_ball⟩ : Opens F) :=
    ⟨Ψ ⟨x₀, hx₀W⟩⟩
  let e := Ψ.toDiffeomorph.toPartialDiffeomorph.liftOpens hW hB
  have he_src : e.source = W := by
    simp [e, Diffeomorph.toPartialDiffeomorph_toPartialEquiv]
  have he_tgt : e.target = Metric.ball 0 r := by
    ext z
    simp [e, Diffeomorph.toPartialDiffeomorph_toPartialEquiv]
  have he_apply (x : W) : e x = (Ψ x : F) := by
    simp [e, Diffeomorph.toPartialDiffeomorph_toPartialEquiv]
  have he_x₀ : e x₀ = 0 := (he_apply ⟨x₀, hx₀W⟩).trans hΨ0
  have hc : ContMDiff I 𝓘(ℝ) ∞ fun y ↦ (f y)⁻¹ := hf.inv₀ fun y ↦ (hf_pos y).ne'
  have hc_pos (y : M) : 0 < (f y)⁻¹ := inv_pos.2 (hf_pos y)
  refine ⟨r, hr, fun y ↦ (f y)⁻¹, hc, hc_pos, e, he_src ▸ hx₀W, he_src ▸ hWU, he_tgt, he_x₀,
    fun y hy u v ↦ ?_⟩
  have hyW : y ∈ W := by rwa [he_src] at hy
  have hinner_eq :
      ⟪mfderiv I 𝓘(ℝ, F) e y u, mfderiv I 𝓘(ℝ, F) e y v⟫_ℝ = f y * g.inner y u v := by
    calc ⟪mfderiv I 𝓘(ℝ, F) e y u, mfderiv I 𝓘(ℝ, F) e y v⟫_ℝ
        = ⟪u, v⟫_ℝ := Ψ.inner_mfderiv_liftOpens hW hB hyW u v
      _ = g₁.inner y u v := inner_riemannianBundle g₁ y u v
      _ = f y * g.inner y u v := g.rescale_inner f hf hf_pos y u v
  rw [hinner_eq, inv_mul_cancel_left₀ (hf_pos y).ne']

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- A conformal partial diffeomorphism `e` into `F` induces a local Riemannian isometry on any open
subset `W ⊆ e.source` where `hF ∘ e = c`. -/
private theorem isLocalRiemannianIsometry_partialDiffeomorph_rescale
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (e : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞) {W : Opens M} (hWe : (W : Set M) ⊆ e.source)
    {c : M → ℝ}
    (hinner : ∀ y ∈ e.source, ∀ u v : TangentSpace I y,
      g.inner y u v = c y * ⟪mfderiv I 𝓘(ℝ, F) e y u, mfderiv I 𝓘(ℝ, F) e y v⟫_ℝ)
    {hF : F → ℝ} (hhF : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ hF) (hhF_pos : ∀ z, 0 < hF z)
    (hhe : ∀ y : W, hF (e y.val) = c y.val) :
    letI : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
      ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
    letI : RiemannianBundle (fun z : F ↦ TangentSpace 𝓘(ℝ, F) z) :=
      ⟨(((riemannianMetricVectorSpace F).ofLE le_top).rescale hF hhF hhF_pos).toRiemannianMetric⟩
    TauCeti.IsLocalRiemannianIsometry I 𝓘(ℝ, F) (e ∘ (Subtype.val : W → M)) := by
  let gF := ((riemannianMetricVectorSpace F).ofLE le_top).rescale hF hhF hhF_pos
  let _ : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
    ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
  let _ : RiemannianBundle (fun z : F ↦ TangentSpace 𝓘(ℝ, F) z) := ⟨gF.toRiemannianMetric⟩
  have hmf (y : W) :
      mfderiv I 𝓘(ℝ, F) (e ∘ (Subtype.val : W → M)) y =
        (mfderiv I 𝓘(ℝ, F) e y.val).comp
          (tangentSpaceOpenEquiv (I := I) y).toContinuousLinearMap := by
    rw [mfderiv_comp y
      ((e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (hWe y.property))).mdifferentiableAt
        (by simp))
      ((contMDiff_subtypeVal (n := ∞)).mdifferentiableAt (by simp)), mfderiv_subtype_val]
  refine
    { contMDiff := fun y ↦
        (e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (hWe y.property))).comp y
          contMDiff_subtypeVal.contMDiffAt
      isInvertible_mfderiv := fun y ↦ by
        rw [hmf y, ContinuousLinearMap.isInvertible_comp_equiv]
        exact (e.isLocalDiffeomorphAt I 𝓘(ℝ, F) ∞ (hWe y.property)).isInvertible_mfderiv (by simp)
      inner_mfderiv := fun y u v ↦ ?_ }
  rw [inner_riemannianBundle gF, inner_riemannianBundle (g.restrictOpenTangentSpace W)]
  simp only [Function.comp_apply, gF, rescale_inner, ofLE_inner, hmf y,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hhe y,
    restrictOpenTangentSpace_inner, hinner y.val (hWe y.property),
    ← inner_riemannianBundle (riemannianMetricVectorSpace F)]

/-- **Conformal charts into a real inner-product space imply local conformal flatness.** Suppose
every point `x : M` lies in the source of a smooth partial diffeomorphism `e` into `F` on which `g`
is a smooth positive multiple `c` of the pulled-back Euclidean metric. Then `g` is locally
conformally flat. No boundaryless assumption on `M` is needed. -/
theorem isLocallyConformallyFlat_of_forall_exists_partialDiffeomorph
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (h : ∀ x : M, ∃ (e : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞) (c : M → ℝ),
      x ∈ e.source ∧ ContMDiffOn I 𝓘(ℝ) ∞ c e.source ∧ (∀ y ∈ e.source, 0 < c y) ∧
        ∀ y ∈ e.source, ∀ u v : TangentSpace I y,
          g.inner y u v = c y * ⟪mfderiv I 𝓘(ℝ, F) e y u, mfderiv I 𝓘(ℝ, F) e y v⟫_ℝ) :
    g.IsLocallyConformallyFlat := by
  rw [g.isLocallyConformallyFlat_iff]
  intro x
  obtain ⟨e, c, hx, hc_on, hc_pos, hinner⟩ := h x
  have hl_on : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ) ∞ (fun z ↦ Real.log (c (e.symm z))) e.target :=
    fun z hz ↦ (((hc_on.comp e.symm.contMDiffOn e.symm.mapsTo).contMDiffAt
      (e.open_target.mem_nhds hz)).log (hc_pos _ (e.map_target hz)).ne').contMDiffWithinAt
  obtain ⟨G, hG_eq⟩ := hl_on.exists_contMDiffMap_eventuallyEq (n := (⊤ : ℕ∞))
    (e.open_target.mem_nhds (e.map_source hx))
  let hF (z : F) : ℝ := Real.exp (G z)
  have hhF : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ hF := Real.contDiff_exp.comp_contMDiff G.contMDiff
  have hhF_pos (z : F) : 0 < hF z := Real.exp_pos _
  obtain ⟨V_F, hVF_sub, hVF_open, hexVF⟩ :=
    eventually_nhds_iff.1 (hG_eq.and (e.open_target.mem_nhds (e.map_source hx)))
  let W : Opens M :=
    ⟨e.source ∩ e ⁻¹' V_F, e.contMDiffOn.continuousOn.isOpen_inter_preimage e.open_source hVF_open⟩
  have hf_iso := isLocalRiemannianIsometry_partialDiffeomorph_rescale g e
    (W := W) inter_subset_left hinner hhF hhF_pos fun y ↦ by
      have hGe : G (e y.val) = Real.log (c (e.symm (e y.val))) := (hVF_sub (e y.val) y.property.2).1
      have hleft : e.symm (e y.val) = y.val := e.left_inv y.property.1
      simp only [hF, hGe, hleft, Real.exp_log (hc_pos y.val y.property.1)]
  exact g.exists_eventually_curvatureTensor_rescale_eq_zero_of_isLocalRiemannianIsometry
    (W := W) ⟨hx, hexVF⟩ (((riemannianMetricVectorSpace F).ofLE le_top).rescale hF hhF hhF_pos)
    (isLocallyConformallyFlat_rescale_model_space hhF hhF_pos) hf_iso

section Boundaryless

variable [BoundarylessManifold I M]

/-- **Conformal Euclidean-ball charts on a boundaryless manifold.** -/
theorem IsLocallyConformallyFlat.exists_partialDiffeomorph_ball
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsLocallyConformallyFlat) (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {x₀ : M} {U : Set M} (hU : U ∈ 𝓝 x₀) :
    ∃ (r : ℝ) (_ : 0 < r) (c : M → ℝ) (_ : ContMDiff I 𝓘(ℝ) ∞ c) (_ : ∀ y, 0 < c y)
      (e : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞),
      x₀ ∈ e.source ∧ e.source ⊆ U ∧ e.target = Metric.ball 0 r ∧ e x₀ = 0 ∧
        ∀ y ∈ e.source, ∀ u v : TangentSpace I y,
          g.inner y u v = c y * ⟪mfderiv I 𝓘(ℝ, F) e y u, mfderiv I 𝓘(ℝ, F) e y v⟫_ℝ :=
  hg.exists_partialDiffeomorph_ball_of_isInteriorPoint hdim BoundarylessManifold.isInteriorPoint hU

/-- **Conformal-chart characterization of local conformal flatness.** On a boundaryless smooth
manifold `M`, a metric `g` is locally conformally flat if and only if every point lies in the source
of a smooth partial diffeomorphism into a real inner-product space `F` of the same dimension on
which `g` is a smooth positive multiple of the pulled-back inner product. -/
theorem isLocallyConformallyFlat_iff_forall_exists_partialDiffeomorph
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    g.IsLocallyConformallyFlat ↔
      ∀ x : M, ∃ (e : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞) (c : M → ℝ),
        x ∈ e.source ∧ ContMDiffOn I 𝓘(ℝ) ∞ c e.source ∧ (∀ y ∈ e.source, 0 < c y) ∧
          ∀ y ∈ e.source, ∀ u v : TangentSpace I y,
            g.inner y u v = c y * ⟪mfderiv I 𝓘(ℝ, F) e y u, mfderiv I 𝓘(ℝ, F) e y v⟫_ℝ := by
  refine ⟨fun hg x ↦ ?_, g.isLocallyConformallyFlat_of_forall_exists_partialDiffeomorph⟩
  obtain ⟨_, -, c, hc, hc_pos, e, hx, -, -, -, hinner⟩ :=
    hg.exists_partialDiffeomorph_ball hdim univ_mem
  exact ⟨e, c, hx, hc.contMDiffOn, fun y _ ↦ hc_pos y, hinner⟩

/-- **Centred Euclidean-ball chart characterization of local conformal flatness.** On a boundaryless
smooth manifold `M`, a metric `g` is locally conformally flat if and only if around every point
`x : M` there exist `r > 0`, a globally smooth positive function `c : M → ℝ`, and a smooth partial
diffeomorphism `e` onto the open ball `B(0, r)` in `EuclideanSpace ℝ (Fin (Module.finrank ℝ E))`
sending `x` to `0` on which `g` is `c` times the pulled-back Euclidean inner product. -/
theorem isLocallyConformallyFlat_iff_forall_exists_partialDiffeomorph_ball
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    g.IsLocallyConformallyFlat ↔
      ∀ x : M, ∃ (r : ℝ) (_ : 0 < r) (c : M → ℝ) (_ : ContMDiff I 𝓘(ℝ) ∞ c) (_ : ∀ y, 0 < c y)
        (e : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞),
        x ∈ e.source ∧ e.target = Metric.ball 0 r ∧ e x = 0 ∧
          ∀ y ∈ e.source, ∀ u v : TangentSpace I y,
            g.inner y u v =
              c y * ⟪mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) e y u,
                mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) e y v⟫_ℝ := by
  refine ⟨fun hg x ↦ ?_, fun h ↦ g.isLocallyConformallyFlat_of_forall_exists_partialDiffeomorph
    (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) fun x ↦ ?_⟩
  · obtain ⟨r, hr, c, hc, hc_pos, e, hx, -, htarget, hex0, hinner⟩ :=
      hg.exists_partialDiffeomorph_ball
        (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (by simp) (x₀ := x) univ_mem
    exact ⟨r, hr, c, hc, hc_pos, e, hx, htarget, hex0, hinner⟩
  · obtain ⟨_, -, c, hc, hc_pos, e, hx, -, -, hinner⟩ := h x
    exact ⟨e, c, hx, hc.contMDiffOn, fun y _ ↦ hc_pos y, hinner⟩

end Boundaryless

end Bundle.ContMDiffRiemannianMetric
