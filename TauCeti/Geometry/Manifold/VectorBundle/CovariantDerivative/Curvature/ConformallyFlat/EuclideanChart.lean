/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ConformallyFlat.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Log
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Flat

/-!
# Conformal Euclidean coordinate charts and functoriality of local conformal flatness

A smooth Riemannian metric `g` on `M` is defined to be locally conformally flat
(`Bundle.ContMDiffRiemannianMetric.IsLocallyConformallyFlat`) if every point has a neighbourhood on
which a conformal rescaling `f g` by a positive smooth function `f` has vanishing curvature tensor.
Classically, on a manifold without boundary, local conformal flatness is equivalently defined by
requiring around every point a coordinate chart in which `g` is conformal to the Euclidean metric.

This file establishes the functoriality and locality properties of `IsLocallyConformallyFlat` and
proves the equivalence between the curvature definition and both Euclidean chart formulations, in
**every** dimension:

* **Pullbacks, restrictions, and locality:** `IsLocallyConformallyFlat` pulls back along any smooth
  map with everywhere invertible differential (`IsLocallyConformallyFlat.pullback_of_isInvertible`)
  and along diffeomorphisms (`IsLocallyConformallyFlat.pullback`,
  `isLocallyConformallyFlat_pullback_iff`), restricts to open submanifolds
  (`IsLocallyConformallyFlat.restrictOpenTangentSpace`), and is local with respect to open
  neighbourhoods (`isLocallyConformallyFlat_iff_forall_exists_opens`).
* **Isometry onto a Euclidean ball:** near any interior point `x₀`, existence of a flat conformal
  rescaling `f g` is equivalent to existence of an open neighbourhood `W` of `x₀`, a smooth positive
  `f : W → ℝ`, and a `TauCeti.RiemannianIsometry` from `(W, f g|_W)` onto an open ball around `0` in
  `EuclideanSpace ℝ (Fin (Module.finrank ℝ E))` sending `x₀` to `0`
  (`exists_eventually_curvatureTensor_rescale_eq_zero_iff_of_isInteriorPoint`), yielding the global
  characterization `isLocallyConformallyFlat_iff_exists_riemannianIsometry_ball` on boundaryless
  manifolds.
* **Pullback of a conformally Euclidean metric:** on a boundaryless manifold, `g` is locally
  conformally flat if and only if every point has an open neighbourhood `W` on which `g|_W` is the
  pullback along a local diffeomorphism into `EuclideanSpace ℝ (Fin (Module.finrank ℝ E))` of a
  globally conformally Euclidean metric
  (`isLocallyConformallyFlat_iff_exists_restrictOpenTangentSpace_eq_pullback_rescale`). The reverse
  implication uses `TauCeti.Manifold.isLocallyConformallyFlat_rescale_model_space` and holds even on
  manifolds with boundary
  (`isLocallyConformallyFlat_of_forall_exists_restrictOpenTangentSpace_eq_pullback_rescale`).

## Main results

In `Bundle.ContMDiffRiemannianMetric`:

* `IsLocallyConformallyFlat.pullback_of_isInvertible` and `IsLocallyConformallyFlat.pullback`
* `IsLocallyConformallyFlat.restrictOpenTangentSpace`
* `isLocallyConformallyFlat_pullback_iff`
* `isLocallyConformallyFlat_iff_forall_exists_opens`
* `exists_eventually_curvatureTensor_rescale_eq_zero_iff_of_isInteriorPoint`
* `isLocallyConformallyFlat_iff_exists_riemannianIsometry_ball`
* `isLocallyConformallyFlat_of_forall_exists_restrictOpenTangentSpace_eq_pullback_rescale`
* `isLocallyConformallyFlat_iff_exists_restrictOpenTangentSpace_eq_pullback_rescale`

## References

* L. P. Eisenhart, *Riemannian Geometry*, Princeton University Press (1926), §28.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 2.
-/

public section

open Bundle Filter Function Set TopologicalSpace
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

section Functoriality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [T2Space N] [IsManifold J ∞ N]

/-- Vanishing of the curvature tensor is preserved and reflected by a local Riemannian isometry. -/
private theorem curvatureTensor_eq_zero_iff_of_isLocalRiemannianIsometry
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
    [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
    {f : M → N} (hf : TauCeti.IsLocalRiemannianIsometry I J f) (x : M) :
    (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x = 0 ↔
      (CovariantDerivative.leviCivitaConnection J N).curvatureTensor (f x) = 0 := by
  constructor
  · intro h
    ext u v w
    obtain ⟨u, rfl⟩ := hf.mfderiv_surjective x u
    obtain ⟨v, rfl⟩ := hf.mfderiv_surjective x v
    obtain ⟨w, rfl⟩ := hf.mfderiv_surjective x w
    rw [← hf.mfderiv_curvatureTensor, h]
    simp
  · intro h
    ext u v w
    apply (hf.isInvertible_mfderiv x).injective
    rw [hf.mfderiv_curvatureTensor, h]
    simp

/-- The curvature tensor of a restricted smooth metric `g|_W` at `z ∈ W` vanishes if and only if
the curvature tensor of `g` vanishes at `z.1`. -/
private theorem curvatureTensor_restrictOpenTangentSpace_eq_zero_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (W : Opens M) (z : W) :
    (letI : RiemannianBundle (fun w : W ↦ TangentSpace I w) :=
        ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I W).curvatureTensor z = 0) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor (z : M) = 0) := by
  let _ : RiemannianBundle (fun w : W ↦ TangentSpace I w) :=
    ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun w : W ↦ TangentSpace I w) :=
    ⟨(g.restrictOpenTangentSpace W).inner, (g.restrictOpenTangentSpace W).contMDiff,
      fun _ _ _ ↦ rfl⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  exact curvatureTensor_eq_zero_iff_of_isLocalRiemannianIsometry
    (g.isLocalRiemannianIsometry_restrictOpenTangentSpace W) z

/-- Two smooth metrics whose inner products agree near `x` have vanishing curvature tensor at `x`
simultaneously. -/
private theorem curvatureTensor_eq_zero_iff_of_eventually_inner_eq
    {g₁ g₂ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {x : M}
    (h : ∀ᶠ y in 𝓝 x, g₁.inner y = g₂.inner y) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x = 0) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₂.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x = 0) := by
  obtain ⟨U, hU, hUo, hxU⟩ := eventually_nhds_iff.1 h
  let W : Opens M := ⟨U, hUo⟩
  have hres := restrictOpenTangentSpace_eq_of_inner_eq (g₁ := g₁) (g₂ := g₂) W hU
  refine (g₁.curvatureTensor_restrictOpenTangentSpace_eq_zero_iff W ⟨x, hxU⟩).symm.trans
    (Iff.trans ?_ (g₂.curvatureTensor_restrictOpenTangentSpace_eq_zero_iff W ⟨x, hxU⟩))
  rw [hres]

/-- A smooth positive function on an open subset `W` agrees near any `x ∈ W` with a globally smooth
positive function on `M`. -/
private theorem exists_contMDiff_pos_eventuallyEq_of_opens {W : Opens M} (x : W) {h : W → ℝ}
    (hh : ContMDiff I 𝓘(ℝ) ∞ h) (hh_pos : ∀ z, 0 < h z) :
    ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (_ : ∀ y, 0 < f y),
      ∀ᶠ z : W in 𝓝 x, f (z : M) = h z := by
  have hlog : ContMDiffOn I 𝓘(ℝ) (⊤ : ℕ∞) (extend Subtype.val (fun z ↦ Real.log (h z)) 0) W :=
    ContMDiffMap.contMDiffOn_extend W ⟨fun z ↦ Real.log (h z), hh.log fun z ↦ (hh_pos z).ne'⟩ 0
  obtain ⟨G, hG⟩ := hlog.exists_contMDiffMap_eventuallyEq (W.isOpen.mem_nhds x.2)
  refine ⟨fun y ↦ Real.exp (G y), Real.contDiff_exp.comp_contMDiff G.contMDiff,
    fun _ ↦ Real.exp_pos _, ?_⟩
  filter_upwards [(continuous_subtype_val.tendsto x).eventually hG] with z hz
  rw [hz, Subtype.val_injective.extend_apply _ _ z, Real.exp_log (hh_pos z)]

/-- Extending a local flattening factor `h : W → ℝ` on an open neighbourhood `W` of `x` yields a
global smooth positive factor `f : M → ℝ` flattening `g` near `x`. -/
private theorem exists_eventually_curvatureTensor_rescale_eq_zero_of_opens
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {W : Opens M} {x : M} (hxW : x ∈ W) {h : W → ℝ} (hh : ContMDiff I 𝓘(ℝ) ∞ h)
    (hh_pos : ∀ z, 0 < h z)
    (hflat : ∀ᶠ z in 𝓝 (⟨x, hxW⟩ : W),
      (letI : RiemannianBundle (fun w : W ↦ TangentSpace I w) :=
          ⟨((g.restrictOpenTangentSpace W).rescale h hh hh_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I W).curvatureTensor z) = 0) :
    ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ y, 0 < f y),
      ∀ᶠ y in 𝓝 x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 := by
  obtain ⟨f, hf, hf_pos, hfeq⟩ := exists_contMDiff_pos_eventuallyEq_of_opens ⟨x, hxW⟩ hh hh_pos
  have hWflat : ∀ᶠ z : W in 𝓝 ⟨x, hxW⟩,
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor (z : M)) = 0 := by
    filter_upwards [hfeq.eventually_nhds, hflat] with z hz hzf
    have hinner : ∀ᶠ w in 𝓝 z,
        ((g.rescale f hf hf_pos).restrictOpenTangentSpace W).inner w =
          ((g.restrictOpenTangentSpace W).rescale h hh hh_pos).inner w :=
      hz.mono fun w hw ↦ by
        ext u v
        rw [restrictOpenTangentSpace_inner, rescale_inner, rescale_inner,
          restrictOpenTangentSpace_inner, hw]
    exact ((g.rescale f hf hf_pos).curvatureTensor_restrictOpenTangentSpace_eq_zero_iff W z).1
      ((curvatureTensor_eq_zero_iff_of_eventually_inner_eq hinner).2 hzf)
  obtain ⟨S, hS, hSopen, hxS⟩ := eventually_nhds_iff.1 hWflat
  refine ⟨f, hf, hf_pos, eventually_nhds_iff.2 ⟨Subtype.val '' S, ?_,
    W.isOpen.isOpenMap_subtype_val S hSopen, ⟨⟨x, hxW⟩, hxS, rfl⟩⟩⟩
  rintro y ⟨z, hz, rfl⟩
  exact hS z hz

/-- **Pullback invariance of local conformal flatness.** The pullback of a locally conformally flat
metric along a smooth map with invertible differential at every point is locally conformally
flat. -/
theorem IsLocallyConformallyFlat.pullback_of_isInvertible
    {g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)}
    (hg : g.IsLocallyConformallyFlat) {f : M → N} (hf : ContMDiff I J (∞ + 1) f)
    (hinv : ∀ x, (mfderiv I J f x).IsInvertible) :
    (g.pullback f hf fun x ↦ (hinv x).injective).IsLocallyConformallyFlat := by
  rw [isLocallyConformallyFlat_iff] at hg ⊢
  intro x
  obtain ⟨h, hh, hh_pos, hflat⟩ := hg (f x)
  have hhf : ContMDiff I 𝓘(ℝ) ∞ (h ∘ f) := hh.comp (hf.of_le le_self_add)
  have hhf_pos (y : M) : 0 < (h ∘ f) y := hh_pos (f y)
  have heq : (g.pullback f hf fun x ↦ (hinv x).injective).rescale (h ∘ f) hhf hhf_pos =
      (g.rescale h hh hh_pos).pullback f hf (fun x ↦ (hinv x).injective) :=
    (g.pullback_rescale (f := f) (hf := hf) h hh hh_pos).symm
  let gN := g.rescale h hh hh_pos
  let gM := gN.pullback f hf fun x ↦ (hinv x).injective
  have hiso := gN.isLocalRiemannianIsometry_pullback_of_isInvertible hf hinv
  refine ⟨h ∘ f, hhf, hhf_pos,
    ((hf.of_le le_self_add).continuous.tendsto x |>.eventually hflat).mono fun y hy ↦ ?_⟩
  let _ : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨gM.toRiemannianMetric⟩
  let _ : RiemannianBundle (fun w : N ↦ TangentSpace J w) := ⟨gN.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun z : M ↦ TangentSpace I z) :=
    ⟨gM.inner, gM.contMDiff, fun _ _ _ ↦ rfl⟩
  have : IsContMDiffRiemannianBundle J ∞ F (fun w : N ↦ TangentSpace J w) :=
    ⟨gN.inner, gN.contMDiff, fun _ _ _ ↦ rfl⟩
  exact (curvatureTensor_leviCivitaConnection_eq_of_riemannianBundle_eq (by rw [heq]; rfl) y).trans
    ((curvatureTensor_eq_zero_iff_of_isLocalRiemannianIsometry hiso y).2 hy)

/-- The restriction of a locally conformally flat metric to an open submanifold is locally
conformally flat. -/
theorem IsLocallyConformallyFlat.restrictOpenTangentSpace
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsLocallyConformallyFlat) (U : Opens M) :
    (g.restrictOpenTangentSpace U).IsLocallyConformallyFlat := by
  rw [g.restrictOpenTangentSpace_eq_pullback U]
  exact hg.pullback_of_isInvertible contMDiff_subtype_val fun x ↦
    ⟨TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x,
      (TauCeti.Manifold.mfderiv_subtype_val x).symm⟩

/-- Pulling a metric back along a diffeomorphism preserves and reflects local conformal flatness. -/
@[simp]
theorem isLocallyConformallyFlat_pullback_iff
    (g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y))
    (Φ : M ≃ₘ^∞⟮I, J⟯ N) (hf : ContMDiff I J (∞ + 1) Φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J Φ x)) :
    (g.pullback Φ hf hinj).IsLocallyConformallyFlat ↔ g.IsLocallyConformallyFlat := by
  refine ⟨fun h ↦ ?_,
    fun h ↦ h.pullback_of_isInvertible hf fun _ ↦ Φ.isInvertible_mfderiv (by simp)⟩
  have hcomp : (g.pullback Φ hf hinj).pullback Φ.symm (Φ.symm.contMDiff.of_le (by simp))
      (fun _ ↦ (Φ.symm.isInvertible_mfderiv (by simp)).injective) = g := by
    rw [← g.pullback_comp Φ Φ.symm hf (Φ.symm.contMDiff.of_le (by simp)) hinj]
    have hid : (Φ : M → N) ∘ Φ.symm = id := funext Φ.apply_symm_apply
    ext y v w
    simp [hid]
  exact hcomp ▸ h.pullback_of_isInvertible (Φ.symm.contMDiff.of_le (by simp))
    fun _ ↦ Φ.symm.isInvertible_mfderiv (by simp)

/-- Pulling a locally conformally flat metric back along a diffeomorphism gives a locally
conformally flat metric. -/
theorem IsLocallyConformallyFlat.pullback
    {g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)}
    (hg : g.IsLocallyConformallyFlat) (Φ : M ≃ₘ^∞⟮I, J⟯ N) (hf : ContMDiff I J (∞ + 1) Φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J Φ x)) :
    (g.pullback Φ hf hinj).IsLocallyConformallyFlat :=
  (isLocallyConformallyFlat_pullback_iff g Φ hf hinj).2 hg

/-- **Locality of local conformal flatness.** A smooth Riemannian metric `g` is locally conformally
flat if and only if every point lies in an open subset on which the restriction of `g` is locally
conformally flat. -/
theorem isLocallyConformallyFlat_iff_forall_exists_opens
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    g.IsLocallyConformallyFlat ↔
      ∀ x : M, ∃ W : Opens M, x ∈ W ∧ (g.restrictOpenTangentSpace W).IsLocallyConformallyFlat := by
  refine ⟨fun hg x ↦ ⟨⊤, trivial, hg.restrictOpenTangentSpace ⊤⟩, fun hloc ↦ ?_⟩
  rw [g.isLocallyConformallyFlat_iff]
  intro x
  obtain ⟨W, hxW, hW⟩ := hloc x
  rw [isLocallyConformallyFlat_iff] at hW
  obtain ⟨h, hh, hh_pos, hflat⟩ := hW ⟨x, hxW⟩
  exact g.exists_eventually_curvatureTensor_rescale_eq_zero_of_opens hxW hh hh_pos hflat

end Functoriality

/-! ### Comparison with conformal Euclidean coordinate charts -/

section EuclideanCharts

open scoped TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- **Conformal Euclidean ball chart around an interior point.** At an interior point `x₀` of `M`,
existence of a conformal rescaling of `g` that is flat near `x₀` is equivalent, in every dimension,
to existence of an open neighbourhood `W` of `x₀`, a smooth positive factor `f : W → ℝ`, a radius
`r > 0`, and a `TauCeti.RiemannianIsometry` from `(W, f g|_W)` onto the Euclidean open ball
`Metric.ball 0 r ⊆ EuclideanSpace ℝ (Fin (Module.finrank ℝ E))` sending `x₀` to `0`. -/
theorem exists_eventually_curvatureTensor_rescale_eq_zero_iff_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) :
    (∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ y, 0 < f y),
      ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0) ↔
    ∃ (W : Opens M) (hx₀W : x₀ ∈ W) (f : W → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
      (hf_pos : ∀ z, 0 < f z) (r : ℝ) (_ : 0 < r),
      letI : RiemannianBundle (fun z : W ↦ TangentSpace I z) :=
        ⟨((g.restrictOpenTangentSpace W).rescale f hf hf_pos).toRiemannianMetric⟩
      ∃ Ψ : TauCeti.RiemannianIsometry I
          𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) W
          (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
            Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))),
        (Ψ ⟨x₀, hx₀W⟩ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0 := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  constructor
  · rintro ⟨f, hf, hf_pos, hflat⟩
    obtain ⟨W, hx₀W, r, hr, hΨ⟩ :=
      ((g.rescale f hf hf_pos
        ).eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff_of_isInteriorPoint hx₀).1
        hflat
    let fw : W → ℝ := f ∘ Subtype.val
    have hfw : ContMDiff I 𝓘(ℝ) ∞ fw := hf.comp contMDiff_subtype_val
    have hfw_pos (z : W) : 0 < fw z := hf_pos z.1
    have hres : (g.rescale f hf hf_pos).restrictOpenTangentSpace W =
        (g.restrictOpenTangentSpace W).rescale fw hfw hfw_pos := by
      ext z u v
      rw [restrictOpenTangentSpace_inner, rescale_inner, rescale_inner,
        restrictOpenTangentSpace_inner]
      rfl
    rw [hres] at hΨ
    exact ⟨W, hx₀W, fw, hfw, hfw_pos, r, hr, hΨ⟩
  · rintro ⟨W, hx₀W, f, hf, hf_pos, r, -, Ψ, -⟩
    refine g.exists_eventually_curvatureTensor_rescale_eq_zero_of_opens hx₀W hf hf_pos
      (Eventually.of_forall fun z ↦ ?_)
    let gW := (g.restrictOpenTangentSpace W).rescale f hf hf_pos
    let _ : RiemannianBundle (fun w : W ↦ TangentSpace I w) := ⟨gW.toRiemannianMetric⟩
    have : IsContMDiffRiemannianBundle I ∞ E (fun w : W ↦ TangentSpace I w) :=
      ⟨gW.inner, gW.contMDiff, fun _ _ _ ↦ rfl⟩
    let B : Opens F := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
    have hiso : TauCeti.IsLocalRiemannianIsometry I 𝓘(ℝ, F) ((Subtype.val : B → F) ∘ Ψ) :=
      (TauCeti.IsLocalRiemannianIsometry.subtype_val B).comp Ψ.isLocalRiemannianIsometry
    have : IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun v : F ↦ TangentSpace 𝓘(ℝ, F) v) :=
      ⟨(riemannianMetricVectorSpace F).inner,
        (riemannianMetricVectorSpace F).contMDiff.of_le le_top, fun _ _ _ ↦ rfl⟩
    exact (curvatureTensor_eq_zero_iff_of_isLocalRiemannianIsometry hiso z).2
      (TauCeti.Manifold.curvatureTensor_leviCivitaConnection_model_space _)

/-- **Characterization of local conformal flatness by Riemannian isometries onto Euclidean balls.**
On a boundaryless manifold of any dimension, a smooth metric `g` is locally conformally flat if and
only if every point `x` has an open neighbourhood `W` and a smooth positive factor `f : W → ℝ` such
that `(W, f g|_W)` admits a `TauCeti.RiemannianIsometry` onto an open ball around `0` in Euclidean
space sending `x` to `0`. -/
theorem isLocallyConformallyFlat_iff_exists_riemannianIsometry_ball [BoundarylessManifold I M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    g.IsLocallyConformallyFlat ↔
      ∀ x : M, ∃ (W : Opens M) (hxW : x ∈ W) (f : W → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
        (hf_pos : ∀ z, 0 < f z) (r : ℝ) (_ : 0 < r),
        letI : RiemannianBundle (fun z : W ↦ TangentSpace I z) :=
          ⟨((g.restrictOpenTangentSpace W).rescale f hf hf_pos).toRiemannianMetric⟩
        ∃ Ψ : TauCeti.RiemannianIsometry I
            𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) W
            (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
              Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))),
          (Ψ ⟨x, hxW⟩ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0 := by
  rw [g.isLocallyConformallyFlat_iff]
  exact forall_congr' fun _ ↦
    g.exists_eventually_curvatureTensor_rescale_eq_zero_iff_of_isInteriorPoint
      BoundarylessManifold.isInteriorPoint

/-- If every point of `M` lies in an open subset on which `g` pulls back a globally conformally
Euclidean metric along a smooth map with invertible differential, then `g` is locally conformally
flat. This direction holds without any boundaryless assumption on `M`. -/
theorem isLocallyConformallyFlat_of_forall_exists_restrictOpenTangentSpace_eq_pullback_rescale
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hchart : ∀ x : M, ∃ (W : Opens M) (_ : x ∈ W)
      (Φ : W → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
      (hΦ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (∞ + 1) Φ)
      (hinv : ∀ z,
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) Φ z).IsInvertible)
      (h : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
      (hh : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 𝓘(ℝ) ∞ h)
      (hh_pos : ∀ v, 0 < h v),
      g.restrictOpenTangentSpace W =
        (((riemannianMetricVectorSpace
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).ofLE le_top).rescale
          h hh hh_pos).pullback Φ hΦ (fun z ↦ (hinv z).injective)) :
    g.IsLocallyConformallyFlat := by
  refine (g.isLocallyConformallyFlat_iff_forall_exists_opens).2 fun x ↦ ?_
  obtain ⟨W, hxW, Φ, hΦ, hinv, h, hh, hh_pos, heq⟩ := hchart x
  exact ⟨W, hxW, heq ▸ (TauCeti.Manifold.isLocallyConformallyFlat_rescale_model_space hh
    hh_pos).pullback_of_isInvertible hΦ hinv⟩

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
/-- Compatibility of `tangentSpaceOpenEquiv` with the differential of an inclusion `W' → W` of
nested open subsets. -/
private theorem tangentSpaceOpenEquiv_mfderiv_opensInclusion {W' W : Opens M}
    (hUW : (W' : Set M) ⊆ W) (z : W') (w : TangentSpace I z) :
    TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) (⟨z.1, hUW z.2⟩ : W)
        (mfderiv I I (fun y : W' ↦ (⟨y.1, hUW y.2⟩ : W)) z w) =
      TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) z w := by
  let j : W' → W := fun y ↦ ⟨y.1, hUW y.2⟩
  have hj : ContMDiff I I ∞ j := (ContMDiff.subtypeVal_comp_iff W _).1 contMDiff_subtype_val
  have hc : mfderiv I I (Subtype.val : W' → M) z =
      (mfderiv I I (Subtype.val : W → M) (j z)).comp (mfderiv I I j z) :=
    mfderiv_comp z ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
      (hj.mdifferentiableAt (by simp))
  have hcw := congrArg (fun L ↦ L w) hc
  rw [ContinuousLinearMap.comp_apply, TauCeti.Manifold.mfderiv_subtype_val,
    TauCeti.Manifold.mfderiv_subtype_val] at hcw
  exact hcw.symm

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
/-- The differential of an inclusion `W' → W` of nested open subsets is invertible at every
point. -/
private theorem isInvertible_mfderiv_opensInclusion {W' W : Opens M}
    (hUW : (W' : Set M) ⊆ W) (z : W') :
    (mfderiv I I (fun y : W' ↦ (⟨y.1, hUW y.2⟩ : W)) z).IsInvertible :=
  ⟨(TauCeti.Manifold.tangentSpaceOpenEquiv z).trans
    (TauCeti.Manifold.tangentSpaceOpenEquiv (⟨z.1, hUW z.2⟩ : W)).symm, by
    ext u
    apply (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) (⟨z.1, hUW z.2⟩ : W)).injective
    rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply,
      tangentSpaceOpenEquiv_mfderiv_opensInclusion hUW z u]⟩

omit [T2Space M] in
/-- Given a Riemannian isometry `Ψ` from `(W, f g|_W)` onto an open subset `B` of Euclidean space
and a global positive function `h` on Euclidean space agreeing with `(f ∘ Ψ⁻¹)⁻¹` along `Ψ` on an
open subset `W' ⊆ W`, `g|_W'` is the pullback along `Subtype.val ∘ Ψ ∘ j` of `h · g_eucl`. -/
private theorem exists_pullback_rescale_of_riemannianIsometry_of_eq_inv
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {W W' : Opens M} (hUW : (W' : Set M) ⊆ W) {f : W → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hf_pos : ∀ z, 0 < f z) {B : Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (Ψ : letI : RiemannianBundle (fun z : W ↦ TangentSpace I z) :=
        ⟨((g.restrictOpenTangentSpace W).rescale f hf hf_pos).toRiemannianMetric⟩
      TauCeti.RiemannianIsometry I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) W B)
    {h : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hh : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 𝓘(ℝ) ∞ h)
    (hh_pos : ∀ v, 0 < h v)
    (hhf : ∀ z : W', h (Ψ ⟨z.1, hUW z.2⟩) = (f ⟨z.1, hUW z.2⟩)⁻¹) :
    ∃ (Φ : W' → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
      (hΦ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (∞ + 1) Φ)
      (hinv : ∀ z,
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) Φ z).IsInvertible),
      g.restrictOpenTangentSpace W' =
        (((riemannianMetricVectorSpace
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).ofLE le_top).rescale
          h hh hh_pos).pullback Φ hΦ (fun z ↦ (hinv z).injective) := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let _ : RiemannianBundle (fun z : W ↦ TangentSpace I z) :=
    ⟨((g.restrictOpenTangentSpace W).rescale f hf hf_pos).toRiemannianMetric⟩
  let j : W' → W := fun z ↦ ⟨z.1, hUW z.2⟩
  have hj : ContMDiff I I ∞ j := (ContMDiff.subtypeVal_comp_iff W _).1 contMDiff_subtype_val
  have hΨcont := Ψ.isLocalRiemannianIsometry.contMDiff
  have hιB := TauCeti.IsLocalRiemannianIsometry.subtype_val (I := 𝓘(ℝ, F)) B
  let Φ : W' → F := (Subtype.val : B → F) ∘ Ψ ∘ j
  have hΦ : ContMDiff I 𝓘(ℝ, F) (∞ + 1) Φ :=
    (contMDiff_subtype_val.comp (hΨcont.comp hj)).of_le (by simp)
  have hmf (z : W') : mfderiv I 𝓘(ℝ, F) Φ z =
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (Subtype.val : B → F) (Ψ (j z))).comp
        ((mfderiv I 𝓘(ℝ, F) Ψ (j z)).comp (mfderiv I I j z)) := by
    rw [show Φ = (Subtype.val : B → F) ∘ (Ψ ∘ j) from rfl,
      mfderiv_comp z ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
        ((hΨcont.comp hj).mdifferentiableAt (by simp)),
      mfderiv_comp z (hΨcont.mdifferentiableAt (by simp)) (hj.mdifferentiableAt (by simp))]
    rfl
  have hinv (z : W') : (mfderiv I 𝓘(ℝ, F) Φ z).IsInvertible := by
    rw [hmf z]
    exact (hιB.isInvertible_mfderiv (Ψ (j z))).comp
      ((Ψ.isLocalRiemannianIsometry.isInvertible_mfderiv (j z)).comp
        (isInvertible_mfderiv_opensInclusion hUW z))
  refine ⟨Φ, hΦ, hinv, ?_⟩
  ext z u v
  have hhz : h (Φ z) = (f (j z))⁻¹ := hhf z
  have heucl : (riemannianMetricVectorSpace F).inner (Φ z)
      (mfderiv I 𝓘(ℝ, F) Φ z u) (mfderiv I 𝓘(ℝ, F) Φ z v) =
      f (j z) * (g.restrictOpenTangentSpace W').inner z u v := by
    calc (riemannianMetricVectorSpace F).inner (Φ z)
          (mfderiv I 𝓘(ℝ, F) Φ z u) (mfderiv I 𝓘(ℝ, F) Φ z v)
        = ⟪mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (Subtype.val : B → F) (Ψ (j z))
              (mfderiv I 𝓘(ℝ, F) Ψ (j z) (mfderiv I I j z u)),
            mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (Subtype.val : B → F) (Ψ (j z))
              (mfderiv I 𝓘(ℝ, F) Ψ (j z) (mfderiv I I j z v))⟫_ℝ := by
          simp only [hmf z, ContinuousLinearMap.comp_apply]; rfl
      _ = ((g.restrictOpenTangentSpace W).rescale f hf hf_pos).inner (j z)
            (mfderiv I I j z u) (mfderiv I I j z v) :=
          (hιB.inner_mfderiv (Ψ (j z)) _ _).trans (Ψ.inner_mfderiv (j z) _ _)
      _ = f (j z) * (g.restrictOpenTangentSpace W').inner z u v := by
          rw [rescale_inner, restrictOpenTangentSpace_inner, restrictOpenTangentSpace_inner,
            tangentSpaceOpenEquiv_mfderiv_opensInclusion hUW z u,
            tangentSpaceOpenEquiv_mfderiv_opensInclusion hUW z v]
  rw [pullback_inner, rescale_inner, ofLE_inner, hhz, heucl,
    inv_mul_cancel_left₀ (hf_pos (j z)).ne']

omit [T2Space M] in
/-- Construct a conformal Euclidean coordinate chart on a shrunk open neighbourhood `W' ⊆ W` of `x`
from a Riemannian isometry `Ψ` of `(W, f g|_W)` onto an open subset `B` of Euclidean space. -/
private theorem exists_restrictOpenTangentSpace_eq_pullback_rescale_of_riemannianIsometry
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {W : Opens M} {x : M} (hxW : x ∈ W) {f : W → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hf_pos : ∀ z, 0 < f z) {B : Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (Ψ : letI : RiemannianBundle (fun z : W ↦ TangentSpace I z) :=
        ⟨((g.restrictOpenTangentSpace W).rescale f hf hf_pos).toRiemannianMetric⟩
      TauCeti.RiemannianIsometry I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) W B) :
    ∃ (W' : Opens M) (_ : x ∈ W')
      (Φ : W' → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
      (hΦ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (∞ + 1) Φ)
      (hinv : ∀ z,
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) Φ z).IsInvertible)
      (h : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
      (hh : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 𝓘(ℝ) ∞ h)
      (hh_pos : ∀ v, 0 < h v),
      g.restrictOpenTangentSpace W' =
        (((riemannianMetricVectorSpace
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).ofLE le_top).rescale
          h hh hh_pos).pullback Φ hΦ (fun z ↦ (hinv z).injective) := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let _ : RiemannianBundle (fun z : W ↦ TangentSpace I z) :=
    ⟨((g.restrictOpenTangentSpace W).rescale f hf hf_pos).toRiemannianMetric⟩
  let k : B → ℝ := fun y ↦ (f (Ψ.symm y))⁻¹
  have hk : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ k :=
    (hf.comp Ψ.symm.isLocalRiemannianIsometry.contMDiff).inv₀ fun y ↦ (hf_pos (Ψ.symm y)).ne'
  obtain ⟨h, hh, hh_pos, hheq⟩ := exists_contMDiff_pos_eventuallyEq_of_opens
    (Ψ ⟨x, hxW⟩) hk (fun y ↦ inv_pos.2 (hf_pos (Ψ.symm y)))
  obtain ⟨S, hS, hSopen, hxS⟩ := eventually_nhds_iff.1
    ((Ψ.isLocalRiemannianIsometry.contMDiff.continuous.tendsto ⟨x, hxW⟩).eventually hheq)
  let W' : Opens M := ⟨Subtype.val '' S, W.isOpen.isOpenMap_subtype_val S hSopen⟩
  have hUW : (W' : Set M) ⊆ W := by rintro _ ⟨w, -, rfl⟩; exact w.2
  have hhf (z : W') : h (Ψ ⟨z.1, hUW z.2⟩) = (f ⟨z.1, hUW z.2⟩)⁻¹ := by
    obtain ⟨w, hw, hwz⟩ := z.2
    have hw_eq : w = (⟨z.1, hUW z.2⟩ : W) := Subtype.ext hwz
    simpa [k, Ψ.symm_apply_apply] using hS ⟨z.1, hUW z.2⟩ (hw_eq ▸ hw)
  obtain ⟨Φ, hΦ, hinv, heq⟩ := g.exists_pullback_rescale_of_riemannianIsometry_of_eq_inv
    hUW hf hf_pos Ψ hh hh_pos hhf
  exact ⟨W', ⟨⟨x, hxW⟩, hxS, rfl⟩, Φ, hΦ, hinv, h, hh, hh_pos, heq⟩

/-- **Euclidean chart characterization of local conformal flatness.** On a boundaryless manifold of
any dimension, a smooth Riemannian metric `g` is locally conformally flat if and only if every point
lies in an open coordinate neighbourhood `W` on which `g|_W` is the pullback along a smooth map with
invertible differential into Euclidean space of a globally conformally Euclidean metric. -/
theorem isLocallyConformallyFlat_iff_exists_restrictOpenTangentSpace_eq_pullback_rescale
    [BoundarylessManifold I M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    g.IsLocallyConformallyFlat ↔
      ∀ x : M, ∃ (W : Opens M) (_ : x ∈ W)
        (Φ : W → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
        (hΦ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (∞ + 1) Φ)
        (hinv : ∀ z,
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) Φ z).IsInvertible)
        (h : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
        (hh : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 𝓘(ℝ) ∞ h)
        (hh_pos : ∀ v, 0 < h v),
        g.restrictOpenTangentSpace W =
          (((riemannianMetricVectorSpace
              (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).ofLE le_top).rescale
            h hh hh_pos).pullback Φ hΦ (fun z ↦ (hinv z).injective) := by
  refine ⟨fun hg x ↦ ?_,
    g.isLocallyConformallyFlat_of_forall_exists_restrictOpenTangentSpace_eq_pullback_rescale⟩
  obtain ⟨W, hxW, f, hf, hf_pos, _, _, Ψ, -⟩ :=
    (g.isLocallyConformallyFlat_iff_exists_riemannianIsometry_ball.1 hg) x
  exact g.exists_restrictOpenTangentSpace_eq_pullback_rescale_of_riemannianIsometry
    hxW hf hf_pos Ψ

end EuclideanCharts

end Bundle.ContMDiffRiemannianMetric
