/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ConformallyFlat.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Solvability
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.Instances.OpenBall.Diffeomorph
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Isometry.ConformalCurvature
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Polarization
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Divergence

/-!
# The Weyl–Schouten theorem on smooth Riemannian manifolds

Let `g` be a smooth Riemannian metric on a smooth manifold `M`. This file transports the Frobenius
integrability theory for the conformal flattening equation

`Hess φ = P + dφ ⊗ dφ - (|dφ|² / 2) g`

from a model vector space (`TauCeti.Manifold.exists_contDiff_hessian_eq_family_model_space`) to
interior points of `M`, and hence to every point when `M` is boundaryless, proving the
manifold-level **Weyl–Schouten theorem**:

* Around any interior point `x₀` near which the Weyl and Cotton tensors vanish, and around any
  initial jet `(c₀, ξ₀) : ℝ × TangentSpace I x₀`, there is a jointly smooth family `Φ (x, c, ξ)`
  whose slices solve the conformal flattening equation on a common open neighbourhood of `x₀` with
  `Φ (x₀, c, ξ) = c` and `grad (Φ (·, c, ξ)) x₀ = ξ`
  (`TauCeti.Manifold.exists_contMDiff_hessian_eq_family_of_isInteriorPoint`).
* Consequently, in **every** dimension, vanishing of the Weyl and Cotton tensors near an interior
  point `x₀` yields a smooth function `φ` with any prescribed value and gradient at `x₀` for which
  `e^(2φ) g` is flat near `x₀`
  (`exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint` in
  `Bundle.ContMDiffRiemannianMetric`). In dimensions `0` and `1` every metric is flat; in dimension
  `2` our totalized Schouten tensor is `0`, so `W = 0` means `g` is already flat and the conformal
  flattening equation has trace `Δφ = |∇φ|² - (|∇φ|² / 2) · 2 = 0`, keeping `Scal^(e^(2φ) g) = 0`.
* On a boundaryless manifold:
  - in dimension `n ≠ 2`, `g` is locally conformally flat if and only if both `W = 0` and `C = 0`
    (`isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero`);
  - in dimension `n ∉ {2, 3}` (in particular, `n ≥ 4`), `g` is locally conformally flat if and only
    if `W = 0` (`Bundle.ContMDiffRiemannianMetric.isLocallyConformallyFlat_iff_weylTensor_eq_zero`),
    since `div W = (n - 3) C` forces `C = 0` (and sufficiency holds for every `n ≠ 3`, including
    `n = 2` where our totalized `P = 0` makes `W = Rm`);
  - in dimension `n ≤ 3` with `n ≠ 2` (in particular, `n = 3`), `g` is locally conformally flat if
    and only if `C = 0`
    (`Bundle.ContMDiffRiemannianMetric.isLocallyConformallyFlat_iff_cottonTensor_eq_zero`), since
    `W = 0` identically in dimensions `0`, `1`, and `3`.

## Main results

* `TauCeti.Manifold.exists_contMDiff_hessian_eq_family_of_isInteriorPoint` and
  `TauCeti.Manifold.exists_contMDiff_hessian_eq_family`: smooth dependence on the initial jet
  `(c, ξ)` for local solutions of the conformal flattening equation on a manifold.
* `TauCeti.Manifold.exists_eventually_hessian_eq_of_isInteriorPoint` and
  `TauCeti.Manifold.exists_eventually_hessian_eq`: local existence with prescribed value and
  gradient at `x₀`.
* `exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint` and
  `exists_eventually_curvatureTensor_rescale_exp_eq_zero` (in `Bundle.ContMDiffRiemannianMetric`):
  local existence of a flat conformal rescaling `e^(2φ) g` with prescribed `(φ x₀, grad φ x₀)`.
* `isLocallyConformallyFlat_of_weylTensor_eq_zero_and_cottonTensor_eq_zero`,
  `isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero`,
  `isLocallyConformallyFlat_of_weylTensor_eq_zero`,
  `isLocallyConformallyFlat_iff_weylTensor_eq_zero`,
  `isLocallyConformallyFlat_of_cottonTensor_eq_zero`, and
  `isLocallyConformallyFlat_iff_cottonTensor_eq_zero` (in `Bundle.ContMDiffRiemannianMetric`): the
  manifold-level Weyl–Schouten theorems.

## References

* É. Cotton, *Sur les variétés à trois dimensions*, Ann. Fac. Sci. Toulouse (2) 1 (1899),
  385–438.
* J. A. Schouten, *Über die konforme Abbildung n-dimensionaler Mannigfaltigkeiten mit
  quadratischer Maßbestimmung auf eine Mannigfaltigkeit mit euklidischer Maßbestimmung*,
  Math. Z. 11 (1921), 58–88.
* L. P. Eisenhart, *Riemannian Geometry*, Princeton University Press (1926), §28.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 2.
-/

public section

open Bundle Filter Function Set TopologicalSpace
open scoped ContDiff InnerProductSpace Manifold TauCeti Topology

noncomputable section

namespace TauCeti.Manifold

section ChartTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

omit [T2Space M] in
/-- Around any interior point `x₀` of `M`, there is an open neighbourhood `W` of `x₀` diffeomorphic
to `EuclideanSpace ℝ (Fin (Module.finrank ℝ E))`. -/
private theorem exists_diffeomorph_opens_of_isInteriorPoint {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (W : Opens M) (_ : x₀ ∈ W),
      Nonempty (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
        ≃ₘ^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))), I⟯ W) := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  have hfin : Module.finrank ℝ F = Module.finrank ℝ E :=
    finrank_euclideanSpace_fin (n := Module.finrank ℝ E)
  let e : F ≃L[ℝ] E := (LinearEquiv.ofFinrankEq F E hfin).toContinuousLinearEquiv
  let φ := TauCeti.extChartPartialDiffeomorph I ∞ x₀
  have hx₀φ : x₀ ∈ φ.source := (TauCeti.mem_extChartPartialDiffeomorph_source I ∞ x₀).2 hx₀
  let A₀ : F ≃ₘ^∞⟮𝓘(ℝ, F), 𝓘(ℝ, E)⟯ E :=
    e.toDiffeomorph.trans (Diffeomorph.smulAdd ∞ (1 : ℝ) (φ x₀) one_ne_zero)
  have h0_mem : (0 : F) ∈ A₀ ⁻¹' φ.target := by simpa [A₀] using φ.map_source hx₀φ
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (φ.open_target.preimage A₀.continuous) 0 h0_mem
  let A : F ≃ₘ^∞⟮𝓘(ℝ, F), 𝓘(ℝ, E)⟯ E := (Diffeomorph.smulAdd ∞ δ (0 : F) hδ.ne').trans A₀
  have hA_sub : A '' (TauCeti.unitBallOpens F : Set F) ⊆ φ.target := by
    rintro _ ⟨v, hv, rfl⟩
    have hδv : Diffeomorph.smulAdd ∞ δ (0 : F) hδ.ne' v ∈ Metric.ball (0 : F) δ := by
      rw [Diffeomorph.smulAdd_apply, add_zero, Metric.mem_ball, dist_zero_right, norm_smul,
        Real.norm_of_nonneg hδ.le]
      exact mul_lt_of_lt_one_right hδ (TauCeti.mem_unitBallOpens.1 hv)
    exact hball hδv
  have hA_open : IsOpen (A '' (TauCeti.unitBallOpens F : Set F)) :=
    A.toHomeomorph.isOpenMap _ (TauCeti.unitBallOpens F).isOpen
  let ψ := φ.symm.restrOpen (A '' (TauCeti.unitBallOpens F : Set F)) hA_open
  have hψ_src : ψ.source = A '' (TauCeti.unitBallOpens F : Set F) :=
    (φ.symm.restrOpen_source hA_open).trans (inter_eq_right.2 hA_sub)
  have h_iff (v : F) :
      v ∈ TauCeti.unitBallOpens F ↔ A v ∈ (⟨ψ.source, ψ.open_source⟩ : Opens E) := by
    change v ∈ (TauCeti.unitBallOpens F : Set F) ↔ A v ∈ ψ.source
    rw [hψ_src]
    exact A.injective.mem_set_image.symm
  have hx₀W : x₀ ∈ ψ.target := by
    have hφx₀ : φ x₀ ∈ ψ.source :=
      hψ_src.symm ▸ ⟨0, TauCeti.zero_mem_unitBallOpens F, by simp [A, A₀]⟩
    have h1 : ψ (φ x₀) = x₀ :=
      (congrFun (φ.symm.coe_restrOpen hA_open) (φ x₀)).trans (φ.left_inv hx₀φ)
    exact h1 ▸ ψ.map_source hφx₀
  exact ⟨⟨ψ.target, ψ.open_target⟩, hx₀W,
    ⟨((TauCeti.unitBallDiffeomorph F).symm.trans (A.subtype h_iff)).trans
      ψ.toDiffeomorphSourceTarget⟩⟩

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
/-- The inclusion between nested open submanifolds is a local Riemannian isometry. -/
private theorem isLocalRiemannianIsometry_opensInclusion
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {U W : Opens M} (hUW : (U : Set M) ⊆ W) :
    IsLocalRiemannianIsometry I I (fun z : U ↦ (⟨z.1, hUW z.2⟩ : W)) := by
  let j : U → W := fun z ↦ ⟨z.1, hUW z.2⟩
  have hj : ContMDiff I I ∞ j := (ContMDiff.subtypeVal_comp_iff W _).1 contMDiff_subtype_val
  have hιU := IsLocalRiemannianIsometry.subtype_val (I := I) U
  have hιW := IsLocalRiemannianIsometry.subtype_val (I := I) W
  have hcomp (z : U) : (mfderiv I I (Subtype.val : W → M) (j z)).comp (mfderiv I I j z) =
      mfderiv I I (Subtype.val : U → M) z :=
    (mfderiv_comp z (hιW.mdifferentiableAt (j z)) (hj.mdifferentiableAt (by simp))).symm
  refine ⟨hj, fun z ↦ ?_, fun z v w ↦ ?_⟩
  · obtain ⟨eU, heU⟩ := hιU.isInvertible_mfderiv z
    obtain ⟨eW, heW⟩ := hιW.isInvertible_mfderiv (j z)
    refine ⟨eU.trans eW.symm, ?_⟩
    ext u
    apply eW.injective
    have hu := congrArg (fun L : TangentSpace I z →L[ℝ] TangentSpace I z.1 ↦ L u) (hcomp z)
    simpa [← heU, ← heW] using hu.symm
  · rw [← hιW.inner_mfderiv (j z), ← ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.comp_apply, hcomp z, hιU.inner_mfderiv z]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Given a Riemannian isometry `Ψ : W → F` from an open neighbourhood `W` of `x₀` onto a normed
space `F`, extend `Ψ` near `x₀` to a globally smooth map `α : M → F` that factors through a local
Riemannian isometry on a smaller open neighbourhood `U₁` of `x₀`. -/
private theorem exists_contMDiff_chart_extension {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [RiemannianBundle (fun y : F ↦ TangentSpace 𝓘(ℝ, F) y)]
    {W : Opens M} {x₀ : M} (hx₀W : x₀ ∈ W) (Ψ : RiemannianIsometry I 𝓘(ℝ, F) W F) :
    ∃ (α : M → F) (U₁ : Opens M) (_ : x₀ ∈ U₁), ContMDiff I 𝓘(ℝ, F) ∞ α ∧
      α x₀ = Ψ ⟨x₀, hx₀W⟩ ∧
      IsLocalRiemannianIsometry I 𝓘(ℝ, F) (α ∘ (Subtype.val : U₁ → M)) := by
  have hext : ContMDiffOn I 𝓘(ℝ, F) (⊤ : ℕ∞) (extend Subtype.val Ψ 0) W :=
    ContMDiffMap.contMDiffOn_extend W ⟨Ψ, Ψ.contMDiff⟩ 0
  obtain ⟨α, hαeq⟩ := hext.exists_contMDiffMap_eventuallyEq (W.isOpen.mem_nhds hx₀W)
  let U_set : Set M := interior {y ∈ (W : Set M) | α y = extend Subtype.val Ψ 0 y}
  have hx₀U : x₀ ∈ U_set :=
    mem_interior_iff_mem_nhds.2 (inter_mem (W.isOpen.mem_nhds hx₀W) hαeq)
  let U₁ : Opens M := ⟨U_set, isOpen_interior⟩
  have hU₁W : (U₁ : Set M) ⊆ W := fun _ hy ↦ (interior_subset hy).1
  let j : U₁ → W := fun z ↦ ⟨z.1, hU₁W z.2⟩
  have hcomp : (α ∘ (Subtype.val : U₁ → M)) = Ψ ∘ j := by
    funext z
    exact ((interior_subset z.2).2).trans (Subtype.val_injective.extend_apply Ψ 0 (j z))
  refine ⟨α, U₁, hx₀U, α.contMDiff, ?_, hcomp ▸ Ψ.isLocalRiemannianIsometry.comp
    (isLocalRiemannianIsometry_opensInclusion hU₁W)⟩
  exact ((interior_subset hx₀U).2).trans (Subtype.val_injective.extend_apply Ψ 0 ⟨x₀, hx₀W⟩)

/-- Vanishing of the Weyl and Cotton tensors near `x₀ ∈ W` transfers along a Riemannian isometry
`Ψ : W → F` to a neighbourhood of `Ψ ⟨x₀, hx₀W⟩`. -/
private theorem eventually_weylTensor_and_cottonTensor_eq_zero_of_riemannianIsometry
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [RiemannianBundle (fun y : F ↦ TangentSpace 𝓘(ℝ, F) y)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun y : F ↦ TangentSpace 𝓘(ℝ, F) y)]
    {W : Opens M} {x₀ : M} (hx₀W : x₀ ∈ W) (Ψ : RiemannianIsometry I 𝓘(ℝ, F) W F)
    (hW : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).weylTensor y = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).cottonTensor y = 0) :
    (∀ᶠ y in 𝓝 (Ψ ⟨x₀, hx₀W⟩),
      (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) F).weylTensor y = 0) ∧
    (∀ᶠ y in 𝓝 (Ψ ⟨x₀, hx₀W⟩),
      (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) F).cottonTensor y = 0) := by
  have hιW := IsLocalRiemannianIsometry.subtype_val (I := I) W
  have h0 : (Ψ.symm (Ψ ⟨x₀, hx₀W⟩) : M) = x₀ := congrArg Subtype.val (Ψ.symm_apply_apply _)
  have htend : Tendsto (fun y : F ↦ (Ψ.symm y : M)) (𝓝 (Ψ ⟨x₀, hx₀W⟩)) (𝓝 x₀) := by
    have ht := (continuous_subtype_val.comp
      Ψ.symm.isLocalRiemannianIsometry.contMDiff.continuous).tendsto (Ψ ⟨x₀, hx₀W⟩)
    rwa [Function.comp_apply, h0] at ht
  refine ⟨(htend.eventually hW).mono fun y hy ↦ ?_, (htend.eventually hC).mono fun y hy ↦ ?_⟩
  · exact (Ψ.symm.isLocalRiemannianIsometry.weylTensor_eq_zero_iff y).1
      ((hιW.weylTensor_eq_zero_iff (Ψ.symm y)).1 hy)
  · exact (Ψ.symm.isLocalRiemannianIsometry.cottonTensor_eq_zero_iff y).1
      ((hιW.cottonTensor_eq_zero_iff (Ψ.symm y)).1 hy)

omit [T2Space M] in
/-- Around any interior point `x₀` of `M`, there is an open neighbourhood `W` of `x₀`, a smooth
Riemannian metric `g_F` on `EuclideanSpace ℝ (Fin (Module.finrank ℝ E))`, and a Riemannian isometry
from `(W, g|_W)` to `g_F`. -/
private theorem exists_riemannianIsometry_euclideanSpace_of_isInteriorPoint
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (W : Opens M) (_ : x₀ ∈ W)
      (g_F : ContMDiffRiemannianMetric
        𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ↦
          TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) y)),
      letI : RiemannianBundle
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ↦
            TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) y) :=
        ⟨g_F.toRiemannianMetric⟩
      Nonempty (RiemannianIsometry I
        𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) W
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  obtain ⟨W, hx₀W, ⟨d⟩⟩ := exists_diffeomorph_opens_of_isInteriorPoint hx₀
  let g_W := contMDiffRiemannianMetricOpen (I := I) (n := ∞) W
  let g_F := g_W.pullback d (d.contMDiff.of_le (by simp))
    (fun v ↦ (d.isInvertible_mfderiv (by simp)).injective)
  let _ : RiemannianBundle (fun y : F ↦ TangentSpace 𝓘(ℝ, F) y) := ⟨g_F.toRiemannianMetric⟩
  let d_iso : RiemannianIsometry 𝓘(ℝ, F) I F W :=
    { toDiffeomorph := d
      inner_mfderiv' := fun v u w ↦ by
        rw [inner_tangentSpace_open, g_F.inner_riemannianBundle]
        dsimp only [g_F, g_W]
        rw [ContMDiffRiemannianMetric.pullback_inner, contMDiffRiemannianMetricOpen_inner] }
  exact ⟨W, hx₀W, g_F, ⟨d_iso.symm⟩⟩

/-- **Smooth dependence on the initial jet for the conformal flattening equation at an interior
point.** Let `M` be a smooth Riemannian manifold whose Weyl and Cotton tensors vanish near an
interior point `x₀`. Around every initial jet `(c₀, ξ₀) : ℝ × TangentSpace I x₀`, there exist open
neighbourhoods `V` of `x₀` and `Ω` of `(c₀, ξ₀)` and a jointly smooth function
`Φ : M × (ℝ × TangentSpace I x₀) → ℝ` whose slice `x ↦ Φ (x, c, ξ)` takes the value `c` and
gradient `ξ` at `x₀` and solves the conformal flattening equation on `V` for every `(c, ξ) ∈ Ω`. -/
theorem exists_contMDiff_hessian_eq_family_of_isInteriorPoint {x₀ : M} (hx₀ : I.IsInteriorPoint x₀)
    (hW : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).weylTensor y = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).cottonTensor y = 0)
    (c₀ : ℝ) (ξ₀ : TangentSpace I x₀) :
    ∃ (Φ : M × (ℝ × TangentSpace I x₀) → ℝ) (V : Set M) (Ω : Set (ℝ × TangentSpace I x₀)),
      IsOpen V ∧ x₀ ∈ V ∧ IsOpen Ω ∧ (c₀, ξ₀) ∈ Ω ∧
      ContMDiff (I.prod 𝓘(ℝ, ℝ × TangentSpace I x₀)) 𝓘(ℝ) ∞ Φ ∧
      (∀ c ξ, (c, ξ) ∈ Ω → Φ (x₀, c, ξ) = c) ∧
      (∀ c ξ, (c, ξ) ∈ Ω → mgradient I (fun x ↦ Φ (x, c, ξ)) x₀ = ξ) ∧
      ∀ y ∈ V, ∀ c ξ, (c, ξ) ∈ Ω → ∀ u v : TangentSpace I y,
        hessian I (fun x ↦ Φ (x, c, ξ)) y u v =
          (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm y
            (mgradient I (fun x ↦ Φ (x, c, ξ)) y) u v := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  obtain ⟨W, hx₀W, g_F, ⟨Ψ⟩⟩ := exists_riemannianIsometry_euclideanSpace_of_isInteriorPoint hx₀
  let _ : RiemannianBundle (fun y : F ↦ TangentSpace 𝓘(ℝ, F) y) := ⟨g_F.toRiemannianMetric⟩
  have _ : IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun y : F ↦ TangentSpace 𝓘(ℝ, F) y) :=
    ⟨g_F.inner, g_F.contMDiff, fun _ _ _ ↦ rfl⟩
  obtain ⟨α, U₁, hx₀U₁, hα, hα0, hαiso⟩ := exists_contMDiff_chart_extension hx₀W Ψ
  let z₀ : U₁ := ⟨x₀, hx₀U₁⟩
  let y₀ : F := (α ∘ (Subtype.val : U₁ → M)) z₀
  obtain ⟨hW_F, hC_F⟩ := hα0 ▸
    eventually_weylTensor_and_cottonTensor_eq_zero_of_riemannianIsometry hx₀W Ψ hW hC
  let L : TangentSpace I x₀ →L[ℝ] TangentSpace 𝓘(ℝ, F) y₀ :=
    (mfderiv I 𝓘(ℝ, F) (α ∘ (Subtype.val : U₁ → M)) z₀).comp
      (tangentSpaceOpenEquiv (I := I) z₀).symm.toContinuousLinearMap
  let P_map : (ℝ × TangentSpace I x₀) →L[ℝ] (ℝ × TangentSpace 𝓘(ℝ, F) y₀) :=
    (ContinuousLinearMap.id ℝ ℝ).prodMap L
  obtain ⟨Φ_F, V_F, Ω_F, hV_F, hy₀V_F, hΩ_F, hp₀Ω_F, hΦ_F, hval_F, hgrad_F, hsol_F⟩ :=
    exists_contDiff_hessian_eq_family_model_space hW_F hC_F c₀ (L ξ₀)
  let Φ : M × (ℝ × TangentSpace I x₀) → ℝ := fun q ↦ Φ_F (α q.1, P_map q.2)
  have hΦ : ContMDiff (I.prod 𝓘(ℝ, ℝ × TangentSpace I x₀)) 𝓘(ℝ) ∞ Φ :=
    hΦ_F.comp_contMDiff ((hα.comp contMDiff_fst).prodMk_space (P_map.contMDiff.comp contMDiff_snd))
  have hιU₁ := IsLocalRiemannianIsometry.subtype_val (I := I) U₁
  refine ⟨Φ, (U₁ : Set M) ∩ α ⁻¹' V_F, P_map ⁻¹' Ω_F,
    U₁.isOpen.inter (hV_F.preimage hα.continuous), ⟨hx₀U₁, hy₀V_F⟩,
    hΩ_F.preimage P_map.continuous, hp₀Ω_F, hΦ,
    fun c ξ hp ↦ hval_F c (L ξ) hp, fun c ξ hp ↦ ?_, fun y hy c ξ hp ↦ ?_⟩
  · let ψ : F → ℝ := fun w ↦ Φ_F (w, c, L ξ)
    have hψ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ ψ :=
      (hΦ_F.comp (contDiff_id.prodMk contDiff_const)).contMDiff
    have h1 := hαiso.mfderiv_mgradient_comp (x := z₀) (hψ.mdifferentiableAt (by simp))
    have h2 := hιU₁.mfderiv_mgradient_comp (x := z₀)
      ((hψ.comp hα).mdifferentiableAt (by simp))
    have hgrad_z₀ : mgradient I ((ψ ∘ α) ∘ (Subtype.val : U₁ → M)) z₀ =
        (tangentSpaceOpenEquiv (I := I) z₀).symm ξ :=
      (hαiso.isInvertible_mfderiv z₀).injective (h1.trans (hgrad_F c (L ξ) hp))
    rw [hgrad_z₀, mfderiv_subtype_val] at h2
    exact h2.symm.trans ((tangentSpaceOpenEquiv (I := I) z₀).apply_symm_apply ξ)
  · let ψ : F → ℝ := fun w ↦ Φ_F (w, c, L ξ)
    have hψ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ ψ :=
      (hΦ_F.comp (contDiff_id.prodMk contDiff_const)).contMDiff
    let z : U₁ := ⟨y, hy.1⟩
    exact (hιU₁.hessian_comp_eq_conformalFlatteningForm_iff (x := z)
      ((hψ.comp hα).contMDiffAt.of_le (by simp))).1
      ((hαiso.hessian_comp_eq_conformalFlatteningForm_iff (x := z)
        (hψ.contMDiffAt.of_le (by simp))).2 (hsol_F (α y) hy.2 c (L ξ) hp))

/-- **Smooth dependence on the initial jet for the conformal flattening equation on a boundaryless
manifold.** Around any point `x₀` near which the Weyl and Cotton tensors vanish, and any initial
jet `(c₀, ξ₀)`, there is a jointly smooth solution family `Φ (x, c, ξ)` solving the conformal
flattening equation on an open neighbourhood of `x₀` with `Φ (x₀, c, ξ) = c` and
`grad (Φ (·, c, ξ)) x₀ = ξ`. -/
theorem exists_contMDiff_hessian_eq_family [BoundarylessManifold I M] {x₀ : M}
    (hW : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).weylTensor y = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).cottonTensor y = 0)
    (c₀ : ℝ) (ξ₀ : TangentSpace I x₀) :
    ∃ (Φ : M × (ℝ × TangentSpace I x₀) → ℝ) (V : Set M) (Ω : Set (ℝ × TangentSpace I x₀)),
      IsOpen V ∧ x₀ ∈ V ∧ IsOpen Ω ∧ (c₀, ξ₀) ∈ Ω ∧
      ContMDiff (I.prod 𝓘(ℝ, ℝ × TangentSpace I x₀)) 𝓘(ℝ) ∞ Φ ∧
      (∀ c ξ, (c, ξ) ∈ Ω → Φ (x₀, c, ξ) = c) ∧
      (∀ c ξ, (c, ξ) ∈ Ω → mgradient I (fun x ↦ Φ (x, c, ξ)) x₀ = ξ) ∧
      ∀ y ∈ V, ∀ c ξ, (c, ξ) ∈ Ω → ∀ u v : TangentSpace I y,
        hessian I (fun x ↦ Φ (x, c, ξ)) y u v =
          (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm y
            (mgradient I (fun x ↦ Φ (x, c, ξ)) y) u v :=
  exists_contMDiff_hessian_eq_family_of_isInteriorPoint BoundarylessManifold.isInteriorPoint
    hW hC c₀ ξ₀

/-- **Local solutions of the conformal flattening equation at an interior point.** Where the Weyl
and Cotton tensors vanish near an interior point `x₀`, the conformal flattening equation admits a
globally smooth solution `φ : M → ℝ` near `x₀` with any prescribed value `c` and gradient `ξ` at
`x₀`. -/
theorem exists_eventually_hessian_eq_of_isInteriorPoint {x₀ : M} (hx₀ : I.IsInteriorPoint x₀)
    (hW : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).weylTensor y = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).cottonTensor y = 0)
    (c : ℝ) (ξ : TangentSpace I x₀) :
    ∃ φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ ∧ φ x₀ = c ∧ mgradient I φ x₀ = ξ ∧
      ∀ᶠ y in 𝓝 x₀, ∀ u v : TangentSpace I y, hessian I φ y u v =
        (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm y
          (mgradient I φ y) u v := by
  obtain ⟨Φ, V, _, hV, hx₀V, _, hp₀Ω, hΦ, hval, hgrad, hsol⟩ :=
    exists_contMDiff_hessian_eq_family_of_isInteriorPoint hx₀ hW hC c ξ
  exact ⟨fun x ↦ Φ (x, c, ξ), hΦ.comp (contMDiff_id.prodMk contMDiff_const),
    hval c ξ hp₀Ω, hgrad c ξ hp₀Ω,
    eventually_of_mem (hV.mem_nhds hx₀V) fun y hy ↦ hsol y hy c ξ hp₀Ω⟩

/-- **Local solutions of the conformal flattening equation on a boundaryless manifold.** Where the
Weyl and Cotton tensors vanish near `x₀`, the conformal flattening equation admits a globally smooth
solution `φ : M → ℝ` near `x₀` with any prescribed value `c` and gradient `ξ` at `x₀`. -/
theorem exists_eventually_hessian_eq [BoundarylessManifold I M] {x₀ : M}
    (hW : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).weylTensor y = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (CovariantDerivative.leviCivitaConnection I M).cottonTensor y = 0)
    (c : ℝ) (ξ : TangentSpace I x₀) :
    ∃ φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ ∧ φ x₀ = c ∧ mgradient I φ x₀ = ξ ∧
      ∀ᶠ y in 𝓝 x₀, ∀ u v : TangentSpace I y, hessian I φ y u v =
        (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm y
          (mgradient I φ y) u v :=
  exists_eventually_hessian_eq_of_isInteriorPoint BoundarylessManifold.isInteriorPoint
    hW hC c ξ

end ChartTransport

end TauCeti.Manifold

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- In dimension `2`, any solution of the conformal flattening equation at a point `x` where the
Weyl tensor of `g` vanishes makes `e^(2φ) g` flat at `x`. -/
private theorem curvatureTensor_leviCivitaConnection_rescale_eq_zero_of_finrank_eq_two
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hE : Module.finrank ℝ E = 2) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hf_pos : ∀ x, 0 < f x) {φ : M → ℝ} (hfφ : ∀ x, f x = Real.exp (2 * φ x)) {x : M}
    (hW : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor x) = 0)
    (hsol : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      ∀ u v : TangentSpace I x, hessian I φ x u v =
        (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm x
          (mgradient I φ x) u v) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x) = 0 := by
  have hx : Module.finrank ℝ (TangentSpace I x) = 2 := by rw [TauCeti.finrank_tangentSpace, hE]
  have hP0 : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).schoutenTensor x) = 0 := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ext u v
    simp [CovariantDerivative.schoutenTensor_apply, hx]
  have hscal_g : g.scalarCurvature x = 0 := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let D := CovariantDerivative.leviCivitaConnection I M
    rw [scalarCurvature_def]
    exact D.scalarCurvature_eq_zero_of_curvatureTensor_eq_zero x
      ((D.curvatureTensor_eq_zero_iff_weylTensor_eq_zero_and_schoutenTensor_eq_zero x).2 ⟨hW, hP0⟩)
  have hlap : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      laplaceBeltrami I φ x) = 0 := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let b := (stdOrthonormalBasis ℝ (TangentSpace I x)).reindex (finCongr hx)
    rw [laplaceBeltrami_eq_sum_hessian I φ x b]
    have hsum : ∑ i : Fin 2, hessian I φ x (b i) (b i) =
        (∑ i : Fin 2, ⟪mgradient I φ x, b i⟫_ℝ * ⟪b i, mgradient I φ x⟫_ℝ) -
          ‖mgradient I φ x‖ ^ 2 / 2 * ∑ i : Fin 2, ⟪b i, b i⟫_ℝ := by
      refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans
        (by rw [Finset.sum_sub_distrib, Finset.mul_sum])
      simp only [hsol, CovariantDerivative.conformalFlatteningForm_apply, hP0,
        LinearMap.zero_apply, zero_add]
      rw [real_inner_comm (b i) (mgradient I φ x)]
    rw [hsum, b.sum_inner_mul_inner, real_inner_self_eq_norm_sq]
    simp
  have hscal_fg : (g.rescale f hf hf_pos).scalarCurvature x = 0 := by
    rw [g.scalarCurvature_rescale_of_finrank_eq_two hE hf hf_pos hfφ x, hscal_g, hlap]
    ring
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩
  ext w u v
  rw [CovariantDerivative.curvatureTensor_eq_scalarCurvature_div_two_smul _
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) hx,
    ← scalarCurvature_def, hscal_fg]
  simp

/-- **Flatness of `e^(2φ) g` from the conformal flattening equation, in every dimension.** If the
Weyl tensor of `g` vanishes at `x` and `φ` solves the conformal flattening equation at `x`, then the
rescaled metric `f g` with `f = e^(2φ)` has vanishing curvature tensor at `x`, with no restriction
on the dimension of `M`. -/
theorem curvatureTensor_leviCivitaConnection_rescale_eq_zero_of_weylTensor_eq_zero_of_hessian_eq
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x) {φ : M → ℝ}
    (hfφ : ∀ x, f x = Real.exp (2 * φ x)) {x : M}
    (hW : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor x) = 0)
    (hsol : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      ∀ u v : TangentSpace I x, hessian I φ x u v =
        (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm x
          (mgradient I φ x) u v) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x) = 0 := by
  rcases lt_trichotomy (Module.finrank ℝ E) 2 with hn1 | hn2 | hn3
  · let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩
    exact (CovariantDerivative.leviCivitaConnection I M).curvatureTensor_eq_zero_of_finrank_le_one x
      (by rw [TauCeti.finrank_tangentSpace]; omega)
  · exact g.curvatureTensor_leviCivitaConnection_rescale_eq_zero_of_finrank_eq_two hn2 hf hf_pos
      hfφ hW hsol
  · exact (g.curvatureTensor_leviCivitaConnection_rescale_eq_zero_iff hf hf_pos hfφ hn3 x).2
      ⟨hW, hsol⟩

/-- **Flat conformal rescaling near an interior point, with prescribed 1-jet.** Where the Weyl and
Cotton tensors of a smooth Riemannian metric `g` vanish near an interior point `x`, there is in
every dimension a globally smooth function `φ : M → ℝ` with prescribed value `c` and gradient `ξ` at
`x` such that `e^(2φ) g` has vanishing curvature tensor near `x`. -/
theorem exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {x : M}
    (hx : I.IsInteriorPoint x)
    (hW : ∀ᶠ y in 𝓝 x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor y) = 0)
    (hC : ∀ᶠ y in 𝓝 x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).cottonTensor y) = 0)
    (c : ℝ) (ξ : TangentSpace I x) :
    ∃ (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ), φ x = c ∧
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        mgradient I φ x = ξ) ∧
      ∀ᶠ y in 𝓝 x,
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale (fun z ↦ Real.exp (2 * φ z))
            (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ))
            (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  obtain ⟨φ, hφ, hval, hgrad, hsol⟩ :=
    exists_eventually_hessian_eq_of_isInteriorPoint hx hW hC c ξ
  refine ⟨φ, hφ, hval, hgrad, ?_⟩
  filter_upwards [hW, hsol] with y hyW hy
  exact g.curvatureTensor_leviCivitaConnection_rescale_eq_zero_of_weylTensor_eq_zero_of_hessian_eq
    (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ)) (fun _ ↦ Real.exp_pos _)
    (fun _ ↦ rfl) hyW hy

/-- **Flat conformal rescaling on a boundaryless manifold, with prescribed 1-jet.** Where the Weyl
and Cotton tensors of `g` vanish near `x`, there is in every dimension a globally smooth function
`φ : M → ℝ` with prescribed value `c` and gradient `ξ` at `x` such that `e^(2φ) g` has vanishing
curvature tensor near `x`. -/
theorem exists_eventually_curvatureTensor_rescale_exp_eq_zero [BoundarylessManifold I M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {x : M}
    (hW : ∀ᶠ y in 𝓝 x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor y) = 0)
    (hC : ∀ᶠ y in 𝓝 x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).cottonTensor y) = 0)
    (c : ℝ) (ξ : TangentSpace I x) :
    ∃ (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ), φ x = c ∧
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        mgradient I φ x = ξ) ∧
      ∀ᶠ y in 𝓝 x,
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale (fun z ↦ Real.exp (2 * φ z))
            (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ))
            (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 :=
  g.exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint hW hC c ξ

/-- On a boundaryless manifold of any dimension, a smooth Riemannian metric whose Weyl and Cotton
tensors vanish identically is locally conformally flat. -/
theorem isLocallyConformallyFlat_of_weylTensor_eq_zero_and_cottonTensor_eq_zero
    [BoundarylessManifold I M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hW : ∀ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor x) = 0)
    (hC : ∀ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).cottonTensor x) = 0) :
    g.IsLocallyConformallyFlat := by
  rw [g.isLocallyConformallyFlat_iff]
  intro x
  obtain ⟨φ, hφ, -, -, hflat⟩ :=
    g.exists_eventually_curvatureTensor_rescale_exp_eq_zero
      (Eventually.of_forall hW) (Eventually.of_forall hC) 0 0
  exact ⟨fun y ↦ Real.exp (2 * φ y),
    Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ), fun _ ↦ Real.exp_pos _, hflat⟩

/-- **Joint Weyl–Cotton criterion for local conformal flatness.** Away from dimension `2`, a smooth
Riemannian metric on a boundaryless manifold is locally conformally flat if and only if both its
Weyl tensor and its Cotton tensor vanish identically. -/
theorem isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero
    [BoundarylessManifold I M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E ≠ 2) :
    g.IsLocallyConformallyFlat ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0) ∧
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0) :=
  ⟨fun hg ↦ ⟨hg.weylTensor_eq_zero hn, hg.cottonTensor_eq_zero hn⟩,
    fun ⟨hW, hC⟩ ↦ g.isLocallyConformallyFlat_of_weylTensor_eq_zero_and_cottonTensor_eq_zero hW hC⟩

/-- **Weyl–Schouten theorem away from dimension three (sufficiency).** A smooth Riemannian metric on
a boundaryless manifold of dimension `n ≠ 3` with vanishing Weyl tensor is locally conformally
flat. -/
theorem isLocallyConformallyFlat_of_weylTensor_eq_zero [BoundarylessManifold I M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E ≠ 3)
    (hW : ∀ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor x) = 0) :
    g.IsLocallyConformallyFlat := by
  by_cases hn₂ : Module.finrank ℝ E = 2
  · refine g.isLocallyConformallyFlat_of_curvatureTensor_eq_zero fun x ↦ ?_
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    have hx : Module.finrank ℝ (TangentSpace I x) = 2 := by rw [TauCeti.finrank_tangentSpace, hn₂]
    have hP0 : (CovariantDerivative.leviCivitaConnection I M).schoutenTensor x = 0 := by
      ext u v; simp [CovariantDerivative.schoutenTensor_apply, hx]
    exact ((CovariantDerivative.leviCivitaConnection I M
      ).curvatureTensor_eq_zero_iff_weylTensor_eq_zero_and_schoutenTensor_eq_zero x).2 ⟨hW x, hP0⟩
  · refine g.isLocallyConformallyFlat_of_weylTensor_eq_zero_and_cottonTensor_eq_zero hW fun x ↦ ?_
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    have hcov := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
    exact hcov.cottonTensor_eq_zero_of_eventually_weylTensor_eq_zero
      (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I) hn₂ hn (Eventually.of_forall hW)

/-- **Weyl–Schouten theorem away from dimensions two and three.** A smooth Riemannian metric on a
boundaryless manifold of dimension `n ∉ {2, 3}` (in particular, `4 ≤ n`) is locally conformally flat
if and only if its Weyl tensor vanishes identically. -/
theorem isLocallyConformallyFlat_iff_weylTensor_eq_zero [BoundarylessManifold I M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn₂ : Module.finrank ℝ E ≠ 2) (hn₃ : Module.finrank ℝ E ≠ 3) :
    g.IsLocallyConformallyFlat ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0) :=
  ⟨fun hg ↦ hg.weylTensor_eq_zero hn₂, g.isLocallyConformallyFlat_of_weylTensor_eq_zero hn₃⟩

/-- **Weyl–Schouten Cotton criterion (sufficiency).** A smooth Riemannian metric on a boundaryless
manifold of dimension at most `3` and different from `2` (in particular, dimension `3`) with
vanishing Cotton tensor is locally conformally flat. -/
theorem isLocallyConformallyFlat_of_cottonTensor_eq_zero [BoundarylessManifold I M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn₂ : Module.finrank ℝ E ≠ 2) (hn₃ : Module.finrank ℝ E ≤ 3)
    (hC : ∀ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).cottonTensor x) = 0) :
    g.IsLocallyConformallyFlat := by
  refine g.isLocallyConformallyFlat_of_weylTensor_eq_zero_and_cottonTensor_eq_zero (fun x ↦ ?_) hC
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let D := CovariantDerivative.leviCivitaConnection I M
  by_cases hn1 : Module.finrank ℝ E ≤ 1
  · exact ((D.curvatureTensor_eq_zero_iff_weylTensor_eq_zero_and_schoutenTensor_eq_zero x).1
      (D.curvatureTensor_eq_zero_of_finrank_le_one x
        (by rw [TauCeti.finrank_tangentSpace]; omega))).1
  · exact CovariantDerivative.IsMetricCompatible.weylTensor_eq_zero_of_finrank_eq_three
      (cov := D) (CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)) x
      (by rw [TauCeti.finrank_tangentSpace]; omega)

/-- **Weyl–Schouten theorem in dimension three (and dimensions `0`, `1`).** A smooth Riemannian
metric on a boundaryless manifold of dimension at most `3` and different from `2` is locally
conformally flat if and only if its Cotton tensor vanishes identically. -/
theorem isLocallyConformallyFlat_iff_cottonTensor_eq_zero [BoundarylessManifold I M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn₂ : Module.finrank ℝ E ≠ 2) (hn₃ : Module.finrank ℝ E ≤ 3) :
    g.IsLocallyConformallyFlat ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0) :=
  ⟨fun hg ↦ hg.cottonTensor_eq_zero hn₂,
    g.isLocallyConformallyFlat_of_cottonTensor_eq_zero hn₂ hn₃⟩

end Bundle.ContMDiffRiemannianMetric
