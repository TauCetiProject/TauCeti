/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ConformallyFlat.Chart
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Divergence
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Solvability

/-!
# The Weyl–Schouten theorem on smooth Riemannian manifolds

This file proves the Weyl–Schouten characterization of locally conformally flat metrics on smooth
Riemannian manifolds of dimension at least three:

* In dimension `n ≥ 4`, a smooth Riemannian metric `g` on a boundaryless manifold is locally
  conformally flat if and only if its Weyl tensor vanishes everywhere.
* In dimension `n = 3` (where the Weyl tensor vanishes identically), `g` is locally conformally
  flat if and only if its Cotton tensor vanishes everywhere.

At an interior point `x` where the Weyl and Cotton tensors vanish on a neighbourhood in dimension
`n ≥ 3`, local manifold solvability of the conformal flattening equation
(`TauCeti.Manifold.exists_eventually_hessian_eq_of_isInteriorPoint`) produces a globally smooth
function `φ` with prescribed value and gradient at `x` solving
`Hess φ = P + dφ ⊗ dφ - (|dφ|² / 2) g` near `x`, so the rescaled metric `e^(2φ) g` has vanishing
curvature tensor near `x`
(`Bundle.ContMDiffRiemannianMetric.curvatureTensor_leviCivitaConnection_rescale_eq_zero_iff`). In
dimension `n ≥ 4`, the divergence identity
(`CovariantDerivative.IsMetricCompatible.cottonTensor_eq_zero_of_eventually_weylTensor_eq_zero`)
implies that vanishing of the Weyl tensor already forces the Cotton tensor to vanish; in dimension
`n = 3`, the Weyl tensor vanishes automatically
(`CovariantDerivative.IsMetricCompatible.weylTensor_eq_zero_of_finrank_eq_three`).

Combining the Weyl–Schouten theorem with `ConformallyFlat.Chart` characterizes conformally
Euclidean coordinate charts directly by the vanishing of the Weyl tensor (`n ≥ 4`) or Cotton tensor
(`n = 3`), and shows that every constant-curvature Riemannian manifold of dimension `n ≠ 2` is
locally conformally flat.

## Main results

In `Bundle.ContMDiffRiemannianMetric`:

* `exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint` and
  `exists_eventually_curvatureTensor_rescale_exp_eq_zero`: local conformal flattening `e^(2φ) g`
  with prescribed `φ x` and `mgradient I φ x`.
* `isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero`: characterization of
  local conformal flatness in dimension `n ≥ 3` by `W = 0` and `C = 0`.
* `isLocallyConformallyFlat_iff_weylTensor_eq_zero`,
  `isLocallyConformallyFlat_iff_weylTensor_eq_zero_of_riemannianBundle_eq`, and
  `isLocallyConformallyFlat_of_weylTensor_eq_zero`: the Weyl–Schouten theorem for `n ≥ 4`.
* `isLocallyConformallyFlat_iff_cottonTensor_eq_zero`,
  `isLocallyConformallyFlat_iff_cottonTensor_eq_zero_of_riemannianBundle_eq`, and
  `isLocallyConformallyFlat_of_cottonTensor_eq_zero`: the Weyl–Schouten theorem for `n = 3`.
* `forall_exists_partialDiffeomorph_iff_weylTensor_eq_zero` and
  `forall_exists_partialDiffeomorph_iff_cottonTensor_eq_zero`: existence of conformally Euclidean
  charts characterized by `W = 0` (`n ≥ 4`) or `C = 0` (`n = 3`).
* `IsConstantCurvatureTensor.isLocallyConformallyFlat`: constant-curvature manifolds of dimension
  `n ≠ 2` (spheres, Euclidean spaces, hyperbolic manifolds) are locally conformally flat.

## References

* É. Cotton, *Sur les variétés à trois dimensions*, Ann. Fac. Sci. Toulouse (2) 1 (1899), 385–438,
  Chapter III, n° 18, p. 412.
* H. Weyl, *Reine Infinitesimalgeometrie*, Math. Z. 2 (1918), 384–411.
* J. A. Schouten, *Über die konforme Abbildung `n`-dimensionaler Mannigfaltigkeiten mit
  quadratischer Maßbestimmung auf eine Mannigfaltigkeit mit euklidischer Maßbestimmung*, Math. Z.
  11 (1921), 58–88.
* L. P. Eisenhart, *Riemannian Geometry*, Princeton Univ. Press (1926), §28.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 2, p. 43.
-/

public section

open Bundle Filter Manifold
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- Where the Weyl and Cotton tensors vanish near an interior point `x` in dimension at least `3`,
a smooth Riemannian metric `g` admits a flat conformal rescaling `e^(2φ) g` near `x` with arbitrary
prescribed value `c` and gradient `ξ` of `φ` at `x`. -/
theorem exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 3 ≤ Module.finrank ℝ E) {x : M} (hx : I.IsInteriorPoint x)
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
  obtain ⟨φ, hφ, hval, hgrad, hsol⟩ :=
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    exists_eventually_hessian_eq_of_isInteriorPoint hx hW hC c ξ
  refine ⟨φ, hφ, hval, hgrad, ?_⟩
  filter_upwards [hW, hsol] with y hyW hy
  exact (g.curvatureTensor_leviCivitaConnection_rescale_eq_zero_iff
    (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ)) (fun _ ↦ Real.exp_pos _)
    (fun _ ↦ rfl) hn y).2 ⟨hyW, hy⟩

section Boundaryless

variable [BoundarylessManifold I M]

/-- On a boundaryless manifold of dimension at least `3`, vanishing Weyl and Cotton tensors near
`x` give a flat conformal rescaling `e^(2φ) g` near `x` with prescribed value and gradient of `φ`
at `x`. -/
theorem exists_eventually_curvatureTensor_rescale_exp_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 3 ≤ Module.finrank ℝ E) {x : M}
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
  g.exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint hn
    BoundarylessManifold.isInteriorPoint hW hC c ξ

/-- On a boundaryless smooth manifold of dimension at least `3`, a smooth Riemannian metric is
locally conformally flat if and only if both its Weyl tensor and its Cotton tensor vanish
everywhere. -/
theorem isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 3 ≤ Module.finrank ℝ E) :
    g.IsLocallyConformallyFlat ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0) ∧
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0) := by
  refine ⟨fun hg ↦ ⟨hg.weylTensor_eq_zero (by omega), hg.cottonTensor_eq_zero (by omega)⟩, ?_⟩
  rintro ⟨hW, hC⟩
  rw [g.isLocallyConformallyFlat_iff]
  intro x
  obtain ⟨φ, hφ, -, -, hflat⟩ :=
    g.exists_eventually_curvatureTensor_rescale_exp_eq_zero hn
      (Eventually.of_forall hW) (Eventually.of_forall hC) 0 0
  exact ⟨fun y ↦ Real.exp (2 * φ y),
    Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ), fun _ ↦ Real.exp_pos _, hflat⟩

/-- **Weyl–Schouten theorem in dimension at least four.** On a boundaryless smooth manifold of
dimension `n ≥ 4`, a smooth Riemannian metric is locally conformally flat if and only if its Weyl
tensor vanishes everywhere. -/
theorem isLocallyConformallyFlat_iff_weylTensor_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 4 ≤ Module.finrank ℝ E) :
    g.IsLocallyConformallyFlat ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0) := by
  rw [g.isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero (by omega)]
  refine and_iff_left_of_imp fun hW x ↦ ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  have hcov := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  exact hcov.cottonTensor_eq_zero_of_eventually_weylTensor_eq_zero
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I) (by omega) (by omega)
    (Eventually.of_forall hW)

/-- **Weyl–Schouten theorem in dimension at least four (installed metric form).** When `g` is
installed as the ambient `RiemannianBundle` on a boundaryless manifold of dimension `n ≥ 4`, `g` is
locally conformally flat if and only if its Weyl tensor vanishes everywhere. -/
theorem isLocallyConformallyFlat_iff_weylTensor_eq_zero_of_riemannianBundle_eq
    [inst : RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 4 ≤ Module.finrank ℝ E) (hg : RiemannianBundle.g = g.toRiemannianMetric) :
    g.IsLocallyConformallyFlat ↔
      ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0 := by
  obtain ⟨_⟩ := inst
  subst hg
  exact g.isLocallyConformallyFlat_iff_weylTensor_eq_zero hn

/-- **Converse Weyl–Schouten theorem in dimension at least four (installed metric form).** On a
boundaryless smooth manifold of dimension `n ≥ 4`, if `g` is installed as the ambient
`RiemannianBundle` and its Weyl tensor vanishes everywhere, then `g` is locally conformally flat.
`IsLocallyConformallyFlat.weylTensor_eq_zero` is the forward implication. -/
theorem isLocallyConformallyFlat_of_weylTensor_eq_zero
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 4 ≤ Module.finrank ℝ E) (hg : RiemannianBundle.g = g.toRiemannianMetric)
    (hW : ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0) :
    g.IsLocallyConformallyFlat :=
  (g.isLocallyConformallyFlat_iff_weylTensor_eq_zero_of_riemannianBundle_eq hn hg).2 hW

/-- **Weyl–Schouten theorem in dimension three.** On a boundaryless smooth `3`-manifold, a smooth
Riemannian metric is locally conformally flat if and only if its Cotton tensor vanishes
everywhere. -/
theorem isLocallyConformallyFlat_iff_cottonTensor_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E = 3) :
    g.IsLocallyConformallyFlat ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0) := by
  rw [g.isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero hn.ge]
  refine and_iff_right ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro x
  have hcov := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  exact CovariantDerivative.IsMetricCompatible.weylTensor_eq_zero_of_finrank_eq_three
    (cov := CovariantDerivative.leviCivitaConnection I M) hcov x
    (by rw [TauCeti.finrank_tangentSpace, hn])

/-- **Weyl–Schouten theorem in dimension three (installed metric form).** When `g` is installed as
the ambient `RiemannianBundle` on a boundaryless `3`-manifold, `g` is locally conformally flat if
and only if its Cotton tensor vanishes everywhere. -/
theorem isLocallyConformallyFlat_iff_cottonTensor_eq_zero_of_riemannianBundle_eq
    [inst : RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E = 3) (hg : RiemannianBundle.g = g.toRiemannianMetric) :
    g.IsLocallyConformallyFlat ↔
      ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0 := by
  obtain ⟨_⟩ := inst
  subst hg
  exact g.isLocallyConformallyFlat_iff_cottonTensor_eq_zero hn

/-- **Converse Weyl–Schouten theorem in dimension three (installed metric form).** On a
boundaryless smooth `3`-manifold, if `g` is installed as the ambient `RiemannianBundle` and its
Cotton tensor vanishes everywhere, then `g` is locally conformally flat.
`IsLocallyConformallyFlat.cottonTensor_eq_zero` is the forward implication. -/
theorem isLocallyConformallyFlat_of_cottonTensor_eq_zero
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E = 3) (hg : RiemannianBundle.g = g.toRiemannianMetric)
    (hC : ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0) :
    g.IsLocallyConformallyFlat :=
  (g.isLocallyConformallyFlat_iff_cottonTensor_eq_zero_of_riemannianBundle_eq hn hg).2 hC

/-- On a boundaryless smooth manifold of dimension `n ≥ 4`, every point admits a conformally
Euclidean `PartialDiffeomorph` sending it to `0` if and only if the Weyl tensor of `g` vanishes
everywhere. -/
theorem forall_exists_partialDiffeomorph_iff_weylTensor_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 4 ≤ Module.finrank ℝ E) :
    (∀ x : M, ∃ (φ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞) (h : M → ℝ),
      x ∈ φ.source ∧ φ x = 0 ∧ ContMDiffOn I 𝓘(ℝ) ∞ h φ.source ∧
      (∀ y ∈ φ.source, 0 < h y) ∧
      ∀ y ∈ φ.source, ∀ v w : TangentSpace I y,
        g.inner y v w = h y *
          ⟪mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) φ y v,
            mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) φ y w⟫_ℝ) ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0) :=
  g.isLocallyConformallyFlat_iff_forall_exists_partialDiffeomorph.symm.trans
    (g.isLocallyConformallyFlat_iff_weylTensor_eq_zero hn)

/-- On a boundaryless smooth `3`-manifold, every point admits a conformally Euclidean
`PartialDiffeomorph` sending it to `0` if and only if the Cotton tensor of `g` vanishes
everywhere. -/
theorem forall_exists_partialDiffeomorph_iff_cottonTensor_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E = 3) :
    (∀ x : M, ∃ (φ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞) (h : M → ℝ),
      x ∈ φ.source ∧ φ x = 0 ∧ ContMDiffOn I 𝓘(ℝ) ∞ h φ.source ∧
      (∀ y ∈ φ.source, 0 < h y) ∧
      ∀ y ∈ φ.source, ∀ v w : TangentSpace I y,
        g.inner y v w = h y *
          ⟪mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) φ y v,
            mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) φ y w⟫_ℝ) ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0) :=
  g.isLocallyConformallyFlat_iff_forall_exists_partialDiffeomorph.symm.trans
    (g.isLocallyConformallyFlat_iff_cottonTensor_eq_zero hn)

/-- **Spaces of constant sectional curvature are locally conformally flat.** On a boundaryless
smooth manifold of dimension `n ≠ 2`, every smooth Riemannian metric of constant curvature `κ`
(including round spheres, Euclidean spaces, and hyperbolic manifolds) is locally conformally flat.
-/
theorem IsConstantCurvatureTensor.isLocallyConformallyFlat
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {κ : ℝ}
    (hg : g.IsConstantCurvatureTensor κ) (hn : Module.finrank ℝ E ≠ 2) :
    g.IsLocallyConformallyFlat := by
  rcases le_or_gt (Module.finrank ℝ E) 1 with h1 | h1
  · refine g.isLocallyConformallyFlat_of_curvatureTensor_eq_zero fun x ↦ ?_
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    exact (CovariantDerivative.leviCivitaConnection I M).curvatureTensor_eq_zero_of_finrank_le_one
      x (by rwa [TauCeti.finrank_tangentSpace])
  · have hn3 : 3 ≤ Module.finrank ℝ E := by omega
    rw [g.isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero hn3]
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    have hcurv := g.isConstantCurvatureTensor_iff κ |>.1 hg
    have hcov := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
    open CovariantDerivative in
    refine ⟨fun x ↦ (leviCivitaConnection I M)
        |>.weylTensor_eq_zero_of_curvatureTensor_eq_smul_inner_sub x κ
          (by rwa [TauCeti.finrank_tangentSpace]) (hcurv x),
      fun x ↦ IsMetricCompatible.cottonTensor_eq_zero_of_curvatureTensor_eq_smul_inner_sub
        (cov := leviCivitaConnection I M) hcov κ hcurv x⟩

end Boundaryless

end Bundle.ContMDiffRiemannianMetric
