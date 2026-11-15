/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ConformallyFlat.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Solvability
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Divergence

/-!
# The Weyl–Schouten theorem on smooth manifolds

Let `g` be a smooth Riemannian metric on a smooth manifold `M` modelled on a finite-dimensional real
normed space `E` of dimension at least `3`. Combining the manifold-level local solvability of the
conformal flattening equation (`TauCeti.Manifold.exists_eventually_hessian_eq_of_isInteriorPoint`
and its smooth-family version) with the curvature decomposition into Weyl and Schouten tensors
(`Bundle.ContMDiffRiemannianMetric.curvatureTensor_leviCivitaConnection_rescale_eq_zero_iff`) yields
flat conformal rescalings `e^(2φ) g` near any interior point `x₀` at which the Weyl and Cotton
tensors of `g` vanish nearby, with arbitrary prescribed value and gradient of `φ` at `x₀` (and
smooth dependence on that initial jet).

On a boundaryless smooth manifold `M`, this proves the **Weyl–Schouten theorem**:

* In dimension at least `3`, `g` is locally conformally flat if and only if both its Weyl tensor and
  its Cotton tensor vanish identically
  (`isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero`).
* In dimension at least `4`, `g` is locally conformally flat if and only if its Weyl tensor vanishes
  identically (`isLocallyConformallyFlat_iff_weylTensor_eq_zero`), since vanishing of the Cotton
  tensor follows from the divergence identity `div W = (dim M - 3) C`
  (`CovariantDerivative.IsMetricCompatible.cottonTensor_eq_zero_of_eventually_weylTensor_eq_zero`).
* In dimension `3`, `g` is locally conformally flat if and only if its Cotton tensor vanishes
  identically (`isLocallyConformallyFlat_iff_cottonTensor_eq_zero`), since the Weyl tensor vanishes
  identically in dimension `3`
  (`CovariantDerivative.IsMetricCompatible.weylTensor_eq_zero_of_finrank_eq_three`).

## Main results

In `Bundle.ContMDiffRiemannianMetric`:

* `exists_contMDiff_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint` and
  `exists_contMDiff_curvatureTensor_rescale_exp_eq_zero`: smooth families of locally flat conformal
  rescalings `e^(2 Φ(p, ·)) g` parametrized by initial jets `p = (φ x₀, grad φ x₀)`.
* `exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint` and
  `exists_eventually_curvatureTensor_rescale_exp_eq_zero`: locally flat conformal rescalings
  `e^(2φ) g` with prescribed value and gradient of `φ` at a point.
* `isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero`: characterization of
  local conformal flatness in dimension at least `3`.
* `isLocallyConformallyFlat_iff_weylTensor_eq_zero` and
  `isLocallyConformallyFlat_of_weylTensor_eq_zero`: the Weyl–Schouten theorem in dimension at least
  `4`.
* `isLocallyConformallyFlat_iff_cottonTensor_eq_zero` and
  `isLocallyConformallyFlat_of_cottonTensor_eq_zero`: Cotton's theorem (the three-dimensional case
  of Weyl–Schouten).

## References

* H. Weyl, *Reine Infinitesimalgeometrie*, Math. Z. 2 (1918), 384–411.
* J. A. Schouten, *Über die konforme Abbildung `n`-dimensionaler Mannigfaltigkeiten mit
  quadratischer Maßbestimmung auf eine Mannigfaltigkeit mit euklidischer Maßbestimmung*, Math. Z. 11
  (1921), 58–88.
* É. Cotton, *Sur les variétés à trois dimensions*, Ann. Fac. Sci. Toulouse (2) 1 (1899), 385–438,
  Chapter III, Section 18.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 2.
-/

public section

open Bundle Filter Set TauCeti.Manifold
open scoped ContDiff Manifold Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-! ### Locally flat conformal rescalings with prescribed initial jet -/

/-- **Smooth family of flat conformal rescalings near an interior point.** In dimension at least
`3`, if the Weyl and Cotton tensors of `g` vanish near an interior point `x₀`, then around every
initial jet `(c₀, ξ₀)` there is a jointly smooth family `Φ : (ℝ × TangentSpace I x₀) × M → ℝ` and an
open neighbourhood `V` of `x₀` such that for every `p` near `(c₀, ξ₀)`, `Φ (p, ·)` has value `p.1`
and `g`-gradient `p.2` at `x₀` and `e^(2 Φ(p, ·)) g` is flat on `V`. -/
theorem exists_contMDiff_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 3 ≤ Module.finrank ℝ E) {x₀ : M} (hx₀ : I.IsInteriorPoint x₀)
    (hW : ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor y) = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).cottonTensor y) = 0)
    (c₀ : ℝ) (ξ₀ : TangentSpace I x₀) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ∃ (Φ : (ℝ × TangentSpace I x₀) × M → ℝ)
      (hΦ : ContMDiff (𝓘(ℝ, ℝ × TangentSpace I x₀).prod I) 𝓘(ℝ) ∞ Φ)
      (Ω : Set (ℝ × TangentSpace I x₀)) (V : Set M),
      IsOpen Ω ∧ (c₀, ξ₀) ∈ Ω ∧ IsOpen V ∧ x₀ ∈ V ∧
      ∀ p ∈ Ω, Φ (p, x₀) = p.1 ∧ mgradient I (fun y ↦ Φ (p, y)) x₀ = p.2 ∧
        ∀ y ∈ V,
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g.rescale (fun z ↦ Real.exp (2 * Φ (p, z)))
              (Real.contDiff_exp.comp_contMDiff
                (contMDiff_const.mul (hΦ.comp (contMDiff_const.prodMk contMDiff_id))))
              (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩;
            (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨U_W, hU_W, hUW_open, hx₀UW⟩ := eventually_nhds_iff.1 hW
  obtain ⟨Φ, Ω, V₀, hΩ, hpΩ, hV₀, hx₀V₀, hΦ, hsol⟩ :=
    exists_contMDiff_hessian_eq_conformalFlatteningForm_of_isInteriorPoint hx₀ hW hC c₀ ξ₀
  refine ⟨Φ, hΦ, Ω, V₀ ∩ U_W, hΩ, hpΩ, hV₀.inter hUW_open, ⟨hx₀V₀, hx₀UW⟩, fun p hp ↦ ?_⟩
  obtain ⟨hval, hgrad, hhess⟩ := hsol p hp
  refine ⟨hval, hgrad, fun y hy ↦ ?_⟩
  exact (g.curvatureTensor_leviCivitaConnection_rescale_eq_zero_iff
    (Real.contDiff_exp.comp_contMDiff
      (contMDiff_const.mul (hΦ.comp (contMDiff_const.prodMk contMDiff_id))))
    (fun _ ↦ Real.exp_pos _) (fun _ ↦ rfl) hn y).2 ⟨hU_W y hy.2, hhess y hy.1⟩

/-- **Smooth family of flat conformal rescalings on a boundaryless manifold.** -/
theorem exists_contMDiff_curvatureTensor_rescale_exp_eq_zero [BoundarylessManifold I M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 3 ≤ Module.finrank ℝ E) {x₀ : M}
    (hW : ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor y) = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).cottonTensor y) = 0)
    (c₀ : ℝ) (ξ₀ : TangentSpace I x₀) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ∃ (Φ : (ℝ × TangentSpace I x₀) × M → ℝ)
      (hΦ : ContMDiff (𝓘(ℝ, ℝ × TangentSpace I x₀).prod I) 𝓘(ℝ) ∞ Φ)
      (Ω : Set (ℝ × TangentSpace I x₀)) (V : Set M),
      IsOpen Ω ∧ (c₀, ξ₀) ∈ Ω ∧ IsOpen V ∧ x₀ ∈ V ∧
      ∀ p ∈ Ω, Φ (p, x₀) = p.1 ∧ mgradient I (fun y ↦ Φ (p, y)) x₀ = p.2 ∧
        ∀ y ∈ V,
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g.rescale (fun z ↦ Real.exp (2 * Φ (p, z)))
              (Real.contDiff_exp.comp_contMDiff
                (contMDiff_const.mul (hΦ.comp (contMDiff_const.prodMk contMDiff_id))))
              (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩;
            (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 :=
  g.exists_contMDiff_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint hn
    BoundarylessManifold.isInteriorPoint hW hC c₀ ξ₀

/-- **Flat conformal rescaling near an interior point with prescribed initial jet.** Where the Weyl
and Cotton tensors vanish near an interior point `x`, a smooth Riemannian metric in dimension at
least `3` admits a flat conformal rescaling `e^(2φ) g` near `x`, with arbitrary prescribed value and
gradient of `φ` at `x`. -/
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
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨Φ, hΦ, Ω, V, -, hpΩ, hV, hxV, hsol⟩ :=
    g.exists_contMDiff_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint hn hx hW hC c ξ
  obtain ⟨hval, hgrad, hflat⟩ := hsol (c, ξ) hpΩ
  exact ⟨fun z ↦ Φ ((c, ξ), z), hΦ.comp (contMDiff_const.prodMk contMDiff_id), hval, hgrad,
    eventually_of_mem (hV.mem_nhds hxV) hflat⟩

/-- **Flat conformal rescaling on a boundaryless manifold with prescribed initial jet.** -/
theorem exists_eventually_curvatureTensor_rescale_exp_eq_zero [BoundarylessManifold I M]
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

/-! ### The Weyl–Schouten theorem on boundaryless manifolds -/

/-- **Characterization of locally conformally flat metrics in dimension at least three.** On a
boundaryless smooth manifold of dimension at least `3`, a smooth Riemannian metric is locally
conformally flat if and only if both its Weyl tensor and its Cotton tensor vanish everywhere. -/
theorem isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero
    [BoundarylessManifold I M]
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

/-- **The Weyl–Schouten theorem in dimension at least four.** On a boundaryless smooth manifold of
dimension at least `4`, a smooth Riemannian metric is locally conformally flat if and only if its
Weyl tensor vanishes everywhere. -/
theorem isLocallyConformallyFlat_iff_weylTensor_eq_zero [BoundarylessManifold I M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 4 ≤ Module.finrank ℝ E) :
    g.IsLocallyConformallyFlat ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0) := by
  rw [g.isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero (by omega)]
  refine and_iff_left_of_imp fun hW x ↦ ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hcov := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  exact hcov.cottonTensor_eq_zero_of_eventually_weylTensor_eq_zero
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I) (by omega) (by omega)
    (Eventually.of_forall hW)

/-- **Sufficiency half of the Weyl–Schouten theorem in dimension at least four.** On a boundaryless
smooth manifold of dimension at least `4`, a smooth Riemannian metric whose Weyl tensor vanishes
everywhere is locally conformally flat. -/
theorem isLocallyConformallyFlat_of_weylTensor_eq_zero [BoundarylessManifold I M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 4 ≤ Module.finrank ℝ E)
    (hW : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0) :
    g.IsLocallyConformallyFlat :=
  (g.isLocallyConformallyFlat_iff_weylTensor_eq_zero hn).2 hW

/-- **The Weyl–Schouten theorem in dimension three (Cotton's theorem).** On a boundaryless smooth
three-manifold, a smooth Riemannian metric is locally conformally flat if and only if its Cotton
tensor vanishes everywhere. -/
theorem isLocallyConformallyFlat_iff_cottonTensor_eq_zero [BoundarylessManifold I M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E = 3) :
    g.IsLocallyConformallyFlat ↔
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0) := by
  rw [g.isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero hn.ge]
  refine and_iff_right ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  intro x
  have hcov := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  exact CovariantDerivative.IsMetricCompatible.weylTensor_eq_zero_of_finrank_eq_three
    (cov := CovariantDerivative.leviCivitaConnection I M) hcov x
    (by rw [TauCeti.finrank_tangentSpace, hn])

/-- **Sufficiency half of Cotton's theorem in dimension three.** On a boundaryless smooth
three-manifold, a smooth Riemannian metric whose Cotton tensor vanishes everywhere is locally
conformally flat. -/
theorem isLocallyConformallyFlat_of_cottonTensor_eq_zero [BoundarylessManifold I M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E = 3)
    (hC : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0) :
    g.IsLocallyConformallyFlat :=
  (g.isLocallyConformallyFlat_iff_cottonTensor_eq_zero hn).2 hC

end Bundle.ContMDiffRiemannianMetric
