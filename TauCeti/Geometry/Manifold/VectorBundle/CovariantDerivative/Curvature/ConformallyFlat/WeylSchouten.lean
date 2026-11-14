/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ConformallyFlat.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Solvability
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Divergence
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# The Weyl–Schouten theorem on smooth Riemannian manifolds

For a smooth Riemannian metric `g` on a manifold `M` of dimension `n ≥ 3`, the conformal
flattening equation `Hess φ = P + dφ ⊗ dφ - (|dφ|² / 2) g` is locally solvable through every
prescribed value and gradient `(φ(x₀), grad φ(x₀))` around any interior point `x₀` near which the
Weyl and Cotton tensors vanish, with joint smoothness in `(x, φ(x₀), grad φ(x₀))`
(`TauCeti.Manifold.exists_contMDiff_hessian_eq_family_of_isInteriorPoint`). Combining that local
solvability with the curvature characterization
`Bundle.ContMDiffRiemannianMetric.curvatureTensor_leviCivitaConnection_rescale_eq_zero_iff` yields
a jointly smooth initial-value family of conformal rescalings `e^(2 Φ(·, q)) g` with vanishing
Riemann curvature tensor near `x₀`.

On a boundaryless manifold `M` every point is an interior point, which completes the converse half
of the **Weyl–Schouten theorem** (in `Bundle.ContMDiffRiemannianMetric`):

* For `n ≥ 3`, `g` is locally conformally flat if and only if both its Weyl tensor and its Cotton
  tensor vanish identically
  (`isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero`).
* For `n ≥ 4`, the divergence identity `div W = (n - 3) C` forces the Cotton tensor to vanish
  whenever the Weyl tensor vanishes, so `g` is locally conformally flat if and only if its Weyl
  tensor vanishes (`isLocallyConformallyFlat_iff_weylTensor_eq_zero` and
  `isLocallyConformallyFlat_of_weylTensor_eq_zero`).
* For `n = 3`, the Weyl tensor vanishes identically for algebraic reasons, so `g` is locally
  conformally flat if and only if its Cotton tensor vanishes
  (`isLocallyConformallyFlat_iff_cottonTensor_eq_zero` and
  `isLocallyConformallyFlat_of_cottonTensor_eq_zero`).

For callers that have already installed `g` as the `RiemannianBundle` instance on `M` via
`hg : RiemannianBundle.g = g.toRiemannianMetric`, transport versions `..._of_riemannianBundle_eq`
avoid any `letI` binder in the curvature hypotheses.

## Main results

In `Bundle.ContMDiffRiemannianMetric`:

* `exists_contMDiff_curvatureTensor_rescale_exp_eq_zero_family_of_isInteriorPoint` and
  `exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint`: smooth initial-value
  families and individual local conformal flattenings around an interior point where `W = 0` and
  `C = 0` nearby.
* `exists_contMDiff_curvatureTensor_rescale_exp_eq_zero_family` and
  `exists_eventually_curvatureTensor_rescale_exp_eq_zero`: boundaryless specializations.
* `isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero`: characterization of
  local conformal flatness in dimension `n ≥ 3`.
* `isLocallyConformallyFlat_of_weylTensor_eq_zero` and
  `isLocallyConformallyFlat_iff_weylTensor_eq_zero`: the Weyl–Schouten theorem in dimension
  `n ≥ 4`.
* `isLocallyConformallyFlat_of_cottonTensor_eq_zero` and
  `isLocallyConformallyFlat_iff_cottonTensor_eq_zero`: the Cotton–Schouten theorem in dimension
  `n = 3`.
* `isLocallyConformallyFlat_iff_weylTensor_eq_zero_of_riemannianBundle_eq` and
  `isLocallyConformallyFlat_iff_cottonTensor_eq_zero_of_riemannianBundle_eq`: versions phrased in
  terms of an already-installed `RiemannianBundle` instance.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 2, p. 43.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* L. P. Eisenhart, *Riemannian Geometry*, Princeton University Press (1926), §28.
* É. Cotton, *Sur les variétés à trois dimensions*, Ann. Fac. Sci. Toulouse (2) 1 (1899),
  385–438, Chapter III, n° 18, p. 412.
-/

public section

open Bundle Filter TauCeti.Manifold
open scoped ContDiff Manifold Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- **Smooth initial-value family of conformal flattenings around an interior point.** Let `x₀` be
an interior point of `M` near which the Weyl and Cotton tensors of `g` vanish, in dimension at least
`3`. Around any `(c₀, ξ₀) : ℝ × TangentSpace I x₀` there exist open neighbourhoods `W` of `x₀` and
`Q` of `(c₀, ξ₀)` and a smooth family `Φ : M × (ℝ × TangentSpace I x₀) → ℝ` such that for every
`q ∈ Q`, the slice `y ↦ Φ (y, q)` has value `q.1` and `g`-gradient `q.2` at `x₀`, and the rescaled
metric `e^(2 Φ(·, q)) g` has vanishing curvature tensor at every point of `W`. -/
theorem exists_contMDiff_curvatureTensor_rescale_exp_eq_zero_family_of_isInteriorPoint
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
    ∃ (W : Set M) (Q : Set (ℝ × TangentSpace I x₀))
      (Φ : M × (ℝ × TangentSpace I x₀) → ℝ)
      (hΦ : ContMDiff (I.prod 𝓘(ℝ, ℝ × TangentSpace I x₀)) 𝓘(ℝ) ∞ Φ),
      IsOpen W ∧ x₀ ∈ W ∧ IsOpen Q ∧ (c₀, ξ₀) ∈ Q ∧
      ∀ q ∈ Q, Φ (x₀, q) = q.1 ∧ mgradient I (fun y ↦ Φ (y, q)) x₀ = q.2 ∧
        ∀ y ∈ W,
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g.rescale (fun z ↦ Real.exp (2 * Φ (z, q)))
              (Real.contDiff_exp.comp_contMDiff
                (contMDiff_const.mul (hΦ.comp (contMDiff_id.prodMk contMDiff_const))))
              (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩;
            (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  obtain ⟨W₀, Q, Φ, hW₀_open, hx₀W₀, hQ_open, hq₀Q, hΦ, hsol⟩ :=
    exists_contMDiff_hessian_eq_family_of_isInteriorPoint hx₀ hW hC c₀ ξ₀
  obtain ⟨W₁, hW₁_zero, hW₁_open, hx₀W₁⟩ := eventually_nhds_iff.1 hW
  refine ⟨W₀ ∩ W₁, Q, Φ, hΦ, hW₀_open.inter hW₁_open, ⟨hx₀W₀, hx₀W₁⟩, hQ_open, hq₀Q,
    fun q hq ↦ ?_⟩
  obtain ⟨hval, hgrad, hhess⟩ := hsol q hq
  refine ⟨hval, hgrad, fun y hy ↦ ?_⟩
  exact (g.curvatureTensor_leviCivitaConnection_rescale_eq_zero_iff
    (Real.contDiff_exp.comp_contMDiff
      (contMDiff_const.mul (hΦ.comp (contMDiff_id.prodMk contMDiff_const))))
    (fun _ ↦ Real.exp_pos _) (fun _ ↦ rfl) hn y).2 ⟨hW₁_zero y hy.2, hhess y hy.1⟩

/-- **Local flat conformal rescaling around an interior point.** In dimension at least `3`, if the
Weyl and Cotton tensors of `g` vanish near an interior point `x₀`, then for any `c : ℝ` and
`ξ : TangentSpace I x₀` there exists a globally smooth function `φ : M → ℝ` with `φ x₀ = c` and
`grad φ x₀ = ξ` such that `e^(2φ) g` has vanishing curvature tensor near `x₀`. -/
theorem exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 3 ≤ Module.finrank ℝ E) {x₀ : M} (hx₀ : I.IsInteriorPoint x₀)
    (hW : ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor y) = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).cottonTensor y) = 0)
    (c : ℝ) (ξ : TangentSpace I x₀) :
    ∃ (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ), φ x₀ = c ∧
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        mgradient I φ x₀ = ξ) ∧
      ∀ᶠ y in 𝓝 x₀,
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale (fun z ↦ Real.exp (2 * φ z))
            (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ))
            (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨W, Q, Φ, hΦ, hW_open, hx₀W, -, hqQ, hsol⟩ :=
    g.exists_contMDiff_curvatureTensor_rescale_exp_eq_zero_family_of_isInteriorPoint hn hx₀ hW hC c
      ξ
  obtain ⟨hval, hgrad, hflat⟩ := hsol (c, ξ) hqQ
  exact ⟨fun z ↦ Φ (z, (c, ξ)), hΦ.comp (contMDiff_id.prodMk contMDiff_const), hval, hgrad,
    eventually_of_mem (hW_open.mem_nhds hx₀W) hflat⟩

section Boundaryless

variable [BoundarylessManifold I M]

/-- **Smooth initial-value family of conformal flattenings on a boundaryless manifold.** -/
theorem exists_contMDiff_curvatureTensor_rescale_exp_eq_zero_family
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
    ∃ (W : Set M) (Q : Set (ℝ × TangentSpace I x₀))
      (Φ : M × (ℝ × TangentSpace I x₀) → ℝ)
      (hΦ : ContMDiff (I.prod 𝓘(ℝ, ℝ × TangentSpace I x₀)) 𝓘(ℝ) ∞ Φ),
      IsOpen W ∧ x₀ ∈ W ∧ IsOpen Q ∧ (c₀, ξ₀) ∈ Q ∧
      ∀ q ∈ Q, Φ (x₀, q) = q.1 ∧ mgradient I (fun y ↦ Φ (y, q)) x₀ = q.2 ∧
        ∀ y ∈ W,
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
            ⟨(g.rescale (fun z ↦ Real.exp (2 * Φ (z, q)))
              (Real.contDiff_exp.comp_contMDiff
                (contMDiff_const.mul (hΦ.comp (contMDiff_id.prodMk contMDiff_const))))
              (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩;
            (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 :=
  g.exists_contMDiff_curvatureTensor_rescale_exp_eq_zero_family_of_isInteriorPoint hn
    BoundarylessManifold.isInteriorPoint hW hC c₀ ξ₀

/-- **Local flat conformal rescaling on a boundaryless manifold.** -/
theorem exists_eventually_curvatureTensor_rescale_exp_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 3 ≤ Module.finrank ℝ E) {x₀ : M}
    (hW : ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor y) = 0)
    (hC : ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).cottonTensor y) = 0)
    (c : ℝ) (ξ : TangentSpace I x₀) :
    ∃ (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ), φ x₀ = c ∧
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        mgradient I φ x₀ = ξ) ∧
      ∀ᶠ y in 𝓝 x₀,
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale (fun z ↦ Real.exp (2 * φ z))
            (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ))
            (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 :=
  g.exists_eventually_curvatureTensor_rescale_exp_eq_zero_of_isInteriorPoint hn
    BoundarylessManifold.isInteriorPoint hW hC c ξ

/-- **Characterization of local conformal flatness in dimension at least `3`.** On a boundaryless
smooth manifold of dimension at least `3`, a smooth Riemannian metric is locally conformally flat
if and only if both its Weyl tensor and its Cotton tensor vanish identically. -/
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

/-- **Weyl–Schouten theorem in dimension at least `4` (equivalence).** On a boundaryless smooth
manifold of dimension `n ≥ 4`, a smooth Riemannian metric is locally conformally flat if and only
if its Weyl tensor vanishes identically. -/
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

/-- **Converse of the Weyl–Schouten theorem in dimension at least `4`.** On a boundaryless smooth
manifold of dimension `n ≥ 4`, a smooth Riemannian metric whose Weyl tensor vanishes everywhere is
locally conformally flat (Eisenhart 1926, §28; Lee–Parker 1987, p. 43). -/
theorem isLocallyConformallyFlat_of_weylTensor_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 4 ≤ Module.finrank ℝ E)
    (hW : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0) :
    g.IsLocallyConformallyFlat :=
  (g.isLocallyConformallyFlat_iff_weylTensor_eq_zero hn).2 hW

/-- **Cotton–Schouten theorem in dimension `3` (equivalence).** On a boundaryless smooth
`3`-manifold, a smooth Riemannian metric is locally conformally flat if and only if its Cotton
tensor vanishes identically. -/
theorem isLocallyConformallyFlat_iff_cottonTensor_eq_zero
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

/-- **Converse of the Cotton–Schouten theorem in dimension `3`.** On a boundaryless smooth
`3`-manifold, a smooth Riemannian metric whose Cotton tensor vanishes everywhere is locally
conformally flat (Cotton 1899, Chapter III, n° 18, p. 412). -/
theorem isLocallyConformallyFlat_of_cottonTensor_eq_zero
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : Module.finrank ℝ E = 3)
    (hC : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0) :
    g.IsLocallyConformallyFlat :=
  (g.isLocallyConformallyFlat_iff_cottonTensor_eq_zero hn).2 hC

/-- **Weyl–Schouten in dimension at least `4` for an installed `RiemannianBundle`.** -/
theorem isLocallyConformallyFlat_iff_weylTensor_eq_zero_of_riemannianBundle_eq
    [inst : RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : RiemannianBundle.g = g.toRiemannianMetric) (hn : 4 ≤ Module.finrank ℝ E) :
    g.IsLocallyConformallyFlat ↔
      ∀ x, (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0 := by
  obtain ⟨_⟩ := inst
  subst hg
  exact g.isLocallyConformallyFlat_iff_weylTensor_eq_zero hn

/-- **Cotton–Schouten in dimension `3` for an installed `RiemannianBundle`.** -/
theorem isLocallyConformallyFlat_iff_cottonTensor_eq_zero_of_riemannianBundle_eq
    [inst : RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : RiemannianBundle.g = g.toRiemannianMetric) (hn : Module.finrank ℝ E = 3) :
    g.IsLocallyConformallyFlat ↔
      ∀ x, (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0 := by
  obtain ⟨_⟩ := inst
  subst hg
  exact g.isLocallyConformallyFlat_iff_cottonTensor_eq_zero hn

end Boundaryless

end Bundle.ContMDiffRiemannianMetric
