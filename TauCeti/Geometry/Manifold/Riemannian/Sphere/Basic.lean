/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Riemannian.Induced
import TauCeti.Geometry.Manifold.Riemannian.MetricBridge
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The round metric on the unit sphere

The unit sphere `Sⁿ` of a real inner product space `E` of dimension `n + 1` is an analytic manifold
modelled on `ℝⁿ` (Mathlib's stereographic atlas), and its inclusion into `E` is an analytic
immersion. The *round metric* is the Riemannian metric induced by this immersion: the inner
product of two tangent vectors is the inner product in `E` of their images under the differential
of the inclusion. This file installs it as the `RiemannianBundle` instance on the tangent bundle of
the sphere, together with its analyticity.

With `E = EuclideanSpace ℝ (Fin 4)` this is the round three-sphere `S³`, the spherical one of
Thurston's eight model geometries.

## Main definitions

* `TauCeti.sphereTangentEquiv`: the isometric identification of tangent spaces with the
  orthogonal complements of their radius vectors.
* `TauCeti.sphereRoundMetric`: the analytic round metric on the unit sphere.
* `TauCeti.instRiemannianBundleSphere`, `TauCeti.instIsContMDiffRiemannianBundleSphere` and
  `TauCeti.instIsContinuousRiemannianBundleSphere`: the corresponding instances.

## Main statements

* `TauCeti.inner_tangentSpace_sphere`: the round inner product of two tangent vectors is the inner
  product of their images in `E`.
* `TauCeti.norm_tangentSpace_sphere`: the round norm of a tangent vector is the norm of its image
  in `E`.
* `TauCeti.inner_coe_mvfderiv_subtypeVal_sphere`: tangent vectors are orthogonal to the radius.
* `TauCeti.inner_mvfderiv_subtypeVal_sphere_self_pos`: nonzero tangent vectors have positive
  squared length in `E`.
* `TauCeti.contMDiff_coe_sphereTangentEquiv`: reading a tangent vector in `E` via
  `sphereTangentEquiv` is `C^m` on the tangent bundle.
* `TauCeti.edist_le_riemannianEDist_sphere`: the chordal distance in `E` is at most the round
  distance.
* `TauCeti.tendsto_abs_nhdsGT_zero_of_inner_mfderiv_eq_mul_sphereRoundMetric`,
  `TauCeti.apply_zero_of_inner_mfderiv_eq_mul_sphereRoundMetric`: if a continuous Riemannian metric
  on `E` (`dim E ≥ 2`) restricts on concentric spheres of small positive radius `r` to
  `f(r)² g_(Sⁿ)` for a function `f : ℝ → ℝ`, then `|f(r)| → 0` as `r → 0⁺`, so `f(0) = 0` when `f`
  is right-continuous at `0` (`ContinuousWithinAt f (Ici 0) 0`).

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (the round metric as an induced metric).
-/

public section

open Bundle Filter Metric Module Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The round metric on the unit sphere of `E`: the analytic Riemannian metric induced by the
inclusion of the sphere into `E`. -/
def sphereRoundMetric :
    ContMDiffRiemannianMetric (𝓡 n) ω (EuclideanSpace ℝ (Fin n))
      (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
  inducedRiemannianMetric (n := ω) ((↑) : sphere (0 : E) 1 → E) contMDiff_coe_sphere
    injective_mvfderiv_subtypeVal_sphere

/-- The round metric evaluates the inner product of `E` on the images of tangent vectors under the
differential of the inclusion. -/
@[simp]
theorem sphereRoundMetric_inner (x : sphere (0 : E) 1) (v w : TangentSpace (𝓡 n) x) :
    (sphereRoundMetric (E := E)).inner x v w =
      inner ℝ (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v)
        (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x w) :=
  inducedRiemannianMetric_inner _ _ _ x v w

/-- The unit sphere is a Riemannian manifold for its round metric. -/
instance instRiemannianBundleSphere :
    RiemannianBundle (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
  ⟨(sphereRoundMetric (E := E)).toRiemannianMetric⟩

/-- The round metric is analytic. -/
instance instIsContMDiffRiemannianBundleSphere :
    IsContMDiffRiemannianBundle (𝓡 n) ω (EuclideanSpace ℝ (Fin n))
      (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
  Bundle.instIsContMDiffRiemannianBundle (sphereRoundMetric (E := E))

/-- The round metric is continuous. -/
instance instIsContinuousRiemannianBundleSphere :
    IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
  Bundle.instIsContinuousRiemannianBundle
    (sphereRoundMetric (E := E)).toContinuousRiemannianMetric

/-- The round inner product of two tangent vectors to the sphere is the inner product in `E` of
their images under the differential of the inclusion. -/
@[simp]
theorem inner_tangentSpace_sphere (x : sphere (0 : E) 1) (v w : TangentSpace (𝓡 n) x) :
    inner ℝ v w =
      inner ℝ (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v)
        (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x w) :=
  sphereRoundMetric_inner x v w

/-- The round norm of a tangent vector to the sphere is the norm in `E` of its image under the
differential of the inclusion. -/
@[simp]
theorem norm_tangentSpace_sphere (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    ‖v‖ = ‖mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_tangentSpace_sphere]

/-- The differential of the unit-sphere inclusion identifies its round tangent space
isometrically with the orthogonal complement of the radius vector. -/
def sphereTangentEquiv (x : sphere (0 : E) 1) :
    TangentSpace (𝓡 n) x ≃ₗᵢ[ℝ] (ℝ ∙ (x : E))ᗮ :=
  let L : TangentSpace (𝓡 n) x →ₗᵢ[ℝ] E :=
    { toLinearMap := (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x).toLinearMap
      norm_map' := fun v => (norm_tangentSpace_sphere x v).symm }
  L.equivRange.trans (LinearIsometryEquiv.ofEq _ _ (range_mvfderiv_subtypeVal x))

/-- In ambient coordinates, the tangent-space identification is the differential of
inclusion. -/
@[simp]
theorem coe_sphereTangentEquiv_apply (x : sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) x) :
    (sphereTangentEquiv x v : E) =
      mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v := by
  simp only [sphereTangentEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.coe_ofEq_apply]
  rw [LinearIsometry.equivRange_apply_coe]
  exact mvfderiv_apply_eq_mfderiv_apply _ x v

/-- The image of a tangent vector to the sphere under the differential of the inclusion is the
value of `TauCeti.sphereTangentEquiv` on it. -/
theorem mvfderiv_subtypeVal_sphere_eq_sphereTangentEquiv (x : sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v = sphereTangentEquiv x v := by
  rw [coe_sphereTangentEquiv_apply, mvfderiv_apply_eq_mfderiv_apply]

/-- Reading a tangent vector to the unit sphere in the ambient inner product space `E` via
`sphereTangentEquiv` is `C^m` for every `m : ℕ∞ω` (including `m = ω`). -/
theorem contMDiff_coe_sphereTangentEquiv {m : ℕ∞ω} :
    ContMDiff (𝓡 n).tangent 𝓘(ℝ, E) m
      (fun p : TangentBundle (𝓡 n) (sphere (0 : E) 1) ↦
        (sphereTangentEquiv p.proj p.snd : E)) := by
  have htan : ContMDiff (𝓡 n).tangent 𝓘(ℝ, E).tangent m
      (tangentMap (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E)) :=
    (contMDiff_coe_sphere (E := E) (n := n) (m := ω)).contMDiff_tangentMap le_top
  exact ((contMDiff_snd_tangentBundle_modelSpace E 𝓘(ℝ, E)).comp htan).congr fun p ↦
    coe_sphereTangentEquiv_apply p.proj p.snd

/-- The image of a tangent vector under the differential of the sphere inclusion is orthogonal
to the radius vector. -/
theorem inner_coe_mvfderiv_subtypeVal_sphere (x : sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) x) :
    inner ℝ (x : E) (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v) = 0 := by
  have h := (sphereTangentEquiv x v).property
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, coe_sphereTangentEquiv_apply] at h
  rwa [mvfderiv_apply_eq_mfderiv_apply]

/-- A nonzero tangent vector to the unit sphere has positive squared length in `E`: the
differential of the inclusion is injective. -/
theorem inner_mvfderiv_subtypeVal_sphere_self_pos (x : sphere (0 : E) 1)
    {v : TangentSpace (𝓡 n) x} (hv : v ≠ 0) :
    0 < inner ℝ (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v)
      (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v) :=
  real_inner_self_pos.2 fun h ↦
    hv (injective_mvfderiv_subtypeVal_sphere x (h.trans (map_zero _).symm))

/-- **The chordal distance is at most the round distance.** The distance in `E` between two points
of the unit sphere is at most their Riemannian distance for the round metric: the inclusion of the
sphere into `E` preserves the length of tangent vectors, so every path on the sphere is at least as
long as the chord between its endpoints. -/
theorem edist_le_riemannianEDist_sphere (x y : sphere (0 : E) 1) :
    edist x y ≤ Manifold.riemannianEDist (𝓡 n) x y := by
  have h := Manifold.edist_le_mul_riemannianEDist (I := 𝓡 n) (C := 1)
    (contMDiff_coe_sphere (E := E) (n := n)) one_ne_zero (fun p v ↦ ?_) x y
  · simpa [Subtype.edist_eq] using h
  rw [ENNReal.coe_one, one_mul, ← ofReal_norm, ← ofReal_norm, ← norm_tangentSpace_sphere]

/-- Let `E` be a real inner product space of dimension `n + 1` with `0 < n` (`dim E ≥ 2`), and let
`g` be a continuous Riemannian metric on `E`. If on concentric spheres `u ↦ r • u` of small positive
radius `r`, `g` restricts to `f(r)² g_(Sⁿ)`, then `|f(r)| → 0` as `r → 0⁺`. The hypothesis `0 < n`
cannot be dropped: when `n = 0` (`E = ℝ`), `S⁰` is discrete (`T_u S⁰ = 0`) and `f = 1` describes the
flat metric `dx²` across `0`. -/
theorem tendsto_abs_nhdsGT_zero_of_inner_mfderiv_eq_mul_sphereRoundMetric (hn : 0 < n)
    (g : ContinuousRiemannianMetric E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)) {f : ℝ → ℝ}
    (hpull : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ (u : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) u),
      g.inner (r • (u : E))
        (mfderiv (𝓡 n) 𝓘(ℝ, E) (fun q : sphere (0 : E) 1 ↦ r • (q : E)) u v)
        (mfderiv (𝓡 n) 𝓘(ℝ, E) (fun q : sphere (0 : E) 1 ↦ r • (q : E)) u v) =
        f r ^ 2 * (sphereRoundMetric (E := E)).inner u v v) :
    Tendsto (fun r ↦ |f r|) (𝓝[>] 0) (𝓝 0) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by
    rw [Fact.out (p := finrank ℝ E = n + 1)]; omega)
  obtain ⟨u⟩ : Nonempty (sphere (0 : E) 1) :=
    Set.Nonempty.to_subtype (NormedSpace.sphere_nonempty.2 zero_le_one)
  have hfin : 0 < finrank ℝ (TangentSpace (𝓡 n) u) := by
    rw [(tangentSpaceCastModel (𝓡 n) u).toLinearEquiv.finrank_eq, finrank_euclideanSpace_fin]
    exact hn
  have : Nontrivial (TangentSpace (𝓡 n) u) := Module.nontrivial_of_finrank_pos hfin
  obtain ⟨v, hv⟩ := exists_ne (0 : TangentSpace (𝓡 n) u)
  have hpos : 0 < (sphereRoundMetric (E := E)).inner u v v :=
    (sphereRoundMetric (E := E)).pos u v hv
  set w : E := mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) u v
  have heq : (fun r : ℝ ↦ f r ^ 2) =ᶠ[𝓝[>] (0 : ℝ)] fun r : ℝ ↦
      r ^ 2 * g.inner (r • (u : E)) ((NormedSpace.fromTangentSpace (r • (u : E))).symm w)
        ((NormedSpace.fromTangentSpace (r • (u : E))).symm w) /
        (sphereRoundMetric (E := E)).inner u v v := by
    filter_upwards [hpull] with r hr
    have hdf : mfderiv (𝓡 n) 𝓘(ℝ, E) (fun q : sphere (0 : E) 1 ↦ r • (q : E)) u v =
        r • (NormedSpace.fromTangentSpace (r • (u : E))).symm w := by
      apply (NormedSpace.fromTangentSpace (r • (u : E))).injective
      rw [NormedSpace.fromTangentSpace_apply, ← mvfderiv_apply_eq_mfderiv_apply,
        mvfderiv_const_smul ((contMDiff_coe_sphere (E := E) (n := n) (m := 1) u).mdifferentiableAt
          one_ne_zero) r,
        _root_.smul_apply, map_smul, ContinuousLinearEquiv.apply_symm_apply]
    have hpull_r := hr u v
    rw [hdf, map_smul, map_smul, _root_.smul_apply, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, ← sq] at hpull_r
    exact (eq_div_iff hpos.ne').2 hpull_r.symm
  have hcont_g : Continuous fun r : ℝ ↦
      g.inner (r • (u : E)) ((NormedSpace.fromTangentSpace (r • (u : E))).symm w)
        ((NormedSpace.fromTangentSpace (r • (u : E))).symm w) :=
    (g.continuous_inner_const_vector w w).comp (continuous_id.smul continuous_const)
  have hlim : Tendsto (fun r : ℝ ↦
      r ^ 2 * g.inner (r • (u : E)) ((NormedSpace.fromTangentSpace (r • (u : E))).symm w)
        ((NormedSpace.fromTangentSpace (r • (u : E))).symm w) /
        (sphereRoundMetric (E := E)).inner u v v) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((((continuous_pow 2).mul hcont_g).div_const _).continuousAt (x := 0)).tendsto
      |>.mono_left nhdsWithin_le_nhds
  have hsq : Tendsto (fun r : ℝ ↦ f r ^ 2) (𝓝[>] 0) (𝓝 0) := hlim.congr' heq.symm
  simpa only [Real.sqrt_zero] using
    (Real.continuous_sqrt.continuousAt.tendsto.comp hsq).congr fun r ↦ Real.sqrt_sq_eq_abs (f r)

/-- If `f : ℝ → ℝ` is right-continuous at `0` (`ContinuousWithinAt f (Ici 0) 0`) and a continuous
Riemannian metric `g` on `E` (`dim E = n + 1`, `0 < n`) restricts on concentric spheres
`u ↦ r • u` of small positive radius `r` to `f(r)² g_(Sⁿ)`, then `f 0 = 0`; in particular
`¬ 0 < f 0`. -/
theorem apply_zero_of_inner_mfderiv_eq_mul_sphereRoundMetric (hn : 0 < n)
    (g : ContinuousRiemannianMetric E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)) {f : ℝ → ℝ}
    (hf : ContinuousWithinAt f (Ici 0) 0)
    (hpull : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ (u : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) u),
      g.inner (r • (u : E))
        (mfderiv (𝓡 n) 𝓘(ℝ, E) (fun q : sphere (0 : E) 1 ↦ r • (q : E)) u v)
        (mfderiv (𝓡 n) 𝓘(ℝ, E) (fun q : sphere (0 : E) 1 ↦ r • (q : E)) u v) =
        f r ^ 2 * (sphereRoundMetric (E := E)).inner u v v) :
    f 0 = 0 := by
  have : (𝓝[>] (0 : ℝ)).NeBot := nhdsGT_neBot (0 : ℝ)
  have h1 : Tendsto (fun r ↦ |f r|) (𝓝[>] 0) (𝓝 |f 0|) :=
    (continuous_abs.continuousAt.tendsto.comp hf).mono_left
      (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  exact abs_eq_zero.1 (tendsto_nhds_unique h1
    (tendsto_abs_nhdsGT_zero_of_inner_mfderiv_eq_mul_sphereRoundMetric hn g hpull))

end TauCeti
