/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Analysis.ODE.Gronwall.TwoSided

/-!
# Ricci bounds and distance comparison between time slices

For a family of smooth Riemannian metrics satisfying the diagonal Ricci equation, a quadratic
Ricci bound gives two-sided exponential comparison of metric pairings. Applying the intrinsic
distance comparison theorem to the identity diffeomorphism between the native metric copies
gives distortion factor `exp (K * |t - s|)`. The same bounds imply joint continuity of extended
distance and propagate completeness from one time slice.

The hypotheses are stated directly for the native Levi-Civita Ricci tensor and allow arbitrary
convex time sets, including their endpoints. The distance conclusions use a global spatial
Ricci bound; local curvature bounds and compact localization are separate results.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Lemma 3.15(1).
* Formalization references: https://github.com/frenzymath/lean-eval-submissions and
  https://github.com/frenzymath/PoincareConjecture.
-/

public section

open Bundle Filter Manifold Set TauCeti TauCeti.WithMetric
open scoped ContDiff Manifold NNReal ENNReal Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- A Ricci quadratic bound at a fixed point and vector gives exponential comparison of the
metric pairing between any two included times in a convex time set. Only the diagonal Ricci
equation at that point and vector is required. The coefficient may be signed. -/
theorem inner_self_exp_bounds_of_ricci_bound {S : Set ℝ} (hS : Convex ℝ S)
    (x : M) (v : TangentSpace I x)
    (heq : ∀ t ∈ S,
      HasDerivWithinAt (fun τ ↦ (g τ).inner x v v)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v)) S t)
    (K : ℝ)
    (hRic : ∀ t ∈ S, |(letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v)| ≤ K * (g t).inner x v v)
    {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) :
    Real.exp (-(2 * K) * |b - a|) * (g a).inner x v v ≤ (g b).inner x v v ∧
      (g b).inner x v v ≤ Real.exp ((2 * K) * |b - a|) * (g a).inner x v v := by
  let q := fun τ ↦ (g τ).inner x v v
  let c := 2 * K
  have hsub : Icc (min a b) (max a b) ⊆ S := hS.ordConnected.uIcc_subset ha hb
  have hq0 (τ : ℝ) : 0 ≤ q τ := by
    by_cases hv : v = 0
    · simp [q, hv]
    · exact ((g τ).pos x v hv).le
  have hd (τ : ℝ) (hτ : τ ∈ Icc (min a b) (max a b)) :
      HasDerivWithinAt q (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g τ).toRiemannianMetric⟩
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v))
        (Icc (min a b) (max a b)) τ :=
    (heq τ (hsub hτ)).mono hsub
  have hbound (τ : ℝ) (hτ : τ ∈ Icc (min a b) (max a b)) :
      ‖-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g τ).toRiemannianMetric⟩
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v)‖ ≤ c * ‖q τ‖ + 0 := by
    have h := mul_le_mul_of_nonneg_left (hRic τ (hsub hτ)) (by norm_num : (0 : ℝ) ≤ 2)
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 τ), c, q, mul_assoc] using h
  have hu := norm_le_gronwallBound_of_norm_derivWithin_le
    left_mem_uIcc hd (le_refl ‖q a‖)
    hbound b right_mem_uIcc
  have hl := norm_le_gronwallBound_of_norm_derivWithin_le
    right_mem_uIcc hd (le_refl ‖q b‖)
    hbound a left_mem_uIcc
  simp only [gronwallBound_ε0, Real.norm_eq_abs, abs_of_nonneg (hq0 _), abs_sub_comm a b]
    at hu hl
  rw [mul_comm (q b)] at hl
  constructor
  · have he : Real.exp (-(c * |b - a|)) * Real.exp (c * |b - a|) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h := mul_le_mul_of_nonneg_left hl (Real.exp_pos (-(c * |b - a|))).le
    rw [← mul_assoc, he, one_mul] at h
    simpa only [c, q, neg_mul] using h
  · simpa only [c, q, mul_comm] using hu

/-- A global Ricci quadratic bound controls the intrinsic extended distance between two time
slices by `exp (K * |t - s|)`. The distance is that of the native copies carrying the two metrics;
points in distinct components and included time endpoints are allowed. -/
theorem riemannianEDist_le_exp_mul_of_ricci_bound {S : Set ℝ} (hS : Convex ℝ S)
    (heq : ∀ t ∈ S, ∀ x (v : TangentSpace I x),
      HasDerivWithinAt (fun τ ↦ (g τ).inner x v v)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v)) S t)
    (K : ℝ) (hRic : ∀ t ∈ S, ∀ x (v : TangentSpace I x),
      |(letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v)| ≤ K * (g t).inner x v v)
    {s t : ℝ} (hs : s ∈ S) (ht : t ∈ S) (x y : M) :
    riemannianEDist I (toWithMetric (g t) x) (toWithMetric (g t) y) ≤
      ENNReal.ofReal (Real.exp (K * |t - s|)) *
        riemannianEDist I (toWithMetric (g s) x) (toWithMetric (g s) y) := by
  let C : ℝ≥0 := .mk (Real.exp (K * |t - s|)) (Real.exp_pos _).le
  have hC0 : C ≠ 0 := by
    apply NNReal.coe_ne_zero.mp
    exact (Real.exp_pos (K * |t - s|)).ne'
  have hsq (z : M) (v : TangentSpace I z) :
      (g t).inner z v v ≤ (C : ℝ) ^ 2 * (g s).inner z v v := by
    have h := (inner_self_exp_bounds_of_ricci_bound g hS z v
      (fun τ hτ ↦ heq τ hτ z v) K (fun τ hτ ↦ hRic τ hτ z v) hs ht).2
    have he : Real.exp ((2 * K) * |t - s|) = Real.exp (K * |t - s|) ^ 2 := by
      rw [← Real.exp_natCast_mul]
      congr 1
      ring
    rw [he] at h
    simpa only [C, NNReal.coe_mk] using h
  have hn (z : WithMetric (g s)) (v : TangentSpace I z) :
      ‖mfderiv I I (diffeomorphWithMetric (g s) (g t) 1) z v‖ ≤ C * ‖v‖ := by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg C.coe_nonneg (norm_nonneg _)) two_ne_zero).1
    have htN : ‖mfderiv I I (diffeomorphWithMetric (g s) (g t) 1) z v‖ ^ 2 =
        (g t).inner z.ofWithMetric v v := by
      rw [← real_inner_self_eq_norm_sq, inner_def, mfderiv_ofWithMetric_apply]
      have hd : mfderiv I I (diffeomorphWithMetric (g s) (g t) 1) z v = v :=
        DFunLike.congr_fun (mfderiv_diffeomorphWithMetric (g t) 1 z) v
      rw [hd, diffeomorphWithMetric_apply, ofWithMetric_toWithMetric]
    have hsN : ‖v‖ ^ 2 = (g s).inner z.ofWithMetric v v := by
      rw [← real_inner_self_eq_norm_sq, inner_def, mfderiv_ofWithMetric_apply]
    rw [mul_pow, htN, hsN]
    exact hsq z.ofWithMetric v
  have hcoe : (C : ℝ≥0∞) = ENNReal.ofReal (Real.exp (K * |t - s|)) :=
    ENNReal.ofReal_coe_nnreal.symm
  simpa only [diffeomorphWithMetric_apply, ofWithMetric_toWithMetric, hcoe] using
    (TauCeti.Manifold.riemannianEDist_le_mul
      (diffeomorphWithMetric (g s) (g t) 1).contMDiff hC0 hn
      (toWithMetric (g s) x) (toWithMetric (g s) y))

/-- The reverse exponential estimate for intrinsic extended distance under a global Ricci
quadratic bound. This is valid also for infinite distances. -/
theorem exp_mul_riemannianEDist_le_of_ricci_bound {S : Set ℝ} (hS : Convex ℝ S)
    (heq : ∀ t ∈ S, ∀ x (v : TangentSpace I x),
      HasDerivWithinAt (fun τ ↦ (g τ).inner x v v)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v)) S t)
    (K : ℝ) (hRic : ∀ t ∈ S, ∀ x (v : TangentSpace I x),
      |(letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v)| ≤ K * (g t).inner x v v)
    {s t : ℝ} (hs : s ∈ S) (ht : t ∈ S) (x y : M) :
    ENNReal.ofReal (Real.exp (-K * |t - s|)) *
        riemannianEDist I (toWithMetric (g s) x) (toWithMetric (g s) y) ≤
      riemannianEDist I (toWithMetric (g t) x) (toWithMetric (g t) y) := by
  have h := riemannianEDist_le_exp_mul_of_ricci_bound g hS heq K hRic ht hs x y
  rw [abs_sub_comm s t] at h
  have he : ENNReal.ofReal (Real.exp (-K * |t - s|)) *
      ENNReal.ofReal (Real.exp (K * |t - s|)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    simp
  have h' := mul_le_mul_right h (ENNReal.ofReal (Real.exp (-K * |t - s|)))
  rwa [← mul_assoc, he, one_mul] at h'

/-- Under a global Ricci quadratic bound, intrinsic extended distance is jointly continuous in
time and both spatial endpoints, on the included convex time set. The codomain is `ℝ≥0∞` with its
order topology, so no finiteness or connectedness premise is required. -/
theorem continuousOn_riemannianEDist_of_ricci_bound {S : Set ℝ} (hS : Convex ℝ S)
    (heq : ∀ t ∈ S, ∀ x (v : TangentSpace I x),
      HasDerivWithinAt (fun τ ↦ (g τ).inner x v v)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v)) S t)
    (K : ℝ) (hRic : ∀ t ∈ S, ∀ x (v : TangentSpace I x),
      |(letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v)| ≤
        K * (g t).inner x v v) :
    ContinuousOn (fun p : ℝ × M × M ↦
      riemannianEDist I (toWithMetric (g p.1) p.2.1) (toWithMetric (g p.1) p.2.2))
      (S ×ˢ Set.univ) := by
  rintro ⟨s, x, y⟩ hp
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let : PseudoEMetricSpace (WithMetric (g s)) := .ofRiemannianMetric I (WithMetric (g s))
  have hd : Continuous (fun p : ℝ × M × M ↦
      riemannianEDist I (toWithMetric (g s) p.2.1) (toWithMetric (g s) p.2.2)) := by
    have hx : Continuous (fun p : ℝ × M × M ↦ toWithMetric (g s) p.2.1) :=
      continuous_toWithMetric.comp (continuous_fst.comp continuous_snd)
    have hy : Continuous (fun p : ℝ × M × M ↦ toWithMetric (g s) p.2.2) :=
      continuous_toWithMetric.comp (continuous_snd.comp continuous_snd)
    -- The chosen metric-space structure identifies edist with the intrinsic distance.
    simpa only [IsRiemannianManifold.out (I := I)] using hx.edist hy
  have he (k : ℝ) : Filter.Tendsto (fun p : ℝ × M × M ↦
      ENNReal.ofReal (Real.exp (k * |p.1 - s|))) (𝓝 (s, x, y)) (𝓝 1) := by
    have hc : Continuous (fun p : ℝ × M × M ↦
        ENNReal.ofReal (Real.exp (k * |p.1 - s|))) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa using hc.tendsto (s, x, y)
  have hlim (k : ℝ) := ENNReal.Tendsto.mul (he k) (Or.inl one_ne_zero)
    (hd.tendsto (s, x, y)) (Or.inr ENNReal.one_ne_top)
  simp only [one_mul] at hlim
  apply (hlim (-K)).mono_left inf_le_left |>.squeeze' ((hlim K).mono_left inf_le_left)
  · filter_upwards [self_mem_nhdsWithin] with p hp'
    exact exp_mul_riemannianEDist_le_of_ricci_bound g hS heq K hRic hp.1 hp'.1
      p.2.1 p.2.2
  · filter_upwards [self_mem_nhdsWithin] with p hp'
    exact riemannianEDist_le_exp_mul_of_ricci_bound g hS heq K hRic hp.1 hp'.1
      p.2.1 p.2.2

/-- A global Ricci quadratic bound propagates completeness from one included time slice to any
other. Both copies carry their intrinsic Riemannian extended distances. Regularity of the
underlying topology follows from the finite-dimensional Hausdorff manifold hypotheses. -/
theorem completeSpace_of_ricci_bound {S : Set ℝ} (hS : Convex ℝ S)
    (heq : ∀ t ∈ S, ∀ x (v : TangentSpace I x),
      HasDerivWithinAt (fun τ ↦ (g τ).inner x v v)
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v)) S t)
    (K : ℝ) (hRic : ∀ t ∈ S, ∀ x (v : TangentSpace I x),
      |(letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v)| ≤ K * (g t).inner x v v)
    {s t : ℝ} (hs : s ∈ S) (ht : t ∈ S) :
    letI : RegularSpace M := by
      have : LocallyCompactSpace H := I.locallyCompactSpace
      have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
      infer_instance
    letI : PseudoEMetricSpace (WithMetric (g s)) :=
      .ofRiemannianMetric I (WithMetric (g s))
    CompleteSpace (WithMetric (g s)) →
      letI : PseudoEMetricSpace (WithMetric (g t)) :=
        .ofRiemannianMetric I (WithMetric (g t))
      CompleteSpace (WithMetric (g t)) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let : PseudoEMetricSpace (WithMetric (g s)) := .ofRiemannianMetric I (WithMetric (g s))
  let : PseudoEMetricSpace (WithMetric (g t)) := .ofRiemannianMetric I (WithMetric (g t))
  intro hc
  have : CompleteSpace (WithMetric (g s)) := hc
  let C : ℝ≥0 := .mk (Real.exp (K * |s - t|)) (Real.exp_pos _).le
  have hL : LipschitzWith C (fun x : WithMetric (g t) ↦ toWithMetric (g s) x.ofWithMetric) := by
    intro x y
    -- Convert both metric-copy distances through their Riemannian-manifold instances.
    rw [IsRiemannianManifold.out (I := I), IsRiemannianManifold.out (I := I)]
    have h := riemannianEDist_le_exp_mul_of_ricci_bound g hS heq K hRic ht hs
      x.ofWithMetric y.ofWithMetric
    have hcoe : (C : ℝ≥0∞) = ENNReal.ofReal (Real.exp (K * |s - t|)) :=
      ENNReal.ofReal_coe_nnreal.symm
    simpa only [toWithMetric_ofWithMetric, hcoe] using h
  exact CompleteSpace.of_comp_eq_id
    (fun x : WithMetric (g s) ↦ toWithMetric (g t) x.ofWithMetric)
    (fun x : WithMetric (g t) ↦ toWithMetric (g s) x.ofWithMetric)
    (by
      funext x
      simp only [Function.comp_apply, toWithMetric_ofWithMetric, id_eq])
    (continuous_toWithMetric.comp continuous_ofWithMetric) hL.uniformContinuous

end TauCeti.Manifold
