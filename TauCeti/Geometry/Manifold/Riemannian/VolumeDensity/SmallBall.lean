/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Distortion
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Conformal
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Total
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Distance
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.WithMetric

/-!
# Small-ball volume bounds and rescaling laws

This file develops the small-ball volume lower bound and scaling/isometry laws for smooth
Riemannian manifolds:

* `TauCeti.euclideanUnitBallVolume`: the volume `ωₙ = √πⁿ / Γ(n/2 + 1)` of the unit ball in `ℝⁿ`,
  with positivity (`TauCeti.euclideanUnitBallVolume_pos`) and `ω₃ = 4 / 3 * π`
  (`TauCeti.euclideanUnitBallVolume_three`).
* `TauCeti.WithMetric.riemannianEDist_rescale_const` and
  `TauCeti.WithMetric.riemannianVolume_ball_rescale_const`: multiplying a smooth metric by a
  positive constant `c` scales Riemannian distance by `√c` and ball volume by `c^(n/2)` at
  rescaled radius `r / √c`.
* `TauCeti.RiemannianIsometry.riemannianVolume_setOf_riemannianEDist_lt`: Riemannian isometries
  preserve the Riemannian volumes of intrinsic metric balls.
* `TauCeti.Manifold.exists_pos_forall_riemannianVolume_ball_ge`: on every compact, boundaryless,
  positive-dimensional smooth Riemannian manifold, for any `θ < 1` there exists `r₀ > 0` such that
  every Riemannian ball of radius `0 < r ≤ r₀` has volume at least `θ * ωₙ * rⁿ`.

The proof of the uniform small-ball volume lower bound avoids any variable-base derivative
computation by combining the fixed-base normal-ball derivative bounds of
`TauCeti.Manifold.exists_isNormalDomain_ball_norm_mfderiv_bounds`, Hadamard's determinant inequality
(`Matrix.re_det_gram_le_prod_norm_sq`), and finite covering by normal neighbourhoods.
-/

public section

open Bundle Manifold MeasureTheory Metric Set
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal Topology

noncomputable section

namespace TauCeti

/-! ### Volume of the Euclidean unit ball -/

/-- The Lebesgue volume `ωₙ = √π ^ n / Γ(n / 2 + 1)` of the unit Euclidean ball in `ℝⁿ`. -/
def euclideanUnitBallVolume (n : ℕ) : ℝ :=
  Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)

/-- The Euclidean unit ball volume constant `ωₙ` is strictly positive in every dimension. -/
theorem euclideanUnitBallVolume_pos (n : ℕ) : 0 < euclideanUnitBallVolume n := by
  unfold euclideanUnitBallVolume
  have _ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have _ : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  positivity

/-- In dimension three, the Euclidean unit ball has volume `4 / 3 * π`. -/
@[simp]
theorem euclideanUnitBallVolume_three :
    euclideanUnitBallVolume 3 = 4 / 3 * Real.pi := by
  have h1 := EuclideanSpace.volume_ball (Fin 3) 0 1
  have h2 := InnerProductSpace.volume_ball_of_dim_odd (E := EuclideanSpace ℝ (Fin 3))
    (k := 1) (by rw [finrank_euclideanSpace_fin]) 0 1
  rw [h1] at h2
  simp only [Fintype.card_fin, finrank_euclideanSpace_fin, ENNReal.ofReal_one, one_pow,
    one_mul] at h2
  have hfact : ((Nat.doubleFactorial 3 : ℕ) : ℝ) = 3 := by rfl
  have heq : Real.sqrt Real.pi ^ 3 / Real.Gamma ((3 : ℕ) / 2 + 1) =
      Real.pi ^ 1 * 2 ^ (1 + 1) / ((Nat.doubleFactorial 3 : ℕ) : ℝ) := by
    refine (ENNReal.ofReal_eq_ofReal_iff ?_ ?_).mp h2
    · have := euclideanUnitBallVolume_pos 3
      unfold euclideanUnitBallVolume at this
      push_cast at this
      exact this.le
    · positivity
  push_cast at heq
  have h3 : euclideanUnitBallVolume 3 = Real.sqrt Real.pi ^ 3 / Real.Gamma ((3 : ℝ) / 2 + 1) :=
    rfl
  rw [h3, heq, hfact]
  ring

/-- The volume of an open ball in a nontrivial finite-dimensional inner product space in terms of
`euclideanUnitBallVolume`. -/
theorem InnerProductSpace.volume_ball_eq_euclideanUnitBallVolume
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [Nontrivial V] [MeasurableSpace V] [BorelSpace V] (x : V) (r : ℝ) :
    volume (Metric.ball x r) =
      ENNReal.ofReal r ^ Module.finrank ℝ V *
        ENNReal.ofReal (euclideanUnitBallVolume (Module.finrank ℝ V)) :=
  InnerProductSpace.volume_ball x r

/-! ### Openness of intrinsic Riemannian balls -/

section OpenBall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- An intrinsic open Riemannian ball `{y | riemannianEDist I x y < r}` is open in `M`. -/
theorem isOpen_setOf_riemannianEDist_lt
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] (x : M) (r : ℝ≥0∞) :
    IsOpen {y : M | Manifold.riemannianEDist I x y < r} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  change Manifold.riemannianEDist I x y < r at hy
  have hne : Manifold.riemannianEDist I x y ≠ ⊤ := ne_top_of_lt hy
  have hc : 0 < r - Manifold.riemannianEDist I x y := tsub_pos_of_lt hy
  filter_upwards [_root_.eventually_riemannianEDist_lt I y hc] with z hz
  calc
    Manifold.riemannianEDist I x z
        ≤ Manifold.riemannianEDist I x y + Manifold.riemannianEDist I y z :=
        Manifold.riemannianEDist_triangle
    _ < Manifold.riemannianEDist I x y + (r - Manifold.riemannianEDist I x y) :=
        ENNReal.add_lt_add_left hne hz
    _ = r := add_tsub_cancel_of_le hy.le

end OpenBall

/-! ### Constant rescaling of distance and ball volume -/

namespace WithMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- Multiplying a smooth metric `g` by a positive constant `c` multiplies the intrinsic Riemannian
extended distance by `√c`. -/
theorem riemannianEDist_rescale_const
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (x y : M) :
    Manifold.riemannianEDist I
        (toWithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) x)
        (toWithMetric (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) y) =
      ENNReal.ofReal (Real.sqrt c) *
        Manifold.riemannianEDist I (toWithMetric g x) (toWithMetric g y) := by
  let gc := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  let f : WithMetric g → WithMetric gc := toWithMetric gc ∘ ofWithMetric
  let fInv : WithMetric gc → WithMetric g := toWithMetric g ∘ ofWithMetric
  let K : ℝ≥0 := ⟨Real.sqrt c, Real.sqrt_nonneg c⟩
  let KInv : ℝ≥0 := ⟨Real.sqrt c⁻¹, Real.sqrt_nonneg c⁻¹⟩
  have hK0 : K ≠ 0 := NNReal.coe_ne_zero.mp (Real.sqrt_pos.mpr hc).ne'
  have hKInv0 : KInv ≠ 0 := NNReal.coe_ne_zero.mp (Real.sqrt_pos.mpr (inv_pos.mpr hc)).ne'
  have hf_diff : ContMDiff I I 1 f :=
    (contMDiff_toWithMetric (g := gc)).comp (contMDiff_ofWithMetric (g := g))
  have hfInv_diff : ContMDiff I I 1 fInv :=
    (contMDiff_toWithMetric (g := g)).comp (contMDiff_ofWithMetric (g := gc))
  let L (z : WithMetric g) : TangentSpace I z →L[ℝ] TangentSpace I (f z) :=
    ContinuousLinearMap.id ℝ E
  let LInv (z : WithMetric gc) : TangentSpace I z →L[ℝ] TangentSpace I (fInv z) :=
    ContinuousLinearMap.id ℝ E
  have hf_deriv (z : WithMetric g) : HasMFDerivAt I I f z (L z) :=
    (hasMFDerivAt_toWithMetric z.ofWithMetric).comp z (hasMFDerivAt_ofWithMetric z)
  have hfInv_deriv (z : WithMetric gc) : HasMFDerivAt I I fInv z (LInv z) :=
    (hasMFDerivAt_toWithMetric z.ofWithMetric).comp z (hasMFDerivAt_ofWithMetric z)
  have hf_norm (z : WithMetric g) (v : TangentSpace I z) :
      ‖mfderiv I I f z v‖ ≤ K * ‖v‖ := by
    have hsq : ‖mfderiv I I f z v‖ ^ 2 ≤ (K : ℝ) ^ 2 * ‖v‖ ^ 2 := by
      rw [(hf_deriv z).mfderiv]
      let vf : TangentSpace I (f z) := L z v
      have hL : L z v = vf := rfl
      rw [hL, ← real_inner_self_eq_norm_sq vf, ← real_inner_self_eq_norm_sq v]
      rw [WithMetric.inner_def (f z) vf vf, WithMetric.inner_def z v v,
        mfderiv_ofWithMetric_apply (f z) vf, mfderiv_ofWithMetric_apply z v]
      let v0 : TangentSpace I z.ofWithMetric := v
      change gc.inner z.ofWithMetric v0 v0 ≤ (K : ℝ) ^ 2 * g.inner z.ofWithMetric v0 v0
      dsimp only [gc]
      rw [g.rescale_inner (fun _ ↦ c) contMDiff_const (fun _ ↦ hc)]
      change c * g.inner z.ofWithMetric v0 v0 ≤ (Real.sqrt c) ^ 2 * g.inner z.ofWithMetric v0 v0
      rw [Real.sq_sqrt hc.le]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg K.coe_nonneg (norm_nonneg v))).mp <| by
      simpa only [mul_pow] using hsq
  have hfInv_norm (z : WithMetric gc) (v : TangentSpace I z) :
      ‖mfderiv I I fInv z v‖ ≤ KInv * ‖v‖ := by
    have hsq : ‖mfderiv I I fInv z v‖ ^ 2 ≤ (KInv : ℝ) ^ 2 * ‖v‖ ^ 2 := by
      rw [(hfInv_deriv z).mfderiv]
      let vf : TangentSpace I (fInv z) := LInv z v
      have hL : LInv z v = vf := rfl
      rw [hL, ← real_inner_self_eq_norm_sq vf, ← real_inner_self_eq_norm_sq v]
      rw [WithMetric.inner_def (fInv z) vf vf, WithMetric.inner_def z v v,
        mfderiv_ofWithMetric_apply (fInv z) vf, mfderiv_ofWithMetric_apply z v]
      let v0 : TangentSpace I z.ofWithMetric := v
      change g.inner z.ofWithMetric v0 v0 ≤ (KInv : ℝ) ^ 2 * gc.inner z.ofWithMetric v0 v0
      dsimp only [gc]
      rw [g.rescale_inner (fun _ ↦ c) contMDiff_const (fun _ ↦ hc)]
      change g.inner z.ofWithMetric v0 v0 ≤
        (Real.sqrt c⁻¹) ^ 2 * (c * g.inner z.ofWithMetric v0 v0)
      rw [Real.sq_sqrt (inv_pos.mpr hc).le, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg KInv.coe_nonneg (norm_nonneg v))).mp <| by
      simpa only [mul_pow] using hsq
  have hle1 : Manifold.riemannianEDist I (toWithMetric gc x) (toWithMetric gc y) ≤
      ENNReal.ofReal (Real.sqrt c) *
        Manifold.riemannianEDist I (toWithMetric g x) (toWithMetric g y) := by
    have h := Manifold.riemannianEDist_le_mul hf_diff hK0 hf_norm
      (toWithMetric g x) (toWithMetric g y)
    have hK_eq : (K : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt c) :=
      (ENNReal.ofReal_eq_coe_nnreal (Real.sqrt_nonneg c)).symm
    simpa only [f, Function.comp_apply, ofWithMetric_toWithMetric, hK_eq] using h
  have hle2 : Manifold.riemannianEDist I (toWithMetric g x) (toWithMetric g y) ≤
      ENNReal.ofReal (Real.sqrt c⁻¹) *
        Manifold.riemannianEDist I (toWithMetric gc x) (toWithMetric gc y) := by
    have h := Manifold.riemannianEDist_le_mul hfInv_diff hKInv0 hfInv_norm
      (toWithMetric gc x) (toWithMetric gc y)
    have hKInv_eq : (KInv : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt c⁻¹) :=
      (ENNReal.ofReal_eq_coe_nnreal (Real.sqrt_nonneg c⁻¹)).symm
    simpa only [fInv, Function.comp_apply, ofWithMetric_toWithMetric, hKInv_eq] using h
  refine le_antisymm hle1 ?_
  have hmul : ENNReal.ofReal (Real.sqrt c) *
      Manifold.riemannianEDist I (toWithMetric g x) (toWithMetric g y) ≤
      ENNReal.ofReal (Real.sqrt c) * (ENNReal.ofReal (Real.sqrt c⁻¹) *
        Manifold.riemannianEDist I (toWithMetric gc x) (toWithMetric gc y)) :=
    mul_le_mul' le_rfl hle2
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg c),
    ← Real.sqrt_mul hc.le c⁻¹, mul_inv_cancel₀ hc.ne', Real.sqrt_one,
    ENNReal.ofReal_one, one_mul] at hmul
  exact hmul

/-- Multiplying a smooth metric `g` by a positive constant `c` scales the volume of an intrinsic
ball of radius `r` around `x` by `c ^ (n / 2)` evaluated at radius `r / √c`. -/
theorem riemannianVolume_ball_rescale_const [LindelofSpace M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (x : M) (r : ℝ) :
    let gc := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
    riemannianVolume I (WithMetric gc)
        {y : WithMetric gc |
          Manifold.riemannianEDist I (toWithMetric gc x) y < ENNReal.ofReal r} =
      ENNReal.ofReal (c ^ ((Module.finrank ℝ E : ℝ) / 2)) *
        riemannianVolume I (WithMetric g)
          {z : WithMetric g |
            Manifold.riemannianEDist I (toWithMetric g x) z <
              ENNReal.ofReal (r / Real.sqrt c)} := by
  intro gc
  let Φ : WithMetric g → WithMetric gc := fun z ↦ toWithMetric gc z.ofWithMetric
  have hΦ_cont : Continuous Φ := continuous_toWithMetric.comp continuous_ofWithMetric
  have : IsContinuousRiemannianBundle E (fun y : WithMetric gc ↦ TangentSpace I y) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := E)
  have : IsContinuousRiemannianBundle E (fun y : WithMetric g ↦ TangentSpace I y) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := E)
  have hset_meas : MeasurableSet
      {y : WithMetric gc | Manifold.riemannianEDist I (toWithMetric gc x) y < ENNReal.ofReal r} :=
    (isOpen_setOf_riemannianEDist_lt (I := I) (toWithMetric gc x) (ENNReal.ofReal r)).measurableSet
  rw [riemannianVolume_rescale (I := I) (g := g) (f := fun _ ↦ c)]
  rw [Measure.map_apply hΦ_cont.measurable hset_meas]
  have hpre :
      Φ ⁻¹' {y : WithMetric gc |
          Manifold.riemannianEDist I (toWithMetric gc x) y < ENNReal.ofReal r} =
        {z : WithMetric g |
          Manifold.riemannianEDist I (toWithMetric g x) z < ENNReal.ofReal (r / Real.sqrt c)} := by
    ext z
    simp only [Φ, mem_preimage, mem_ofPred_eq]
    rw [riemannianEDist_rescale_const g hc x z.ofWithMetric, toWithMetric_ofWithMetric]
    have hsqrt_pos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
    rw [ENNReal.ofReal_div_of_pos hsqrt_pos,
      ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.ofReal_pos.mpr hsqrt_pos).ne')
        (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  rw [hpre, withDensity_apply _ (isOpen_setOf_riemannianEDist_lt (I := I)
    (toWithMetric g x) (ENNReal.ofReal (r / Real.sqrt c))).measurableSet]
  rw [setLIntegral_const]

end WithMetric

/-! ### Isometry invariance of intrinsic ball volumes -/

section Isometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [LindelofSpace M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  [LindelofSpace N] [MeasurableSpace N] [BorelSpace N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContinuousRiemannianBundle E (fun y : N ↦ TangentSpace J y)]

/-- A smooth Riemannian isometry preserves the Riemannian volume of intrinsic metric balls. -/
theorem RiemannianIsometry.riemannianVolume_setOf_riemannianEDist_lt
    (Φ : RiemannianIsometry I J M N) (x : M) (r : ℝ≥0∞) :
    riemannianVolume J N {y : N | Manifold.riemannianEDist J (Φ x) y < r} =
      riemannianVolume I M {z : M | Manifold.riemannianEDist I x z < r} := by
  have hmp := Φ.toDiffeomorph.toHomeomorph.measurePreserving_riemannianVolume
    (fun z v w ↦ Φ.inner_mfderiv z v w)
  have hmeas : MeasurableSet {y : N | Manifold.riemannianEDist J (Φ x) y < r} :=
    (isOpen_setOf_riemannianEDist_lt (I := J) (Φ x) r).measurableSet
  have hpre : Φ.toDiffeomorph.toHomeomorph ⁻¹' {y : N | Manifold.riemannianEDist J (Φ x) y < r} =
      {z : M | Manifold.riemannianEDist I x z < r} := by
    ext z
    simp only [mem_preimage, mem_ofPred_eq, Diffeomorph.coe_toHomeomorph,
      Φ.coe_toDiffeomorph, Φ.riemannianEDist_eq]
  rw [← hmp.measure_preimage hmeas.nullMeasurableSet, hpre]

end Isometry

/-! ### Uniform small-ball volume lower bound on compact manifolds -/

namespace Manifold

section SmallBall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- Helper deriving `LipschitzOnWith` from derivative bounds on a convex normal ball without
regenerating the radius. -/
private theorem lipschitzOnWith_riemannianExp_of_bounds {p : M} {R c : ℝ} (hc : 0 ≤ c)
    (hn : IsNormalDomain I M p (Metric.ball 0 R))
    (hb : ∀ v ∈ Metric.ball (0 : TangentSpace I p) R, ∀ w : TangentSpace I p,
      ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ ≤ c * ‖w‖) :
    LipschitzOnWith ⟨c, hc⟩ (riemannianExp I M p) (Metric.ball 0 R) := by
  intro a ha b hb'
  have hseg := (convex_ball (0 : TangentSpace I p) R).segment_subset ha hb'
  have hle := IsRiemannianManifold.edist_le_of_norm_mfderiv_le
    (I := I) (f := riemannianExp I M p)
    (fun z hz ↦ (contMDiffAt_riemannianExp (hn.subset_expDomain (hseg hz))).of_le (by simp))
    (fun z hz ↦ hb z (hseg hz) (b - a))
  let cNN : ℝ≥0 := ⟨c, hc⟩
  have hcoe : (cNN : ℝ≥0∞) = ENNReal.ofReal c :=
    (ENNReal.ofReal_eq_coe_nnreal hc).symm
  change edist (riemannianExp I M p a) (riemannianExp I M p b) ≤ (cNN : ℝ≥0∞) * edist a b
  rw [hcoe]
  simpa [edist_dist, dist_eq_norm, norm_sub_rev, ENNReal.ofReal_mul hc] using hle

private theorem hasMFDerivAt_continuousLinearMap {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : U →L[ℝ] V) (u : U) :
    HasMFDerivAt 𝓘(ℝ, U) 𝓘(ℝ, V) f u f :=
  f.hasFDerivAt.hasMFDerivAt

section

variable [Nontrivial E] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- **Uniform small-ball volume lower bound** on a compact boundaryless positive-dimensional
smooth Riemannian manifold: for every `θ < 1`, there exists `r₀ > 0` such that every
Riemannian ball of radius `0 < r ≤ r₀` has volume at least `θ * ωₙ * rⁿ`. -/
theorem exists_pos_forall_riemannianVolume_ball_ge {θ : ℝ} (hθ : θ < 1) :
    ∃ r₀ > 0, ∀ (q : M) (r : ℝ), 0 < r → r ≤ r₀ →
      ENNReal.ofReal (θ * euclideanUnitBallVolume (Module.finrank ℝ E) *
          r ^ Module.finrank ℝ E) ≤
        riemannianVolume I M (Metric.eball q (ENNReal.ofReal r)) := by
  by_cases hM : IsEmpty M
  · exact ⟨1, one_pos, fun q ↦ (hM.false q).elim⟩
  rw [not_isEmpty_iff] at hM
  rcases le_or_gt θ 0 with hθ_nonpos | hθ_pos
  · refine ⟨1, one_pos, fun q r hr _ ↦ ?_⟩
    have hnonpos : θ * euclideanUnitBallVolume (Module.finrank ℝ E) * r ^ Module.finrank ℝ E ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hθ_nonpos
          (euclideanUnitBallVolume_pos (Module.finrank ℝ E)).le)
        (pow_nonneg hr.le _)
    rw [ENNReal.ofReal_of_nonpos hnonpos]
    exact bot_le
  let n : ℕ := Module.finrank ℝ E
  have hn_pos : 0 < n := Module.finrank_pos
  let c : ℝ := θ⁻¹ ^ (1 / (2 * (n : ℝ)))
  have hc_gt_one : 1 < c := by
    refine Real.one_lt_rpow ?_ ?_
    · exact one_lt_inv_iff₀.mpr ⟨hθ_pos, hθ⟩
    · positivity
  have hc_pos : 0 < c := zero_lt_one.trans hc_gt_one
  have hc_pow : c ^ (2 * n) = θ⁻¹ := by
    dsimp only [c]
    rw [← Real.rpow_natCast (θ⁻¹ ^ (1 / (2 * (n : ℝ)))) (2 * n),
      ← Real.rpow_mul (inv_nonneg.mpr hθ_pos.le)]
    have hmul : (1 / (2 * (n : ℝ))) * ((2 * n : ℕ) : ℝ) = 1 := by
      push_cast
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn_pos.ne'
      field_simp [hn0]
    rw [hmul, Real.rpow_one]
  -- Around each `p : M`, obtain a normal ball `B(0, R p)` with `c`-bi-Lipschitz differential.
  have hnb : ∀ p : M, ∃ R > 0, IsNormalDomain I M p (Metric.ball 0 R) ∧
      (∀ v ∈ Metric.ball (0 : TangentSpace I p) R, ∀ w : TangentSpace I p,
        c⁻¹ * ‖w‖ ≤ ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ ∧
        ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ ≤ c * ‖w‖) ∧
      (∀ q ∈ riemannianExp I M p '' Metric.ball 0 R, ∀ w : TangentSpace I q,
        c⁻¹ * ‖w‖ ≤ ‖mfderiv I 𝓘(ℝ, TangentSpace I p)
          (riemannianLog I M p (Metric.ball 0 R)) q w‖ ∧
        ‖mfderiv I 𝓘(ℝ, TangentSpace I p)
          (riemannianLog I M p (Metric.ball 0 R)) q w‖ ≤ c * ‖w‖) :=
    fun p ↦ exists_isNormalDomain_ball_norm_mfderiv_bounds (I := I) p hc_gt_one
  choose R hR_pos hnorm hExp hLog using hnb
  let U : M → Set M := fun p ↦ riemannianExp I M p '' Metric.ball 0 (R p / 2)
  have hU_open (p : M) : IsOpen (U p) :=
    ((hnorm p).ball (Metric.ball_subset_ball (half_lt_self (hR_pos p)).le)
      (half_pos (hR_pos p))).isOpen_image
  have hp_mem_U (p : M) : p ∈ U p :=
    ⟨0, Metric.mem_ball_self (half_pos (hR_pos p)), riemannianExp_zero p⟩
  have hcov : (univ : Set M) ⊆ ⋃ p : M, U p := fun q _ ↦ mem_iUnion.mpr ⟨q, hp_mem_U q⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU_open hcov
  by_cases hs_ne : s.Nonempty
  · let r₀ : ℝ := s.inf' hs_ne fun p ↦ R p / (2 * c)
    have hr₀_pos : 0 < r₀ := by
      refine (Finset.lt_inf'_iff hs_ne).mpr fun p _ ↦ ?_
      exact div_pos (hR_pos p) (mul_pos two_pos hc_pos)
    refine ⟨r₀, hr₀_pos, fun q r hr hrr₀ ↦ ?_⟩
    have hq_mem : q ∈ ⋃ p ∈ s, U p := hs (mem_univ q)
    simp only [mem_iUnion, exists_prop] at hq_mem
    obtain ⟨p, hp_s, v₀, hv₀_mem, rfl⟩ := hq_mem
    have hr_le_Rp : r ≤ R p / (2 * c) :=
      hrr₀.trans (Finset.inf'_le (fun p ↦ R p / (2 * c)) hp_s)
    have hv₀_norm : ‖v₀‖ < R p / 2 := by simpa only [mem_ball, dist_zero_right] using hv₀_mem
    have hv₀_ball : v₀ ∈ Metric.ball (0 : TangentSpace I p) (R p) :=
      Metric.ball_subset_ball (half_lt_self (hR_pos p)).le hv₀_mem
    -- Work in orthonormal coordinates `A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace I p`.
    let b := stdOrthonormalBasis ℝ (TangentSpace I p)
    let bE : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
      EuclideanSpace.basisFun (Fin n) ℝ
    have hdim_T : Module.finrank ℝ (TangentSpace I p) = n := rfl
    let A_iso : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] TangentSpace I p :=
      (b.reindex (finCongr hdim_T)).repr.symm
    let A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace I p := A_iso.toContinuousLinearEquiv
    let u₀ : EuclideanSpace ℝ (Fin n) := A.symm v₀
    let S : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball u₀ (r / c)
    have hmap : MapsTo A S (Metric.ball 0 (R p)) := by
      intro u hu
      have hdist : ‖A u - v₀‖ < r / c := by
        rw [mem_ball, dist_eq_norm] at hu
        change ‖u - A.symm v₀‖ < r / c at hu
        rw [← A.apply_symm_apply v₀, ← map_sub]
        change ‖A_iso (u - A.symm v₀)‖ < r / c
        rw [A_iso.norm_map]
        exact hu
      rw [mem_ball, dist_zero_right]
      have hrc : r / c ≤ R p / 2 := by
        calc
          r / c ≤ (R p / (2 * c)) / c := div_le_div_of_nonneg_right hr_le_Rp hc_pos.le
          _ = R p / (2 * (c * c)) := by ring
          _ ≤ R p / 2 := by
              refine div_le_div_of_nonneg_left (hR_pos p).le (by positivity) ?_
              have : 1 ≤ c * c := one_le_mul_of_one_le_of_one_le hc_gt_one.le hc_gt_one.le
              linarith
      calc
        ‖A u‖ = ‖(A u - v₀) + v₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖A u - v₀‖ + ‖v₀‖ := norm_add_le _ _
        _ < r / c + R p / 2 := add_lt_add hdist hv₀_norm
        _ ≤ R p / 2 + R p / 2 := by linarith
        _ = R p := add_halves (R p)
    obtain ⟨Φ, hΦ_src, hΦ_coe⟩ :=
      (hnorm p).exists_partialDiffeomorph_riemannianExp_comp A isOpen_ball hmap
    -- Show `Φ '' S ⊆ eball (exp_p v₀) r` via Lipschitz bound on `B(0, R p)`.
    let cNN : ℝ≥0 := ⟨c, hc_pos.le⟩
    have hLip : LipschitzOnWith cNN (riemannianExp I M p) (Metric.ball 0 (R p)) :=
      lipschitzOnWith_riemannianExp_of_bounds hc_pos.le (hnorm p) fun v hv w ↦ (hExp p v hv w).2
    have hsub_eball : Φ '' S ⊆ Metric.eball (riemannianExp I M p v₀) (ENNReal.ofReal r) := by
      rintro _ ⟨u, hu, rfl⟩
      rw [hΦ_coe, Function.comp_apply, Metric.mem_eball, edist_comm]
      have hAu_ball : A u ∈ Metric.ball (0 : TangentSpace I p) (R p) := hmap hu
      have hcoe : (cNN : ℝ≥0∞) = ENNReal.ofReal c :=
        (ENNReal.ofReal_eq_coe_nnreal hc_pos.le).symm
      have hed : edist (riemannianExp I M p v₀) (riemannianExp I M p (A u)) ≤
          ENNReal.ofReal c * edist v₀ (A u) := by
        rw [← hcoe]
        exact hLip hv₀_ball hAu_ball
      have hdist_lt : dist v₀ (A u) < r / c := by
        rw [mem_ball, dist_eq_norm] at hu
        change ‖u - A.symm v₀‖ < r / c at hu
        rw [dist_eq_norm, norm_sub_rev, ← A.apply_symm_apply v₀, ← map_sub]
        change ‖A_iso (u - A.symm v₀)‖ < r / c
        rw [A_iso.norm_map]
        exact hu
      have hed_lt : edist v₀ (A u) < ENNReal.ofReal (r / c) := by
        rw [edist_dist]
        exact (ENNReal.ofReal_lt_ofReal_iff (div_pos hr hc_pos)).2 hdist_lt
      calc
        edist (riemannianExp I M p v₀) (riemannianExp I M p (A u))
            ≤ ENNReal.ofReal c * edist v₀ (A u) := hed
        _ < ENNReal.ofReal c * ENNReal.ofReal (r / c) := by
            simpa only [mul_comm] using
              ENNReal.mul_lt_mul_left (ENNReal.ofReal_pos.mpr hc_pos).ne'
                ENNReal.ofReal_ne_top hed_lt
        _ = ENNReal.ofReal r := by
            rw [← ENNReal.ofReal_mul hc_pos.le, mul_div_cancel₀ _ hc_pos.ne']
    have hΦ_tgt_sub : Φ.target ⊆ Metric.eball (riemannianExp I M p v₀) (ENNReal.ofReal r) := by
      rw [← Φ.image_source_eq_target, hΦ_src]
      exact hsub_eball
    -- Lower bound the Riemannian Jacobian of `Φ` on `S` using Hadamard's inequality.
    have hJac_ge : ∀ u ∈ S, c⁻¹ ^ n ≤ riemannianJacobian (I := I) bE.toBasis Φ u := by
      intro u hu
      have hAu : A u ∈ Metric.ball (0 : TangentSpace I p) (R p) := hmap hu
      rw [riemannianJacobian_eq_normDet bE Φ u]
      have hΦu_eq : Φ u = riemannianExp I M p (A u) := by
        rw [hΦ_coe]
        rfl
      have hΦ_mem : Φ u ∈ riemannianExp I M p '' Metric.ball 0 (R p) :=
        hΦu_eq ▸ mem_image_of_mem _ hAu
      have hΦ_diff : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I Φ u :=
        ((Φ.contMDiffOn u (hΦ_src ▸ hu)).contMDiffAt
          (Φ.open_source.mem_nhds (hΦ_src ▸ hu))).mdifferentiableAt (by simp)
      have hlog_diff :
          MDifferentiableAt I 𝓘(ℝ, TangentSpace I p)
            (riemannianLog I M p (Metric.ball 0 (R p))) (Φ u) :=
        (hnorm p).mdifferentiableAt_riemannianLog hΦ_mem
      have heq_log_Φ :
          riemannianLog I M p (Metric.ball 0 (R p)) ∘ Φ =ᶠ[𝓝 u]
            (A : EuclideanSpace ℝ (Fin n) → TangentSpace I p) := by
        filter_upwards [isOpen_ball.mem_nhds hu] with y hy
        change riemannianLog I M p (Metric.ball 0 (R p)) (Φ.toPartialEquiv y) = A y
        rw [hΦ_coe, Function.comp_apply, (hnorm p).riemannianLog_riemannianExp (hmap hy)]
      let Ψ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] TangentSpace I (Φ u) :=
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I Φ u).toLinearMap
      let B : TangentSpace I (Φ u) →ₗ[ℝ] TangentSpace I p :=
        (mfderiv I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p (Metric.ball 0 (R p)))
          (Φ u)).toLinearMap
      have hcomp_mf :
          (mfderiv I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p (Metric.ball 0 (R p))) (Φ u)).comp
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I Φ u) =
          (A : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace I p) :=
        hasMFDerivAt_unique
          (hlog_diff.hasMFDerivAt.comp u hΦ_diff.hasMFDerivAt)
          ((hasMFDerivAt_continuousLinearMap A.toContinuousLinearMap u).congr_of_eventuallyEq_abuse
            heq_log_Φ)
      have hBΨ : B ∘ₗ Ψ = (A : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace I p).toLinearMap :=
        congrArg ContinuousLinearMap.toLinearMap hcomp_mf
      have hA_iso : (A : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace I p).toLinearMap.normDet = 1 :=
        A_iso.toLinearIsometry.normDet_eq_one
      have hprod : B.normDet * Ψ.normDet = 1 := by
        have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
            Module.finrank ℝ (TangentSpace I (Φ u)) := by
          rw [finrank_euclideanSpace_fin]
          rfl
        have hcomp_det := LinearMap.normDet_comp_of_finrank_eq Ψ B hfr
        rw [hBΨ, hA_iso] at hcomp_det
        exact hcomp_det.symm
      have hB_le : B.normDet ≤ c ^ n := by
        let b' := stdOrthonormalBasis ℝ (TangentSpace I (Φ u))
        have hB_sq : B.normDet ^ 2 ≤ (c ^ n) ^ 2 := by
          have hgram := B.normDet_sq_eq_det_gram b'
          rw [RCLike.ofReal_real_eq_id, id_eq] at hgram
          rw [hgram]
          have hhad := Matrix.re_det_gram_le_prod_norm_sq (𝕜 := ℝ) (B ∘ b')
          have hnorm_b' (i) : ‖B (b' i)‖ ≤ c := by
            have hle := (hLog p (Φ u) hΦ_mem (b' i)).2
            rwa [b'.orthonormal.norm_eq_one, mul_one] at hle
          calc
            (Matrix.gram ℝ (B ∘ b')).det
                ≤ ∏ i, ‖B (b' i)‖ ^ 2 := by simpa using hhad
            _ ≤ ∏ _i : Fin (Module.finrank ℝ (TangentSpace I (Φ u))),
                  c ^ 2 := by
                  gcongr with i
                  exact hnorm_b' i
            _ = (c ^ n) ^ 2 := by
                have hfin : Module.finrank ℝ (TangentSpace I (Φ u)) = n := rfl
                simp only [Finset.prod_const, Finset.card_fin, hfin]
                ring
        exact (sq_le_sq₀ B.normDet_nonneg (pow_nonneg hc_pos.le n)).mp hB_sq
      have hB_pos : 0 < B.normDet := by
        by_contra h0
        have hle0 : B.normDet = 0 := le_antisymm (not_lt.mp h0) B.normDet_nonneg
        rw [hle0, zero_mul] at hprod
        exact zero_ne_one hprod
      change c⁻¹ ^ n ≤ Ψ.normDet
      have hΨ_eq : Ψ.normDet = (B.normDet)⁻¹ := eq_inv_of_mul_eq_one_right hprod
      rw [hΨ_eq, inv_pow]
      exact inv_anti₀ hB_pos hB_le
    -- Apply change of variables on `Φ.target` with `φ = 1`.
    have h1inf : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by simp
    have hcov_vol := (Φ.ofLE h1inf).setLIntegral_riemannianVolume_eq
      bE.toBasis (by simp [n]) (φ := fun _ ↦ 1) measurable_const
    have hcov_vol' : riemannianVolume I M Φ.target =
        ∫⁻ u in S, ENNReal.ofReal (riemannianJacobian (I := I) bE.toBasis Φ u) ∂volume := by
      have htgt : (Φ.ofLE h1inf).target = Φ.target :=
        congrArg PartialEquiv.target (Φ.ofLE_toPartialEquiv h1inf)
      have hsrc : (Φ.ofLE h1inf).source = Φ.source :=
        congrArg PartialEquiv.source (Φ.ofLE_toPartialEquiv h1inf)
      simpa only [setLIntegral_one, mul_one, htgt, hsrc, PartialDiffeomorph.ofLE_toPartialEquiv,
        hΦ_src, bE.addHaar_eq_volume] using hcov_vol
    have hfin_ne : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
    have hvol_S : volume S =
        ENNReal.ofReal (r / c) ^ n * ENNReal.ofReal (euclideanUnitBallVolume n) := by
      simpa only [Fintype.card_fin, euclideanUnitBallVolume] using
        EuclideanSpace.volume_ball (Fin n) u₀ (r / c)
    calc
      ENNReal.ofReal (θ * euclideanUnitBallVolume n * r ^ n)
          = ENNReal.ofReal (c⁻¹ ^ n) *
              (ENNReal.ofReal (r / c) ^ n * ENNReal.ofReal (euclideanUnitBallVolume n)) := by
            rw [← ENNReal.ofReal_pow (div_pos hr hc_pos).le,
              ← ENNReal.ofReal_mul (pow_nonneg (div_pos hr hc_pos).le n),
              ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hc_pos.le) n)]
            congr 1
            have hinv : (c ^ (2 * n))⁻¹ = θ := by rw [hc_pow, inv_inv]
            calc
              θ * euclideanUnitBallVolume n * r ^ n
                  = (c ^ (2 * n))⁻¹ * euclideanUnitBallVolume n * r ^ n := by rw [hinv]
              _ = c⁻¹ ^ n * ((r / c) ^ n * euclideanUnitBallVolume n) := by
                  rw [div_pow, inv_pow, show 2 * n = n + n by ring, pow_add]
                  field_simp
      _ = ∫⁻ _ in S, ENNReal.ofReal (c⁻¹ ^ n) ∂volume := by
          rw [setLIntegral_const, hvol_S]
      _ ≤ ∫⁻ u in S, ENNReal.ofReal (riemannianJacobian (I := I) bE.toBasis Φ u) ∂volume :=
          setLIntegral_mono' measurableSet_ball fun u hu ↦ ENNReal.ofReal_le_ofReal (hJac_ge u hu)
      _ = riemannianVolume I M Φ.target := hcov_vol'.symm
      _ ≤ riemannianVolume I M (Metric.eball (riemannianExp I M p v₀) (ENNReal.ofReal r)) :=
          measure_mono hΦ_tgt_sub
  · exfalso
    have hmem : (Classical.arbitrary M) ∈ (⋃ p ∈ s, U p) := hs (mem_univ _)
    simp only [mem_iUnion, exists_prop] at hmem
    obtain ⟨p, hp, _⟩ := hmem
    exact hs_ne ⟨p, hp⟩

end

/-- `WithMetric` variant of the uniform small-ball volume lower bound on a closed smooth manifold
carrying a `C^∞` Riemannian metric `g`. -/
theorem exists_pos_forall_riemannianVolume_ball_ge_of_metric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ChartedSpace H M] [IsManifold I ∞ M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {θ : ℝ} (hθ : θ < 1) :
    ∃ r₀ > 0, ∀ (q : M) (r : ℝ), 0 < r → r ≤ r₀ →
      ENNReal.ofReal (θ * euclideanUnitBallVolume (Module.finrank ℝ E) *
          r ^ Module.finrank ℝ E) ≤
        riemannianVolume I (TauCeti.WithMetric g)
          {y : TauCeti.WithMetric g |
            Manifold.riemannianEDist I (TauCeti.WithMetric.toWithMetric g q) y <
              ENNReal.ofReal r} := by
  have : CompactSpace (TauCeti.WithMetric g) :=
    (TauCeti.WithMetric.homeomorph g).symm.compactSpace
  have : T2Space (TauCeti.WithMetric g) :=
    (TauCeti.WithMetric.homeomorph g).symm.t2Space
  let : EMetricSpace (TauCeti.WithMetric g) :=
    EMetricSpace.ofRiemannianMetric I (TauCeti.WithMetric g)
  have : IsRiemannianManifold I (TauCeti.WithMetric g) := ⟨fun _ _ ↦ rfl⟩
  have : IsContinuousRiemannianBundle E (fun x : TauCeti.WithMetric g ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := E)
  obtain ⟨r₀, hr₀, hball⟩ := exists_pos_forall_riemannianVolume_ball_ge (I := I)
    (M := TauCeti.WithMetric g) hθ
  refine ⟨r₀, hr₀, fun q r hr hrr₀ ↦ ?_⟩
  have heq : Metric.eball (TauCeti.WithMetric.toWithMetric g q) (ENNReal.ofReal r) =
      {y : TauCeti.WithMetric g |
        Manifold.riemannianEDist I (TauCeti.WithMetric.toWithMetric g q) y < ENNReal.ofReal r} := by
    ext y
    rw [Metric.mem_eball, edist_comm, mem_ofPred_eq, IsRiemannianManifold.out (I := I)]
  simpa only [← heq] using hball (TauCeti.WithMetric.toWithMetric g q) r hr hrr₀

end SmallBall

end Manifold

end TauCeti
