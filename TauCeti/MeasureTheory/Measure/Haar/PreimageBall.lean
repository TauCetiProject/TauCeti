/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.MeasureTheory.Integral.Bochner.Set
public import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.Normed.Group.RelativeApproximation
import TauCeti.Topology.Order.Squeeze

/-!
# Volumes of small preimages of balls under a map with injective derivative

Let `E` be an `n`-dimensional real normed space with a basis `b`, let `F` be a real inner product
space and let `A : E → F` be an injective linear map. The Haar measure `λ_b` of
the ellipsoid `A⁻¹(B_1(0))`, times the Gram determinant `√ det ⟪A (b i), A (b j)⟫`, is the volume
`ωₙ` of the unit ball of `ℝⁿ`: both are the volume of the unit ball of the range of `A`, measured
through the basis `A ∘ b` of the range.

Suppose `g : E → F` has injective derivative `A` at `z₀`, and on `B_δ(z₀)` for `δ > 0` its error
satisfies
`‖g z - g z₀ - A (z - z₀)‖ ≤ c ‖A (z - z₀)‖` for some `c < 1`. For small `r > 0`, the localized
set `S_r = B_δ(z₀) ∩ g⁻¹(B_r(g z₀))` lies between the ellipsoids
`z₀ + A⁻¹(B_{r/(1+ε)})` and `z₀ + A⁻¹(B_{r/(1-ε)})`. Assume each `S_r` is measurable, and the
density `J` is continuous at `z₀` and almost everywhere strongly measurable on `B_δ(z₀)`, with
`J z₀ = √ det ⟪A (b i), A (b j)⟫`. Then `∫_{S_r} J dλ_b / rⁿ → ωₙ` as `r → 0⁺`.
Read in a chart, this says that the part near a point of an immersed submanifold inside a small
ambient ball of radius `r` has area `≈ ωₙ rⁿ`, as in the small-ball limit of the monotonicity
formula for minimal submanifolds.

## Main results

* `Module.Basis.ofReal_sqrt_det_gram_mul_addHaar_preimage_ball`:
  `√ det Gram(A b) · λ_b(A⁻¹ B_1) = ωₙ`.
* `Module.Basis.addHaar_preimage_ball_sub`: the translated ellipsoid of radius `s > 0` has measure
  `sⁿ λ_b(A⁻¹ B_1)`.
* `Module.Basis.tendsto_setIntegral_preimage_ball_div_pow`: `∫_{S_r} J dλ_b / rⁿ → ωₙ` as `r → 0⁺`.

The relative linearization estimate for every `ε > 0` follows from Mathlib's
`HasFDerivAt.isEquivalent_sub` and `Asymptotics.IsEquivalent.isLittleO`, since an injective linear
map on a finite-dimensional space is antilipschitz (`LinearMap.injective_iff_antilipschitz`).

## References

* T. H. Colding and W. P. Minicozzi II, *A Course in Minimal Surfaces*, Graduate Studies in
  Mathematics 121, American Mathematical Society (2011), Chapter 1, §3.
-/

public section

open Filter Function MeasureTheory Metric Module Set
open scoped ENNReal NNReal Pointwise Topology

namespace Module.Basis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The ellipsoid of an injective linear map.** For an injective linear map `A : E → F` and a
basis `b` of `E`, `√ det ⟪A (b i), A (b j)⟫ · λ_b(A⁻¹(B_1(0))) = ωₙ`. -/
theorem ofReal_sqrt_det_gram_mul_addHaar_preimage_ball (b : Basis ι ℝ E) {A : E →L[ℝ] F}
    (hA : Injective A) :
    ENNReal.ofReal √(Matrix.gram ℝ fun i ↦ A (b i)).det * b.addHaar (A ⁻¹' ball 0 1) =
      volume (ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) := by
  let V := LinearMap.range (A : E →ₗ[ℝ] F)
  let : MeasurableSpace V := borel V
  have : BorelSpace V := ⟨rfl⟩
  let e : E ≃L[ℝ] V := (LinearEquiv.ofInjective (A : E →ₗ[ℝ] F) hA).toContinuousLinearEquiv
  have he (x : E) : (e x : F) = A x := by
    simp [e, LinearEquiv.ofInjective_apply]
  have hpre : A ⁻¹' ball (0 : F) 1 = e ⁻¹' ball (0 : V) 1 := by
    ext x
    simp [← Submodule.norm_coe, he]
  have hgram : Matrix.gram ℝ (b.map e.toLinearEquiv) = Matrix.gram ℝ fun i ↦ A (b i) := by
    ext i j
    simp [Matrix.gram_apply, Submodule.coe_inner, he]
  let f : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
    ((stdOrthonormalBasis ℝ V).reindex (finCongr e.toLinearEquiv.finrank_eq.symm)).repr
  have hball : volume (ball (0 : V) 1) =
      volume (ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) := by
    rw [← f.measurePreserving.measure_preimage measurableSet_ball.nullMeasurableSet,
      f.preimage_ball, map_zero]
  have hV := congrArg (fun μ : Measure V ↦ μ (ball 0 1))
    (b.map e.toLinearEquiv).volume_eq_smul_addHaar
  simp only [smul_apply, smul_eq_mul] at hV
  rw [hpre, ← Measure.map_apply e.continuous.measurable measurableSet_ball, b.map_addHaar e,
    ← hgram, ← hV, hball]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Near `z₀`, a map differentiable at `z₀` is within `ε ‖A (z - z₀)‖` of its linearization, and
a function continuous at `z₀` is within `ε` of its value there. -/
private theorem exists_forall_mem_ball_le {g : E → F} {z₀ : E} {A : E →L[ℝ] F}
    (hg : HasFDerivAt g A z₀) {K : ℝ≥0} (hK : AntilipschitzWith K A) {J : E → ℝ}
    (hJ : ContinuousAt J z₀) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ δε, 0 < δε ∧ δε ≤ δ ∧ ∀ z ∈ ball z₀ δε,
      ‖g z - g z₀ - A (z - z₀)‖ ≤ ε * ‖A (z - z₀)‖ ∧ |J z - J z₀| ≤ ε := by
  have h1 : ∀ᶠ z in 𝓝 z₀, ‖g z - g z₀ - A (z - z₀)‖ ≤ ε * ‖A (z - z₀)‖ :=
    (hg.isEquivalent_sub (hK.isInducing A.continuous)).isLittleO.def hε
  have h2 : ∀ᶠ z in 𝓝 z₀, |J z - J z₀| ≤ ε :=
    (hJ.eventually (Metric.closedBall_mem_nhds (J z₀) hε)).mono fun z hz ↦ by
      simpa [Real.dist_eq] using hz
  obtain ⟨δ', hδ', hδ'm⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  refine ⟨min δ δ', lt_min hδ hδ', min_le_left _ _, fun z hz ↦ ?_⟩
  obtain ⟨hz1, hz2⟩ := hδ'm z (ball_subset_ball (min_le_right _ _) hz)
  exact ⟨hz1, hz2⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For small `r`, the set `S_r = B_δ(z₀) ∩ g⁻¹(B_r(g z₀))` lies in `B_{δε}(z₀)` and between the
ellipsoids `z₀ + A⁻¹(B_{r/(1+ε)})` and `z₀ + A⁻¹(B_{r/(1-ε)})`. -/
private theorem preimage_ball_subset_and_subset {g : E → F} {z₀ : E} {A : E →L[ℝ] F}
    {K δ δε ε r c : ℝ} (hK : 0 ≤ K) (hc : c < 1) (hKA : ∀ w, ‖w‖ ≤ K * ‖A w‖)
    (hgδ : ∀ z ∈ ball z₀ δ, ‖g z - g z₀ - A (z - z₀)‖ ≤ c * ‖A (z - z₀)‖)
    (hest : ∀ z ∈ ball z₀ δε, ‖g z - g z₀ - A (z - z₀)‖ ≤ ε * ‖A (z - z₀)‖)
    (hδε : δε ≤ δ) (hε : 0 < ε) (hε1 : ε < 1) (hr : 0 < r) (hrδ : (1 + (1 - c)⁻¹) * K * r < δε) :
    (fun z ↦ A (z - z₀)) ⁻¹' ball 0 (r / (1 + ε)) ⊆ ball z₀ δ ∩ g ⁻¹' ball (g z₀) r ∧
      ball z₀ δ ∩ g ⁻¹' ball (g z₀) r ⊆
        ball z₀ δε ∩ (fun z ↦ A (z - z₀)) ⁻¹' ball 0 (r / (1 - ε)) := by
  constructor
  · intro z hz
    rw [mem_preimage, mem_ball_zero_iff, lt_div_iff₀ (by linarith)] at hz
    have hzδε : z ∈ ball z₀ δε := by
      rw [mem_ball, dist_eq_norm]
      calc ‖z - z₀‖ ≤ K * ‖A (z - z₀)‖ := hKA _
        _ ≤ K * r := by gcongr; nlinarith [norm_nonneg (A (z - z₀))]
        _ < δε := by
          have := mul_nonneg (inv_nonneg.2 (sub_pos.2 hc).le) (mul_nonneg hK hr.le)
          nlinarith
    refine ⟨ball_subset_ball hδε hzδε, ?_⟩
    rw [mem_preimage, mem_ball, dist_eq_norm]
    nlinarith [(TauCeti.norm_bounds_of_norm_sub_le (hest z hzδε)).2]
  · rintro z ⟨hzδ, hzr⟩
    rw [mem_preimage, mem_ball, dist_eq_norm] at hzr
    have hA2 := (TauCeti.norm_bounds_of_norm_sub_le (hgδ z hzδ)).1
    have hzδε : z ∈ ball z₀ δε := by
      rw [mem_ball, dist_eq_norm]
      calc ‖z - z₀‖ ≤ K * ‖A (z - z₀)‖ := hKA _
        _ < δε := by
          have hAc : ‖A (z - z₀)‖ < r / (1 - c) :=
            (lt_div_iff₀ (sub_pos.2 hc)).2 (by nlinarith [hA2.trans_lt hzr])
          have hbound := mul_le_mul_of_nonneg_left hAc.le hK
          rw [← mul_div_assoc] at hbound
          have : 0 < 1 - c := sub_pos.2 hc
          have hδr : K * r / (1 - c) < δε := by
            rw [div_eq_mul_inv]
            nlinarith [mul_nonneg hK hr.le]
          exact hbound.trans_lt hδr
    refine ⟨hzδε, ?_⟩
    rw [mem_preimage, mem_ball_zero_iff, lt_div_iff₀ (by linarith)]
    nlinarith [(TauCeti.norm_bounds_of_norm_sub_le (hest z hzδε)).1]

omit [DecidableEq ι] in
/-- The ellipsoid `z₀ + A⁻¹(B_s)` has measure `sⁿ λ_b(A⁻¹(B_1))`. -/
theorem addHaar_preimage_ball_sub {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (b : Basis ι ℝ E) (A : E →L[ℝ] G) (z₀ : E) {s : ℝ}
    (hs : 0 < s) :
    b.addHaar ((fun z ↦ A (z - z₀)) ⁻¹' ball 0 s) =
      ENNReal.ofReal (s ^ finrank ℝ E) * b.addHaar (A ⁻¹' ball 0 1) := by
  have hset : (fun z ↦ A (z - z₀)) ⁻¹' ball (0 : G) s =
      (fun z ↦ z + -z₀) ⁻¹' (s • (A ⁻¹' ball (0 : G) 1)) := by
    ext z
    simp only [mem_preimage, mem_ball_zero_iff, mem_smul_set_iff_inv_smul_mem₀ hs.ne',
      map_smul, norm_smul, sub_eq_add_neg, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
    rw [inv_mul_lt_iff₀ hs, mul_one]
  rw [hset, measure_preimage_add_right, Measure.addHaar_smul, abs_of_nonneg (by positivity)]

omit [DecidableEq ι] in
/-- The two-sided estimate behind `tendsto_setIntegral_preimage_ball_div_pow`,
at a fixed small `ε`. -/
private theorem eventually_le_setIntegral_div_pow_le (b : Basis ι ℝ E) {g : E → F} {z₀ : E}
    {A : E →L[ℝ] F} (hg : HasFDerivAt g A z₀) (hA : Injective A) {J : E → ℝ} {δ : ℝ}
    (hJ : ContinuousAt J z₀) (hJm : AEStronglyMeasurable J (b.addHaar.restrict (ball z₀ δ)))
    (hδ : 0 < δ) (hS : ∀ r > 0, MeasurableSet (ball z₀ δ ∩ g ⁻¹' ball (g z₀) r))
    {c : ℝ} (hc : c < 1)
    (hgδ : ∀ z ∈ ball z₀ δ, ‖g z - g z₀ - A (z - z₀)‖ ≤ c * ‖A (z - z₀)‖) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hεJ : ε < J z₀) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (J z₀ - ε) * ((1 + ε)⁻¹) ^ finrank ℝ E * b.addHaar.real (A ⁻¹' ball 0 1) ≤
          (∫ z in ball z₀ δ ∩ g ⁻¹' ball (g z₀) r, J z ∂b.addHaar) / r ^ finrank ℝ E ∧
        (∫ z in ball z₀ δ ∩ g ⁻¹' ball (g z₀) r, J z ∂b.addHaar) / r ^ finrank ℝ E ≤
          (J z₀ + ε) * ((1 - ε)⁻¹) ^ finrank ℝ E * b.addHaar.real (A ⁻¹' ball 0 1) := by
  obtain ⟨K, hK0, hK⟩ := (LinearMap.injective_iff_antilipschitz (A : E →ₗ[ℝ] F)).1 hA
  have hKA (w : E) : ‖w‖ ≤ K * ‖A w‖ := by simpa using hK.le_mul_dist w 0
  have hK0' : (0 : ℝ) < K := NNReal.coe_pos.2 hK0
  obtain ⟨δε, hδε, hδεδ, hest⟩ := exists_forall_mem_ball_le hg hK hJ hδ hε
  have : 0 < 1 - c := sub_pos.2 hc
  have hrad : 0 < δε / ((1 + (1 - c)⁻¹) * K) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hrad] with r hr
  obtain ⟨hsub, hsup⟩ := preimage_ball_subset_and_subset hK0'.le hc hKA hgδ
    (fun z hz ↦ (hest z hz).1) hδεδ hε hε1 hr.1 (by
      have hrδε := (lt_div_iff₀ (by positivity : 0 < (1 + (1 - c)⁻¹) * (K : ℝ))).1 hr.2
      simpa only [mul_comm r] using hrδε)
  set S := ball z₀ δ ∩ g ⁻¹' ball (g z₀) r
  set μ := b.addHaar
  have hP (s : ℝ) (hs : 0 < s) : μ.real ((fun z ↦ A (z - z₀)) ⁻¹' ball 0 s) =
      s ^ finrank ℝ E * μ.real (A ⁻¹' ball 0 1) := by
    rw [measureReal_def, addHaar_preimage_ball_sub b A z₀ hs, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), measureReal_def]
  have hPfin (s : ℝ) (hs : 0 < s) : μ ((fun z ↦ A (z - z₀)) ⁻¹' ball 0 s) < ⊤ := by
    rw [addHaar_preimage_ball_sub b A z₀ hs]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hK.isBounded_preimage isBounded_ball).measure_lt_top
  have hs₁ : 0 < r / (1 - ε) := div_pos hr.1 (by linarith)
  have hSfin : μ S < ⊤ :=
    (measure_mono (hsup.trans inter_subset_right)).trans_lt (hPfin _ hs₁)
  have hd := abs_le.1 (by
    simpa only [Real.norm_eq_abs, smul_eq_mul, mul_comm] using
      MeasureTheory.norm_setIntegral_sub_smul_measureReal_le (hS r hr.1) hSfin
        (hJm.mono_set inter_subset_left) (c := J z₀)
        (fun z hz ↦ (Real.norm_eq_abs _).trans_le (hest z (hsup hz).1).2))
  have hμ1 := hP _ (div_pos hr.1 (by linarith : (0 : ℝ) < 1 + ε)) ▸ measureReal_mono hsub hSfin.ne
  have hμ2 := hP _ hs₁ ▸ measureReal_mono (hsup.trans inter_subset_right) (hPfin _ hs₁).ne
  have hrn : 0 < r ^ finrank ℝ E := pow_pos hr.1 _
  simp only [div_pow, inv_pow] at hμ1 hμ2 ⊢
  constructor
  · rw [le_div_iff₀ hrn]
    calc (J z₀ - ε) * ((1 + ε) ^ finrank ℝ E)⁻¹ * μ.real (A ⁻¹' ball 0 1) * r ^ finrank ℝ E
        = (J z₀ - ε) * (r ^ finrank ℝ E / (1 + ε) ^ finrank ℝ E * μ.real (A ⁻¹' ball 0 1)) := by
          ring
      _ ≤ (J z₀ - ε) * μ.real S := mul_le_mul_of_nonneg_left hμ1 (by linarith)
      _ ≤ ∫ z in S, J z ∂μ := by linarith
  · rw [div_le_iff₀ hrn]
    calc ∫ z in S, J z ∂μ ≤ (J z₀ + ε) * μ.real S := by linarith
      _ ≤ (J z₀ + ε) * (r ^ finrank ℝ E / (1 - ε) ^ finrank ℝ E * μ.real (A ⁻¹' ball 0 1)) :=
          mul_le_mul_of_nonneg_left hμ2 (by linarith)
      _ = (J z₀ + ε) * ((1 - ε) ^ finrank ℝ E)⁻¹ * μ.real (A ⁻¹' ball 0 1) * r ^ finrank ℝ E := by
          ring

/-- **Volumes of small preimages of balls.** Suppose `g` has injective derivative `A` at `z₀`,
and `‖g z - g z₀ - A (z - z₀)‖ ≤ c ‖A (z - z₀)‖` on `B_δ(z₀)` for some `c < 1` and `δ > 0`.
Let `J` be continuous at `z₀` and almost everywhere strongly measurable on `B_δ(z₀)`, with
`J z₀ = √ det ⟪A (b i), A (b j)⟫`. If `S_r = B_δ(z₀) ∩ g⁻¹(B_r(g z₀))` is measurable for every
`r > 0`, then `∫_{S_r} J dλ_b / rⁿ → ωₙ` as `r → 0⁺`, where `ωₙ` is the volume of the unit ball
of `ℝⁿ`. -/
theorem tendsto_setIntegral_preimage_ball_div_pow (b : Basis ι ℝ E) {g : E → F} {z₀ : E}
    {A : E →L[ℝ] F}
    (hg : HasFDerivAt g A z₀) (hA : Injective A) {J : E → ℝ} {δ : ℝ}
    (hJ : ContinuousAt J z₀) (hJm : AEStronglyMeasurable J (b.addHaar.restrict (ball z₀ δ)))
    (hδ : 0 < δ)
    (hJ0 : J z₀ = √(Matrix.gram ℝ fun i ↦ A (b i)).det)
    (hS : ∀ r > 0, MeasurableSet (ball z₀ δ ∩ g ⁻¹' ball (g z₀) r))
    {c : ℝ} (hc : c < 1)
    (hgδ : ∀ z ∈ ball z₀ δ, ‖g z - g z₀ - A (z - z₀)‖ ≤ c * ‖A (z - z₀)‖) :
    Tendsto (fun r ↦ (∫ z in ball z₀ δ ∩ g ⁻¹' ball (g z₀) r, J z ∂b.addHaar) /
        r ^ finrank ℝ E) (𝓝[>] 0)
      (𝓝 (volume.real (ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1))) := by
  set L := b.addHaar.real (A ⁻¹' ball 0 1)
  set ωn := volume.real (ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1)
  have hLω : J z₀ * L = ωn := by
    have h := congrArg ENNReal.toReal (ofReal_sqrt_det_gram_mul_addHaar_preimage_ball b hA)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), ← hJ0] at h
  have hω0 : 0 < ωn := ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have hJ0' : 0 < J z₀ := by
    refine (hJ0 ▸ Real.sqrt_nonneg _).lt_of_ne fun h ↦ hω0.ne ?_
    rw [← hLω, ← h, zero_mul]
  have hl : Tendsto (fun ε : ℝ ↦ (J z₀ - ε) * ((1 + ε)⁻¹) ^ finrank ℝ E * L) (𝓝[>] 0)
      (𝓝 ωn) := by
    have : ContinuousAt (fun ε : ℝ ↦ (J z₀ - ε) * ((1 + ε)⁻¹) ^ finrank ℝ E * L) 0 := by
      fun_prop (disch := norm_num)
    simpa [hLω] using this.tendsto.mono_left nhdsWithin_le_nhds
  have hh : Tendsto (fun ε : ℝ ↦ (J z₀ + ε) * ((1 - ε)⁻¹) ^ finrank ℝ E * L) (𝓝[>] 0)
      (𝓝 ωn) := by
    have : ContinuousAt (fun ε : ℝ ↦ (J z₀ + ε) * ((1 - ε)⁻¹) ^ finrank ℝ E * L) 0 := by
      fun_prop (disch := norm_num)
    simpa [hLω] using this.tendsto.mono_left nhdsWithin_le_nhds
  apply hl.squeeze_of_eventually_bounds hh
  filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos hJ0')] with ε hε
  exact eventually_le_setIntegral_div_pow_le b hg hA hJ hJm hδ hS hc hgδ hε.1
    (hε.2.trans_le (min_le_left _ _)) (hε.2.trans_le (min_le_right _ _))

end Module.Basis
