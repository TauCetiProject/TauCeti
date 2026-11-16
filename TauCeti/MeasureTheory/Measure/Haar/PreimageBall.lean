/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Volumes of small preimages of balls under a map with injective derivative

Let `E` be an `n`-dimensional real normed space with a basis `b`, let `F` be a real inner product
space and let `A : E → F` be an injective linear map. The Haar measure `λ_b` of
the ellipsoid `A⁻¹(B_1(0))`, times the Gram determinant `√ det ⟪A (b i), A (b j)⟫`, is the volume
`ωₙ` of the unit ball of `ℝⁿ`: both are the volume of the unit ball of the range of `A`, measured
through the basis `A ∘ b` of the range.

If `g : E → F` is differentiable at `z₀` with derivative `A`, then for small `r` the set
`S_r = {z : |g z - g z₀| < r}` near `z₀` lies between the ellipsoids `z₀ + A⁻¹(B_{r/(1+ε)})` and
`z₀ + A⁻¹(B_{r/(1-ε)})`. Hence, for a density `J` continuous at `z₀` with
`J z₀ = √ det ⟪A (b i), A (b j)⟫`, `∫_{S_r} J dλ_b / rⁿ → ωₙ` as `r → 0`. Read in a chart, this
says that the part near a point of an immersed submanifold of a Euclidean space inside a small
ambient ball of radius `r` about that point has area `≈ ωₙ rⁿ`, as in the small-ball limit of the
monotonicity formula for minimal submanifolds.

## Main results

* `TauCeti.ofReal_sqrt_det_gram_mul_addHaar_preimage_ball`: `√ det Gram(A b) · λ_b(A⁻¹ B_1) = ωₙ`.
* `TauCeti.exists_pos_norm_le_of_hasFDerivAt`: near `z₀`, a map with injective derivative stays
  within half of its linearization.
* `TauCeti.tendsto_setIntegral_div_pow`: `∫_{S_r} J dλ_b / rⁿ → ωₙ` as `r → 0`.

## References

* T. H. Colding and W. P. Minicozzi II, *A Course in Minimal Surfaces*, Graduate Studies in
  Mathematics 121, American Mathematical Society (2011), Chapter 1, §3.
-/

public section

open Filter Function MeasureTheory Metric Module Set
open scoped ENNReal Pointwise Topology

namespace TauCeti

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
  have he (x : E) : (e x : F) = A x := rfl
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

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A map with injective derivative stays close to its linearization.** Near `z₀`,
`|g z - g z₀ - A (z - z₀)| ≤ |A (z - z₀)| / 2`; moreover `|w| ≤ K |A w|` for some `K > 0`. -/
theorem exists_pos_norm_le_of_hasFDerivAt {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : E → G} {z₀ : E} {A : E →L[ℝ] G} (hg : HasFDerivAt g A z₀) (hA : Injective A) :
    ∃ K : ℝ, 0 < K ∧ (∀ w, ‖w‖ ≤ K * ‖A w‖) ∧ ∃ δ, 0 < δ ∧ ∀ z ∈ ball z₀ δ,
      ‖g z - g z₀ - A (z - z₀)‖ ≤ ‖A (z - z₀)‖ / 2 := by
  obtain ⟨K, hK0, hK⟩ := (LinearMap.injective_iff_antilipschitz (A : E →ₗ[ℝ] G)).1 hA
  have hKA (w : E) : ‖w‖ ≤ K * ‖A w‖ := by simpa using hK.le_mul_dist w 0
  have hK0' : (0 : ℝ) < K := hK0
  refine ⟨K, hK0', hKA, ?_⟩
  obtain ⟨δ, hδ, hδm⟩ := Metric.eventually_nhds_iff_ball.1
    (hg.isLittleO.def (show (0 : ℝ) < 1 / (2 * K) by positivity))
  refine ⟨δ, hδ, fun z hz ↦ (hδm z hz).trans ?_⟩
  calc 1 / (2 * K) * ‖z - z₀‖ ≤ 1 / (2 * K) * (K * ‖A (z - z₀)‖) := by gcongr; exact hKA _
    _ = ‖A (z - z₀)‖ / 2 := by field_simp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
/-- A vector `x` within `c ‖y‖` of `y` has norm between `(1 - c) ‖y‖` and `(1 + c) ‖y‖`. -/
private theorem norm_bounds_of_norm_sub_le {G : Type*} [SeminormedAddCommGroup G] {x y : G} {c : ℝ}
    (h : ‖x - y‖ ≤ c * ‖y‖) :
    (1 - c) * ‖y‖ ≤ ‖x‖ ∧ ‖x‖ ≤ (1 + c) * ‖y‖ := by
  have h1 := norm_sub_norm_le x y
  have h2 := norm_sub_norm_le y x
  rw [norm_sub_rev y x] at h2
  constructor <;> nlinarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Near `z₀`, a map differentiable at `z₀` is within `ε ‖A (z - z₀)‖` of its linearization, and
a function continuous at `z₀` is within `ε` of its value there. -/
private theorem exists_forall_mem_ball_le {g : E → F} {z₀ : E} {A : E →L[ℝ] F}
    (hg : HasFDerivAt g A z₀) {K : ℝ} (hK : 0 < K) (hKA : ∀ w, ‖w‖ ≤ K * ‖A w‖) {J : E → ℝ}
    (hJ : ContinuousAt J z₀) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ δε, 0 < δε ∧ δε ≤ δ ∧ ∀ z ∈ ball z₀ δε,
      ‖g z - g z₀ - A (z - z₀)‖ ≤ ε * ‖A (z - z₀)‖ ∧ |J z - J z₀| ≤ ε := by
  have h1 : ∀ᶠ z in 𝓝 z₀, ‖g z - g z₀ - A (z - z₀)‖ ≤ ε / K * ‖z - z₀‖ :=
    hg.isLittleO.def (by positivity)
  have h2 : ∀ᶠ z in 𝓝 z₀, |J z - J z₀| ≤ ε :=
    (hJ.eventually (Metric.closedBall_mem_nhds (J z₀) hε)).mono fun z hz ↦ by
      simpa [Real.dist_eq] using hz
  obtain ⟨δ', hδ', hδ'm⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  refine ⟨min δ δ', lt_min hδ hδ', min_le_left _ _, fun z hz ↦ ?_⟩
  obtain ⟨hz1, hz2⟩ := hδ'm z (ball_subset_ball (min_le_right _ _) hz)
  refine ⟨hz1.trans ?_, hz2⟩
  calc ε / K * ‖z - z₀‖ ≤ ε / K * (K * ‖A (z - z₀)‖) := by gcongr; exact hKA _
    _ = ε * ‖A (z - z₀)‖ := by field_simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For small `r`, the set `S_r = B_δ(z₀) ∩ g⁻¹(B_r(g z₀))` lies in `B_{δε}(z₀)` and between the
ellipsoids `z₀ + A⁻¹(B_{r/(1+ε)})` and `z₀ + A⁻¹(B_{r/(1-ε)})`. -/
private theorem preimage_ball_subset_and_subset {g : E → F} {z₀ : E} {A : E →L[ℝ] F}
    {K δ δε ε r : ℝ} (hK : 0 < K) (hKA : ∀ w, ‖w‖ ≤ K * ‖A w‖)
    (hgδ : ∀ z ∈ ball z₀ δ, ‖g z - g z₀ - A (z - z₀)‖ ≤ ‖A (z - z₀)‖ / 2)
    (hest : ∀ z ∈ ball z₀ δε, ‖g z - g z₀ - A (z - z₀)‖ ≤ ε * ‖A (z - z₀)‖)
    (hδε : δε ≤ δ) (hε : 0 < ε) (hε1 : ε < 1) (hr : 0 < r) (hrδ : 2 * K * r < δε) :
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
        _ < δε := by nlinarith
    refine ⟨ball_subset_ball hδε hzδε, ?_⟩
    rw [mem_preimage, mem_ball, dist_eq_norm]
    nlinarith [(norm_bounds_of_norm_sub_le (hest z hzδε)).2]
  · rintro z ⟨hzδ, hzr⟩
    rw [mem_preimage, mem_ball, dist_eq_norm] at hzr
    have hA2 := (norm_bounds_of_norm_sub_le ((hgδ z hzδ).trans_eq
      (by ring : ‖A (z - z₀)‖ / 2 = 1 / 2 * ‖A (z - z₀)‖))).1
    have hzδε : z ∈ ball z₀ δε := by
      rw [mem_ball, dist_eq_norm]
      calc ‖z - z₀‖ ≤ K * ‖A (z - z₀)‖ := hKA _
        _ < δε := by nlinarith [norm_nonneg (A (z - z₀))]
    refine ⟨hzδε, ?_⟩
    rw [mem_preimage, mem_ball_zero_iff, lt_div_iff₀ (by linarith)]
    nlinarith [(norm_bounds_of_norm_sub_le (hest z hzδε)).1]

omit [DecidableEq ι] in
/-- The ellipsoid `z₀ + A⁻¹(B_s)` has measure `sⁿ λ_b(A⁻¹(B_1))`. -/
private theorem addHaar_preimage_ball_sub (b : Basis ι ℝ E) (A : E →L[ℝ] F) (z₀ : E) {s : ℝ}
    (hs : 0 < s) :
    b.addHaar ((fun z ↦ A (z - z₀)) ⁻¹' ball 0 s) =
      ENNReal.ofReal (s ^ finrank ℝ E) * b.addHaar (A ⁻¹' ball 0 1) := by
  have hset : (fun z ↦ A (z - z₀)) ⁻¹' ball (0 : F) s =
      (fun z ↦ z + -z₀) ⁻¹' (s • (A ⁻¹' ball (0 : F) 1)) := by
    ext z
    rw [mem_preimage, mem_preimage, mem_smul_set_iff_inv_smul_mem₀ hs.ne', mem_preimage,
      mem_ball_zero_iff, mem_ball_zero_iff, map_smul, norm_smul, Real.norm_of_nonneg
        (inv_nonneg.2 hs.le), ← sub_eq_add_neg, inv_mul_lt_iff₀ hs, mul_one]
  rw [hset, measure_preimage_add_right, Measure.addHaar_smul, abs_of_nonneg (by positivity)]

omit [DecidableEq ι] in
/-- The ellipsoid `A⁻¹(B_1)` of an injective linear map has finite measure. -/
private theorem addHaar_preimage_ball_lt_top (b : Basis ι ℝ E) {A : E →L[ℝ] F} {K : ℝ}
    (hK : 0 ≤ K) (hKA : ∀ w, ‖w‖ ≤ K * ‖A w‖) : b.addHaar (A ⁻¹' ball 0 1) < ⊤ := by
  refine (Metric.isBounded_closedBall (x := (0 : E)) (r := K)).subset (fun w hw ↦ ?_)
    |>.measure_lt_top
  rw [mem_closedBall_zero_iff]
  rw [mem_preimage, mem_ball_zero_iff] at hw
  nlinarith [hKA w, norm_nonneg w]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A function within `ε` of the constant `c` on an open set `S` of finite measure has integral
over `S` within `ε μ(S)` of `c μ(S)`. -/
private theorem abs_setIntegral_sub_mul_le {μ : Measure E} {S : Set E} (hS : IsOpen S)
    (hSfin : μ S < ⊤) {J : E → ℝ} (hJ : ContinuousOn J S) {c ε : ℝ}
    (hJS : ∀ z ∈ S, |J z - c| ≤ ε) :
    |(∫ z in S, J z ∂μ) - c * μ.real S| ≤ ε * μ.real S := by
  have hJint : IntegrableOn J S μ := by
    refine IntegrableOn.of_bound hSfin (hJ.aestronglyMeasurable hS.measurableSet) (|c| + ε)
      (ae_restrict_of_forall_mem hS.measurableSet fun z hz ↦ ?_)
    rw [Real.norm_eq_abs]
    linarith [abs_sub_abs_le_abs_sub (J z) c, hJS z hz]
  have heq : (∫ z in S, J z ∂μ) - c * μ.real S = ∫ z in S, (J z - c) ∂μ := by
    rw [integral_sub hJint (integrableOn_const hSfin.ne), setIntegral_const, smul_eq_mul,
      mul_comm]
  have h := norm_setIntegral_le_of_norm_le_const hSfin fun z hz ↦
    (Real.norm_eq_abs (J z - c)).trans_le (hJS z hz)
  rwa [Real.norm_eq_abs, ← heq] at h

omit [DecidableEq ι] in
/-- The two-sided estimate behind `tendsto_setIntegral_div_pow`, at a fixed small `ε`. -/
private theorem eventually_le_setIntegral_div_pow_le (b : Basis ι ℝ E) {g : E → F} {z₀ : E}
    {A : E →L[ℝ] F} (hg : HasFDerivAt g A z₀) (hA : Injective A) {J : E → ℝ} {δ : ℝ}
    (hJ : ContinuousOn J (ball z₀ δ)) (hδ : 0 < δ) (hgc : ContinuousOn g (ball z₀ δ))
    (hgδ : ∀ z ∈ ball z₀ δ, ‖g z - g z₀ - A (z - z₀)‖ ≤ ‖A (z - z₀)‖ / 2) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hεJ : ε < J z₀) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (J z₀ - ε) * ((1 + ε)⁻¹) ^ finrank ℝ E * b.addHaar.real (A ⁻¹' ball 0 1) ≤
          (∫ z in ball z₀ δ ∩ g ⁻¹' ball (g z₀) r, J z ∂b.addHaar) / r ^ finrank ℝ E ∧
        (∫ z in ball z₀ δ ∩ g ⁻¹' ball (g z₀) r, J z ∂b.addHaar) / r ^ finrank ℝ E ≤
          (J z₀ + ε) * ((1 - ε)⁻¹) ^ finrank ℝ E * b.addHaar.real (A ⁻¹' ball 0 1) := by
  obtain ⟨K, hK0, hK⟩ := (LinearMap.injective_iff_antilipschitz (A : E →ₗ[ℝ] F)).1 hA
  have hKA (w : E) : ‖w‖ ≤ K * ‖A w‖ := by simpa using hK.le_mul_dist w 0
  have hK0' : (0 : ℝ) < K := hK0
  obtain ⟨δε, hδε, hδεδ, hest⟩ := exists_forall_mem_ball_le hg hK0' hKA
    (hJ.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hδ))) hδ hε
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < δε / (2 * K) by positivity)] with r hr
  obtain ⟨hsub, hsup⟩ := preimage_ball_subset_and_subset hK0' hKA hgδ (fun z hz ↦ (hest z hz).1)
    hδεδ hε hε1 hr.1 (by have := hr.2; rw [lt_div_iff₀ (by positivity)] at this; linarith)
  set S := ball z₀ δ ∩ g ⁻¹' ball (g z₀) r
  set μ := b.addHaar
  have hP (s : ℝ) (hs : 0 < s) : μ.real ((fun z ↦ A (z - z₀)) ⁻¹' ball 0 s) =
      s ^ finrank ℝ E * μ.real (A ⁻¹' ball 0 1) := by
    rw [measureReal_def, addHaar_preimage_ball_sub b A z₀ hs, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), measureReal_def]
  have hPfin (s : ℝ) (hs : 0 < s) : μ ((fun z ↦ A (z - z₀)) ⁻¹' ball 0 s) < ⊤ := by
    rw [addHaar_preimage_ball_sub b A z₀ hs]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (addHaar_preimage_ball_lt_top b hK0'.le hKA)
  have hs₁ : 0 < r / (1 - ε) := div_pos hr.1 (by linarith)
  have hSfin : μ S < ⊤ :=
    (measure_mono (hsup.trans inter_subset_right)).trans_lt (hPfin _ hs₁)
  have hd := abs_le.1 (abs_setIntegral_sub_mul_le
    (hgc.isOpen_inter_preimage isOpen_ball isOpen_ball) hSfin (hJ.mono inter_subset_left)
    fun z hz ↦ (hest z (hsup hz).1).2)
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

/-- A squeeze: if for every small `ε > 0`, eventually `l ε ≤ u ≤ h ε`, and `l ε` and `h ε` tend to
`c` as `ε → 0⁺`, then `u` tends to `c`. -/
private theorem tendsto_of_forall_eventually_mem {α : Type*} {f : Filter α} {u : α → ℝ} {c : ℝ}
    {l h : ℝ → ℝ} {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hl : Tendsto l (𝓝[>] 0) (𝓝 c))
    (hh : Tendsto h (𝓝[>] 0) (𝓝 c))
    (H : ∀ ε, 0 < ε → ε < ε₀ → ∀ᶠ x in f, l ε ≤ u x ∧ u x ≤ h ε) : Tendsto u f (𝓝 c) := by
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · obtain ⟨ε, hε1, hε2⟩ :=
      ((hl.eventually (lt_mem_nhds ha)).and (Ioo_mem_nhdsGT hε₀)).exists
    exact (H ε hε2.1 hε2.2).mono fun x hx ↦ hε1.trans_le hx.1
  · obtain ⟨ε, hε1, hε2⟩ :=
      ((hh.eventually (gt_mem_nhds ha)).and (Ioo_mem_nhdsGT hε₀)).exists
    exact (H ε hε2.1 hε2.2).mono fun x hx ↦ hx.2.trans_lt hε1

/-- **Volumes of small preimages of balls.** Let `g : E → F` be continuous on `B_δ(z₀)` and
differentiable at `z₀` with injective derivative `A`, with
`|g z - g z₀ - A (z - z₀)| ≤ |A (z - z₀)| / 2` on `B_δ(z₀)`, and let `J` be continuous on
`B_δ(z₀)` with `J z₀ = √ det ⟪A (b i), A (b j)⟫`. Then `∫_{S_r} J dλ_b / rⁿ → ωₙ` as `r → 0⁺`,
where `S_r = B_δ(z₀) ∩ g⁻¹(B_r(g z₀))` and `ωₙ` is the volume of the unit ball of `ℝⁿ`. -/
theorem tendsto_setIntegral_div_pow (b : Basis ι ℝ E) {g : E → F} {z₀ : E} {A : E →L[ℝ] F}
    (hg : HasFDerivAt g A z₀) (hA : Injective A) {J : E → ℝ} {δ : ℝ}
    (hJ : ContinuousOn J (ball z₀ δ)) (hδ : 0 < δ)
    (hJ0 : J z₀ = √(Matrix.gram ℝ fun i ↦ A (b i)).det) (hgc : ContinuousOn g (ball z₀ δ))
    (hgδ : ∀ z ∈ ball z₀ δ, ‖g z - g z₀ - A (z - z₀)‖ ≤ ‖A (z - z₀)‖ / 2) :
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
  exact tendsto_of_forall_eventually_mem (lt_min one_pos hJ0') hl hh fun ε hε hε' ↦
    eventually_le_setIntegral_div_pow_le b hg hA hJ hδ hgc hgδ hε
      (hε'.trans_le (min_le_left _ _)) (hε'.trans_le (min_le_right _ _))

end TauCeti
