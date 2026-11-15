/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.EllipticRegularity
public import TauCeti.Analysis.Pseudodifferential.Symbol.Differential
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
import TauCeti.Analysis.Distribution.TemperedDistribution.Deriv
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# Local elliptic regularity for differential operators

Let `P = ∑ i ∈ t, c i g i ∂^{m i}` be a linear differential operator of order `k` on an open set
`Ω ⊆ ℝⁿ`, with smooth real coefficients `g i`, and suppose that `P` is elliptic at a point `x`.
This file proves **local elliptic regularity** for distributions: if `P T` is `H^(s - k)` near
`x`, then `T` is `H^s` near `x`
(`Distribution.IsLocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`). Here `T` is an
arbitrary distribution on `Ω`, of any order, and `H^s` near `x` is
`Distribution.IsLocallySobolevAt`: some cutoff `φ T` with `φ x ≠ 0` lies in the Bessel-potential
space `H^s(ℝⁿ)`. Together with the converse
`Distribution.IsLocallySobolevAt.sum_smul_smulLeftCLM_iteratedLineDerivOp`, valid for every
differential operator, this says that an elliptic operator of order `k` shifts local Sobolev
regularity by exactly `k`.

The proof applies the pseudodifferential parametrix on Bessel-potential spaces
(`TauCeti.Symbol.IsEllipticAbove.memSobolev_smulLeftCLM`) to the tempered distribution `χ T` for
a cutoff `χ` equal to `1` near `x`, which lies in some `H^r`. Two facts connect the symbol calculus
with `P`.

* `TauCeti.ClassicalSymbol.toDistr_quantizeSobolev_ofDifferentialSymbol`: the quantization
  `Op(a) : H^r → H^(r - k)` of the symbol `a` of a differential operator with compactly supported
  scalar coefficients is that differential operator, acting on tempered distributions. Applied
  to the coefficients `ψ c i g i`, for a cutoff `ψ` with `χ = 1` near its support, it maps `χ T`
  to `ψ (P T)` (`Distribution.smulLeftCLM_iteratedLineDerivOp_cutoffTempered`).
* `TauCeti.Symbol.exists_isEllipticAbove_and_eventually_coefficient_eq_differentialSymbol`: the
  parametrix needs a symbol elliptic above a fixed radius at all positions, whereas `P` is only
  elliptic near `x`. Freezing the coefficients of `P` outside a small ball, that is, evaluating
  them at `x + θ(y) (y - x)` for a bump function `θ` equal to `1` near `x`, gives such a symbol
  agreeing with the symbol of `P` near `x`.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.6)–(4.11).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open scoped SchwartzMap BesselPotentialSpace ContDiff Topology Distributions LineDeriv
  RealInnerProductSpace

namespace TauCeti

namespace ClassicalSymbol

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {ι : Type*} {k : ι → ℕ}

/-- **Differential operators on Bessel-potential spaces.** Let `a` be the symbol of the
differential operator `u ↦ ∑ i ∈ s, βᵢ ∂^{vᵢ} u` with scalar coefficients `βᵢ` of temperate
growth, and suppose `a` has compact spatial support, for instance because the `βᵢ` are compactly
supported. Then the operator `Op(a) : H^r → H^{r - m}` is this differential operator in the sense
of tempered distributions. -/
theorem toDistr_quantizeSobolev_ofDifferentialSymbol [CompleteSpace V] (m : ℕ) (s : Finset ι)
    (v : ∀ i, Fin (k i) → CoordinateSpace n) {β : ι → CoordinateSpace n → ℂ}
    (hβ : ∀ i ∈ s, (β i).HasTemperateGrowth) (hk : ∀ i ∈ s, k i ≤ m)
    (ha : (ofDifferentialSymbol m s v (fun i x ↦ β i x • ContinuousLinearMap.id ℂ V)
      (fun i hi ↦ (hβ i hi).1.smul contDiff_const) hk).toSymbol.HasCompactSpatialSupport)
    (r : ℝ) (u : H^{r}(CoordinateSpace n, V)) :
    ((ofDifferentialSymbol m s v _ _ hk).toSymbol.quantizeSobolev ha r u).toDistr =
      ∑ i ∈ s, TemperedDistribution.smulLeftCLM V (β i) (∂^{v i} u.toDistr) := by
  let D (t : ℝ) : H^{t}(CoordinateSpace n, V) →L[ℂ] 𝓢'(CoordinateSpace n, V) :=
    ⟨⟨⟨fun u ↦ u.toDistr, BesselPotentialSpace.toDistr_add⟩,
      BesselPotentialSpace.toDistr_smul⟩, BesselPotentialSpace.continuous_toDistr⟩
  have key : D _ ∘L (ofDifferentialSymbol m s v _ _ hk).toSymbol.quantizeSobolev ha r =
      (∑ i ∈ s, TemperedDistribution.smulLeftCLM V (β i) ∘L
        LineDeriv.iteratedLineDerivOpCLM ℂ 𝓢'(CoordinateSpace n, V) (v i)) ∘L D r := by
    refine BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun u ↦ ?_
    ext φ
    simp only [D, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_mk',
      LinearMap.coe_mk, AddHom.coe_mk,
      Symbol.toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply,
      quantizeSchwartzValue_ofDifferentialSymbol, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
      sum_apply, LineDeriv.iteratedLineDerivOpCLM_apply,
      TemperedDistribution.iteratedLineDerivOp_toTemperedDistributionCLM_eq,
      TemperedDistribution.smulLeftCLM_toTemperedDistributionCLM_eq]
    rw [← sum_apply, ← map_sum,
      SchwartzMap.toTemperedDistributionCLM_apply_apply MeasureTheory.volume]
    refine MeasureTheory.integral_congr_ae (.of_forall fun x ↦ ?_)
    simp only [sum_apply, smul_apply,
      ContinuousLinearMap.id_apply]
    congr 1
    exact Finset.sum_congr rfl fun i hi ↦ by
      rw [SchwartzMap.smulLeftCLM_apply_apply (hβ i hi)]
  simpa [D] using congrArg (fun T ↦ T u) key

end ClassicalSymbol

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {ι : Type*} {k : ι → ℕ}

/-- Invertibility of a homogeneous differential symbol at a point and every nonzero frequency
persists on a ball around that point. -/
private theorem exists_pos_forall_isInvertible_differentialSymbol (s : Finset ι)
    (v : ∀ i, Fin (k i) → CoordinateSpace n) {b : ι → CoordinateSpace n → V →L[ℂ] W}
    (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i)) {d : ℕ} (hk : ∀ i ∈ s, k i = d) {x₀ : CoordinateSpace n}
    (hx₀ : ∀ ξ, ξ ≠ 0 → (differentialSymbol s v b (x₀, ξ)).IsInvertible) :
    ∃ r > 0, ∀ x ∈ Metric.closedBall x₀ r, ∀ ξ, ξ ≠ 0 →
      (differentialSymbol s v b (x, ξ)).IsInvertible := by
  -- Invertibility at the unit frequencies is an open condition, and the sphere is compact.
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ e ∈ Metric.sphere (0 : CoordinateSpace n) 1,
      (differentialSymbol s v b (x, e)).IsInvertible :=
    (isCompact_sphere 0 1).eventually_forall_of_forall_eventually fun e he ↦
      (contDiff_differentialSymbol s v hb).continuous.continuousAt.preimage_mem_nhds
        (ContinuousLinearEquiv.isOpen.mem_nhds (hx₀ e (by rintro rfl; simp at he)))
  obtain ⟨r, hr, hrD⟩ := Metric.eventually_nhds_iff_ball.1 hev
  -- By homogeneity, it holds at every nonzero frequency.
  refine ⟨r / 2, by positivity, fun x hx ξ hξ ↦ ?_⟩
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hu : ‖ξ‖⁻¹ • ξ ∈ Metric.sphere (0 : CoordinateSpace n) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have h := hrD x (Metric.closedBall_subset_ball (by linarith) hx) _ hu
  rwa [← ContinuousLinearMap.isInvertible_smul_iff (c := ((‖ξ‖ ^ d : ℝ) : ℂ)) (by simp [hn.ne']),
    Complex.coe_smul, ← differentialSymbol_smul_snd s v b hk, smul_smul,
    mul_inv_cancel₀ hn.ne', one_smul] at h

/-- **Differential operators elliptic at a point are locally elliptic symbols.** Let
`P u = ∑ i ∈ s, bᵢ(x) (∂^{vᵢ} u)(x)` be a differential operator of order `m` with smooth
coefficients whose top-order part is invertible at `x₀` at every nonzero frequency. Then some
symbol of order `m`, elliptic above a radius `R` at every position, agrees with the symbol of `P`
near `x₀`. -/
theorem exists_isEllipticAbove_and_eventually_coefficient_eq_differentialSymbol (m : ℕ)
    (s : Finset ι) (v : ∀ i, Fin (k i) → CoordinateSpace n)
    {b : ι → CoordinateSpace n → V →L[ℂ] W} (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i))
    (hk : ∀ i ∈ s, k i ≤ m) {x₀ : CoordinateSpace n}
    (hx₀ : ∀ ξ, ξ ≠ 0 → (differentialSymbol {i ∈ s | k i = m} v b (x₀, ξ)).IsInvertible) :
    ∃ (p : Symbol n V W m) (R : ℝ), p.IsEllipticAbove R ∧
      ∀ᶠ x in 𝓝 x₀, ∀ ξ, p.coefficient (x, ξ) = differentialSymbol s v b (x, ξ) := by
  obtain ⟨r, hr, hinv⟩ := exists_pos_forall_isInvertible_differentialSymbol _ v
    (fun i hi ↦ hb i (Finset.mem_filter.1 hi).1) (fun i hi ↦ (Finset.mem_filter.1 hi).2) hx₀
  -- Freeze the coefficients outside the ball of radius `r`: the symbol `a` is the symbol of `P` at
  -- the position `G x = x₀ + θ(x) (x - x₀)`, which stays in that ball.
  let θ : ContDiffBump x₀ := ⟨r / 2, r, by positivity, by linarith⟩
  set G : CoordinateSpace n → CoordinateSpace n := fun x ↦ x₀ + θ x • (x - x₀) with hG
  have hGc : ContDiff ℝ ∞ G := contDiff_const.add (θ.contDiff.smul (contDiff_id.sub contDiff_const))
  have hGball (x : CoordinateSpace n) : G x ∈ Metric.closedBall x₀ r := by
    rw [Metric.mem_closedBall, hG, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg θ.nonneg, ← dist_eq_norm]
    by_cases hx : dist x x₀ < r
    · exact (mul_le_of_le_one_left dist_nonneg θ.le_one).trans hx.le
    · rw [θ.zero_of_le_dist (not_lt.1 hx), zero_mul]
      positivity
  have hGout (x : CoordinateSpace n) (hx : x ∉ Metric.closedBall x₀ r) : G x = G x₀ := by
    rw [Metric.mem_closedBall, not_le] at hx
    simp [hG, θ.zero_of_le_dist hx.le]
  have hGin (x : CoordinateSpace n) (hx : x ∈ Metric.closedBall x₀ (r / 2)) : G x = x := by
    simp [hG, θ.one_of_mem_closedBall hx]
  let a := ClassicalSymbol.ofDifferentialSymbol m s v (fun i x ↦ b i (G x))
    (fun i hi ↦ (hb i hi).comp hGc) hk
  have hcomp (t : Finset ι) (x ξ : CoordinateSpace n) :
      differentialSymbol t v (fun i x ↦ b i (G x)) (x, ξ) = differentialSymbol t v b (G x, ξ) := by
    simp only [differentialSymbol_def]
  have ha (x ξ : CoordinateSpace n) :
      a.toSymbol.coefficient (x, ξ) = differentialSymbol s v b (G x, ξ) := by
    rw [ClassicalSymbol.coefficient_toSymbol_ofDifferentialSymbol, hcomp]
  have hell : a.IsElliptic :=
    (ClassicalSymbol.isElliptic_ofDifferentialSymbol_iff ..).2 fun x ξ hξ ↦ by
      rw [hcomp]
      exact hinv _ (hGball x) ξ hξ
  obtain ⟨R, C, hRC⟩ := hell.exists_isInvertible_and_norm_inverse_le (isCompact_closedBall x₀ r)
  refine ⟨a.toSymbol, R, isEllipticAbove_iff.2 fun K _ ↦ ⟨C, fun x _ ξ hξ ↦ ?_⟩, ?_⟩
  · by_cases hx : x ∈ Metric.closedBall x₀ r
    · exact hRC x hx ξ hξ
    · rw [ha, hGout x hx, ← ha]
      exact hRC x₀ (Metric.mem_closedBall_self (by positivity)) ξ hξ
  · filter_upwards [Metric.closedBall_mem_nhds x₀ (by positivity : 0 < r / 2)] with x hx ξ
    rw [ha, hGin x hx]

end Symbol

end TauCeti

namespace Distribution

open TopologicalSpace TauCeti

variable {n : ℕ} {Ω : Opens (CoordinateSpace n)}

/-- The complex test function given by a bump function whose support lies in `Ω`. -/
private def bumpTestFunction {x : CoordinateSpace n} (f : ContDiffBump x)
    (hf : Metric.closedBall x f.rOut ⊆ Ω) : 𝓓(Ω, ℂ) :=
  ⟨fun y ↦ (f y : ℂ), Complex.ofRealCLM.contDiff.comp f.contDiff,
    f.hasCompactSupport.comp_left Complex.ofReal_zero,
    (tsupport_comp_subset Complex.ofReal_zero f).trans (f.tsupport_eq ▸ hf)⟩

private theorem bumpTestFunction_apply {x : CoordinateSpace n} (f : ContDiffBump x)
    (hf : Metric.closedBall x f.rOut ⊆ Ω) (y : CoordinateSpace n) :
    bumpTestFunction f hf y = f y :=
  rfl

private theorem tsupport_bumpTestFunction {x : CoordinateSpace n} (f : ContDiffBump x)
    (hf : Metric.closedBall x f.rOut ⊆ Ω) :
    tsupport (bumpTestFunction f hf) ⊆ Metric.closedBall x f.rOut :=
  (tsupport_comp_subset Complex.ofReal_zero f).trans f.tsupport_eq.le

/-- A bump function `f` is equal to `1` near the support of a bump function with a smaller outer
radius than the inner radius of `f`. -/
private theorem eventually_bumpTestFunction_eq_one {x : CoordinateSpace n} {f g : ContDiffBump x}
    (hf : Metric.closedBall x f.rOut ⊆ Ω) (hg : Metric.closedBall x g.rOut ⊆ Ω)
    (hfg : g.rOut < f.rIn) : ∀ᶠ y in 𝓝ˢ (tsupport (bumpTestFunction g hg)),
      bumpTestFunction f hf y = 1 :=
  Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhdsSet.2
    ((tsupport_bumpTestFunction g hg).trans (Metric.closedBall_subset_ball hfg))) fun y hy ↦ by
      rw [bumpTestFunction_apply, f.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),
        Complex.ofReal_one]

/-- The top-order part of the symbol of `∑ i ∈ t, c i g i ∂^{m i}` is `i ^ k` times the scalar
principal symbol `∑_{d i = k} c i g i(x) ∏ₗ ⟪m i l, ξ⟫`. -/
private theorem differentialSymbol_filter_eq {ι : Type*} (t : Finset ι) (c : ι → ℂ)
    (g : ι → CoordinateSpace n → ℝ) {d : ι → ℕ} (m : ∀ i, Fin (d i) → CoordinateSpace n) (k : ℕ)
    (x ξ : CoordinateSpace n) :
    differentialSymbol {i ∈ t | d i = k} m
        (fun i y ↦ (c i * g i y) • ContinuousLinearMap.id ℂ ℂ) (x, ξ) =
      (Complex.I ^ k * ∑ i ∈ t with d i = k, c i * ↑(g i x * ∏ l, ⟪m i l, ξ⟫)) •
        ContinuousLinearMap.id ℂ ℂ := by
  ext
  simp only [differentialSymbol_def, sum_apply, smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, mul_one, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← (Finset.mem_filter.1 hi).2]
  push_cast
  simp only [real_inner_comm]
  ring

/-- Three nested test functions around `x`, supported in a given neighbourhood `W ⊆ Ω` of `x`:
`φ` does not vanish at `x`, `ψ` is equal to `1` near the support of `φ`, and `χ` is equal to `1`
near the support of `ψ`. -/
private theorem exists_nested_testFunctions {x : CoordinateSpace n} {W : Set (CoordinateSpace n)}
    (hW : W ∈ 𝓝 x) (hWΩ : W ⊆ Ω) :
    ∃ φ ψ χ : 𝓓(Ω, ℂ), φ x ≠ 0 ∧ tsupport ψ ⊆ W ∧ (∀ᶠ y in 𝓝ˢ (tsupport φ), ψ y = 1) ∧
      ∀ᶠ y in 𝓝ˢ (tsupport ψ), χ y = 1 := by
  obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhds_iff.1 hW
  have hball (f : ContDiffBump x) (hf : f.rOut < δ) : Metric.closedBall x f.rOut ⊆ Ω :=
    (Metric.closedBall_subset_ball hf).trans (hδW.trans hWΩ)
  let φb : ContDiffBump x := ⟨δ / 8, δ / 4, by positivity, by linarith⟩
  let ψb : ContDiffBump x := ⟨3 * δ / 8, δ / 2, by positivity, by linarith⟩
  let χb : ContDiffBump x := ⟨5 * δ / 8, 3 * δ / 4, by positivity, by linarith⟩
  have hφb : φb.rOut < δ := by simp [φb]; linarith
  have hψb : ψb.rOut < δ := by simp [ψb]; linarith
  have hχb : χb.rOut < δ := by simp [χb]; linarith
  refine ⟨bumpTestFunction φb (hball φb hφb), bumpTestFunction ψb (hball ψb hψb),
    bumpTestFunction χb (hball χb hχb), ?_, (tsupport_bumpTestFunction _ _).trans
      ((Metric.closedBall_subset_ball hψb).trans hδW),
    eventually_bumpTestFunction_eq_one _ _ (by simp [φb, ψb]; linarith),
    eventually_bumpTestFunction_eq_one _ _ (by simp [ψb, χb]; linarith)⟩
  rw [bumpTestFunction_apply, φb.one_of_mem_closedBall (Metric.mem_closedBall_self φb.rIn_pos.le),
    Complex.ofReal_one]
  exact one_ne_zero

/-- Let `χ` be equal to `1` near the support of `ψ`. On an element `u` of `H^r` whose tempered
distribution is `χ T`, the localized differential operator `ψ P`, with coefficients `c i ψ g i`,
gives the cut-off `ψ (P T)` of `P T` for `P = ∑ i ∈ t, c i g i ∂^{m i}`. -/
private theorem toDistr_quantizeSobolev_ofDifferentialSymbol_eq_cutoffTempered (T : 𝓓'(Ω, ℂ))
    {χ ψ : 𝓓(Ω, ℂ)} (hχψ : ∀ᶠ y in 𝓝ˢ (tsupport ψ), χ y = 1) {ι : Type*} (t : Finset ι)
    (c : ι → ℂ) {g : ι → CoordinateSpace n → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i)) {d : ι → ℕ}
    (m : ∀ i, Fin (d i) → CoordinateSpace n) {k : ℕ} (hk : ∀ i ∈ t, d i ≤ k)
    (hb : ∀ i ∈ t, ContDiff ℝ ∞ fun y ↦ (c i * (ψ y * g i y)) • ContinuousLinearMap.id ℂ ℂ)
    (ha : (ClassicalSymbol.ofDifferentialSymbol k t m _ hb hk).toSymbol.HasCompactSpatialSupport)
    {r : ℝ} (u : H^{r}(CoordinateSpace n, ℂ)) (hu : u.toDistr = T.cutoffTempered χ) :
    ((ClassicalSymbol.ofDifferentialSymbol k t m _ hb hk).toSymbol.quantizeSobolev ha r u).toDistr =
      (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).cutoffTempered ψ := by
  have hψg (i : ι) : (fun y ↦ ψ y * (g i y : ℂ)).HasTemperateGrowth :=
    HasCompactSupport.hasTemperateGrowth ψ.hasCompactSupport.mul_right
      (ψ.contDiff.mul (Complex.ofRealCLM.contDiff.comp (hg i)))
  have hβ : ∀ i ∈ t, (fun y ↦ c i * (ψ y * (g i y : ℂ))).HasTemperateGrowth := fun i _ ↦
    ψ.hasCompactSupport.mul_right.mul_left.hasTemperateGrowth
      (contDiff_const.mul (hψg i).1)
  rw [ClassicalSymbol.toDistr_quantizeSobolev_ofDifferentialSymbol k t m hβ hk ha, hu,
    cutoffTempered_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hβi : (fun y ↦ c i * (ψ y * (g i y : ℂ))) = c i • fun y ↦ ψ y * (g i y : ℂ) := by
    ext y
    simp
  rw [hβi, TemperedDistribution.smulLeftCLM_smul (hψg i), smul_apply, cutoffTempered_smul,
    smulLeftCLM_iteratedLineDerivOp_cutoffTempered T hχψ (hg i)]

/-- **Local elliptic regularity for differential operators with smooth coefficients.** Let
`P = ∑ i ∈ t, c i g i ∂^{m i}` be a linear differential operator on `Ω ⊆ ℝⁿ` with smooth real
coefficients `g i`, complex constants `c i` and derivatives `∂^{m i}` of orders `d i ≤ k`, and let
`P` be elliptic at `x`: its principal symbol
`σ_k(P)(x, ξ) = ∑_{d i = k} c i g i(x) ∏ₗ ⟪m i l, ξ⟫` vanishes at no nonzero `ξ`. If `P T` is
`H^(s - k)` near `x`, then `T` is `H^s` near `x`, for every distribution `T` and every real `s`. -/
theorem IsLocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp {T : 𝓓'(Ω, ℂ)}
    {x : CoordinateSpace n} {s : ℝ} {ι : Type*} {t : Finset ι} {c : ι → ℂ}
    {g : ι → CoordinateSpace n → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i)) {d : ι → ℕ}
    {m : ∀ i, Fin (d i) → CoordinateSpace n} {k : ℕ} (hk : ∀ i ∈ t, d i ≤ k)
    (hP : ∀ ξ, ξ ≠ 0 → ∑ i ∈ t with d i = k, c i * ↑(g i x * ∏ l, ⟪m i l, ξ⟫) ≠ 0)
    (h : (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).IsLocallySobolevAt
      (s - k) x) :
    T.IsLocallySobolevAt s x := by
  obtain ⟨U, hU, hPT⟩ := h.exists_nhds_forall_memSobolev_cutoffTempered
  have hxΩ : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isLocallySobolevAt_iff_exists_memSobolev_cutoffTempered.1 h
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  -- A symbol `p` elliptic above some radius that agrees with the symbol of `P` near `x`.
  have hb : ∀ i ∈ t, ContDiff ℝ ∞ fun y ↦ (c i * g i y) • ContinuousLinearMap.id ℂ ℂ :=
    fun i _ ↦ (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hg i))).smul contDiff_const
  obtain ⟨p, R, hp, hpP⟩ :=
    Symbol.exists_isEllipticAbove_and_eventually_coefficient_eq_differentialSymbol k t m hb hk
      (x₀ := x) fun ξ hξ ↦ by
        rw [differentialSymbol_filter_eq, ContinuousLinearMap.isInvertible_smul_iff
          (mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) (hP ξ hξ))]
        exact ⟨ContinuousLinearEquiv.refl ℂ ℂ, rfl⟩
  -- Nested cutoffs `φ`, `ψ`, `χ` around `x`, inside the neighbourhood where all the above holds.
  obtain ⟨φ, ψ, χ, hφx, hψW, hψφ, hχψ⟩ := exists_nested_testFunctions
    (Filter.inter_mem (Filter.inter_mem hU (Ω.isOpen.mem_nhds hxΩ)) hpP)
    (Set.inter_subset_left.trans Set.inter_subset_right)
  have hφψ : tsupport φ ⊆ tsupport ψ := fun y hy ↦
    subset_tsupport _ (by rw [Function.mem_support, hψφ.self_of_nhdsSet y hy]; exact one_ne_zero)
  -- The localized operator `ψ P`, the quantization of a symbol `a` with compact spatial support,
  -- maps `u = χ T` to `ψ (P T) ∈ H^(s - k)`.
  have hb' : ∀ i ∈ t, ContDiff ℝ ∞ fun y ↦ (c i * (ψ y * g i y)) • ContinuousLinearMap.id ℂ ℂ :=
    fun i _ ↦ (contDiff_const.mul (ψ.contDiff.mul
      (Complex.ofRealCLM.contDiff.comp (hg i)))).smul contDiff_const
  have ha := ClassicalSymbol.hasCompactSpatialSupport_toSymbol_ofDifferentialSymbol k t m _ hb' hk
    fun i _ ↦ ψ.hasCompactSupport.mul_right.mul_left.smul_right
  obtain ⟨r, hr⟩ := T.exists_memSobolev_cutoffTempered χ
  have hmem := toDistr_quantizeSobolev_ofDifferentialSymbol_eq_cutoffTempered T hχψ t c hg m hk
    hb' ha _ hr.toBesselPotentialSpace_toDistr ▸ hPT ψ fun _ hy ↦ (hψW hy).1.1
  -- Near the support of `φ`, the symbol `a` is the symbol of `P`, hence that of `p`.
  have hap : ∀ᶠ y in 𝓝ˢ (tsupport φ), ∀ ξ,
      (ClassicalSymbol.ofDifferentialSymbol k t m _ hb' hk).toSymbol.coefficient (y, ξ) =
        p.coefficient (y, ξ) := by
    filter_upwards [hψφ] with y hψy ξ
    have hyW := hψW (subset_tsupport _ (by rw [Function.mem_support, hψy]; exact one_ne_zero))
    rw [hyW.2 ξ, ClassicalSymbol.coefficient_toSymbol_ofDifferentialSymbol]
    simp [differentialSymbol_def, hψy]
  have hreg := hp.memSobolev_smulLeftCLM ha (φ := φ.hasCompactSupport.toSchwartzMap φ.contDiff)
    φ.hasCompactSupport hap hmem
  rw [BesselPotentialSpace.toDistr_smulLeftCLM, hr.toBesselPotentialSpace_toDistr] at hreg
  exact isLocallySobolevAt_iff_exists_memSobolev_cutoffTempered.2
    ⟨φ, hφx, smulLeftCLM_cutoffTempered T (hχψ.filter_mono (nhdsSet_mono hφψ)) ▸ hreg⟩

end Distribution
