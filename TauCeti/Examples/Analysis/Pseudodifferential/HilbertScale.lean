/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.L2
public import TauCeti.Analysis.Pseudodifferential.UniformSobolev

/-!
# Checks for the `L²` mapping of quantizations

Three examples calibrate the Sobolev mapping theorems for pseudodifferential operators on `ℝⁿ` at
the orders `s = m = 0`, where `H^0 = L²`: `TauCeti.Symbol.quantizeSobolev` for symbols with compact
spatial support, and `TauCeti.Symbol.quantizeUniformOrderZero` (Calderón–Vaillancourt) for
symbols whose estimates are uniform in the position.

* **The identity symbol.** The constant symbol `1 = id` is uniform, and its bounded extension to
  `H^0` is the identity (`quantizeUniformOrderZero_const_id`), of operator norm `1` on a nonzero
  fibre (`norm_quantizeUniformOrderZero_const_id`). In positive dimension a nonzero constant symbol
  does not have compact spatial support (`TauCeti.Symbol.not_hasCompactSpatialSupport_const`), so
  here the uniform theorem is needed: compact spatial support is not necessary for `L²`
  boundedness.
* **Multiplication by a compactly supported function.** For a compactly supported smooth
  `f : ℝⁿ → (V →L[ℂ] W)`, the operator `H^0 → H^0` quantizing the symbol `f(x)` has norm at most
  `sup ‖f‖` (`TauCeti.Symbol.norm_quantizeSobolev_ofSpatial_le`). For `f = χ id` with a scalar `χ`
  this operator is multiplication by `χ` (`TauCeti.Symbol.quantizeSobolev_ofSpatial_smul`), of
  norm at most `sup |χ|` (`norm_quantizeSobolev_ofSpatial_smul_id_le`), and `χ = 0` gives the zero
  map (`quantizeSobolev_ofSpatial_smul_id_eq_zero`).
* **Multiplication by a coordinate.** For `T ≠ 0` the symbol `x_j T` satisfies the local estimates
  of order `0`, but not uniformly in the position (`TauCeti.Symbol.not_isUniform_ofSpatial_smul`),
  and its quantization `u ↦ x_j T u` is not bounded on `L²`: no `L²` estimate holds on Schwartz
  functions (`not_exists_eLpNorm_quantizeSchwartzValue_ofSpatial_smul_le`), and no bounded operator
  on `H^0` extends it (`not_exists_quantizeOrderZero_ofSpatial_smul`). The test functions are the
  translates by `k e_j` of a fixed bump, supported in the ball of radius `2`: their `L²` norms do
  not depend on `k`, and multiplication by `x_j` scales them by at least `k - 2`. So the local
  symbol estimates alone give no global `L²` bound, which is why the Calderón–Vaillancourt theorem
  asks for estimates uniform in the position.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3.
-/

public section

noncomputable section

open MeasureTheory TauCeti.Symbol
open scoped ENNReal SchwartzMap BesselPotentialSpace ContDiff

namespace TauCeti.HilbertScaleExample

variable {n : ℕ}

/-! ### Translated bumps -/

section Bump

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A fixed smooth bump on `ℝⁿ`, supported in the ball of radius `2` about the origin and equal to
`1` on the unit ball. -/
private def bump (n : ℕ) : ContDiffBump (0 : CoordinateSpace n) :=
  ⟨1, 2, one_pos, one_lt_two⟩

private theorem contDiff_bump_smul (c : CoordinateSpace n) (v : F) :
    ContDiff ℝ ∞ fun x : CoordinateSpace n ↦ ((bump n (x - c) : ℝ) : ℂ) • v :=
  (Complex.ofRealCLM.contDiff.comp ((bump n).contDiff.comp (contDiff_id.sub contDiff_const))).smul
    contDiff_const

private theorem hasCompactSupport_bump_smul (c : CoordinateSpace n) (v : F) :
    HasCompactSupport fun x : CoordinateSpace n ↦ ((bump n (x - c) : ℝ) : ℂ) • v := by
  have h := ((bump n).hasCompactSupport.comp_homeomorph (Homeomorph.subRight c)).comp_left
    Complex.ofReal_zero
  simp only [Function.comp_def, Homeomorph.subRight_apply] at h
  exact h.smul_right

/-- The translate `x ↦ b(x - c) v` of the bump `b` by `c`, with value `v`, as a Schwartz
function. -/
private def bumpSmul (c : CoordinateSpace n) (v : F) : 𝓢(CoordinateSpace n, F) :=
  (hasCompactSupport_bump_smul c v).toSchwartzMap (contDiff_bump_smul c v)

private theorem bumpSmul_apply (c : CoordinateSpace n) (v : F) (x : CoordinateSpace n) :
    bumpSmul c v x = ((bump n (x - c) : ℝ) : ℂ) • v :=
  HasCompactSupport.toSchwartzMap_toFun _ _ _

private theorem hasCompactSupport_bumpSmul (c : CoordinateSpace n) (v : F) :
    HasCompactSupport (bumpSmul c v) := by
  rw [funext (bumpSmul_apply c v)]
  exact hasCompactSupport_bump_smul c v

/-- The translates of `x ↦ r b(x)` all have the same `L²` norm. -/
private theorem eLpNorm_bump_sub (c : CoordinateSpace n) (r : ℝ) :
    eLpNorm (fun x : CoordinateSpace n ↦ r * bump n (x - c)) 2 volume =
      ‖r‖ₑ * eLpNorm (bump n) 2 volume := by
  have h : (fun x : CoordinateSpace n ↦ r * bump n (x - c)) = r • ((bump n) ∘ (· - c)) := by
    ext x
    simp
  rw [h, eLpNorm_const_smul, eLpNorm_comp_measurePreserving (bump n).continuous.aestronglyMeasurable
      (measurePreserving_sub_right volume c)]

private theorem eLpNorm_bumpSmul (c : CoordinateSpace n) (v : F) :
    eLpNorm (bumpSmul c v) 2 volume = ‖v‖ₑ * eLpNorm (bump n) 2 volume := by
  rw [← eNorm_norm v, ← eLpNorm_bump_sub c ‖v‖]
  refine eLpNorm_congr_norm_ae (bumpSmul c v).continuous.aestronglyMeasurable
    (continuous_const.mul ((bump n).continuous.comp
      (continuous_id.sub continuous_const))).aestronglyMeasurable (.of_forall fun x ↦ ?_)
  simp [bumpSmul_apply, norm_smul, mul_comm]

private theorem eLpNorm_bump_pos : 0 < eLpNorm (bump n) 2 volume := by
  refine pos_iff_ne_zero.2 fun h ↦ ?_
  rw [eLpNorm_eq_zero_iff two_ne_zero] at h
  have h0 := congrFun (((bump n).continuous.ae_eq_iff_eq volume continuous_const).1 h) 0
  rw [(bump n).one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)] at h0
  exact absurd h0 one_ne_zero

private theorem eLpNorm_bump_ne_top : eLpNorm (bump n) 2 volume ≠ ⊤ := by
  have h := ((bumpSmul (0 : CoordinateSpace n) (1 : ℂ)).memLp 2).eLpNorm_ne_top
  rwa [eLpNorm_bumpSmul, eNorm_one, one_mul] at h

/-- On the support of the translate of the bump by `k e_j`, the coordinate `x_j` exceeds
`k - 2`. -/
private theorem sub_two_mul_le_abs_mul (j : Fin n) (k : ℝ) (x : CoordinateSpace n) :
    (k - 2) * |bump n (x - EuclideanSpace.single j k)| ≤
      |x j| * |bump n (x - EuclideanSpace.single j k)| := by
  rcases eq_or_ne (bump n (x - EuclideanSpace.single j k)) 0 with h | h
  · rw [h, abs_zero, mul_zero, mul_zero]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have hx : x - EuclideanSpace.single j k ∈ Metric.ball (0 : CoordinateSpace n) (bump n).rOut := by
    rw [← (bump n).support_eq]
    exact h
  have hr : (bump n).rOut = 2 := rfl
  rw [mem_ball_zero_iff, hr] at hx
  have hj := (PiLp.norm_apply_le (x - EuclideanSpace.single j k) j).trans_lt hx
  simp only [PiLp.sub_apply, EuclideanSpace.single, PiLp.single_apply, ite_true,
    Real.norm_eq_abs] at hj
  linarith [abs_lt.1 hj, le_abs_self (x j)]

end Bump

section L2

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-! ### The identity symbol -/

/-- **The identity symbol quantizes to the identity on `L²`.** The constant symbol `1 = id` is
uniform of order `0`, and the bounded extension of its quantization to `H^0 = L²` is the
identity. -/
theorem quantizeUniformOrderZero_const_id :
    (const (ContinuousLinearMap.id ℂ V) : Symbol n V V 0).quantizeUniformOrderZero
      (isUniform_const _) = ContinuousLinearMap.id ℂ _ := by
  have hC := (isUniform_const (ContinuousLinearMap.id ℂ V) :
    (const _ : Symbol n V V 0).IsUniform).exists_eLpNorm_quantizeSchwartzValue_le
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
  rw [quantizeUniformOrderZero_toBesselPotentialSpaceCLM _ hC, ContinuousLinearMap.id_apply]
  congr 1
  ext x
  rw [quantizeUniformCLM_apply, quantizeSchwartzValue_const, ContinuousLinearMap.id_apply]

/-- **The identity symbol has operator norm `1` on `L²`**, on a nonzero fibre. -/
theorem norm_quantizeUniformOrderZero_const_id [Nontrivial V] :
    ‖(const (ContinuousLinearMap.id ℂ V) : Symbol n V V 0).quantizeUniformOrderZero
      (isUniform_const _)‖ = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hu : ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 (bumpSmul (0 : CoordinateSpace n) v)‖ ≠
      0 := by
    rw [SchwartzMap.norm_toBesselPotentialSpaceCLM_zero, eLpNorm_bumpSmul]
    exact ENNReal.toReal_ne_zero.2 ⟨mul_ne_zero (eNorm_ne_zero.2 hv) eLpNorm_bump_pos.ne',
      ENNReal.mul_ne_top eNorm_ne_top eLpNorm_bump_ne_top⟩
  have : Nontrivial H^{0}(CoordinateSpace n, V) :=
    ⟨⟨SchwartzMap.toBesselPotentialSpaceCLM 0 2 (bumpSmul (0 : CoordinateSpace n) v), 0,
      fun h ↦ hu (by rw [h, norm_zero])⟩⟩
  rw [quantizeUniformOrderZero_const_id, ContinuousLinearMap.norm_id]

/-! ### Multiplication by a compactly supported function -/

/-- **Multiplication by a compactly supported scalar function on `L²`.** For a compactly
supported Schwartz function `χ` with `|χ| ≤ C`, the quantization of the symbol `χ(x)`, which is
multiplication by `χ` (`TauCeti.Symbol.quantizeSobolev_ofSpatial_smul`), has norm at most `C` as
an operator `H^0 → H^0`. -/
theorem norm_quantizeSobolev_ofSpatial_smul_id_le {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : ContDiff ℝ ∞ fun x ↦ χ x • ContinuousLinearMap.id ℂ V)
    (h : (ofSpatial (fun x ↦ χ x • ContinuousLinearMap.id ℂ V) hχ).HasCompactSpatialSupport)
    {C : ℝ} (hC : ∀ x, ‖χ x‖ ≤ C) :
    ‖(ofSpatial (fun x ↦ χ x • ContinuousLinearMap.id ℂ V) hχ).quantizeSobolev h 0‖ ≤ C :=
  norm_quantizeSobolev_ofSpatial_le hχ h fun x ↦
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (χ x)) fun v ↦ by
      rw [smul_apply, ContinuousLinearMap.id_apply, norm_smul]).trans (hC x)

/-- **The zero cutoff gives the zero map.** The symbol `χ(x)` with `χ = 0` quantizes to the zero
operator on `L²`. -/
theorem quantizeSobolev_ofSpatial_smul_id_eq_zero
    (hχ : ContDiff ℝ ∞ fun x ↦ (0 : 𝓢(CoordinateSpace n, ℂ)) x • ContinuousLinearMap.id ℂ V)
    (h : (ofSpatial (fun x ↦ (0 : 𝓢(CoordinateSpace n, ℂ)) x • ContinuousLinearMap.id ℂ V)
      hχ).HasCompactSpatialSupport) :
    (ofSpatial _ hχ).quantizeSobolev h 0 = 0 :=
  norm_le_zero_iff.1 (norm_quantizeSobolev_ofSpatial_smul_id_le hχ h fun x ↦ by simp)

end L2

/-! ### Multiplication by a coordinate -/

section Coordinate

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] (j : Fin n) {T : V →L[ℂ] W}

/-- For every `C`, a translated bump `u` violates the estimate `‖x_j T u‖_{L²} ≤ C ‖u‖_{L²}`. -/
private theorem exists_lt_eLpNorm_smul (hT : T ≠ 0) (C : ℝ) :
    ∃ u : 𝓢(CoordinateSpace n, V), HasCompactSupport u ∧
      ENNReal.ofReal C * eLpNorm u 2 volume <
        eLpNorm (fun x : CoordinateSpace n ↦ x j • T (u x)) 2 volume := by
  obtain ⟨v, hv⟩ : ∃ v, T v ≠ 0 := by
    by_contra! h
    exact hT (ContinuousLinearMap.ext h)
  have hTv : 0 < ‖T v‖ := norm_pos_iff.2 hv
  -- Translate the bump by `k e_j` for `k - 2 > |C| ‖v‖ / ‖T v‖`.
  obtain ⟨k, hk⟩ := exists_nat_gt (|C| * ‖v‖ / ‖T v‖ + 2)
  have hk₂ : |C| * ‖v‖ < (k - 2) * ‖T v‖ := by
    rw [← lt_sub_iff_add_lt, div_lt_iff₀ hTv] at hk
    exact hk
  have hk₀ : 0 ≤ (k : ℝ) - 2 :=
    nonneg_of_mul_nonneg_left ((by positivity : 0 ≤ |C| * ‖v‖).trans hk₂.le) hTv
  set c : CoordinateSpace n := EuclideanSpace.single j (k : ℝ)
  refine ⟨bumpSmul c v, hasCompactSupport_bumpSmul c v, ?_⟩
  -- Pointwise `(k - 2) ‖T v‖ |b(x - c)| ≤ ‖x_j T u(x)‖`, which integrates to an `L²` bound.
  have hlow : eLpNorm (fun x ↦ ((k - 2) * ‖T v‖) * bump n (x - c)) 2 volume ≤
      eLpNorm (fun x : CoordinateSpace n ↦ x j • T (bumpSmul c v x)) 2 volume := by
    refine eLpNorm_mono (continuous_const.mul ((bump n).continuous.comp
      (continuous_id.sub continuous_const))).aestronglyMeasurable fun x ↦ ?_
    simp only [bumpSmul_apply, map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hk₀, abs_norm]
    nlinarith [sub_two_mul_le_abs_mul j k x, norm_nonneg (T v), abs_nonneg (bump n (x - c))]
  refine lt_of_lt_of_le ?_ hlow
  rw [eLpNorm_bumpSmul, eLpNorm_bump_sub, ← mul_assoc,
    Real.eNorm_eq_ofReal (mul_nonneg hk₀ (norm_nonneg _)), ← ofReal_norm]
  refine ENNReal.mul_lt_mul_left eLpNorm_bump_pos.ne' eLpNorm_bump_ne_top ?_
  calc ENNReal.ofReal C * ENNReal.ofReal ‖v‖ ≤ ENNReal.ofReal (|C| * ‖v‖) := by
        rw [ENNReal.ofReal_mul (abs_nonneg C)]
        gcongr
        exact le_abs_self C
    _ < ENNReal.ofReal ((k - 2) * ‖T v‖) :=
        (ENNReal.ofReal_lt_ofReal_iff ((by positivity : 0 ≤ |C| * ‖v‖).trans_lt hk₂)).2 hk₂

/-- **Multiplication by a coordinate admits no `L²` estimate.** For `T ≠ 0` the symbol `x_j T` of
order `0`, which satisfies the local symbol estimates but not uniformly in the position, admits no
estimate `‖Op(x_j T) u‖_{L²} ≤ C ‖u‖_{L²}` on Schwartz functions. -/
theorem not_exists_eLpNorm_quantizeSchwartzValue_ofSpatial_smul_le [CompleteSpace V]
    [CompleteSpace W] (hT : T ≠ 0)
    (hf : ContDiff ℝ ∞ fun x : CoordinateSpace n ↦ x j • T) :
    ¬∃ C : ℝ, ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue (ofSpatial _ hf).coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume := by
  rintro ⟨C, hC⟩
  obtain ⟨u, -, hu⟩ := exists_lt_eLpNorm_smul j hT C
  rw [← funext fun x ↦ (quantizeSchwartzValue_ofSpatial _ hf u x).trans
    (smul_apply _ _ _)] at hu
  exact (hC u).not_gt hu

end Coordinate

section CoordinateL2

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] (j : Fin n) {T : V →L[ℂ] W}

/-- **Multiplication by a coordinate is not bounded on `L²`.** For `T ≠ 0`, no bounded operator
on `H^0 = L²` agrees with the quantization of the symbol `x_j T` on Schwartz functions, in contrast
with symbols that have compact spatial support (`TauCeti.Symbol.exists_quantizeSobolev`) or
estimates uniform in the position (`TauCeti.Symbol.exists_quantizeUniformOrderZero`). -/
theorem not_exists_quantizeOrderZero_ofSpatial_smul (hT : T ≠ 0)
    (hf : ContDiff ℝ ∞ fun x : CoordinateSpace n ↦ x j • T) :
    ¬∃ A : H^{0}(CoordinateSpace n, V) →L[ℂ] H^{0}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (A (SchwartzMap.toBesselPotentialSpaceCLM 0 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue (ofSpatial _ hf).coefficient u x := by
  rintro ⟨A, hA⟩
  obtain ⟨u, hu, hlt⟩ := exists_lt_eLpNorm_smul j hT ‖A‖
  -- On the compactly supported `u`, the output `x_j T u` is again a Schwartz function `w`.
  have hw : HasCompactSupport fun x : CoordinateSpace n ↦ x j • T (u x) :=
    hu.mono fun x hx h ↦ hx (by simp [h])
  have hwc : ContDiff ℝ ∞ fun x : CoordinateSpace n ↦ x j • T (u x) :=
    (EuclideanSpace.proj j).contDiff.smul ((T.restrictScalars ℝ).contDiff.comp (u.smooth ⊤))
  set w : 𝓢(CoordinateSpace n, W) := hw.toSchwartzMap hwc
  have hwx (x : CoordinateSpace n) : w x = x j • T (u x) :=
    HasCompactSupport.toSchwartzMap_toFun _ _ _
  have hAu : A (SchwartzMap.toBesselPotentialSpaceCLM 0 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM 0 2 w := by
    refine BesselPotentialSpace.ext ?_
    ext φ
    rw [hA, SchwartzMap.toDistr_toBesselPotentialSpaceCLM, SchwartzMap.coe_apply]
    simp only [quantizeSchwartzValue_ofSpatial, smul_apply, hwx]
  refine (SchwartzMap.eLpNorm_le_of_toBesselPotentialSpaceCLM_eq hAu).not_gt ?_
  simpa only [← hwx] using hlt

end CoordinateL2

end TauCeti.HilbertScaleExample
