/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import TauCeti.Analysis.InnerProductSpace.LyapunovForm
public import TauCeti.Analysis.ODE.EnergyEstimate.Fredholm

/-!
# The trajectory operator with hyperbolic limits

Let `A : ℝ → End(E)` be a continuous family of operators on a finite-dimensional real inner product
space `E`, with limits `A±` at `±∞` that have Lyapunov forms
(`ContinuousLinearMap.HasLyapunovForm`): there are symmetric `S±` and `c > 0` with
`c ‖v‖² ≤ ⟪S± (A± v), v⟫`. By the inertia theorem this says exactly that `A±` are hyperbolic, with
no eigenvalue on the imaginary axis; only the easy half of that equivalence is formalized, in
`TauCeti.Analysis.InnerProductSpace.LyapunovForm`. This file proves
that the trajectory operator

`D_A u = u' + A u : W^{1,2}(ℝ, E) → L²(ℝ, E)`

(`TauCeti.WeakDerivStep.trajectoryOperator`, for an `L∞` class of `A`) is a Fredholm operator, with
index `dim ker D_A - dim ker D_{-A†}`. Neither symmetry of `A` nor any derivative of `A` is
assumed. A symmetric operator bounded below has the Lyapunov form `S = A`
(`ContinuousLinearMap.hasLyapunovForm_of_isSymmetric`), and a limit of symmetric operators is
symmetric (`ContinuousLinearMap.hasLyapunovForm_of_tendsto_of_isSymmetric`), so this applies in
particular to every continuous family of symmetric operators with invertible limits.

The estimate behind the theorem replaces the energy identity of the symmetric case by the
monotonicity of a quadratic form. For a `C¹` family `S(s)` of symmetric operators and a compactly
supported `C¹` path `u`, integrating the derivative of `⟪S u, u⟫` gives

`∫ ⟪S (u' + A u), u⟫ = ∫ ⟪S A u, u⟫ - ½ ∫ ⟪S' u, u⟫`

(`TauCeti.integral_inner_apply_deriv_add_eq`). Interpolating between `S-` and `S+` across a
bounded interval `[-R, R]`, the right side controls `∫ ‖u‖²` up to an error supported in
`[-R, R]`, while the left side is at most `‖S‖ ‖u' + A u‖ ‖u‖`. This gives the estimate

`‖u‖²_{W^{1,2}} ≤ C ‖D_A u‖²_{L²} + C ‖u‖²_{L²(-R, R)}`

first on test paths and then, by density, on `W^{1,2}(ℝ, E)`. Restriction to a bounded interval is
compact, so Peetre's lemma gives a finite-dimensional kernel and a closed range. The cokernel is the
orthogonal complement of the range, which lies in the kernel of the formal adjoint
`D_{-A†} = d/ds - A†` (`TauCeti.WeakDerivStep.orthogonal_range_trajectoryOperator_le_map_ker`). The
family `-A†` has limits `-A±†`, which again have Lyapunov forms
(`ContinuousLinearMap.HasLyapunovForm.neg_adjoint`), so that kernel is finite dimensional too.

## Main declarations

* `exists_pos_nonneg_forall_integral_norm_deriv_sq_add_integral_norm_sq_le_of_hasLyapunovForm`, in
  the namespace `TauCeti`: the estimate with an interior error on compactly supported `C¹` paths.
* `TauCeti.WeakDerivStep.exists_norm_sq_le_mul_norm_trajectoryOperator_sq_add_of_hasLyapunovForm`:
  the estimate on `W^{1,2}(ℝ, E)`.
* `TauCeti.WeakDerivStep.finiteDimensional_ker_trajectoryOperator_of_hasLyapunovForm` and
  `TauCeti.WeakDerivStep.isClosed_range_trajectoryOperator_of_hasLyapunovForm`: the kernel of
  `D_A` is finite dimensional and its range is closed.
* `TauCeti.WeakDerivStep.finiteDimensional_coker_trajectoryOperator_of_hasLyapunovForm`: the
  cokernel of `D_A` is finite dimensional.
* `TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_of_hasLyapunovForm`: `D_A` is Fredholm.
* `TauCeti.WeakDerivStep.index_trajectoryOperator_of_hasLyapunovForm`: its index is
  `dim ker D_A - dim ker D_{-A†}`.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, §3 (the operator `d/ds + A(s)` with hyperbolic limits).
* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 2 (the Fredholm property of linearized
  trajectory operators).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.1
  (estimates with a compact error and the Fredholm criterion).
-/

public section

open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A S : ℝ → E →L[ℝ] E} {u : ℝ → E}

/-! ### Estimates on test paths -/

/-- The estimate given by a family of quadratic forms: if `⟪S A v, v⟫ - ½ ⟪S' v, v⟫` is at least
`c ‖v‖²` outside a set `I` and at least `-K ‖v‖²` on `I`, and `‖S‖ ≤ M`, then
`c/2 ∫ ‖u‖² ≤ M²/(2c) ∫ ‖u' + A u‖² + (K + c) ∫_I ‖u‖²`. -/
private theorem half_mul_integral_norm_sq_le (hS : ContDiff ℝ 1 S)
    (hsym : ∀ s, (S s : E →ₗ[ℝ] E).IsSymmetric) (hA : Continuous A) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) {I : Set ℝ} (hI : MeasurableSet I) {c M K : ℝ} (hc0 : 0 < c)
    (hM : ∀ s, ‖S s‖ ≤ M)
    (hout : ∀ s ∉ I, ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S s (A s v), v⟫_ℝ - ⟪deriv S s v, v⟫_ℝ / 2)
    (hin : ∀ s ∈ I, ∀ v, -K * ‖v‖ ^ 2 ≤ ⟪S s (A s v), v⟫_ℝ - ⟪deriv S s v, v⟫_ℝ / 2) :
    c / 2 * ∫ s, ‖u s‖ ^ 2 ≤
      M ^ 2 / (2 * c) * (∫ s, ‖deriv u s + A s (u s)‖ ^ 2) + (K + c) * ∫ s in I, ‖u s‖ ^ 2 := by
  have hiu := integrable_norm_sq_of_hasCompactSupport hu.continuous hc
  have hcD : HasCompactSupport fun s ↦ deriv u s + A s (u s) :=
    hc.deriv.add (hc.mono fun s hs hu0 ↦ hs (by simp [hu0]))
  have hiDu := integrable_norm_sq_of_hasCompactSupport (w := fun s ↦ deriv u s + A s (u s))
    (hu.continuous_deriv_one.add (hA.clm_apply hu.continuous)) hcD
  have hiI : Integrable fun s ↦ I.indicator (fun s ↦ ‖u s‖ ^ 2) s := hiu.indicator hI
  have hiA := integrable_inner_apply_of_hasCompactSupport hS.continuous
    (hA.clm_apply hu.continuous) hu.continuous hc
  have hiS := integrable_inner_apply_of_hasCompactSupport hS.continuous_deriv_one hu.continuous
    hu.continuous hc
  have hiSD := integrable_inner_apply_of_hasCompactSupport (w := fun s ↦ deriv u s + A s (u s))
    hS.continuous (hu.continuous_deriv_one.add (hA.clm_apply hu.continuous)) hu.continuous hc
  -- Pointwise lower bound for the right side of the integration-by-parts identity.
  have hlow (s : ℝ) : c * ‖u s‖ ^ 2 - (K + c) * I.indicator (fun s ↦ ‖u s‖ ^ 2) s ≤
      ⟪S s (A s (u s)), u s⟫_ℝ - ⟪deriv S s (u s), u s⟫_ℝ / 2 := by
    by_cases hs : s ∈ I
    · rw [indicator_of_mem hs]
      linarith [hin s hs (u s)]
    · rw [indicator_of_notMem hs, mul_zero, sub_zero]
      exact hout s hs (u s)
  -- Pointwise upper bound for the left side, by Cauchy–Schwarz and `2ab ≤ a² + b²`.
  have hup (s : ℝ) : ⟪S s (deriv u s + A s (u s)), u s⟫_ℝ ≤
      c / 2 * ‖u s‖ ^ 2 + M ^ 2 / (2 * c) * ‖deriv u s + A s (u s)‖ ^ 2 := by
    set w := deriv u s + A s (u s)
    have h₁ : ⟪S s w, u s⟫_ℝ ≤ M * ‖w‖ * ‖u s‖ :=
      (real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right ((S s).le_of_opNorm_le (hM s) w) (norm_nonneg _))
    have h₂ : 2 * c * (c / 2 * ‖u s‖ ^ 2 + M ^ 2 / (2 * c) * ‖w‖ ^ 2) =
        c ^ 2 * ‖u s‖ ^ 2 + M ^ 2 * ‖w‖ ^ 2 := by
      field_simp
    refine h₁.trans (le_of_mul_le_mul_left ?_ (by positivity : 0 < 2 * c))
    rw [h₂]
    nlinarith [sq_nonneg (c * ‖u s‖ - M * ‖w‖)]
  have hL := integral_mono ((hiu.const_mul c).sub (hiI.const_mul (K + c)))
    (hiA.sub (hiS.div_const 2)) hlow
  have hU := integral_mono hiSD ((hiu.const_mul (c / 2)).add (hiDu.const_mul _)) hup
  simp only [Pi.sub_apply, Pi.add_apply] at hL hU
  rw [integral_sub (hiu.const_mul c) (hiI.const_mul (K + c)), integral_const_mul,
    integral_const_mul, integral_indicator hI, integral_sub hiA (hiS.div_const 2),
    integral_div] at hL
  rw [integral_add (hiu.const_mul (c / 2)) (hiDu.const_mul _), integral_const_mul,
    integral_const_mul, integral_inner_apply_deriv_add_eq hS hsym hA hu hc] at hU
  linarith

/-- A `C¹` family of symmetric operators equal to `Sm` on `(-∞, -R]` and to `Sp` on `[R, ∞)`, with
norm at most `‖Sm‖ + ‖Sp - Sm‖`. It interpolates through `Real.smoothTransition`. -/
private theorem exists_contDiff_isSymmetric_interpolation {Sm Sp : E →L[ℝ] E}
    (hSm : (Sm : E →ₗ[ℝ] E).IsSymmetric) (hSp : (Sp : E →ₗ[ℝ] E).IsSymmetric) {R : ℝ}
    (hR : 0 < R) :
    ∃ S : ℝ → E →L[ℝ] E, ContDiff ℝ 1 S ∧ (∀ s, (S s : E →ₗ[ℝ] E).IsSymmetric) ∧
      (∀ s ≤ -R, S s = Sm) ∧ (∀ s, R ≤ s → S s = Sp) ∧
      (∀ s ∉ Icc (-R) R, deriv S s = 0) ∧ ∀ s, ‖S s‖ ≤ ‖Sm‖ + ‖Sp - Sm‖ := by
  set σ : ℝ → ℝ := fun s ↦ Real.smoothTransition ((s + R) / (2 * R))
  set S : ℝ → E →L[ℝ] E := fun s ↦ Sm + σ s • (Sp - Sm)
  have hSbot (s : ℝ) (hs : s ≤ -R) : S s = Sm := by
    have : σ s = 0 := Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
    simp [S, this]
  have hStop (s : ℝ) (hs : R ≤ s) : S s = Sp := by
    have : σ s = 1 := Real.smoothTransition.one_of_one_le
      (by rw [le_div_iff₀ (by positivity)]; linarith)
    simp [S, this]
  refine ⟨S, contDiff_const.add
    ((Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const _)).smul
      contDiff_const), fun s x y ↦ ?_, hSbot, hStop, fun s hs ↦ ?_, fun s ↦ ?_⟩
  · simp only [S, ContinuousLinearMap.coe_coe, add_apply, smul_apply, sub_apply, inner_add_left,
      inner_add_right, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
      hSm.apply_clm, hSp.apply_clm, RCLike.conj_to_real]
  · -- Off `[-R, R]` the family is locally constant.
    rcases lt_or_ge s (-R) with h | h
    · have : S =ᶠ[𝓝 s] fun _ ↦ Sm := by
        filter_upwards [Iio_mem_nhds h] with t ht using hSbot t ht.le
      rw [this.deriv_eq, deriv_const]
    · have h' : R < s := lt_of_not_ge fun h' ↦ hs ⟨h, h'⟩
      have : S =ᶠ[𝓝 s] fun _ ↦ Sp := by
        filter_upwards [Ioi_mem_nhds h'] with t ht using hStop t ht.le
      rw [this.deriv_eq, deriv_const]
  · refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
    rw [norm_smul, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one _)

/-- The derivative of a compactly supported `C¹` path is controlled by `u' + A u` and `u`:
`∫ ‖u'‖² ≤ 2 ∫ ‖u' + A u‖² + 2 M² ∫ ‖u‖²` when `‖A s‖ ≤ M` everywhere. -/
private theorem integral_norm_deriv_sq_le (hA : Continuous A) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) {M : ℝ} (hM : ∀ s, ‖A s‖ ≤ M) :
    ∫ s, ‖deriv u s‖ ^ 2 ≤
      2 * (∫ s, ‖deriv u s + A s (u s)‖ ^ 2) + 2 * M ^ 2 * ∫ s, ‖u s‖ ^ 2 := by
  have hiu := integrable_norm_sq_of_hasCompactSupport hu.continuous hc
  have hiDu := integrable_norm_sq_of_hasCompactSupport (w := fun s ↦ deriv u s + A s (u s))
    (hu.continuous_deriv_one.add (hA.clm_apply hu.continuous))
    (hc.deriv.add (hc.mono fun s hs hu0 ↦ hs (by simp [hu0])))
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hiDu.const_mul 2)
    (hiu.const_mul _)]
  refine integral_mono (integrable_norm_sq_of_hasCompactSupport hu.continuous_deriv_one hc.deriv)
    ((hiDu.const_mul 2).add (hiu.const_mul _)) fun s ↦ ?_
  have h₁ : ‖deriv u s‖ ≤ ‖deriv u s + A s (u s)‖ + M * ‖u s‖ := by
    calc ‖deriv u s‖ = ‖(deriv u s + A s (u s)) - A s (u s)‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖deriv u s + A s (u s)‖ + ‖A s (u s)‖ := norm_sub_le _ _
      _ ≤ ‖deriv u s + A s (u s)‖ + M * ‖u s‖ := by
          gcongr
          exact (A s).le_of_opNorm_le (hM s) (u s)
  have h₂ := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
  nlinarith [sq_nonneg (‖deriv u s + A s (u s)‖ - M * ‖u s‖)]

/-- The quadratic form `⟪S (A v), v⟫ - ½ ⟪D v, v⟫` is at least `-(‖S‖ ‖A‖ + ‖D‖ / 2) ‖v‖²`. -/
private theorem neg_mul_norm_sq_le_inner_sub (S A D : E →L[ℝ] E) (v : E) :
    -((‖S‖ * ‖A‖ + ‖D‖ / 2) * ‖v‖ ^ 2) ≤ ⟪S (A v), v⟫_ℝ - ⟪D v, v⟫_ℝ / 2 := by
  have h₁ := neg_le_of_abs_le (S.abs_inner_apply_apply_le A v)
  have h₂ := le_of_abs_le (D.abs_inner_apply_le v)
  linarith

/-- The arithmetic combining the estimates for `Y = ∫ ‖u‖²` and `X = ∫ ‖u'‖²` in terms of
`Z = ∫ ‖u' + A u‖²` and `W = ∫_{[-R, R]} ‖u‖²`. -/
private theorem add_le_mul_add_mul {X Y Z W a b c m : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hZ : 0 ≤ Z) (hW : 0 ≤ W) (hY : c / 2 * Y ≤ a * Z + b * W)
    (hX : X ≤ 2 * Z + 2 * m ^ 2 * Y) :
    X + Y ≤ (2 + (2 * m ^ 2 + 1) * (2 / c) * (a + b)) * Z +
      (2 + (2 * m ^ 2 + 1) * (2 / c) * (a + b)) * W := by
  have hY' : Y ≤ 2 / c * (a * Z + b * W) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    linarith
  set k := (2 * m ^ 2 + 1) * (2 / c)
  have hk : 0 ≤ k := by positivity
  have h₁ : k * (a * Z) ≤ k * ((a + b) * Z) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hZ) hk
  have h₂ : k * (b * W) ≤ k * ((a + b) * W) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hW) hk
  have h₃ : (2 * m ^ 2 + 1) * Y ≤ (2 * m ^ 2 + 1) * (2 / c * (a * Z + b * W)) :=
    mul_le_mul_of_nonneg_left hY' (by positivity)
  have h₄ : (2 * m ^ 2 + 1) * (2 / c * (a * Z + b * W)) = k * (a * Z) + k * (b * W) := by
    ring
  have h₅ : (2 + k * (a + b)) * Z + (2 + k * (a + b)) * W =
      2 * Z + 2 * W + k * ((a + b) * Z) + k * ((a + b) * W) := by
    ring
  rw [h₅]
  nlinarith

/-- **The trajectory estimate for hyperbolic limits on test paths.** Let `A` be a continuous
family of operators whose limits `A±` at `±∞` have Lyapunov forms. Then there are `R > 0` and
`C ≥ 0` with

`∫ ‖u'‖² + ∫ ‖u‖² ≤ C ∫ ‖u' + A u‖² + C ∫_{[-R, R]} ‖u‖²`

for every compactly supported `C¹` path `u`. -/
theorem exists_pos_nonneg_forall_integral_norm_deriv_sq_add_integral_norm_sq_le_of_hasLyapunovForm
    (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus)) :
    ∃ R > 0, ∃ C ≥ 0, ∀ u : ℝ → E, ContDiff ℝ 1 u → HasCompactSupport u →
      (∫ s, ‖deriv u s‖ ^ 2) + (∫ s, ‖u s‖ ^ 2) ≤
        C * (∫ s, ‖deriv u s + A s (u s)‖ ^ 2) + C * ∫ s in Icc (-R) R, ‖u s‖ ^ 2 := by
  obtain ⟨Sm, hSm, cm, hcm, hm⟩ := hminus.exists_eventually_nhds
  obtain ⟨Sp, hSp, cp, hcp, hp⟩ := hplus.exists_eventually_nhds
  -- Outside `[-R, R]`, `A s` satisfies the Lyapunov inequality of the nearby limit and has
  -- bounded norm.
  obtain ⟨a, ha⟩ := eventually_atBot.mp ((hbot.eventually hm).and
    (hbot.norm.eventually (Iic_mem_nhds (lt_add_one ‖Aminus‖))))
  obtain ⟨b, hb⟩ := eventually_atTop.mp ((htop.eventually hp).and
    (htop.norm.eventually (Iic_mem_nhds (lt_add_one ‖Aplus‖))))
  set R := max (max (-a) b) 1
  have hRa : -R ≤ a := by linarith [le_max_left (-a) b, le_max_left (max (-a) b) 1]
  have hRb : b ≤ R := by linarith [le_max_right (-a) b, le_max_left (max (-a) b) 1]
  have hR : 0 < R := by linarith [le_max_right (max (-a) b) 1]
  -- The family of quadratic forms passes from `Sm` to `Sp` across `[-R, R]`.
  obtain ⟨S, hS, hsym, hSbot, hStop, hdS, hM⟩ :=
    exists_contDiff_isSymmetric_interpolation hSm hSp hR
  -- On `[-R, R]` the error term `⟪S A v, v⟫ - ½ ⟪S' v, v⟫` is bounded below by `-K ‖v‖²`.
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    (f := fun s ↦ ‖S s‖ * ‖A s‖ + ‖deriv S s‖ / 2)
    ((hS.continuous.norm.mul hA.norm).add (hS.continuous_deriv_one.norm.div_const 2)).continuousOn
  have hK' (s : ℝ) (hs : s ∈ Icc (-R) R) : ‖S s‖ * ‖A s‖ + ‖deriv S s‖ / 2 ≤ K :=
    (Real.le_norm_self _).trans (hK s hs)
  have hK₀ : 0 ≤ K := (by positivity : (0 : ℝ) ≤ ‖S 0‖ * ‖A 0‖ + ‖deriv S 0‖ / 2).trans
    (hK' 0 ⟨by linarith, by linarith⟩)
  -- A uniform bound on `A`.
  obtain ⟨KA, hKA⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hA.continuousOn
  set MA := max KA (max (‖Aminus‖ + 1) (‖Aplus‖ + 1))
  have hMA (s : ℝ) : ‖A s‖ ≤ MA := by
    rcases lt_or_ge s (-R) with hs | hs
    · exact (mem_Iic.mp (ha s (by linarith)).2).trans (le_max_of_le_right (le_max_left _ _))
    rcases le_or_gt s R with hs' | hs'
    · exact (hKA s ⟨hs, hs'⟩).trans (le_max_left _ _)
    · exact (mem_Iic.mp (hb s (by linarith)).2).trans (le_max_of_le_right (le_max_right _ _))
  set c := min cm cp
  have hc : 0 < c := lt_min hcm hcp
  refine ⟨R, hR, 2 + (2 * MA ^ 2 + 1) * (2 / c) * ((‖Sm‖ + ‖Sp - Sm‖) ^ 2 / (2 * c) + (K + c)),
    by positivity, fun u hu hcu ↦ ?_⟩
  have hY := half_mul_integral_norm_sq_le hS hsym hA hu hcu measurableSet_Icc hc hM
    (I := Icc (-R) R) (K := K) (fun s hs v ↦ by
      rw [hdS s hs, zero_apply, inner_zero_left, zero_div, sub_zero]
      rcases lt_or_ge s (-R) with h₁ | h₁
      · rw [hSbot s h₁.le]
        exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans
          ((ha s (by linarith)).1 v)
      · have h₂ : R < s := lt_of_not_ge fun h ↦ hs ⟨h₁, h⟩
        rw [hStop s h₂.le]
        exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans
          ((hb s (by linarith)).1 v))
    (fun s hs v ↦ by
      have := mul_le_mul_of_nonneg_right (hK' s hs) (sq_nonneg ‖v‖)
      linarith [neg_mul_norm_sq_le_inner_sub (S s) (A s) (deriv S s) v])
  exact add_le_mul_add_mul hc (by positivity) (by positivity)
    (integral_nonneg fun _ ↦ by positivity)
    (setIntegral_nonneg measurableSet_Icc fun _ _ ↦ by positivity) hY
    (integral_norm_deriv_sq_le hA hu hcu hMA)

end TauCeti

/-! ### The trajectory operator on Sobolev paths -/

namespace TauCeti.WeakDerivStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : ℝ → E →L[ℝ] E}

/-- **The trajectory estimate for hyperbolic limits on Sobolev paths.** Let `A` be a continuous
family of operators whose limits at `±∞` have Lyapunov forms. Then the trajectory operator
satisfies `‖u‖² ≤ C ‖D_A u‖² + C ‖u‖²_{L²(-R, R)}` on `W^{1,2}(ℝ, E)`. The coefficient of the
operator is any `L∞` class `AL` of `A`. -/
theorem exists_norm_sq_le_mul_norm_trajectoryOperator_sq_add_of_hasLyapunovForm
    (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    ∃ R > 0, ∃ C ≥ 0, ∀ u : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      ‖u‖ ^ 2 ≤ C * ‖trajectoryOperator AL u‖ ^ 2 +
        C * ‖restrictBaseL _ (V := ⟨Ioo (-R) R, isOpen_Ioo⟩) le_top u‖ ^ 2 := by
  obtain ⟨R, hR, C, hC, hest⟩ :=
    exists_pos_nonneg_forall_integral_norm_deriv_sq_add_integral_norm_sq_le_of_hasLyapunovForm hA
      hminus hplus hbot htop
  refine ⟨R + 1, by linarith, C, hC, fun u ↦ ?_⟩
  have := mul_norm_weakFDeriv_sq_add_mul_norm_prev_sq_le_of_forall_contDiff AL hAL (a := 1)
    (b := 1) (c := C) hC (lt_add_one R) (fun φ hφ hφc ↦ by simpa using hest φ hφ hφc) u
  rw [norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq]
  linarith

/-- The trajectory estimate in the form of Peetre's lemma: `‖u‖ ≤ K ‖D_A u‖ + ‖K • ρ u‖`, where `ρ`
is the restriction to a bounded interval. -/
private theorem exists_norm_le_mul_norm_trajectoryOperator_add_of_hasLyapunovForm
    (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    ∃ R > 0, ∃ K ≥ 0, ∀ u : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      ‖u‖ ≤ K * ‖trajectoryOperator AL u‖ +
      ‖(K • restrictBaseL _ (V := ⟨Ioo (-R) R, isOpen_Ioo⟩) le_top) u‖ := by
  obtain ⟨R, hR, C, hC, hest⟩ :=
    exists_norm_sq_le_mul_norm_trajectoryOperator_sq_add_of_hasLyapunovForm hA hminus hplus hbot
      htop AL hAL
  refine ⟨R, hR, √C, Real.sqrt_nonneg _, fun u ↦ ?_⟩
  have key := hest u
  have ha := norm_nonneg (trajectoryOperator AL u)
  have hb := norm_nonneg (restrictBaseL _ (V := ⟨Ioo (-R) R, isOpen_Ioo⟩) le_top u)
  rw [FunLike.coe_smul, Pi.smul_apply, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    ← mul_add]
  generalize ‖trajectoryOperator AL u‖ = a at key ha ⊢
  generalize ‖restrictBaseL _ (V := ⟨Ioo (-R) R, isOpen_Ioo⟩) le_top u‖ = b at key hb ⊢
  refine (pow_le_pow_iff_left₀ (norm_nonneg u) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, Real.sq_sqrt hC]
  nlinarith [mul_nonneg hC (mul_nonneg ha hb)]

/-- **The kernel of the trajectory operator is finite dimensional for hyperbolic limits.** For a
continuous family of operators whose limits at `±∞` have Lyapunov forms, the solutions in
`W^{1,2}(ℝ, E)` of `u' + A u = 0` form a finite-dimensional space. -/
theorem finiteDimensional_ker_trajectoryOperator_of_hasLyapunovForm
    (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    FiniteDimensional ℝ (trajectoryOperator (p := 2) AL).ker := by
  obtain ⟨R, -, K, -, hest⟩ := exists_norm_le_mul_norm_trajectoryOperator_add_of_hasLyapunovForm
    hA hminus hplus hbot htop AL hAL
  exact (trajectoryOperator (p := 2) AL).finiteDimensional_ker_of_compact_estimate
    (isCompactOperator_smul_restrictBaseL K R) hest

/-- **The range of the trajectory operator is closed for hyperbolic limits.** For a continuous
family of operators whose limits at `±∞` have Lyapunov forms, the image of `u ↦ u' + A u` from
`W^{1,2}(ℝ, E)` is a closed subspace of `L²(ℝ, E)`. -/
theorem isClosed_range_trajectoryOperator_of_hasLyapunovForm
    (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    IsClosed ((trajectoryOperator (p := 2) AL).range :
      Set (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) := by
  obtain ⟨R, -, K, -, hest⟩ := exists_norm_le_mul_norm_trajectoryOperator_add_of_hasLyapunovForm
    hA hminus hplus hbot htop AL hAL
  exact (trajectoryOperator (p := 2) AL).isClosed_range_of_compact_estimate
    (isCompactOperator_smul_restrictBaseL K R) hest

/-- **The cokernel of the trajectory operator is finite dimensional for hyperbolic limits.** For a
continuous family of operators whose limits at `±∞` have Lyapunov forms, the quotient of
`L²(ℝ, E)` by the range of `u ↦ u' + A u` is finite dimensional. -/
theorem finiteDimensional_coker_trajectoryOperator_of_hasLyapunovForm
    (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    FiniteDimensional ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) ⧸
      (trajectoryOperator (p := 2) AL).range) := by
  have := (isClosed_range_trajectoryOperator_of_hasLyapunovForm hA hminus hplus hbot htop AL
    hAL).completeSpace_coe
  obtain ⟨BL, hBL⟩ := exists_ae_eq_adjoint AL hAL
  -- The family `-A†` of the formal adjoint has limits `-A±†`, which have Lyapunov forms.
  have hadj := (ContinuousLinearMap.adjoint : (E →L[ℝ] E) ≃ₗᵢ⋆[ℝ] (E →L[ℝ] E)).continuous
  have hnegBL : ⇑(-BL) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -ContinuousLinearMap.adjoint (A s) := by
    filter_upwards [Lp.coeFn_neg BL, hBL] with s hs hBs
    rw [hs, Pi.neg_apply, hBs]
  have := finiteDimensional_ker_trajectoryOperator_of_hasLyapunovForm (hadj.comp hA).neg
    hminus.neg_adjoint hplus.neg_adjoint ((hadj.tendsto Aminus).comp hbot).neg
    ((hadj.tendsto Aplus).comp htop).neg (-BL) hnegBL
  -- The orthogonal complement of the range lies in the image of the kernel of `D_{-A†}`.
  have : FiniteDimensional ℝ (trajectoryOperator (p := 2) AL).rangeᗮ :=
    Submodule.finiteDimensional_of_le
      (orthogonal_range_trajectoryOperator_le_map_ker (ae_eq_adjoint_of_ae_eq hAL hBL))
  exact (trajectoryOperator (p := 2) AL).range.quotientEquivOrthogonal.toLinearEquiv.symm
    |>.finiteDimensional

/-- **The trajectory operator with hyperbolic limits is Fredholm.** For a continuous family `A`
of operators on a finite-dimensional real inner product space whose limits at `±∞` have Lyapunov
forms, `u ↦ u' + A u` is a Fredholm operator from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)`. Neither symmetry
nor differentiability of `A` is assumed. -/
theorem isFredholm_trajectoryOperator_of_hasLyapunovForm
    (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    (trajectoryOperator (p := 2) AL).IsFredholm :=
  .of_finite_ker_coker _
    (finiteDimensional_ker_trajectoryOperator_of_hasLyapunovForm hA hminus hplus hbot htop AL hAL)
    (finiteDimensional_coker_trajectoryOperator_of_hasLyapunovForm hA hminus hplus hbot htop AL
      hAL)

/-- **The index of the trajectory operator with hyperbolic limits.** Under the hypotheses of
`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_of_hasLyapunovForm`, the index of
`D_A u = u' + A u` is `dim ker D_A - dim ker D_{-A†}`, where `BL` is an `L∞` class of the pointwise
adjoint `A†`: the cokernel of `D_A` is the kernel of the formal adjoint `-d/ds + A†`. Such a class
exists by `TauCeti.WeakDerivStep.exists_ae_eq_adjoint`; for a symmetric family, `AL` itself is
one. -/
theorem index_trajectoryOperator_of_hasLyapunovForm
    (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (AL BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ ContinuousLinearMap.adjoint (A s)) :
    (trajectoryOperator (p := 2) AL).index =
      (Module.finrank ℝ (trajectoryOperator (p := 2) AL).ker : ℤ) -
        Module.finrank ℝ (trajectoryOperator (p := 2) (-BL)).ker :=
  index_trajectoryOperator_of_isClosed_range (ae_eq_adjoint_of_ae_eq hAL hBL)
    (isClosed_range_trajectoryOperator_of_hasLyapunovForm hA hminus hplus hbot htop AL hAL)

end TauCeti.WeakDerivStep
