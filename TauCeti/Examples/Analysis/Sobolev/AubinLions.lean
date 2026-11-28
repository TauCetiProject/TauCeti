/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Translation
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Fourier.RiemannLebesgue
import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.Translation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The hypotheses of the Aubin–Lions lemma cannot be dropped

The Aubin–Lions lemma takes Banach spaces `X₀ ↪ X ↪ X₁`, the first embedding compact, and a
sequence `uₙ` bounded in `Lᵖ(a, b; X₀)` whose weak time derivatives are bounded in
`Lʳ(a, b; X₁)`, and extracts a subsequence converging in `Lᵖ(a, b; X)`. On the whole space `E` it
is used in a local form, with `X₀ = H¹(E)`, `X = L²(B)` for bounded `B` and `X₁ = H⁻¹(E)`. The
three sequences of this file show that each ingredient is needed: in each, one hypothesis fails
and no subsequence converges.

* **Compactness of `X₀ ↪ X`.** In an infinite-dimensional space take `X₀ = X = X₁` and a bounded
  sequence `xₙ` of pairwise distance at least `1`, such as an orthonormal sequence of a Hilbert
  space. The maps `uₙ(t) = xₙ`, constant in time, are bounded and have zero weak derivative
  (`TauCeti.hasWeakLineDerivOn_const`), but no subsequence converges in `Lᵖ(μ; X)` for any
  nonzero measure `μ` and `p ≠ 0`
  (`TauCeti.Examples.AubinLions.not_exists_tendsto_eLpNorm_const_sub`,
  `TauCeti.Examples.AubinLions.not_exists_tendsto_eLpNorm_const_sub_of_orthonormal`,
  `TauCeti.Examples.AubinLions.exists_norm_le_not_exists_tendsto_eLpNorm_const_sub`).
* **The bound on the time derivative.** For `x ≠ 0` in any normed space, `uₙ(t) = sin (n t) x` is
  bounded in `L²(a, b; X)`
  (`TauCeti.Examples.AubinLions.eLpNorm_sin_mul_smul_le`), with
  `‖uₙ‖ → √((b - a) / 2) ‖x‖` (`TauCeti.Examples.AubinLions.tendsto_eLpNorm_sin_mul_smul`), and
  converges weakly to `0` (`TauCeti.Examples.AubinLions.tendsto_apply_toLp_sin_mul_smul`), by the
  Riemann–Lebesgue lemma. A strong limit would have to be the weak limit `0`, so no subsequence
  converges in `L²(a, b; X)`
  (`TauCeti.Examples.AubinLions.not_exists_tendsto_eLpNorm_sin_mul_smul_sub`). What fails is the
  bound on the time derivatives `n cos (n t) x`, whose norms grow linearly in `n`.
* **Locality of the whole-space form.** The translates `u(· + hₙ)` of a nonzero `u ∈ W^{1,p}(E)`,
  `p < ∞`, along vectors with `‖hₙ‖ → ∞` all have the norm of `u` (`TauCeti.W1p.norm_translate`),
  and are constant in time; they converge to `0` in `Lᵖ` on every ball
  (`MeasureTheory.MemLp.tendsto_eLpNorm_comp_add_restrict_closedBall`), as the local form allows,
  but no subsequence converges in `Lᵖ(E)`
  (`TauCeti.Examples.AubinLions.not_exists_tendsto_eLpNorm_value_translate_sub`).

## References

* J.-L. Lions, *Quelques méthodes de résolution des problèmes aux limites non linéaires*, Dunod,
  1969, Chapitre 1, Théorème 5.1.
* J. Simon, *Compact sets in the space `Lᵖ(0, T; B)`*, Ann. Mat. Pura Appl. 146 (1987), 65–96.
-/

public section

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal

namespace TauCeti.Examples.AubinLions

/-! ### Without compactness: constant sequences in an infinite-dimensional space -/

section Constant

variable {α X : Type*} [MeasurableSpace α] [NormedAddCommGroup X] {μ : Measure α} [NeZero μ]
  {p : ℝ≥0∞}

/-- If the points `x n` are pairwise at distance at least `1`, no subsequence of the maps
`t ↦ x n`, constant in time, converges in `Lᵖ(μ; X)`, for any nonzero measure `μ` and `p ≠ 0`. -/
theorem not_exists_tendsto_eLpNorm_const_sub (hp : p ≠ 0) {x : ℕ → X}
    (hx : Pairwise fun m n ↦ 1 ≤ ‖x m - x n‖) :
    ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : α → X,
      Tendsto (fun n ↦ eLpNorm (fun t ↦ x (φ n) - g t) p μ) atTop (𝓝 0) := by
  rintro ⟨φ, hφ, g, hg⟩
  -- Consecutive terms of the subsequence stay `μ univ ^ (1 / p)` apart in `Lᵖ`.
  have hc : μ univ ^ (1 / p.toReal) ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, NeZero.ne μ]
  have hle (n : ℕ) :
      μ univ ^ (1 / p.toReal) ≤ eLpNorm (fun _ : α ↦ x (φ n) - x (φ (n + 1))) p μ := by
    rw [eLpNorm_const _ hp (NeZero.ne μ)]
    have h1 : (1 : ℝ≥0∞) ≤ ‖x (φ n) - x (φ (n + 1))‖ₑ := by
      rw [← ofReal_norm]
      exact ENNReal.one_le_ofReal.2 (hx (hφ.injective.ne (Nat.lt_succ_self n).ne))
    simpa only [one_mul] using mul_le_mul_left h1 (μ univ ^ (1 / p.toReal))
  have hlim : Tendsto (fun n ↦ eLpNorm (fun _ : α ↦ x (φ n) - x (φ (n + 1))) p μ) atTop
      (𝓝 0) := by
    have hsum := ENNReal.Tendsto.const_mul (hg.add (hg.comp (tendsto_add_atTop_nat 1)))
      (Or.inr (ENNReal.LpAddConst_lt_top p).ne)
    rw [add_zero, mul_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ bot_le)
      fun n ↦ ?_
    calc eLpNorm (fun _ : α ↦ x (φ n) - x (φ (n + 1))) p μ
        = eLpNorm ((fun t ↦ x (φ n) - g t) - fun t ↦ x (φ (n + 1)) - g t) p μ := by
          congr 1
          ext t
          simp
      _ ≤ _ := eLpNorm_sub_le' p
  exact hc (nonpos_iff_eq_zero.1 (ge_of_tendsto hlim (Eventually.of_forall hle)))

/-- **Compactness is necessary in the Aubin–Lions lemma.** An orthonormal sequence `e n`, constant
in time, is bounded with zero time derivative, and no subsequence converges in `Lᵖ(μ; H)`. -/
theorem not_exists_tendsto_eLpNorm_const_sub_of_orthonormal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (hp : p ≠ 0) {e : ℕ → H} (he : Orthonormal ℝ e) :
    ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : α → H,
      Tendsto (fun n ↦ eLpNorm (fun t ↦ e (φ n) - g t) p μ) atTop (𝓝 0) := by
  refine not_exists_tendsto_eLpNorm_const_sub hp fun m n hmn ↦ ?_
  have hsq : ‖e m - e n‖ ^ 2 = 2 := by
    rw [norm_sub_sq_real, he.1 m, he.1 n, he.2 hmn]
    norm_num
  nlinarith [norm_nonneg (e m - e n)]

/-- In every infinite-dimensional real normed space `X` there is a bounded sequence whose terms,
constant in time, have no subsequence converging in `Lᵖ(μ; X)`: with `X₀ = X = X₁`, the
Aubin–Lions conclusion fails as soon as the embedding `X₀ ↪ X` is not compact. -/
theorem exists_norm_le_not_exists_tendsto_eLpNorm_const_sub [NormedSpace ℝ X]
    (hX : ¬ FiniteDimensional ℝ X) (hp : p ≠ 0) :
    ∃ R : ℝ, ∃ x : ℕ → X, (∀ n, ‖x n‖ ≤ R) ∧ ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : α → X,
      Tendsto (fun n ↦ eLpNorm (fun t ↦ x (φ n) - g t) p μ) atTop (𝓝 0) := by
  obtain ⟨R, x, -, hR, hx⟩ := exists_seq_norm_le_one_le_norm_sub (𝕜 := ℝ) hX
  exact ⟨R, x, hR, not_exists_tendsto_eLpNorm_const_sub hp hx⟩

/-- The constant sequences have zero weak time derivative on any interval. -/
example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (e : ℕ → H)
    (a b : ℝ) (n : ℕ) :
    HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun _ ↦ e n) (fun _ ↦ 0) 1 :=
  hasWeakLineDerivOn_const _

end Constant

/-! ### Without a bound on the time derivative: `sin (n t) x` -/

section Sine

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {a b : ℝ}

/-- The oscillating maps `t ↦ sin (n t) x` are square integrable on `(a, b)`. -/
theorem memLp_sin_mul_smul (n : ℕ) (x : X) :
    MemLp (fun t ↦ Real.sin (n * t) • x) 2 (volume.restrict (Ioo a b)) :=
  MemLp.of_bound (by fun_prop) ‖x‖ (Eventually.of_forall fun t ↦ by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg x) (Real.abs_sin_le_one _))

/-- `∫_a^b sin² (n t) dt = (b - a) / 2 + (sin (n a) cos (n a) - sin (n b) cos (n b)) / (2 n)`. -/
private theorem integral_sin_mul_sq {n : ℕ} (hn : n ≠ 0) :
    ∫ t in a..b, Real.sin (n * t) ^ 2 = (b - a) / 2 +
      (Real.sin (n * a) * Real.cos (n * a) - Real.sin (n * b) * Real.cos (n * b)) / (2 * n) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [intervalIntegral.integral_comp_mul_left (fun t ↦ Real.sin t ^ 2) hn', integral_sin_sq,
    smul_eq_mul]
  field_simp
  ring

private theorem abs_sin_mul_cos_le_one (y : ℝ) : |Real.sin y * Real.cos y| ≤ 1 := by
  rw [abs_mul]
  simpa using mul_le_mul (Real.abs_sin_le_one y) (Real.abs_cos_le_one y) (abs_nonneg _) zero_le_one

/-- `∫_a^b sin² (n t) dt → (b - a) / 2`. -/
private theorem tendsto_integral_sin_mul_sq :
    Tendsto (fun n : ℕ ↦ ∫ t in a..b, Real.sin (n * t) ^ 2) atTop (𝓝 ((b - a) / 2)) := by
  have hrem : Tendsto (fun n : ℕ ↦
      (Real.sin (n * a) * Real.cos (n * a) - Real.sin (n * b) * Real.cos (n * b)) / (2 * n))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n : ℕ ↦ 1 / (n : ℝ)) (fun n ↦ ?_)
      tendsto_one_div_atTop_nhds_zero_nat
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * n)]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    rw [div_le_div_iff₀ (by positivity) hn']
    have h1 := abs_sub (Real.sin (n * a) * Real.cos (n * a)) (Real.sin (n * b) * Real.cos (n * b))
    have h2 := abs_sin_mul_cos_le_one (n * a)
    have h3 := abs_sin_mul_cos_le_one (n * b)
    nlinarith
  have hlim := (tendsto_const_nhds (x := (b - a) / 2)).add hrem
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [integral_sin_mul_sq hn]

/-- The `L²(a, b; X)` norm of `t ↦ sin (n t) x` is `‖x‖` times the square root of
`∫_a^b sin² (n t) dt`. -/
private theorem eLpNorm_sin_mul_smul_eq (hab : a ≤ b) (n : ℕ) (x : X) :
    eLpNorm (fun t ↦ Real.sin (n * t) • x) 2 (volume.restrict (Ioo a b)) =
      ENNReal.ofReal (√(∫ t in a..b, Real.sin (n * t) ^ 2) * ‖x‖) := by
  rw [(memLp_sin_mul_smul n x).eLpNorm_two_eq_ofReal_sqrt_integral,
    intervalIntegral.integral_of_le hab, ← integral_Ioc_eq_integral_Ioo,
    ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul
      (integral_nonneg fun t ↦ sq_nonneg _), ← integral_mul_const]
  congr 3
  ext t
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- The maps `t ↦ sin (n t) x` are bounded in `L²(a, b; X)` by `√(b - a) ‖x‖`. -/
theorem eLpNorm_sin_mul_smul_le (hab : a ≤ b) (n : ℕ) (x : X) :
    eLpNorm (fun t ↦ Real.sin (n * t) • x) 2 (volume.restrict (Ioo a b)) ≤
      ENNReal.ofReal (√(b - a) * ‖x‖) := by
  rw [eLpNorm_sin_mul_smul_eq hab]
  gcongr
  calc ∫ t in a..b, Real.sin (n * t) ^ 2 ≤ ∫ _ in a..b, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hab (Continuous.intervalIntegrable (by fun_prop) _ _)
          intervalIntegrable_const fun t _ ↦ by
          rw [sq_le_one_iff_abs_le_one]
          exact Real.abs_sin_le_one _
    _ = b - a := by simp

/-- The `L²(a, b; X)` norm of `t ↦ sin (n t) x` tends to `√((b - a) / 2) ‖x‖`. -/
theorem tendsto_eLpNorm_sin_mul_smul (hab : a ≤ b) (x : X) :
    Tendsto (fun n : ℕ ↦ eLpNorm (fun t ↦ Real.sin (n * t) • x) 2 (volume.restrict (Ioo a b)))
      atTop (𝓝 (ENNReal.ofReal (√((b - a) / 2) * ‖x‖))) := by
  simp only [eLpNorm_sin_mul_smul_eq hab]
  exact ENNReal.tendsto_ofReal
    (((Real.continuous_sqrt.tendsto _).comp tendsto_integral_sin_mul_sq).mul_const ‖x‖)

/-- **`sin (n t) x` converges weakly to zero** in `L²(a, b; X)`: every continuous linear functional
tends to zero along the sequence. This is the Riemann–Lebesgue lemma. -/
theorem tendsto_apply_toLp_sin_mul_smul (x : X)
    (ℓ : StrongDual ℝ (Lp X 2 (volume.restrict (Ioo a b)))) :
    Tendsto (fun n : ℕ ↦ ℓ ((memLp_sin_mul_smul n x).toLp _)) atTop (𝓝 0) := by
  -- `ℓ (s • x)` is a continuous linear functional of the scalar `s ∈ L²`, so it is `⟪g, s⟫`.
  let L : Lp ℝ 2 (volume.restrict (Ioo a b)) →L[ℝ] Lp X 2 (volume.restrict (Ioo a b)) :=
    (ContinuousLinearMap.toSpanSingleton ℝ x).compLpL 2 _
  let g : Lp ℝ 2 (volume.restrict (Ioo a b)) := (InnerProductSpace.toDual ℝ _).symm (ℓ.comp L)
  have hs (n : ℕ) : MemLp (fun t ↦ Real.sin (n * t)) 2 (volume.restrict (Ioo a b)) := by
    simpa using memLp_sin_mul_smul (a := a) (b := b) n (1 : ℝ)
  have hkey (n : ℕ) : ℓ ((memLp_sin_mul_smul n x).toLp _) =
      ∫ t in Ioo a b, g t * Real.sin (n * t) := by
    have hL : L ((hs n).toLp _) = (memLp_sin_mul_smul n x).toLp _ := by
      refine Lp.ext ?_
      filter_upwards [ContinuousLinearMap.coeFn_compLpL (μ := volume.restrict (Ioo a b)) (p := 2)
        (ContinuousLinearMap.toSpanSingleton ℝ x) ((hs n).toLp _), (hs n).coeFn_toLp,
        (memLp_sin_mul_smul n x).coeFn_toLp] with t h1 h2 h3
      rw [h1, h3, h2, ContinuousLinearMap.toSpanSingleton_apply]
    rw [← hL, ← ContinuousLinearMap.comp_apply, ← InnerProductSpace.toDual_symm_apply,
      L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(hs n).coeFn_toLp] with t ht
    rw [ht, RCLike.inner_apply, conj_trivial, mul_comm]
  have hI : Integrable ((Ioo a b).indicator g) :=
    (integrable_indicator_iff measurableSet_Ioo).2 ((Lp.memLp g).integrable one_le_two)
  refine (hI.tendsto_integral_mul_sin_atTop.comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  rw [hkey, Function.comp_apply, ← integral_indicator measurableSet_Ioo]
  congr 1
  ext t
  simp only [indicator_mul_left]

/-- **The time-derivative bound is necessary in the Aubin–Lions lemma.** For `a < b` and `x ≠ 0`,
no subsequence of `t ↦ sin (n t) x` converges in `L²(a, b; X)`: a limit would be the weak limit
`0`, but the norms tend to `√((b - a) / 2) ‖x‖ ≠ 0`. -/
theorem not_exists_tendsto_eLpNorm_sin_mul_smul_sub (hab : a < b) {x : X} (hx : x ≠ 0) :
    ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℝ → X, Tendsto
      (fun n ↦ eLpNorm (fun t ↦ Real.sin (φ n * t) • x - g t) 2 (volume.restrict (Ioo a b)))
      atTop (𝓝 0) := by
  rintro ⟨φ, hφ, g, hg⟩
  -- `g` is square integrable, as it is at finite distance from a square integrable map.
  obtain ⟨n₀, hn₀⟩ := (hg.eventually (gt_mem_nhds zero_lt_one)).exists
  have hgm : MemLp g 2 (volume.restrict (Ioo a b)) := by
    have hd : MemLp (fun t ↦ Real.sin (φ n₀ * t) • x - g t) 2 (volume.restrict (Ioo a b)) :=
      memLp_iff.2 (hn₀.trans ENNReal.one_lt_top)
    have hg' : g = (fun t ↦ Real.sin (φ n₀ * t) • x) - fun t ↦ Real.sin (φ n₀ * t) • x - g t := by
      ext t
      simp
    rw [hg']
    exact (memLp_sin_mul_smul (φ n₀) x).sub hd
  -- The subsequence converges in `L²` to the class of `g`, which is then killed by every
  -- continuous linear functional, hence is zero.
  have hconv : Tendsto (fun n ↦ (memLp_sin_mul_smul (a := a) (b := b) (φ n) x).toLp _) atTop
      (𝓝 (hgm.toLp g)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine hg.congr fun n ↦ eLpNorm_congr_ae ?_
    filter_upwards [(memLp_sin_mul_smul (a := a) (b := b) (φ n) x).coeFn_toLp,
      hgm.coeFn_toLp] with t h1 h2
    rw [Pi.sub_apply, h1, h2]
  have hzero : hgm.toLp g = 0 := SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ ↦
    tendsto_nhds_unique ((ℓ.continuous.tendsto _).comp hconv)
      ((tendsto_apply_toLp_sin_mul_smul x ℓ).comp hφ.tendsto_atTop)
  have hg0 : g =ᵐ[volume.restrict (Ioo a b)] 0 :=
    hgm.coeFn_toLp.symm.trans ((Lp.eq_zero_iff_ae_eq_zero).1 hzero)
  -- Then the norms of the subsequence tend to zero, but also to `√((b - a) / 2) ‖x‖ ≠ 0`.
  have hnorm := (tendsto_eLpNorm_sin_mul_smul hab.le x).comp hφ.tendsto_atTop
  have hlim : ENNReal.ofReal (√((b - a) / 2) * ‖x‖) = 0 := by
    refine tendsto_nhds_unique hnorm (hg.congr fun n ↦ eLpNorm_congr_ae ?_)
    filter_upwards [hg0] with t ht
    simp [ht]
  rw [ENNReal.ofReal_eq_zero] at hlim
  have : 0 < √((b - a) / 2) * ‖x‖ :=
    mul_pos (Real.sqrt_pos.2 (by linarith)) (norm_pos_iff.2 hx)
  linarith

end Sine

/-! ### On the whole space: translates escaping to infinity -/

section Translate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞}
  [Fact (1 ≤ p)]

/-- **The whole-space Aubin–Lions lemma is only local.** If `u ∈ W^{1,p}(E)` is nonzero,
`p < ∞`, and `‖h n‖ → ∞`, the translates `u (· + h n)`, which all have the norm of `u`
(`TauCeti.W1p.norm_translate`), have no subsequence converging in `Lᵖ(E)`. -/
theorem not_exists_tendsto_eLpNorm_value_translate_sub (hp : p ≠ ∞) {u : W1p μ ⊤ p} (hu : u ≠ 0)
    {h : ℕ → E} (hh : Tendsto (fun n ↦ ‖h n‖) atTop atTop) :
    ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : E → ℝ, Tendsto (fun n ↦ eLpNorm
      (fun x ↦ W1p.value (W1p.translate (V := ⊤) (h := h (φ n)) (mapsTo_univ _ _) u) x - g x)
      p μ) atTop (𝓝 0) := by
  rintro ⟨φ, hφ, g, hg⟩
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hμ : μ ≤ μ.restrict ((⊤ : Opens E) : Set E) := by
    rw [Opens.coe_top, Measure.restrict_univ]
  -- The translated values are the translates of the value of `u`, which must then vanish.
  have hval : W1p.value u =ᵐ[μ] 0 :=
    ((Lp.memLp (W1p.value u)).mono_measure hμ).ae_eq_zero_of_tendsto_eLpNorm_comp_add_sub hp0
      hp (hh.comp hφ.tendsto_atTop) (hg.congr fun n ↦ eLpNorm_congr_ae
        (((W1p.value_translate_ae _ u).filter_mono (ae_mono hμ)).sub Filter.EventuallyEq.rfl))
  exact hu (W1p.ext_value (by
    rw [(Lp.eq_zero_iff_ae_eq_zero).2 (ae_restrict_of_ae hval), W1p.value_zero]))

/-- The translates `u (· + n v)` along a nonzero vector `v` escape to infinity. -/
example (v : E) (hv : v ≠ 0) : Tendsto (fun n : ℕ ↦ ‖(n : ℝ) • v‖) atTop atTop := by
  simp only [norm_smul, Real.norm_natCast]
  exact tendsto_natCast_atTop_atTop.atTop_mul_const (norm_pos_iff.2 hv)

end Translate

end TauCeti.Examples.AubinLions
