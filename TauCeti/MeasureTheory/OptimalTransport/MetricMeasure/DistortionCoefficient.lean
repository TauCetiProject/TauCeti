/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.SineRatio
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The distortion coefficients `σ_{K,N}^{(t)}(θ)` and `τ_{K,N}^{(t)}(θ)`

The curvature-dimension conditions `CD(K, N)` and `CD*(K, N)` of Sturm and Lott–Villani, and the
measure-contraction property `MCP(K, N)`, compare the reference measure along a Wasserstein
geodesic with the model space of constant curvature `K / N` (or `K / (N - 1)`) through two families
of *distortion coefficients*. For a curvature bound `K : ℝ`, a dimension bound `N`, a time `t` and
a distance `θ`, put `D = K θ² / N`. Then

* `σ_{K,N}^{(t)}(θ) = ∞` if `D ≥ π²`,
* `σ_{K,N}^{(t)}(θ) = sin (t √D) / sin √D` if `0 < D < π²`,
* `σ_{K,N}^{(t)}(θ) = t` if `D = 0`,
* `σ_{K,N}^{(t)}(θ) = sinh (t √(-D)) / sinh √(-D)` if `D < 0`,

and, for `N > 1`, `τ_{K,N}^{(t)}(θ) = ∞` if `(N - 1) π² ≤ K θ²` (exactly when
`σ_{K,N-1}^{(t)}(θ) = ∞`) and `τ_{K,N}^{(t)}(θ) = t ^ (1 / N) σ_{K,N-1}^{(t)}(θ) ^ (1 - 1 / N)`
otherwise, with `τ_{K,1}^{(t)}(θ) = ∞` for `K θ² > 0` and `τ_{K,1}^{(t)}(θ) = t` for `K θ² ≤ 0`.
This `N = 1` case deviates from Sturm at distance zero: Sturm puts `τ_{K,1}^{(t)}(θ) = ∞` for
every `K > 0`, including `θ = 0`, whereas here `τ_{K,1}^{(t)}(0) = t`, the limit of
`τ_{K,N}^{(t)}(0) = t` as `N ↓ 1`. The two conventions agree whenever `θ ≠ 0` or `K ≤ 0`.
For `0 < D < π²` and `θ ≥ 0`, `√D = θ √(K / N)`, so the second case of `σ` is the familiar
`sin (t θ √(K / N)) / sin (θ √(K / N))`.

Both families take values in `[0, ∞]` for `t ∈ [0, 1]`, so they are `ℝ≥0∞`-valued here. The value
`∞` records the Bonnet–Myers phenomenon: under `CD(K, N)` with `K > 0` no two points are at
distance more than `π √((N - 1) / K)`. As in Sturm, the critical-distance case of `τ` is `∞`
for every `t`, including `t = 0`, rather than the `ℝ≥0∞` product `0 · ∞ = 0`. Outside
`t ∈ [0, 1]`, `N > 0` for `σ` and `N ≥ 1` for `τ`, the values are junk values carrying no meaning.

The basic theory is the dependence on the parameters. For `t ∈ [0, 1]` the coefficient
`σ_{K,N}^{(t)}(θ)` depends on `(K, N, θ)` only through `D` and is monotone in `D`
(`TauCeti.distortionSigma_mono`). This rests on the monotonicity of the model ratios
`Real.monotoneOn_sin_mul_div_sin` and `Real.antitoneOn_sinh_mul_div_sinh`, and on the comparisons
`Real.mul_sin_le_sin_mul` and `Real.sinh_mul_le_mul_sinh` with the flat value `t`. Hence both
coefficients increase with the curvature bound `K`. In particular they are at least `t` for
`K ≥ 0` and at most `t` for `K ≤ 0`, with equality `σ_{0,N}^{(t)}(θ) = τ_{0,N}^{(t)}(θ) = t` in
the flat case. This monotonicity is what makes the curvature-dimension conditions weaker as `K`
decreases, as in the implication from `CD(K, N)` to `CD(K', N)` for `K' ≤ K`.

## Main definitions

* `TauCeti.distortionSigma K N t θ`: the distortion coefficient `σ_{K,N}^{(t)}(θ)`.
* `TauCeti.distortionTau K N t θ`: the distortion coefficient `τ_{K,N}^{(t)}(θ)`.

## Main statements

* `TauCeti.distortionSigma_mono`: for `t ∈ [0, 1]`, `σ_{K,N}^{(t)}(θ) ≤ σ_{K',N'}^{(t)}(θ')`
  whenever `K θ² / N ≤ K' θ'² / N'`.
* `TauCeti.distortionSigma_left_monotone`, `TauCeti.distortionTau_left_monotone`: both
  coefficients are monotone in the curvature bound `K`.
* `TauCeti.antitoneOn_distortionSigma_of_nonneg`, `TauCeti.monotoneOn_distortionSigma_of_nonpos`:
  `σ_{K,N}` decreases with `N` for `K ≥ 0` and increases with `N` for `K ≤ 0`.
* `TauCeti.distortionSigma_zero_left`, `TauCeti.distortionTau_zero_left`: the flat coefficients
  are `t`.
* `TauCeti.ofReal_le_distortionSigma`, `TauCeti.distortionSigma_le_ofReal` and their `τ`
  analogues: comparison with the flat value `t` for `K ≥ 0` and for `K ≤ 0`.
* `TauCeti.distortionSigma_eq_top_iff`, `TauCeti.distortionTau_eq_top_iff`: for `N > 0`,
  `σ_{K,N}^{(t)}(θ)` is infinite exactly when `N π² ≤ K θ²`; for `N > 1`, `τ_{K,N}^{(t)}(θ)`
  is infinite exactly when `(N - 1) π² ≤ K θ²`.
* `TauCeti.distortionSigma_time_one`, `TauCeti.distortionTau_time_one`: below the critical
  distance both coefficients equal `1` at time `1`.

## References

* K.-T. Sturm, *On the geometry of metric measure spaces. II*, Acta Math. 196 (2006), 133–177.
* K. Bacher and K.-T. Sturm, *Localization and tensorization properties of the
  curvature-dimension condition for metric measure spaces*, J. Funct. Anal. 259 (2010), 28–56.
* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapters 14 and 29.
-/

public section

open Real Set
open scoped ENNReal

namespace TauCeti

/-- The **distortion coefficient** `σ_{K,N}^{(t)}(θ)` of the curvature-dimension condition
`CD*(K, N)`. With `D = K θ² / N`, it is `∞` if `π² ≤ D`, `sin (t √D) / sin √D` if `0 < D < π²`,
`t` if `D = 0`, and `sinh (t √(-D)) / sinh √(-D)` if `D < 0`. It is meaningful for `N > 0` and
`t ∈ [0, 1]`. -/
noncomputable def distortionSigma (K N t θ : ℝ) : ℝ≥0∞ :=
  if π ^ 2 ≤ K * θ ^ 2 / N then ⊤
  else if 0 < K * θ ^ 2 / N then
    ENNReal.ofReal (sin (t * √(K * θ ^ 2 / N)) / sin √(K * θ ^ 2 / N))
  else if K * θ ^ 2 / N = 0 then ENNReal.ofReal t
  else ENNReal.ofReal (sinh (t * √(-(K * θ ^ 2 / N))) / sinh √(-(K * θ ^ 2 / N)))

/-- The **distortion coefficient** `τ_{K,N}^{(t)}(θ)` of the curvature-dimension condition
`CD(K, N)`. For `N > 1` it is `∞` if `(N - 1) π² ≤ K θ²` and
`t ^ (1 / N) σ_{K,N-1}^{(t)}(θ) ^ (1 - 1 / N)` otherwise, while `τ_{K,1}^{(t)}(θ)` is `∞` for
`K θ² > 0` and `t` for `K θ² ≤ 0`; unlike Sturm, who puts `τ_{K,1}^{(t)}(θ) = ∞` for every
`K > 0`, this gives `τ_{K,1}^{(t)}(0) = t`, the limit of `τ_{K,N}^{(t)}(0)` as `N ↓ 1`. It is
meaningful for `N ≥ 1` and `t ∈ [0, 1]`. -/
noncomputable def distortionTau (K N t θ : ℝ) : ℝ≥0∞ :=
  if 1 < N then
    if (N - 1) * π ^ 2 ≤ K * θ ^ 2 then ⊤
    else ENNReal.ofReal t ^ (1 / N) * distortionSigma K (N - 1) t θ ^ (1 - 1 / N)
  else if 0 < K * θ ^ 2 then ⊤ else ENNReal.ofReal t

/-! ### The coefficient `σ` -/

section Sigma

variable {K N t θ : ℝ}

/-- The coefficient `σ` as a function of the time `t` and of `D = K θ² / N`. -/
private noncomputable def sigmaOf (t D : ℝ) : ℝ≥0∞ :=
  if π ^ 2 ≤ D then ⊤
  else if 0 < D then ENNReal.ofReal (sin (t * √D) / sin √D)
  else if D = 0 then ENNReal.ofReal t
  else ENNReal.ofReal (sinh (t * √(-D)) / sinh √(-D))

private theorem distortionSigma_eq_sigmaOf (K N t θ : ℝ) :
    distortionSigma K N t θ = sigmaOf t (K * θ ^ 2 / N) :=
  rfl

private theorem sigmaOf_of_le {D : ℝ} (h : π ^ 2 ≤ D) : sigmaOf t D = ⊤ :=
  ite_eq_left h

private theorem sigmaOf_of_pos {D : ℝ} (h₀ : 0 < D) (h : D < π ^ 2) :
    sigmaOf t D = ENNReal.ofReal (sin (t * √D) / sin √D) := by
  rw [sigmaOf, ite_eq_right h.not_ge, ite_eq_left h₀]

private theorem sigmaOf_zero : sigmaOf t 0 = ENNReal.ofReal t := by
  rw [sigmaOf, ite_eq_right (not_le.2 (pow_pos pi_pos 2)), ite_eq_right (lt_irrefl 0),
    ite_eq_left rfl]

private theorem sigmaOf_of_neg {D : ℝ} (h : D < 0) :
    sigmaOf t D = ENNReal.ofReal (sinh (t * √(-D)) / sinh √(-D)) := by
  rw [sigmaOf, ite_eq_right (by nlinarith [sq_nonneg π]), ite_eq_right h.not_gt,
    ite_eq_right h.ne]

/-- At or beyond the critical distance, `N π² ≤ K θ²`, the coefficient is infinite. -/
@[simp]
theorem distortionSigma_eq_top_of_le (hN : 0 < N) (h : N * π ^ 2 ≤ K * θ ^ 2) :
    distortionSigma K N t θ = ⊤ :=
  sigmaOf_of_le ((le_div_iff₀' hN).2 h)

/-- The spherical formula, for `0 < K θ² < N π²`. -/
@[simp]
theorem distortionSigma_of_pos (hN : 0 < N) (h₀ : 0 < K * θ ^ 2) (h : K * θ ^ 2 < N * π ^ 2) :
    distortionSigma K N t θ =
      ENNReal.ofReal (sin (t * √(K * θ ^ 2 / N)) / sin √(K * θ ^ 2 / N)) :=
  sigmaOf_of_pos (div_pos h₀ hN) ((div_lt_iff₀' hN).2 h)

/-- The hyperbolic formula, for `K θ² < 0`. -/
@[simp]
theorem distortionSigma_of_neg (hN : 0 < N) (h : K * θ ^ 2 < 0) :
    distortionSigma K N t θ =
      ENNReal.ofReal (sinh (t * √(-(K * θ ^ 2 / N))) / sinh √(-(K * θ ^ 2 / N))) :=
  sigmaOf_of_neg (div_neg_of_neg_of_pos h hN)

/-- The flat coefficient `σ_{0,N}^{(t)}(θ)` is `t`. -/
@[simp]
theorem distortionSigma_zero_left : distortionSigma 0 N t θ = ENNReal.ofReal t := by
  rw [distortionSigma_eq_sigmaOf, zero_mul, zero_div, sigmaOf_zero]

/-- At distance `0` the coefficient `σ_{K,N}^{(t)}(0)` is `t`. -/
@[simp]
theorem distortionSigma_zero_right : distortionSigma K N t 0 = ENNReal.ofReal t := by
  rw [distortionSigma_eq_sigmaOf, zero_pow two_ne_zero, mul_zero, zero_div, sigmaOf_zero]

/-- Below `π²`, the coefficient at a nonnegative `D` is at least the flat value `t`. -/
private theorem ofReal_le_sigmaOf (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) {D : ℝ} (h₀ : 0 ≤ D)
    (h : D < π ^ 2) : ENNReal.ofReal t ≤ sigmaOf t D := by
  rcases h₀.eq_or_lt with rfl | h₀
  · rw [sigmaOf_zero]
  have hs : √D < π := (sqrt_lt' pi_pos).2 h
  rw [sigmaOf_of_pos h₀ h]
  refine ENNReal.ofReal_le_ofReal ((le_div_iff₀ (sin_pos_of_pos_of_lt_pi (sqrt_pos.2 h₀) hs)).2 ?_)
  exact mul_sin_le_sin_mul ht₀ ht₁ (sqrt_nonneg D) hs.le

/-- At a negative `D`, the coefficient is at most the flat value `t`. -/
private theorem sigmaOf_le_ofReal (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) {D : ℝ} (h : D < 0) :
    sigmaOf t D ≤ ENNReal.ofReal t := by
  rw [sigmaOf_of_neg h]
  refine ENNReal.ofReal_le_ofReal ((div_le_iff₀ (sinh_pos_iff.2 (sqrt_pos.2 (neg_pos.2 h)))).2 ?_)
  exact sinh_mul_le_mul_sinh ht₀ ht₁ (sqrt_nonneg _)

/-- For `t ∈ [0, 1]` the coefficient is monotone in `D`. Within the spherical and the hyperbolic
regimes this is the monotonicity of the model ratios; across regimes the flat value `t` separates
the hyperbolic values from the spherical ones. -/
private theorem sigmaOf_mono (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) {D D' : ℝ} (h : D ≤ D') :
    sigmaOf t D ≤ sigmaOf t D' := by
  by_cases hπ : π ^ 2 ≤ D'
  · rw [sigmaOf_of_le hπ]
    exact le_top
  rw [not_le] at hπ
  rcases lt_or_ge D 0 with hD | hD
  · rcases lt_or_ge D' 0 with hD' | hD'
    · rw [sigmaOf_of_neg hD, sigmaOf_of_neg hD']
      exact ENNReal.ofReal_le_ofReal (antitoneOn_sinh_mul_div_sinh ht₀ ht₁
        (sqrt_pos.2 (neg_pos.2 hD')) (sqrt_pos.2 (neg_pos.2 hD)) (sqrt_le_sqrt (neg_le_neg h)))
    · exact (sigmaOf_le_ofReal ht₀ ht₁ hD).trans (ofReal_le_sigmaOf ht₀ ht₁ hD' hπ)
  rcases hD.eq_or_lt with rfl | hD
  · rw [sigmaOf_zero]
    exact ofReal_le_sigmaOf ht₀ ht₁ h hπ
  have hD' : 0 < D' := hD.trans_le h
  rw [sigmaOf_of_pos hD (h.trans_lt hπ), sigmaOf_of_pos hD' hπ]
  exact ENNReal.ofReal_le_ofReal (monotoneOn_sin_mul_div_sin ht₀ ht₁
    ⟨sqrt_pos.2 hD, (sqrt_lt' pi_pos).2 (h.trans_lt hπ)⟩ ⟨sqrt_pos.2 hD', (sqrt_lt' pi_pos).2 hπ⟩
    (sqrt_le_sqrt h))

/-- **Monotonicity of `σ`.** For `t ∈ [0, 1]`, `σ_{K,N}^{(t)}(θ)` is a monotone function of
`K θ² / N`. -/
theorem distortionSigma_mono {K' N' θ' : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (h : K * θ ^ 2 / N ≤ K' * θ' ^ 2 / N') :
    distortionSigma K N t θ ≤ distortionSigma K' N' t θ' := by
  simpa only [distortionSigma_eq_sigmaOf] using sigmaOf_mono ht₀ ht₁ h

/-- For `t ∈ [0, 1]` and `N ≥ 0`, `σ_{K,N}^{(t)}(θ)` is monotone in the curvature bound `K`. -/
theorem distortionSigma_left_monotone (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hN : 0 ≤ N) :
    Monotone fun K ↦ distortionSigma K N t θ := fun _ _ hK ↦
  distortionSigma_mono ht₀ ht₁ (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hK (sq_nonneg θ)) hN)

/-- For `t ∈ [0, 1]` and `K ≥ 0`, `σ_{K,N}^{(t)}(θ)` decreases with the dimension bound `N > 0`.
-/
theorem antitoneOn_distortionSigma_of_nonneg (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hK : 0 ≤ K) :
    AntitoneOn (fun N ↦ distortionSigma K N t θ) (Ioi 0) := fun _ hN _ _ hNN' ↦
  distortionSigma_mono ht₀ ht₁ (div_le_div_of_nonneg_left (mul_nonneg hK (sq_nonneg θ)) hN hNN')

/-- For `t ∈ [0, 1]` and `K ≤ 0`, `σ_{K,N}^{(t)}(θ)` increases with the dimension bound `N > 0`.
-/
theorem monotoneOn_distortionSigma_of_nonpos (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hK : K ≤ 0) :
    MonotoneOn (fun N ↦ distortionSigma K N t θ) (Ioi 0) := fun _ hN _ _ hNN' ↦ by
  refine distortionSigma_mono ht₀ ht₁ ?_
  have := div_le_div_of_nonneg_left
    (neg_nonneg.2 (mul_nonpos_of_nonpos_of_nonneg hK (sq_nonneg θ))) hN hNN'
  rw [neg_div, neg_div] at this
  linarith

/-- For `K ≥ 0` the coefficient `σ_{K,N}^{(t)}(θ)` is at least the flat value `t`. -/
theorem ofReal_le_distortionSigma (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hN : 0 ≤ N) (hK : 0 ≤ K) :
    ENNReal.ofReal t ≤ distortionSigma K N t θ := by
  simpa using distortionSigma_left_monotone (θ := θ) ht₀ ht₁ hN hK

/-- For `K ≤ 0` the coefficient `σ_{K,N}^{(t)}(θ)` is at most the flat value `t`. -/
theorem distortionSigma_le_ofReal (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hN : 0 ≤ N) (hK : K ≤ 0) :
    distortionSigma K N t θ ≤ ENNReal.ofReal t := by
  simpa using distortionSigma_left_monotone (θ := θ) ht₀ ht₁ hN hK

/-- The coefficient `σ_{K,N}^{(t)}(θ)` is infinite exactly when `N π² ≤ K θ²`. -/
theorem distortionSigma_eq_top_iff (hN : 0 < N) :
    distortionSigma K N t θ = ⊤ ↔ N * π ^ 2 ≤ K * θ ^ 2 := by
  rw [distortionSigma_eq_sigmaOf, ← le_div_iff₀' hN]
  refine ⟨fun h ↦ ?_, sigmaOf_of_le⟩
  by_contra hπ
  rw [not_le] at hπ
  rcases lt_trichotomy (K * θ ^ 2 / N) 0 with hD | hD | hD
  · simp [sigmaOf_of_neg hD] at h
  · simp [hD, sigmaOf_zero] at h
  · simp [sigmaOf_of_pos hD hπ] at h

/-- Below the critical distance, `σ_{K,N}^{(1)}(θ) = 1`. -/
@[simp]
theorem distortionSigma_time_one (hN : 0 < N) (h : K * θ ^ 2 < N * π ^ 2) :
    distortionSigma K N 1 θ = 1 := by
  rw [distortionSigma_eq_sigmaOf]
  have hπ : K * θ ^ 2 / N < π ^ 2 := (div_lt_iff₀' hN).2 h
  rcases lt_trichotomy (K * θ ^ 2 / N) 0 with hD | hD | hD
  · rw [sigmaOf_of_neg hD, one_mul, div_self (sinh_pos_iff.2 (sqrt_pos.2 (neg_pos.2 hD))).ne',
      ENNReal.ofReal_one]
  · rw [hD, sigmaOf_zero, ENNReal.ofReal_one]
  · rw [sigmaOf_of_pos hD hπ, one_mul, div_self (sin_pos_of_pos_of_lt_pi (sqrt_pos.2 hD)
      ((sqrt_lt' pi_pos).2 hπ)).ne', ENNReal.ofReal_one]

/-- Below the critical distance, `σ_{K,N}^{(0)}(θ) = 0`. -/
@[simp]
theorem distortionSigma_time_zero (hN : 0 < N) (h : K * θ ^ 2 < N * π ^ 2) :
    distortionSigma K N 0 θ = 0 := by
  rw [distortionSigma_eq_sigmaOf]
  have hπ : K * θ ^ 2 / N < π ^ 2 := (div_lt_iff₀' hN).2 h
  rcases lt_trichotomy (K * θ ^ 2 / N) 0 with hD | hD | hD
  · simp [sigmaOf_of_neg hD]
  · simp [hD, sigmaOf_zero]
  · simp [sigmaOf_of_pos hD hπ]

end Sigma

/-! ### The coefficient `τ` -/

section Tau

variable {K N t θ : ℝ}

/-- For `N > 1` and `(N - 1) π² ≤ K θ²`, the coefficient `τ_{K,N}^{(t)}(θ)` is infinite. -/
@[simp]
theorem distortionTau_eq_top_of_le (hN : 1 < N) (h : (N - 1) * π ^ 2 ≤ K * θ ^ 2) :
    distortionTau K N t θ = ⊤ := by
  rw [distortionTau, ite_eq_left hN, ite_eq_left h]

/-- For `N > 1` and `K θ² < (N - 1) π²`,
`τ_{K,N}^{(t)}(θ) = t ^ (1 / N) σ_{K,N-1}^{(t)}(θ) ^ (1 - 1 / N)`. -/
@[simp]
theorem distortionTau_of_one_lt (hN : 1 < N) (h : K * θ ^ 2 < (N - 1) * π ^ 2) :
    distortionTau K N t θ =
      ENNReal.ofReal t ^ (1 / N) * distortionSigma K (N - 1) t θ ^ (1 - 1 / N) := by
  rw [distortionTau, ite_eq_left hN, ite_eq_right h.not_ge]

/-- For `N ≤ 1` the coefficient `τ_{K,N}^{(t)}(θ)` is `∞` if `K θ² > 0` and `t` otherwise. -/
private theorem distortionTau_of_le_one (hN : N ≤ 1) :
    distortionTau K N t θ = if 0 < K * θ ^ 2 then ⊤ else ENNReal.ofReal t := by
  rw [distortionTau, ite_eq_right hN.not_gt]

/-- For `N = 1` and `K θ² > 0`, the coefficient `τ_{K,1}^{(t)}(θ)` is infinite. -/
@[simp]
theorem distortionTau_one_eq_top_of_pos (h : 0 < K * θ ^ 2) : distortionTau K 1 t θ = ⊤ := by
  rw [distortionTau, ite_eq_right (lt_irrefl 1), ite_eq_left h]

/-- For `N = 1` and `K θ² ≤ 0`, the coefficient `τ_{K,1}^{(t)}(θ)` is `t`. -/
@[simp]
theorem distortionTau_one_of_nonpos (h : K * θ ^ 2 ≤ 0) :
    distortionTau K 1 t θ = ENNReal.ofReal t := by
  rw [distortionTau, ite_eq_right (lt_irrefl 1), ite_eq_right h.not_gt]

/-- The flat coefficient `τ_{0,N}^{(t)}(θ)` is `t`. -/
@[simp]
theorem distortionTau_zero_left : distortionTau 0 N t θ = ENNReal.ofReal t := by
  rcases lt_or_ge 1 N with hN | hN
  · rw [distortionTau_of_one_lt hN (by rw [zero_mul]; have := sub_pos.2 hN; positivity),
      distortionSigma_zero_left, ENNReal.rpow_mul_rpow_one_sub _
      (one_div_nonneg.2 (zero_le_one.trans hN.le)) ((div_le_one (zero_lt_one.trans hN)).2 hN.le)]
  · rw [distortionTau_of_le_one hN, zero_mul, ite_eq_right (lt_irrefl 0)]

/-- At distance `0` the coefficient `τ_{K,N}^{(t)}(0)` is `t`. -/
@[simp]
theorem distortionTau_zero_right : distortionTau K N t 0 = ENNReal.ofReal t := by
  rcases lt_or_ge 1 N with hN | hN
  · rw [distortionTau_of_one_lt hN
      (by rw [zero_pow two_ne_zero, mul_zero]; have := sub_pos.2 hN; positivity),
      distortionSigma_zero_right, ENNReal.rpow_mul_rpow_one_sub _
      (one_div_nonneg.2 (zero_le_one.trans hN.le)) ((div_le_one (zero_lt_one.trans hN)).2 hN.le)]
  · rw [distortionTau_of_le_one hN, zero_pow two_ne_zero, mul_zero, ite_eq_right (lt_irrefl 0)]

/-- For `t ∈ [0, 1]`, `τ_{K,N}^{(t)}(θ)` is monotone in the curvature bound `K`. -/
theorem distortionTau_left_monotone (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    Monotone fun K ↦ distortionTau K N t θ := by
  intro K K' hK
  rcases lt_or_ge 1 N with hN | hN
  · dsimp only
    rcases le_or_gt ((N - 1) * π ^ 2) (K' * θ ^ 2) with hK' | hK'
    · rw [distortionTau_eq_top_of_le hN hK']
      exact le_top
    rw [distortionTau_of_one_lt hN hK',
      distortionTau_of_one_lt hN ((mul_le_mul_of_nonneg_right hK (sq_nonneg θ)).trans_lt hK')]
    gcongr
    · exact sub_nonneg.2 ((div_le_one (zero_lt_one.trans hN)).2 hN.le)
    · exact distortionSigma_left_monotone ht₀ ht₁ (sub_nonneg.2 hN.le) hK
  · dsimp only
    rw [distortionTau_of_le_one hN, distortionTau_of_le_one hN]
    rcases lt_or_ge 0 (K' * θ ^ 2) with hK' | hK'
    · rw [ite_eq_left hK']
      exact le_top
    · rw [ite_eq_right ((mul_le_mul_of_nonneg_right hK (sq_nonneg θ)).trans hK').not_gt,
        ite_eq_right hK'.not_gt]

/-- For `K ≥ 0` the coefficient `τ_{K,N}^{(t)}(θ)` is at least the flat value `t`. -/
theorem ofReal_le_distortionTau (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hK : 0 ≤ K) :
    ENNReal.ofReal t ≤ distortionTau K N t θ := by
  simpa using distortionTau_left_monotone (N := N) (θ := θ) ht₀ ht₁ hK

/-- For `K ≤ 0` the coefficient `τ_{K,N}^{(t)}(θ)` is at most the flat value `t`. -/
theorem distortionTau_le_ofReal (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hK : K ≤ 0) :
    distortionTau K N t θ ≤ ENNReal.ofReal t := by
  simpa using distortionTau_left_monotone (N := N) (θ := θ) ht₀ ht₁ hK

/-- For `N > 1`, the coefficient `τ_{K,N}^{(t)}(θ)` is infinite exactly when
`(N - 1) π² ≤ K θ²`. -/
theorem distortionTau_eq_top_iff (hN : 1 < N) :
    distortionTau K N t θ = ⊤ ↔ (N - 1) * π ^ 2 ≤ K * θ ^ 2 := by
  refine ⟨fun h ↦ ?_, distortionTau_eq_top_of_le hN⟩
  by_contra hπ
  rw [not_le] at hπ
  have hσ : distortionSigma K (N - 1) t θ ≠ ⊤ :=
    mt (distortionSigma_eq_top_iff (sub_pos.2 hN)).1 hπ.not_ge
  have hN₀ : 0 < N := zero_lt_one.trans hN
  have hNi : N⁻¹ < 1 := inv_lt_one_of_one_lt₀ hN
  rw [distortionTau_of_one_lt hN hπ, ENNReal.mul_eq_top] at h
  simp [ENNReal.rpow_eq_top_iff, hσ, hN₀, hN₀.not_gt, hNi.not_gt] at h

/-- Below the critical distance, `τ_{K,N}^{(1)}(θ) = 1`. -/
@[simp]
theorem distortionTau_time_one (h : K * θ ^ 2 < (N - 1) * π ^ 2) :
    distortionTau K N 1 θ = 1 := by
  rcases lt_or_ge 1 N with hN | hN
  · rw [distortionTau_of_one_lt hN h, distortionSigma_time_one (sub_pos.2 hN) h]
    simp
  · rw [distortionTau_of_le_one hN, ite_eq_right (h.trans_le (mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.2 hN) (sq_nonneg π))).not_gt, ENNReal.ofReal_one]

/-- Below the critical distance, `τ_{K,N}^{(0)}(θ) = 0`. -/
@[simp]
theorem distortionTau_time_zero (h : K * θ ^ 2 < (N - 1) * π ^ 2) :
    distortionTau K N 0 θ = 0 := by
  rcases lt_or_ge 1 N with hN | hN
  · rw [distortionTau_of_one_lt hN h, ENNReal.ofReal_zero,
      ENNReal.zero_rpow_of_pos (by have := zero_lt_one.trans hN; positivity), zero_mul]
  · rw [distortionTau_of_le_one hN, ite_eq_right (h.trans_le (mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.2 hN) (sq_nonneg π))).not_gt, ENNReal.ofReal_zero]

end Tau

end TauCeti
