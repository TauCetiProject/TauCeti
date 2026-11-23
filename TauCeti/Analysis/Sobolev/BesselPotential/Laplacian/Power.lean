/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.LaplacianResolvent
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Real powers of the shifted Laplacian on the `L²` Bessel-potential scale

For `c > 0` the shifted Laplacian `-Δ + c` on tempered distributions is the Fourier multiplier
with symbol `(2π)² ‖ζ‖² + c`
(`TemperedDistribution.neg_laplacian_add_smul_eq_fourierMultiplierCLM`), where `ζ` is Mathlib's
Fourier variable. In the angular frequency `ξ = 2π ζ`, for which
`∂ⱼ` has symbol `i ξⱼ`, this symbol is `‖ξ‖² + c`. Its real powers are the Fourier multipliers

`(-Δ + c) ^ s = 𝓕⁻ ((2π)² ‖ζ‖² + c) ^ s 𝓕`, `s ∈ ℝ`

(`TemperedDistribution.shiftedLaplacianRpow F c s`). They form a one-parameter group, extending
the integer powers already present: `(-Δ + c) ^ 1` is `-Δ + c` and `(-Δ + c) ^ (-1)` is the
resolvent `TemperedDistribution.laplacianResolvent c`. For `c = 1` and a flat metric they are the
powers `L ^ s` of the positive operator `L = 1 + ∇*∇ = 1 - Δ`.

Mathlib's Bessel-potential spaces `H^t = H^{t,2}` are normed with the weight
`⟨ζ⟩ ^ t = (1 + ‖ζ‖ ^ 2) ^ (t / 2)` in the Fourier variable `ζ = ξ / (2π)`, while the norm
`‖(1 - Δ) ^ (t / 2) u‖_{L²}` uses the angular weight `⟨ξ⟩ ^ t = (1 + 4π² ‖ζ‖²) ^ (t / 2)`. The two
weights are not equal but comparable, and this file compares the operators and the norms they
define:

* `(-Δ + (2π)²) ^ s` is exactly `(2π) ^ (2s)` times Mathlib's Bessel potential `J ^ (2s)`
  (`TemperedDistribution.shiftedLaplacianRpow_two_pi_sq`);
* `(-Δ + c) ^ s` maps `H^t` onto `H^{t - 2s}` for every real `s` and `t`
  (`TemperedDistribution.memSobolev_shiftedLaplacianRpow_iff`), giving an isomorphism
  `H^t ≃ H^{t - 2s}` with inverse `(-Δ + c) ^ (-s)`
  (`BesselPotentialSpace.shiftedLaplacianRpowEquiv`). For `s = -1` the resolvent maps `H^t` to
  `H^{t+2}` (`TemperedDistribution.MemSobolev.laplacianResolvent`), and for `s = 1` this is elliptic
  regularity: `f` lies in `H^{t+2}` exactly when `-Δ f + c f` lies in `H^t`
  (`TemperedDistribution.memSobolev_add_two_iff_neg_laplacian_add_smul`). Inverting a
  constant-coefficient first-order operator `L` satisfying a Weitzenböck identity
  `L* L = L L* = -Δ + c` on the Sobolev scale reduces to these statements, through
  `L⁻¹ = L* (-Δ + c)⁻¹`;
* with `a = min c (2π)²` and `b = max c (2π)²`, the norms satisfy the two-sided bound

  `‖u‖_{H^t} ≤ max (a ^ (-s)) (b ^ (-s)) ‖(-Δ + c) ^ s u‖_{H^{t - 2s}}` and
  `‖(-Δ + c) ^ s u‖_{H^{t - 2s}} ≤ max (a ^ s) (b ^ s) ‖u‖_{H^t}`

  (`BesselPotentialSpace.norm_le_norm_shiftedLaplacianRpowEquiv`,
  `BesselPotentialSpace.norm_shiftedLaplacianRpowEquiv_le`). For `s = t / 2` the target is
  `H^0 = L²`, so the norm `‖(-Δ + c) ^ (t / 2) u‖_{L²}` is equivalent to the Bessel-potential norm
  `‖u‖_{H^t}`, with these explicit constants; for `c = 1` it is the angular-weight norm
  `‖(1 - Δ) ^ (t / 2) u‖_{L²}`.

The proofs factor `(-Δ + c) ^ s` as `J ^ (2s)` after the Fourier multiplier with the bounded symbol
`((2π)² ‖ζ‖² + c) ^ s (1 + ‖ζ‖ ^ 2) ^ (-s)`, whose values lie between `min (a ^ s) (b ^ s)` and
`max (a ^ s) (b ^ s)` because `a (1 + ‖ζ‖²) ≤ (2π)² ‖ζ‖² + c ≤ b (1 + ‖ζ‖²)`. The norm bounds are
Plancherel's theorem in the form `BesselPotentialSpace.norm_le_of_toDistr_eq_fourierMultiplierCLM`.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Chapter 4, §1 (the Sobolev spaces
  `H^s(ℝⁿ)` and the operators `Λ^s = (1 - Δ)^(s/2)`).
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap Laplacian Real BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace TemperedDistribution

omit [InnerProductSpace ℝ E] in
/-- The symbol `(2π)² ‖ζ‖² + c` of `-Δ + c` lies between `min c (2π)²` and `max c (2π)²` times the
squared Japanese bracket `1 + ‖ζ‖ ^ 2`. -/
private theorem shiftedLaplacianSymbol_mem_Icc (c : ℝ) (ζ : E) :
    min c ((2 * π) ^ 2) * (1 + ‖ζ‖ ^ 2) ≤ (2 * π) ^ 2 * ‖ζ‖ ^ 2 + c ∧
      (2 * π) ^ 2 * ‖ζ‖ ^ 2 + c ≤ max c ((2 * π) ^ 2) * (1 + ‖ζ‖ ^ 2) := by
  have h₁ := min_le_left c ((2 * π) ^ 2)
  have h₂ := min_le_right c ((2 * π) ^ 2)
  have h₃ := le_max_left c ((2 * π) ^ 2)
  have h₄ := le_max_right c ((2 * π) ^ 2)
  constructor <;> nlinarith [sq_nonneg ‖ζ‖]

omit [InnerProductSpace ℝ E] in
/-- The powers of the symbol of `-Δ + c` are bounded by the corresponding powers of the squared
Japanese bracket: `((2π)² ‖ζ‖² + c) ^ s ≤ max (a ^ s) (b ^ s) (1 + ‖ζ‖ ^ 2) ^ s`, with
`a = min c (2π)²` and `b = max c (2π)²`. -/
private theorem shiftedLaplacianSymbol_rpow_le {c : ℝ} (hc : 0 < c) (s : ℝ) (ζ : E) :
    ((2 * π) ^ 2 * ‖ζ‖ ^ 2 + c) ^ s ≤
      max (min c ((2 * π) ^ 2) ^ s) (max c ((2 * π) ^ 2) ^ s) * (1 + ‖ζ‖ ^ 2) ^ s :=
  Real.rpow_le_max_mul_rpow (lt_min hc (by positivity)) (by positivity)
    (shiftedLaplacianSymbol_mem_Icc c ζ).1 (shiftedLaplacianSymbol_mem_Icc c ζ).2 s

/-- For `c > 0`, the complex-valued symbol `((2π)² ‖ζ‖² + c) ^ s` of `(-Δ + c) ^ s` has temperate
growth. -/
theorem hasTemperateGrowth_shiftedLaplacianSymbol_rpow {c : ℝ} (hc : 0 < c) (s : ℝ) :
    (fun ζ : E ↦ ((((2 * π) ^ 2 * ‖ζ‖ ^ 2 + c) ^ s : ℝ) : ℂ)).HasTemperateGrowth :=
  Complex.hasTemperateGrowth_ofReal.comp
    (TauCeti.hasTemperateGrowth_mul_norm_sq_add_rpow (by positivity) hc s)

/-- For `c > 0`, the symbol `((2π)² ‖ζ‖² + c) ^ s (1 + ‖ζ‖ ^ 2) ^ (-s)` comparing `(-Δ + c) ^ s`
with the Bessel potential `J ^ (2s)` has temperate growth. -/
private theorem hasTemperateGrowth_shiftedLaplacianSymbol_rpow_mul_rpow_neg {c : ℝ} (hc : 0 < c)
    (s : ℝ) : (fun ζ : E ↦
      ((((2 * π) ^ 2 * ‖ζ‖ ^ 2 + c) ^ s * (1 + ‖ζ‖ ^ 2) ^ (-s) : ℝ) : ℂ)).HasTemperateGrowth := by
  have h := hasTemperateGrowth_shiftedLaplacianSymbol_rpow (E := E) hc s
  simp only [Complex.ofReal_mul]
  fun_prop

omit [InnerProductSpace ℝ E] in
/-- For `c > 0`, the symbol `((2π)² ‖ζ‖² + c) ^ s (1 + ‖ζ‖ ^ 2) ^ (-s)` is bounded by
`max (a ^ s) (b ^ s)`, with `a = min c (2π)²` and `b = max c (2π)²`. -/
private theorem norm_shiftedLaplacianSymbol_rpow_mul_rpow_neg_le {c : ℝ} (hc : 0 < c) (s : ℝ)
    (ζ : E) :
    ‖((((2 * π) ^ 2 * ‖ζ‖ ^ 2 + c) ^ s * (1 + ‖ζ‖ ^ 2) ^ (-s) : ℝ) : ℂ)‖ ≤
      max (min c ((2 * π) ^ 2) ^ s) (max c ((2 * π) ^ 2) ^ s) := by
  have hpos : 0 < (1 + ‖ζ‖ ^ 2) ^ s := by positivity
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.rpow_neg (by positivity),
    ← div_eq_mul_inv, div_le_iff₀ hpos]
  exact shiftedLaplacianSymbol_rpow_le hc s ζ

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]

section normed

variable [NormedSpace ℂ F]

variable (F) in
/-- The **real powers of the shifted Laplacian** `(-Δ + c) ^ s` on tempered distributions: the
Fourier multiplier with symbol `((2π)² ‖ζ‖² + c) ^ s`. For `c > 0` they form a one-parameter
group (`shiftedLaplacianRpow_shiftedLaplacianRpow`) with `(-Δ + c) ^ 1 = -Δ + c`
(`shiftedLaplacianRpow_one`) and `(-Δ + c) ^ (-1) = (c - Δ)⁻¹` (`shiftedLaplacianRpow_neg_one`);
for `c ≤ 0` the value is not meaningful. -/
def shiftedLaplacianRpow (c s : ℝ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  fourierMultiplierCLM F (fun ζ : E ↦ ((((2 * π) ^ 2 * ‖ζ‖ ^ 2 + c) ^ s : ℝ) : ℂ))

variable (F) in
/-- The power `(-Δ + c) ^ s` is the Fourier multiplier with symbol `((2π)² ‖ζ‖² + c) ^ s`. -/
theorem shiftedLaplacianRpow_eq_fourierMultiplierCLM (c s : ℝ) :
    shiftedLaplacianRpow F c s =
      fourierMultiplierCLM F (fun ζ : E ↦ ((((2 * π) ^ 2 * ‖ζ‖ ^ 2 + c) ^ s : ℝ) : ℂ)) :=
  (rfl)

variable (E F) in
/-- The power of exponent `0` is the identity. -/
@[simp]
theorem shiftedLaplacianRpow_zero (c : ℝ) :
    shiftedLaplacianRpow F c 0 = ContinuousLinearMap.id ℂ 𝓢'(E, F) := by
  ext1 f
  simp [shiftedLaplacianRpow_eq_fourierMultiplierCLM]

/-- **The group law**: `(-Δ + c) ^ t (-Δ + c) ^ s = (-Δ + c) ^ (s + t)` for `c > 0`. -/
@[simp]
theorem shiftedLaplacianRpow_shiftedLaplacianRpow {c : ℝ} (hc : 0 < c) (s t : ℝ)
    (f : 𝓢'(E, F)) :
    shiftedLaplacianRpow F c t (shiftedLaplacianRpow F c s f) =
      shiftedLaplacianRpow F c (s + t) f := by
  rw [shiftedLaplacianRpow_eq_fourierMultiplierCLM, shiftedLaplacianRpow_eq_fourierMultiplierCLM,
    fourierMultiplierCLM_fourierMultiplierCLM_apply
      (hasTemperateGrowth_shiftedLaplacianSymbol_rpow hc s)
      (hasTemperateGrowth_shiftedLaplacianSymbol_rpow hc t),
    shiftedLaplacianRpow_eq_fourierMultiplierCLM]
  congr 2
  ext ζ
  simp only [Pi.mul_apply, ← Complex.ofReal_mul]
  rw [← Real.rpow_add (by positivity)]

/-- The power `(-Δ + c) ^ (-s)` is a left inverse of `(-Δ + c) ^ s`, for `c > 0`. -/
theorem shiftedLaplacianRpow_neg_shiftedLaplacianRpow {c : ℝ} (hc : 0 < c) (s : ℝ)
    (f : 𝓢'(E, F)) : shiftedLaplacianRpow F c (-s) (shiftedLaplacianRpow F c s f) = f := by
  simp [hc]

/-- The power `(-Δ + c) ^ (-s)` is a right inverse of `(-Δ + c) ^ s`, for `c > 0`. -/
theorem shiftedLaplacianRpow_shiftedLaplacianRpow_neg {c : ℝ} (hc : 0 < c) (s : ℝ)
    (f : 𝓢'(E, F)) : shiftedLaplacianRpow F c s (shiftedLaplacianRpow F c (-s) f) = f := by
  simp [hc]

/-- The power of exponent `1` is the shifted Laplacian `-Δ + c`. -/
theorem shiftedLaplacianRpow_one (c : ℝ) (f : 𝓢'(E, F)) :
    shiftedLaplacianRpow F c 1 f = -Δ f + c • f := by
  rw [neg_laplacian_add_smul_eq_fourierMultiplierCLM, shiftedLaplacianRpow_eq_fourierMultiplierCLM]
  simp only [Real.rpow_one]

variable (F) in
/-- The power of exponent `-1` is the resolvent `(c - Δ)⁻¹`. -/
theorem shiftedLaplacianRpow_neg_one (c : ℝ) :
    (shiftedLaplacianRpow F c (-1) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F)) = laplacianResolvent F c := by
  rw [shiftedLaplacianRpow_eq_fourierMultiplierCLM, laplacianResolvent_eq_fourierMultiplierCLM]
  simp only [Real.rpow_neg_one]

variable (F) in
/-- For `c = (2π)²` the powers of the shifted Laplacian are Mathlib's Bessel potentials, up to a
constant: `(-Δ + (2π)²) ^ s = (2π) ^ (2s) J ^ (2s)`. Thus the Bessel potential `J ^ t` is the power
`(1 - (2π)⁻² Δ) ^ (t / 2)`, whose symbol is the Japanese bracket of the Fourier variable
`ζ = ξ / (2π)` rather than of the angular frequency `ξ`. -/
theorem shiftedLaplacianRpow_two_pi_sq (s : ℝ) :
    shiftedLaplacianRpow F ((2 * π) ^ 2) s =
      (((2 * π) ^ (2 * s) : ℝ) : ℂ) • besselPotential E F (2 * s) := by
  rw [shiftedLaplacianRpow_eq_fourierMultiplierCLM, besselPotential,
    ← fourierMultiplierCLM_smul (by fun_prop)]
  congr 1
  ext ζ
  simp only [Pi.smul_apply, smul_eq_mul, ← Complex.ofReal_mul]
  congr 1
  have h2π : 0 ≤ 2 * π := by positivity
  rw [show (2 * π) ^ 2 * ‖ζ‖ ^ 2 + (2 * π) ^ 2 = (2 * π) ^ 2 * (1 + ‖ζ‖ ^ 2) by ring,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul h2π]
  congr 2
  ring

end normed

section inner

variable [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- For `c > 0`, `(-Δ + c) ^ s` is `J ^ (2s)` after the Fourier multiplier with the bounded symbol
`((2π)² ‖ζ‖² + c) ^ s (1 + ‖ζ‖ ^ 2) ^ (-s)`. -/
private theorem shiftedLaplacianRpow_eq_besselPotential_fourierMultiplierCLM {c : ℝ} (hc : 0 < c)
    (s : ℝ) (f : 𝓢'(E, F)) :
    shiftedLaplacianRpow F c s f = besselPotential E F (2 * s)
      (fourierMultiplierCLM F (fun ζ : E ↦
        ((((2 * π) ^ 2 * ‖ζ‖ ^ 2 + c) ^ s * (1 + ‖ζ‖ ^ 2) ^ (-s) : ℝ) : ℂ)) f) := by
  rw [besselPotential, fourierMultiplierCLM_fourierMultiplierCLM_apply
      (hasTemperateGrowth_shiftedLaplacianSymbol_rpow_mul_rpow_neg hc s) (by fun_prop),
    shiftedLaplacianRpow_eq_fourierMultiplierCLM]
  congr 2
  ext ζ
  simp only [Pi.mul_apply, ← Complex.ofReal_mul]
  congr 1
  rw [mul_assoc, ← Real.rpow_add (by positivity), show -s + 2 * s / 2 = 0 by ring,
    Real.rpow_zero, mul_one]

/-- **The powers of the shifted Laplacian on the Sobolev scale**: for `c > 0`, `(-Δ + c) ^ s` maps
`H^t` to `H^{t - 2s}`, for all real `s` and `t`. -/
theorem MemSobolev.shiftedLaplacianRpow {c t : ℝ} (hc : 0 < c) (s : ℝ) {f : 𝓢'(E, F)}
    (hf : MemSobolev t 2 f) : MemSobolev (t - 2 * s) 2 (shiftedLaplacianRpow F c s f) := by
  rw [shiftedLaplacianRpow_eq_besselPotential_fourierMultiplierCLM hc,
    memSobolev_besselPotential_iff, show 2 * s + (t - 2 * s) = t by ring]
  exact hf.fourierMultiplierCLM_of_bounded
    (hasTemperateGrowth_shiftedLaplacianSymbol_rpow_mul_rpow_neg hc s)
    ⟨_, norm_shiftedLaplacianSymbol_rpow_mul_rpow_neg_le hc s⟩

/-- For `c > 0`, a tempered distribution `f` lies in `H^t` if and only if `(-Δ + c) ^ s f` lies in
`H^{t - 2s}`. -/
theorem memSobolev_shiftedLaplacianRpow_iff {c t : ℝ} (hc : 0 < c) (s : ℝ) {f : 𝓢'(E, F)} :
    MemSobolev (t - 2 * s) 2 (shiftedLaplacianRpow F c s f) ↔ MemSobolev t 2 f := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.shiftedLaplacianRpow hc s⟩
  have h' := h.shiftedLaplacianRpow hc (-s)
  rwa [shiftedLaplacianRpow_neg_shiftedLaplacianRpow hc, show t - 2 * s - 2 * -s = t by ring]
    at h'

/-- **The resolvent of the Laplacian gains two derivatives**: it maps the Sobolev space `H^s` to
`H^{s+2}`, for `c > 0`. -/
theorem MemSobolev.laplacianResolvent {c s : ℝ} (hc : 0 < c) {f : 𝓢'(E, F)}
    (hf : MemSobolev s 2 f) :
    MemSobolev (s + 2) 2 (TemperedDistribution.laplacianResolvent F c f) := by
  have h := hf.shiftedLaplacianRpow hc (-1)
  rwa [shiftedLaplacianRpow_neg_one, show s - 2 * -1 = s + 2 by ring] at h

/-- **Elliptic regularity for the shifted Laplacian**: for `c > 0`, a tempered distribution `f`
lies in the Sobolev space `H^{s+2}` if and only if `-Δ f + c f` lies in `H^s`. -/
theorem memSobolev_add_two_iff_neg_laplacian_add_smul {c s : ℝ} (hc : 0 < c) {f : 𝓢'(E, F)} :
    MemSobolev (s + 2) 2 f ↔ MemSobolev s 2 (-Δ f + c • f) := by
  rw [← memSobolev_shiftedLaplacianRpow_iff hc 1 (t := s + 2) (f := f), shiftedLaplacianRpow_one,
    show s + 2 - 2 * 1 = s by ring]

end inner

end TemperedDistribution

namespace BesselPotentialSpace

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ F] [CompleteSpace F] {c : ℝ}

/-- **The powers of the shifted Laplacian as isomorphisms of the Sobolev scale**: for `c > 0` and
real `s`, `t`, the power `(-Δ + c) ^ s` restricts to an isomorphism `H^t ≃ H^{t - 2s}` whose
inverse is the restriction of `(-Δ + c) ^ (-s)`. -/
def shiftedLaplacianRpowEquiv (hc : 0 < c) (s t : ℝ) : H^{t}(E, F) ≃L[ℂ] H^{t - 2 * s}(E, F) :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    (mapCLM (TemperedDistribution.shiftedLaplacianRpow F c s) fun u ↦
      u.memSobolev_toDistr.shiftedLaplacianRpow hc s)
    (mapCLM (TemperedDistribution.shiftedLaplacianRpow F c (-s)) fun u ↦ by
      have h := u.memSobolev_toDistr.shiftedLaplacianRpow hc (-s)
      rwa [show t - 2 * s - 2 * -s = t by ring] at h)
    (ContinuousLinearMap.ext fun u ↦ ext (by simp [hc]))
    (ContinuousLinearMap.ext fun u ↦ ext (by simp [hc]))

/-- The isomorphism `shiftedLaplacianRpowEquiv` acts on the underlying tempered distributions by
`(-Δ + c) ^ s`. -/
@[simp]
theorem toDistr_shiftedLaplacianRpowEquiv (hc : 0 < c) (s t : ℝ) (u : H^{t}(E, F)) :
    (shiftedLaplacianRpowEquiv hc s t u).toDistr =
      TemperedDistribution.shiftedLaplacianRpow F c s u.toDistr :=
  toDistr_mapCLM _ _ u

/-- The inverse of `shiftedLaplacianRpowEquiv` acts on the underlying tempered distributions by
`(-Δ + c) ^ (-s)`. -/
@[simp]
theorem toDistr_shiftedLaplacianRpowEquiv_symm (hc : 0 < c) (s t : ℝ)
    (v : H^{t - 2 * s}(E, F)) :
    ((shiftedLaplacianRpowEquiv hc s t).symm v).toDistr =
      TemperedDistribution.shiftedLaplacianRpow F c (-s) v.toDistr :=
  toDistr_mapCLM _ _ v

/-- **Upper norm bound**: for `c > 0`,
`‖(-Δ + c) ^ s u‖_{H^{t - 2s}} ≤ max (a ^ s) (b ^ s) ‖u‖_{H^t}`
with `a = min c (2π)²` and `b = max c (2π)²`. -/
theorem norm_shiftedLaplacianRpowEquiv_le (hc : 0 < c) (s t : ℝ) (u : H^{t}(E, F)) :
    ‖shiftedLaplacianRpowEquiv hc s t u‖ ≤
      max (min c ((2 * π) ^ 2) ^ s) (max c ((2 * π) ^ 2) ^ s) * ‖u‖ := by
  refine norm_le_of_toDistr_eq_fourierMultiplierCLM
    (TemperedDistribution.hasTemperateGrowth_shiftedLaplacianSymbol_rpow hc s) (fun ζ ↦ ?_)
    (toDistr_shiftedLaplacianRpowEquiv hc s t u)
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity),
    show t / 2 = (2 * s + (t - 2 * s)) / 2 by ring, TauCeti.one_add_norm_sq_rpow_add,
    show 2 * s / 2 = s by ring, ← mul_assoc]
  gcongr
  exact TemperedDistribution.shiftedLaplacianSymbol_rpow_le hc s ζ

/-- **Lower norm bound**: for `c > 0`,
`‖u‖_{H^t} ≤ max (a ^ (-s)) (b ^ (-s)) ‖(-Δ + c) ^ s u‖_{H^{t - 2s}}`
with `a = min c (2π)²` and `b = max c (2π)²`. -/
theorem norm_le_norm_shiftedLaplacianRpowEquiv (hc : 0 < c) (s t : ℝ) (u : H^{t}(E, F)) :
    ‖u‖ ≤ max (min c ((2 * π) ^ 2) ^ (-s)) (max c ((2 * π) ^ 2) ^ (-s)) *
      ‖shiftedLaplacianRpowEquiv hc s t u‖ := by
  set v := shiftedLaplacianRpowEquiv hc s t u
  refine norm_le_of_toDistr_eq_fourierMultiplierCLM
    (TemperedDistribution.hasTemperateGrowth_shiftedLaplacianSymbol_rpow hc (-s)) (fun ζ ↦ ?_)
    (u := v) (v := u) ?_
  · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity),
      show (t - 2 * s) / 2 = (2 * -s + t) / 2 by ring, TauCeti.one_add_norm_sq_rpow_add,
      show 2 * -s / 2 = -s by ring, ← mul_assoc]
    gcongr
    exact TemperedDistribution.shiftedLaplacianSymbol_rpow_le hc (-s) ζ
  · rw [toDistr_shiftedLaplacianRpowEquiv,
      ← TemperedDistribution.shiftedLaplacianRpow_eq_fourierMultiplierCLM,
      TemperedDistribution.shiftedLaplacianRpow_neg_shiftedLaplacianRpow hc]

end BesselPotentialSpace
