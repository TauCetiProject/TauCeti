/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Cusp.Multiplier
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Cusp integrals, constant terms and cuspidality at level `N`

For a function `f : ℍ → ℂ`, a level `N` and `σ ∈ SL₂(ℤ)`, the *cusp integral*
`I_σ(f, y) = ∫₀^N f(σ(x + iy)) dx` integrates `f` in the coordinate of the cusp `σ ∞` over a
horizontal segment of length `N`, and the *constant term* `c_σ(f, y) = w⁻¹ ∫₀^w f(σ(x + iy)) dx`
averages it over one period `w = cuspWidthGamma0 N σ` of that cusp. Points of `ℍ` are written
`pt x y = x + iy`, which is meaningful for `y > 0`.

Suppose `f` transforms by the multiplier `ζ` under the generator `σ T^w σ⁻¹ ∈ Γ₀(N)` of the
stabilizer of `σ ∞`, as every `f` with `f (γ z) = χ(d_γ) f z` for `γ ∈ Γ₀(N)` does with
`ζ = cuspMultiplier χ σ`. Then `x ↦ f(σ(x + iy))` satisfies `g (x + w) = ζ g x`, the segment of
length `N` consists of `N / w` periods, and so `I_σ(f, y) = (1 + ζ + ⋯ + ζ^(N/w - 1)) w c_σ(f, y)`.
At a regular cusp (`ζ = 1`) this is `N c_σ(f, y)`; at an irregular cusp `ζ` is a nontrivial
`N / w`-th root of unity and the cusp integral vanishes identically. Thus the single condition
`IsCuspidal N f`, that every cusp integral vanishes at every height, needs no bookkeeping of
widths or characters, and it is equivalent to the vanishing of the constant term at every
regular cusp (`TauCeti.MaassForms.isCuspidal_iff_constantTerm_eq_zero`). It is the cusp
condition of a Maass cusp form of level `N` with nebentypus.

## Main definitions

* `TauCeti.MaassForms.pt`: the point `x + iy` of `ℍ`.
* `TauCeti.MaassForms.horizontalCuspIntegral`: the cusp integral `I_σ(f, y)`.
* `TauCeti.MaassForms.constantTerm`: the constant term `c_σ(f, y)`.
* `TauCeti.MaassForms.IsCuspidal`: every cusp integral vanishes at every positive height.

## Main results

* `TauCeti.MaassForms.horizontalCuspIntegral_eq_natCast_mul_constantTerm`: at a regular cusp,
  `I_σ(f, y) = N c_σ(f, y)`.
* `TauCeti.MaassForms.horizontalCuspIntegral_eq_zero_of_not_isRegularCusp`: at an irregular cusp,
  `I_σ(f, y) = 0`.
* `TauCeti.MaassForms.isCuspidal_iff_constantTerm_eq_zero`: cuspidality is the vanishing of the
  constant term at every regular cusp.
* `TauCeti.MaassForms.not_isCuspidal_const`: a nonzero constant is not cuspidal.

## References

* Henryk Iwaniec, *Spectral Methods of Automorphic Forms*, §3.4.
* Andrew R. Booker, Min Lee and Andreas Strömbergsson, *Twist-minimal trace formulas and the
  Selberg eigenvalue conjecture*, arXiv:1803.06016, §1.1.
-/

public noncomputable section

open Complex UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups

namespace TauCeti.MaassForms

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {σ : SL(2, ℤ)} {f g : ℍ → ℂ} {y : ℝ}

/-! ### The coordinate `x + iy` -/

/-- **The point `x + iy` of the upper half-plane**, for `y > 0`. For `y ≤ 0` it is the junk value
of `UpperHalfPlane.ofComplex`, a fixed point of `ℍ` independent of `x` and `y`. -/
def pt (x y : ℝ) : ℍ :=
  ofComplex (x + y * Complex.I)

/-- For `y > 0`, the point `pt x y` is `x + iy`. -/
theorem coe_pt (x : ℝ) (hy : 0 < y) : (pt x y : ℂ) = x + y * Complex.I := by
  rw [pt, ofComplex_apply_of_im_pos (by simpa using hy)]

/-- For `y > 0`, the real part of `pt x y` is `x`. -/
theorem re_pt (x : ℝ) (hy : 0 < y) : (pt x y).re = x := by
  rw [← coe_re, coe_pt x hy]
  simp

/-- For `y > 0`, the imaginary part of `pt x y` is `y`. -/
theorem im_pt (x : ℝ) (hy : 0 < y) : (pt x y).im = y := by
  rw [← coe_im, coe_pt x hy]
  simp

/-- For `y > 0`, translating `x` by `t` is the action of `t` on `ℍ` by translation. -/
theorem pt_add (x t : ℝ) (hy : 0 < y) : pt (x + t) y = t +ᵥ pt x y := by
  ext1
  rw [coe_pt _ hy, coe_vadd, coe_pt _ hy]
  push_cast
  ring

/-- The point `pt x y` depends continuously on `x`; for `y ≤ 0` it is constant. -/
theorem continuous_pt (y : ℝ) : Continuous fun x : ℝ ↦ pt x y := by
  rcases lt_or_ge 0 y with hy | hy
  · rw [isOpenEmbedding_coe.isEmbedding.continuous_iff]
    have h : ((↑) : ℍ → ℂ) ∘ (fun x : ℝ ↦ pt x y) = fun x : ℝ ↦ (x : ℂ) + y * Complex.I :=
      funext fun x ↦ coe_pt x hy
    rw [h]
    fun_prop
  · have h : (fun x : ℝ ↦ pt x y) = fun _ ↦ pt 0 y :=
      funext fun x ↦ ofComplex_apply_eq_of_im_nonpos (by simpa using hy) (by simpa using hy)
    rw [h]
    exact continuous_const

/-- A continuous function, read in the coordinate of the cusp `σ ∞` along the horizontal line of
height `y`, is interval integrable. -/
theorem intervalIntegrable_smul_pt (hf : Continuous f) (σ : SL(2, ℤ)) (y a b : ℝ) :
    IntervalIntegrable (fun x : ℝ ↦ f (σ • pt x y)) volume a b :=
  (hf.comp ((continuous_const_smul (σ : GL (Fin 2) ℝ)).comp (continuous_pt y))).intervalIntegrable
    a b

/-! ### Cusp integrals and constant terms -/

variable (N) in
/-- **The horizontal cusp integral** `I_σ(f, y) = ∫₀^N f(σ(x + iy)) dx`: the integral of `f` in
the coordinate of the cusp `σ ∞` over a horizontal segment of length the level `N`, at height `y`.
It is unrelated to `TauCeti.cuspIntegral`, the integral of a one-form between two cusps. -/
def horizontalCuspIntegral (σ : SL(2, ℤ)) (f : ℍ → ℂ) (y : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..N, f (σ • pt x y)

variable (N) in
theorem horizontalCuspIntegral_def (σ : SL(2, ℤ)) (f : ℍ → ℂ) (y : ℝ) :
    horizontalCuspIntegral N σ f y = ∫ x in (0 : ℝ)..N, f (σ • pt x y) := (rfl)

variable (N) in
/-- **The constant term** `c_σ(f, y) = w⁻¹ ∫₀^w f(σ(x + iy)) dx` of `f` at the cusp `σ ∞`, its
mean over one period `w = cuspWidthGamma0 N σ` of the cusp at height `y`. It is the zeroth
Fourier mode of `f` at a regular cusp. -/
def constantTerm (σ : SL(2, ℤ)) (f : ℍ → ℂ) (y : ℝ) : ℂ :=
  (cuspWidthGamma0 N σ : ℂ)⁻¹ * ∫ x in (0 : ℝ)..cuspWidthGamma0 N σ, f (σ • pt x y)

variable (N) in
theorem constantTerm_def (σ : SL(2, ℤ)) (f : ℍ → ℂ) (y : ℝ) :
    constantTerm N σ f y =
      (cuspWidthGamma0 N σ : ℂ)⁻¹ * ∫ x in (0 : ℝ)..cuspWidthGamma0 N σ, f (σ • pt x y) := (rfl)

@[simp]
theorem horizontalCuspIntegral_zero : horizontalCuspIntegral N σ 0 y = 0 := by
  simp [horizontalCuspIntegral]

theorem horizontalCuspIntegral_const_smul (c : ℂ) :
    horizontalCuspIntegral N σ (c • f) y = c * horizontalCuspIntegral N σ f y := by
  simp [horizontalCuspIntegral, intervalIntegral.integral_const_mul]

theorem horizontalCuspIntegral_add (hf : Continuous f) (hg : Continuous g) :
    horizontalCuspIntegral N σ (f + g) y =
      horizontalCuspIntegral N σ f y + horizontalCuspIntegral N σ g y :=
  intervalIntegral.integral_add (intervalIntegrable_smul_pt hf σ y _ _)
    (intervalIntegrable_smul_pt hg σ y _ _)

/-- The cusp integral of the constant `c` is `N c`. -/
@[simp]
theorem horizontalCuspIntegral_const (c : ℂ) :
    horizontalCuspIntegral N σ (fun _ ↦ c) y = N * c := by
  simp [horizontalCuspIntegral]

@[simp]
theorem constantTerm_zero : constantTerm N σ 0 y = 0 := by
  simp [constantTerm]

theorem constantTerm_const_smul (c : ℂ) :
    constantTerm N σ (c • f) y = c * constantTerm N σ f y := by
  simp only [constantTerm, Pi.smul_apply, smul_eq_mul, intervalIntegral.integral_const_mul]
  ring

theorem constantTerm_add (hf : Continuous f) (hg : Continuous g) :
    constantTerm N σ (f + g) y = constantTerm N σ f y + constantTerm N σ g y := by
  rw [constantTerm, constantTerm, constantTerm, ← mul_add]
  congr 1
  exact intervalIntegral.integral_add (intervalIntegrable_smul_pt hf σ y _ _)
    (intervalIntegrable_smul_pt hg σ y _ _)

/-- At positive level the constant term of the constant `c` is `c`. -/
@[simp]
theorem constantTerm_const [NeZero N] (c : ℂ) : constantTerm N σ (fun _ ↦ c) y = c := by
  have hw : (cuspWidthGamma0 N σ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (cuspWidthGamma0_pos N σ).ne'
  simp [constantTerm, hw]

/-- **The cusp integral as a geometric sum of constant terms.** If `f` transforms by `ζ` under the
generator `σ T^w σ⁻¹` of the stabilizer of `σ ∞`, then for `y > 0` the segment of length `N`
consists of `N / w` periods, the `j`-th contributing `ζ ^ j w c_σ(f, y)`. -/
theorem horizontalCuspIntegral_eq_geom_sum_mul {ζ : ℂ}
    (hf : ∀ z, f ((cuspGeneratorGamma0 N σ : SL(2, ℤ)) • z) = ζ * f z) (hy : 0 < y) :
    horizontalCuspIntegral N σ f y = (∑ j ∈ Finset.range (N / cuspWidthGamma0 N σ), ζ ^ j) *
      ∫ x in (0 : ℝ)..cuspWidthGamma0 N σ, f (σ • pt x y) := by
  have hper (x : ℝ) : f (σ • pt (x + cuspWidthGamma0 N σ) y) = ζ • f (σ • pt x y) := by
    rw [pt_add x _ hy, ← cuspGeneratorGamma0_smul_smul, hf, smul_eq_mul]
  have hN : ((N / cuspWidthGamma0 N σ) • (cuspWidthGamma0 N σ : ℝ)) = N := by
    rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.div_mul_cancel (cuspWidthGamma0_dvd N σ)]
  have h := intervalIntegral.integral_add_nsmul_eq_geom_sum_smul
    (f := fun x ↦ f (σ • pt x y)) hper 0 (N / cuspWidthGamma0 N σ)
  rw [zero_add, zero_add, hN] at h
  rw [horizontalCuspIntegral, h, smul_eq_mul]

/-- **At a regular cusp the cusp integral is `N` times the constant term**, for `y > 0` and `f`
transforming under the generator of the stabilizer of `σ ∞` by the multiplier of `χ`. -/
theorem horizontalCuspIntegral_eq_natCast_mul_constantTerm
    (hf : ∀ z, f ((cuspGeneratorGamma0 N σ : SL(2, ℤ)) • z) = cuspMultiplier χ σ * f z)
    (hσ : IsRegularCusp χ σ) (hy : 0 < y) :
    horizontalCuspIntegral N σ f y = N * constantTerm N σ f y := by
  rcases eq_zero_or_neZero N with rfl | _
  · simp [horizontalCuspIntegral]
  have hw : (cuspWidthGamma0 N σ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (cuspWidthGamma0_pos N σ).ne'
  rw [horizontalCuspIntegral_eq_geom_sum_mul hf hy, (isRegularCusp_iff χ σ).mp hσ, constantTerm]
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [Nat.cast_div (cuspWidthGamma0_dvd N σ) hw, div_eq_mul_inv, mul_assoc]

/-- **At an irregular cusp the cusp integral vanishes**, for `y > 0` and `f` transforming under
the generator of the stabilizer of `σ ∞` by the multiplier `ζ ≠ 1` of `χ`: `ζ` is an `N / w`-th
root of unity, so the geometric sum of its powers vanishes. -/
theorem horizontalCuspIntegral_eq_zero_of_not_isRegularCusp
    (hf : ∀ z, f ((cuspGeneratorGamma0 N σ : SL(2, ℤ)) • z) = cuspMultiplier χ σ * f z)
    (hσ : ¬IsRegularCusp χ σ) (hy : 0 < y) :
    horizontalCuspIntegral N σ f y = 0 := by
  rw [horizontalCuspIntegral_eq_geom_sum_mul hf hy, geom_sum_eq (mt (isRegularCusp_iff χ σ).mpr hσ),
    cuspMultiplier_pow_div_cuspWidthGamma0]
  simp

/-- **Cuspidality at level `N`**: every cusp integral `I_σ(f, y) = ∫₀^N f(σ(x + iy)) dx`
vanishes, for every `σ ∈ SL₂(ℤ)` and every height `y > 0`. For `f` transforming under `Γ₀(N)` by
a character, this is the vanishing of the constant term at every regular cusp
(`isCuspidal_iff_constantTerm_eq_zero`); irregular cusps impose no condition. -/
def IsCuspidal (N : ℕ) (f : ℍ → ℂ) : Prop :=
  ∀ σ : SL(2, ℤ), ∀ y > 0, horizontalCuspIntegral N σ f y = 0

theorem isCuspidal_iff :
    IsCuspidal N f ↔ ∀ σ : SL(2, ℤ), ∀ y > 0, horizontalCuspIntegral N σ f y = 0 :=
  Iff.rfl

/-- The zero function is cuspidal. -/
@[simp]
theorem isCuspidal_zero : IsCuspidal N 0 :=
  fun _ _ _ ↦ horizontalCuspIntegral_zero

/-- Cuspidal functions are closed under complex scalars. -/
theorem IsCuspidal.const_smul (hf : IsCuspidal N f) (c : ℂ) : IsCuspidal N (c • f) :=
  fun σ y hy ↦ by rw [horizontalCuspIntegral_const_smul, hf σ y hy, mul_zero]

/-- Continuous cuspidal functions are closed under addition. -/
theorem IsCuspidal.add (hf : IsCuspidal N f) (hg : IsCuspidal N g) (hf' : Continuous f)
    (hg' : Continuous g) : IsCuspidal N (f + g) :=
  fun σ y hy ↦ by rw [horizontalCuspIntegral_add hf' hg', hf σ y hy, hg σ y hy, add_zero]

/-- At positive level a nonzero constant is not cuspidal: its cusp integrals are `N c ≠ 0`. -/
theorem not_isCuspidal_const [NeZero N] {c : ℂ} (hc : c ≠ 0) : ¬IsCuspidal N fun _ ↦ c := by
  intro h
  have := h 1 1 one_pos
  rw [horizontalCuspIntegral_const] at this
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne N)) hc this

/-- **Cuspidality is the vanishing of the constant term at every regular cusp**, for `f`
transforming under the generator of the stabilizer of every cusp by the multiplier of `χ`, as
every `f` with `f (γ z) = χ(d_γ) f z` for `γ ∈ Γ₀(N)` does. -/
theorem isCuspidal_iff_constantTerm_eq_zero
    (hf : ∀ σ z, f ((cuspGeneratorGamma0 N σ : SL(2, ℤ)) • z) = cuspMultiplier χ σ * f z) :
    IsCuspidal N f ↔ ∀ σ : SL(2, ℤ), IsRegularCusp χ σ → ∀ y > 0, constantTerm N σ f y = 0 := by
  -- at level `0` every cusp integral and every constant term is an integral over `[0, 0]`
  rcases eq_zero_or_neZero N with rfl | _
  · exact iff_of_true (fun _ _ _ ↦ by simp [horizontalCuspIntegral])
      (fun _ _ _ _ ↦ by simp [constantTerm])
  refine ⟨fun h σ hσ y hy ↦ ?_, fun h σ y hy ↦ ?_⟩
  · have := h σ y hy
    rw [horizontalCuspIntegral_eq_natCast_mul_constantTerm (hf σ) hσ hy] at this
    exact (mul_eq_zero.mp this).resolve_left (Nat.cast_ne_zero.mpr (NeZero.ne N))
  · by_cases hσ : IsRegularCusp χ σ
    · rw [horizontalCuspIntegral_eq_natCast_mul_constantTerm (hf σ) hσ hy, h σ hσ y hy, mul_zero]
    · exact horizontalCuspIntegral_eq_zero_of_not_isRegularCusp (hf σ) hσ hy

end TauCeti.MaassForms
