/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.FlatTorus.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Analysis.Fourier.Torus.Decay
import TauCeti.Analysis.Fourier.Torus.Smooth
import TauCeti.Topology.Instances.AddCircle.UnitAddTorus

/-!
# The inverse of the Cauchy–Riemann operator on a nontrivial flat line over a torus

Let `ω₁, ω₂ ∈ ℂ` be linearly independent over `ℝ`, and let `θ₁, θ₂ ∈ ℝ`. The smooth sections of
the flat line over `ℂ / (ℤ ω₁ + ℤ ω₂)` with holonomy `exp (2πiθ₁)`, `exp (2πiθ₂)` along `ω₁`,
`ω₂` are the smooth functions `u : ℂ → ℂ` with

`u (z + ω₁) = exp (2πiθ₁) u z`,  `u (z + ω₂) = exp (2πiθ₂) u z`

(`TauCeti.flatLineSections`). The Cauchy–Riemann operator
`∂bar u = TauCeti.conjWirtingerDeriv u · 1` maps these sections to themselves
(`TauCeti.flatLineConjWirtingerDerivₗ`); both are defined in
`TauCeti.Analysis.Complex.Wirtinger.FlatTorus.Basic`. This file proves that
when the holonomy is nontrivial, that is when `θ₁` or `θ₂` is not an integer, `∂bar` is a linear
bijection of the smooth sections (`TauCeti.bijective_flatLineConjWirtingerDerivₗ`). Its inverse
`(TauCeti.flatLineConjWirtingerDerivEquiv hω hθ).symm` is the leading complex inverse in Taubes's
construction of Seiberg–Witten solutions near a square-zero pseudoholomorphic torus whose normal
line is flat with nontrivial holonomy. By the coercivity estimate of
`TauCeti.Analysis.Complex.Wirtinger.FlatTorus.Basic` it is bounded in `L²` over a fundamental
domain, with norm at most `(π² / 2 · (‖θ₁‖ℤ² / |ω₁|² + ‖θ₂‖ℤ² / |ω₂|²))^(-1/2)`
(`TauCeti.mul_setIntegral_norm_sq_flatLineConjWirtingerDerivEquiv_symm_apply_le`). If the holonomy
has infinite image, the same holds on every power of the line pulled back to every finite cover
of the torus (`TauCeti.bijective_flatLineConjWirtingerDerivₗ_of_irrational`).

## Proof

In the lattice coordinates `z = s ω₁ + t ω₂`, multiplying a section by the phase
`exp (-2πi (θ₁ s + θ₂ t))` gives a smooth function on the torus `UnitAddTorus (Fin 2)`, and every
smooth function on the torus arises from exactly one section in this way. Writing `A` and `B` for
the derivatives of a section along `ω₁` and `ω₂` and `D = Im (conj ω₁ ω₂)`, the identity
`2 i D ∂bar u = ω₂ A - ω₁ B` turns `∂bar` into a constant-coefficient operator on the torus, which
multiplies the `n`-th Fourier coefficient by

`m(n) = π (ω₂ (n₀ + θ₁) - ω₁ (n₁ + θ₂)) / D`.

Since `Im (conj ω₁ (ω₂ a - ω₁ b)) = a D`, this multiplier satisfies
`|m(n)| ≥ π |n₀ + θ₁| / |ω₁| ≥ π ‖θ₁‖ℤ / |ω₁|`, and similarly with the second coordinate. For
nontrivial holonomy it is therefore bounded away from zero, so dividing the rapidly decreasing
Fourier coefficients of a smooth function by `m(n)` gives the rapidly decreasing coefficients of
a smooth preimage, and a function killed by the operator has vanishing Fourier coefficients.

The argument adapts the Fourier proof for the square torus `ℂ / (ℤ + ℤ i)` with trivial twist
in `TauCeti.Analysis.Fourier.Torus.ConjWirtinger`, specifically
`UnitAddTorus.exists_conjWirtingerDeriv_eq_iff`, to an arbitrary lattice and a nontrivial
twist.

## References

* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818–893.
-/

public section

noncomputable section

open Complex ComplexConjugate MeasureTheory Set
open scoped Real ContDiff

namespace TauCeti

variable {u : ℂ → ℂ} {ω₁ ω₂ : ℂ} {θ₁ θ₂ : ℝ}

/-! ### The operator on the torus -/

section Torus

open _root_.UnitAddTorus TauCeti.UnitAddTorus

/-- After removing the phase, `∂bar` of a section becomes this constant-coefficient operator on
functions on the torus, in the lattice coordinates. -/
private def torusOp (ω₁ ω₂ : ℂ) (θ₁ θ₂ : ℝ) (g : UnitAddTorus (Fin 2) → ℂ) :
    UnitAddTorus (Fin 2) → ℂ :=
  (2 * I * (conj ω₁ * ω₂).im : ℂ)⁻¹ • (ω₂ • lineDeriv g (Pi.single 0 1) +
    (-ω₁) • lineDeriv g (Pi.single 1 1) + (2 * π * I * (ω₂ * θ₁ - ω₁ * θ₂)) • g)

private theorem torusOp_mem {g : UnitAddTorus (Fin 2) → ℂ} (hg : g ∈ smoothFunctions (Fin 2)) :
    torusOp ω₁ ω₂ θ₁ θ₂ g ∈ smoothFunctions (Fin 2) :=
  Submodule.smul_mem _ _ <| Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.smul_mem _ _ (lineDeriv_mem_smoothFunctions hg _))
      (Submodule.smul_mem _ _ (lineDeriv_mem_smoothFunctions hg _)))
    (Submodule.smul_mem _ _ hg)

/-- The Fourier multiplier `π (ω₂ (n₀ + θ₁) - ω₁ (n₁ + θ₂)) / Im (conj ω₁ ω₂)` of the torus
operator. -/
private def torusMultiplier (ω₁ ω₂ : ℂ) (θ₁ θ₂ : ℝ) (n : Fin 2 → ℤ) : ℂ :=
  π * (ω₂ * (n 0 + θ₁) - ω₁ * (n 1 + θ₂)) / (conj ω₁ * ω₂).im

/-- The torus operator multiplies the `n`-th Fourier coefficient by `torusMultiplier`. -/
private theorem mFourierCoeff_torusOp (hω : (conj ω₁ * ω₂).im ≠ 0)
    {g : UnitAddTorus (Fin 2) → ℂ} (hg : g ∈ smoothFunctions (Fin 2)) (n : Fin 2 → ℤ) :
    mFourierCoeff (torusOp ω₁ ω₂ θ₁ θ₂ g) n =
      torusMultiplier ω₁ ω₂ θ₁ θ₂ n * mFourierCoeff g n := by
  have hint (w : Fin 2 → ℝ) : Integrable (lineDeriv g w) :=
    integrable_of_mem_smoothFunctions (lineDeriv_mem_smoothFunctions hg w)
  have hD : ((conj ω₁ * ω₂).im : ℂ) ≠ 0 := mod_cast hω
  rw [torusOp, mFourierCoeff_smul,
    mFourierCoeff_add (((hint _).smul _).add ((hint _).smul _))
      ((integrable_of_mem_smoothFunctions hg).smul _),
    mFourierCoeff_add ((hint _).smul _) ((hint _).smul _), mFourierCoeff_smul, mFourierCoeff_smul,
    mFourierCoeff_smul, mFourierCoeff_lineDeriv hg, mFourierCoeff_lineDeriv hg]
  simp only [Fin.sum_univ_two, Pi.single_apply, smul_eq_mul]
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one, ofReal_one, ofReal_zero, mul_one,
    mul_zero, zero_add, add_zero]
  rw [torusMultiplier]
  field_simp
  ring

/-- The torus multiplier is bounded away from zero when the holonomy is nontrivial. -/
private theorem exists_pos_le_norm_multiplier (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ)) :
    ∃ c > 0, ∀ n : Fin 2 → ℤ, c ≤ ‖torusMultiplier ω₁ ω₂ θ₁ θ₂ n‖ := by
  have hω₁ : ω₁ ≠ 0 := by rintro rfl; simp at hω
  have hω₂ : ω₂ ≠ 0 := by rintro rfl; simp at hω
  -- The norm of the multiplier is `π ‖ω₂ a - ω₁ b‖ / |D|`.
  have hnorm (n : Fin 2 → ℤ) : ‖torusMultiplier ω₁ ω₂ θ₁ θ₂ n‖ =
      π * ‖ω₂ * ((n 0 + θ₁ : ℝ) : ℂ) - ω₁ * ((n 1 + θ₂ : ℝ) : ℂ)‖ / |(conj ω₁ * ω₂).im| := by
    rw [torusMultiplier, norm_div, norm_mul, norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      norm_real, Real.norm_eq_abs]
    push_cast
    rfl
  -- Pairing with `conj ω₁` and `conj ω₂` isolates the two coordinates.
  have him (a b : ℝ) :
      (conj ω₁ * (ω₂ * a - ω₁ * b)).im = a * (conj ω₁ * ω₂).im ∧
        (conj ω₂ * (ω₂ * a - ω₁ * b)).im = b * (conj ω₁ * ω₂).im := by
    constructor <;> simp only [mul_sub, sub_im, mul_im, mul_re, conj_re, conj_im, ofReal_re,
      ofReal_im] <;> ring
  have hpos : 0 < |(conj ω₁ * ω₂).im| := abs_pos.2 hω
  have hround {x : ℝ} (hx : x ∉ range ((↑) : ℤ → ℝ)) : 0 < |x - round x| :=
    abs_pos.2 (sub_ne_zero.2 fun h ↦ hx ⟨round x, h.symm⟩)
  rcases hθ with h | h
  · refine ⟨π * |θ₁ - round θ₁| / ‖ω₁‖, by have := hround h; positivity, fun n ↦ ?_⟩
    have hle : |θ₁ - round θ₁| ≤ |(n 0 : ℝ) + θ₁| := by
      simpa [add_comm, sub_eq_add_neg] using round_le θ₁ (-n 0)
    have hc := (him (n 0 + θ₁) (n 1 + θ₂)).1
    have hcs : |(n 0 + θ₁ : ℝ)| * |(conj ω₁ * ω₂).im| ≤
        ‖ω₁‖ * ‖ω₂ * ((n 0 + θ₁ : ℝ) : ℂ) - ω₁ * ((n 1 + θ₂ : ℝ) : ℂ)‖ := by
      rw [← abs_mul, ← hc, ← norm_conj ω₁, ← norm_mul]
      exact abs_im_le_norm _
    rw [hnorm, div_le_div_iff₀ (norm_pos_iff.2 hω₁) hpos]
    calc π * |θ₁ - round θ₁| * |(conj ω₁ * ω₂).im|
        = π * (|θ₁ - round θ₁| * |(conj ω₁ * ω₂).im|) := by ring
      _ ≤ π * (‖ω₁‖ * ‖ω₂ * ((n 0 + θ₁ : ℝ) : ℂ) - ω₁ * ((n 1 + θ₂ : ℝ) : ℂ)‖) := by
          exact mul_le_mul_of_nonneg_left
            ((mul_le_mul_of_nonneg_right hle hpos.le).trans hcs) Real.pi_pos.le
      _ = _ := by ring
  · refine ⟨π * |θ₂ - round θ₂| / ‖ω₂‖, by have := hround h; positivity, fun n ↦ ?_⟩
    have hle : |θ₂ - round θ₂| ≤ |(n 1 : ℝ) + θ₂| := by
      simpa [add_comm, sub_eq_add_neg] using round_le θ₂ (-n 1)
    have hc := (him (n 0 + θ₁) (n 1 + θ₂)).2
    have hcs : |(n 1 + θ₂ : ℝ)| * |(conj ω₁ * ω₂).im| ≤
        ‖ω₂‖ * ‖ω₂ * ((n 0 + θ₁ : ℝ) : ℂ) - ω₁ * ((n 1 + θ₂ : ℝ) : ℂ)‖ := by
      rw [← abs_mul, ← hc, ← norm_conj ω₂, ← norm_mul]
      exact abs_im_le_norm _
    rw [hnorm, div_le_div_iff₀ (norm_pos_iff.2 hω₂) hpos]
    calc π * |θ₂ - round θ₂| * |(conj ω₁ * ω₂).im|
        = π * (|θ₂ - round θ₂| * |(conj ω₁ * ω₂).im|) := by ring
      _ ≤ π * (‖ω₂‖ * ‖ω₂ * ((n 0 + θ₁ : ℝ) : ℂ) - ω₁ * ((n 1 + θ₂ : ℝ) : ℂ)‖) := by
          exact mul_le_mul_of_nonneg_left
            ((mul_le_mul_of_nonneg_right hle hpos.le).trans hcs) Real.pi_pos.le
      _ = _ := by ring

/-- For nontrivial holonomy the torus operator is injective on smooth functions. -/
private theorem eq_zero_of_torusOp_eq_zero (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ))
    {g : UnitAddTorus (Fin 2) → ℂ} (hg : g ∈ smoothFunctions (Fin 2))
    (h : torusOp ω₁ ω₂ θ₁ θ₂ g = 0) : g = 0 := by
  obtain ⟨c, hc, hle⟩ := exists_pos_le_norm_multiplier hω hθ
  refine eq_of_mFourierCoeff_eq hg (Submodule.zero_mem _) fun n ↦ ?_
  have h0 : mFourierCoeff (0 : UnitAddTorus (Fin 2) → ℂ) n = 0 := by
    simpa using mFourierCoeff_smul (0 : ℂ) (0 : UnitAddTorus (Fin 2) → ℂ) n
  have hm := mFourierCoeff_torusOp (θ₁ := θ₁) (θ₂ := θ₂) hω hg n
  rw [h, h0, eq_comm, mul_eq_zero] at hm
  rw [h0]
  refine hm.resolve_left fun h' ↦ ?_
  have := hle n
  rw [h', norm_zero] at this
  linarith

/-- For nontrivial holonomy every smooth function on the torus is the image of a smooth function
under the torus operator. -/
private theorem exists_torusOp_eq (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ))
    {g : UnitAddTorus (Fin 2) → ℂ} (hg : g ∈ smoothFunctions (Fin 2)) :
    ∃ h ∈ smoothFunctions (Fin 2), torusOp ω₁ ω₂ θ₁ θ₂ h = g := by
  obtain ⟨c₀, hc₀, hle⟩ := exists_pos_le_norm_multiplier hω hθ
  have hm (n : Fin 2 → ℤ) : torusMultiplier ω₁ ω₂ θ₁ θ₂ n ≠ 0 := fun h ↦ by
    have := hle n
    rw [h, norm_zero] at this
    linarith
  -- Divide the coefficients of `g` by the multiplier.
  set c : (Fin 2 → ℤ) → ℂ := fun n ↦ mFourierCoeff g n / torusMultiplier ω₁ ω₂ θ₁ θ₂ n
  have hcle (n : Fin 2 → ℤ) : ‖c n‖ ≤ c₀⁻¹ * ‖mFourierCoeff g n‖ := by
    rw [norm_div, div_eq_inv_mul]
    gcongr
    exact hle n
  have hc (k : ℕ) : Summable fun n ↦ ‖c n‖ * ‖n‖ ^ k := by
    refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
      ((summable_norm_mFourierCoeff_mul_pow hg zero_le_one k).mul_left c₀⁻¹)
    rw [one_mul, ← mul_assoc]
    exact mul_le_mul (hcle n) (pow_le_pow_left₀ (norm_nonneg _) (by linarith) k)
      (by positivity) (by positivity)
  have hc1 : Summable fun n ↦ ‖c n‖ := by simpa using hc 0
  have hmem := tsum_smul_mFourier_mem_smoothFunctions hc
  refine ⟨fun z ↦ ∑' n, c n • mFourier n z, hmem, ?_⟩
  refine eq_of_mFourierCoeff_eq (torusOp_mem hmem) hg fun n ↦ ?_
  rw [mFourierCoeff_torusOp hω hmem, mFourierCoeff_tsum_smul_mFourier hc1]
  exact mul_div_cancel₀ _ (hm n)

end Torus

/-! ### Sections and functions on the torus -/

section Correspondence

open _root_.UnitAddTorus TauCeti.UnitAddTorus

/-- The lattice coordinates `p ↦ p₀ ω₁ + p₁ ω₂`, a real-linear equivalence when `ω₁` and `ω₂` are
linearly independent. -/
private def latticeEquiv (hω : (conj ω₁ * ω₂).im ≠ 0) : (Fin 2 → ℝ) ≃L[ℝ] ℂ :=
  (LinearMap.linearEquivOfInjective
    ((LinearMap.proj 0).smulRight ω₁ + (LinearMap.proj 1).smulRight ω₂ :
      (Fin 2 → ℝ) →ₗ[ℝ] ℂ)
    (by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro p hp
      simp only [LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
        real_smul] at hp
      have hre := congrArg re hp
      have hi := congrArg im hp
      simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, zero_re, add_im,
        mul_im, zero_im] at hre hi
      replace hω : ω₁.re * ω₂.im - ω₁.im * ω₂.re ≠ 0 := fun h ↦ hω <| by
        simp only [mul_im, conj_re, conj_im]
        linarith
      have h0 : p 0 * (ω₁.re * ω₂.im - ω₁.im * ω₂.re) = 0 := by
        linear_combination ω₂.im * hre - ω₂.re * hi
      have h1 : p 1 * (ω₁.re * ω₂.im - ω₁.im * ω₂.re) = 0 := by
        linear_combination ω₁.re * hi - ω₁.im * hre
      funext i
      fin_cases i
      · simpa [hω] using h0
      · simpa [hω] using h1)
    (by rw [Complex.finrank_real_complex]; simp)).toContinuousLinearEquiv

private theorem latticeEquiv_apply (hω : (conj ω₁ * ω₂).im ≠ 0) (p : Fin 2 → ℝ) :
    latticeEquiv hω p = p 0 * ω₁ + p 1 * ω₂ := by
  simp [latticeEquiv, real_smul]

private theorem latticeEquiv_symm_apply_fst (hω : (conj ω₁ * ω₂).im ≠ 0) :
    (latticeEquiv hω).symm ω₁ = Pi.single 0 1 :=
  (latticeEquiv hω).symm_apply_eq.2 (by simp [latticeEquiv_apply])

private theorem latticeEquiv_symm_apply_snd (hω : (conj ω₁ * ω₂).im ≠ 0) :
    (latticeEquiv hω).symm ω₂ = Pi.single 1 1 :=
  (latticeEquiv hω).symm_apply_eq.2 (by simp [latticeEquiv_apply])

/-- The exponent `2πi (θ₁ p₀ + θ₂ p₁)` of the phase of a section in lattice coordinates. -/
private def phaseCLM (θ₁ θ₂ : ℝ) : (Fin 2 → ℝ) →L[ℝ] ℂ :=
  (2 * π * I : ℂ) • ofRealCLM.comp (θ₁ • ContinuousLinearMap.proj 0 +
    θ₂ • ContinuousLinearMap.proj 1)

private theorem phaseCLM_apply (p : Fin 2 → ℝ) :
    phaseCLM θ₁ θ₂ p = 2 * π * I * (θ₁ * p 0 + θ₂ * p 1) := by
  simp [phaseCLM]
  ring

/-- Translating by a lattice vector multiplies the phase by the corresponding holonomy. -/
private theorem exp_phaseCLM_add_single (p : Fin 2 → ℝ) :
    exp (phaseCLM θ₁ θ₂ (p + Pi.single 0 1)) = exp (2 * π * θ₁ * I) * exp (phaseCLM θ₁ θ₂ p) ∧
      exp (phaseCLM θ₁ θ₂ (p + Pi.single 1 1)) =
        exp (2 * π * θ₂ * I) * exp (phaseCLM θ₁ θ₂ p) := by
  constructor <;> rw [map_add, Complex.exp_add, mul_comm] <;> congr 2 <;>
    simp [phaseCLM_apply] <;> ring

/-- The section of the flat line corresponding to a function on the torus: in lattice coordinates
`p`, it is `exp (2πi (θ₁ p₀ + θ₂ p₁)) g p`. -/
private def ofTorus (hω : (conj ω₁ * ω₂).im ≠ 0) (θ₁ θ₂ : ℝ) (g : UnitAddTorus (Fin 2) → ℂ) :
    ℂ → ℂ :=
  (fun p : Fin 2 → ℝ ↦ exp (phaseCLM θ₁ θ₂ p) * g fun i ↦ (p i : UnitAddCircle)) ∘
    (latticeEquiv hω).symm

private theorem ofTorus_latticeEquiv (hω : (conj ω₁ * ω₂).im ≠ 0)
    (g : UnitAddTorus (Fin 2) → ℂ) (p : Fin 2 → ℝ) :
    ofTorus hω θ₁ θ₂ g (latticeEquiv hω p) =
      exp (phaseCLM θ₁ θ₂ p) * g fun i ↦ (p i : UnitAddCircle) := by
  simp [ofTorus]

private theorem ofTorus_mem (hω : (conj ω₁ * ω₂).im ≠ 0) {g : UnitAddTorus (Fin 2) → ℂ}
    (hg : g ∈ smoothFunctions (Fin 2)) : ofTorus hω θ₁ θ₂ g ∈ flatLineSections ω₁ ω₂ θ₁ θ₂ := by
  refine ⟨((contDiff_exp.comp (phaseCLM θ₁ θ₂).contDiff).mul
    (mem_smoothFunctions.1 hg)).comp (latticeEquiv hω).symm.contDiff, fun z ↦ ?_, fun z ↦ ?_⟩ <;>
    obtain ⟨p, rfl⟩ := (latticeEquiv hω).surjective z
  · have hz : latticeEquiv hω p + ω₁ = latticeEquiv hω (p + Pi.single 0 1) := by
      simp only [latticeEquiv_apply, Pi.add_apply]
      simp
      ring
    rw [hz, ofTorus_latticeEquiv, ofTorus_latticeEquiv, (exp_phaseCLM_add_single _).1,
      coe_add_single]
    ring
  · have hz : latticeEquiv hω p + ω₂ = latticeEquiv hω (p + Pi.single 1 1) := by
      simp only [latticeEquiv_apply, Pi.add_apply]
      simp
      ring
    rw [hz, ofTorus_latticeEquiv, ofTorus_latticeEquiv, (exp_phaseCLM_add_single _).2,
      coe_add_single]
    ring

/-- `∂bar` of the section corresponding to a smooth function on the torus corresponds to the torus
operator applied to that function. -/
private theorem conjWirtingerDeriv_ofTorus (hω : (conj ω₁ * ω₂).im ≠ 0)
    {g : UnitAddTorus (Fin 2) → ℂ} (hg : g ∈ smoothFunctions (Fin 2)) (z : ℂ) :
    conjWirtingerDeriv (ofTorus hω θ₁ θ₂ g) z 1 = ofTorus hω θ₁ θ₂ (torusOp ω₁ ω₂ θ₁ θ₂ g) z := by
  set L := latticeEquiv hω
  set G : (Fin 2 → ℝ) → ℂ := fun p ↦ g fun i ↦ (p i : UnitAddCircle)
  have hG := mem_smoothFunctions.1 hg
  obtain ⟨p, rfl⟩ := L.surjective z
  -- The derivative of the section in lattice coordinates, by the product rule.
  have hv : HasFDerivAt (fun q ↦ exp (phaseCLM θ₁ θ₂ q) * G q)
      (exp (phaseCLM θ₁ θ₂ p) • fderiv ℝ G p + G p • (exp (phaseCLM θ₁ θ₂ p) • phaseCLM θ₁ θ₂))
      p :=
    ((phaseCLM θ₁ θ₂).hasFDerivAt.cexp).mul ((hG.differentiable (by simp)) p).hasFDerivAt
  have hD (w : ℂ) : fderiv ℝ (ofTorus hω θ₁ θ₂ g) (L p) w =
      exp (phaseCLM θ₁ θ₂ p) * fderiv ℝ G p (L.symm w) +
        G p * (exp (phaseCLM θ₁ θ₂ p) * phaseCLM θ₁ θ₂ (L.symm w)) := by
    rw [ofTorus, L.symm.comp_right_fderiv, L.symm_apply_apply, hv.fderiv]
    simp
  have hline (i : Fin 2) : fderiv ℝ G p (Pi.single i 1) =
      lineDeriv g (Pi.single i 1) fun j ↦ (p j : UnitAddCircle) :=
    (lineDeriv_coe p _ ((hG.differentiable (by simp)) p)).symm
  rw [conjWirtingerDeriv_apply_one_eq_inv_smul_sub hω, hD, hD, latticeEquiv_symm_apply_fst,
    latticeEquiv_symm_apply_snd, hline, hline, ofTorus_latticeEquiv]
  simp only [torusOp, Pi.smul_apply, Pi.add_apply, smul_eq_mul, G, phaseCLM_apply]
  simp only [Pi.single_apply, Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one, ofReal_one,
    ofReal_zero, mul_one, mul_zero, add_zero, zero_add]
  ring

/-- Every smooth section of the flat line comes from a smooth function on the torus. -/
private theorem exists_ofTorus_eq (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hu : u ∈ flatLineSections ω₁ ω₂ θ₁ θ₂) :
    ∃ g ∈ smoothFunctions (Fin 2), ofTorus hω θ₁ θ₂ g = u := by
  set L := latticeEquiv hω
  set G : (Fin 2 → ℝ) → ℂ := fun p ↦ exp (-phaseCLM θ₁ θ₂ p) * u (L p)
  have hGc : ContDiff ℝ ∞ G :=
    (contDiff_exp.comp (phaseCLM θ₁ θ₂).contDiff.neg).mul (hu.1.comp L.contDiff)
  have hper (m : Fin 2 → ℤ) : Function.Periodic G fun i ↦ (m i : ℝ) := fun p ↦ by
    have hL : L (p + fun i ↦ (m i : ℝ)) = L p + (m 0 : ℂ) * ω₁ + (m 1 : ℂ) * ω₂ := by
      rw [map_add, latticeEquiv_apply, latticeEquiv_apply]
      push_cast
      ring
    have hexp : exp (phaseCLM θ₁ θ₂ fun i ↦ (m i : ℝ)) =
        exp (2 * π * θ₁ * I) ^ m 0 * exp (2 * π * θ₂ * I) ^ m 1 := by
      rw [← exp_int_mul, ← exp_int_mul, ← Complex.exp_add, phaseCLM_apply]
      congr 1
      push_cast
      ring
    simp only [G]
    rw [hL, Function.apply_add_int_mul_eq_zpow_mul (exp_ne_zero _) hu.2.2,
      Function.apply_add_int_mul_eq_zpow_mul (exp_ne_zero _) hu.2.1, map_add, neg_add,
      Complex.exp_add, Complex.exp_neg (phaseCLM θ₁ θ₂ fun i ↦ (m i : ℝ)), hexp]
    have h₁ : exp (2 * π * θ₁ * I) ^ m 0 ≠ 0 := zpow_ne_zero _ (exp_ne_zero _)
    have h₂ : exp (2 * π * θ₂ * I) ^ m 1 ≠ 0 := zpow_ne_zero _ (exp_ne_zero _)
    field_simp
  obtain ⟨g, hg, hgG⟩ := TauCeti.UnitAddTorus.exists_continuous_comp_coe_eq hGc.continuous hper
  have hlift : (fun x : Fin 2 → ℝ ↦ g fun i ↦ (x i : UnitAddCircle)) = G := funext hgG
  refine ⟨g, mem_smoothFunctions.2 (hlift ▸ hGc), funext fun z ↦ ?_⟩
  obtain ⟨p, rfl⟩ := L.surjective z
  rw [ofTorus_latticeEquiv, hgG, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, exp_zero,
    one_mul]

/-- A function on the torus whose section vanishes is zero. -/
private theorem eq_zero_of_ofTorus_eq_zero (hω : (conj ω₁ * ω₂).im ≠ 0)
    {g : UnitAddTorus (Fin 2) → ℂ} (h : ofTorus hω θ₁ θ₂ g = 0) : g = 0 := by
  funext x
  obtain ⟨p, rfl⟩ := TauCeti.UnitAddTorus.surjective_coe x
  have := congrFun h (latticeEquiv hω p)
  rw [ofTorus_latticeEquiv, Pi.zero_apply, mul_eq_zero] at this
  exact this.resolve_left (exp_ne_zero _)

end Correspondence

/-! ### Bijectivity of `∂bar` -/

/-- **`∂bar` is invertible on a nontrivial flat line over a torus.** Let `ω₁, ω₂` be linearly
independent over `ℝ`, and let `θ₁` or `θ₂` be non-integral, so that the flat line over
`ℂ / (ℤ ω₁ + ℤ ω₂)` with holonomy `exp (2πiθ₁)`, `exp (2πiθ₂)` is nontrivial. Then `∂bar` is a
bijection of its smooth sections: every smooth section `f` is `∂bar u` for exactly one smooth
section `u`. -/
theorem bijective_flatLineConjWirtingerDerivₗ (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ)) :
    Function.Bijective (flatLineConjWirtingerDerivₗ ω₁ ω₂ θ₁ θ₂) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    obtain ⟨g, hg, hgu⟩ := exists_ofTorus_eq hω u.2
    have h0 : ofTorus hω θ₁ θ₂ (torusOp ω₁ ω₂ θ₁ θ₂ g) = 0 := funext fun z ↦ by
      rw [← conjWirtingerDeriv_ofTorus hω hg, hgu]
      exact congrFun (congrArg Subtype.val hu) z
    have hg0 := eq_zero_of_torusOp_eq_zero hω hθ hg
      (eq_zero_of_ofTorus_eq_zero hω h0)
    refine Subtype.ext ?_
    rw [← hgu, hg0]
    funext z
    simp [ofTorus]
  · intro f
    obtain ⟨g, hg, hgf⟩ := exists_ofTorus_eq hω f.2
    obtain ⟨h, hh, rfl⟩ := exists_torusOp_eq hω hθ hg
    refine ⟨⟨ofTorus hω θ₁ θ₂ h, ofTorus_mem hω hh⟩, Subtype.ext (funext fun z ↦ ?_)⟩
    simp [conjWirtingerDeriv_ofTorus hω hh, hgf]

/-- **The leading complex inverse.** For linearly independent `ω₁, ω₂` and nontrivial holonomy,
`∂bar` as a complex-linear automorphism of the smooth sections of the flat line; its inverse
`(flatLineConjWirtingerDerivEquiv hω hθ).symm` solves `∂bar u = f`. -/
def flatLineConjWirtingerDerivEquiv (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ)) :
    flatLineSections ω₁ ω₂ θ₁ θ₂ ≃ₗ[ℂ] flatLineSections ω₁ ω₂ θ₁ θ₂ :=
  LinearEquiv.ofBijective _ (bijective_flatLineConjWirtingerDerivₗ hω hθ)

@[simp]
theorem flatLineConjWirtingerDerivEquiv_apply (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ))
    (u : flatLineSections ω₁ ω₂ θ₁ θ₂) :
    flatLineConjWirtingerDerivEquiv hω hθ u = flatLineConjWirtingerDerivₗ ω₁ ω₂ θ₁ θ₂ u :=
  (rfl)

/-- The inverse of `∂bar` solves the Cauchy–Riemann equation: `∂bar u = f` for
`u = (flatLineConjWirtingerDerivEquiv hω hθ).symm f`. -/
@[simp]
theorem conjWirtingerDeriv_flatLineConjWirtingerDerivEquiv_symm_apply
    (hω : (conj ω₁ * ω₂).im ≠ 0) (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ))
    (f : flatLineSections ω₁ ω₂ θ₁ θ₂) (z : ℂ) :
    conjWirtingerDeriv ((flatLineConjWirtingerDerivEquiv hω hθ).symm f : ℂ → ℂ) z 1 =
      (f : ℂ → ℂ) z := by
  have h := congrFun (congrArg Subtype.val
    ((flatLineConjWirtingerDerivEquiv hω hθ).apply_symm_apply f)) z
  rwa [flatLineConjWirtingerDerivEquiv_apply, coe_flatLineConjWirtingerDerivₗ_apply] at h

/-- **The inverse of `∂bar` is bounded in `L²`.** For linearly independent `ω₁, ω₂` and nontrivial
holonomy, the solution `u` of `∂bar u = f` satisfies, over the fundamental parallelogram in lattice
coordinates, `π² / 2 · (‖θ₁‖ℤ² / |ω₁|² + ‖θ₂‖ℤ² / |ω₂|²) ∫ |u|² ≤ ∫ |f|²`, with
`‖θ‖ℤ = |θ - round θ|`. -/
theorem mul_setIntegral_norm_sq_flatLineConjWirtingerDerivEquiv_symm_apply_le
    (hω : (conj ω₁ * ω₂).im ≠ 0) (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ))
    (f : flatLineSections ω₁ ω₂ θ₁ θ₂) :
    π ^ 2 / 2 * (|θ₁ - round θ₁| ^ 2 / ‖ω₁‖ ^ 2 + |θ₂ - round θ₂| ^ 2 / ‖ω₂‖ ^ 2) *
        ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
          ‖((flatLineConjWirtingerDerivEquiv hω hθ).symm f : ℂ → ℂ) (p.1 * ω₁ + p.2 * ω₂)‖ ^ 2 ≤
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖(f : ℂ → ℂ) (p.1 * ω₁ + p.2 * ω₂)‖ ^ 2 := by
  set u := (flatLineConjWirtingerDerivEquiv hω hθ).symm f
  have h := mul_setIntegral_norm_sq_le_setIntegral_norm_conjWirtingerDeriv_sq
    (u.2.1.of_le (by simp)) hω u.2.2.1 u.2.2.2
  simpa only [u, conjWirtingerDeriv_flatLineConjWirtingerDerivEquiv_symm_apply] using h

/-- **`∂bar` is invertible on the powers and finite covers of a flat line with infinite
holonomy.** Let `ω₁, ω₂` be linearly independent and let `θ₁` or `θ₂` be irrational. For every
nonzero integer `j` and every sublattice basis `a ω₁ + b ω₂, c ω₁ + d ω₂` with `a d - b c ≠ 0`,
`∂bar` is a bijection of the smooth sections of the `j`-th power of the line, pulled back to the
torus of the sublattice. -/
theorem bijective_flatLineConjWirtingerDerivₗ_of_irrational (hθ : Irrational θ₁ ∨ Irrational θ₂)
    (hω : (conj ω₁ * ω₂).im ≠ 0) {j a b c d : ℤ} (hj : j ≠ 0) (hdet : a * d - b * c ≠ 0) :
    Function.Bijective (flatLineConjWirtingerDerivₗ (a * ω₁ + b * ω₂) (c * ω₁ + d * ω₂)
      (j * (a * θ₁ + b * θ₂)) (j * (c * θ₁ + d * θ₂))) :=
  bijective_flatLineConjWirtingerDerivₗ
    (im_conj_intCast_mul_add_mul_intCast_mul_add_ne_zero hω hdet)
    (notMem_range_intCast_or_notMem_range_intCast_of_irrational hθ hj hdet)

end TauCeti
