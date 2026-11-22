/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.OrderAtInfty
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation
import TauCeti.Algebra.BigOperators.ZPow
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.NumberTheory.ModularForms.DedekindEta.Basic

/-!
# Eta quotients and their orders at the cusps

For a level `N` and integer exponents `r_δ` indexed by the positive divisors `δ ∣ N`, the
**eta quotient** is `f(τ) = ∏_{δ ∣ N} η(δ τ) ^ r_δ`. This file computes the leading term of `f`
at every cusp. For `σ = (a b; c d) ∈ SL(2, ℤ)`, representing the cusp `σ ∞ = a / c`,

  `f(σ τ) ~ C · (√(c τ + d)) ^ (∑_δ r_δ) · e(L τ)`  as `Im τ → ∞`,

with `C ≠ 0`, `e(x) = exp(2 π i x)`, the principal square root, and
`L = ∑_{δ ∣ N} gcd(δ, c)² r_δ / (24 δ)`. The exponents need not have even sum, so the weight
`k = ½ ∑_δ r_δ` may be a half-integer. When `k` is an integer, `L` is the order at `i ∞` of
`f ∣[k] σ`, in Mathlib's normalization `UpperHalfPlane.orderAtInfty`, and its sign decides whether
`f ∣[k] σ` is bounded, or tends to zero, at `i ∞`: these are the cusp conditions that make an eta
quotient a modular form or a cusp form.

For a cusp with denominator `d ∣ N`, of width `w = N / gcd(N, d²)` for `Γ₀(N)`
(`TauCeti.conj_T_zpow_mem_Gamma0_iff_width_dvd`), the file proves the arithmetic identity

  `w L = (N / 24) ∑_{δ ∣ N} gcd(d, δ)² r_δ / (gcd(d, N / d) d δ)`,

whose right side is Ligozat's formula. Since `L` is the order in `e(τ)`, `w L` is to be read as
the order in the local parameter `e(τ / w)` of the cusp; that reading is an interpretation, and
no statement about the parameter `e(τ / w)` is formalized here.

Each factor is treated separately. With `A = gcd(δ, c)`, the first column `(δ a, c)` of
`diag(δ, 1) σ` has gcd `A`, so `diag(δ, 1) σ = σ' (A B; 0 δ / A)` with `σ' ∈ SL(2, ℤ)`, and the
transformation law of `η` at `σ'` gives `η(δ σ τ) = C √(c τ + d) η(A (A τ + B) / δ)`. Since
`η(z) ~ e(z / 24)` as `Im z → ∞` (`TauCeti.ModularForm.tendsto_eta_div_exp`), the factor
`η(δ σ τ)` has leading exponent `A² / (24 δ)`.

## Main definitions

* `TauCeti.ModularForm.etaQuotient N r`: the eta quotient `∏_{δ ∣ N} η(δ τ) ^ r δ`.
* `TauCeti.ModularForm.etaQuotientOrder N r c`: the order `L` at a cusp with denominator `c`.

## Main results

* `TauCeti.ModularForm.etaQuotient_ne_zero`, `TauCeti.ModularForm.mdifferentiable_etaQuotient`:
  an eta quotient is nonvanishing and holomorphic on the upper half-plane.
* `TauCeti.ModularForm.exists_eta_natCast_mul_smul_eq`:
  `η(δ σ τ) = C √(c τ + d) η(A (A τ + B) / δ)` with `A = gcd(δ, c)`.
* `TauCeti.ModularForm.exists_tendsto_etaQuotient_smul_div`: the leading term of `f(σ τ)`.
* `TauCeti.ModularForm.orderAtInfty_etaQuotient_slash`: `orderAtInfty (f ∣[k] σ) = L`.
* `TauCeti.ModularForm.isBoundedAtImInfty_etaQuotient_slash_iff`,
  `TauCeti.ModularForm.isZeroAtImInfty_etaQuotient_slash_iff`: `f ∣[k] σ` is bounded at `i ∞`
  exactly when `0 ≤ L`, and tends to zero exactly when `0 < L`.
* `TauCeti.ModularForm.natCast_div_gcd_mul_etaQuotientOrder`: `w L` equals Ligozat's expression.
* `TauCeti.ModularForm.etaQuotientOrder_gcd`: `L` depends on `c` only through `gcd(N, c)`.

## References

* K. Ono, *The Web of Modularity*, Theorems 1.64 and 1.65.
* G. Ligozat, *Courbes modulaires de genre 1*, Bull. Soc. Math. France Mém. **43** (1975).
* J. Rouse and J. J. Webb, *On spaces of modular forms spanned by eta-quotients*,
  Adv. Math. **272** (2015), §1.
-/

public section

open Complex Filter Topology
open UpperHalfPlane (atImInfty IsBoundedAtImInfty IsZeroAtImInfty orderAtInfty)
open scoped Real ModularForm MatrixGroups UpperHalfPlane Manifold

namespace TauCeti.ModularForm

/-! ### `η(δ τ)` at an arbitrary cusp -/

/-- The principal square root `√(c τ + d)` does not vanish on `ℍ`. -/
private theorem sqrt_denom_ne_zero (σ : SL(2, ℤ)) (τ : ℍ) :
    Complex.sqrt ((σ 1 0 : ℂ) * τ + σ 1 1) ≠ 0 :=
  Complex.sqrt_eq_zero_iff.not.2 (UpperHalfPlane.denom_ne_zero σ τ)

/-- The integer data of the factorization `diag(δ, 1) σ = σ' (A B; 0 D)`: with `A = gcd(δ, c)`,
`δ = A D` with `D > 0`, `c = A c'`, and Bézout coefficients `A = δ x + c y`. -/
private theorem exists_gcd_decomposition (δ : ℕ) [NeZero δ] (c : ℤ) :
    ∃ D c' x y : ℤ, 0 < D ∧ (δ : ℤ) = Nat.gcd δ c.natAbs * D ∧
      c = Nat.gcd δ c.natAbs * c' ∧ (Nat.gcd δ c.natAbs : ℤ) = δ * x + c * y := by
  have hAg : (Nat.gcd δ c.natAbs : ℤ) = Int.gcd δ c := by simp [Int.gcd]
  obtain ⟨D, hD⟩ : (Nat.gcd δ c.natAbs : ℤ) ∣ δ := by rw [hAg]; exact Int.gcd_dvd_left ..
  obtain ⟨c', hc'⟩ : (Nat.gcd δ c.natAbs : ℤ) ∣ c := by rw [hAg]; exact Int.gcd_dvd_right ..
  have hδ : (0 : ℤ) < δ := by exact_mod_cast NeZero.pos δ
  refine ⟨D, c', Int.gcdA δ c, Int.gcdB δ c,
    pos_of_mul_pos_right (hD ▸ hδ) (Int.natCast_nonneg _), hD, hc', ?_⟩
  rw [hAg]
  exact Int.gcd_eq_gcd_ab δ c

/-- The automorphy factor of `σ' = (D a, x δ b - y; c', x d)` at `w = A (A τ + y d) / δ` is
`(c τ + d) / D`. -/
private theorem denom_eq_of_gcd_decomposition {A D δ c c' d x y τ : ℂ} (hδ : δ = A * D)
    (hc : c = A * c') (hbez : A = δ * x + c * y) (hA : A ≠ 0) (hD : D ≠ 0) :
    c' * (A * (A * τ + y * d) / δ) + x * d = D⁻¹ * (c * τ + d) := by
  have hδ0 : δ ≠ 0 := hδ ▸ mul_ne_zero hA hD
  field_simp
  linear_combination (-(τ * c) - d) * hδ + (-(τ * A * D) - D * d * y) * hc - D * d * hbez

/-- `σ' = (D a, x δ b - y; c', x d)` maps `w = A (A τ + y d) / δ` to `δ σ τ`. -/
private theorem smul_eq_of_gcd_decomposition {A D δ a b c d x y τ : ℂ} (hδ : δ = A * D)
    (hbez : A = δ * x + c * y) (hdet : a * d - b * c = 1) (hA : A ≠ 0)
    (hD : D ≠ 0) (hj : c * τ + d ≠ 0) :
    (D * a * (A * (A * τ + y * d) / δ) + (x * δ * b - y)) / (D⁻¹ * (c * τ + d)) =
      δ * ((a * τ + b) / (c * τ + d)) := by
  have hδ0 : δ ≠ 0 := hδ ▸ mul_ne_zero hA hD
  have hj' : τ * c + d ≠ 0 := by rwa [mul_comm]
  field_simp
  linear_combination (-(a * τ * (δ + A * D)) - δ * b - D * a * y * d) * hδ +
    (D * δ * y) * hdet - (D * δ * b) * hbez

/-- **`η(δ τ)` at the cusp `σ ∞`.** For `δ ≥ 1` and `σ = (a b; c d) ∈ SL(2, ℤ)`, put
`A = gcd(δ, c)`. Then `η(δ σ τ) = C √(c τ + d) η(A (A τ + B) / δ)` on the upper half-plane, for
some nonzero constant `C` and integer `B`, with the principal square root. -/
theorem exists_eta_natCast_mul_smul_eq (δ : ℕ) [NeZero δ] (σ : SL(2, ℤ)) :
    ∃ (C : ℂ) (B : ℤ), C ≠ 0 ∧ ∀ τ : ℍ,
      η (δ * ((σ • τ : ℍ) : ℂ)) = C * Complex.sqrt ((σ 1 0 : ℂ) * τ + σ 1 1) *
        η (Nat.gcd δ (σ 1 0).natAbs * (Nat.gcd δ (σ 1 0).natAbs * (τ : ℂ) + B) / δ) := by
  set A := Nat.gcd δ (σ 1 0).natAbs
  obtain ⟨D, c', x, y, hD, hδ, hc, hbez⟩ := exists_gcd_decomposition δ (σ 1 0)
  have hA : (A : ℂ) ≠ 0 := by exact_mod_cast (Nat.gcd_pos_of_pos_left _ (NeZero.pos δ)).ne'
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hdet : σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have := σ.det_coe
    rwa [Matrix.det_fin_two] at this
  -- `diag(δ, 1) σ = σ' (A B; 0 D)` with `B = y d`.
  let σ' : SL(2, ℤ) := ⟨!![D * σ 0 0, x * δ * σ 0 1 - y; c', x * σ 1 1], by
    rw [Matrix.det_fin_two_of]
    refine mul_left_cancel₀ (a := (A : ℤ)) (by exact_mod_cast hA) ?_
    linear_combination (-(σ 0 0 * x * σ 1 1)) * hδ + (x * δ * σ 0 1 - y) * hc +
      (δ * x) * hdet - hbez⟩
  refine ⟨etaMultiplier σ' * Complex.sqrt (D : ℂ)⁻¹, y * σ 1 1,
    mul_ne_zero (etaMultiplier_ne_zero σ') (Complex.sqrt_eq_zero_iff.not.2 (inv_ne_zero hD0)),
    fun τ ↦ ?_⟩
  let w : ℍ := ⟨A * (A * τ + (y * σ 1 1 : ℤ)) / δ, by
    have : 0 < (A : ℝ) := by exact_mod_cast Nat.gcd_pos_of_pos_left _ (NeZero.pos δ)
    have : 0 < (δ : ℝ) := by exact_mod_cast NeZero.pos δ
    simp only [Complex.div_natCast_im, Complex.mul_im, Complex.add_im, Complex.natCast_re,
      Complex.natCast_im, Complex.intCast_im, UpperHalfPlane.coe_im, zero_mul, add_zero]
    positivity⟩
  have hwC : (w : ℂ) = A * (A * τ + (y * σ 1 1 : ℤ)) / δ := rfl
  have hδC : (δ : ℂ) = A * D := by exact_mod_cast hδ
  have hcC : (σ 1 0 : ℂ) = A * c' := by exact_mod_cast hc
  have hbezC : (A : ℂ) = δ * x + σ 1 0 * y := by exact_mod_cast hbez
  have hden : (σ' 1 0 : ℂ) * w + σ' 1 1 = (D : ℂ)⁻¹ * ((σ 1 0 : ℂ) * τ + σ 1 1) := by
    simpa [σ', hwC] using denom_eq_of_gcd_decomposition (d := (σ 1 1 : ℂ)) (τ := τ) hδC hcC hbezC
      hA hD0
  have hsmul : ((σ' • w : ℍ) : ℂ) = δ * ((σ • τ : ℍ) : ℂ) := by
    have hτ : (σ 1 0 : ℂ) * τ + σ 1 1 ≠ 0 := UpperHalfPlane.denom_ne_zero σ τ
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
    rw [hden]
    simpa [σ', hwC] using smul_eq_of_gcd_decomposition (τ := τ) hδC hbezC
      (by exact_mod_cast hdet) hA hD0 hτ
  have hsqrt := Complex.sqrt_ofReal_mul (r := (D : ℝ)⁻¹) (by positivity)
    ((σ 1 0 : ℂ) * τ + σ 1 1)
  push_cast at hsqrt
  rw [← hsmul, eta_smul σ' w, hden, hsqrt, hwC]
  ring

/-- `η(δ σ τ) ~ C √(c τ + d) e(gcd(δ, c)² τ / (24 δ))` as `Im τ → ∞`, with `C ≠ 0`. -/
private theorem exists_tendsto_eta_natCast_mul_smul_div (δ : ℕ) [NeZero δ] (σ : SL(2, ℤ)) :
    ∃ C : ℂ, C ≠ 0 ∧ Tendsto (fun τ : ℍ ↦ η (δ * ((σ • τ : ℍ) : ℂ)) /
      (Complex.sqrt ((σ 1 0 : ℂ) * τ + σ 1 1) *
        cexp (2 * π * I * ((Nat.gcd δ (σ 1 0).natAbs ^ 2 / (24 * δ) : ℚ) : ℂ) * τ)))
      atImInfty (𝓝 C) := by
  obtain ⟨C, B, hC, h⟩ := exists_eta_natCast_mul_smul_eq δ σ
  set A := Nat.gcd δ (σ 1 0).natAbs
  have hA : 0 < (A : ℝ) := by exact_mod_cast Nat.gcd_pos_of_pos_left _ (NeZero.pos δ)
  have hδ : 0 < (δ : ℝ) := by exact_mod_cast NeZero.pos δ
  set u : ℍ → ℂ := fun τ ↦ A * (A * τ + B) / δ
  have hu : Tendsto u atImInfty (comap im atTop) := by
    refine tendsto_comap_iff.2 (((tendsto_comap : Tendsto UpperHalfPlane.im atImInfty atTop)
      |>.const_mul_atTop (by positivity : 0 < (A : ℝ) * A / δ)).congr fun τ ↦ ?_)
    simp only [Function.comp_apply, u, Complex.div_natCast_im, Complex.mul_im, Complex.add_im,
      Complex.natCast_re, Complex.natCast_im, Complex.intCast_im, UpperHalfPlane.coe_im,
      zero_mul, add_zero]
    ring
  set E : ℂ := cexp (2 * π * I * (A * B / (24 * δ)))
  refine ⟨C * E, mul_ne_zero hC (exp_ne_zero _), ?_⟩
  have := (tendsto_eta_div_exp.comp hu).const_mul (C * E)
  rw [mul_one] at this
  refine this.congr fun τ ↦ ?_
  have hexp : cexp (2 * π * I * u τ / 24) =
      cexp (2 * π * I * ((A ^ 2 / (24 * δ) : ℚ) : ℂ) * τ) * E := by
    rw [← exp_add]
    congr 1
    simp only [u]
    push_cast
    field_simp
  have key : ∀ s e x : ℂ, s ≠ 0 → e ≠ 0 → C * E * (x / (e * E)) = C * s * x / (s * e) :=
    fun s e x hs he ↦ by
      have hE : E ≠ 0 := exp_ne_zero _
      field_simp
  rw [Function.comp_apply, h τ, hexp]
  exact key _ _ _ (sqrt_denom_ne_zero σ τ) (exp_ne_zero _)

/-! ### Eta quotients -/

/-- The **eta quotient** `∏_{δ ∣ N} η(δ τ) ^ r δ` of level `N` with integer exponents `r δ`. -/
noncomputable def etaQuotient (N : ℕ) (r : ℕ → ℤ) (τ : ℂ) : ℂ :=
  ∏ δ ∈ N.divisors, η (δ * τ) ^ r δ

theorem etaQuotient_apply (N : ℕ) (r : ℕ → ℤ) (τ : ℂ) :
    etaQuotient N r τ = ∏ δ ∈ N.divisors, η (δ * τ) ^ r δ :=
  (rfl)

/-- An eta quotient does not vanish on the upper half-plane. -/
theorem etaQuotient_ne_zero (N : ℕ) (r : ℕ → ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    etaQuotient N r τ ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun δ hδ ↦ zpow_ne_zero _ <| _root_.ModularForm.eta_ne_zero <| by
    simpa using mul_pos (Nat.cast_pos.2 (Nat.pos_of_mem_divisors hδ)) hτ

/-- An eta quotient is complex differentiable at every point of the upper half-plane. -/
theorem differentiableAt_etaQuotient (N : ℕ) (r : ℕ → ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (etaQuotient N r) τ := by
  refine DifferentiableAt.fun_finsetProd fun δ hδ ↦ ?_
  have hδτ : 0 < ((δ : ℂ) * τ).im := by
    simpa using mul_pos (Nat.cast_pos.2 (Nat.pos_of_mem_divisors hδ)) hτ
  exact ((_root_.ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hδτ).comp τ
    (differentiableAt_id.const_mul _)).zpow
      (Or.inl (_root_.ModularForm.eta_ne_zero hδτ))

/-- An eta quotient is holomorphic on the upper half-plane. -/
theorem mdifferentiable_etaQuotient (N : ℕ) (r : ℕ → ℤ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ ↦ etaQuotient N r τ) := fun τ ↦
  (differentiableAt_etaQuotient N r τ.im_pos).mdifferentiableAt.comp τ τ.mdifferentiable_coe

/-- **The order of an eta quotient at a cusp**, `∑_{δ ∣ N} gcd(δ, c)² r δ / (24 δ)`. For
`σ ∈ SL(2, ℤ)` with lower-left entry `c` it is the order at `i ∞`, in the parameter `e(τ)`, of
`etaQuotient N r` transported by `σ` (`orderAtInfty_etaQuotient_slash`); this is the order of
`etaQuotient N r` at the cusp `σ ∞`. For `c ∣ N`, `natCast_div_gcd_mul_etaQuotientOrder` shows
that `w` times this, with `w = N / gcd(N, c²)` the width of that cusp of `Γ₀(N)`, equals
Ligozat's expression; it is read as the order in the local parameter `e(τ / w)`, but that
reading is not formalized. -/
def etaQuotientOrder (N : ℕ) (r : ℕ → ℤ) (c : ℤ) : ℚ :=
  ∑ δ ∈ N.divisors, (Nat.gcd δ c.natAbs ^ 2 * r δ : ℚ) / (24 * δ)

theorem etaQuotientOrder_def (N : ℕ) (r : ℕ → ℤ) (c : ℤ) :
    etaQuotientOrder N r c = ∑ δ ∈ N.divisors, (Nat.gcd δ c.natAbs ^ 2 * r δ : ℚ) / (24 * δ) :=
  (rfl)

/-- At the cusp `∞ = 1 / 0`, the order of `∏_{δ ∣ N} η(δ τ) ^ r δ` is `∑_{δ ∣ N} δ r δ / 24`. -/
@[simp]
theorem etaQuotientOrder_zero (N : ℕ) (r : ℕ → ℤ) :
    etaQuotientOrder N r 0 = ∑ δ ∈ N.divisors, (δ * r δ : ℚ) / 24 := by
  refine Finset.sum_congr rfl fun δ hδ ↦ ?_
  have : (δ : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hδ).ne'
  rw [Int.natAbs_zero, Nat.gcd_zero_right]
  field_simp

/-- The order of an eta quotient at a cusp depends on its denominator `c` only through
`gcd(N, c)`, a divisor of `N` when `N ≠ 0`. -/
theorem etaQuotientOrder_gcd (N : ℕ) (r : ℕ → ℤ) (c : ℤ) :
    etaQuotientOrder N r (N.gcd c.natAbs) = etaQuotientOrder N r c := by
  simp only [etaQuotientOrder_def, Int.natAbs_natCast]
  refine Finset.sum_congr rfl fun δ hδ ↦ ?_
  rw [← Nat.gcd_assoc, Nat.gcd_eq_left (Nat.dvd_of_mem_divisors hδ)]

/-- **Ligozat's formula**, as an identity in `ℚ`. For `d ∣ N` and `w = N / gcd(N, d²)`,
`w · etaQuotientOrder N r d = (N / 24) ∑_{δ ∣ N} gcd(d, δ)² r δ / (gcd(d, N / d) d δ)`.

Interpretation (not formalized here): `etaQuotientOrder N r d` is the order of
`∏_{δ ∣ N} η(δ τ) ^ r δ` in the parameter `e(τ)` at a cusp `a / d`
(`orderAtInfty_etaQuotient_slash`), and `w` is the width of that cusp of `Γ₀(N)`
(`TauCeti.conj_T_zpow_mem_Gamma0_iff_width_dvd`), so the left side is read as the order in the
local parameter `e(τ / w)`. -/
theorem natCast_div_gcd_mul_etaQuotientOrder (N : ℕ) (r : ℕ → ℤ) {d : ℕ} (hd : d ∣ N) :
    ((N / Nat.gcd N (d ^ 2) : ℕ) : ℚ) * etaQuotientOrder N r d = N / 24 *
      ∑ δ ∈ N.divisors, (Nat.gcd d δ ^ 2 * r δ : ℚ) / (Nat.gcd d (N / d) * d * δ) := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [etaQuotientOrder]
  obtain ⟨m, rfl⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (left_ne_zero_of_mul hN)
  have hg : Nat.gcd (d * m) (d ^ 2) = d * Nat.gcd d m := by
    rw [sq, Nat.gcd_mul_left, Nat.gcd_comm]
  have hg0 : (Nat.gcd d m : ℚ) ≠ 0 := by exact_mod_cast (Nat.gcd_pos_of_pos_left _ hd0).ne'
  rw [Nat.mul_div_cancel_left m hd0, hg, Nat.mul_div_mul_left _ _ hd0,
    Nat.cast_div (Nat.gcd_dvd_right d m) hg0, etaQuotientOrder, Int.natAbs_natCast,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun δ hδ ↦ ?_
  have : (δ : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hδ).ne'
  have : (d : ℚ) ≠ 0 := by exact_mod_cast hd0.ne'
  rw [Nat.gcd_comm δ d]
  push_cast
  field_simp

/-- **The leading term of an eta quotient at a cusp.** For `σ = (a b; c d) ∈ SL(2, ℤ)`,
`f(σ τ) ~ C (√(c τ + d)) ^ (∑_δ r δ) e(L τ)` as `Im τ → ∞` for some `C ≠ 0`, where
`f = etaQuotient N r`, `e(x) = exp(2 π i x)` and `L = etaQuotientOrder N r c`. -/
theorem exists_tendsto_etaQuotient_smul_div (N : ℕ) (r : ℕ → ℤ) (σ : SL(2, ℤ)) :
    ∃ C : ℂ, C ≠ 0 ∧ Tendsto (fun τ : ℍ ↦ etaQuotient N r (σ • τ : ℍ) /
      (Complex.sqrt ((σ 1 0 : ℂ) * τ + σ 1 1) ^ (∑ δ ∈ N.divisors, r δ) *
        cexp (2 * π * I * etaQuotientOrder N r (σ 1 0) * τ))) atImInfty (𝓝 C) := by
  have key (δ : ℕ) (hδ : δ ∈ N.divisors) : ∃ C : ℂ, C ≠ 0 ∧ Tendsto (fun τ : ℍ ↦
      η (δ * ((σ • τ : ℍ) : ℂ)) / (Complex.sqrt ((σ 1 0 : ℂ) * τ + σ 1 1) *
        cexp (2 * π * I * ((Nat.gcd δ (σ 1 0).natAbs ^ 2 / (24 * δ) : ℚ) : ℂ) * τ)))
      atImInfty (𝓝 C) :=
    haveI : NeZero δ := ⟨(Nat.pos_of_mem_divisors hδ).ne'⟩
    exists_tendsto_eta_natCast_mul_smul_div δ σ
  choose! C hC hT using key
  refine ⟨∏ δ ∈ N.divisors, C δ ^ r δ,
    Finset.prod_ne_zero_iff.2 fun δ hδ ↦ zpow_ne_zero _ (hC δ hδ), ?_⟩
  refine (tendsto_finsetProd _ fun δ hδ ↦ (hT δ hδ).zpow₀ (r δ) (Or.inl (hC δ hδ))).congr
    fun τ ↦ ?_
  set s := Complex.sqrt ((σ 1 0 : ℂ) * τ + σ 1 1)
  have hs : s ≠ 0 := sqrt_denom_ne_zero σ τ
  have hexp : cexp (2 * π * I * etaQuotientOrder N r (σ 1 0) * τ) = ∏ δ ∈ N.divisors,
      cexp (2 * π * I * ((Nat.gcd δ (σ 1 0).natAbs ^ 2 / (24 * δ) : ℚ) : ℂ) * τ) ^ r δ := by
    simp_rw [← exp_intCast_mul, ← exp_sum, etaQuotientOrder, Rat.cast_sum, Finset.mul_sum,
      Finset.sum_mul]
    refine congrArg cexp (Finset.sum_congr rfl fun δ _ ↦ ?_)
    push_cast
    ring
  rw [etaQuotient_apply, hexp, ← Finset.prod_zpow_eq_zpow_sum_of_isUnit N.divisors hs.isUnit r,
    ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun δ _ ↦ by rw [div_zpow, mul_zpow]

/-- `τ ↦ f(σ τ) / (√(c τ + d)) ^ (∑_δ r δ)` is comparable to `e^{-2 π L Im τ}` at `i ∞`, where
`f = etaQuotient N r` and `L = etaQuotientOrder N r c`. -/
private theorem isTheta_etaQuotient_smul_div (N : ℕ) (r : ℕ → ℤ) (σ : SL(2, ℤ)) :
    (fun τ : ℍ ↦ etaQuotient N r (σ • τ : ℍ) /
      Complex.sqrt ((σ 1 0 : ℂ) * τ + σ 1 1) ^ (∑ δ ∈ N.divisors, r δ)) =Θ[atImInfty]
      fun τ ↦ Real.exp (-(2 * π * τ.im * etaQuotientOrder N r (σ 1 0))) := by
  obtain ⟨C, hC, hT⟩ := exists_tendsto_etaQuotient_smul_div N r σ
  refine (Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero (hT.congr fun τ ↦ by rw [div_div])
    hC).symm.trans (Asymptotics.IsTheta.of_norm_eventuallyEq (Eventually.of_forall fun τ ↦ ?_))
  simp only [norm_exp]
  congr 1
  simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero, I_re, mul_im,
    zero_mul, add_zero, I_im, mul_one, sub_self, ratCast_re, ratCast_im, UpperHalfPlane.coe_re,
    zero_add, UpperHalfPlane.coe_im, zero_sub, neg_inj]
  ring

/-- For integral `k` with `∑_δ r δ = 2 k`, `etaQuotient N r ∣[k] σ` is
`τ ↦ f(σ τ) / (√(c τ + d)) ^ (∑_δ r δ)`. -/
private theorem etaQuotient_slash_eq (N : ℕ) (r : ℕ → ℤ) {k : ℤ}
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (σ : SL(2, ℤ)) :
    (fun τ : ℍ ↦ etaQuotient N r τ) ∣[k] σ = fun τ : ℍ ↦ etaQuotient N r (σ • τ : ℍ) /
      Complex.sqrt ((σ 1 0 : ℂ) * τ + σ 1 1) ^ (∑ δ ∈ N.divisors, r δ) := by
  ext τ
  rw [ModularForm.SL_slash_apply, hk, zpow_mul, zpow_ofNat, Complex.sq_sqrt, zpow_neg,
    div_eq_mul_inv]
  simp [UpperHalfPlane.denom]

/-- **The order of an eta quotient at a cusp.** For integral `k` with `∑_δ r δ = 2 k` and
`σ ∈ SL(2, ℤ)` with lower-left entry `c`, the order at `i ∞` of `etaQuotient N r ∣[k] σ` is
`∑_{δ ∣ N} gcd(δ, c)² r δ / (24 δ)`. -/
theorem orderAtInfty_etaQuotient_slash (N : ℕ) (r : ℕ → ℤ) {k : ℤ}
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (σ : SL(2, ℤ)) :
    orderAtInfty ((fun τ : ℍ ↦ etaQuotient N r τ) ∣[k] σ) =
      ((etaQuotientOrder N r (σ 1 0) : ℝ) : EReal) := by
  rw [etaQuotient_slash_eq N r hk σ]
  exact UpperHalfPlane.orderAtInfty_eq_of_isTheta (isTheta_etaQuotient_smul_div N r σ)

/-- For integral `k` with `∑_δ r δ = 2 k`, `etaQuotient N r ∣[k] σ` is bounded at `i ∞` exactly
when the order of the eta quotient at the cusp `σ ∞` is nonnegative. -/
theorem isBoundedAtImInfty_etaQuotient_slash_iff (N : ℕ) (r : ℕ → ℤ) {k : ℤ}
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (σ : SL(2, ℤ)) :
    IsBoundedAtImInfty ((fun τ : ℍ ↦ etaQuotient N r τ) ∣[k] σ) ↔
      0 ≤ etaQuotientOrder N r (σ 1 0) := by
  refine ⟨fun h ↦ by exact_mod_cast orderAtInfty_etaQuotient_slash N r hk σ ▸
    h.orderAtInfty_nonneg, fun h ↦ ?_⟩
  rw [etaQuotient_slash_eq N r hk σ]
  refine (isTheta_etaQuotient_smul_div N r σ).isBigO.trans (Asymptotics.IsBigO.of_bound 1 ?_)
  filter_upwards with τ
  simp only [Real.norm_eq_abs, Real.abs_exp, Pi.one_apply, norm_one, one_mul,
    Real.exp_le_one_iff, Left.neg_nonpos_iff]
  have := τ.im_pos
  positivity

/-- For integral `k` with `∑_δ r δ = 2 k`, `etaQuotient N r ∣[k] σ` tends to zero at `i ∞`
exactly when the order of the eta quotient at the cusp `σ ∞` is positive. -/
theorem isZeroAtImInfty_etaQuotient_slash_iff (N : ℕ) (r : ℕ → ℤ) {k : ℤ}
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (σ : SL(2, ℤ)) :
    IsZeroAtImInfty ((fun τ : ℍ ↦ etaQuotient N r τ) ∣[k] σ) ↔
      0 < etaQuotientOrder N r (σ 1 0) := by
  have hΘ := isTheta_etaQuotient_smul_div N r σ
  rw [etaQuotient_slash_eq N r hk σ] at *
  refine ⟨fun h ↦ ?_, fun h ↦ hΘ.isBigO.trans_tendsto ?_⟩
  · refine lt_of_le_of_ne ((isBoundedAtImInfty_etaQuotient_slash_iff N r hk σ).1 ?_) fun h0 ↦ ?_
    · rw [etaQuotient_slash_eq N r hk σ]
      exact h.isBoundedAtImInfty
    have h1 := hΘ.isBigO_symm.trans_tendsto h
    simp only [← h0, Rat.cast_zero, mul_zero, neg_zero, Real.exp_zero] at h1
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)
  · have hlin : Tendsto (fun τ : ℍ ↦ -(2 * π * etaQuotientOrder N r (σ 1 0)) * τ.im) atImInfty
        atBot :=
      (tendsto_comap : Tendsto UpperHalfPlane.im atImInfty atTop).const_mul_atTop_of_neg
        (by simp [Real.pi_pos, h])
    exact (Real.tendsto_exp_atBot.comp hlin).congr fun τ ↦ by
      simp only [neg_mul, Function.comp_apply, Real.exp_eq_exp, neg_inj]
      ring

end TauCeti.ModularForm
