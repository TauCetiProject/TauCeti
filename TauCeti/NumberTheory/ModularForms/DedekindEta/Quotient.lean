/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation
public import TauCeti.NumberTheory.ModularForms.Degeneracy
import TauCeti.Algebra.BigOperators.ZPow
import TauCeti.Analysis.Complex.Sqrt

/-!
# Eta quotients and their transformation under `Γ₀(N)`

For a level `N` and integer exponents `r_δ` at the divisors `δ ∣ N`, the eta quotient is
`f(τ) = ∏_{δ ∣ N} η(δ τ) ^ {r_δ}`. With `k = ½ ∑_δ r_δ`, the criterion of Newman,
Gordon–Hughes and Ligozat decides when `f` is a modular form of weight `k` on `Γ₀(N)` with a
quadratic nebentypus, and computes its orders at the cusps. This file proves the reduction at the
heart of that criterion: the transformation of `f` under `Γ₀(N)` is a product of eta multipliers.

For `γ = (a b; c d) ∈ Γ₀(N)` and `δ ∣ N`, the matrix `γ_δ = (a, δ b; c / δ, d) ∈ SL(2, ℤ)` is the
conjugate of `γ` by `diag(δ, 1)` (`TauCeti.conjScaleGamma0`). It sends `δ τ` to `δ · γ τ` and has
the same automorphy factor `c τ + d` at `δ τ` as `γ` at `τ`. By the transformation law of `η`,
`η(δ · γ τ) = ε(γ_δ) √(c τ + d) η(δ τ)`, so
`f(γ τ) = (∏_δ ε(γ_δ) ^ {r_δ}) · √(c τ + d) ^ {∑_δ r_δ} · f(τ)`.
When `∑_δ r_δ = 2 k` is even this is the slash relation `f ∣[k] γ = (∏_δ ε(γ_δ) ^ {r_δ}) • f`,
and the multiplier `γ ↦ ∏_δ ε(γ_δ) ^ {r_δ}` is a character of `Γ₀(N)` with values in the 24th roots
of unity. Evaluating it as a Kronecker symbol in `d` is the arithmetic half of the criterion.

The file also records that `f` is holomorphic and nowhere zero on the upper half-plane, and its
translation law `f(τ + n) = e^{π i n (∑_δ δ r_δ) / 12} f(τ)`.

## Main definitions

* `TauCeti.ModularForm.etaQuotient N r`: the eta quotient `τ ↦ ∏_{δ ∣ N} η(δ τ) ^ {r δ}`.
* `TauCeti.conjScaleGamma0 hδ γ`: the conjugate `γ_δ = (a, δ b; c / δ, d)` of `γ ∈ Γ₀(N)` by
  `diag(δ, 1)`, for `δ ∣ N`.
* `TauCeti.ModularForm.etaQuotientMultiplier N r γ`: the multiplier `∏_{δ ∣ N} ε(γ_δ) ^ {r δ}` at
  `γ ∈ Γ₀(N)`.

## Main results

* `TauCeti.ModularForm.etaQuotient_ne_zero`, `TauCeti.ModularForm.differentiableAt_etaQuotient`,
  `TauCeti.ModularForm.mdifferentiable_etaQuotient`: `f` is nonvanishing and holomorphic on the
  upper half-plane.
* `TauCeti.ModularForm.etaQuotient_add_intCast`: the translation law.
* `TauCeti.ModularForm.eta_natCast_mul_smul`: `η(δ · γ τ) = ε(γ_δ) √(c τ + d) η(δ τ)` when
  `δ ∣ c`.
* `TauCeti.ModularForm.etaQuotient_smul`: the transformation of `f` under `γ ∈ Γ₀(N)`.
* `TauCeti.ModularForm.etaQuotient_slash`: `f ∣[k] γ = (∏_δ ε(γ_δ) ^ {r_δ}) • f` when
  `∑_δ r_δ = 2 k`.
* `TauCeti.ModularForm.etaQuotientMultiplier_pow_twentyFour`,
  `TauCeti.ModularForm.etaQuotientMultiplier_one`, `TauCeti.ModularForm.etaQuotientMultiplier_mul`:
  the multiplier is a 24th root of unity, and multiplicative when `∑_δ r_δ` is even.

## References

* K. Ono, *The Web of Modularity: Arithmetic of the Coefficients of Modular Forms and
  q-series*, CBMS Regional Conference Series in Mathematics 102, Theorems 1.64 and 1.65.
* T. M. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, 2nd ed., GTM 41,
  Theorem 3.4.
-/

public section

open Complex Finset CongruenceSubgroup
open scoped Real ModularForm MatrixGroups Manifold UpperHalfPlane

namespace TauCeti.ModularForm

/-- The **eta quotient** `f(τ) = ∏_{δ ∣ N} η(δ τ) ^ {r δ}` of level `N` with integer exponents
`r δ` at the divisors `δ` of `N`. It is holomorphic and nowhere zero on the upper half-plane
(`differentiableAt_etaQuotient`, `etaQuotient_ne_zero`), and transforms under `Γ₀(N)` by a
product of eta multipliers (`etaQuotient_smul`). -/
noncomputable def etaQuotient (N : ℕ) (r : ℕ → ℤ) (τ : ℂ) : ℂ :=
  ∏ δ ∈ N.divisors, η (δ * τ) ^ r δ

/-- The defining product of the eta quotient. -/
theorem etaQuotient_def (N : ℕ) (r : ℕ → ℤ) (τ : ℂ) :
    etaQuotient N r τ = ∏ δ ∈ N.divisors, η (δ * τ) ^ r δ := (rfl)

/-- A positive integer multiple of a point of the upper half-plane lies in the upper half-plane. -/
private theorem im_natCast_mul_pos {δ : ℕ} (hδ : 0 < δ) {τ : ℂ} (hτ : 0 < τ.im) :
    0 < ((δ : ℂ) * τ).im := by
  simpa using mul_pos (Nat.cast_pos.2 hδ : (0 : ℝ) < δ) hτ

/-- The eta quotient does not vanish on the upper half-plane. -/
theorem etaQuotient_ne_zero (N : ℕ) (r : ℕ → ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    etaQuotient N r τ ≠ 0 :=
  prod_ne_zero_iff.2 fun _ hδ ↦ zpow_ne_zero _ <|
    _root_.ModularForm.eta_ne_zero (im_natCast_mul_pos (Nat.pos_of_mem_divisors hδ) hτ)

/-- The eta quotient is holomorphic at every point of the upper half-plane. -/
theorem differentiableAt_etaQuotient (N : ℕ) (r : ℕ → ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (etaQuotient N r) τ := by
  rw [funext (etaQuotient_def N r)]
  refine DifferentiableAt.fun_finsetProd fun δ hδ ↦ ?_
  have hδτ := im_natCast_mul_pos (Nat.pos_of_mem_divisors hδ) hτ
  exact ((_root_.ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hδτ).comp τ
    ((differentiableAt_id.const_mul _))).zpow (Or.inl (_root_.ModularForm.eta_ne_zero hδτ))

/-- The eta quotient, as a function on the upper half-plane, is holomorphic. -/
theorem mdifferentiable_etaQuotient (N : ℕ) (r : ℕ → ℤ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun τ : ℍ ↦ etaQuotient N r τ := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  refine (differentiableAt_etaQuotient N r hz).differentiableWithinAt.congr (fun w hw ↦ ?_) ?_
  · simp [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  · simp [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-- **The translation law of an eta quotient**:
`f(τ + n) = e^{π i n (∑_{δ ∣ N} δ r_δ) / 12} f(τ)` for every integer `n`. -/
theorem etaQuotient_add_intCast (N : ℕ) (r : ℕ → ℤ) (τ : ℂ) (n : ℤ) :
    etaQuotient N r (τ + n) =
      cexp (π * I * n * (∑ δ ∈ N.divisors, (δ * r δ : ℤ)) / 12) * etaQuotient N r τ := by
  have h (δ : ℕ) : η (δ * (τ + n)) ^ r δ =
      cexp (π * I * n * (δ * r δ : ℤ) / 12) * η (δ * τ) ^ r δ := by
    have hδ : (δ : ℂ) * (τ + n) = δ * τ + ((δ * n : ℤ) : ℂ) := by
      push_cast
      ring
    rw [hδ, eta_add_intCast, mul_zpow, ← Complex.exp_int_mul]
    congr 2
    push_cast
    ring
  simp only [etaQuotient_def, h, prod_mul_distrib, ← Complex.exp_sum, Int.cast_sum, mul_sum,
    sum_div]

/-! ### The transformation under `Γ₀(N)` -/

/-- **The transformation of `η(δ τ)`**: if `δ > 0` divides the lower-left entry `c = δ c'` of
`γ = (a b; c d) ∈ SL(2, ℤ)`, then `η(δ · γ τ) = ε(γ_δ) √(c τ + d) η(δ τ)` on the upper half-plane,
where `γ_δ = (a, δ b; c', d)` is the conjugate `conjScale δ γ c'` of `γ` by `diag(δ, 1)`. -/
theorem eta_natCast_mul_smul {δ : ℕ} (hδ : 0 < δ) (γ : SL(2, ℤ)) {c : ℤ} (hc : γ 1 0 = δ * c)
    (τ : ℍ) :
    η (δ * (γ • τ : ℍ)) =
      etaMultiplier (conjScale δ γ c hc) * Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) * η (δ * τ) := by
  let τ' : ℍ := UpperHalfPlane.mk (δ * τ) (im_natCast_mul_pos hδ τ.im_pos)
  have hden : (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := by
    simpa [UpperHalfPlane.denom] using UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ
  have hc' : (γ 1 0 : ℂ) = δ * c := by exact_mod_cast hc
  -- `γ_δ` sends `δ τ` to `δ · γ τ`, with automorphy factor `c' (δ τ) + d = c τ + d`.
  have hsmul : ((conjScale δ γ c hc • τ' : ℍ) : ℂ) = δ * (γ • τ : ℍ) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [coe_conjScale, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, algebraMap_int_eq,
      eq_intCast, Int.cast_mul, Int.cast_natCast, ofReal_intCast, ofReal_mul, ofReal_natCast, τ']
    rw [hc'] at hden ⊢
    field_simp
  have hfac : ((conjScale δ γ c hc 1 0 : ℤ) : ℂ) * τ' + conjScale δ γ c hc 1 1 =
      (γ 1 0 : ℂ) * τ + γ 1 1 := by
    simp only [coe_conjScale, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, τ', hc']
    ring
  have h := eta_smul (conjScale δ γ c hc) τ'
  rwa [hsmul, hfac] at h

end TauCeti.ModularForm

namespace TauCeti

/-- For `γ = (a b; c d) ∈ Γ₀(N)` and a divisor `δ ∣ N`, the matrix `γ_δ = (a, δ b; c / δ, d)` of
`SL(2, ℤ)`: the conjugate `conjScale δ γ (c / δ)` of `γ` by `diag(δ, 1)`, which is integral since
`δ ∣ N ∣ c`. -/
def conjScaleGamma0 {N δ : ℕ} (hδ : δ ∣ N) (γ : Gamma0 N) : SL(2, ℤ) :=
  conjScale δ γ ((γ : SL(2, ℤ)) 1 0 / δ)
    (Int.mul_ediv_cancel' ((Int.natCast_dvd_natCast.2 hδ).trans (mem_Gamma0_iff_dvd.1 γ.2))).symm

@[simp]
lemma coe_conjScaleGamma0 {N δ : ℕ} (hδ : δ ∣ N) (γ : Gamma0 N) :
    ((conjScaleGamma0 hδ γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(γ : SL(2, ℤ)) 0 0, (δ : ℤ) * (γ : SL(2, ℤ)) 0 1; (γ : SL(2, ℤ)) 1 0 / δ,
        (γ : SL(2, ℤ)) 1 1] := by
  rw [conjScaleGamma0, coe_conjScale]

/-- `γ_δ` is the identity when `γ` is. -/
@[simp]
lemma conjScaleGamma0_one {N δ : ℕ} (hδ : δ ∣ N) : conjScaleGamma0 hδ (1 : Gamma0 N) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end TauCeti

namespace TauCeti.ModularForm

/-- **The multiplier of an eta quotient** at `γ = (a b; c d) ∈ Γ₀(N)`: the product
`∏_{δ ∣ N} ε(γ_δ) ^ {r δ}` of eta multipliers at the conjugates `γ_δ = (a, δ b; c / δ, d)` of `γ`
by `diag(δ, 1)` (`conjScaleGamma0`). The eta quotient transforms under `γ` by this root of unity
(`etaQuotient_smul`, `etaQuotient_slash`). -/
noncomputable def etaQuotientMultiplier (N : ℕ) (r : ℕ → ℤ) (γ : Gamma0 N) : ℂ :=
  ∏ δ ∈ N.divisors.attach, etaMultiplier (conjScaleGamma0 (Nat.dvd_of_mem_divisors δ.2) γ) ^ r δ

/-- The defining product of the eta-quotient multiplier. -/
theorem etaQuotientMultiplier_def (N : ℕ) (r : ℕ → ℤ) (γ : Gamma0 N) :
    etaQuotientMultiplier N r γ =
      ∏ δ ∈ N.divisors.attach,
        etaMultiplier (conjScaleGamma0 (Nat.dvd_of_mem_divisors δ.2) γ) ^ r δ := (rfl)

/-- **The transformation of an eta quotient under `Γ₀(N)`**: for `γ = (a b; c d) ∈ Γ₀(N)`,
`f(γ τ) = (∏_{δ ∣ N} ε(γ_δ) ^ {r δ}) · √(c τ + d) ^ {∑_{δ ∣ N} r δ} · f(τ)` on the upper
half-plane, with the principal square root. -/
theorem etaQuotient_smul (N : ℕ) (r : ℕ → ℤ) (γ : Gamma0 N) (τ : ℍ) :
    etaQuotient N r ((γ : SL(2, ℤ)) • τ : ℍ) =
      etaQuotientMultiplier N r γ *
        Complex.sqrt (((γ : SL(2, ℤ)) 1 0 : ℂ) * τ + (γ : SL(2, ℤ)) 1 1) ^
          (∑ δ ∈ N.divisors, r δ) * etaQuotient N r τ := by
  have hsqrt : IsUnit (Complex.sqrt (((γ : SL(2, ℤ)) 1 0 : ℂ) * τ + (γ : SL(2, ℤ)) 1 1)) := by
    refine Ne.isUnit (Complex.sqrt_eq_zero_iff.not.2 ?_)
    simpa [UpperHalfPlane.denom] using
      UpperHalfPlane.denom_ne_zero ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ
  rw [etaQuotientMultiplier_def, etaQuotient_def, etaQuotient_def, ← sum_attach N.divisors r,
    ← prod_zpow_eq_zpow_sum_of_isUnit _ hsqrt,
    ← prod_attach N.divisors (fun δ ↦ η (δ * ((γ : SL(2, ℤ)) • τ : ℍ)) ^ r δ),
    ← prod_attach N.divisors (fun δ ↦ η (δ * τ) ^ r δ), ← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun δ _ ↦ ?_
  rw [← mul_zpow, ← mul_zpow]
  -- `conjScaleGamma0` is by definition the `conjScale` of `eta_natCast_mul_smul`.
  exact congrArg (· ^ r δ) (eta_natCast_mul_smul (Nat.pos_of_mem_divisors δ.2) _ _ τ)

/-- **The slash relation of an eta quotient**: if `∑_{δ ∣ N} r δ = 2 k`, then
`f ∣[k] γ = (∏_{δ ∣ N} ε(γ_δ) ^ {r δ}) • f` for every `γ ∈ Γ₀(N)`. -/
theorem etaQuotient_slash (N : ℕ) (r : ℕ → ℤ) {k : ℤ} (hk : ∑ δ ∈ N.divisors, r δ = 2 * k)
    (γ : Gamma0 N) :
    (fun τ : ℍ ↦ etaQuotient N r τ) ∣[k] (γ : SL(2, ℤ)) =
      etaQuotientMultiplier N r γ • fun τ : ℍ ↦ etaQuotient N r τ := by
  ext τ
  have hdenom : UpperHalfPlane.denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ =
      ((γ : SL(2, ℤ)) 1 0 : ℂ) * τ + (γ : SL(2, ℤ)) 1 1 := by
    simp [UpperHalfPlane.denom]
  have hden := UpperHalfPlane.denom_ne_zero ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ
  rw [hdenom] at hden
  rw [ModularForm.SL_slash_apply, etaQuotient_smul, hk, zpow_mul, zpow_ofNat, Complex.sq_sqrt,
    hdenom, Pi.smul_apply, smul_eq_mul, zpow_neg]
  field_simp

/-- The eta-quotient multiplier is a 24th root of unity. -/
theorem etaQuotientMultiplier_pow_twentyFour (N : ℕ) (r : ℕ → ℤ) (γ : Gamma0 N) :
    etaQuotientMultiplier N r γ ^ 24 = 1 := by
  rw [etaQuotientMultiplier_def, ← prod_pow]
  refine prod_eq_one fun δ _ ↦ ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, etaMultiplier_pow_twentyFour,
    one_zpow]

/-- The eta-quotient multiplier is `1` at the identity. -/
@[simp]
theorem etaQuotientMultiplier_one (N : ℕ) (r : ℕ → ℤ) : etaQuotientMultiplier N r 1 = 1 := by
  rw [etaQuotientMultiplier_def]
  simp

/-- **The eta-quotient multiplier is a character of `Γ₀(N)`** when `∑_{δ ∣ N} r δ` is even: then
the eta quotient has integral weight `k = ½ ∑_δ r δ`, and the slash relation `etaQuotient_slash`
is compatible with the slash action. -/
theorem etaQuotientMultiplier_mul (N : ℕ) (r : ℕ → ℤ) (hr : Even (∑ δ ∈ N.divisors, r δ))
    (γ γ' : Gamma0 N) :
    etaQuotientMultiplier N r (γ * γ') =
      etaQuotientMultiplier N r γ * etaQuotientMultiplier N r γ' := by
  obtain ⟨k, hk⟩ := hr
  have hk' : ∑ δ ∈ N.divisors, r δ = 2 * k := by rw [hk, two_mul]
  set f : ℍ → ℂ := fun τ ↦ etaQuotient N r τ
  have h : etaQuotientMultiplier N r (γ * γ') • f =
      (etaQuotientMultiplier N r γ * etaQuotientMultiplier N r γ') • f := by
    rw [← etaQuotient_slash N r hk', Subgroup.coe_mul, SlashAction.slash_mul,
      etaQuotient_slash N r hk', ModularForm.SL_smul_slash, etaQuotient_slash N r hk', smul_smul]
  have hI := congrFun h UpperHalfPlane.I
  simp only [Pi.smul_apply, smul_eq_mul, f] at hI
  exact mul_right_cancel₀ (etaQuotient_ne_zero N r (by simp)) hI

end TauCeti.ModularForm
