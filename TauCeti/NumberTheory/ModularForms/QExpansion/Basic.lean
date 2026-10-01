/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import TauCeti.Analysis.Complex.Periodic

/-!
# The `q`-expansion as a linear map, and uniqueness of coefficients for raw functions

The `q`-expansion of modular forms for a determinant-one subgroup of `GL(2, ℝ)`, bundled as
a `ℂ`-linear map into power series, refining Mathlib's additive `ModularForm.qExpansionAddHom`.

Alongside it, the raw-function form of Mathlib's coefficient-uniqueness statement. Mathlib's
`UpperHalfPlane.qExpansion_coeff_unique` is stated for a bundled `f : F` with
`[FunLike F ℍ ℂ]`, and `ℍ → ℂ` carries no such instance, so an operator built as a plain
function on `ℍ` — every Hecke-style slash sum before it is packaged as a `ModularForm` — cannot
invoke it. The proof is Mathlib's, run through `UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction`,
which *is* stated for `{f : ℍ → ℂ}`, with `qExpansionFormalMultilinearSeries` spelled out
inline for the same reason.

Alongside them, the `n`-th coefficient bundled as a `ℂ`-linear functional on *cusp* forms,
`CuspForm.qExpansionCoeffₗ` — the linear map above, composed with the inclusion of cusp forms
and with `PowerSeries.coeff n`. It is what a coefficient computation on a linear combination of
cusp forms is run through, and `CuspForm.qExpansion_injective` turns the resulting coefficient
identity back into an identity of cusp forms.

Alongside those, the effect of a `1 / d` translation on the `q`-powers a support condition
leaves alive: shifting the argument by `1 / d` scales the `n`-th `q`-power by a `d`-th root of
unity raised to `n`, so a coefficient function supported on the multiples of `d` does not see the
shift. That is what a `q`-support hypothesis is spent on when descending along `V_d`, and it is
stated here rather than at the descent because it mentions only coefficients, divisibility and
`Function.Periodic.qParam`.

Finally, the `q`-parameter as a function on `ℍ`: it is periodic, its own `q`-expansion is `X`,
and a periodic function whose `q`-expansion has no constant term is asymptotic at `i∞` to its
`q`-coefficient times `q`.  These are what a function with a pole at the cusp, such as `j`, is
expanded through: one multiplies by `q` and divides the expansion of the product by `q`.

## Main declarations

* `TauCeti.ModularForm.qExpansionLinearMap`.
* `TauCeti.UpperHalfPlane.qExpansion_coeff_unique`.
* `CuspForm.qExpansionCoeffₗ` (at root, so dot notation on `CuspForm` elaborates): the `n`-th
  coefficient as a `ℂ`-linear functional on cusp forms.
* `CuspForm.qExpansion_injective`: a cusp form is determined by its `q`-expansion.
* `TauCeti.smul_qParam_pow_shift_eq`: a shift by `1 / d` fixes every `q`-power that a
  `d`-supported coefficient function leaves alive.
* `TauCeti.UpperHalfPlane.qExpansion_qParam`: the `q`-expansion of `q` is `X`.
* `TauCeti.UpperHalfPlane.tendsto_div_qParam_atImInfty`: `f / q` tends to the `q`-coefficient of
  `f` when the constant coefficient vanishes.

## References

* [Mathlib PR #39000](https://github.com/leanprover-community/mathlib4/pull/39000)
  (Chris Birkbeck) — the upstream draft this file ports onto the current Mathlib pin.
-/

public noncomputable section

open UpperHalfPlane
open scoped Manifold

namespace TauCeti

variable {h : ℝ}

/-- The `q`-expansion map as a `ℂ`-linear map to power series over `ℂ`, refining the additive
`ModularForm.qExpansionAddHom`. -/
def ModularForm.qExpansionLinearMap {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (k : ℤ) :
    ModularForm Γ k →ₗ[ℂ] PowerSeries ℂ where
  toAddHom := (_root_.ModularForm.qExpansionAddHom hh hΓ k).toAddHom
  map_smul' a f := _root_.ModularForm.qExpansion_smul hh hΓ a f

@[simp]
lemma ModularForm.qExpansionLinearMap_apply {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {k : ℤ} (f : ModularForm Γ k) :
    ModularForm.qExpansionLinearMap hh hΓ k f = qExpansion h f := by
  unfold ModularForm.qExpansionLinearMap
  rfl

/-- **Uniqueness of `q`-expansion coefficients, for a raw function on `ℍ`.** If `f` is given by
a convergent expansion `f τ = ∑' m, c m * 𝕢 h τ ^ m` and its cusp function is analytic at `0`,
then the `c m` are the coefficients of `qExpansion h f`.

This is Mathlib's `UpperHalfPlane.qExpansion_coeff_unique` with the `[FunLike F ℍ ℂ]` bundling
removed: `ℍ → ℂ` has no `FunLike` instance, so the bundled statement does not apply to an
operator that is still a plain function. -/
lemma UpperHalfPlane.qExpansion_coeff_unique {f : ℍ → ℂ} {c : ℕ → ℂ} (hh : 0 < h)
    (hfanalytic : AnalyticAt ℂ (cuspFunction h f) 0)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Function.Periodic.qParam h τ ^ m) (f τ)) (m : ℕ) :
    c m = (qExpansion h f).coeff m := by
  have h1 := (_root_.UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction hh hfanalytic
    hf).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h f)
      (.ofScalars ℂ fun m ↦ (qExpansion h f).coeff m) 0 := by
    simpa [_root_.UpperHalfPlane.qExpansion_coeff, div_eq_mul_inv, mul_comm]
      using hfanalytic.hasFPowerSeriesAt
  simpa using congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

/-- The `q`-parameter of width `h` is `h`-periodic, read on `ℂ` through `ofComplex`. -/
theorem UpperHalfPlane.periodic_qParam_comp_ofComplex (hh : h ≠ 0) :
    Function.Periodic ((fun τ : ℍ ↦ Function.Periodic.qParam h τ) ∘ ofComplex) h :=
  _root_.UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ by
    simp only [coe_vadd, Function.Periodic.qParam, mul_add, add_div,
      mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr hh), Complex.exp_add,
      Complex.exp_two_pi_mul_I, one_mul]

/-- The `q`-expansion of the `q`-parameter itself is the variable `X`. -/
theorem UpperHalfPlane.qExpansion_qParam (hh : 0 < h) :
    qExpansion h (fun τ : ℍ ↦ Function.Periodic.qParam h τ) = PowerSeries.X := by
  have hper := periodic_qParam_comp_ofComplex hh.ne'
  have hhol : MDiff (fun τ : ℍ ↦ Function.Periodic.qParam h τ) :=
    Function.Periodic.differentiable_qParam.mdifferentiable.comp mdifferentiable_coe
  have hbdd : IsBoundedAtImInfty (fun τ : ℍ ↦ Function.Periodic.qParam h τ) :=
    (_root_.UpperHalfPlane.qParam_tendsto_atImInfty hh).isBigO_one ℝ
  ext m
  rw [← qExpansion_coeff_unique hh
    (_root_.UpperHalfPlane.analyticAt_cuspFunction_zero hh hper hhol hbdd)
    (c := fun m ↦ PowerSeries.coeff m (PowerSeries.X : PowerSeries ℂ)) (fun τ ↦ ?_) m]
  convert hasSum_ite_eq 1 (Function.Periodic.qParam h (τ : ℂ)) using 2 with m
  rw [PowerSeries.coeff_X]
  split_ifs with hm <;> simp [hm]

/-- A periodic function whose `q`-expansion has no constant term is asymptotic to its first
coefficient times `q` at `i∞`: `f τ / q` tends to the coefficient of `q`. -/
theorem UpperHalfPlane.tendsto_div_qParam_atImInfty {f : ℍ → ℂ} (hh : 0 < h)
    (hfper : Function.Periodic (f ∘ ofComplex) h)
    (hfanalytic : AnalyticAt ℂ (cuspFunction h f) 0) (hf0 : (qExpansion h f).coeff 0 = 0) :
    Filter.Tendsto (fun τ ↦ f τ / Function.Periodic.qParam h τ) atImInfty
      (nhds ((qExpansion h f).coeff 1)) := by
  have hderiv : HasDerivAt (cuspFunction h f) ((qExpansion h f).coeff 1) 0 := by
    simpa [_root_.UpperHalfPlane.qExpansion_coeff] using hfanalytic.differentiableAt.hasDerivAt
  have h0 : cuspFunction h f 0 = 0 := by
    simpa [_root_.UpperHalfPlane.qExpansion_coeff] using hf0
  have hq : Filter.Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam h τ) atImInfty
      (nhdsWithin 0 {0}ᶜ) :=
    tendsto_nhdsWithin_iff.mpr ⟨_root_.UpperHalfPlane.qParam_tendsto_atImInfty hh,
      .of_forall fun τ ↦ Function.Periodic.qParam_ne_zero _⟩
  refine (hderiv.tendsto_slope_zero.comp hq).congr fun τ ↦ ?_
  simp [h0, _root_.UpperHalfPlane.eq_cuspFunction τ hh.ne' hfper, div_eq_inv_mul]

/-- **The `n`-th `q`-expansion coefficient as a `ℂ`-linear functional on cusp forms.**
`f ↦ (qExpansion h f).coeff n`, bundled: the coefficient of a linear combination of cusp forms
is that combination of their coefficients, by `map_add`, `map_sub` and `map_smul`. -/
def _root_.CuspForm.qExpansionCoeffₗ {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (k : ℤ) (n : ℕ) : CuspForm Γ k →ₗ[ℂ] ℂ :=
  (PowerSeries.coeff n).comp
    ((ModularForm.qExpansionLinearMap hh hΓ k).comp CuspForm.toModularFormₗ)

@[simp]
lemma _root_.CuspForm.qExpansionCoeffₗ_apply {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {k : ℤ} (n : ℕ) (f : CuspForm Γ k) :
    CuspForm.qExpansionCoeffₗ hh hΓ k n f = (qExpansion h ⇑f).coeff n := by
  rw [CuspForm.qExpansionCoeffₗ, LinearMap.comp_apply, LinearMap.comp_apply,
    ModularForm.qExpansionLinearMap_apply]
  exact congrArg (fun g ↦ (qExpansion h g).coeff n) (funext (CuspForm.toModularFormₗ_apply f))

/-- **A cusp form is determined by its `q`-expansion.** The cusp-form counterpart of Mathlib's
`ModularForm.qExpansion_injective`: a cusp form and its image under the injective inclusion
`CuspForm.toModularFormₗ` have the same underlying function. -/
lemma _root_.CuspForm.qExpansion_injective {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {k : ℤ} :
    Function.Injective (fun f : CuspForm Γ k ↦ qExpansion h f) := by
  have hcoe (f : CuspForm Γ k) : ⇑(CuspForm.toModularFormₗ f) = ⇑f :=
    funext (CuspForm.toModularFormₗ_apply f)
  refine fun f g hfg ↦ CuspForm.toModularFormₗ_injective
    (_root_.ModularForm.qExpansion_injective hh hΓ ?_)
  simpa only [hcoe] using hfg

/-- The translate `1 / d +ᵥ σ`, read in `ℂ`, is the subtraction `TauCeti.Periodic.qParam_sub`
expects: that lemma is stated at `z - j`, and the shift here enters as a `+ᵥ` on `ℍ`. Naming the
coercion bridge keeps the root-of-unity computation below free of casting. -/
private lemma coe_vadd_one_div_eq_sub {d : ℕ} (σ : ℍ) :
    ((((1 : ℝ) / (d : ℝ)) +ᵥ σ : ℍ) : ℂ) = (σ : ℂ) - -(1 / (d : ℂ)) := by
  rw [UpperHalfPlane.coe_vadd]
  push_cast
  ring

/-- **A shift by `1 / d` fixes every `q`-power the support condition leaves alive.** Translating
the argument by `1 / d` scales the `n`-th `q`-power by a `d`-th root of unity raised to `n`, which
is trivial exactly on the multiples of `d` — and a coefficient function supported there kills
every other index. This is what a `q`-support hypothesis is spent on when descending along `V_d`.
-/
theorem smul_qParam_pow_shift_eq {d : ℕ} [NeZero d] {c : ℕ → ℂ}
    (hc : ∀ n : ℕ, ¬ d ∣ n → c n = 0) (σ : ℍ) (n : ℕ) :
    c n • Function.Periodic.qParam (1 : ℝ) ((((1 : ℝ) / (d : ℝ)) +ᵥ σ : ℍ) : ℂ) ^ n =
      c n • Function.Periodic.qParam (1 : ℝ) (σ : ℂ) ^ n := by
  have hqP : Function.Periodic.qParam (1 : ℝ) ((((1 : ℝ) / (d : ℝ)) +ᵥ σ : ℍ) : ℂ) =
      Function.Periodic.qParam (1 : ℝ) (σ : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (d : ℂ)) := by
    rw [coe_vadd_one_div_eq_sub, TauCeti.Periodic.qParam_sub]
    congr 1
    push_cast
    ring_nf
  by_cases hdn : d ∣ n
  · obtain ⟨m, rfl⟩ := hdn
    rw [hqP, mul_pow, pow_mul (Complex.exp _) d m,
      (Complex.isPrimitiveRoot_exp d (NeZero.ne d)).pow_eq_one, one_pow, mul_one]
  · rw [hc n hdn, zero_smul, zero_smul]

end TauCeti

end
