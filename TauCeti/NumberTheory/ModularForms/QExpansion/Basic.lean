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

Cusp functions of raw functions on `ℍ` are then compared off `q = 0`, where the cusp function is
just the function evaluated at the logarithm of `q`. There they commute with pointwise
operations, so meromorphy at `q = 0` is preserved by the field operations, twisting by `𝕢 ^ k`
multiplies the cusp function by `q ^ k`, and the `q`-expansion only depends on the cusp function
on a punctured neighbourhood of `0`. Constant functions have constant cusp functions, and for an
analytic cusp function the cusp function and the `q`-expansion of a power are the powers.

Finally, the `q`-parameter as a function on `ℍ`: it is periodic, its own `q`-expansion is `X`
(and that of its `m`-th power is `X ^ m`),
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
* `TauCeti.UpperHalfPlane.cuspFunction_map₂_eventuallyEq`,
  `TauCeti.UpperHalfPlane.cuspFunction_qParam_pow_mul_eventuallyEq` and
  `TauCeti.UpperHalfPlane.qExpansion_congr`: cusp functions off `q = 0`.
* `TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_mul` and its companions: meromorphy at `0`
  of cusp functions under the field operations.
* `TauCeti.UpperHalfPlane.cuspFunction_pow` and `TauCeti.UpperHalfPlane.qExpansion_pow`: powers of
  functions with analytic cusp functions.
* `TauCeti.UpperHalfPlane.qExpansion_qParam` and `TauCeti.UpperHalfPlane.qExpansion_qParam_pow`:
  the `q`-expansions of `q` and of its powers are `X` and its powers.
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

/-- The cusp function of the `q`-parameter is analytic at `0`. -/
theorem UpperHalfPlane.analyticAt_cuspFunction_qParam (hh : 0 < h) :
    AnalyticAt ℂ (cuspFunction h fun τ : ℍ ↦ Function.Periodic.qParam h τ) 0 :=
  _root_.UpperHalfPlane.analyticAt_cuspFunction_zero hh (periodic_qParam_comp_ofComplex hh.ne')
    (Function.Periodic.differentiable_qParam.mdifferentiable.comp mdifferentiable_coe)
    ((_root_.UpperHalfPlane.qParam_tendsto_atImInfty hh).isBigO_one ℝ)

/-- The `q`-expansion of the `q`-parameter itself is the variable `X`. -/
theorem UpperHalfPlane.qExpansion_qParam (hh : 0 < h) :
    qExpansion h (fun τ : ℍ ↦ Function.Periodic.qParam h τ) = PowerSeries.X := by
  ext m
  rw [← qExpansion_coeff_unique hh (analyticAt_cuspFunction_qParam hh)
    (c := fun m ↦ PowerSeries.coeff m (PowerSeries.X : PowerSeries ℂ)) (fun τ ↦ ?_) m]
  convert hasSum_ite_eq 1 (Function.Periodic.qParam h (τ : ℂ)) using 2 with m
  rw [PowerSeries.coeff_X]
  split_ifs with hm <;> simp [hm]

section CuspFunction

open Filter Topology

variable {f g : ℍ → ℂ}

/-- Off `q = 0`, the cusp function is evaluated at the logarithm of `q`. -/
theorem UpperHalfPlane.cuspFunction_of_ne_zero {q : ℂ} (hq : q ≠ 0) (f : ℍ → ℂ) :
    cuspFunction h f q = f (ofComplex (Function.Periodic.invQParam h q)) := by
  simp [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq]

/-- Off `q = 0`, cusp functions commute with pointwise binary operations. -/
theorem UpperHalfPlane.cuspFunction_map₂_eventuallyEq (op : ℂ → ℂ → ℂ) (f g : ℍ → ℂ) :
    cuspFunction h (fun τ ↦ op (f τ) (g τ)) =ᶠ[𝓝[≠] 0]
      fun q ↦ op (cuspFunction h f q) (cuspFunction h g q) :=
  eventually_nhdsWithin_of_forall fun q hq ↦ by
    simp only [cuspFunction_of_ne_zero (Set.mem_compl_singleton_iff.mp hq)]

/-- Off `q = 0`, cusp functions commute with pointwise operations. -/
theorem UpperHalfPlane.cuspFunction_map_eventuallyEq (op : ℂ → ℂ) (f : ℍ → ℂ) :
    cuspFunction h (fun τ ↦ op (f τ)) =ᶠ[𝓝[≠] 0] fun q ↦ op (cuspFunction h f q) :=
  eventually_nhdsWithin_of_forall fun q hq ↦ by
    simp only [cuspFunction_of_ne_zero (Set.mem_compl_singleton_iff.mp hq)]

/-- Off `q = 0` and inside the unit disc, the cusp function of `𝕢 ^ k * f` is `q ^ k` times the
cusp function of `f`. -/
theorem UpperHalfPlane.cuspFunction_qParam_pow_mul_eventuallyEq (hh : 0 < h) (k : ℕ)
    (f : ℍ → ℂ) :
    cuspFunction h (fun τ ↦ Function.Periodic.qParam h τ ^ k * f τ) =ᶠ[𝓝[≠] 0]
      fun q ↦ q ^ k * cuspFunction h f q := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with q hq hqn
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hq
  rw [cuspFunction_of_ne_zero hq, cuspFunction_of_ne_zero hq,
    ofComplex_apply_of_im_pos (Function.Periodic.im_invQParam_pos_of_norm_lt_one hh
      (mem_ball_zero_iff.mp hqn) hq)]
  rw [Function.Periodic.qParam_right_inv hh.ne' hq]

/-- Cusp functions which agree off `q = 0` agree near `q = 0`: the value at `0` is the limit
along the punctured neighbourhoods. -/
theorem UpperHalfPlane.cuspFunction_eventuallyEq_nhds
    (hfg : cuspFunction h f =ᶠ[𝓝[≠] 0] cuspFunction h g) :
    cuspFunction h f =ᶠ[𝓝 0] cuspFunction h g := by
  refine eventuallyEq_nhds_of_eventuallyEq_nhdsNE hfg ?_
  simp only [cuspFunction]
  rw [Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne,
    Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
  exact congrArg lim (Filter.map_congr hfg)

/-- A cusp function which agrees off `q = 0` with a function continuous at `0` agrees with it
near `0`. -/
theorem UpperHalfPlane.cuspFunction_eventuallyEq_nhds_of_continuousAt {ψ : ℂ → ℂ}
    (hf : cuspFunction h f =ᶠ[𝓝[≠] 0] ψ) (hψ : ContinuousAt ψ 0) :
    cuspFunction h f =ᶠ[𝓝 0] ψ := by
  refine eventuallyEq_nhds_of_eventuallyEq_nhdsNE hf ?_
  simp only [cuspFunction]
  rw [Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
  exact ((hψ.tendsto.mono_left nhdsWithin_le_nhds).congr' hf.symm).limUnder_eq

/-- The `q`-expansion only depends on the cusp function off `q = 0`. -/
theorem UpperHalfPlane.qExpansion_congr (hfg : cuspFunction h f =ᶠ[𝓝[≠] 0] cuspFunction h g) :
    qExpansion h f = qExpansion h g := by
  ext n
  rw [_root_.UpperHalfPlane.qExpansion_coeff, _root_.UpperHalfPlane.qExpansion_coeff,
    (cuspFunction_eventuallyEq_nhds hfg).iteratedDeriv_eq]

/-- The cusp function of a constant function is constant. -/
theorem UpperHalfPlane.cuspFunction_const (h : ℝ) (c : ℂ) :
    cuspFunction h (fun _ : ℍ ↦ c) = fun _ ↦ c := by
  have h_lim : limUnder (𝓝[≠] (0 : ℂ))
      (((fun _ ↦ c : ℍ → ℂ) ∘ ofComplex) ∘ Function.Periodic.invQParam h) = c :=
    Filter.Tendsto.limUnder_eq tendsto_const_nhds
  rw [cuspFunction, Function.Periodic.cuspFunction, h_lim]
  exact Function.update_eq_self 0 (fun _ ↦ c)

/-- The cusp function of `1` is `1`. -/
theorem UpperHalfPlane.cuspFunction_one (h : ℝ) : cuspFunction h (1 : ℍ → ℂ) = 1 :=
  cuspFunction_const h 1

/-- The cusp function of a power is the power of the cusp function, when the cusp function is
analytic at `0`. -/
theorem UpperHalfPlane.cuspFunction_pow (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    ∀ n : ℕ, cuspFunction h (f ^ n) = cuspFunction h f ^ n
  | 0 => by rw [pow_zero, pow_zero]; exact cuspFunction_one h
  | n + 1 => by
    rw [pow_succ, pow_succ, ← cuspFunction_pow hf n,
      _root_.UpperHalfPlane.cuspFunction_mul
        (by rw [cuspFunction_pow hf n]; exact (hf.continuousAt.pow n)) hf.continuousAt]

/-- The `q`-expansion of a power is the power of the `q`-expansion, when the cusp function is
analytic at `0`. -/
theorem UpperHalfPlane.qExpansion_pow (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    ∀ n : ℕ, qExpansion h (f ^ n) = qExpansion h f ^ n
  | 0 => by rw [pow_zero, pow_zero, _root_.UpperHalfPlane.qExpansion_one]
  | n + 1 => by
    have h_an : AnalyticAt ℂ (cuspFunction h (f ^ n)) 0 := by
      rw [cuspFunction_pow hf n]
      exact hf.pow n
    rw [pow_succ, pow_succ, _root_.UpperHalfPlane.qExpansion_mul h_an hf, qExpansion_pow hf n]

/-- The cusp function of a product is meromorphic at `0` when both cusp functions are. -/
theorem UpperHalfPlane.meromorphicAt_cuspFunction_mul (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) : MeromorphicAt (cuspFunction h (f * g)) 0 :=
  (hf.mul hg).congr (cuspFunction_map₂_eventuallyEq (· * ·) f g).symm

/-- The cusp function of a sum is meromorphic at `0` when both cusp functions are. -/
theorem UpperHalfPlane.meromorphicAt_cuspFunction_add (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) : MeromorphicAt (cuspFunction h (f + g)) 0 :=
  (hf.add hg).congr (cuspFunction_map₂_eventuallyEq (· + ·) f g).symm

/-- The cusp function of a difference is meromorphic at `0` when both cusp functions are. -/
theorem UpperHalfPlane.meromorphicAt_cuspFunction_sub (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) : MeromorphicAt (cuspFunction h (f - g)) 0 :=
  (hf.sub hg).congr (cuspFunction_map₂_eventuallyEq (· - ·) f g).symm

/-- The cusp function of a quotient is meromorphic at `0` when both cusp functions are. -/
theorem UpperHalfPlane.meromorphicAt_cuspFunction_div (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) : MeromorphicAt (cuspFunction h (f / g)) 0 :=
  (hf.div hg).congr (cuspFunction_map₂_eventuallyEq (· / ·) f g).symm

/-- The cusp function of a negation is meromorphic at `0` when the cusp function is. -/
theorem UpperHalfPlane.meromorphicAt_cuspFunction_neg (hf : MeromorphicAt (cuspFunction h f) 0) :
    MeromorphicAt (cuspFunction h (-f)) 0 :=
  hf.neg.congr (cuspFunction_map_eventuallyEq (- ·) f).symm

/-- The cusp function of an inverse is meromorphic at `0` when the cusp function is. -/
theorem UpperHalfPlane.meromorphicAt_cuspFunction_inv (hf : MeromorphicAt (cuspFunction h f) 0) :
    MeromorphicAt (cuspFunction h f⁻¹) 0 :=
  hf.inv.congr (cuspFunction_map_eventuallyEq (·⁻¹) f).symm

/-- The cusp function of a power is meromorphic at `0` when the cusp function is. -/
theorem UpperHalfPlane.meromorphicAt_cuspFunction_pow (hf : MeromorphicAt (cuspFunction h f) 0)
    (n : ℕ) : MeromorphicAt (cuspFunction h (f ^ n)) 0 :=
  (hf.pow n).congr (cuspFunction_map_eventuallyEq (· ^ n) f).symm

/-- The cusp function of a constant function is meromorphic at `0`. -/
theorem UpperHalfPlane.meromorphicAt_cuspFunction_const (c : ℂ) :
    MeromorphicAt (cuspFunction h fun _ : ℍ ↦ c) 0 :=
  cuspFunction_const h c ▸ analyticAt_const.meromorphicAt

/-- The order at `0` of `q ^ k` times the cusp function of `f`. -/
theorem UpperHalfPlane.meromorphicOrderAt_qParam_pow_mul {k : ℕ}
    (hf : MeromorphicAt (cuspFunction h f) 0) :
    meromorphicOrderAt (fun q ↦ q ^ k * cuspFunction h f q) 0 =
      k + meromorphicOrderAt (cuspFunction h f) 0 := by
  have hq : MeromorphicAt (fun q : ℂ ↦ q ^ k) 0 := (analyticAt_id.pow k).meromorphicAt
  rw [fun_meromorphicOrderAt_mul hq hf]
  congr 1
  simpa using fun_meromorphicOrderAt_pow_id_sub_const (x := (0 : ℂ)) (n := k)

end CuspFunction

/-- The cusp function of a power of the `q`-parameter is analytic at `0`. -/
theorem UpperHalfPlane.analyticAt_cuspFunction_qParam_pow (hh : 0 < h) (m : ℕ) :
    AnalyticAt ℂ (cuspFunction h fun τ : ℍ ↦ Function.Periodic.qParam h τ ^ m) 0 := by
  have hq := analyticAt_cuspFunction_qParam hh
  change AnalyticAt ℂ (cuspFunction h ((fun τ : ℍ ↦ Function.Periodic.qParam h τ) ^ m)) 0
  rw [cuspFunction_pow hq m]
  exact hq.pow m

/-- The `q`-expansion of the `m`-th power of the `q`-parameter is `X ^ m`. -/
theorem UpperHalfPlane.qExpansion_qParam_pow (hh : 0 < h) (m : ℕ) :
    qExpansion h (fun τ : ℍ ↦ Function.Periodic.qParam h τ ^ m) = PowerSeries.X ^ m := by
  change qExpansion h ((fun τ : ℍ ↦ Function.Periodic.qParam h τ) ^ m) = _
  rw [qExpansion_pow (analyticAt_cuspFunction_qParam hh) m, qExpansion_qParam hh]

/-- A periodic function whose `q`-expansion has no constant term is asymptotic to its first
coefficient times `q` at `i∞`: `f τ / q` tends to the coefficient of `q`. -/
theorem UpperHalfPlane.tendsto_div_qParam_atImInfty {f : ℍ → ℂ} (hh : 0 < h)
    (hfper : Function.Periodic (f ∘ ofComplex) h)
    (hfdiff : DifferentiableAt ℂ (cuspFunction h f) 0) (hf0 : (qExpansion h f).coeff 0 = 0) :
    Filter.Tendsto (fun τ ↦ f τ / Function.Periodic.qParam h τ) atImInfty
      (nhds ((qExpansion h f).coeff 1)) := by
  have hderiv : HasDerivAt (cuspFunction h f) ((qExpansion h f).coeff 1) 0 := by
    simpa [_root_.UpperHalfPlane.qExpansion_coeff] using hfdiff.hasDerivAt
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
