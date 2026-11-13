/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ContDiff.Basic
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Limits

/-!
# Derivatives of exponential functions

Viewed as a function of a real vector variable, `Complex.exp` has the same iterated derivatives
as it has over `ℂ`, restricted to real scalars. Since every complex derivative of `exp` is `exp`,
every real iterated derivative of `Complex.exp` at `z` has norm `‖exp z‖`. This is the input a
Faà di Bruno bound needs for compositions `Complex.exp ∘ f` with a real-differentiable `f`.

For a function `f` on `ℝ`, `f ∘ exp` is differentiable at `y` exactly when `f` is differentiable
at `exp y`, so the chain rule `(f ∘ exp)'(y) = e^y f'(e^y)` holds with no hypothesis on `f`.

## Main results

* `TauCeti.differentiableAt_comp_exp_iff`: `f ∘ exp` is differentiable at `y` exactly when `f` is
  differentiable at `exp y`.
* `TauCeti.deriv_comp_exp`: `(f ∘ exp)'(y) = e^y • f'(e^y)`, unconditionally.
* `TauCeti.norm_iteratedFDeriv_real_cexp`: every real iterated derivative of `Complex.exp` at `z`
  has norm `‖exp z‖`.
* `ContinuousLinearMap.norm_iteratedFDeriv_cexp_comp_le`: for a real-linear map `ℓ` to `ℂ`, the
  `n`-th derivative of `x ↦ exp (ℓ x)` has norm at most `‖exp (ℓ x)‖ ‖ℓ‖ ^ n`.
* `TauCeti.isBigO_iteratedFDeriv_succ_exp`: along any filter, the derivative of order `n + 1` of
  `exp ℓ` is `O(ρ)` when the derivatives of `ℓ` of positive order up to that order are `O(ρ)` and
  those of `exp ℓ` of lower order are bounded.
* `TauCeti.isBigO_iteratedFDeriv_exp_sub_one`, `TauCeti.isBigO_iteratedFDeriv_exp`: if `ℓ → 0`
  and the derivatives of `ℓ` are `O(ρ)` for a bounded `ρ`, then so are those of `exp ℓ - 1`, and
  those of `exp ℓ` are bounded.
* `TauCeti.isBigO_iteratedFDeriv_iteratedFDeriv_exp_sub_smul`: the commutator
  `Dᵏ (exp ℓ) - exp ℓ • Dᵏ ℓ` and its derivatives are `O(ρ)`, as it involves only derivatives of
  `ℓ` of order below `k`.
-/

public section

namespace Real

/-- The derivative of an exponential with linear exponent. -/
@[simp] theorem deriv_exp_mul (a x : ℝ) :
    deriv (fun y : ℝ => exp (a * y)) x = a * exp (a * x) := by
  simpa [mul_comm] using (((hasDerivAt_id x).const_mul a).exp).deriv

/-- The norm of the Fréchet derivative of an exponential with linear exponent. -/
@[simp] theorem norm_fderiv_exp_mul (a x : ℝ) :
    ‖fderiv ℝ (fun y : ℝ => exp (a * y)) x‖ = |a| * exp (a * x) := by
  rw [← norm_deriv_eq_norm_fderiv, deriv_exp_mul, Real.norm_eq_abs, abs_mul,
    abs_of_pos (exp_pos _)]

end Real

namespace TauCeti

/-- Every real iterated derivative of the complex exponential at `z` has norm `‖exp z‖`. -/
theorem norm_iteratedFDeriv_real_cexp (n : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ n Complex.exp z‖ = ‖Complex.exp z‖ := by
  rw [← ((Complex.contDiff_exp (𝕜 := ℂ) (n := n)).contDiffAt).restrictScalars_iteratedFDeriv
      (𝕜 := ℝ),
    Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Complex.iter_deriv_exp]

section ExpComp

open Real Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {y : ℝ}

/-- `f ∘ exp` is differentiable at `y` exactly when `f` is differentiable at `exp y`. -/
@[simp]
theorem differentiableAt_comp_exp_iff :
    DifferentiableAt ℝ (fun y ↦ f (exp y)) y ↔ DifferentiableAt ℝ f (exp y) := by
  refine ⟨fun h ↦ ?_, fun hf ↦ hf.comp y differentiableAt_exp⟩
  have h' : DifferentiableAt ℝ (fun y ↦ f (exp y)) (log (exp y)) := by simpa using h
  refine (h'.comp (exp y) (differentiableAt_log (exp_pos y).ne')).congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds (exp_pos y)] with z hz
  simp [exp_log hz]

/-- The chain rule for `f ∘ exp`, with no differentiability hypothesis: where `f` is not
differentiable at `exp y`, neither is `f ∘ exp` at `y`, and both sides are `0`. -/
theorem deriv_comp_exp : deriv (fun y ↦ f (exp y)) y = exp y • deriv f (exp y) := by
  by_cases hf : DifferentiableAt ℝ f (exp y)
  · exact (hf.hasDerivAt.scomp y (hasDerivAt_exp y)).deriv
  · rw [deriv_zero_of_not_differentiableAt hf, smul_zero,
      deriv_zero_of_not_differentiableAt (mt differentiableAt_comp_exp_iff.1 hf)]

end ExpComp

end TauCeti

namespace ContinuousLinearMap

/-- For a real-linear map `ℓ : E →L[ℝ] ℂ`, the `n`-th derivative of `x ↦ exp (ℓ x)` has norm at
most `‖exp (ℓ x)‖ ‖ℓ‖ ^ n`. For a purely imaginary `ℓ`, such as the phase `x ↦ 2πi ⟪x, w⟫` of a
character, this is `‖ℓ‖ ^ n`. -/
theorem norm_iteratedFDeriv_cexp_comp_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : E →L[ℝ] ℂ) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y ↦ Complex.exp (ℓ y)) x‖ ≤ ‖Complex.exp (ℓ x)‖ * ‖ℓ‖ ^ n := by
  have h := ℓ.iteratedFDeriv_comp_right ((Complex.contDiff_exp (𝕜 := ℂ)).restrict_scalars ℝ) x
    (i := n) (mod_cast le_top)
  rw [Function.comp_def] at h
  rw [h, ← TauCeti.norm_iteratedFDeriv_real_cexp n (ℓ x)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_eq ?_
  simp

end ContinuousLinearMap

namespace TauCeti

section Asymptotics

open Asymptotics Filter Topology

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] {ℓ : D → ℝ} {l : Filter D}
  {ρ : D → ℝ}

/-- **Asymptotic bounds on the derivatives of `exp ℓ`.** Along any filter, the derivative of order
`n + 1` of `y ↦ exp (ℓ y)` is `O(ρ)` when `ℓ` is eventually `C^(n + 1)`, the derivatives of `ℓ` of
orders `1` to `n + 1` are `O(ρ)` and those of `exp ℓ` of order at most `n` are bounded: it is the
order-`n` derivative of `exp ℓ • Dℓ`, which `ContinuousLinearMap.isBigO_iteratedFDeriv_of_bilinear`
bounds. -/
theorem isBigO_iteratedFDeriv_succ_exp {n : ℕ} (hℓ : ∀ᶠ y in l, ContDiffAt ℝ (n + 1) ℓ y)
    (hℓn : ∀ i, 1 ≤ i → i ≤ n + 1 → iteratedFDeriv ℝ i ℓ =O[l] ρ)
    (hen : ∀ i ≤ n, iteratedFDeriv ℝ i (fun y ↦ Real.exp (ℓ y)) =O[l] fun _ ↦ (1 : ℝ)) :
    iteratedFDeriv ℝ (n + 1) (fun y ↦ Real.exp (ℓ y)) =O[l] ρ := by
  have hB := (ContinuousLinearMap.lsmul ℝ ℝ).isBigO_iteratedFDeriv_of_bilinear
    (f := fun y ↦ Real.exp (ℓ y)) (g := fderiv ℝ ℓ)
    (hℓ.mono fun y hy ↦ hy.exp.of_le (by norm_cast; omega))
    (hℓ.mono fun y hy ↦ hy.fderiv_right (m := n) le_rfl) hen
    (fun i hi ↦ (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_fderiv.le).trans
      (hℓn (i + 1) (by omega) (by omega)))
  simp only [ContinuousLinearMap.lsmul_apply, one_mul] at hB
  refine (IsBigO.of_bound 1 ?_).trans hB
  filter_upwards [hℓ] with y hy
  -- Near `y`, the derivative of `exp ℓ` is `exp ℓ • Dℓ`.
  have hfe : fderiv ℝ (fun y ↦ Real.exp (ℓ y)) =ᶠ[𝓝 y] fun z ↦ Real.exp (ℓ z) • fderiv ℝ ℓ z := by
    filter_upwards [hy.eventually (by simp)] with z hz
    exact fderiv_exp (hz.differentiableAt (by simp))
  rw [one_mul, ← norm_iteratedFDeriv_fderiv, (hfe.iteratedFDeriv ℝ n).eq_of_nhds]

/-- The derivatives of `exp ℓ` and of `exp ℓ - 1` differ by the derivative of a constant. -/
private theorem isBigO_iteratedFDeriv_exp_of_sub_one {n : ℕ}
    (hℓ : ∀ᶠ y in l, ContDiffAt ℝ n ℓ y) (hρ : ρ =O[l] fun _ ↦ (1 : ℝ))
    (h : iteratedFDeriv ℝ n (fun y ↦ Real.exp (ℓ y) - 1) =O[l] ρ) :
    iteratedFDeriv ℝ n (fun y ↦ Real.exp (ℓ y)) =O[l] fun _ ↦ (1 : ℝ) := by
  have hc : iteratedFDeriv ℝ n (fun _ : D ↦ (1 : ℝ)) =O[l] fun _ ↦ (1 : ℝ) := by
    refine isBigO_of_le _ fun y ↦ ?_
    rcases n with _ | n
    · simp [norm_iteratedFDeriv_zero]
    · simp [iteratedFDeriv_const_of_ne]
  refine ((h.trans hρ).add hc).congr' ?_ EventuallyEq.rfl
  filter_upwards [hℓ] with y hy
  rw [fun_iteratedFDeriv_sub_apply hy.exp contDiffAt_const, sub_add_cancel]

/-- **Asymptotic bounds on the derivatives of `exp ℓ - 1`.** Along any filter, if `ℓ` is eventually
`C^n` and tends to `0`, and its derivatives of order at most `n` are `O(ρ)` for a bounded `ρ`, then
the derivative of order `n` of `y ↦ exp (ℓ y) - 1` is `O(ρ)`. -/
theorem isBigO_iteratedFDeriv_exp_sub_one {n : ℕ} (hℓ : ∀ᶠ y in l, ContDiffAt ℝ n ℓ y)
    (hℓ0 : Tendsto ℓ l (𝓝 0)) (hρ : ρ =O[l] fun _ ↦ (1 : ℝ))
    (hℓn : ∀ i ≤ n, iteratedFDeriv ℝ i ℓ =O[l] ρ) :
    iteratedFDeriv ℝ n (fun y ↦ Real.exp (ℓ y) - 1) =O[l] ρ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | n
  · exact (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_zero.le).trans
      (Real.isBigO_exp_comp_sub_one hℓ0
        ((isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_zero.ge).trans (hℓn 0 le_rfl)))
  · -- The derivatives of `exp ℓ` of lower order are bounded by the induction hypothesis.
    have hen : ∀ i ≤ n, iteratedFDeriv ℝ i (fun y ↦ Real.exp (ℓ y)) =O[l] fun _ ↦ (1 : ℝ) :=
      fun i hi ↦ by
        have hℓi : ∀ᶠ y in l, ContDiffAt ℝ i ℓ y :=
          hℓ.mono fun y hy ↦ hy.of_le (by norm_cast; omega)
        exact isBigO_iteratedFDeriv_exp_of_sub_one hℓi hρ
          (ih i (by omega) hℓi fun j hj ↦ hℓn j (by omega))
    refine (isBigO_iteratedFDeriv_succ_exp (by exact_mod_cast hℓ) (fun i _ hi ↦ hℓn i hi)
      hen).congr' ?_ EventuallyEq.rfl
    filter_upwards [hℓ] with y hy
    rw [fun_iteratedFDeriv_sub_apply hy.exp contDiffAt_const,
      iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, sub_zero]

/-- **Bounded derivatives of `exp ℓ`.** Under the hypotheses of
`TauCeti.isBigO_iteratedFDeriv_exp_sub_one`, the derivative of order `n` of `y ↦ exp (ℓ y)` is
bounded along the filter. -/
theorem isBigO_iteratedFDeriv_exp {n : ℕ} (hℓ : ∀ᶠ y in l, ContDiffAt ℝ n ℓ y)
    (hℓ0 : Tendsto ℓ l (𝓝 0)) (hρ : ρ =O[l] fun _ ↦ (1 : ℝ))
    (hℓn : ∀ i ≤ n, iteratedFDeriv ℝ i ℓ =O[l] ρ) :
    iteratedFDeriv ℝ n (fun y ↦ Real.exp (ℓ y)) =O[l] fun _ ↦ (1 : ℝ) :=
  isBigO_iteratedFDeriv_exp_of_sub_one hℓ hρ (isBigO_iteratedFDeriv_exp_sub_one hℓ hℓ0 hρ hℓn)

/-- The commutator `Dᵏ (exp ℓ) - exp ℓ • Dᵏ ℓ`. -/
private noncomputable def expCommutator (ℓ : D → ℝ) (k : ℕ) (y : D) : D [×k]→L[ℝ] ℝ :=
  iteratedFDeriv ℝ k (fun z ↦ Real.exp (ℓ z)) y - Real.exp (ℓ y) • iteratedFDeriv ℝ k ℓ y

private theorem contDiffAt_expCommutator {k m : ℕ} {y : D} (hy : ContDiffAt ℝ (k + m) ℓ y) :
    ContDiffAt ℝ m (expCommutator ℓ k) y :=
  (hy.exp.iteratedFDeriv_right (by norm_cast; omega)).sub
    ((hy.exp.of_le (by norm_cast; omega)).smul
      (hy.iteratedFDeriv_right (by norm_cast; omega)))

private theorem expCommutator_one_apply {y : D} (hy : DifferentiableAt ℝ ℓ y) :
    expCommutator ℓ 1 y = 0 := by
  ext m
  simp [expCommutator, iteratedFDeriv_one_apply, fderiv_exp hy]

/-- The recursion `Cₖ₊₁ = D Cₖ + D (exp ℓ) ⊗ Dᵏ ℓ`, up to the currying isometry. -/
private theorem expCommutator_succ_apply {k : ℕ} {y : D} (hy : ContDiffAt ℝ (k + 1) ℓ y) :
    expCommutator ℓ (k + 1) y = (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (k + 1) ↦ D) ℝ).symm (fderiv ℝ (expCommutator ℓ k) y +
        (fderiv ℝ (fun y ↦ Real.exp (ℓ y)) y).smulRight (iteratedFDeriv ℝ k ℓ y)) := by
  have hdC : DifferentiableAt ℝ (expCommutator ℓ k) y :=
    (contDiffAt_expCommutator (m := 1) hy).differentiableAt (by simp)
  have hdℓ : DifferentiableAt ℝ (iteratedFDeriv ℝ k ℓ) y :=
    (hy.iteratedFDeriv_right (m := 1) (by norm_cast; omega)).differentiableAt (by simp)
  have hde : DifferentiableAt ℝ (fun y ↦ Real.exp (ℓ y)) y :=
    (hy.differentiableAt (by simp)).exp
  -- Differentiate `Dᵏ (exp ℓ) = Cₖ + exp ℓ • Dᵏ ℓ`.
  have hDe : fderiv ℝ (iteratedFDeriv ℝ k fun y ↦ Real.exp (ℓ y)) y =
      fderiv ℝ (expCommutator ℓ k) y + (Real.exp (ℓ y) • fderiv ℝ (iteratedFDeriv ℝ k ℓ) y +
        (fderiv ℝ (fun y ↦ Real.exp (ℓ y)) y).smulRight (iteratedFDeriv ℝ k ℓ y)) := by
    have hsplit : (iteratedFDeriv ℝ k fun y ↦ Real.exp (ℓ y)) =
        fun x ↦ expCommutator ℓ k x + Real.exp (ℓ x) • iteratedFDeriv ℝ k ℓ x := by
      funext x
      simp [expCommutator]
    rw [hsplit]
    exact (hdC.hasFDerivAt.add (hde.hasFDerivAt.smul hdℓ.hasFDerivAt)).fderiv
  simp only [expCommutator, iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hDe, map_add,
    map_smul]
  abel

/-- **Asymptotic bounds on the commutator `Dᵏ (exp ℓ) - exp ℓ • Dᵏ ℓ`.** Along any filter, let `ℓ`
be eventually `C^(n + 1)`, with derivatives of order at most `n` that are `O(ρ)`, and let the
derivatives of `exp ℓ` of order at most `n` be bounded. For `1 ≤ k` and `j + k ≤ n + 1`, the
order-`j` derivative of the commutator `y ↦ Dᵏ (exp ℓ) y - exp (ℓ y) • Dᵏ ℓ y` is then `O(ρ)`.
The derivative of order `k` of `ℓ` cancels from the commutator, which involves only derivatives of
`ℓ` of order below `k`. -/
theorem isBigO_iteratedFDeriv_iteratedFDeriv_exp_sub_smul {n : ℕ}
    (hℓ : ∀ᶠ y in l, ContDiffAt ℝ (n + 1) ℓ y)
    (hℓn : ∀ i ≤ n, iteratedFDeriv ℝ i ℓ =O[l] ρ)
    (hen : ∀ i ≤ n, iteratedFDeriv ℝ i (fun y ↦ Real.exp (ℓ y)) =O[l] fun _ ↦ (1 : ℝ))
    {k : ℕ} (hk : 1 ≤ k) {j : ℕ} (hjk : j + k ≤ n + 1) :
    iteratedFDeriv ℝ j (fun y ↦ iteratedFDeriv ℝ k (fun z ↦ Real.exp (ℓ z)) y -
      Real.exp (ℓ y) • iteratedFDeriv ℝ k ℓ y) =O[l] ρ := by
  change iteratedFDeriv ℝ j (expCommutator ℓ k) =O[l] ρ
  induction k, hk using Nat.le_induction generalizing j with
  | base =>
    refine (isBigO_zero ρ l).congr' ?_ EventuallyEq.rfl
    filter_upwards [hℓ] with y hy
    have hC : expCommutator ℓ 1 =ᶠ[𝓝 y] 0 := (hy.eventually (by simp)).mono fun z hz ↦
      expCommutator_one_apply (hz.differentiableAt (by simp))
    rw [(hC.iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_zero, Pi.zero_apply]
  | succ k hk ih =>
    have hde : ∀ᶠ y in l, ContDiffAt ℝ (j + 1) (fun y ↦ Real.exp (ℓ y)) y :=
      hℓ.mono fun y hy ↦ hy.exp.of_le (by norm_cast; omega)
    have hdℓ : ∀ᶠ y in l, ContDiffAt ℝ j (iteratedFDeriv ℝ k ℓ) y :=
      hℓ.mono fun y hy ↦ hy.iteratedFDeriv_right (by norm_cast; omega)
    -- The term `D (exp ℓ) ⊗ Dᵏ ℓ`.
    have hT := isBigO_iteratedFDeriv_smulRight (n := j)
      (hde.mono fun y hy ↦ hy.fderiv_right le_rfl) hdℓ
      (fun i hi ↦ (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_fderiv.le).trans
        (hen (i + 1) (by omega)))
      (fun i hi ↦ (isBigO_of_le _ fun y ↦ (norm_iteratedFDeriv_iteratedFDeriv ℓ i k y).le).trans
        (hℓn (i + k) (by omega)))
    simp only [one_mul] at hT
    -- The term `D Cₖ`.
    have hF : iteratedFDeriv ℝ j (fderiv ℝ (expCommutator ℓ k)) =O[l] ρ :=
      (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_fderiv.le).trans (ih (j := j + 1) (by omega))
    refine (IsBigO.of_bound 1 ?_).trans (hF.add hT)
    filter_upwards [hℓ, hde, hdℓ] with y hy hdey hdℓy
    have hrec : expCommutator ℓ (k + 1) =ᶠ[𝓝 y] (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (k + 1) ↦ D) ℝ).symm ∘ fun y ↦ fderiv ℝ (expCommutator ℓ k) y +
          (fderiv ℝ (fun y ↦ Real.exp (ℓ y)) y).smulRight (iteratedFDeriv ℝ k ℓ y) :=
      ((hy.of_le (by norm_cast; omega) : ContDiffAt ℝ (k + 1) ℓ y).eventually (by simp)).mono
        fun z hz ↦ expCommutator_succ_apply hz
    -- The spaces are given explicitly: unifying them against the instances carried by the
    -- currying isometry otherwise fails.
    rw [one_mul, (hrec.iteratedFDeriv ℝ j).eq_of_nhds,
      LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := D)
        (F := D →L[ℝ] D [×k]→L[ℝ] ℝ) (G := D [×k + 1]→L[ℝ] ℝ),
      fun_iteratedFDeriv_add_apply
        ((contDiffAt_expCommutator (k := k) (m := j + 1)
          (hy.of_le (by norm_cast; omega))).fderiv_right le_rfl)
        ((hdey.fderiv_right le_rfl).smulRight hdℓy)]

end Asymptotics

end TauCeti
