/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Fredholm
public import TauCeti.Analysis.Calculus.Morse.OneDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The interval base of a continuation: regularity of its scalar operators

A continuation between two Morse functions `f₀` and `f₁` on `X` can be realized as a Morse
function on the product `X × ℝ`, of the form `F(x, t) = C h(t) + f_t(x)` with the double-well
`h(t) = (t² - 1)² / 4` and a large constant `C > 0`. This file studies its base factor, the
function `C h` of the parameter `t` alone (`TauCeti.intervalBasePotential`).

Its negative gradient is the field `a(t) = C t (1 - t²)`. The critical point `0` is a local
maximum, of Morse index `1`, and `1` is a local minimum, of Morse index `0`; the Hessians there
are `-C` and `2 C`. So `0 → 1` is the source-to-sink flow of the parameter, and the endpoint index
shifts of a continuation are `1` at `t = 0` and `0` at `t = 1`. One trajectory from `0` to `1` is

`q(s) = 1 / √(1 + e^{-2 C s})` (`TauCeti.intervalBaseOrbit`),

and along every solution in `(0, 1)` the coordinate `U(t) = log t - (1 / 2) log (1 - t²)`
(`TauCeti.intervalBaseTimeCoordinate`) advances at the constant rate `C`; along `q` it is `C s`.

The main results verify that this base is regular, in the sense needed to glue continuation
moduli spaces over it. Along every trajectory `γ` from `0` to `1`, the linearized operator
`ξ ↦ ξ' - a'(γ) ξ` from `W^{1,2}(ℝ, ℝ)` to `L²(ℝ, ℝ)` is Fredholm of index `1`; its kernel is the
line spanned by the velocity `γ'`; it is surjective; and its formal adjoint `-d/ds - a'(γ)` is
injective. At the constant trajectories the linearized operators `d/ds - C` and `d/ds + 2 C` are
bijective.

## Main declarations

* `TauCeti.intervalBasePotential`: the function `C (t² - 1)² / 4`.
* `TauCeti.isNondegenerateCriticalPoint_intervalBasePotential_zero`,
  `TauCeti.morseIndex_intervalBasePotential_zero` and their analogues at `1`: the two critical
  points and their Morse indices.
* `TauCeti.intervalBaseOrbit` and `TauCeti.isIntegralCurve_intervalBaseOrbit`: a trajectory from
  `0` to `1`.
* `TauCeti.intervalBaseTimeCoordinate` and
  `TauCeti.intervalBaseTimeCoordinate_intervalBaseOrbit`: the coordinate `U` with `U(q(s)) = C s`.
* `TauCeti.index_trajectoryOperator_intervalBasePotential`,
  `TauCeti.exists_ker_trajectoryOperator_intervalBasePotential_eq_span`,
  `TauCeti.surjective_trajectoryOperator_intervalBasePotential` and
  `TauCeti.ker_trajectoryOperator_neg_intervalBasePotential_eq_bot`: the operator along a
  trajectory from `0` to `1`.
* `TauCeti.bijective_trajectoryOperator_intervalBasePotential_zero` and
  `TauCeti.bijective_trajectoryOperator_intervalBasePotential_one`: the operators at the constant
  trajectories.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4 (continuation maps).
* M. Schwarz, *Morse Homology*, Progress in Mathematics **111**, Birkhäuser, 1993, Chapter 2
  (the linearized trajectory operator).
-/

public section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Gradient Topology

namespace TauCeti

variable {C : ℝ}

/-! ### The potential -/

/-- The base potential `C h(t)` of a continuation, with `h(t) = (t² - 1)² / 4`. Its negative
gradient is `C t (1 - t²)`. -/
noncomputable def intervalBasePotential (C : ℝ) (t : ℝ) : ℝ :=
  C * ((t ^ 2 - 1) ^ 2 / 4)

theorem intervalBasePotential_apply (C t : ℝ) :
    intervalBasePotential C t = C * ((t ^ 2 - 1) ^ 2 / 4) := (rfl)

/-- The base potential is a polynomial, hence smooth. -/
theorem contDiff_intervalBasePotential (C : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (intervalBasePotential C) := by
  unfold intervalBasePotential
  fun_prop

/-- The derivative of the base potential is `C t (t² - 1)`. -/
theorem hasDerivAt_intervalBasePotential (C t : ℝ) :
    HasDerivAt (intervalBasePotential C) (C * t * (t ^ 2 - 1)) t := by
  refine (((((hasDerivAt_pow 2 t).sub_const 1).pow 2).div_const 4).const_mul C).congr_deriv ?_
  norm_num
  ring

theorem deriv_intervalBasePotential (C : ℝ) :
    deriv (intervalBasePotential C) = fun t ↦ C * t * (t ^ 2 - 1) :=
  funext fun t ↦ (hasDerivAt_intervalBasePotential C t).deriv

/-- The gradient of the base potential is `C t (t² - 1)`, so its negative gradient is the field
`C t (1 - t²)`. -/
theorem gradient_intervalBasePotential (C t : ℝ) :
    ∇ (intervalBasePotential C) t = C * t * (t ^ 2 - 1) := by
  rw [gradient_eq_deriv', deriv_intervalBasePotential]

/-- The second derivative of the base potential is `C (3 t² - 1)`: it is `-C` at `0` and `2 C` at
`1`. -/
theorem iteratedDeriv_two_intervalBasePotential (C t : ℝ) :
    iteratedDeriv 2 (intervalBasePotential C) t = C * (3 * t ^ 2 - 1) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_intervalBasePotential]
  refine (((hasDerivAt_id t).const_mul C).mul ((hasDerivAt_pow 2 t).sub_const 1)).congr_deriv
    ?_ |>.deriv
  simp only [id, Nat.cast_ofNat]
  ring

/-- The Hessian operator of the base potential at `t` is multiplication by `C (3 t² - 1)`. -/
theorem hessianOperator_intervalBasePotential (C t : ℝ) :
    hessianOperator (intervalBasePotential C) t =
      (C * (3 * t ^ 2 - 1)) • ContinuousLinearMap.id ℝ ℝ := by
  rw [hessianOperator_real, iteratedDeriv_two_intervalBasePotential]

/-! ### The critical points -/

/-- For `C ≠ 0`, `0` is a nondegenerate critical point of the base potential, with Hessian `-C`. -/
theorem isNondegenerateCriticalPoint_intervalBasePotential_zero (hC : C ≠ 0) :
    IsNondegenerateCriticalPoint (intervalBasePotential C) 0 := by
  rw [isNondegenerateCriticalPoint_real_iff (contDiff_intervalBasePotential C).contDiffAt,
    iteratedDeriv_two_intervalBasePotential, deriv_intervalBasePotential]
  simpa using hC

/-- For `C ≠ 0`, `1` is a nondegenerate critical point of the base potential, with Hessian `2 C`.
-/
theorem isNondegenerateCriticalPoint_intervalBasePotential_one (hC : C ≠ 0) :
    IsNondegenerateCriticalPoint (intervalBasePotential C) 1 := by
  rw [isNondegenerateCriticalPoint_real_iff (contDiff_intervalBasePotential C).contDiffAt,
    iteratedDeriv_two_intervalBasePotential, deriv_intervalBasePotential]
  norm_num [hC]

/-- For `C > 0` the critical point `0` of the base potential is a local maximum: its Morse index
is `1`. -/
theorem morseIndex_intervalBasePotential_zero (hC : 0 < C) :
    morseIndex (intervalBasePotential C) 0 = 1 :=
  (isNondegenerateCriticalPoint_intervalBasePotential_zero hC.ne').morseIndex_real_of_neg
    (by rw [iteratedDeriv_two_intervalBasePotential]; linarith)

/-- For `C > 0` the critical point `1` of the base potential is a local minimum: its Morse index
is `0`. -/
theorem morseIndex_intervalBasePotential_one (hC : 0 < C) :
    morseIndex (intervalBasePotential C) 1 = 0 :=
  (isNondegenerateCriticalPoint_intervalBasePotential_one hC.ne').morseIndex_real_of_pos
    (by rw [iteratedDeriv_two_intervalBasePotential]; linarith)

/-! ### A trajectory from `0` to `1` and the time coordinate -/

/-- The trajectory `q(s) = 1 / √(1 + e^{-2 C s})` of the negative gradient field `C t (1 - t²)` of
the base potential. For `C > 0` it runs from `0` at `-∞` to `1` at `+∞`. -/
noncomputable def intervalBaseOrbit (C s : ℝ) : ℝ :=
  (√(1 + Real.exp (-(2 * C * s))))⁻¹

theorem intervalBaseOrbit_apply (C s : ℝ) :
    intervalBaseOrbit C s = (√(1 + Real.exp (-(2 * C * s))))⁻¹ := (rfl)

/-- The square of the trajectory `q` is `1 / (1 + e^{-2 C s})`. -/
theorem intervalBaseOrbit_sq (C s : ℝ) :
    intervalBaseOrbit C s ^ 2 = (1 + Real.exp (-(2 * C * s)))⁻¹ := by
  rw [intervalBaseOrbit, inv_pow, Real.sq_sqrt (by positivity)]

/-- The trajectory `q` takes values in `(0, 1)`. -/
theorem intervalBaseOrbit_mem_Ioo (C s : ℝ) : intervalBaseOrbit C s ∈ Ioo 0 1 := by
  have h1 : 1 < √(1 + Real.exp (-(2 * C * s))) :=
    Real.lt_sqrt_of_sq_lt (by nlinarith [Real.exp_pos (-(2 * C * s))])
  exact ⟨by unfold intervalBaseOrbit; positivity, inv_lt_one_of_one_lt₀ h1⟩

/-- The trajectory `q` solves `q' = C q (1 - q²)`. -/
theorem hasDerivAt_intervalBaseOrbit (C s : ℝ) :
    HasDerivAt (intervalBaseOrbit C)
      (C * intervalBaseOrbit C s * (1 - intervalBaseOrbit C s ^ 2)) s := by
  set w := 1 + Real.exp (-(2 * C * s)) with hw
  have hw0 : 0 < w := by positivity
  have hsq : 0 < √w := Real.sqrt_pos.2 hw0
  have hexp : HasDerivAt (fun s ↦ 1 + Real.exp (-(2 * C * s)))
      (Real.exp (-(2 * C * s)) * -(2 * C)) s := by
    have := ((hasDerivAt_id s).const_mul (2 * C)).neg.exp.const_add 1
    simpa using this
  refine ((hexp.sqrt hw0.ne').inv hsq.ne').congr_deriv ?_
  rw [intervalBaseOrbit_sq, intervalBaseOrbit, ← hw, Real.sq_sqrt hw0.le]
  field_simp
  rw [hw]
  ring

theorem tendsto_intervalBaseOrbit_atBot (hC : 0 < C) :
    Tendsto (intervalBaseOrbit C) atBot (𝓝 0) := by
  have h : Tendsto (fun s ↦ 1 + Real.exp (-(2 * C * s))) atBot atTop :=
    tendsto_atTop_add_const_left _ _ (Real.tendsto_exp_atTop.comp
      (tendsto_neg_atBot_atTop.comp (tendsto_id.const_mul_atBot (by positivity))))
  exact (Real.tendsto_sqrt_atTop.comp h).inv_tendsto_atTop

theorem tendsto_intervalBaseOrbit_atTop (hC : 0 < C) :
    Tendsto (intervalBaseOrbit C) atTop (𝓝 1) := by
  have h : Tendsto (fun s ↦ 1 + Real.exp (-(2 * C * s))) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by positivity))))
  have h' := ((Real.continuous_sqrt.tendsto _).comp h).inv₀ (by norm_num)
  rw [add_zero, Real.sqrt_one, inv_one] at h'
  exact h'

/-- The trajectory `q` is a negative gradient trajectory of the base potential. -/
theorem isIntegralCurve_intervalBaseOrbit (C : ℝ) :
    IsIntegralCurve (intervalBaseOrbit C) (fun _ t ↦ -∇ (intervalBasePotential C) t) := by
  intro s
  refine (hasDerivAt_intervalBaseOrbit C s).congr_deriv ?_
  dsimp only
  rw [gradient_intervalBasePotential]
  ring

/-- The time coordinate `U(t) = log t - (1 / 2) log (1 - t²)` of the base flow on `(0, 1)`. Along
every solution of `t' = C t (1 - t²)` in `(0, 1)` it advances at rate `C`
(`HasDerivAt.intervalBaseTimeCoordinate_comp`). -/
noncomputable def intervalBaseTimeCoordinate (t : ℝ) : ℝ :=
  Real.log t - Real.log (1 - t ^ 2) / 2

theorem intervalBaseTimeCoordinate_apply (t : ℝ) :
    intervalBaseTimeCoordinate t = Real.log t - Real.log (1 - t ^ 2) / 2 := (rfl)

/-- On `(0, 1)` the derivative of the time coordinate is `1 / (t (1 - t²))`. -/
theorem hasDerivAt_intervalBaseTimeCoordinate {t : ℝ} (ht : t ∈ Ioo 0 1) :
    HasDerivAt intervalBaseTimeCoordinate (t * (1 - t ^ 2))⁻¹ t := by
  have h1 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  refine ((Real.hasDerivAt_log ht.1.ne').sub
    ((((hasDerivAt_pow 2 t).const_sub 1).log h1.ne').div_const 2)).congr_deriv ?_
  field_simp [ht.1.ne', h1.ne']
  ring

/-- **The time coordinate advances at rate `C`.** Along a solution of `x' = C x (1 - x²)` taking
values in `(0, 1)`, the derivative of `U ∘ x` is `C`. -/
theorem _root_.HasDerivAt.intervalBaseTimeCoordinate_comp {x : ℝ → ℝ} {s : ℝ}
    (hx : HasDerivAt x (C * x s * (1 - x s ^ 2)) s) (hxs : x s ∈ Ioo 0 1) :
    HasDerivAt (fun s ↦ intervalBaseTimeCoordinate (x s)) C s := by
  have h1 : 0 < 1 - x s ^ 2 := by nlinarith [hxs.1, hxs.2]
  refine ((hasDerivAt_intervalBaseTimeCoordinate hxs).comp s hx).congr_deriv ?_
  field_simp [hxs.1.ne', h1.ne']

/-- Along the trajectory `q` the time coordinate is exactly `C s`. -/
theorem intervalBaseTimeCoordinate_intervalBaseOrbit (C s : ℝ) :
    intervalBaseTimeCoordinate (intervalBaseOrbit C s) = C * s := by
  have hw0 : 0 < 1 + Real.exp (-(2 * C * s)) := by positivity
  have h1 : 1 - intervalBaseOrbit C s ^ 2 =
      Real.exp (-(2 * C * s)) * (1 + Real.exp (-(2 * C * s)))⁻¹ := by
    rw [intervalBaseOrbit_sq]
    field_simp
    ring
  rw [intervalBaseTimeCoordinate, h1, intervalBaseOrbit, Real.log_inv, Real.log_sqrt hw0.le,
    Real.log_mul (Real.exp_pos _).ne' (inv_ne_zero hw0.ne'), Real.log_exp, Real.log_inv]
  ring

/-! ### Regularity of the linearized operators -/

section Operator

open TauCeti.WeakDerivStep

variable {γ : ℝ → ℝ}
  {AL : Lp (ℝ →L[ℝ] ℝ) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}

/-- Along a trajectory of the base flow from `0` to `1`, the linearized operator
`ξ ↦ ξ' - a'(γ) ξ`, with `a(t) = C t (1 - t²)`, is Fredholm. -/
theorem isFredholm_trajectoryOperator_intervalBasePotential (hC : C ≠ 0)
    (hγ : IsIntegralCurve γ (fun _ t ↦ -∇ (intervalBasePotential C) t))
    (hbot : Tendsto γ atBot (𝓝 0)) (htop : Tendsto γ atTop (𝓝 1))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (intervalBasePotential C) (γ s)) :
    (trajectoryOperator (p := 2) AL).IsFredholm :=
  hγ.isFredholm_trajectoryOperator_hessianOperator (contDiff_intervalBasePotential C)
    (isNondegenerateCriticalPoint_intervalBasePotential_zero hC)
    (isNondegenerateCriticalPoint_intervalBasePotential_one hC) hbot htop hAL

/-- **The base operator has index one.** For `C > 0`, along a trajectory of the base flow from
`0` to `1`, the linearized operator `ξ ↦ ξ' - a'(γ) ξ` has index `1`, the drop of the Morse index
from the maximum `0` to the minimum `1`. -/
theorem index_trajectoryOperator_intervalBasePotential (hC : 0 < C)
    (hγ : IsIntegralCurve γ (fun _ t ↦ -∇ (intervalBasePotential C) t))
    (hbot : Tendsto γ atBot (𝓝 0)) (htop : Tendsto γ atTop (𝓝 1))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (intervalBasePotential C) (γ s)) :
    (trajectoryOperator (p := 2) AL).index = 1 := by
  rw [hγ.index_trajectoryOperator_hessianOperator (contDiff_intervalBasePotential C)
    (isNondegenerateCriticalPoint_intervalBasePotential_zero hC.ne')
    (isNondegenerateCriticalPoint_intervalBasePotential_one hC.ne') hbot htop hAL,
    morseIndex_intervalBasePotential_zero hC, morseIndex_intervalBasePotential_one hC]
  simp

/-- **The kernel of the base operator is spanned by the velocity.** Along a trajectory `γ` of
the base flow from `0` to `1`, the kernel of `ξ ↦ ξ' - a'(γ) ξ` on `W^{1,2}(ℝ, ℝ)` is the line
through the element whose value is `γ'`. -/
theorem exists_ker_trajectoryOperator_intervalBasePotential_eq_span
    (hγ : IsIntegralCurve γ (fun _ t ↦ -∇ (intervalBasePotential C) t))
    (hbot : Tendsto γ atBot (𝓝 0)) (htop : Tendsto γ atTop (𝓝 1))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (intervalBasePotential C) (γ s)) :
    ∃ u : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      ⇑(prev (ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u)
          =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] deriv γ ∧
        (trajectoryOperator (p := 2) AL).ker = ℝ ∙ u :=
  hγ.exists_ker_trajectoryOperator_hessianOperator_eq_span (Module.finrank_self ℝ)
    (contDiff_intervalBasePotential C) hbot htop zero_ne_one hAL

/-- **The base operator is onto.** For `C > 0`, along a trajectory of the base flow from `0` to
`1`, the linearized operator `ξ ↦ ξ' - a'(γ) ξ` from `W^{1,2}(ℝ, ℝ)` to `L²(ℝ, ℝ)` is
surjective. -/
theorem surjective_trajectoryOperator_intervalBasePotential (hC : 0 < C)
    (hγ : IsIntegralCurve γ (fun _ t ↦ -∇ (intervalBasePotential C) t))
    (hbot : Tendsto γ atBot (𝓝 0)) (htop : Tendsto γ atTop (𝓝 1))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (intervalBasePotential C) (γ s)) :
    Function.Surjective (trajectoryOperator (p := 2) AL) :=
  (hγ.surjective_trajectoryOperator_hessianOperator_iff (Module.finrank_self ℝ)
    (contDiff_intervalBasePotential C)
    (isNondegenerateCriticalPoint_intervalBasePotential_zero hC.ne')
    (isNondegenerateCriticalPoint_intervalBasePotential_one hC.ne') hbot htop zero_ne_one hAL).2
    (by rw [morseIndex_intervalBasePotential_zero hC, morseIndex_intervalBasePotential_one hC])

/-- **The adjoint of the base operator is injective.** For `C > 0`, along a trajectory of the
base flow from `0` to `1`, the formal adjoint `-d/ds - a'(γ)` of the linearized operator has
trivial kernel on `W^{1,2}(ℝ, ℝ)`: the kernel of `ξ ↦ ξ' + a'(γ) ξ` vanishes. -/
theorem ker_trajectoryOperator_neg_intervalBasePotential_eq_bot (hC : 0 < C)
    (hγ : IsIntegralCurve γ (fun _ t ↦ -∇ (intervalBasePotential C) t))
    (hbot : Tendsto γ atBot (𝓝 0)) (htop : Tendsto γ atTop (𝓝 1))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (intervalBasePotential C) (γ s)) :
    (trajectoryOperator (p := 2) (-AL)).ker = ⊥ := by
  have hadj : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      AL s = ContinuousLinearMap.adjoint (AL s) := by
    filter_upwards [hAL] with s hs
    rw [hs]
    exact (contDiff_intervalBasePotential C).contDiffAt.isSelfAdjoint_hessianOperator.isSymmetric
      |>.clm_adjoint_eq.symm
  exact (surjective_trajectoryOperator_iff_ker_neg_eq_bot hadj
    (isFredholm_trajectoryOperator_intervalBasePotential hC.ne' hγ hbot htop hAL).isClosed_range).1
    (surjective_trajectoryOperator_intervalBasePotential hC hγ hbot htop hAL)

/-- **The base operator at the maximum is invertible.** For `C ≠ 0`, the linearized operator at
the constant trajectory at `0`, which is `ξ ↦ ξ' - C ξ`, is a bijection from `W^{1,2}(ℝ, ℝ)` onto
`L²(ℝ, ℝ)`. -/
theorem bijective_trajectoryOperator_intervalBasePotential_zero (hC : C ≠ 0)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun _ ↦ hessianOperator (intervalBasePotential C) 0) :
    Function.Bijective (trajectoryOperator (p := 2) AL) :=
  IsNondegenerateCriticalPoint.bijective_trajectoryOperator_hessianOperator
    (isNondegenerateCriticalPoint_intervalBasePotential_zero hC) hAL

/-- **The base operator at the minimum is invertible.** For `C ≠ 0`, the linearized operator at
the constant trajectory at `1`, which is `ξ ↦ ξ' + 2 C ξ`, is a bijection from `W^{1,2}(ℝ, ℝ)`
onto `L²(ℝ, ℝ)`. -/
theorem bijective_trajectoryOperator_intervalBasePotential_one (hC : C ≠ 0)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun _ ↦ hessianOperator (intervalBasePotential C) 1) :
    Function.Bijective (trajectoryOperator (p := 2) AL) :=
  IsNondegenerateCriticalPoint.bijective_trajectoryOperator_hessianOperator
    (isNondegenerateCriticalPoint_intervalBasePotential_one hC) hAL

end Operator

end TauCeti

end
