/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Topology.Algebra.Algebra
import TauCeti.Analysis.Analytic.ConstantOrder.Basic
import TauCeti.Analysis.Analytic.Inverse
import TauCeti.Analysis.Analytic.IteratedDeriv
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.IteratedDeriv.Leibniz
import TauCeti.Analysis.Calculus.JointImplicitFunction
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.HolomorphicFunctions.DiscAlgebra
import TauCeti.Analysis.Complex.LocalNormalForm

/-!
# The holomorphic Chester-Friedman-Ursell cubic normal form

Let `p(α, t)` be a holomorphic function on `E × ℂ` (with `E` a finite-dimensional complex normed
space) near `(α₀, t₀)` at which two critical points in `t` coalesce: `∂p/∂t = ∂²p/∂t² = 0` and
`∂³p/∂t³ ≠ 0` at `(α₀, t₀)`. The theorem of Chester, Friedman and Ursell (proved holomorphically in
several variables by Levinson) provides a parameter-dependent biholomorphic change of the
integration variable `t ↦ w(α, t)` near `(α₀, t₀)` together with holomorphic coefficient functions
`ζ(α)` and `η(α)` near `α₀` such that `ζ(α₀) = 0`, `η(α₀) = p(α₀, t₀)`, `w(α₀, t₀) = 0`,
`∂w/∂t (α₀, t₀) ≠ 0`, and locally `p(α, t) = w(α, t) ^ 3 / 3 - ζ(α) * w(α, t) + η(α)`.

This reduction is the geometric heart of uniform Airy asymptotic approximations for contour
integrals with two coalescing saddle points: under `u = w(α, t)` with local inverse `t = T(α, u)`
(see `AnalyticAt.exists_analyticAt_mul_deriv_eq` in
`TauCeti.Analysis.Calculus.JointImplicitFunction`), an oscillatory integral
`∫ exp(-z p(α, t)) q(α, t) dt` becomes
`exp(-z η(α)) ∫ exp(-z (u ^ 3 / 3 - ζ(α) u)) f(α, u) du` with holomorphic transformed amplitude
`f(α, u) = q(α, T(α, u)) ∂T/∂u (α, u)`, and the critical points `∂p/∂t = 0` near `(α₀, t₀)` map
bijectively to the two square roots `w ^ 2 = ζ(α)`.

The existence of the cubic normal form requires only `∂p/∂t = ∂²p/∂t² = 0` and `∂³p/∂t³ ≠ 0`. For
a one-dimensional complex parameter `α`, the mixed-derivative condition `∂²p/∂α∂t (α₀, t₀) ≠ 0` is
equivalent to `ζ'(α₀) ≠ 0` (`TauCeti.CubicNormalForm.deriv_ne_zero_iff_deriv_deriv_ne_zero`), which
governs whether `ζ` is a local coordinate in `α` so that the critical points coalesce at the generic
square-root rate `√(α - α₀)`.

## Main results

* `TauCeti.exists_deriv_eq_add_sq_mul`: local inflection curve `τ(α)` with `∂²p/∂t² (α, τ(α)) = 0`
  and quadratic remainder `∂p/∂t (α, τ(α) + s) = c(α) + s ^ 2 * U(α, s)`.
* `AnalyticAt.exists_cubic_normal_form`, `TauCeti.exists_cubic_normal_form`: the holomorphic
  Chester-Friedman-Ursell cubic normal form `p(α, t) = w(α, t) ^ 3 / 3 - ζ(α) * w(α, t) + η(α)`
  for an arbitrary finite-dimensional complex parameter space `E`.
* `TauCeti.add_pow_three_div_three_sub_mul_add`, `TauCeti.exists_translated_cubic_normal_form`:
  equivalence with the translated cubic normal form `u ^ 3 / 3 + a(α) u ^ 2 + b(α) u + c(α)`.
* `TauCeti.CubicNormalForm.hasDerivAt_sq_sub_mul`,
  `TauCeti.CubicNormalForm.deriv_eq_sq_sub_mul_deriv`,
  `TauCeti.CubicNormalForm.deriv_eq_zero_iff_sq_eq`,
  `TauCeti.CubicNormalForm.eventually_deriv_eq_zero_iff_sq_eq`,
  `TauCeti.CubicNormalForm.exists_bijOn_deriv_eq_zero_sq_eq`,
  `TauCeti.CubicNormalForm.exists_bijOn_deriv_eq_zero_sq_eq_of_eq_zero`: derivative factorization
  `∂p/∂t = (w ^ 2 - ζ) ∂w/∂t`, critical-point correspondence
  `∂p/∂t (α, t) = 0 ↔ w(α, t) ^ 2 = ζ(α)`, and local bijection between the critical and root
  loci (including onto the full set of square roots near a centered point).
* `TauCeti.CubicNormalForm.hasDerivAt_deriv_deriv_two_mul_deriv_pow_three`,
  `TauCeti.CubicNormalForm.deriv_deriv_deriv_eq_two_mul_deriv_pow_three`,
  `TauCeti.CubicNormalForm.hasDerivAt_deriv_neg_mul_deriv`,
  `TauCeti.CubicNormalForm.deriv_deriv_eq_neg_deriv_mul_deriv`,
  `TauCeti.CubicNormalForm.deriv_ne_zero_iff_deriv_deriv_ne_zero`: jet identities
  `∂³p/∂t³ = 2 (∂w/∂t) ^ 3` (under `C²` regularity over any normed field of characteristic `≠ 3`)
  and `∂²p/∂α∂t = -ζ'(α₀) ∂w/∂t`, characterizing nondegenerate square-root coalescence
  `ζ'(α₀) ≠ 0`.

## References

* C. Chester, B. Friedman, F. Ursell, *An extension of the method of steepest descents*, Proc.
  Cambridge Philos. Soc. **53** (1957), 599-611.
* N. Levinson, *Transformation of an analytic function of several variables to a canonical form*,
  Duke Math. J. **28** (1961), 345-353.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press (1974), Chapter 9, §12.
* NIST Digital Library of Mathematical Functions, §2.4(v), equations (2.4.17)-(2.4.20),
  <https://dlmf.nist.gov/2.4.v>.
-/

public section

open Complex Filter Metric Set Topology

namespace TauCeti

/-! ### Local inflection decomposition -/

/-- **Local inflection curve and quadratic remainder of `∂p/∂t`.** Let `p(α, t)` be holomorphic on
a neighbourhood `V` of `(α₀, t₀)` with `∂²p/∂t² (α₀, t₀) = 0` and `∂³p/∂t³ (α₀, t₀) ≠ 0`. Then
there exist analytic functions `τ` and `c` at `α₀` and `U` at `(α₀, 0)` such that `τ(α₀) = t₀`,
`∂²p/∂t² (α, τ(α)) = 0` near `α₀`, and `∂p/∂t (α, τ(α) + s) = c(α) + s ^ 2 * U(α, s)` near
`(α₀, 0)`, with `c(α₀) = ∂p/∂t (α₀, t₀)`, `c'(α₀) = ∂²p/∂α∂t (α₀, t₀)`, and
`U(α₀, 0) = ½ ∂³p/∂t³ (α₀, t₀)`. -/
theorem exists_deriv_eq_add_sq_mul {p : ℂ × ℂ → ℂ} {V : Set (ℂ × ℂ)} {α₀ t₀ : ℂ}
    (hV : V ∈ 𝓝 (α₀, t₀)) (hp : DifferentiableOn ℂ p V)
    (h₂ : deriv (deriv fun t => p (α₀, t)) t₀ = 0)
    (h₃ : deriv (deriv (deriv fun t => p (α₀, t))) t₀ ≠ 0) :
    ∃ τ c : ℂ → ℂ, ∃ U : ℂ × ℂ → ℂ,
      AnalyticAt ℂ τ α₀ ∧ AnalyticAt ℂ c α₀ ∧ AnalyticAt ℂ U (α₀, 0) ∧
      τ α₀ = t₀ ∧ c α₀ = deriv (fun t => p (α₀, t)) t₀ ∧
      deriv c α₀ = deriv (fun α => deriv (fun t => p (α, t)) t₀) α₀ ∧
      U (α₀, 0) = deriv (deriv (deriv fun t => p (α₀, t))) t₀ / 2 ∧
      (∀ᶠ α in 𝓝 α₀, deriv (deriv fun t => p (α, t)) (τ α) = 0) ∧
      ∀ᶠ q in 𝓝 (α₀, 0),
        deriv (fun t => p (q.1, t)) (τ q.1 + q.2) = c q.1 + q.2 ^ 2 * U q := by
  have hpa : AnalyticAt ℂ p (α₀, t₀) := hp.analyticAt_of_finiteDimensional hV
  set p₁ : ℂ × ℂ → ℂ := fun q => deriv (fun t => p (q.1, t)) q.2
  set p₂ : ℂ × ℂ → ℂ := fun q => deriv (deriv fun t => p (q.1, t)) q.2
  have hp₁ : AnalyticAt ℂ p₁ (α₀, t₀) := hpa.deriv_snd
  have hp₂ : AnalyticAt ℂ p₂ (α₀, t₀) := hp₁.deriv_snd
  obtain ⟨τ, hτ, hτ0, hτeq, -⟩ := hp₂.exists_analyticAt_eventually_eq_zero_iff h₂ h₃
  dsimp only at hτ hτ0 hτeq
  set c : ℂ → ℂ := fun α => p₁ (α, τ α)
  have hc : AnalyticAt ℂ c α₀ := hp₁.comp_of_eq (analyticAt_id.prod hτ) (by simp [hτ0])
  have hc_deriv : deriv c α₀ = deriv (fun α => p₁ (α, t₀)) α₀ := by
    have hp₁_at : HasFDerivAt p₁ (fderiv ℂ p₁ (α₀, τ α₀)) (α₀, τ α₀) :=
      (hτ0.symm ▸ hp₁.differentiableAt).hasFDerivAt
    have hzero : fderiv ℂ (fun t => p₁ (α₀, t)) (τ α₀) = 0 := by
      ext
      simpa [hτ0, p₁] using h₂
    have hf := hp₁_at.fderiv_comp_graph_eq_fderiv_slice_of_fderiv_right_eq_zero
      hτ.differentiableAt hzero
    simpa [c, hτ0, fderiv_apply_one_eq_deriv] using congrArg (· (1 : ℂ)) hf
  set g : ℂ × ℂ → ℂ := fun q => p₁ (q.1, τ q.1 + q.2)
  have hg : AnalyticAt ℂ g (α₀, 0) :=
    hp₁.comp_of_eq (analyticAt_fst.prod
      ((hτ.comp_of_eq analyticAt_fst rfl).add analyticAt_snd)) (by simp [hτ0])
  have hg_sub : AnalyticAt ℂ (fun q : ℂ × ℂ => g q - c q.1) (α₀, 0) :=
    hg.sub (hc.comp_of_eq analyticAt_fst rfl)
  have hord : ∀ᶠ α in 𝓝 α₀, ((2 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun s => g (α, s) - c α) 0 := by
    filter_upwards [hτeq, hg_sub.eventually_analyticAt_curry_right] with α hα hGα
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hGα]
    rintro (_ | _ | i) hi
    · simp [g, c]
    · simpa [g, p₁, deriv_comp_const_add] using hα
    · omega
  obtain ⟨U, hU, hGU⟩ := hg_sub.eventually_natCast_le_analyticOrderAt_iff.1 hord
  have hgeq : ∀ᶠ q in 𝓝 (α₀, 0), g q = c q.1 + q.2 ^ 2 * U q :=
    hGU.mono fun q hq => by simp only [sub_zero, smul_eq_mul] at hq; linear_combination hq
  have hU0' : U (α₀, 0) = deriv (deriv (deriv fun t => p (α₀, t))) t₀ / 2 := by
    have hgs : (fun s => g (α₀, s)) =ᶠ[𝓝 0] fun s => c α₀ + s ^ 2 * U (α₀, s) :=
      ((continuous_const.prodMk continuous_id).tendsto (0 : ℂ)).eventually hgeq
    have hdd : iteratedDeriv 2 (fun s => g (α₀, s)) 0 = 2 * U (α₀, 0) := by
      rw [hgs.iteratedDeriv_eq 2, iteratedDeriv_const_add (by norm_num : 0 < 2)]
      simpa using TauCeti.iteratedDeriv_pow_sub_smul_self (n := 2) (a := (0 : ℂ))
        hU.curry_right.contDiffAt
    have htrans : iteratedDeriv 2 (fun s => g (α₀, s)) 0 =
        deriv (deriv (deriv fun t => p (α₀, t))) t₀ := by
      simpa [g, hτ0, p₁, iteratedDeriv_succ', iteratedDeriv_one] using
        congrFun (iteratedDeriv_comp_const_add 2 (fun t => p₁ (α₀, t)) t₀) 0
    rw [← htrans, hdd, mul_div_cancel_left₀ _ two_ne_zero]
  exact ⟨τ, c, U, hτ, hc, hU, hτ0, by simp [c, p₁, hτ0], hc_deriv, hU0', hτeq, hgeq⟩

/-! ### Disc-algebra inverse function construction -/

section DiscAlgebraOperator

/-- Linearization `(δu, (δζ, δη)) ↦ z ^ 2 * δu - δζ * z + δη` of the cubic normal-form operator at
`(DiscAlgebra.coord 0 R, (0, 0))`. -/
private noncomputable def cubicLinearCLM (R : ℝ) :
    (discAlgebra 0 R × (ℂ × ℂ)) →L[ℂ] discAlgebra 0 R :=
  (ContinuousLinearMap.mul ℂ (discAlgebra 0 R) (DiscAlgebra.coord 0 R ^ 2)).comp (.fst ℂ _ _) -
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight (DiscAlgebra.coord 0 R)).comp (.snd ℂ _ _) +
    (algebraMapCLM ℂ (discAlgebra 0 R)).comp ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (.snd ℂ _ _))

private theorem cubicLinearCLM_apply_coe (R : ℝ) (x : discAlgebra 0 R × (ℂ × ℂ))
    (z : closedBall (0 : ℂ) R) :
    (cubicLinearCLM R x : C(closedBall (0 : ℂ) R, ℂ)) z =
      z.val ^ 2 * (x.1 : C(closedBall (0 : ℂ) R, ℂ)) z - x.2.1 * z.val + x.2.2 := by
  simp [cubicLinearCLM]

private theorem ker_cubicLinearCLM {R : ℝ} (hR : 0 < R) :
    LinearMap.ker (cubicLinearCLM R : (discAlgebra 0 R × (ℂ × ℂ)) →ₗ[ℂ] discAlgebra 0 R) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  rintro ⟨δu, δζ, δη⟩ hx
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have h0cb : (0 : ℂ) ∈ closedBall (0 : ℂ) R := ball_subset_closedBall h0
  let q₁ : discAlgebra 0 R :=
    DiscAlgebra.coord 0 R * δu - algebraMap ℂ (discAlgebra 0 R) δζ
  have h_eq1 : (DiscAlgebra.coord 0 R - algebraMap ℂ (discAlgebra 0 R) 0) * q₁ +
      algebraMap ℂ (discAlgebra 0 R) δη = 0 := by
    rw [← hx]
    apply Subtype.ext
    ext z
    simp only [q₁, map_zero, sub_zero, ContinuousLinearMap.coe_coe, cubicLinearCLM_apply_coe,
      Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_sub, Algebra.algebraMap_eq_smul_one,
      Subalgebra.coe_smul, Subalgebra.coe_one, ContinuousMap.add_apply, ContinuousMap.mul_apply,
      ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul,
      mul_one, DiscAlgebra.coord_apply]
    ring
  have hq₁ : q₁ = 0 := by
    simpa using DiscAlgebra.eq_dslope_of_coord_sub_algebraMap_mul_add h0 h_eq1
  have eval0 {x : ℂ} (h : algebraMap ℂ (discAlgebra 0 R) x = 0) : x = 0 := by
    simpa [Algebra.algebraMap_eq_smul_one] using
      congrArg (fun f : discAlgebra 0 R => (f : C(closedBall (0 : ℂ) R, ℂ)) ⟨0, h0cb⟩) h
  have hη : δη = 0 := eval0 (by simpa [hq₁] using h_eq1)
  have h_eq2 : (DiscAlgebra.coord 0 R - algebraMap ℂ (discAlgebra 0 R) 0) * δu +
      algebraMap ℂ (discAlgebra 0 R) (-δζ) = 0 := by
    simpa [q₁, map_zero, sub_zero, map_neg, sub_eq_add_neg] using hq₁
  have hδu : δu = 0 := by
    simpa using DiscAlgebra.eq_dslope_of_coord_sub_algebraMap_mul_add h0 h_eq2
  have hζ : δζ = 0 := eval0 (neg_eq_zero.1 (by simpa [hδu] using h_eq2))
  simp [hδu, hζ, hη]

private noncomputable def cubicLinearEquiv {R : ℝ} (hR : 0 < R) :
    (discAlgebra 0 R × (ℂ × ℂ)) ≃L[ℂ] discAlgebra 0 R :=
  ContinuousLinearEquiv.ofBijective (cubicLinearCLM R) (ker_cubicLinearCLM hR) <| by
    rw [LinearMap.range_eq_top]
    intro u
    have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
    let u₁ : discAlgebra 0 R := DiscAlgebra.dslope h0 u
    let u₂ : discAlgebra 0 R := DiscAlgebra.dslope h0 u₁
    refine ⟨(u₂, (-deriv (DiscAlgebra.extend u) 0, DiscAlgebra.extend u 0)), ?_⟩
    have h1 : DiscAlgebra.coord 0 R * u₁ + algebraMap ℂ (discAlgebra 0 R) (DiscAlgebra.extend u 0) =
        u := by
      simpa using DiscAlgebra.coord_sub_algebraMap_mul_dslope_add h0 u
    have h2 : DiscAlgebra.coord 0 R * u₂ +
        algebraMap ℂ (discAlgebra 0 R) (deriv (DiscAlgebra.extend u) 0) = u₁ := by
      have h := DiscAlgebra.coord_sub_algebraMap_mul_dslope_add h0 u₁
      rw [DiscAlgebra.extend_apply u₁ ⟨0, ball_subset_closedBall h0⟩, DiscAlgebra.dslope_apply,
        dslope_same] at h
      simpa [u₁] using h
    apply Subtype.ext
    ext z
    have h1z := congrArg (fun f : discAlgebra 0 R => (f : C(closedBall (0 : ℂ) R, ℂ)) z) h1
    have h2z := congrArg (fun f : discAlgebra 0 R => (f : C(closedBall (0 : ℂ) R, ℂ)) z) h2
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Algebra.algebraMap_eq_smul_one,
      Subalgebra.coe_smul, Subalgebra.coe_one, ContinuousMap.add_apply, ContinuousMap.mul_apply,
      ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one,
      DiscAlgebra.coord_apply] at h1z h2z
    rw [ContinuousLinearMap.coe_coe, cubicLinearCLM_apply_coe]
    linear_combination h1z + z.val * h2z

/-- The nonlinear cubic normal-form operator `(u, (ζ, η)) ↦ u ^ 3 / 3 - ζ u + η` on
`discAlgebra 0 R`. -/
private noncomputable def cubicMap (R : ℝ) (x : discAlgebra 0 R × (ℂ × ℂ)) : discAlgebra 0 R :=
  (3⁻¹ : ℂ) • x.1 ^ 3 - x.2.1 • x.1 + algebraMapCLM ℂ (discAlgebra 0 R) x.2.2

private theorem cubicMap_apply_coe (R : ℝ) (x : discAlgebra 0 R × (ℂ × ℂ))
    (z : closedBall (0 : ℂ) R) :
    (cubicMap R x : C(closedBall (0 : ℂ) R, ℂ)) z =
      ((x.1 : C(closedBall (0 : ℂ) R, ℂ)) z) ^ 3 / 3 -
        x.2.1 * (x.1 : C(closedBall (0 : ℂ) R, ℂ)) z + x.2.2 := by
  simp [cubicMap, div_eq_inv_mul]

private theorem analyticAt_cubicMap (R : ℝ) (x : discAlgebra 0 R × (ℂ × ℂ)) :
    AnalyticAt ℂ (cubicMap R) x := by
  have hu : AnalyticAt ℂ (fun y : discAlgebra 0 R × (ℂ × ℂ) => y.1) x :=
    (ContinuousLinearMap.fst ℂ (discAlgebra 0 R) (ℂ × ℂ)).analyticAt x
  have hζ : AnalyticAt ℂ (fun y : discAlgebra 0 R × (ℂ × ℂ) => y.2.1) x :=
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (.snd ℂ (discAlgebra 0 R) (ℂ × ℂ))).analyticAt x
  have hη : AnalyticAt ℂ (fun y : discAlgebra 0 R × (ℂ × ℂ) =>
      algebraMapCLM ℂ (discAlgebra 0 R) y.2.2) x :=
    ((algebraMapCLM ℂ (discAlgebra 0 R)).comp
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (.snd ℂ (discAlgebra 0 R) (ℂ × ℂ)))).analyticAt x
  refine ((((hu.mul (hu.mul hu)).const_smul (c := (3⁻¹ : ℂ))).sub (hζ.smul hu)).add hη).congr ?_
  exact .of_forall fun y => by simp [cubicMap, pow_three]

private theorem hasFDerivAt_cubicMap (R : ℝ) :
    HasFDerivAt (cubicMap R) (cubicLinearCLM R) (DiscAlgebra.coord 0 R, (0, 0)) := by
  set x₀ : discAlgebra 0 R × (ℂ × ℂ) := (DiscAlgebra.coord 0 R, (0, 0))
  have hu : HasFDerivAt (fun x : discAlgebra 0 R × (ℂ × ℂ) => x.1)
      (.fst ℂ (discAlgebra 0 R) (ℂ × ℂ)) x₀ :=
    (ContinuousLinearMap.fst ℂ (discAlgebra 0 R) (ℂ × ℂ)).hasFDerivAt
  have hu3 := (hu.mul (hu.mul hu)).const_smul (3⁻¹ : ℂ)
  have hζ : HasFDerivAt (fun x : discAlgebra 0 R × (ℂ × ℂ) => x.2.1)
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (.snd ℂ (discAlgebra 0 R) (ℂ × ℂ))) x₀ :=
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (.snd ℂ (discAlgebra 0 R) (ℂ × ℂ))).hasFDerivAt
  have hη : HasFDerivAt (fun x : discAlgebra 0 R × (ℂ × ℂ) =>
      algebraMapCLM ℂ (discAlgebra 0 R) x.2.2)
      ((algebraMapCLM ℂ (discAlgebra 0 R)).comp
        ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (.snd ℂ (discAlgebra 0 R) (ℂ × ℂ)))) x₀ :=
    ((algebraMapCLM ℂ (discAlgebra 0 R)).comp
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (.snd ℂ (discAlgebra 0 R) (ℂ × ℂ)))).hasFDerivAt
  have hcomb := (hu3.sub (hζ.smul hu)).add hη
  refine (hcomb.congr_of_eventuallyEq
    (.of_forall fun x => by simp [cubicMap, pow_three])).congr_fderiv ?_
  apply ContinuousLinearMap.ext
  rintro ⟨δu, δζ, δη⟩
  apply Subtype.ext
  ext z
  simp [cubicLinearCLM_apply_coe, x₀]
  ring

/-- Choose radii `δ, R > 0` so that `F` is jointly analytic on `ball 0 δ ×ˢ closedBall 0 R` and
`F(0, s) = s ^ 3 / 3` on `closedBall 0 R`. -/
private theorem exists_analyticAt_ball_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {F : E × ℂ → ℂ} (hF : AnalyticAt ℂ F (0, 0))
    (hF0 : ∀ᶠ s in 𝓝 (0 : ℂ), F (0, s) = s ^ 3 / 3) :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧
      (∀ β ∈ ball (0 : E) δ, ∀ s ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ F (β, s)) ∧
      ∀ s ∈ closedBall (0 : ℂ) R, F (0, s) = s ^ 3 / 3 := by
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.1 ((isOpen_analyticAt ℂ F).mem_nhds hF)
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.mem_nhds_iff.1 hF0
  set R : ℝ := min r₁ r₂ / 2
  have hR : 0 < R := half_pos (lt_min hr₁ hr₂)
  have hF0_an {s : ℂ} (hs : s ∈ closedBall (0 : ℂ) R) : AnalyticAt ℂ F (0, s) :=
    hball₁ (by simp [Prod.dist_eq, (mem_closedBall_zero_iff.1 hs).trans_lt
      ((half_lt_self (lt_min hr₁ hr₂)).trans_le (min_le_left _ _))])
  have hev_an : ∀ᶠ β in 𝓝 (0 : E), ∀ s ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ F (β, s) :=
    (isCompact_closedBall (0 : ℂ) R).eventually_forall_of_forall_eventually fun _ hs =>
      (hF0_an hs).eventually_analyticAt
  obtain ⟨δ, hδ, hFδ⟩ := Metric.mem_nhds_iff.1 hev_an
  refine ⟨δ, R, hδ, hR, hFδ, fun s hs => hball₂ ?_⟩
  exact mem_ball.2 ((mem_closedBall.1 hs).trans_lt
    ((half_lt_self (lt_min hr₁ hr₂)).trans_le (min_le_right _ _)))

/-- Normalized cubic normal-form existence when `F(0, s) = s ^ 3 / 3` near `s = 0`. -/
private theorem exists_cubic_normal_form_of_normalized {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {F : E × ℂ → ℂ} (hF : AnalyticAt ℂ F (0, 0))
    (hF0 : ∀ᶠ s in 𝓝 (0 : ℂ), F (0, s) = s ^ 3 / 3) :
    ∃ ζ₀ η₀ : E → ℂ, ∃ W : E × ℂ → ℂ,
      AnalyticAt ℂ ζ₀ 0 ∧ AnalyticAt ℂ η₀ 0 ∧ AnalyticAt ℂ W (0, 0) ∧
      ζ₀ 0 = 0 ∧ η₀ 0 = 0 ∧ W (0, 0) = 0 ∧ deriv (fun s => W (0, s)) 0 = 1 ∧
      ∀ᶠ q in 𝓝 ((0 : E), (0 : ℂ)), F q = W q ^ 3 / 3 - ζ₀ q.1 * W q + η₀ q.1 := by
  obtain ⟨δ, R, hδ, hR, hFδ, hF0_cb⟩ := exists_analyticAt_ball_closedBall hF hF0
  set x₀ : discAlgebra 0 R × (ℂ × ℂ) := (DiscAlgebra.coord 0 R, (0, 0))
  have hfderiv : fderiv ℂ (cubicMap R) x₀ = ↑(cubicLinearEquiv hR) := by
    rw [(hasFDerivAt_cubicMap R).fderiv, cubicLinearEquiv, ContinuousLinearEquiv.coe_ofBijective]
  obtain ⟨Θ, hΘ, hx₀_src, -, -, hΘsymm⟩ :=
    (analyticAt_cubicMap R x₀).exists_openPartialHomeomorph hfderiv univ_mem
  let slice : E → discAlgebra 0 R := fun β => DiscAlgebra.mkD 0 R (fun s => F (β, s)) 0
  have hslice_apply {β : E} (hβ : β ∈ ball (0 : E) δ) (s : closedBall (0 : ℂ) R) :
      (slice β : C(closedBall (0 : ℂ) R, ℂ)) s = F (β, s.val) :=
    DiscAlgebra.mkD_apply_of_analyticOnNhd
      (fun z hz => (hFδ β hβ z hz).curry_right) s
  have hslice_eq : slice 0 = cubicMap R x₀ := by
    apply Subtype.ext
    ext s
    rw [hslice_apply (mem_ball_self hδ)]
    simpa [cubicMap_apply_coe, x₀] using hF0_cb s.val s.property
  have hslice_an : AnalyticAt ℂ slice 0 :=
    DiscAlgebra.analyticAt_mkD_of_analyticAt (hFδ 0 (mem_ball_self hδ))
  have hmem_tgt : slice 0 ∈ Θ.target := by rw [hslice_eq, ← hΘ]; exact Θ.map_source hx₀_src
  set Φ : E → discAlgebra 0 R × (ℂ × ℂ) := Θ.symm ∘ slice
  have hΦ_an : AnalyticAt ℂ Φ 0 := (hΘsymm _ hmem_tgt).comp hslice_an
  have hΦ0 : Φ 0 = x₀ := by
    simp only [Φ, Function.comp_apply, hslice_eq, ← hΘ]
    exact Θ.left_inv hx₀_src
  set W : E × ℂ → ℂ := fun q => DiscAlgebra.extend (Φ q.1).1 q.2
  have hW_an : AnalyticAt ℂ W (0, 0) :=
    DiscAlgebra.analyticAt_extend_of_analyticAt (mem_ball_self hR)
      (((ContinuousLinearMap.fst ℂ (discAlgebra 0 R) (ℂ × ℂ)).analyticAt _).comp hΦ_an)
  have hW0_slice : ∀ s ∈ closedBall (0 : ℂ) R, W (0, s) = s := fun s hs => by
    simp [W, hΦ0, x₀, DiscAlgebra.extend_apply _ ⟨s, hs⟩]
  have hW_deriv : deriv (fun s => W (0, s)) 0 = 1 := by
    have heq : (fun s => W (0, s)) =ᶠ[𝓝 0] id := by
      filter_upwards [closedBall_mem_nhds (0 : ℂ) hR] with s hs using hW0_slice s hs
    rw [heq.deriv_eq, deriv_id]
  refine ⟨fun β => (Φ β).2.1, fun β => (Φ β).2.2, W,
    (((ContinuousLinearMap.fst ℂ ℂ ℂ).comp
      (.snd ℂ (discAlgebra 0 R) (ℂ × ℂ))).analyticAt _).comp hΦ_an,
    (((ContinuousLinearMap.snd ℂ ℂ ℂ).comp
      (.snd ℂ (discAlgebra 0 R) (ℂ × ℂ))).analyticAt _).comp hΦ_an,
    hW_an, by simp [hΦ0, x₀], by simp [hΦ0, x₀], hW0_slice 0 (mem_closedBall_self hR.le),
    hW_deriv, ?_⟩
  have hev_tgt : ∀ᶠ β in 𝓝 (0 : E), slice β ∈ Θ.target :=
    hslice_an.continuousAt.eventually (Θ.open_target.mem_nhds hmem_tgt)
  filter_upwards [prod_mem_nhds (hev_tgt.and (ball_mem_nhds 0 hδ)) (ball_mem_nhds 0 hR)]
    with ⟨β, s⟩ ⟨⟨hβ_tgt, hβ_δ⟩, hs_R⟩
  have hs_cb : s ∈ closedBall (0 : ℂ) R := ball_subset_closedBall hs_R
  have hright : cubicMap R (Φ β) = slice β := by simpa [Φ, hΘ] using Θ.right_inv hβ_tgt
  have hval := congrArg (fun f : discAlgebra 0 R => (f : C(closedBall (0 : ℂ) R, ℂ)) ⟨s, hs_cb⟩)
    hright
  rw [cubicMap_apply_coe, hslice_apply hβ_δ] at hval
  simpa [W, DiscAlgebra.extend_apply _ ⟨s, hs_cb⟩] using hval.symm

end DiscAlgebraOperator

/-! ### The holomorphic cubic normal form -/

/-- Vanishing of the first two derivatives and nonvanishing of the third gives analytic order `3`
after subtracting the base value and multiplying by `3`. -/
private theorem analyticOrderAt_three_mul_sub_eq_three {g : ℂ → ℂ} {t₀ : ℂ}
    (hg : AnalyticAt ℂ g t₀) (h₁ : deriv g t₀ = 0) (h₂ : deriv (deriv g) t₀ = 0)
    (h₃ : deriv (deriv (deriv g)) t₀ ≠ 0) :
    analyticOrderAt (fun z => 3 * (g z - g t₀)) t₀ = 3 := by
  have hsub : AnalyticAt ℂ (fun z => g z - g t₀) t₀ := hg.sub analyticAt_const
  have ho₀ : analyticOrderAt (fun z => g z - g t₀) t₀ = 3 := by
    refine (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hsub).2 ⟨?_, ?_⟩
    · intro k hk
      interval_cases k
      · simp
      · simp [iteratedDeriv_one, h₁]
      · rw [iteratedDeriv_succ', iteratedDeriv_one]
        simp [deriv_sub_const_fun, h₂]
    · rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_one]
      simpa [deriv_sub_const_fun] using h₃
  classical
  simpa [ho₀] using analyticOrderAt_fun_const_mul hsub (3 : ℂ)

/-- Local coordinate `e` in `t` at `t₀` normalizing the slice `p(α₀, t) - p(α₀, t₀)` to
`s ^ 3 / 3`. -/
private theorem exists_slice_cubic_coord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : E × ℂ → ℂ} {α₀ : E} {t₀ : ℂ} (hp : AnalyticAt ℂ p (α₀, t₀))
    (h₁ : deriv (fun t => p (α₀, t)) t₀ = 0)
    (h₂ : deriv (deriv fun t => p (α₀, t)) t₀ = 0)
    (h₃ : deriv (deriv (deriv fun t => p (α₀, t))) t₀ ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, t₀ ∈ e.source ∧ e t₀ = 0 ∧
      AnalyticAt ℂ e t₀ ∧ AnalyticAt ℂ e.symm 0 ∧ deriv e t₀ ≠ 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℂ), p (α₀, e.symm s) - p (α₀, t₀) = s ^ 3 / 3 := by
  have hp₀ : AnalyticAt ℂ (fun t => p (α₀, t)) t₀ := hp.curry_right
  have hord : analyticOrderAt (fun z => (3 * (p (α₀, z) - p (α₀, t₀))) -
      (3 * (p (α₀, t₀) - p (α₀, t₀)))) t₀ = 3 := by
    simpa using analyticOrderAt_three_mul_sub_eq_three hp₀ h₁ h₂ h₃
  obtain ⟨e, ht₀_src, he_t₀, -, he_an, he_symm_an, he_pow⟩ :=
    ((analyticAt_const (v := (3 : ℂ))).mul
      (hp₀.sub analyticAt_const)).exists_openPartialHomeomorph_sub_eq_pow
      (by norm_num : 0 < 3) hord univ_mem
  have h0_tgt : (0 : ℂ) ∈ e.target := he_t₀ ▸ e.map_source ht₀_src
  have he_deriv_ne : deriv e t₀ ≠ 0 := by
    have hinv := e.isInvertible_fderiv ht₀_src (he_an t₀ ht₀_src).differentiableAt
      (he_t₀ ▸ (he_symm_an 0 h0_tgt).differentiableAt)
    rw [← fderiv_apply_one_eq_deriv]
    exact fun h => one_ne_zero (hinv.injective (h.trans (map_zero _).symm))
  refine ⟨e, ht₀_src, he_t₀, he_an t₀ ht₀_src, he_symm_an 0 h0_tgt, he_deriv_ne, ?_⟩
  filter_upwards [e.open_target.mem_nhds h0_tgt] with s hs
  have h := he_pow (e.symm s) (e.map_target hs)
  rw [e.right_inv hs] at h
  simp only [Pi.mul_apply, Pi.sub_apply] at h
  linear_combination (3⁻¹ : ℂ) * h

end TauCeti

namespace AnalyticAt

open TauCeti

/-- **The analytic Chester-Friedman-Ursell cubic normal form.** If `p : E × ℂ → ℂ` (with `E` a
finite-dimensional complex normed space) is analytic at `(α₀, t₀)` with `∂p/∂t (α₀, t₀) = 0`,
`∂²p/∂t² (α₀, t₀) = 0`, and `∂³p/∂t³ (α₀, t₀) ≠ 0`, then there exist functions `ζ` and `η`
analytic at `α₀` and `w` analytic at `(α₀, t₀)` with `ζ(α₀) = 0`, `η(α₀) = p(α₀, t₀)`,
`w(α₀, t₀) = 0`, `∂w/∂t (α₀, t₀) ≠ 0`, and `p(α, t) = w(α, t) ^ 3 / 3 - ζ(α) * w(α, t) + η(α)`
near `(α₀, t₀)`. -/
theorem exists_cubic_normal_form {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {p : E × ℂ → ℂ} {α₀ : E} {t₀ : ℂ} (hp : AnalyticAt ℂ p (α₀, t₀))
    (h₁ : deriv (fun t => p (α₀, t)) t₀ = 0)
    (h₂ : deriv (deriv fun t => p (α₀, t)) t₀ = 0)
    (h₃ : deriv (deriv (deriv fun t => p (α₀, t))) t₀ ≠ 0) :
    ∃ ζ η : E → ℂ, ∃ w : E × ℂ → ℂ,
      AnalyticAt ℂ ζ α₀ ∧ AnalyticAt ℂ η α₀ ∧ AnalyticAt ℂ w (α₀, t₀) ∧
      ζ α₀ = 0 ∧ η α₀ = p (α₀, t₀) ∧ w (α₀, t₀) = 0 ∧
      deriv (fun t => w (α₀, t)) t₀ ≠ 0 ∧
      ∀ᶠ q in 𝓝 (α₀, t₀), p q = w q ^ 3 / 3 - ζ q.1 * w q + η q.1 := by
  obtain ⟨e, ht₀_src, he_t₀, he_an, he_symm_an, he_deriv_ne, he_pow⟩ :=
    exists_slice_cubic_coord hp h₁ h₂ h₃
  have he_symm0 : e.symm 0 = t₀ := he_t₀ ▸ e.left_inv ht₀_src
  set F : E × ℂ → ℂ := fun q => p (α₀ + q.1, e.symm q.2) - p (α₀, t₀)
  have hF : AnalyticAt ℂ F (0, 0) :=
    (hp.comp_of_eq (((analyticAt_const (v := α₀)).add analyticAt_fst).prod
      (he_symm_an.comp_of_eq analyticAt_snd rfl)) (by simp [he_symm0])).sub analyticAt_const
  have hF0 : ∀ᶠ s in 𝓝 (0 : ℂ), F (0, s) = s ^ 3 / 3 := by simpa [F] using he_pow
  obtain ⟨ζ₀, η₀, W, hζ₀, hη₀, hW, hζ₀0, hη₀0, hW0, hW_deriv, hFeq⟩ :=
    exists_cubic_normal_form_of_normalized hF hF0
  set w : E × ℂ → ℂ := fun q => W (q.1 - α₀, e q.2)
  have hw_an : AnalyticAt ℂ w (α₀, t₀) :=
    hW.comp_of_eq ((analyticAt_fst.sub analyticAt_const).prod
      (he_an.comp_of_eq analyticAt_snd rfl)) (by simp [he_t₀])
  have hw_deriv : deriv (fun t => w (α₀, t)) t₀ ≠ 0 := by
    set gW : ℂ → ℂ := fun s => W (0, s)
    have hgW : DifferentiableAt ℂ gW (e t₀) :=
      he_t₀ ▸ hW.curry_right.differentiableAt
    have hd := (hgW.hasDerivAt.comp t₀ he_an.differentiableAt.hasDerivAt).deriv
    simp only [Function.comp_def, gW] at hd
    have heq : (fun t => w (α₀, t)) = fun t => W (0, e t) := by ext t; simp [w]
    rw [heq, hd, he_t₀, hW_deriv, one_mul]
    exact he_deriv_ne
  refine ⟨fun α => ζ₀ (α - α₀), fun α => η₀ (α - α₀) + p (α₀, t₀), w,
    hζ₀.comp_of_eq (analyticAt_id.sub analyticAt_const) (sub_self α₀),
    (hη₀.comp_of_eq (analyticAt_id.sub analyticAt_const) (sub_self α₀)).add analyticAt_const,
    hw_an, by simp [hζ₀0], by simp [hη₀0], by simp [w, he_t₀, hW0], hw_deriv, ?_⟩
  have hmap : ContinuousAt (fun q : E × ℂ => (q.1 - α₀, e q.2)) (α₀, t₀) :=
    (continuousAt_fst.sub continuousAt_const).prodMk
      (he_an.continuousAt.comp continuousAt_snd)
  have hnhds : ∀ᶠ q in 𝓝 (α₀, t₀),
      (q.1 - α₀, e q.2) ∈ {r | F r = W r ^ 3 / 3 - ζ₀ r.1 * W r + η₀ r.1} := by
    refine hmap.eventually ?_
    simpa [he_t₀] using hFeq
  filter_upwards [hnhds, prod_mem_nhds univ_mem (e.open_source.mem_nhds ht₀_src)]
    with ⟨α, t⟩ hq ⟨_, ht_src⟩
  dsimp [F] at hq
  rw [add_sub_cancel, e.left_inv ht_src] at hq
  dsimp [w]
  linear_combination hq

end AnalyticAt

namespace TauCeti

/-- **The Chester-Friedman-Ursell holomorphic cubic normal form** (DLMF 2.4.18). Let `p : E × ℂ → ℂ`
(with `E` a finite-dimensional complex normed space) be complex differentiable on a neighbourhood
`U` of `(α₀, t₀)` with `∂p/∂t (α₀, t₀) = 0`, `∂²p/∂t² (α₀, t₀) = 0`, and `∂³p/∂t³ (α₀, t₀) ≠ 0`.
Then there exist `ζ` and `η` complex differentiable near `α₀` and `w` complex differentiable near
`(α₀, t₀)` with `ζ(α₀) = 0`, `η(α₀) = p(α₀, t₀)`, `w(α₀, t₀) = 0`, `∂w/∂t (α₀, t₀) ≠ 0`, and
`p(α, t) = w(α, t) ^ 3 / 3 - ζ(α) * w(α, t) + η(α)` near `(α₀, t₀)`. -/
theorem exists_cubic_normal_form {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {p : E × ℂ → ℂ} {U : Set (E × ℂ)} {α₀ : E} {t₀ : ℂ}
    (hU : U ∈ 𝓝 (α₀, t₀)) (hp : DifferentiableOn ℂ p U)
    (h₁ : deriv (fun t => p (α₀, t)) t₀ = 0)
    (h₂ : deriv (deriv fun t => p (α₀, t)) t₀ = 0)
    (h₃ : deriv (deriv (deriv fun t => p (α₀, t))) t₀ ≠ 0) :
    ∃ ζ η : E → ℂ, ∃ w : E × ℂ → ℂ,
      ζ α₀ = 0 ∧ η α₀ = p (α₀, t₀) ∧ w (α₀, t₀) = 0 ∧
      (∀ᶠ α in 𝓝 α₀, DifferentiableAt ℂ ζ α ∧ DifferentiableAt ℂ η α) ∧
      deriv (fun t => w (α₀, t)) t₀ ≠ 0 ∧
      ∀ᶠ q in 𝓝 (α₀, t₀),
        DifferentiableAt ℂ w q ∧ p q = w q ^ 3 / 3 - ζ q.1 * w q + η q.1 := by
  obtain ⟨ζ, η, w, hζ, hη, hw, hζ0, hη0, hw0, hdw, hpq⟩ :=
    (hp.analyticAt_of_finiteDimensional hU).exists_cubic_normal_form h₁ h₂ h₃
  refine ⟨ζ, η, w, hζ0, hη0, hw0, ?_, hdw, ?_⟩
  · filter_upwards [hζ.eventually_analyticAt, hη.eventually_analyticAt] with α hζα hηα
    exact ⟨hζα.differentiableAt, hηα.differentiableAt⟩
  · filter_upwards [hw.eventually_analyticAt, hpq] with q hwq heq
    exact ⟨hwq.differentiableAt, heq⟩

/-- Algebraic translation identity relating the depressed cubic `w ^ 3 / 3 - ζ * w + η` (with
`w = u + a`) and DLMF's general cubic `u ^ 3 / 3 + a * u ^ 2 + b * u + c` (DLMF 2.4.18), over any
field of characteristic `≠ 3`. -/
theorem add_pow_three_div_three_sub_mul_add {K : Type*} [Field K] [NeZero (3 : K)]
    (u a b c : K) :
    (u + a) ^ 3 / 3 - (a ^ 2 - b) * (u + a) + (c - a * b + 2 * a ^ 3 / 3) =
      u ^ 3 / 3 + a * u ^ 2 + b * u + c := by
  have h3 : (3 : K) ≠ 0 := NeZero.ne 3
  field_simp [h3]
  ring

/-- **Translated cubic normal form** (DLMF 2.4.18). Given any holomorphic shift `a : E → ℂ` near
`α₀` (with `E` finite-dimensional over `ℂ`), translating `w` by `-a(α)` writes `p(α, t)` in the
form `u(α, t) ^ 3 / 3 + a(α) * u(α, t) ^ 2 + b(α) * u(α, t) + c(α)`. -/
theorem exists_translated_cubic_normal_form {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {p : E × ℂ → ℂ} {U : Set (E × ℂ)} {a : E → ℂ}
    {α₀ : E} {t₀ : ℂ} (hU : U ∈ 𝓝 (α₀, t₀)) (hp : DifferentiableOn ℂ p U)
    (h₁ : deriv (fun t => p (α₀, t)) t₀ = 0)
    (h₂ : deriv (deriv fun t => p (α₀, t)) t₀ = 0)
    (h₃ : deriv (deriv (deriv fun t => p (α₀, t))) t₀ ≠ 0)
    (ha : ∀ᶠ α in 𝓝 α₀, DifferentiableAt ℂ a α) :
    ∃ b c : E → ℂ, ∃ u : E × ℂ → ℂ,
      b α₀ = a α₀ ^ 2 ∧ c α₀ = p (α₀, t₀) + a α₀ ^ 3 / 3 ∧ u (α₀, t₀) = -a α₀ ∧
      (∀ᶠ α in 𝓝 α₀, DifferentiableAt ℂ b α ∧ DifferentiableAt ℂ c α) ∧
      deriv (fun t => u (α₀, t)) t₀ ≠ 0 ∧
      ∀ᶠ q in 𝓝 (α₀, t₀),
        DifferentiableAt ℂ u q ∧
          p q = u q ^ 3 / 3 + a q.1 * u q ^ 2 + b q.1 * u q + c q.1 := by
  obtain ⟨ζ, η, w, hζ0, hη0, hw0, hζη, hdw, hw⟩ := exists_cubic_normal_form hU hp h₁ h₂ h₃
  refine ⟨fun α => a α ^ 2 - ζ α, fun α => η α - a α * ζ α + a α ^ 3 / 3,
    fun q => w q - a q.1, by simp [hζ0], by simp [hζ0, hη0], by simp [hw0], ?_,
    by simpa [deriv_sub_const] using hdw, ?_⟩
  · filter_upwards [ha, hζη] with α haα ⟨hζα, hηα⟩
    exact ⟨(haα.fun_pow 2).fun_sub hζα, by
      simpa only [div_eq_mul_inv] using
        (hηα.fun_sub (haα.fun_mul hζα)).fun_add ((haα.fun_pow 3).mul_const (3 : ℂ)⁻¹)⟩
  · filter_upwards [hw, continuousAt_fst.eventually ha] with q ⟨hwq, hpq⟩ haq
    refine ⟨hwq.sub (haq.comp q differentiableAt_fst), ?_⟩
    rw [hpq, ← add_pow_three_div_three_sub_mul_add (w q - a q.1) (a q.1)
      (a q.1 ^ 2 - ζ q.1) (η q.1 - a q.1 * ζ q.1 + a q.1 ^ 3 / 3)]
    simp only [sub_add_cancel, sub_sub_cancel]
    congr 1
    ring

/-! ### Critical points, jet identities, and nondegeneracy -/

namespace CubicNormalForm

/-- Differentiating `g(s) = u(s) ^ 3 / 3 - ζ * u(s) + c` at `t` gives
`HasDerivAt g ((u(t) ^ 2 - ζ) * u') t` whenever `HasDerivAt u u' t`, over any nontrivially normed
field of characteristic `≠ 3`. -/
theorem hasDerivAt_sq_sub_mul {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NeZero (3 : 𝕜)]
    {g u : 𝕜 → 𝕜} {t u' ζ c : 𝕜} (hu : HasDerivAt u u' t)
    (hgu : ∀ᶠ s in 𝓝 t, g s = u s ^ 3 / 3 - ζ * u s + c) :
    HasDerivAt g ((u t ^ 2 - ζ) * u') t := by
  have h3 : (3 : 𝕜) ≠ 0 := NeZero.ne 3
  have hd : HasDerivAt (fun s => u s ^ 3 / 3 - ζ * u s + c)
      (((3 : ℕ) * u t ^ (3 - 1) * u') / 3 - ζ * u') t :=
    (((hu.pow 3).div_const 3).sub (hu.const_mul ζ)).add_const c
  have hval : ((3 : ℕ) * u t ^ (3 - 1) * u') / 3 - ζ * u' = (u t ^ 2 - ζ) * u' := by
    norm_num
    field_simp [h3]
  exact (hval ▸ hd).congr_of_eventuallyEq hgu

/-- Differentiating `g(s) = u(s) ^ 3 / 3 - ζ * u(s) + c` at `t` factors `g'(t)` as
`(u(t) ^ 2 - ζ) * u'(t)`, over any nontrivially normed field of characteristic `≠ 3`. -/
theorem deriv_eq_sq_sub_mul_deriv {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NeZero (3 : 𝕜)]
    {g u : 𝕜 → 𝕜} {t ζ c : 𝕜} (hu : DifferentiableAt 𝕜 u t)
    (hgu : ∀ᶠ s in 𝓝 t, g s = u s ^ 3 / 3 - ζ * u s + c) :
    deriv g t = (u t ^ 2 - ζ) * deriv u t :=
  (hasDerivAt_sq_sub_mul hu.hasDerivAt hgu).deriv

/-- At any point where `u'(t) ≠ 0` and `g(s) = u(s) ^ 3 / 3 - ζ * u(s) + c` near `t`, the
critical-point equation `g'(t) = 0` is equivalent to `u(t) ^ 2 = ζ`. -/
theorem deriv_eq_zero_iff_sq_eq {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NeZero (3 : 𝕜)]
    {g u : 𝕜 → 𝕜} {t ζ c : 𝕜} (hdu : deriv u t ≠ 0)
    (hgu : ∀ᶠ s in 𝓝 t, g s = u s ^ 3 / 3 - ζ * u s + c) :
    deriv g t = 0 ↔ u t ^ 2 = ζ := by
  rw [deriv_eq_sq_sub_mul_deriv (differentiableAt_of_deriv_ne_zero hdu) hgu, mul_eq_zero,
    or_iff_left hdu, sub_eq_zero]

/-- Near `(α₀, t₀)`, if `(α, t) ↦ ∂w/∂t (α, t)` is continuous and nonzero at `(α₀, t₀)`, then
critical points `∂p/∂t (α, t) = 0` of a cubic normal form `p = w ^ 3 / 3 - ζ * w + η` correspond
to the square roots `w(α, t) ^ 2 = ζ(α)`. -/
theorem eventually_deriv_eq_zero_iff_sq_eq {X 𝕜 : Type*} [TopologicalSpace X]
    [NontriviallyNormedField 𝕜] [NeZero (3 : 𝕜)] {p w : X × 𝕜 → 𝕜} {ζ η : X → 𝕜}
    {α₀ : X} {t₀ : 𝕜}
    (hw : ContinuousAt (fun q : X × 𝕜 => deriv (fun t => w (q.1, t)) q.2) (α₀, t₀))
    (hdw : deriv (fun t => w (α₀, t)) t₀ ≠ 0)
    (hpw : ∀ᶠ q in 𝓝 (α₀, t₀), p q = w q ^ 3 / 3 - ζ q.1 * w q + η q.1) :
    ∀ᶠ q in 𝓝 (α₀, t₀), deriv (fun t => p (q.1, t)) q.2 = 0 ↔ w q ^ 2 = ζ q.1 := by
  filter_upwards [hw.eventually_ne hdw, hpw.eventually_nhds] with q hq_ne hq_eq
  exact deriv_eq_zero_iff_sq_eq hq_ne
    (by simpa using (Continuous.prodMk_right q.1).continuousAt.eventually hq_eq)

/-- **Local bijection between critical points and square roots.** Near `(α₀, t₀)` where `w` is
analytic with `∂w/∂t (α₀, t₀) ≠ 0` and `p(α, t) = w(α, t) ^ 3 / 3 - ζ(α) * w(α, t) + η(α)`,
there is an analytic local inverse `T` of `w` at `(α₀, w (α₀, t₀))` with `T (α₀, w (α₀, t₀)) = t₀`,
together with neighbourhoods `U ∈ 𝓝 (α₀, t₀)` and `V ∈ 𝓝 (α₀, w (α₀, t₀))` on which
`(α, t) ↦ (α, w (α, t))` and `(α, u) ↦ (α, T (α, u))` are mutually inverse (`Set.InvOn`) and
restrict to a bijection (`Set.BijOn`) between the critical locus `{q ∈ U | ∂p/∂t q = 0}` and the
root locus `{u ∈ V | u.2 ^ 2 = ζ u.1}`. -/
theorem exists_bijOn_deriv_eq_zero_sq_eq {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [NeZero (3 : 𝕜)] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] {p w : E × 𝕜 → 𝕜} {ζ η : E → 𝕜} {α₀ : E} {t₀ : 𝕜}
    (hw : AnalyticAt 𝕜 w (α₀, t₀)) (hdw : deriv (fun t => w (α₀, t)) t₀ ≠ 0)
    (hpw : ∀ᶠ q in 𝓝 (α₀, t₀), p q = w q ^ 3 / 3 - ζ q.1 * w q + η q.1) :
    ∃ T : E × 𝕜 → 𝕜, ∃ U ∈ 𝓝 (α₀, t₀), ∃ V ∈ 𝓝 (α₀, w (α₀, t₀)),
      AnalyticAt 𝕜 T (α₀, w (α₀, t₀)) ∧ T (α₀, w (α₀, t₀)) = t₀ ∧
      Set.MapsTo (fun q : E × 𝕜 => (q.1, w q)) U V ∧
      Set.MapsTo (fun u : E × 𝕜 => (u.1, T u)) V U ∧
      Set.InvOn (fun u : E × 𝕜 => (u.1, T u)) (fun q : E × 𝕜 => (q.1, w q)) U V ∧
      Set.BijOn (fun q : E × 𝕜 => (q.1, w q))
        (U ∩ {q | deriv (fun t => p (q.1, t)) q.2 = 0}) (V ∩ {u | u.2 ^ 2 = ζ u.1}) := by
  obtain ⟨T, hTa, hT0, hT_right, hT_left⟩ := hw.exists_analyticAt_localInverse_snd hdw
  have hcrit : ∀ᶠ q in 𝓝 (α₀, t₀),
      T (q.1, w q) = q.2 ∧ (deriv (fun t => p (q.1, t)) q.2 = 0 ↔ w q ^ 2 = ζ q.1) :=
    hT_left.and (eventually_deriv_eq_zero_iff_sq_eq hw.deriv_snd.continuousAt hdw hpw)
  set S₁ : Set (E × 𝕜) :=
    {q | T (q.1, w q) = q.2 ∧ (deriv (fun t => p (q.1, t)) q.2 = 0 ↔ w q ^ 2 = ζ q.1)}
  have hS₁ : S₁ ∈ 𝓝 (α₀, t₀) := hcrit
  have hmapT : ContinuousAt (fun u : E × 𝕜 => (u.1, T u)) (α₀, w (α₀, t₀)) :=
    continuousAt_fst.prodMk hTa.continuousAt
  set V : Set (E × 𝕜) := {u | w (u.1, T u) = u.2 ∧ (u.1, T u) ∈ S₁}
  have hV : V ∈ 𝓝 (α₀, w (α₀, t₀)) :=
    hT_right.and (hmapT.preimage_mem_nhds (by simpa [hT0] using hS₁))
  have hmapw : ContinuousAt (fun q : E × 𝕜 => (q.1, w q)) (α₀, t₀) :=
    continuousAt_fst.prodMk hw.continuousAt
  set U : Set (E × 𝕜) := S₁ ∩ (fun q : E × 𝕜 => (q.1, w q)) ⁻¹' V
  have hU : U ∈ 𝓝 (α₀, t₀) := inter_mem hS₁ (hmapw.preimage_mem_nhds hV)
  have hU_maps : Set.MapsTo (fun q : E × 𝕜 => (q.1, w q)) U V := fun _ hq => hq.2
  have hV_maps : Set.MapsTo (fun u : E × 𝕜 => (u.1, T u)) V U := fun _ hu =>
    ⟨hu.2, by simpa [hu.1] using hu⟩
  have hinv_UV : Set.InvOn (fun u : E × 𝕜 => (u.1, T u)) (fun q : E × 𝕜 => (q.1, w q)) U V :=
    ⟨fun _ hq => Prod.ext rfl hq.1.1, fun _ hu => Prod.ext rfl hu.1⟩
  have hmaps₁ : Set.MapsTo (fun q : E × 𝕜 => (q.1, w q))
      (U ∩ {q | deriv (fun t => p (q.1, t)) q.2 = 0}) (V ∩ {u | u.2 ^ 2 = ζ u.1}) := by
    rintro q ⟨hqU, hq0⟩
    exact ⟨hU_maps hqU, (hqU.1.2).1 hq0⟩
  have hmaps₂ : Set.MapsTo (fun u : E × 𝕜 => (u.1, T u))
      (V ∩ {u | u.2 ^ 2 = ζ u.1}) (U ∩ {q | deriv (fun t => p (q.1, t)) q.2 = 0}) := by
    rintro u ⟨huV, hu2⟩
    have hTu := hV_maps huV
    have hwu : w (u.1, T u) = u.2 := congrArg Prod.snd (hinv_UV.2 huV)
    refine ⟨hTu, (hTu.1.2).2 ?_⟩
    simpa [hwu] using hu2
  exact ⟨T, U, hU, V, hV, hTa, hT0, hU_maps, hV_maps, hinv_UV,
    (hinv_UV.mono inter_subset_left inter_subset_left).bijOn hmaps₁ hmaps₂⟩

/-- **Centered local bijection onto all square roots.** Under the hypotheses of
`exists_bijOn_deriv_eq_zero_sq_eq`, if in addition `ζ` is continuous at `α₀`, `ζ α₀ = 0`, and
`w (α₀, t₀) = 0`, then there exist neighbourhoods `A ∈ 𝓝 α₀` and `W ∈ 𝓝 t₀` such that for every
`α ∈ A`, `t ↦ w (α, t)` and `u ↦ T (α, u)` are inverse (`Set.InvOn`) and `t ↦ w (α, t)`
restricts to a bijection (`Set.BijOn`) between `{t ∈ W | ∂p/∂t (α, t) = 0}` and the full set
`{u | u ^ 2 = ζ α}` of square roots of `ζ α`. -/
theorem exists_bijOn_deriv_eq_zero_sq_eq_of_eq_zero {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [NeZero (3 : 𝕜)] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] {p w : E × 𝕜 → 𝕜} {ζ η : E → 𝕜} {α₀ : E} {t₀ : 𝕜}
    (hw : AnalyticAt 𝕜 w (α₀, t₀)) (hdw : deriv (fun t => w (α₀, t)) t₀ ≠ 0)
    (hpw : ∀ᶠ q in 𝓝 (α₀, t₀), p q = w q ^ 3 / 3 - ζ q.1 * w q + η q.1)
    (hζc : ContinuousAt ζ α₀) (hζ0 : ζ α₀ = 0) (hw0 : w (α₀, t₀) = 0) :
    ∃ T : E × 𝕜 → 𝕜, ∃ A ∈ 𝓝 α₀, ∃ W ∈ 𝓝 t₀,
      AnalyticAt 𝕜 T (α₀, 0) ∧ T (α₀, 0) = t₀ ∧
      ∀ α ∈ A,
        Set.MapsTo (fun u : 𝕜 => T (α, u)) {u | u ^ 2 = ζ α} W ∧
        Set.InvOn (fun u : 𝕜 => T (α, u)) (fun t : 𝕜 => w (α, t)) W {u | u ^ 2 = ζ α} ∧
        Set.BijOn (fun t : 𝕜 => w (α, t))
          (W ∩ {t | deriv (fun s => p (α, s)) t = 0}) {u | u ^ 2 = ζ α} := by
  obtain ⟨T, U₀, hU₀, V₀, hV₀, hTa, hT0, _, _, hinvOn₀, hbij₁⟩ :=
    exists_bijOn_deriv_eq_zero_sq_eq hw hdw hpw
  have hbij₂ := hbij₁.symm (hinvOn₀.mono inter_subset_left inter_subset_left).symm
  rw [hw0] at hV₀ hTa hT0
  obtain ⟨A₀, hA₀, W, hW, hAW_sub⟩ := mem_nhds_prod_iff.1 hU₀
  have hV₁ : V₀ ∩ (fun u : E × 𝕜 => (u.1, T u)) ⁻¹' (A₀ ×ˢ W) ∈ 𝓝 (α₀, (0 : 𝕜)) :=
    inter_mem hV₀ ((continuousAt_fst.prodMk hTa.continuousAt).preimage_mem_nhds
      (by simpa [hT0] using prod_mem_nhds hA₀ hW))
  obtain ⟨A₁, hA₁, V₂, hV₂, hAV_sub⟩ := mem_nhds_prod_iff.1 hV₁
  obtain ⟨r, hr, hr_ball⟩ := Metric.mem_nhds_iff.1 hV₂
  have hζ_lt : ∀ᶠ α in 𝓝 α₀, ‖ζ α‖ < r ^ 2 :=
    (hζc.eventually (by rw [hζ0]; exact ball_mem_nhds (0 : 𝕜) (sq_pos_of_pos hr))).mono
      fun _ h => by simpa [mem_ball_zero_iff] using h
  have hball {α : E} {u : 𝕜} (hα : ‖ζ α‖ < r ^ 2) (hu : u ^ 2 = ζ α) : u ∈ ball (0 : 𝕜) r := by
    rw [mem_ball_zero_iff]
    exact lt_of_pow_lt_pow_left₀ 2 hr.le (by rwa [← norm_pow, hu])
  refine ⟨T, A₀ ∩ A₁ ∩ {α | ‖ζ α‖ < r ^ 2}, inter_mem (inter_mem hA₀ hA₁) hζ_lt, W, hW,
    hTa, hT0, fun α hα => ?_⟩
  have hT_maps : Set.MapsTo (fun u : 𝕜 => T (α, u)) {u | u ^ 2 = ζ α} W := fun u hu =>
    (hAV_sub (Set.mk_mem_prod hα.1.2 (hr_ball (hball hα.2 hu)))).2.2
  have hinv_W : Set.InvOn (fun u : 𝕜 => T (α, u)) (fun t : 𝕜 => w (α, t)) W {u | u ^ 2 = ζ α} :=
    ⟨fun t ht => by simpa using congrArg Prod.snd (hinvOn₀.1 (hAW_sub (Set.mk_mem_prod hα.1.1 ht))),
      fun u hu => by
        simpa using congrArg Prod.snd
          (hinvOn₀.2 (hAV_sub (Set.mk_mem_prod hα.1.2 (hr_ball (hball hα.2 hu)))).1)⟩
  have hmaps₁ : Set.MapsTo (fun t : 𝕜 => w (α, t))
      (W ∩ {t | deriv (fun s => p (α, s)) t = 0}) {u | u ^ 2 = ζ α} := fun t ht =>
    (hbij₁.mapsTo ⟨hAW_sub ⟨hα.1.1, ht.1⟩, ht.2⟩).2
  have hmaps₂ : Set.MapsTo (fun u : 𝕜 => T (α, u))
      {u | u ^ 2 = ζ α} (W ∩ {t | deriv (fun s => p (α, s)) t = 0}) := fun u hu =>
    have huV₁ := hAV_sub (Set.mk_mem_prod hα.1.2 (hr_ball (hball hα.2 hu)))
    ⟨huV₁.2.2, (hbij₂.mapsTo ⟨huV₁.1, hu⟩).2⟩
  exact ⟨hT_maps, hinv_W, (hinv_W.mono inter_subset_left Subset.rfl).bijOn hmaps₁ hmaps₂⟩

/-- For a one-variable germ `g(t) = u(t) ^ 3 / 3 + c` with `u` twice continuously differentiable at
`t₀` and `u(t₀) = 0`, `deriv (deriv g)` has derivative `2 * u'(t₀) ^ 3` at `t₀`, over any
nontrivially normed field of characteristic `≠ 3`. -/
theorem hasDerivAt_deriv_deriv_two_mul_deriv_pow_three {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NeZero (3 : 𝕜)] {g u : 𝕜 → 𝕜} {t₀ c : 𝕜}
    (hu0 : u t₀ = 0) (hu : ContDiffAt 𝕜 2 u t₀)
    (hgu : ∀ᶠ t in 𝓝 t₀, g t = u t ^ 3 / 3 + c) :
    HasDerivAt (deriv (deriv g)) (2 * deriv u t₀ ^ 3) t₀ := by
  have hu1 : ContDiffAt 𝕜 1 (deriv u) t₀ := hu.derivWithin (by norm_num)
  have hu2 : ContDiffAt 𝕜 0 (deriv (deriv u)) t₀ := hu1.derivWithin (by norm_num)
  have hu_ev : ∀ᶠ t in 𝓝 t₀, ContDiffAt 𝕜 2 u t := hu.eventually (by simp)
  have hd₁ : deriv g =ᶠ[𝓝 t₀] fun t => u t ^ 2 * deriv u t := by
    filter_upwards [hgu.eventually_nhds, hu_ev] with t ht hut
    simpa using deriv_eq_sq_sub_mul_deriv (ζ := 0) (hut.differentiableAt (by norm_num))
      (by simpa using ht)
  have hd₂ : deriv (deriv g) =ᶠ[𝓝 t₀]
      fun t => 2 * u t * deriv u t ^ 2 + u t ^ 2 * deriv (deriv u) t := by
    filter_upwards [hd₁.eventually_nhds, hu_ev] with t ht hut
    rw [Filter.EventuallyEq.deriv_eq ht]
    have hu't : DifferentiableAt 𝕜 (deriv u) t :=
      (hut.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have h1 : HasDerivAt (fun s => u s ^ 2) ((2 : ℕ) * u t ^ (2 - 1) * deriv u t) t :=
      (hut.differentiableAt (by norm_num)).hasDerivAt.pow 2
    rw [(h1.fun_mul hu't.hasDerivAt).deriv]
    norm_num
    ring
  have h_left : HasDerivAt (fun t => 2 * u t * deriv u t ^ 2) (2 * deriv u t₀ ^ 3) t₀ := by
    have hu0_d : HasDerivAt u (deriv u t₀) t₀ := (hu.differentiableAt (by norm_num)).hasDerivAt
    have hu1_d : HasDerivAt (deriv u) (deriv (deriv u) t₀) t₀ :=
      (hu1.differentiableAt (by norm_num)).hasDerivAt
    have h := (hu0_d.const_mul 2).fun_mul (hu1_d.fun_pow 2)
    have hval : 2 * deriv u t₀ * deriv u t₀ ^ 2 +
        2 * u t₀ * ((2 : ℕ) * deriv u t₀ ^ (2 - 1) * deriv (deriv u) t₀) =
        2 * deriv u t₀ ^ 3 := by
      rw [hu0]; ring
    rwa [hval] at h
  -- Only `C²` regularity of `u` is assumed, so we avoid differentiating `deriv (deriv u)` at `t₀`.
  have h_right : HasDerivAt (fun t => u t ^ 2 * deriv (deriv u) t) 0 t₀ := by
    have ho₁ : (fun t => u t * deriv (deriv u) t) =o[𝓝 t₀] fun _ : 𝕜 => (1 : 𝕜) := by
      rw [Asymptotics.isLittleO_one_iff]
      simpa [hu0] using (hu.continuousAt.fun_mul hu2.continuousAt).tendsto
    have ho₂ : u =O[𝓝 t₀] fun t => t - t₀ := by
      simpa [hu0] using (hu.differentiableAt (by norm_num)).hasDerivAt.isBigO_sub
    rw [hasDerivAt_iff_isLittleO]
    refine (ho₁.mul_isBigO ho₂).congr' (Eventually.of_forall fun t => ?_)
      (Eventually.of_forall fun t => ?_)
    · simp [hu0]; ring
    · simp
  simpa [add_zero] using (h_left.fun_add h_right).congr_of_eventuallyEq hd₂

/-- For a one-variable germ `g(t) = u(t) ^ 3 / 3 + c` with `u` twice continuously differentiable at
`t₀` and `u(t₀) = 0`, the third derivative of `g` at `t₀` is `2 * u'(t₀) ^ 3`, over any nontrivially
normed field of characteristic `≠ 3`. -/
theorem deriv_deriv_deriv_eq_two_mul_deriv_pow_three {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NeZero (3 : 𝕜)] {g u : 𝕜 → 𝕜} {t₀ c : 𝕜}
    (hu0 : u t₀ = 0) (hu : ContDiffAt 𝕜 2 u t₀)
    (hgu : ∀ᶠ t in 𝓝 t₀, g t = u t ^ 3 / 3 + c) :
    deriv (deriv (deriv g)) t₀ = 2 * deriv u t₀ ^ 3 :=
  (hasDerivAt_deriv_deriv_two_mul_deriv_pow_three hu0 hu hgu).deriv

/-- Along `t = t₀`, `∂p/∂t (α, t₀)` agrees near `α₀` with
`(w(α, t₀) ^ 2 - ζ(α)) * ∂w/∂t (α, t₀)`. -/
private theorem eventuallyEq_deriv_snd_slice {p w : ℂ × ℂ → ℂ} {ζ η : ℂ → ℂ} {α₀ t₀ : ℂ}
    (hwa : AnalyticAt ℂ w (α₀, t₀))
    (hpw : ∀ᶠ q in 𝓝 (α₀, t₀), p q = w q ^ 3 / 3 - ζ q.1 * w q + η q.1) :
    (fun α => deriv (fun t => p (α, t)) t₀) =ᶠ[𝓝 α₀]
      fun α => (w (α, t₀) ^ 2 - ζ α) * deriv (fun t => w (α, t)) t₀ := by
  filter_upwards [(Continuous.prodMk_left t₀).continuousAt.eventually
    (hwa.eventually_analyticAt.and hpw.eventually_nhds)] with α ⟨hwα, hpα⟩
  have hwt : DifferentiableAt ℂ (fun t => w (α, t)) t₀ := hwα.curry_right.differentiableAt
  exact deriv_eq_sq_sub_mul_deriv hwt
    (by simpa using (Continuous.prodMk_right α).continuousAt.eventually hpα)

/-- **Mixed-derivative `HasDerivAt` identity for the cubic normal form.** For any cubic normal
form `p(α, t) = w(α, t) ^ 3 / 3 - ζ(α) * w(α, t) + η(α)` where `w` is complex differentiable on
a neighbourhood of `(α₀, t₀)`, with `ζ(α₀) = 0`, `w(α₀, t₀) = 0`, and `HasDerivAt ζ ζ' α₀`, the
slice `α ↦ ∂p/∂t (α, t₀)` is differentiable at `α₀` with derivative `-ζ' * ∂w/∂t (α₀, t₀)`. -/
theorem hasDerivAt_deriv_neg_mul_deriv {p w : ℂ × ℂ → ℂ} {ζ η : ℂ → ℂ} {α₀ t₀ ζ' : ℂ}
    (hζ0 : ζ α₀ = 0) (hw0 : w (α₀, t₀) = 0) (hζ : HasDerivAt ζ ζ' α₀)
    (hw : ∀ᶠ q in 𝓝 (α₀, t₀), DifferentiableAt ℂ w q)
    (hpw : ∀ᶠ q in 𝓝 (α₀, t₀), p q = w q ^ 3 / 3 - ζ q.1 * w q + η q.1) :
    HasDerivAt (fun α => deriv (fun t => p (α, t)) t₀)
      (-ζ' * deriv (fun t => w (α₀, t)) t₀) α₀ := by
  have hwa : AnalyticAt ℂ w (α₀, t₀) :=
    analyticAt_iff_eventually_differentiableAt_of_finiteDimensional.2 hw
  have hg : AnalyticAt ℂ (fun α => deriv (fun t => w (α, t)) t₀) α₀ := hwa.deriv_snd.curry_left
  have hh' : HasDerivAt (fun α => w (α, t₀) ^ 2) 0 α₀ := by
    simpa [Pi.pow_def, hw0] using hwa.curry_left.differentiableAt.hasDerivAt.pow 2
  have hprod : HasDerivAt
      (fun α => (w (α, t₀) ^ 2 - ζ α) * deriv (fun t => w (α, t)) t₀)
      (-ζ' * deriv (fun t => w (α₀, t)) t₀) α₀ := by
    have h := (hh'.fun_sub hζ).fun_mul hg.differentiableAt.hasDerivAt
    simpa [hw0, hζ0] using h
  exact hprod.congr_of_eventuallyEq (eventuallyEq_deriv_snd_slice hwa hpw)

/-- Shared proof of the totalized mixed-derivative identity, requiring continuity of `ζ` only when
`∂w/∂t (α₀, t₀) = 0`. -/
private theorem deriv_deriv_eq_neg_deriv_mul_deriv_aux {p w : ℂ × ℂ → ℂ} {ζ η : ℂ → ℂ}
    {α₀ t₀ : ℂ} (hζ0 : ζ α₀ = 0) (hw0 : w (α₀, t₀) = 0)
    (hζ : deriv (fun t => w (α₀, t)) t₀ = 0 → ContinuousAt ζ α₀)
    (hw : ∀ᶠ q in 𝓝 (α₀, t₀), DifferentiableAt ℂ w q)
    (hpw : ∀ᶠ q in 𝓝 (α₀, t₀), p q = w q ^ 3 / 3 - ζ q.1 * w q + η q.1) :
    deriv (fun α => deriv (fun t => p (α, t)) t₀) α₀ =
      -deriv ζ α₀ * deriv (fun t => w (α₀, t)) t₀ := by
  by_cases hζd : DifferentiableAt ℂ ζ α₀
  · exact (hasDerivAt_deriv_neg_mul_deriv hζ0 hw0 hζd.hasDerivAt hw hpw).deriv
  have hwa : AnalyticAt ℂ w (α₀, t₀) :=
    analyticAt_iff_eventually_differentiableAt_of_finiteDimensional.2 hw
  have hg : AnalyticAt ℂ (fun α => deriv (fun t => w (α, t)) t₀) α₀ := hwa.deriv_snd.curry_left
  have hh : AnalyticAt ℂ (fun α => w (α, t₀) ^ 2) α₀ := hwa.curry_left.pow 2
  rw [(eventuallyEq_deriv_snd_slice hwa hpw).deriv_eq]
  by_cases hdw : deriv (fun t => w (α₀, t)) t₀ = 0
  · have ho₁ : (fun α => w (α, t₀) ^ 2 - ζ α) =o[𝓝 α₀] fun _ : ℂ => (1 : ℂ) := by
      rw [Asymptotics.isLittleO_one_iff]
      simpa [Pi.sub_def, hw0, hζ0] using (hh.continuousAt.sub (hζ hdw)).tendsto
    have ho₂ : (fun α => deriv (fun t => w (α, t)) t₀) =O[𝓝 α₀] fun α => α - α₀ := by
      simpa [hdw] using hg.differentiableAt.hasDerivAt.isBigO_sub
    have hd0 : HasDerivAt
        (fun α => (w (α, t₀) ^ 2 - ζ α) * deriv (fun t => w (α, t)) t₀) 0 α₀ := by
      rw [hasDerivAt_iff_isLittleO]
      simpa [hw0, hζ0, hdw] using ho₁.mul_isBigO ho₂
    rw [hd0.deriv, hdw, mul_zero]
  · have hnot : ¬DifferentiableAt ℂ
        (fun α => (w (α, t₀) ^ 2 - ζ α) * deriv (fun t => w (α, t)) t₀) α₀ := fun hfd => by
      have hζ_eq : ζ =ᶠ[𝓝 α₀] fun α =>
          w (α, t₀) ^ 2 - ((w (α, t₀) ^ 2 - ζ α) * deriv (fun t => w (α, t)) t₀) /
            deriv (fun t => w (α, t)) t₀ :=
        (hg.continuousAt.eventually_ne hdw).mono fun α hgα => by
          dsimp only
          rw [mul_div_cancel_right₀ _ hgα, sub_sub_cancel]
      exact hζd ((hh.differentiableAt.fun_sub
        (hfd.div hg.differentiableAt hdw)).congr_of_eventuallyEq hζ_eq)
    rw [deriv_zero_of_not_differentiableAt hnot, deriv_zero_of_not_differentiableAt hζd,
      neg_zero, zero_mul]

/-- Mixed-derivative identity when `∂w/∂t (α₀, t₀) ≠ 0`, requiring no continuity hypothesis on
`ζ`. -/
private theorem deriv_deriv_eq_neg_deriv_mul_deriv_of_ne_zero {p w : ℂ × ℂ → ℂ} {ζ η : ℂ → ℂ}
    {α₀ t₀ : ℂ} (hζ0 : ζ α₀ = 0) (hw0 : w (α₀, t₀) = 0)
    (hdw : deriv (fun t => w (α₀, t)) t₀ ≠ 0)
    (hw : ∀ᶠ q in 𝓝 (α₀, t₀), DifferentiableAt ℂ w q)
    (hpw : ∀ᶠ q in 𝓝 (α₀, t₀), p q = w q ^ 3 / 3 - ζ q.1 * w q + η q.1) :
    deriv (fun α => deriv (fun t => p (α, t)) t₀) α₀ =
      -deriv ζ α₀ * deriv (fun t => w (α₀, t)) t₀ :=
  deriv_deriv_eq_neg_deriv_mul_deriv_aux hζ0 hw0 (fun h0 => absurd h0 hdw) hw hpw

/-- **Totalized mixed-derivative identity for the cubic normal form.** For any cubic normal form
`p(α, t) = w(α, t) ^ 3 / 3 - ζ(α) * w(α, t) + η(α)` where `w` is complex differentiable on a
neighbourhood of `(α₀, t₀)`, with `ζ(α₀) = 0`, `w(α₀, t₀) = 0`, and `ζ` continuous at `α₀`, one
has `∂²p/∂α∂t (α₀, t₀) = -ζ'(α₀) * ∂w/∂t (α₀, t₀)` as totalized `deriv` values: when `ζ` is not
differentiable at `α₀` and `∂w/∂t (α₀, t₀) ≠ 0`, `α ↦ ∂p/∂t (α, t₀)` is also nondifferentiable
at `α₀` so both sides vanish by Lean's zero-by-default `deriv` convention (whereas when
`∂w/∂t (α₀, t₀) = 0`, `α ↦ ∂p/∂t (α, t₀)` is differentiable at `α₀` with derivative `0`). See
`hasDerivAt_deriv_neg_mul_deriv` for the `HasDerivAt` form when `ζ` is differentiable. -/
theorem deriv_deriv_eq_neg_deriv_mul_deriv {p w : ℂ × ℂ → ℂ} {ζ η : ℂ → ℂ} {α₀ t₀ : ℂ}
    (hζ0 : ζ α₀ = 0) (hw0 : w (α₀, t₀) = 0) (hζ : ContinuousAt ζ α₀)
    (hw : ∀ᶠ q in 𝓝 (α₀, t₀), DifferentiableAt ℂ w q)
    (hpw : ∀ᶠ q in 𝓝 (α₀, t₀), p q = w q ^ 3 / 3 - ζ q.1 * w q + η q.1) :
    deriv (fun α => deriv (fun t => p (α, t)) t₀) α₀ =
      -deriv ζ α₀ * deriv (fun t => w (α₀, t)) t₀ :=
  deriv_deriv_eq_neg_deriv_mul_deriv_aux hζ0 hw0 (fun _ => hζ) hw hpw

/-- **Nondegeneracy criterion for square-root coalescence.** In any cubic normal form
`p(α, t) = w(α, t) ^ 3 / 3 - ζ(α) * w(α, t) + η(α)` where `w` is complex differentiable on a
neighbourhood of `(α₀, t₀)`, with `ζ(α₀) = 0`, `w(α₀, t₀) = 0`, and `∂w/∂t (α₀, t₀) ≠ 0`, one has
`ζ'(α₀) ≠ 0` if and only if `∂²p/∂α∂t (α₀, t₀) ≠ 0`. -/
theorem deriv_ne_zero_iff_deriv_deriv_ne_zero {p w : ℂ × ℂ → ℂ} {ζ η : ℂ → ℂ} {α₀ t₀ : ℂ}
    (hζ0 : ζ α₀ = 0) (hw0 : w (α₀, t₀) = 0)
    (hdw : deriv (fun t => w (α₀, t)) t₀ ≠ 0)
    (hw : ∀ᶠ q in 𝓝 (α₀, t₀), DifferentiableAt ℂ w q)
    (hpw : ∀ᶠ q in 𝓝 (α₀, t₀), p q = w q ^ 3 / 3 - ζ q.1 * w q + η q.1) :
    deriv ζ α₀ ≠ 0 ↔ deriv (fun α => deriv (fun t => p (α, t)) t₀) α₀ ≠ 0 := by
  rw [deriv_deriv_eq_neg_deriv_mul_deriv_of_ne_zero hζ0 hw0 hdw hw hpw,
    mul_ne_zero_iff, neg_ne_zero]
  exact ⟨fun hne => ⟨hne, hdw⟩, fun hne => hne.1⟩

end CubicNormalForm

/-! ### Canonical and degenerate coalescing critical-point examples -/

-- For the canonical Airy potential `p(α, t) = t ^ 3 / 3 - α * t`, the critical points satisfy
-- `t ^ 2 = α`, coalescing at rate `√α` as `α → 0`.
example {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NeZero (3 : 𝕜)] (α t : 𝕜) :
    deriv (fun s : 𝕜 => s ^ 3 / 3 - α * s) t = 0 ↔ t ^ 2 = α :=
  CubicNormalForm.deriv_eq_zero_iff_sq_eq (u := id) (c := 0) (by simp) (.of_forall fun _ => by simp)

-- The canonical Airy potential `p(α, t) = t ^ 3 / 3 - α * t` has nonvanishing mixed derivative
-- `∂²p/∂α∂t (0, 0) = -1`.
example : deriv (fun α : ℂ => deriv (fun t : ℂ => t ^ 3 / 3 - α * t) 0) 0 = -1 := by
  have h := CubicNormalForm.deriv_deriv_eq_neg_deriv_mul_deriv
    (p := fun q : ℂ × ℂ => q.2 ^ 3 / 3 - q.1 * q.2) (w := Prod.snd) (ζ := id) (η := 0)
    rfl rfl continuousAt_id (.of_forall fun _ => differentiableAt_snd)
    (.of_forall fun _ => by simp)
  simpa using h

-- For `p(α, t) = t ^ 3 / 3 + α ^ 2 * t`, the mixed derivative `∂²p/∂α∂t` vanishes at `(0, 0)`,
-- so any cubic normal form has `ζ'(0) = 0`.
example : deriv (fun α : ℂ => deriv (fun t : ℂ => t ^ 3 / 3 + α ^ 2 * t) 0) 0 = 0 := by
  have h := CubicNormalForm.deriv_deriv_eq_neg_deriv_mul_deriv
    (p := fun q : ℂ × ℂ => q.2 ^ 3 / 3 + q.1 ^ 2 * q.2) (w := Prod.snd)
    (ζ := fun α => -(α ^ 2)) (η := 0) (α₀ := 0) (t₀ := 0)
    (by simp) rfl (by fun_prop) (.of_forall fun _ => differentiableAt_snd)
    (.of_forall fun _ => by simp)
  simpa using h

-- For `p(α, t) = t ^ 3 / 3 + α ^ 2 * t`, the critical points are `t = ±i * α`, coalescing
-- linearly in `α` rather than at rate `√α`.
example (α t : ℂ) :
    deriv (fun s : ℂ => s ^ 3 / 3 + α ^ 2 * s) t = 0 ↔
      t = Complex.I * α ∨ t = -(Complex.I * α) := by
  have h := CubicNormalForm.deriv_eq_zero_iff_sq_eq (u := id) (ζ := -(α ^ 2)) (c := 0)
    (g := fun s : ℂ => s ^ 3 / 3 + α ^ 2 * s) (t := t) (by simp)
    (.of_forall fun _ => by simp)
  rw [h, id_eq, show -(α ^ 2) = (Complex.I * α) ^ 2 by rw [mul_pow, Complex.I_sq]; ring,
    sq_eq_sq_iff_eq_or_eq_neg]

end TauCeti
