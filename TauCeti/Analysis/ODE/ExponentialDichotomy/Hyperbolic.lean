/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import TauCeti.Analysis.Complex.Polynomial.ImaginaryAxis
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import TauCeti.Algebra.Polynomial.Semiconj
import TauCeti.Analysis.Normed.Algebra.Exponential
import TauCeti.Analysis.Normed.Module.Complexification
import TauCeti.Analysis.Normed.Operator.Exponential
import TauCeti.Analysis.ODE.ExponentialDichotomy
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Exponential dichotomy for hyperbolic linear operators

Let `A` be a bounded operator on a finite-dimensional real normed space `E`, annihilated by a real
polynomial `p` without complex roots on the imaginary axis. Taking for `p` the characteristic
polynomial, the hypothesis says that `A` is *hyperbolic*: it has no eigenvalue on the imaginary
axis. This file proves that the linear flow `t ↦ exp (t • A)` then has an exponential dichotomy:
there are an idempotent `P` commuting with `A` and constants `K, α > 0` with

* `‖exp (t • A) (P v)‖ ≤ K * exp (-α t) * ‖v‖` for `t ≥ 0`, and
* `‖exp (t • A) (v - P v)‖ ≤ K * exp (α t) * ‖v‖` for `t ≤ 0`

(`ContinuousLinearMap.exists_projection_exponential_bounds_of_aeval_eq_zero`). These are the
hypotheses of the Lyapunov–Perron construction of stable and unstable manifolds
(`ContinuousLinearMap.lyapunovPerronIntegral`). For symmetric operators they are supplied by
`TauCeti.Analysis.ODE.ExponentialDichotomy`, from an orthonormal eigenbasis; the operators here
need not be symmetric or diagonalizable.

The projection `P` is a polynomial in `A`, the projection onto the stable subspace `ker pₛ(A)`
along the unstable subspace `ker pᵤ(A)`, where `p = pₛ * pᵤ` is the factorization of
`Polynomial.exists_isCoprime_mul_eq_of_re_ne_zero` into factors with roots in the left and in the
right half-plane.

## The decay estimate

The analytic input is `ContinuousLinearMap.exists_norm_exp_smul_le_of_aeval_eq_zero`: if
`aeval B p = 0` for a polynomial `p` all of whose complex roots have negative real part, then
`‖exp (t • B)‖ ≤ K * exp (-α t)` for `t ≥ 0`. It is first proved for operators `T` on a
finite-dimensional complex space (`ContinuousLinearMap.exists_norm_exp_smul_le_of_aeval_eq_zero'`),
and transferred to real operators through the isometric complexification
`ContinuousLinearMap.complexify`. For the complex statement:

* the eigenvalues of `T` are roots of `p`. Choose `β > 0` with every root of `p` of real part
  below `-β`; the eigenvalues of `N = T + β` still have negative real part;
* in finite dimension `exp N` is a polynomial in `N` (`TauCeti.exists_aeval_eq_exp`), so by the
  spectral mapping theorem for polynomials the spectrum of `exp N` consists of the values `exp μ`
  at the eigenvalues `μ` of `N` (`ContinuousLinearMap.spectrum_exp`). These lie in the open unit
  disc;
* by Gelfand's formula the powers of `exp N` are bounded
  (`norm_pow_le_mul_pow_of_gelfandRadius_lt`). Writing `t = n + s` with `n` a natural
  number and `0 ≤ s < 1` bounds `exp (t • N) = (exp N) ^ n * exp (s • N)` uniformly in `t ≥ 0`,
  and `exp (t • T) = exp (-β t) * exp (t • N)`.

For the dichotomy, the operator `B = A P - (1 - P)` agrees with `A` on the range of `P` and with
`-1` on its kernel. It is annihilated by `pₛ(X) (X + 1)`, whose roots have negative real part, and
`exp (t • B) P = exp (t • A) P`. The decay estimate for `B` is the forward bound; the backward
bound is the forward bound for `-A`, the projection `1 - P` and the factor `pᵤ(-X)`. These bounds
on the range and kernel of `P` are put in projection form by
`ContinuousLinearMap.IsIdempotentElem.exists_projection_exponential_bounds`.

## Main results

* `ContinuousLinearMap.exists_norm_exp_smul_le_of_aeval_eq_zero'` and
  `ContinuousLinearMap.exists_norm_exp_smul_le_of_aeval_eq_zero`: exponential decay of
  `exp (t • T)` for complex and for real operators annihilated by a polynomial with roots in the
  open left half-plane.
* `ContinuousLinearMap.exists_projection_exponential_bounds_of_aeval_eq_zero`: the exponential
  dichotomy for an operator annihilated by a polynomial without roots on the imaginary axis, and
  `ContinuousLinearMap.exists_projection_exponential_bounds_of_charpoly` for the characteristic
  polynomial.

## References

* M. W. Hirsch, S. Smale and R. L. Devaney, *Differential Equations, Dynamical Systems, and an
  Introduction to Chaos*, 3rd ed., Academic Press, 2013, Chapter 4 (hyperbolic linear systems).
* W. A. Coppel, *Dichotomies in Stability Theory*, Lecture Notes in Mathematics 629, Springer,
  1978, Chapter 1.
-/

public section

open Polynomial NormedSpace Filter Topology
open scoped NNReal

namespace ContinuousLinearMap

section Complex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- **Exponential decay for complex operators.** Let `T` be an operator on a finite-dimensional
complex normed space, annihilated by a polynomial `q` all of whose roots have negative real part,
so that every eigenvalue of `T` lies in the open left half-plane. Then `exp (t T)` decays
exponentially: `‖exp (t T)‖ ≤ K * exp (-α t)` for `t ≥ 0`, with `K, α > 0`. -/
theorem exists_norm_exp_smul_le_of_aeval_eq_zero' (T : V →L[ℂ] V) {q : ℂ[X]}
    (hq : aeval T q = 0) (hroots : ∀ z : ℂ, q.eval z = 0 → z.re < 0) :
    ∃ K α : ℝ, 0 < K ∧ 0 < α ∧ ∀ t : ℝ, 0 ≤ t → ‖exp ((t : ℂ) • T)‖ ≤ K * Real.exp (-α * t) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine ⟨1, 1, one_pos, one_pos, fun t _ ↦ ?_⟩
    rw [Subsingleton.elim (exp ((t : ℂ) • T)) 0, norm_zero]
    positivity
  have := FiniteDimensional.complete ℂ V
  let +nondep : NormedAlgebra ℚ (V →L[ℂ] V) := .restrictScalars ℚ ℂ _
  -- A uniform margin `β` between the roots of `q` and the imaginary axis.
  obtain ⟨β, hβ, hβq⟩ := exists_pos_forall_re_lt_neg_of_re_lt_zero hroots
  -- The shifted operator `N = T + β` is annihilated by `q (X - β)`, whose roots also have
  -- negative real part.
  set N : V →L[ℂ] V := T + (β : ℂ) • 1 with hN
  set r : ℂ[X] := q.comp (X - C (β : ℂ)) with hr
  have hNr : aeval N r = 0 := by
    rw [hr, aeval_comp, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, hN,
      add_sub_cancel_right, hq]
  have hrroots (z : ℂ) (hz : r.eval z = 0) : z.re < 0 := by
    rw [hr, eval_comp, eval_sub, eval_X, eval_C] at hz
    have := hβq _ hz
    rw [Complex.sub_re, Complex.ofReal_re] at this
    linarith
  -- The spectrum of `exp N` lies in the open unit disc, so its powers are bounded.
  have hspec : ∀ z ∈ spectrum ℂ (exp N), ‖z‖₊ < 1 := by
    intro z hz
    rw [N.spectrum_exp] at hz
    obtain ⟨μ, hμ, rfl⟩ := hz
    have hrμ : r.eval μ = 0 := by
      have := spectrum.subset_polynomial_aeval N r ⟨μ, hμ, rfl⟩
      rwa [hNr, spectrum.zero_eq, Set.mem_singleton_iff] at this
    rw [← NNReal.coe_lt_coe, coe_nnnorm, ← Complex.exp_eq_exp_ℂ, Complex.norm_exp,
      NNReal.coe_one, Real.exp_lt_one_iff]
    exact hrroots μ hrμ
  have hρ := spectrum.spectralRadius_lt_of_forall_lt _ hspec
  rw [spectrum.spectralRadius_eq_gelfandRadius, ENNReal.coe_one, ENNReal.ofReal_lt_one] at hρ
  obtain ⟨C, hC0, hC⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt _ hρ
  simp only [one_pow, mul_one] at hC
  refine ⟨C * Real.exp ‖N‖, β, by positivity, hβ, fun t ht ↦ ?_⟩
  -- Undo the shift: `exp (t • T) = exp (t • N) * exp (-β t)`.
  have hTN : (t : ℂ) • T = (t : ℂ) • N + (-((t : ℂ) * β)) • (1 : V →L[ℂ] V) := by
    rw [hN, smul_add, smul_smul, neg_smul]
    abel
  rw [hTN, exp_add_of_commute ((Commute.one_right _).smul_right _),
    ← Algebra.algebraMap_eq_smul_one, ← algebraMap_exp_comm, Algebra.algebraMap_eq_smul_one,
    mul_smul_comm, mul_one, norm_smul, ← Complex.exp_eq_exp_ℂ, Complex.norm_exp, mul_comm]
  gcongr
  · exact TauCeti.norm_exp_smul_le_mul_exp_norm_of_norm_exp_pow_le (by simp) hC ht
  · simp [mul_comm]

end Complex

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Exponential decay for real operators.** Let `B` be an operator on a finite-dimensional real
normed space, annihilated by a real polynomial `p` all of whose complex roots have negative real
part. Then `‖exp (t • B)‖ ≤ K * exp (-α t)` for `t ≥ 0`, with `K, α > 0`. -/
theorem exists_norm_exp_smul_le_of_aeval_eq_zero (B : E →L[ℝ] E) {p : ℝ[X]}
    (hp : aeval B p = 0) (hroots : ∀ z : ℂ, aeval z p = 0 → z.re < 0) :
    ∃ K α : ℝ, 0 < K ∧ 0 < α ∧ ∀ t : ℝ, 0 ≤ t → ‖exp (t • B)‖ ≤ K * Real.exp (-α * t) := by
  have := FiniteDimensional.complete ℝ E
  have : FiniteDimensional ℝ (TauCeti.Complexification E) :=
    (TauCeti.Complexification.equivProd E).symm.toLinearEquiv.finiteDimensional
  have : FiniteDimensional ℂ (TauCeti.Complexification E) :=
    Module.Finite.of_restrictScalars_finite ℝ ℂ _
  obtain ⟨K, α, hK, hα, h⟩ := B.complexify.exists_norm_exp_smul_le_of_aeval_eq_zero'
    (q := p.map (algebraMap ℝ ℂ))
    (by rw [aeval_map_algebraMap, ← complexifyAlgHom_apply, aeval_algHom_apply, hp, map_zero])
    fun z hz ↦ hroots z (by rwa [eval_map_algebraMap] at hz)
  refine ⟨K, α, hK, hα, fun t ht ↦ ?_⟩
  let +nondep : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ _
  let +nondep : NormedAlgebra ℚ (TauCeti.Complexification E →L[ℂ] TauCeti.Complexification E) :=
    .restrictScalars ℚ ℂ _
  have hexp : (exp (t • B)).complexify = exp ((t : ℂ) • B.complexify) := by
    rw [← complexifyAlgHom_apply,
      map_exp (complexifyAlgHom E) continuous_complexifyAlgHom, complexifyAlgHom_apply]
    congr 1
    ext z <;> simp
  rw [← norm_complexify, hexp]
  exact h t ht

end Real

section Dichotomy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The forward half of the dichotomy. If `P` is an idempotent commuting with `A` and `p(A)`
vanishes on the range of `P`, for a polynomial `p` with roots in the open left half-plane, then
`exp (t • A)` decays exponentially on the range of `P`. -/
private theorem exists_norm_exp_smul_apply_le_of_aeval_mul_eq_zero {A P : E →L[ℝ] E}
    (hP : IsIdempotentElem P) (hAP : Commute A P) {p : ℝ[X]} (hp : aeval A p * P = 0)
    (hroots : ∀ z : ℂ, aeval z p = 0 → z.re < 0) :
    ∃ K α : ℝ, 0 < K ∧ 0 < α ∧
      ∀ t : ℝ, 0 ≤ t → ∀ w ∈ P.range, ‖exp (t • A) w‖ ≤ K * Real.exp (-α * t) * ‖w‖ := by
  -- The operator `B = A P - (1 - P)` agrees with `A` on the range of `P`, so
  -- `exp (t • B) P = exp (t • A) P`, and it is annihilated by `p(X) (X + 1)`, so the decay
  -- estimate applies to it.
  set B : E →L[ℝ] E := A * P - (1 - P) with hB
  have hBP : B * P = A * P := by rw [hB, sub_mul, mul_assoc, hP.eq, sub_mul, one_mul, hP.eq,
    sub_self, sub_zero]
  have hBc : Commute B P :=
    (hAP.mul_left (Commute.refl P)).sub_left ((Commute.one_left P).sub_left (Commute.refl P))
  -- `B` is annihilated by `p(X) (X + 1)`, since `B + 1 = P (A + 1)`.
  have hq : aeval B (p * (X + 1)) = 0 := by
    have h1 : B + 1 = P * (A + 1) := by
      rw [hB, mul_add, mul_one, ← hAP.eq]
      abel
    -- `P` semiconjugates `A` to `B`, so `p(B) P = P p(A) = p(A) P`.
    have hsc : SemiconjBy P A B := hAP.eq.symm.trans hBP.symm
    have hpBP : aeval B p * P = aeval A p * P := by
      rw [aeval_eq_smeval, aeval_eq_smeval, ← (hsc.smeval_right p).eq,
        (hAP.symm.smeval_right p).eq]
    rw [map_mul, map_add, aeval_X, map_one, h1, ← mul_assoc, hpBP, hp, zero_mul]
  have hqroots (z : ℂ) (hz : aeval z (p * (X + 1)) = 0) : z.re < 0 := by
    rw [map_mul, map_add, aeval_X, map_one, mul_eq_zero] at hz
    rcases hz with hz | hz
    · exact hroots z hz
    · rw [eq_neg_of_add_eq_zero_left hz]
      norm_num
  obtain ⟨K, α, hK, hα, h⟩ := B.exists_norm_exp_smul_le_of_aeval_eq_zero hq hqroots
  refine ⟨K, α, hK, hα, fun t ht w hw ↦ ?_⟩
  have hPw : P w = w := by
    obtain ⟨u, rfl⟩ := hw
    rw [coe_coe, ← mul_apply_eq_comp, hP.eq]
  let +nondep : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ _
  have hexp : exp (t • A) * P = exp (t • B) * P := by
    have hsc : SemiconjBy P (t • B) (t • A) :=
      (hBc.smul_left t).eq.symm.trans (by rw [smul_mul_assoc, smul_mul_assoc, hBP])
    rw [← hsc.exp_right.eq, (hBc.smul_left t).exp_left.eq]
  calc ‖exp (t • A) w‖ = ‖exp (t • B) w‖ := by
        rw [← hPw, ← mul_apply_eq_comp, hexp, mul_apply_eq_comp]
    _ ≤ ‖exp (t • B)‖ * ‖w‖ := le_opNorm _ _
    _ ≤ K * Real.exp (-α * t) * ‖w‖ := by gcongr; exact h t ht

/-- **Exponential dichotomy for a hyperbolic operator.** Let `A` be an operator on a
finite-dimensional real normed space, annihilated by a real polynomial `p` without complex roots
on the imaginary axis. Then there are an idempotent `P` commuting with `A` and constants
`K, α > 0` such that the flow of `A` contracts the range of `P` in forward time and the kernel of
`P` in backward time:
`‖exp (t • A) (P v)‖ ≤ K * exp (-α t) * ‖v‖` for `t ≥ 0` and
`‖exp (t • A) (v - P v)‖ ≤ K * exp (α t) * ‖v‖` for `t ≤ 0`. -/
theorem exists_projection_exponential_bounds_of_aeval_eq_zero (A : E →L[ℝ] E) {p : ℝ[X]}
    (hp : aeval A p = 0) (hroots : ∀ z : ℂ, aeval z p = 0 → z.re ≠ 0) :
    ∃ P : E →L[ℝ] E, IsIdempotentElem P ∧ Commute A P ∧ ∃ K α : ℝ≥0, 0 < K ∧ 0 < α ∧
      (∀ t : ℝ, 0 ≤ t → ∀ v : E, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖) ∧
      (∀ t : ℝ, t ≤ 0 → ∀ v : E, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖) := by
  obtain ⟨ps, pu, ⟨a, b, hab⟩, hmul, hps, hpu⟩ := p.exists_isCoprime_mul_eq_of_re_ne_zero hroots
  -- The Bézout identity `a pₛ + b pᵤ = 1` gives the projection `P = (b pᵤ)(A)` onto `ker pₛ(A)`
  -- along `ker pᵤ(A)`, with complement `1 - P = (a pₛ)(A)`.
  set P : E →L[ℝ] E := aeval A (b * pu) with hPdef
  have hP1 : 1 - P = aeval A (a * ps) := by
    rw [hPdef, ← map_one (aeval (R := ℝ) A), ← hab, map_add, add_sub_cancel_right]
  have hvanish (c : ℝ[X]) : aeval A (c * p) = 0 := by rw [map_mul, hp, mul_zero]
  have hP : IsIdempotentElem P := by
    have h0 : P * (1 - P) = 0 := by
      rw [hP1, hPdef, ← map_mul, show b * pu * (a * ps) = a * b * p by rw [← hmul]; ring,
        hvanish]
    rw [mul_sub, mul_one, sub_eq_zero] at h0
    exact h0.symm
  have hAP : Commute A P := by simpa only [aeval_X] using (Commute.all X (b * pu)).map (aeval A)
  -- The forward bound on the range of `P`, where `pₛ(A)` vanishes.
  obtain ⟨K₁, α₁, hK₁, hα₁, h₁⟩ := exists_norm_exp_smul_apply_le_of_aeval_mul_eq_zero hP hAP
    (p := ps) (by rw [hPdef, ← map_mul, show ps * (b * pu) = b * p by rw [← hmul]; ring,
      hvanish]) hps
  -- The backward bound on the kernel of `P` is the forward bound for `-A`, the projection
  -- `1 - P` and the polynomial `pᵤ(-X)`.
  obtain ⟨K₂, α₂, hK₂, hα₂, h₂⟩ := exists_norm_exp_smul_apply_le_of_aeval_mul_eq_zero
    (A := -A) hP.one_sub ((Commute.one_right _).sub_right hAP).neg_left (p := pu.comp (-X))
    (by rw [aeval_comp, map_neg, aeval_X, neg_neg, hP1, ← map_mul,
      show pu * (a * ps) = a * p by rw [← hmul]; ring, hvanish])
    fun z hz ↦ by
      rw [aeval_comp, map_neg, aeval_X] at hz
      simpa using hpu _ hz
  refine ⟨P, hP, hAP, IsIdempotentElem.exists_projection_exponential_bounds hP (C := max K₁ K₂)
    (lt_max_of_lt_left hK₁) (lt_min hα₁ hα₂) (fun t ht w hw ↦ (h₁ t ht w hw).trans ?_)
    fun t ht w hw ↦ ?_⟩
  · gcongr
    · exact le_max_left _ _
    · exact min_le_left _ _
  · -- The kernel of `P` is the range of `1 - P`, and the flow of `A` at time `t` is the flow of
    -- `-A` at time `-t`.
    have hw' : w ∈ (1 - P).range := by
      refine ⟨w, ?_⟩
      rw [LinearMap.mem_ker, coe_coe] at hw
      rw [coe_coe, sub_apply, one_apply_eq_self, hw, sub_zero]
    have := h₂ (-t) (by linarith) w hw'
    rw [neg_smul_neg] at this
    refine this.trans (mul_le_mul_of_nonneg_right (mul_le_mul (le_max_right _ _)
      (Real.exp_le_exp.mpr (by nlinarith [min_le_right α₁ α₂])) (Real.exp_nonneg _)
      (by positivity)) (norm_nonneg _))

/-- **Exponential dichotomy for a hyperbolic operator**, in terms of the characteristic
polynomial: if no complex root of the characteristic polynomial of `A` lies on the imaginary axis,
the flow of `A` has an exponential dichotomy, as in
`ContinuousLinearMap.exists_projection_exponential_bounds_of_aeval_eq_zero`. -/
theorem exists_projection_exponential_bounds_of_charpoly (A : E →L[ℝ] E)
    (hA : ∀ z : ℂ, aeval z (A : E →ₗ[ℝ] E).charpoly = 0 → z.re ≠ 0) :
    ∃ P : E →L[ℝ] E, IsIdempotentElem P ∧ Commute A P ∧ ∃ K α : ℝ≥0, 0 < K ∧ 0 < α ∧
      (∀ t : ℝ, 0 ≤ t → ∀ v : E, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖) ∧
      (∀ t : ℝ, t ≤ 0 → ∀ v : E, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖) := by
  refine A.exists_projection_exponential_bounds_of_aeval_eq_zero ?_ hA
  -- Cayley–Hamilton, transported from linear maps to continuous linear maps.
  refine coe_injective ?_
  rw [toLinearMap_aeval, toLinearMap_zero]
  exact LinearMap.aeval_self_charpoly _

end Dichotomy

end ContinuousLinearMap
