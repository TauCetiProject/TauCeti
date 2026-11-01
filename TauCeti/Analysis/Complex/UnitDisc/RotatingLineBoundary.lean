/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import TauCeti.Algebra.Polynomial.ConjReciprocal
public import TauCeti.Algebra.Polynomial.Eval.OnSet
public import TauCeti.Analysis.Complex.PowerSeries.FourierCoeff

/-!
# Holomorphic functions on the disc with boundary values on a rotating line

Fix an integer `k`. This file solves the Riemann–Hilbert problem on the closed unit disc
`closedBall 0 1`

`∂u/∂(conj z) = 0` on the open disc, `u` continuous on `closedBall 0 1`,
`u(e^{iθ}) ∈ e^{ikθ/2} ℝ` for all `θ`.

The boundary condition says that `u(w)` lies on the real line `w^{k/2} ℝ`, which is well defined
since `-ℝ = ℝ`. It is stated without square roots as `u w = w ^ k * conj (u w)` for `‖w‖ = 1`.
The loop of real lines `θ ↦ e^{ikθ/2} ℝ` in `ℂ` has Maslov index `k`, and this problem is the
one-dimensional model to which McDuff and Salamon reduce the Riemann–Roch theorem for
Cauchy–Riemann operators on the disc with totally real boundary conditions: there, the index of
the operator `∂/∂(conj z)` with boundary condition of Maslov index `μ` on a bundle of rank `n` is
`n + μ`.

The solutions are computed explicitly. Expand `u` in its Taylor series `∑ aₙ zⁿ`; the
coefficient `aₙ` is the `n`-th Fourier coefficient of the boundary values, and the negative
Fourier coefficients vanish by Cauchy's theorem. The boundary condition turns into
`aₙ = conj a_{k-n}` for every integer `n`, with `aₙ = 0` for `n < 0`. Hence `u` agrees on the
closed disc with a polynomial of degree at most `k` whose coefficients satisfy `aᵢ = conj aⱼ`
whenever `i + j = k`, a *conjugate-reciprocal* polynomial
(`DiffContOnCl.exists_mem_conjReciprocalPolynomials_eqOn`). Conversely every such polynomial is a
solution.
These polynomials form a real vector space of dimension `k + 1` for `k ≥ -1` and `0` for `k < 0`
(`TauCeti.finrank_conjReciprocalPolynomials`), so the space of solutions, as functions on the
closed disc, has real dimension `max (k + 1) 0` (`TauCeti.finrank_unitDiscCauchyRiemannKernel`).
For `k ≥ -1` this is `1 + k`, rank plus Maslov index, as the Riemann–Roch formula predicts once
the cokernel is known to vanish; the cokernel, which needs Sobolev completions, is not treated
here.

The conjugate-reciprocal polynomials `TauCeti.conjReciprocalPolynomials k` and their dimension
are developed in `TauCeti.Algebra.Polynomial.ConjReciprocal`, and the identification of Taylor
coefficients with Fourier coefficients of boundary values in
`TauCeti.Analysis.Complex.PowerSeries.FourierCoeff`.

## Main definitions

* `TauCeti.unitDiscCauchyRiemannKernel k`: the real subspace of functions on the closed unit disc
  that are restrictions of functions holomorphic on the open unit disc and continuous on its
  closure, satisfying `u w = w ^ k * conj (u w)` on the unit circle.

## Main results

* `DiffContOnCl.exists_mem_conjReciprocalPolynomials_eqOn`: a function `u : ℂ → ℂ` solving the
  problem agrees on the closed disc with a conjugate-reciprocal polynomial of degree at most `k`.
* `TauCeti.mem_unitDiscCauchyRiemannKernel_iff_exists_eval`: the solutions on the closed disc are
  exactly the conjugate-reciprocal polynomials of degree at most `k`.
* `TauCeti.unitDiscCauchyRiemannKernel_eq_bot`: for `k < 0` the only solution is zero.
* `TauCeti.eval_eq_zpow_mul_conj_eval`: a conjugate-reciprocal polynomial of degree at most `k`
  satisfies the boundary condition on the unit circle.
* `TauCeti.finiteDimensional_unitDiscCauchyRiemannKernel`: the solutions form a
  finite-dimensional real vector space.
* `TauCeti.finrank_unitDiscCauchyRiemannKernel`: the solutions form a real vector space of
  dimension `(k + 1).toNat`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C (the Riemann–Roch theorem, Theorem C.1.10, and
  its proof by reduction to the boundary condition `e^{ikθ/2} ℝ` in rank one; the Maslov index of
  a loop of totally real subspaces is Appendix C.3).
-/

public section

namespace TauCeti

open Complex Metric Module Polynomial Set
open scoped ComplexConjugate Real

/-! ### Boundary values of conjugate-reciprocal polynomials -/

variable {k : ℤ} {p : ℂ[X]}

/-- A conjugate-reciprocal polynomial of degree at most `k` takes values on the line
`w ^ (k / 2) ℝ` at each point `w` of the unit circle. -/
theorem eval_eq_zpow_mul_conj_eval (hp : p ∈ conjReciprocalPolynomials k) {w : ℂ}
    (hw : ‖w‖ = 1) : p.eval w = w ^ k * conj (p.eval w) := by
  rcases lt_or_ge k 0 with hk | hk
  · rw [conjReciprocalPolynomials_eq_bot hk, Submodule.mem_bot] at hp
    simp [hp]
  obtain ⟨hp, hp'⟩ := mem_conjReciprocalPolynomials_iff.mp hp
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m := ⟨k.toNat, by omega⟩
  have hdeg : p.natDegree < m + 1 :=
    Nat.lt_succ_of_le (natDegree_le_iff_coeff_eq_zero.mpr fun n hn => hp n (by exact_mod_cast hn))
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hconj : conj w = w⁻¹ := (inv_eq_conj hw).symm
  rw [eval_eq_sum_range' hdeg, zpow_natCast, map_sum, Finset.mul_sum,
    ← Finset.sum_range_reflect _ (m + 1)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [add_tsub_cancel_right, Nat.add_sub_cancel_left, hp' j i (by push_cast; ring)]
  simp [hconj, pow_add]
  field_simp

/-! ### Solutions on the closed disc -/

variable {u : ℂ → ℂ}

/-- Under the boundary condition, the Fourier coefficients of the boundary values satisfy
`bₘ = conj b_{-(k + m)}` in the normalization `bₘ = ∫ e^{imθ} u(e^{iθ}) dθ`. -/
private theorem integral_zpow_mul_eq_conj
    (hb : ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w)) (m : ℤ) :
    ∫ θ in 0..2 * π, circleMap 0 1 θ ^ m * u (circleMap 0 1 θ) =
      conj (∫ θ in 0..2 * π, circleMap 0 1 θ ^ (-(k + m)) * u (circleMap 0 1 θ)) := by
  rw [← intervalIntegral.intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hz : circleMap 0 1 θ ∈ sphere (0 : ℂ) 1 := circleMap_mem_sphere 0 zero_le_one θ
  have hz0 : circleMap 0 1 θ ≠ 0 := circleMap_ne_center one_ne_zero
  have hconj : conj (circleMap 0 1 θ) = (circleMap 0 1 θ)⁻¹ :=
    (inv_eq_conj (by simp)).symm
  conv_lhs => rw [hb _ hz]
  simp [hconj, zpow_add₀ hz0, zpow_neg]
  ring

/-- A function holomorphic on the open unit disc, continuous on its closure, and satisfying
`u w = w ^ k * conj (u w)` on the unit circle agrees on the closed disc with a
conjugate-reciprocal polynomial of degree at most `k`, namely its Taylor polynomial. -/
theorem _root_.DiffContOnCl.exists_mem_conjReciprocalPolynomials_eqOn
    (hu : DiffContOnCl ℂ u (ball 0 1)) (hb : ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w)) :
    ∃ p ∈ conjReciprocalPolynomials k, EqOn u (fun z => p.eval z) (closedBall 0 1) := by
  -- The Taylor coefficients `aₙ` satisfy `aₙ = conj a_{k-n}`, with `aₙ = 0` for `n > k`.
  have ha : ∀ n : ℕ, (cauchyPowerSeries u 0 1).coeff n = (2 * π : ℂ)⁻¹ *
      conj (∫ θ in 0..2 * π, circleMap 0 1 θ ^ ((n : ℤ) - k) * u (circleMap 0 1 θ)) :=
    fun n => by
      have hexp : -(k + -(n : ℤ)) = n - k := by ring
      simp only [coeff_cauchyPowerSeries u 0 one_ne_zero, smul_eq_mul]
      rw [integral_zpow_mul_eq_conj hb, hexp]
  have hvan : ∀ n : ℕ, k < n → (cauchyPowerSeries u 0 1).coeff n = 0 := fun n hn => by
    have h := hu.intervalIntegral_circleMap_zpow_smul_eq_zero one_pos (m := n - k) (by omega)
    simp only [smul_eq_mul] at h
    rw [ha, h, map_zero, mul_zero]
  have hsym : ∀ i j : ℕ, (i + j : ℤ) = k →
      (cauchyPowerSeries u 0 1).coeff i = conj ((cauchyPowerSeries u 0 1).coeff j) :=
    fun i j hij => by
      have hexp : (i : ℤ) - k = -(j : ℤ) := by omega
      rw [ha, coeff_cauchyPowerSeries u 0 one_ne_zero, hexp]
      simp only [smul_eq_mul, map_mul, map_inv₀, conj_ofReal, map_ofNat]
  -- The Taylor polynomial of degree `k` has all the Taylor coefficients, as `aₙ = 0` for `n > k`.
  set p : ℂ[X] := ofFn (k + 1).toNat fun j => (cauchyPowerSeries u 0 1).coeff j
  have hpa : ∀ n, p.coeff n = (cauchyPowerSeries u 0 1).coeff n := fun n => by
    by_cases hn : n < (k + 1).toNat
    · exact ofFn_coeff_eq_val_of_lt _ hn
    · rw [ofFn_coeff_eq_zero_of_ge _ (not_lt.mp hn), hvan n (by omega)]
  refine ⟨p, mem_conjReciprocalPolynomials_iff.mpr ⟨fun n hn => by rw [hpa, hvan n hn],
    fun i j hij => by rw [hpa, hpa, hsym i j hij]⟩, ?_⟩
  -- On the open disc `u` is the sum of its Taylor series, which is finite.
  have hball : EqOn u (fun z => p.eval z) (ball 0 1) := by
    intro z hz
    have hs := (hu.hasFPowerSeriesOnBall (R := 1) one_pos).hasSum
      (y := z) (by simpa [← ENNReal.ofReal_one, edist_dist] using hz)
    simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, zero_add, smul_eq_mul,
      NNReal.coe_one] at hs
    rw [hs.unique (hasSum_sum_of_ne_finset_zero (s := Finset.range (p.natDegree + 1)) _)]
    · beta_reduce
      rw [eval_eq_sum_range]
      exact Finset.sum_congr rfl fun n _ => by rw [hpa, mul_comm]
    · intro n hn
      rw [← hpa, coeff_eq_zero_of_natDegree_lt (by simpa using hn), mul_zero]
  exact hball.of_subset_closure hu.continuousOn_ball p.differentiable.continuous.continuousOn
    ball_subset_closedBall (by rw [closure_ball (0 : ℂ) one_ne_zero])

/-! ### The Cauchy–Riemann kernel on the unit disc -/

/-- The kernel of the Cauchy–Riemann operator `∂/∂(conj z)` on the closed unit disc with
boundary values on the rotating line `w ^ (k / 2) ℝ`: the functions `g` on the closed unit disc
that are restrictions of functions `u : ℂ → ℂ` holomorphic on the open unit disc and continuous on
its closure, with `u w = w ^ k * conj (u w)` for `‖w‖ = 1`. The boundary loop of lines has Maslov
index `k`. Two solutions are equal exactly when they agree at every point of the closed disc
(`TauCeti.unitDiscCauchyRiemannKernel.ext`). -/
def unitDiscCauchyRiemannKernel (k : ℤ) : Submodule ℝ (closedBall (0 : ℂ) 1 → ℂ) where
  carrier := {g | ∃ u : ℂ → ℂ, DiffContOnCl ℂ u (ball 0 1) ∧
    (∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w)) ∧ (closedBall 0 1).domRestrict u = g}
  add_mem' := by
    rintro _ _ ⟨u, hu, hu', rfl⟩ ⟨v, hv, hv', rfl⟩
    refine ⟨u + v, hu.add hv, fun w hw => ?_, rfl⟩
    rw [Pi.add_apply, map_add, mul_add, ← hu' w hw, ← hv' w hw]
  zero_mem' := ⟨0, diffContOnCl_const, fun w _ => by simp, rfl⟩
  smul_mem' := by
    rintro c _ ⟨u, hu, hu', rfl⟩
    refine ⟨c • u, hu.const_smul c, fun w hw => ?_, rfl⟩
    rw [Pi.smul_apply, real_smul, map_mul, conj_ofReal, mul_left_comm, ← hu' w hw]

variable {g : closedBall (0 : ℂ) 1 → ℂ}

/-- Membership in `unitDiscCauchyRiemannKernel k`, unfolded. -/
@[simp]
theorem mem_unitDiscCauchyRiemannKernel_iff :
    g ∈ unitDiscCauchyRiemannKernel k ↔ ∃ u : ℂ → ℂ, DiffContOnCl ℂ u (ball 0 1) ∧
      (∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w)) ∧ (closedBall 0 1).domRestrict u = g :=
  Iff.rfl

/-- Elements of `unitDiscCauchyRiemannKernel k` agreeing at every point of the closed disc are
equal. -/
@[ext]
theorem unitDiscCauchyRiemannKernel.ext {f g : unitDiscCauchyRiemannKernel k}
    (h : ∀ z, (f : closedBall (0 : ℂ) 1 → ℂ) z = (g : closedBall (0 : ℂ) 1 → ℂ) z) : f = g :=
  Subtype.ext (_root_.funext h)

/-- The solutions of the Cauchy–Riemann equation on the unit disc with boundary values on the line
`w ^ (k / 2) ℝ` are exactly the conjugate-reciprocal polynomials of degree at most `k`, evaluated
on the closed disc. -/
theorem mem_unitDiscCauchyRiemannKernel_iff_exists_eval :
    g ∈ unitDiscCauchyRiemannKernel k ↔
      ∃ p ∈ conjReciprocalPolynomials k, (fun z : closedBall (0 : ℂ) 1 => p.eval (z : ℂ)) = g := by
  refine ⟨?_, ?_⟩
  · rintro ⟨u, hu, hb, rfl⟩
    obtain ⟨p, hp, h⟩ := hu.exists_mem_conjReciprocalPolynomials_eqOn hb
    exact ⟨p, hp, funext fun z => (h z.2).symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨fun z => p.eval z, p.differentiable.diffContOnCl,
      fun w hw => eval_eq_zpow_mul_conj_eval hp (by simpa using hw), rfl⟩

private theorem unitDiscCauchyRiemannKernel_eq_map :
    unitDiscCauchyRiemannKernel k =
      (conjReciprocalPolynomials k).map ((evalOn (closedBall (0 : ℂ) 1)).restrictScalars ℝ) := by
  ext g
  simp only [Submodule.mem_map, mem_unitDiscCauchyRiemannKernel_iff_exists_eval, funext_iff,
    LinearMap.coe_restrictScalars, evalOn_apply]

/-- For a boundary condition of negative Maslov index, the only solution is zero. -/
theorem unitDiscCauchyRiemannKernel_eq_bot (hk : k < 0) : unitDiscCauchyRiemannKernel k = ⊥ := by
  rw [unitDiscCauchyRiemannKernel_eq_map, conjReciprocalPolynomials_eq_bot hk, Submodule.map_bot]

/-- The solutions of the Cauchy–Riemann equation on the unit disc with boundary values on the line
`w ^ (k / 2) ℝ` form a finite-dimensional real vector space. -/
instance finiteDimensional_unitDiscCauchyRiemannKernel (k : ℤ) :
    FiniteDimensional ℝ (unitDiscCauchyRiemannKernel k) := by
  rw [unitDiscCauchyRiemannKernel_eq_map]
  infer_instance

/-- The solutions of the Cauchy–Riemann equation on the unit disc with boundary values on the line
`w ^ (k / 2) ℝ` form a real vector space of dimension `k + 1` when `k ≥ -1`, and `0` when
`k < 0`. -/
theorem finrank_unitDiscCauchyRiemannKernel (k : ℤ) :
    finrank ℝ (unitDiscCauchyRiemannKernel k) = (k + 1).toNat := by
  rw [unitDiscCauchyRiemannKernel_eq_map, ← finrank_conjReciprocalPolynomials k]
  have hinj : Function.Injective (evalOn (closedBall (0 : ℂ) 1)) :=
    evalOn_injective (infinite_of_mem_nhds 0 (closedBall_mem_nhds 0 one_pos))
  exact (Submodule.equivMapOfInjective ((evalOn _).restrictScalars ℝ) hinj _).finrank_eq.symm

end TauCeti
