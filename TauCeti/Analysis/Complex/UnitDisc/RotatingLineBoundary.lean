/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.LinearAlgebra.TotallyReal.Finrank

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
(`TauCeti.mem_unitDiscCauchyRiemannKernel_iff_exists_eqOn`). Conversely every such polynomial is a
solution.
These polynomials form a real vector space of dimension `k + 1` for `k ≥ -1` and `0` for `k < 0`
(`TauCeti.finrank_conjReciprocalPolynomials`), so the space of solutions, read on the closed
disc, has real dimension `max (k + 1) 0` (`TauCeti.finrank_map_unitDiscCauchyRiemannKernel`).
For `k ≥ -1` this is `1 + k`, rank plus Maslov index, as the Riemann–Roch formula predicts once
the cokernel is known to vanish; the cokernel, which needs Sobolev completions, is not treated
here.

## Main definitions

* `TauCeti.conjReciprocalPolynomials k`: the real subspace of complex polynomials `p` with
  `p.coeff n = 0` for `n > k` and `p.coeff i = conj (p.coeff j)` whenever `i + j = k`.
* `TauCeti.unitDiscCauchyRiemannKernel k`: the real subspace of functions `u : ℂ → ℂ` that are
  holomorphic on the open unit disc, continuous on its closure, and satisfy
  `u w = w ^ k * conj (u w)` on the unit circle.

## Main results

* `TauCeti.mem_unitDiscCauchyRiemannKernel_iff_exists_eqOn`: `u` is a solution exactly when it
  agrees on the closed disc with a conjugate-reciprocal polynomial of degree at most `k`.
* `TauCeti.eqOn_zero_of_mem_unitDiscCauchyRiemannKernel`: for `k < 0` the only solution is zero.
* `TauCeti.finrank_conjReciprocalPolynomials`: the conjugate-reciprocal polynomials of degree at
  most `k` form a real vector space of dimension `(k + 1).toNat`.
* `TauCeti.finrank_map_unitDiscCauchyRiemannKernel`: the solutions, restricted to the closed
  disc, form a real vector space of dimension `(k + 1).toNat`.

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

/-! ### Conjugate-reciprocal polynomials -/

/-- The *conjugate-reciprocal* complex polynomials of degree at most `k`: those whose
coefficients vanish above `k` and satisfy `aᵢ = conj aⱼ` whenever `i + j = k`. For `k < 0` only
the zero polynomial qualifies. They form a real, not a complex, vector space. -/
def conjReciprocalPolynomials (k : ℤ) : Submodule ℝ ℂ[X] where
  carrier := {p | (∀ n : ℕ, k < n → p.coeff n = 0) ∧
    ∀ i j : ℕ, (i + j : ℤ) = k → p.coeff i = conj (p.coeff j)}
  add_mem' := by
    rintro p q ⟨hp, hp'⟩ ⟨hq, hq'⟩
    exact ⟨fun n hn => by simp [hp n hn, hq n hn], fun i j h => by simp [hp' i j h, hq' i j h]⟩
  zero_mem' := by simp
  smul_mem' := by
    rintro c p ⟨hp, hp'⟩
    exact ⟨fun n hn => by simp [hp n hn], fun i j h => by simp [hp' i j h, real_smul]⟩

variable {k : ℤ} {p : ℂ[X]}

/-- Membership in `conjReciprocalPolynomials k`, unfolded. -/
@[simp]
theorem mem_conjReciprocalPolynomials_iff :
    p ∈ conjReciprocalPolynomials k ↔ (∀ n : ℕ, k < n → p.coeff n = 0) ∧
      ∀ i j : ℕ, (i + j : ℤ) = k → p.coeff i = conj (p.coeff j) :=
  Iff.rfl

/-- The real subspace of `Fin N → ℂ` of vectors `a` with `a (rev j) = conj (a j)`: the
coefficient vectors of conjugate-reciprocal polynomials of degree less than `N`. -/
private def revConjFixed (N : ℕ) : Submodule ℝ (Fin N → ℂ) where
  carrier := {a | ∀ j, a (Fin.rev j) = conj (a j)}
  add_mem' := by
    intro a b ha hb j
    simp [ha j, hb j]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha j
    simp [ha j, real_smul]

/-- The vectors fixed by the conjugate-linear involution `a ↦ conj ∘ a ∘ rev` form a maximal
totally real subspace for multiplication by `i`. -/
private theorem isMaximalTotallyReal_revConjFixed (N : ℕ) :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ (Fin N → ℂ) I).restrictScalars ℝ)
      (revConjFixed N) := by
  rw [isMaximalTotallyReal_iff, isCompl_iff]
  constructor
  · -- A vector `a = i b` with `a` and `b` both fixed satisfies `b ∘ rev = -(b ∘ rev)`.
    rw [Submodule.disjoint_def]
    rintro a ha ⟨b, hb, rfl⟩
    have hb0 : ∀ j, b (Fin.rev j) = 0 := by
      intro j
      have h := ha j
      simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, Pi.smul_apply,
        smul_eq_mul, map_mul, conj_I, ← hb j] at h
      have h2 : 2 * I * b (Fin.rev j) = 0 := by linear_combination h
      simpa [I_ne_zero] using h2
    funext j
    simpa using hb0 (Fin.rev j)
  · -- Every vector splits as `(a + σ a) / 2 + i ((a - σ a) / (2 i))` with `σ a = conj ∘ a ∘ rev`.
    rw [codisjoint_iff, eq_top_iff]
    intro a _
    refine Submodule.mem_sup.mpr ⟨fun j => (a j + conj (a (Fin.rev j))) / 2, ?_,
      I • fun j => (a j - conj (a (Fin.rev j))) / (2 * I), ⟨_, ?_, rfl⟩, ?_⟩
    · intro j
      simp [add_comm, map_ofNat]
    · intro j
      simp only [Fin.rev_rev, map_div₀, map_sub, conj_conj, map_mul, conj_I, map_ofNat]
      field_simp
      ring
    · funext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring

private theorem finrank_revConjFixed (N : ℕ) : finrank ℝ (revConjFixed N) = N := by
  have h := (isMaximalTotallyReal_revConjFixed N).two_mul_finrank_eq fun a b hab => by
    simp only [LinearMap.domRestrict_apply, LinearMap.restrictScalars_apply,
      LinearMap.lsmul_apply] at hab
    exact Subtype.ext (smul_right_injective (Fin N → ℂ) I_ne_zero hab)
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Complex.finrank_real_complex, smul_eq_mul] at h
  omega

private theorem conjReciprocalPolynomials_eq_map :
    conjReciprocalPolynomials k =
      (revConjFixed (k + 1).toNat).map ((ofFn (k + 1).toNat).restrictScalars ℝ) := by
  ext p
  simp only [mem_conjReciprocalPolynomials_iff, Submodule.mem_map,
    LinearMap.restrictScalars_apply]
  constructor
  · rintro ⟨hp, hp'⟩
    refine ⟨fun j => p.coeff j, fun j => hp' _ _ ?_, ?_⟩
    · have := j.isLt
      simp only [Fin.val_rev]
      omega
    · ext n
      by_cases hn : n < (k + 1).toNat
      · rw [ofFn_coeff_eq_val_of_lt _ hn]
      · rw [ofFn_coeff_eq_zero_of_ge _ (not_lt.mp hn), hp n (by omega)]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨fun n hn => ofFn_coeff_eq_zero_of_ge _ (by omega), fun i j hij => ?_⟩
    have hi : i < (k + 1).toNat := by omega
    have hj : j < (k + 1).toNat := by omega
    rw [ofFn_coeff_eq_val_of_lt _ hi, ofFn_coeff_eq_val_of_lt _ hj, ← ha ⟨j, hj⟩]
    congr 1
    ext
    simp only [Fin.val_rev]
    omega

/-- The conjugate-reciprocal polynomials of degree at most `k` form a real vector space of
dimension `k + 1` when `k ≥ -1`, and `0` when `k < 0`. -/
theorem finrank_conjReciprocalPolynomials (k : ℤ) :
    finrank ℝ (conjReciprocalPolynomials k) = (k + 1).toNat := by
  rw [conjReciprocalPolynomials_eq_map]
  exact (Submodule.equivMapOfInjective ((ofFn (k + 1).toNat).restrictScalars ℝ)
    (injective_ofFn (R := ℂ) _) _).finrank_eq.symm.trans (finrank_revConjFixed _)

/-- A conjugate-reciprocal polynomial of degree at most `k` takes values on the line
`w ^ (k / 2) ℝ` at each point `w` of the unit circle. -/
theorem eval_eq_zpow_mul_conj_eval (hp : p ∈ conjReciprocalPolynomials k) {w : ℂ}
    (hw : ‖w‖ = 1) : p.eval w = w ^ k * conj (p.eval w) := by
  obtain ⟨hp, hp'⟩ := hp
  rcases lt_or_ge k 0 with hk | hk
  · -- For `k < 0` every coefficient vanishes.
    have : p = 0 := ext fun n => by simpa using hp n (by omega)
    simp [this]
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m := ⟨k.toNat, by omega⟩
  have hdeg : p.natDegree < m + 1 :=
    Nat.lt_succ_of_le (natDegree_le_iff_coeff_eq_zero.mpr fun n hn => hp n (by exact_mod_cast hn))
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hconj : conj w = w⁻¹ := (inv_eq_conj hw).symm
  rw [eval_eq_sum_range' hdeg, zpow_natCast, map_sum, Finset.mul_sum,
    ← Finset.sum_range_reflect _ (m + 1)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [map_mul, map_pow, hconj, add_tsub_cancel_right,
    hp' (m - i) (m - (m - i)) (by push_cast [Nat.sub_sub_self hi, Nat.cast_sub hi]; ring),
    Nat.sub_sub_self hi]
  conv_rhs => rw [← Nat.sub_add_cancel hi, pow_add]
  rw [inv_pow]
  field_simp

/-! ### The Cauchy–Riemann kernel on the unit disc -/

/-- The kernel of the Cauchy–Riemann operator `∂/∂(conj z)` on the closed unit disc with
boundary values on the rotating line `w ^ (k / 2) ℝ`: the functions `u : ℂ → ℂ` that are
holomorphic on the open unit disc, continuous on its closure, and satisfy
`u w = w ^ k * conj (u w)` for `‖w‖ = 1`. The boundary loop of lines has Maslov index `k`.
Membership only depends on the values of `u` on the closed disc. -/
def unitDiscCauchyRiemannKernel (k : ℤ) : Submodule ℝ (ℂ → ℂ) where
  carrier := {u | DiffContOnCl ℂ u (ball 0 1) ∧
    ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w)}
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    refine ⟨hu.add hv, fun w hw => ?_⟩
    rw [Pi.add_apply, map_add, mul_add, ← hu' w hw, ← hv' w hw]
  zero_mem' := ⟨diffContOnCl_const, fun w _ => by simp⟩
  smul_mem' := by
    rintro c u ⟨hu, hu'⟩
    refine ⟨hu.const_smul c, fun w hw => ?_⟩
    rw [Pi.smul_apply, real_smul, map_mul, conj_ofReal, mul_left_comm, ← hu' w hw]

variable {u : ℂ → ℂ}

/-- Membership in `unitDiscCauchyRiemannKernel k`, unfolded. -/
@[simp]
theorem mem_unitDiscCauchyRiemannKernel_iff :
    u ∈ unitDiscCauchyRiemannKernel k ↔ DiffContOnCl ℂ u (ball 0 1) ∧
      ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w) :=
  Iff.rfl

/-- A circle integral over the unit circle against `z ^ (m - 1)`, in the angle variable. -/
private theorem circleIntegral_zpow_sub_one_mul (u : ℂ → ℂ) (m : ℤ) :
    (∮ z in C(0, 1), z ^ (m - 1) * u z) =
      I * ∫ θ in 0..2 * π, circleMap 0 1 θ ^ m * u (circleMap 0 1 θ) := by
  rw [circleIntegral, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hz : circleMap 0 1 θ ≠ 0 := circleMap_ne_center one_ne_zero
  simp only [deriv_circleMap, smul_eq_mul, zpow_sub_one₀ hz]
  field_simp

/-- The Fourier coefficients of the boundary values of a function holomorphic on the open disc
and continuous on its closure vanish in negative degrees. -/
private theorem integral_zpow_mul_eq_zero (hu : DiffContOnCl ℂ u (ball 0 1)) {m : ℤ}
    (hm : 0 < m) : ∫ θ in 0..2 * π, circleMap 0 1 θ ^ m * u (circleMap 0 1 θ) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨(m - 1).toNat, by omega⟩
  have hcont : ContinuousOn u (closedBall 0 1) := by
    simpa [closure_ball (0 : ℂ) one_ne_zero] using hu.continuousOn
  have h : (∮ z in C(0, 1), z ^ n * u z) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable zero_le_one countable_empty
      ((continuous_pow n).continuousOn.mul hcont) fun z hz =>
        (differentiableAt_pow n).mul (hu.differentiableAt isOpen_ball hz.1)
  have h' := circleIntegral_zpow_sub_one_mul u (n + 1)
  simp only [add_sub_cancel_right, zpow_natCast] at h'
  rw [h] at h'
  exact (mul_eq_zero.mp h'.symm).resolve_left I_ne_zero

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
  rw [map_mul, map_zpow₀, hconj, inv_zpow', neg_neg, zpow_add₀ hz0]
  ring

/-- The Taylor coefficients at `0` of a function holomorphic on the unit disc are the Fourier
coefficients of its boundary values. -/
private theorem coeff_cauchyPowerSeries (u : ℂ → ℂ) (n : ℕ) :
    (cauchyPowerSeries u 0 1).coeff n =
      (2 * π : ℂ)⁻¹ * ∫ θ in 0..2 * π, circleMap 0 1 θ ^ (-(n : ℤ)) * u (circleMap 0 1 θ) := by
  have h := (cauchyPowerSeries u 0 1).apply_eq_pow_smul_coeff (n := n) (z := 1)
  rw [one_pow, one_smul] at h
  rw [← h, cauchyPowerSeries_apply,
    circleIntegral.integral_congr zero_le_one (g := fun z => z ^ (-(n : ℤ) - 1) * u z),
    circleIntegral_zpow_sub_one_mul]
  · simp only [smul_eq_mul]
    field_simp
  · intro z hz
    have hz0 : z ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨z, hz⟩
    simp only [sub_zero, smul_eq_mul, zpow_sub_one₀ hz0, zpow_neg, zpow_natCast, div_pow,
      one_pow]
    ring

/-- A solution agrees on the closed disc with a conjugate-reciprocal polynomial of degree at most
`k`, namely its Taylor polynomial. -/
theorem exists_mem_conjReciprocalPolynomials_eqOn (hu : u ∈ unitDiscCauchyRiemannKernel k) :
    ∃ p ∈ conjReciprocalPolynomials k, EqOn u (fun z => p.eval z) (closedBall 0 1) := by
  obtain ⟨hu, hb⟩ := hu
  -- The Taylor coefficients `aₙ` satisfy `aₙ = conj a_{k-n}`, with `aₙ = 0` for `n > k`.
  have ha : ∀ n : ℕ, (cauchyPowerSeries u 0 1).coeff n = (2 * π : ℂ)⁻¹ *
      conj (∫ θ in 0..2 * π, circleMap 0 1 θ ^ ((n : ℤ) - k) * u (circleMap 0 1 θ)) :=
    fun n => by
      rw [coeff_cauchyPowerSeries, integral_zpow_mul_eq_conj hb, show -(k + -(n : ℤ)) = n - k by
        ring]
  have hvan : ∀ n : ℕ, k < n → (cauchyPowerSeries u 0 1).coeff n = 0 := fun n hn => by
    rw [ha, integral_zpow_mul_eq_zero hu (by omega), map_zero, mul_zero]
  have hsym : ∀ i j : ℕ, (i + j : ℤ) = k →
      (cauchyPowerSeries u 0 1).coeff i = conj ((cauchyPowerSeries u 0 1).coeff j) :=
    fun i j hij => by
      rw [ha, coeff_cauchyPowerSeries, map_mul, map_inv₀, map_mul, conj_ofReal, map_ofNat,
        show (i : ℤ) - k = -(j : ℤ) by omega]
  -- The Taylor polynomial of degree `k` has all the Taylor coefficients, as `aₙ = 0` for `n > k`.
  set p : ℂ[X] := ofFn (k + 1).toNat fun j => (cauchyPowerSeries u 0 1).coeff j
  have hpa : ∀ n, p.coeff n = (cauchyPowerSeries u 0 1).coeff n := fun n => by
    by_cases hn : n < (k + 1).toNat
    · exact ofFn_coeff_eq_val_of_lt _ hn
    · rw [ofFn_coeff_eq_zero_of_ge _ (not_lt.mp hn), hvan n (by omega)]
  refine ⟨p, ⟨fun n hn => by rw [hpa, hvan n hn], fun i j hij => by
    rw [hpa, hpa, hsym i j hij]⟩, ?_⟩
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
  refine hball.of_subset_closure ?_ p.differentiable.continuous.continuousOn ball_subset_closedBall
    (by rw [closure_ball (0 : ℂ) one_ne_zero])
  simpa [closure_ball (0 : ℂ) one_ne_zero] using hu.continuousOn

/-- A function agreeing on the closed disc with a conjugate-reciprocal polynomial of degree at
most `k` is a solution. -/
theorem mem_unitDiscCauchyRiemannKernel_of_eqOn (hp : p ∈ conjReciprocalPolynomials k)
    (h : EqOn u (fun z => p.eval z) (closedBall 0 1)) : u ∈ unitDiscCauchyRiemannKernel k := by
  refine ⟨⟨p.differentiable.differentiableOn.congr fun z hz => h (ball_subset_closedBall hz),
    p.differentiable.continuous.continuousOn.congr ?_⟩, fun w hw => ?_⟩
  · rw [closure_ball (0 : ℂ) one_ne_zero]
    exact h
  · rw [h (sphere_subset_closedBall hw)]
    exact eval_eq_zpow_mul_conj_eval hp (by simpa using hw)

/-- The solutions of the Cauchy–Riemann equation on the unit disc with boundary values on the line
`w ^ (k / 2) ℝ` are exactly the functions agreeing on the closed disc with a conjugate-reciprocal
polynomial of degree at most `k`. -/
theorem mem_unitDiscCauchyRiemannKernel_iff_exists_eqOn :
    u ∈ unitDiscCauchyRiemannKernel k ↔
      ∃ p ∈ conjReciprocalPolynomials k, EqOn u (fun z => p.eval z) (closedBall 0 1) :=
  ⟨exists_mem_conjReciprocalPolynomials_eqOn, fun ⟨_, hp, h⟩ =>
    mem_unitDiscCauchyRiemannKernel_of_eqOn hp h⟩

/-- For a boundary condition of negative Maslov index, the only solution is zero. -/
theorem eqOn_zero_of_mem_unitDiscCauchyRiemannKernel (hk : k < 0)
    (hu : u ∈ unitDiscCauchyRiemannKernel k) : EqOn u 0 (closedBall 0 1) := by
  obtain ⟨p, ⟨hp, -⟩, h⟩ := exists_mem_conjReciprocalPolynomials_eqOn hu
  have : p = 0 := ext fun n => by simpa using hp n (by omega)
  exact fun z hz => by simpa [this] using h hz

/-- The solutions of the Cauchy–Riemann equation on the unit disc with boundary values on the line
`w ^ (k / 2) ℝ`, read on the closed disc, form a real vector space of dimension `k + 1` when
`k ≥ -1`, and `0` when `k < 0`. -/
theorem finrank_map_unitDiscCauchyRiemannKernel (k : ℤ) :
    finrank ℝ ((unitDiscCauchyRiemannKernel k).map
      (LinearMap.funLeft ℝ ℂ ((↑) : closedBall (0 : ℂ) 1 → ℂ))) = (k + 1).toNat := by
  -- Evaluation of polynomials on the closed disc, an injective real-linear map.
  let ev : ℂ[X] →ₗ[ℝ] (closedBall (0 : ℂ) 1 → ℂ) :=
    LinearMap.pi fun z : closedBall (0 : ℂ) 1 => (leval (z : ℂ)).restrictScalars ℝ
  have hev : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    refine eq_zero_of_infinite_isRoot q
      ((infinite_of_mem_nhds (0 : ℂ) (closedBall_mem_nhds 0 one_pos)).mono fun z hz => ?_)
    simpa [ev] using congrFun hq ⟨z, hz⟩
  have hmap : (unitDiscCauchyRiemannKernel k).map
      (LinearMap.funLeft ℝ ℂ ((↑) : closedBall (0 : ℂ) 1 → ℂ)) =
      (conjReciprocalPolynomials k).map ev := by
    ext g
    simp only [Submodule.mem_map, mem_unitDiscCauchyRiemannKernel_iff_exists_eqOn]
    constructor
    · rintro ⟨u, ⟨p, hp, h⟩, rfl⟩
      exact ⟨p, hp, funext fun z => (h z.2).symm⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨fun z => p.eval z, ⟨p, hp, fun _ _ => rfl⟩, rfl⟩
  rw [hmap, ← finrank_conjReciprocalPolynomials k]
  exact (Submodule.equivMapOfInjective _ hev _).finrank_eq.symm

end TauCeti
