/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Sobolev.BesselPotential.Basic
import TauCeti.MeasureTheory.Integral.Asymptotics

/-!
# Sobolev regularity of rational functions of `1 + ‖P‖²`

Let `P` be a complex polynomial of degree `m` and let `φ = (1 + ‖P‖²)⁻¹`. For polynomials `A`, `B`
and `n : ℕ`, the function

`z ↦ φ(z) ^ n conj (A z) B z`

decays at infinity like `‖z‖ ^ (deg A + deg B - 2 m n)`. Its directional derivatives are again of
this form, with the decay improved by one power: differentiating `φ ^ n` gives
`-n φ ^ (n + 1) (conj P P' v + P conj P' conj v)`, and differentiating `A` or `B` lowers its
degree. So if `deg A + deg B + 2 ≤ 2 m n`, so that the function is square integrable on the plane,
every derivative is square integrable as well, and the real part of the function lies in the
Bessel-potential space `H^k(ℂ)` for every `k`
(`Polynomial.re_mem_realSobolevFunctions_of_add_two_le`).

In particular, for a nonconstant `P`, the defect `(1 + ‖P‖²)⁻¹` of the squared modulus
`‖P‖² / (1 + ‖P‖²)` from `1` (`Polynomial.inv_one_add_norm_eval_sq_mem_realSobolevFunctions`) and,
for every `P`, the density `‖P'‖² / (1 + ‖P‖²)²` of the pullback by `P` of the Fubini–Study area
form (`Polynomial.norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq_mem_realSobolevFunctions`)
lie in every `H^k(ℂ)`. These are the coefficients of Taubes's reduced vortex equation for the zero
divisor of `P`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace Polynomial

open ComplexConjugate Asymptotics Filter MeasureTheory TemperedDistribution Topology
open scoped ContDiff

variable {P : ℂ[X]}

/-- The function `φ ^ n conj A B`, with `φ = (1 + ‖P‖²)⁻¹`. -/
private def weightTerm (P : ℂ[X]) (n : ℕ) (A B : ℂ[X]) (z : ℂ) : ℂ :=
  (((1 + ‖P.eval z‖ ^ 2)⁻¹ ^ n : ℝ) : ℂ) * (conj (A.eval z) * B.eval z)

private theorem contDiff_weightTerm (P : ℂ[X]) (n : ℕ) (A B : ℂ[X]) :
    ContDiff ℝ ∞ (weightTerm P n A B) := by
  have heval (A : ℂ[X]) : ContDiff ℝ ∞ fun z ↦ A.eval z := by
    simpa using (A.contDiff_aeval (𝕜 := ℂ) ∞).restrict_scalars ℝ
  have hN : ContDiff ℝ ∞ fun z ↦ ((1 + ‖P.eval z‖ ^ 2)⁻¹ ^ n : ℝ) :=
    ((contDiff_const.add ((contDiff_norm_sq ℝ).comp (heval P))).inv
      fun z ↦ (by positivity : (0 : ℝ) < 1 + ‖P.eval z‖ ^ 2).ne').pow n
  exact (Complex.ofRealCLM.contDiff.comp hN).mul
    ((Complex.conjCLE.contDiff.comp (heval A)).mul (heval B))

/-- The derivative of `φ ^ n conj A B` along the line `t ↦ z + t v` is again a sum of four
functions of the same form. -/
private theorem hasDerivAt_weightTerm (P : ℂ[X]) (n : ℕ) (A B : ℂ[X]) (z v : ℂ) :
    HasDerivAt (fun t : ℝ ↦ weightTerm P n A B (z + t • v))
      (weightTerm P (n + 1) (P * A) (C (-(n : ℂ) * v) * (derivative P * B)) z +
        weightTerm P (n + 1) (C (-(n : ℂ) * v) * (derivative P * A)) (P * B) z +
        weightTerm P n (C v * derivative A) B z + weightTerm P n A (C v * derivative B) z) 0 := by
  have hγ : HasDerivAt (fun t : ℝ ↦ z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h0 : z + (0 : ℝ) • v = z := by simp
  have hpoly (Q : ℂ[X]) :
      HasDerivAt (fun t : ℝ ↦ Q.eval (z + t • v)) (Q.derivative.eval z * v) 0 := by
    have h := (Q.hasDerivAt (z + (0 : ℝ) • v)).comp (0 : ℝ) hγ
    rw [h0] at h
    exact h
  have hN : HasDerivAt (fun t : ℝ ↦ 1 + ‖P.eval (z + t • v)‖ ^ 2)
      (2 * inner ℝ (P.eval z) (P.derivative.eval z * v)) 0 := by
    have h := (hpoly P).norm_sq.const_add 1
    rwa [h0] at h
  have hNz : 1 + ‖P.eval z‖ ^ 2 ≠ 0 := by positivity
  have hφ := ((hN.inv (by rwa [h0])).pow n).ofReal_comp
  have hA := (hpoly A).star
  have hB := hpoly B
  have h := hφ.mul (hA.mul hB)
  simp only [h0] at h
  convert h using 1
  · ext t
    simp [weightTerm]
  -- The product rule, with `2 ⟪p, p' v⟫ = conj p p' v + p conj (p' v)` and
  -- `n φ ^ (n - 1) / N ^ 2 = n φ ^ (n + 1)` for `φ = N⁻¹`.
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, zero_smul, add_zero, weightTerm, eval_mul,
    eval_C, eval_neg, eval_natCast, map_mul, map_neg, map_natCast, Complex.inner,
    Complex.star_def]
  push_cast
  rw [Complex.re_eq_add_conj]
  simp only [map_mul, Complex.conj_conj]
  obtain _ | k := n
  · simp only [CharP.cast_eq_zero, pow_zero]
    ring
  · simp only [div_eq_mul_inv, ← inv_pow, Nat.add_sub_cancel]
    ring

/-- The directional derivatives of the real part of `φ ^ n conj A B`. -/
private theorem fderiv_re_weightTerm (P : ℂ[X]) (n : ℕ) (A B : ℂ[X]) (z v : ℂ) :
    fderiv ℝ (fun z ↦ (weightTerm P n A B z).re) z v =
      (weightTerm P (n + 1) (P * A) (C (-(n : ℂ) * v) * (derivative P * B)) z).re +
        (weightTerm P (n + 1) (C (-(n : ℂ) * v) * (derivative P * A)) (P * B) z).re +
        (weightTerm P n (C v * derivative A) B z).re +
        (weightTerm P n A (C v * derivative B) z).re := by
  have hD : DifferentiableAt ℝ (weightTerm P n A B) z :=
    (contDiff_weightTerm P n A B).differentiable (by simp) z
  have hre := (Complex.reCLM.hasFDerivAt.comp z hD.hasFDerivAt).fderiv
  have hline := (hD.hasFDerivAt.hasLineDerivAt v).unique (hasDerivAt_weightTerm P n A B z v)
  simp only [Function.comp_def, Complex.reCLM_apply] at hre
  rw [hre, ContinuousLinearMap.comp_apply, Complex.reCLM_apply, hline]
  simp only [Complex.add_re]

/-- The decay bound `‖φ ^ n conj A B‖ (1 + ‖z‖)² ≤ K` at infinity when
`deg A + deg B + 2 ≤ 2 m n`. -/
private theorem exists_eventually_norm_weightTerm_mul_le {n : ℕ} {A B : ℂ[X]}
    (h : A.natDegree + B.natDegree + 2 ≤ 2 * P.natDegree * n) :
    ∃ K : ℝ, ∀ᶠ z : ℂ in cocompact ℂ, ‖weightTerm P n A B z‖ * (1 + ‖z‖) ^ 2 ≤ K := by
  have hm : 0 < P.natDegree := by
    rcases Nat.eq_zero_or_pos P.natDegree with h0 | h0
    · rw [h0] at h; omega
    · exact h0
  have hP : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hm
  have hlow : (fun z : ℂ ↦ z ^ P.natDegree) =O[cocompact ℂ] P.eval := by
    have he := (Polynomial.isEquivalent_cobounded_leading_monomial (P := P)).symm.isBigO
    rw [Metric.cobounded_eq_cocompact] at he
    exact (isBigO_self_const_mul (Polynomial.leadingCoeff_ne_zero.mpr hP) _ _).trans he
  have hup (Q : ℂ[X]) : Q.eval =O[cocompact ℂ] fun z : ℂ ↦ z ^ Q.natDegree := by
    have h := Polynomial.isBigO_cobounded_pow_natDegree Q
    rwa [Metric.cobounded_eq_cocompact] at h
  obtain ⟨c₁, hc₁⟩ := hlow.bound
  obtain ⟨c₂, hc₂⟩ := (hup A).bound
  obtain ⟨c₃, hc₃⟩ := (hup B).bound
  set c := max (max c₁ c₂) (max c₃ 1)
  refine ⟨4 * c ^ (2 * n + 2), ?_⟩
  filter_upwards [hc₁, hc₂, hc₃, tendsto_norm_cocompact_atTop.eventually_ge_atTop 1]
    with z h₁ h₂ h₃ hz
  rw [norm_pow] at h₁ h₂ h₃
  set r := ‖z‖
  set N := 1 + ‖P.eval z‖ ^ 2
  have hN : 0 < N := by positivity
  have hpz : r ^ P.natDegree ≤ c * ‖P.eval z‖ :=
    h₁.trans (by gcongr; exact (le_max_left _ _).trans (le_max_left _ _))
  have haz : ‖A.eval z‖ ≤ c * r ^ A.natDegree :=
    h₂.trans (by gcongr; exact (le_max_right _ _).trans (le_max_left _ _))
  have hbz : ‖B.eval z‖ ≤ c * r ^ B.natDegree :=
    h₃.trans (by gcongr; exact (le_max_left _ _).trans (le_max_right _ _))
  -- `r ^ (2 m n) ≤ c ^ (2 n) N ^ n`, from `r ^ m ≤ c ‖P z‖`.
  have hpow : r ^ (2 * P.natDegree * n) ≤ c ^ (2 * n) * N ^ n := by
    have hsq : (r ^ P.natDegree) ^ 2 ≤ c ^ 2 * N := by
      calc (r ^ P.natDegree) ^ 2 ≤ (c * ‖P.eval z‖) ^ 2 := by gcongr
        _ = c ^ 2 * ‖P.eval z‖ ^ 2 := by ring
        _ ≤ c ^ 2 * N := by gcongr; simp [N]
    calc r ^ (2 * P.natDegree * n) = ((r ^ P.natDegree) ^ 2) ^ n := by
          rw [← pow_mul, ← pow_mul]; congr 1; ring
      _ ≤ (c ^ 2 * N) ^ n := by gcongr
      _ = c ^ (2 * n) * N ^ n := by rw [mul_pow, ← pow_mul]
  have hnorm : ‖weightTerm P n A B z‖ * N ^ n = ‖A.eval z‖ * ‖B.eval z‖ := by
    have habs : |1 + ‖P.eval z‖ ^ 2| = N := abs_of_pos hN
    simp only [weightTerm, norm_mul, Complex.norm_real, Complex.norm_conj, norm_pow,
      Real.norm_eq_abs, abs_inv, habs]
    rw [inv_pow, mul_right_comm, inv_mul_cancel₀ (pow_ne_zero n hN.ne'), one_mul]
  -- `‖w‖ r ^ (2 m n) ≤ c ^ (2 n + 2) r ^ (deg A + deg B)`.
  have hmain : ‖weightTerm P n A B z‖ * r ^ (2 * P.natDegree * n) ≤
      c ^ (2 * n + 2) * r ^ (A.natDegree + B.natDegree) := by
    calc ‖weightTerm P n A B z‖ * r ^ (2 * P.natDegree * n)
        ≤ ‖weightTerm P n A B z‖ * (c ^ (2 * n) * N ^ n) := by gcongr
      _ = c ^ (2 * n) * (‖A.eval z‖ * ‖B.eval z‖) := by rw [← hnorm]; ring
      _ ≤ c ^ (2 * n) * ((c * r ^ A.natDegree) * (c * r ^ B.natDegree)) := by gcongr
      _ = c ^ (2 * n + 2) * r ^ (A.natDegree + B.natDegree) := by ring
  have hr0 : 0 < r ^ (A.natDegree + B.natDegree) := by positivity
  have hrr : r ^ (A.natDegree + B.natDegree) * r ^ 2 ≤ r ^ (2 * P.natDegree * n) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hz h
  have hw2 : ‖weightTerm P n A B z‖ * r ^ 2 ≤ c ^ (2 * n + 2) := by
    refine le_of_mul_le_mul_right ?_ hr0
    calc ‖weightTerm P n A B z‖ * r ^ 2 * r ^ (A.natDegree + B.natDegree)
        = ‖weightTerm P n A B z‖ * (r ^ (A.natDegree + B.natDegree) * r ^ 2) := by ring
      _ ≤ ‖weightTerm P n A B z‖ * r ^ (2 * P.natDegree * n) := by gcongr
      _ ≤ c ^ (2 * n + 2) * r ^ (A.natDegree + B.natDegree) := hmain
  calc ‖weightTerm P n A B z‖ * (1 + r) ^ 2 ≤ ‖weightTerm P n A B z‖ * (4 * r ^ 2) := by
        gcongr; nlinarith
    _ = 4 * (‖weightTerm P n A B z‖ * r ^ 2) := by ring
    _ ≤ 4 * c ^ (2 * n + 2) := by gcongr

/-- The real part of `φ ^ n conj A B` is square integrable when `deg A + deg B + 2 ≤ 2 m n`. -/
private theorem memLp_re_weightTerm {n : ℕ} {A B : ℂ[X]}
    (h : A.natDegree + B.natDegree + 2 ≤ 2 * P.natDegree * n) :
    MemLp (fun z ↦ (weightTerm P n A B z).re) 2 := by
  have hcont : Continuous fun z ↦ (weightTerm P n A B z).re :=
    Complex.continuous_re.comp (contDiff_weightTerm P n A B).continuous
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  obtain ⟨K, hK⟩ := exists_eventually_norm_weightTerm_mul_le h
  refine (hcont.pow 2).locallyIntegrable.integrable_of_isBigO_one_add_norm_rpow_neg (r := 4)
    (by simp [Complex.finrank_real_complex]; norm_num) (IsBigO.of_bound (K ^ 2) ?_)
  filter_upwards [hK] with z hz
  have hre : |(weightTerm P n A B z).re| ≤ ‖weightTerm P n A B z‖ := Complex.abs_re_le_norm _
  rw [Pi.pow_apply, Real.norm_eq_abs, abs_pow, Real.norm_of_nonneg (by positivity),
    Real.rpow_neg (by positivity), Real.rpow_ofNat, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc |(weightTerm P n A B z).re| ^ 2 * (1 + ‖z‖) ^ 4
      ≤ ‖weightTerm P n A B z‖ ^ 2 * (1 + ‖z‖) ^ 4 := by gcongr
    _ = (‖weightTerm P n A B z‖ * (1 + ‖z‖) ^ 2) ^ 2 := by ring
    _ ≤ K ^ 2 := by gcongr

/-- **Rational functions of `1 + ‖P‖²` lie in every Sobolev space.** Let `P`, `A`, `B` be complex
polynomials and `n : ℕ` with `deg A + deg B + 2 ≤ 2 (deg P) n`. Then the real part of
`conj (A z) B z / (1 + ‖P z‖²) ^ n` lies in `H^k(ℂ)` for every `k : ℕ`. -/
theorem re_mem_realSobolevFunctions_of_add_two_le {n : ℕ} {A B : ℂ[X]}
    (h : A.natDegree + B.natDegree + 2 ≤ 2 * P.natDegree * n) (k : ℕ) :
    (fun z ↦ ((((1 + ‖P.eval z‖ ^ 2)⁻¹ ^ n : ℝ) : ℂ) * (conj (A.eval z) * B.eval z)).re) ∈
      realSobolevFunctions ℂ k 2 := by
  simp only [← weightTerm.eq_1]
  induction k generalizing n A B with
  | zero =>
    rw [Nat.cast_zero, mem_realSobolevFunctions_zero_iff]
    exact memLp_re_weightTerm h
  | succ k ih =>
    have hm : 0 < P.natDegree := by
      rcases Nat.eq_zero_or_pos P.natDegree with h0 | h0
      · rw [h0] at h; omega
      · exact h0
    have hdP := natDegree_derivative_le P
    have hdA := natDegree_derivative_le A
    have hdB := natDegree_derivative_le B
    rw [Nat.cast_succ]
    refine mem_realSobolevFunctions_add_one_of_fderiv_apply (by norm_num) (by norm_num)
      ((Complex.reCLM.contDiff.comp (contDiff_weightTerm P n A B)).of_le (by simp)) (ih h)
      fun v ↦ ?_
    simp_rw [fderiv_re_weightTerm]
    refine add_mem (add_mem (add_mem (ih ?_) (ih ?_)) (ih ?_)) (ih ?_)
    · have := natDegree_mul_le (p := P) (q := A)
      have := natDegree_C_mul_le (-(n : ℂ) * v) (derivative P * B)
      have := natDegree_mul_le (p := derivative P) (q := B)
      rw [mul_add_one]
      generalize 2 * P.natDegree * n = M at h ⊢
      omega
    · have := natDegree_mul_le (p := P) (q := B)
      have := natDegree_C_mul_le (-(n : ℂ) * v) (derivative P * A)
      have := natDegree_mul_le (p := derivative P) (q := A)
      rw [mul_add_one]
      generalize 2 * P.natDegree * n = M at h ⊢
      omega
    · have := natDegree_C_mul_le v (derivative A)
      omega
    · have := natDegree_C_mul_le v (derivative B)
      omega

/-- For a nonconstant complex polynomial `P`, the function `(1 + ‖P‖²)⁻¹` lies in `H^k(ℂ)` for
every `k : ℕ`. -/
theorem inv_one_add_norm_eval_sq_mem_realSobolevFunctions (hm : 0 < P.natDegree) (k : ℕ) :
    (fun z ↦ (1 + ‖P.eval z‖ ^ 2)⁻¹) ∈ realSobolevFunctions ℂ k 2 := by
  have h := re_mem_realSobolevFunctions_of_add_two_le (P := P) (n := 1) (A := 1) (B := 1)
    (by simp; omega) k
  convert h using 2 with z
  simp only [eval_one, map_one, mul_one, pow_one, Complex.ofReal_re]

/-- For every complex polynomial `P`, the function `‖P'‖² / (1 + ‖P‖²)²` lies in `H^k(ℂ)` for
every `k : ℕ`. -/
theorem norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq_mem_realSobolevFunctions (P : ℂ[X])
    (k : ℕ) :
    (fun z ↦ ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) ∈
      realSobolevFunctions ℂ k 2 := by
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | hm
  · convert (realSobolevFunctions ℂ k 2).zero_mem using 1
    ext z
    simp [derivative_of_natDegree_zero h0]
  have hdP := natDegree_derivative_le P
  have h := re_mem_realSobolevFunctions_of_add_two_le (P := P) (n := 2) (A := derivative P)
    (B := derivative P) (by omega) k
  convert h using 2 with z
  simp only [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [div_eq_inv_mul, inv_pow]

end Polynomial
