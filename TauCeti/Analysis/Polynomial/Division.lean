/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Algebra.Polynomial.FieldDivision
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff

/-!
# Analytic dependence of polynomial division on coefficients

For bounded-degree polynomial families with analytic coefficients, division by a monic family
of fixed degree has analytic quotient and remainder coefficients. The dividend may drop degree.
For a nonmonic divisor, local constancy of its degree and nonvanishing at the center suffice.
In particular these results apply when forming squarefree quotients after recovering an
analytic monic gcd with the derivative.

Monic division commutes with coefficient homomorphisms. Applying it first to universal
polynomials expresses each output coefficient as a polynomial in the input coefficients.
Ordinary division follows by normalizing the divisor with its nonzero leading coefficient.
No completeness or finite-dimensionality assumption on the parameter space is needed.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapter 4 (polynomial division and squarefree reduction).
-/

public section

open Filter Polynomial Topology

namespace TauCeti

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- In a locally bounded-degree family, analyticity of the coefficients through the degree
bound implies analyticity of every coefficient, since higher coefficients vanish near the center. -/
theorem analyticAt_coeff_of_eventually_natDegree_le
    {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] {F : E → A[X]} {x₀ : E} {m : ℕ}
    (hF : ∀ i ≤ m, AnalyticAt 𝕜 (fun x ↦ (F x).coeff i) x₀)
    (hdegF : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ m) (k : ℕ) :
    AnalyticAt 𝕜 (fun x ↦ (F x).coeff k) x₀ := by
  by_cases hk : k ≤ m
  · exact hF k hk
  · apply (analyticAt_const (v := (0 : A))).congr
    filter_upwards [hdegF] with x hx
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

section Monic

variable {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
  {F G : E → A[X]} {x₀ : E} {m d : ℕ}

/-- Quotient coefficients are analytic when the dividend has locally bounded degree and the
monic divisor has locally constant degree. Only coefficients through the given bounds are
required to be analytic. -/
theorem analyticAt_coeff_divByMonic
    (hF : ∀ i ≤ m, AnalyticAt 𝕜 (fun x ↦ (F x).coeff i) x₀)
    (hG : ∀ i < d, AnalyticAt 𝕜 (fun x ↦ (G x).coeff i) x₀)
    (hdegF : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ m)
    (hGmonic : ∀ᶠ x in 𝓝 x₀, (G x).Monic ∧ (G x).natDegree = d) (k : ℕ) :
    AnalyticAt 𝕜 (fun x ↦ (F x /ₘ G x).coeff k) x₀ := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · let := hA
    exact (analyticAt_const (v := (0 : A))).congr (.of_forall fun _ ↦ Subsingleton.elim _ _)
  let := hA
  let c : E → (Fin (m + 1) ⊕ Fin d) → A :=
    fun x ↦ Sum.elim (fun i ↦ (F x).coeff i) (fun i ↦ (G x).coeff i)
  let P : (MvPolynomial (Fin (m + 1) ⊕ Fin d) A)[X] :=
    ∑ i : Fin (m + 1), monomial (i : ℕ) (MvPolynomial.X (Sum.inl i))
  let Q : (MvPolynomial (Fin (m + 1) ⊕ Fin d) A)[X] :=
    Polynomial.monicOfCoeff (fun i ↦ MvPolynomial.X (Sum.inr i))
  have hc (i) : AnalyticAt 𝕜 (fun x ↦ c x i) x₀ := by
    cases i with
    | inl i => exact hF i (by omega)
    | inr i => exact hG i i.2
  have ha := AnalyticAt.aeval_mvPolynomial hc ((P /ₘ Q).coeff k)
  apply ha.congr
  filter_upwards [hdegF, hGmonic] with x hFx hGx
  have hP : P.map (MvPolynomial.eval (c x)) = F x := by
    simp only [P, Polynomial.map_sum, Polynomial.map_monomial, MvPolynomial.eval_X,
      c, Sum.elim_inl]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ monomial i ((F x).coeff i))]
    exact ((F x).as_sum_range' (m + 1) (by omega)).symm
  have hQ : Q.map (MvPolynomial.eval (c x)) = G x := by
    simp only [Q, Polynomial.map_monicOfCoeff, MvPolynomial.eval_X, c, Sum.elim_inr]
    exact Polynomial.monicOfCoeff_coeff hGx.1 hGx.2
  rw [MvPolynomial.aeval_eq_eval, ← Polynomial.coeff_map,
    Polynomial.map_divByMonic _ (Polynomial.monic_monicOfCoeff _), hP, hQ]

/-- Remainder coefficients are analytic under monic division with locally bounded dividend
degree and locally constant divisor degree. Constant divisors and zero dividends are included. -/
theorem analyticAt_coeff_modByMonic
    (hF : ∀ i ≤ m, AnalyticAt 𝕜 (fun x ↦ (F x).coeff i) x₀)
    (hG : ∀ i < d, AnalyticAt 𝕜 (fun x ↦ (G x).coeff i) x₀)
    (hdegF : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ m)
    (hGmonic : ∀ᶠ x in 𝓝 x₀, (G x).Monic ∧ (G x).natDegree = d) (k : ℕ) :
    AnalyticAt 𝕜 (fun x ↦ (F x %ₘ G x).coeff k) x₀ := by
  have hFa := analyticAt_coeff_of_eventually_natDegree_le hF hdegF
  have hGa (i : ℕ) : AnalyticAt 𝕜 (fun x ↦ (G x).coeff i) x₀ := by
    rcases lt_trichotomy i d with hi | rfl | hi
    · exact hG i hi
    · apply (analyticAt_const (v := (1 : A))).congr
      filter_upwards [hGmonic] with x hx
      rw [← hx.2, hx.1.coeff_natDegree]
    · apply (analyticAt_const (v := (0 : A))).congr
      filter_upwards [hGmonic] with x hx
      exact (coeff_eq_zero_of_natDegree_lt (hx.2 ▸ hi)).symm
  simpa only [modByMonic_eq_sub_mul_div, coeff_sub, coeff_mul] using
    (hFa k).fun_sub (Finset.analyticAt_fun_sum (Finset.antidiagonal k) fun i _ ↦ (hGa i.1).fun_mul
      (analyticAt_coeff_divByMonic hF hG hdegF hGmonic i.2))

end Monic

section Field

variable {K : Type*} [NontriviallyNormedField K] [NormedAlgebra 𝕜 K]
  {F G : E → K[X]} {x₀ : E} {m d : ℕ}

/-- Ordinary quotient coefficients are analytic when the dividend has locally bounded degree
and the nonzero divisor has locally constant degree. No monicity is required. -/
theorem analyticAt_coeff_div
    (hF : ∀ i ≤ m, AnalyticAt 𝕜 (fun x ↦ (F x).coeff i) x₀)
    (hG : ∀ i ≤ d, AnalyticAt 𝕜 (fun x ↦ (G x).coeff i) x₀)
    (hdegF : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ m)
    (hdegG : ∀ᶠ x in 𝓝 x₀, (G x).natDegree = d) (hG₀ : G x₀ ≠ 0) (k : ℕ) :
    AnalyticAt 𝕜 (fun x ↦ (F x / G x).coeff k) x₀ := by
  have hlc₀ : (G x₀).coeff d ≠ 0 := by
    rw [← hdegG.self_of_nhds, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hG₀
  have hinv := (hG d le_rfl).fun_inv hlc₀
  let H : E → K[X] := fun x ↦ G x * C ((G x).coeff d)⁻¹
  have hH (i : ℕ) (hi : i < d) : AnalyticAt 𝕜 (fun x ↦ (H x).coeff i) x₀ := by
    simpa only [H, coeff_mul_C] using (hG i hi.le).fun_mul hinv
  have hGn : ∀ᶠ x in 𝓝 x₀, (G x).coeff d ≠ 0 :=
    (hG d le_rfl).continuousAt.eventually_ne hlc₀
  have hHm : ∀ᶠ x in 𝓝 x₀, (H x).Monic ∧ (H x).natDegree = d := by
    filter_upwards [hdegG, hGn] with x hx hn
    have hn' : G x ≠ 0 := fun hz ↦ hn (by simp [hz])
    have hlc : (G x).coeff d = (G x).leadingCoeff := by rw [← hx, coeff_natDegree]
    exact ⟨by simpa only [H, hlc] using monic_mul_leadingCoeff_inv hn', by
      simp only [H, hlc, natDegree_mul_leadingCoeff_inv _ hn', hx]⟩
  apply (hinv.fun_mul (analyticAt_coeff_divByMonic hF hH hdegF hHm k)).congr
  filter_upwards [hdegG] with x hx
  have hlc : (G x).coeff d = (G x).leadingCoeff := by rw [← hx, coeff_natDegree]
  simp only [div_def, coeff_C_mul, H, hlc]

/-- Ordinary remainder coefficients are analytic when the dividend has locally bounded degree
and the nonzero divisor has locally constant degree. The divisor may be nonmonic. -/
theorem analyticAt_coeff_mod
    (hF : ∀ i ≤ m, AnalyticAt 𝕜 (fun x ↦ (F x).coeff i) x₀)
    (hG : ∀ i ≤ d, AnalyticAt 𝕜 (fun x ↦ (G x).coeff i) x₀)
    (hdegF : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ m)
    (hdegG : ∀ᶠ x in 𝓝 x₀, (G x).natDegree = d) (hG₀ : G x₀ ≠ 0) (k : ℕ) :
    AnalyticAt 𝕜 (fun x ↦ (F x % G x).coeff k) x₀ := by
  have hFa := analyticAt_coeff_of_eventually_natDegree_le hF hdegF
  have hGa := analyticAt_coeff_of_eventually_natDegree_le hG (hdegG.mono fun _ hx ↦ hx.le)
  simpa only [EuclideanDomain.mod_eq_sub_mul_div, coeff_sub, coeff_mul] using
    (hFa k).fun_sub (Finset.analyticAt_fun_sum (Finset.antidiagonal k) fun i _ ↦ (hGa i.1).fun_mul
      (analyticAt_coeff_div hF hG hdegF hdegG hG₀ i.2))

end Field

end TauCeti
