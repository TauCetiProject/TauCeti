/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.OrthogonalSplitting
public import TauCeti.Analysis.PDE.Vortex.Existence
public import TauCeti.Analysis.PDE.Vortex.SobolevRealization
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
import TauCeti.Analysis.PDE.Vortex.Fredholm
import TauCeti.Analysis.PDE.Vortex.Reduced.Continuity
import TauCeti.Topology.Algebra.Polynomial.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Kernel projections and right inverses along the family of plane vortices

For a complex polynomial `P`, Taubes's plane vortex with zero divisor `P` is the field
`TauCeti.Vortex.polynomialVortex P` reconstructed from the amplitude `u₀ + w`, where `u₀` is the
background amplitude of `P` and `w` the smooth solution of the reduced equation, and from the
section `P`. Its section is `exp (u₀ + w) P`, so it vanishes exactly at the roots of `P`, with
multiplicity. For monic `P` of degree `m ≥ 1` it is a smooth vortex with the degree-`m` end
framing (`TauCeti.Vortex.equation_polynomialVortex`,
`TauCeti.Vortex.tendsto_sectionValue_polynomialVortex`). The monic polynomials of degree `m` are
parametrized by their lower coefficients `c ∈ ℂᵐ` (`TauCeti.Polynomial.monicOfCoeff`), which are
symmetric coordinates on the divisor space `Sym^m ℂ`, collisions of zeros included.

The field is bounded (`TauCeti.Vortex.exists_norm_polynomialVortex_le`): its section by
`exp (sup w)`, and its connection, the derivative of the amplitude, because `Du₀` is bounded by
the growth of `P'` against `P`, and `Dw` by the interior gradient estimate, since `w` and the
right side of the reduced equation are bounded. So it has an `L∞` class
`TauCeti.Vortex.polynomialVortexLp P`, the coefficient of the realization
`L_P : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` of its gauge-fixed operator
(`TauCeti.Vortex.sobolevGaugeFixedOperator`). At a monic `P` of positive degree, `L_P` is onto
with a finite-dimensional kernel.

Along a family of polynomials of a fixed positive degree whose coefficients depend continuously
on a parameter, the reduced solutions and their derivatives move uniformly on the plane, and so
do the vortices (`TauCeti.Vortex.tendstoUniformly_polynomialVortex`); hence their `L∞` classes
move continuously (`TauCeti.Vortex.continuous_polynomialVortexLp`). Composed with the continuity
of the orthogonal kernel projections and right inverses at Fredholm operators that are onto
(`ContinuousLinearMap.IsFredholm.continuousAt_orthogonalKerProjection`,
`ContinuousLinearMap.IsFredholm.continuousAt_orthogonalRightInverse`), this shows that the
projection of `H¹(ℂ)⁴` onto the kernel of `L_P` along its `L²`-orthogonal complement, and the
right inverse of `L_P` with values in that complement, depend continuously on the vortex, in
operator norm:

* `TauCeti.Vortex.continuous_orthogonalKerProjection_sobolevGaugeFixedOperator_polynomialVortexLp`,
* `TauCeti.Vortex.continuous_orthogonalRightInverse_sobolevGaugeFixedOperator_polynomialVortexLp`.

In particular both are bounded uniformly over every compact set of coefficients, including the
coefficients of divisors with colliding zeros
(`TauCeti.Vortex.exists_norm_orthogonalKerProjection_sobolevGaugeFixedOperator_le_of_isCompact`,
`TauCeti.Vortex.exists_norm_orthogonalRightInverse_sobolevGaugeFixedOperator_le_of_isCompact`).
No bound uniform over all of `Sym^m ℂ`, which is not compact, is asserted. Smooth dependence on
the coefficients is proved in `TauCeti.Analysis.PDE.Vortex.Divisor.Smooth`.

## Main definitions

* `TauCeti.Vortex.polynomialVortex P`: the plane vortex with zero divisor `P`.
* `TauCeti.Vortex.polynomialVortexLp P`: its `L∞` class.

## Main results

* `TauCeti.Vortex.exists_norm_polynomialVortex_le`: the vortex of a polynomial is bounded.
* `TauCeti.Vortex.tendstoUniformly_polynomialVortex`,
  `TauCeti.Vortex.continuous_polynomialVortexLp`: continuity of the vortex in the coefficients.
* `TauCeti.Vortex.sobolevGaugeFixedOperator_polynomialVortexLp_surjective`,
  `TauCeti.Vortex.finiteDimensional_ker_sobolevGaugeFixedOperator_polynomialVortexLp`: at a monic
  polynomial of positive degree the realization is onto with a finite-dimensional kernel.
* `TauCeti.Vortex.continuous_orthogonalKerProjection_sobolevGaugeFixedOperator_polynomialVortexLp`,
  `TauCeti.Vortex.continuous_orthogonalRightInverse_sobolevGaugeFixedOperator_polynomialVortexLp`:
  continuity of the orthogonal kernel projections and right inverses along continuous families of
  monic polynomials of a fixed positive degree.
* `TauCeti.Vortex.exists_norm_orthogonalKerProjection_sobolevGaugeFixedOperator_le_of_isCompact`,
  `TauCeti.Vortex.exists_norm_orthogonalRightInverse_sobolevGaugeFixedOperator_le_of_isCompact`:
  their bounds over a compact set of coefficients.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

open Complex MeasureTheory Filter Metric Set Topology TopologicalSpace InnerProductSpace Laplacian
open scoped ContDiff ENNReal RealInnerProductSpace

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

namespace TauCeti.Vortex

/-! ### The vortex of a polynomial -/

/-- **The plane vortex of a polynomial.** The field reconstructed from the amplitude `u₀ + w`,
with `u₀` the background amplitude of `P` and `w = TauCeti.Vortex.reducedSolution P`, and from
the section `P`. Its section `exp (u₀ + w) P` vanishes exactly at the roots of `P`, and for
monic `P` of positive degree it is a framed vortex (`TauCeti.Vortex.equation_polynomialVortex`,
`TauCeti.Vortex.tendsto_sectionValue_polynomialVortex`). -/
def polynomialVortex (P : Polynomial ℂ) : ℂ → EuclideanSpace ℝ (Fin 4) :=
  amplitudeField (fun z ↦ backgroundAmplitude P.eval z + reducedSolution P z) P.eval

variable (P : Polynomial ℂ)

/-- The vortex of `P` is the field reconstructed from the amplitude `u₀ + w` and the section
`P`. -/
theorem polynomialVortex_def :
    polynomialVortex P =
      amplitudeField (fun z ↦ backgroundAmplitude P.eval z + reducedSolution P z) P.eval :=
  (rfl)

/-- The section of the vortex of `P` is `exp (u₀ + w) P`. -/
@[simp]
theorem sectionValue_polynomialVortex (z : ℂ) :
    sectionValue (polynomialVortex P) z =
      (Real.exp (backgroundAmplitude P.eval z + reducedSolution P z) : ℂ) * P.eval z :=
  sectionValue_amplitudeField _ _ z

/-- The vortex of a polynomial is smooth. -/
theorem contDiff_polynomialVortex : ContDiff ℝ ∞ (polynomialVortex P) :=
  contDiff_amplitudeField (n := ⊤) ((contDiff_backgroundAmplitude
    ((P.differentiable.contDiff).restrict_scalars ℝ)).add (contDiff_reducedSolution P))
    ((P.differentiable.contDiff).restrict_scalars ℝ)

variable {P}

/-- The vortex of a monic polynomial of positive degree solves the vortex equations. -/
theorem equation_polynomialVortex (hP : P.Monic) (hm : 0 < P.natDegree) (z : ℂ) :
    equation (polynomialVortex P) z = 0 :=
  (equation_amplitudeField_reducedSolution_eq_zero_and_tendsto_sectionValue hP hm).1 z

/-- The vortex of a monic polynomial of degree `m ≥ 1` has the degree-`m` end framing
`α(z) (z / ‖z‖)⁻ᵐ → 1`. -/
theorem tendsto_sectionValue_polynomialVortex (hP : P.Monic) (hm : 0 < P.natDegree) :
    Tendsto (fun z ↦ sectionValue (polynomialVortex P) z * ((z / (‖z‖ : ℂ)) ^ P.natDegree)⁻¹)
      (cocompact ℂ) (𝓝 1) :=
  (equation_amplitudeField_reducedSolution_eq_zero_and_tendsto_sectionValue hP hm).2

/-! ### Boundedness -/

/-- The connection coordinates of the vortex of a polynomial are bounded. -/
private theorem exists_abs_polynomialVortex_connection_le (P : Polynomial ℂ) :
    ∃ D, ∀ z, |polynomialVortex P z 0| ≤ D ∧ |polynomialVortex P z 1| ≤ D := by
  obtain ⟨C, hC⟩ := exists_abs_fderiv_backgroundAmplitude_apply_le P
  obtain ⟨D, hD⟩ := exists_norm_fderiv_reducedSolution_le P
  have hu₀ : Differentiable ℝ (backgroundAmplitude P.eval) :=
    (contDiff_backgroundAmplitude
      ((P.differentiable.contDiff (n := 1)).restrict_scalars ℝ)).differentiable one_ne_zero
  have hw : Differentiable ℝ (reducedSolution P) :=
    (contDiff_reducedSolution P).differentiable (by simp)
  have hbound (z v : ℂ) (hv : ‖v‖ = 1) :
      |fderiv ℝ (fun z ↦ backgroundAmplitude P.eval z + reducedSolution P z) z v| ≤ C + D := by
    rw [fderiv_fun_add (hu₀ z) (hw z), add_apply]
    refine (abs_add_le _ _).trans (add_le_add (hC z v hv) ?_)
    have := (fderiv ℝ (reducedSolution P) z).le_opNorm v
    rw [hv, mul_one, Real.norm_eq_abs] at this
    exact this.trans (hD z)
  refine ⟨C + D, fun z ↦ ⟨?_, ?_⟩⟩
  · rw [polynomialVortex_def, amplitudeField_apply_zero, abs_neg]
    exact hbound z I (by simp)
  · rw [polynomialVortex_def, amplitudeField_apply_one]
    exact hbound z 1 (by simp)

/-- The section coordinates of the vortex of a polynomial are bounded. -/
private theorem exists_polynomialVortex_section_le (P : Polynomial ℂ) :
    ∃ S, ∀ z, 4 * (polynomialVortex P z 2 ^ 2 + polynomialVortex P z 3 ^ 2) ≤ S := by
  obtain ⟨B, hB⟩ := exists_abs_reducedSolution_le P
  refine ⟨Real.exp (2 * B), fun z ↦ ?_⟩
  rw [polynomialVortex_def, amplitudeField_normSq, mul_add, Real.exp_add,
    exp_two_mul_backgroundAmplitude]
  have h1 : (1 + ‖P.eval z‖ ^ 2)⁻¹ * ‖P.eval z‖ ^ 2 ≤ 1 := by
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith
  calc (1 + ‖P.eval z‖ ^ 2)⁻¹ * Real.exp (2 * reducedSolution P z) * ‖P.eval z‖ ^ 2
      = Real.exp (2 * reducedSolution P z) * ((1 + ‖P.eval z‖ ^ 2)⁻¹ * ‖P.eval z‖ ^ 2) := by ring
    _ ≤ Real.exp (2 * B) * 1 :=
        mul_le_mul (Real.exp_le_exp.2 (by linarith [(abs_le.1 (hB z)).2])) h1 (by positivity)
          (Real.exp_pos _).le
    _ = Real.exp (2 * B) := mul_one _

/-- **The vortex of a polynomial is bounded.** -/
theorem exists_norm_polynomialVortex_le (P : Polynomial ℂ) :
    ∃ M, ∀ z, ‖polynomialVortex P z‖ ≤ M := by
  obtain ⟨D, hD⟩ := exists_abs_polynomialVortex_connection_le P
  obtain ⟨S, hS⟩ := exists_polynomialVortex_section_le P
  refine ⟨2 * D + S + 1, fun z ↦ ?_⟩
  obtain ⟨h₀, h₁⟩ := hD z
  have hD0 : 0 ≤ D := (abs_nonneg _).trans h₀
  have hS0 : 0 ≤ S := (by positivity : (0 : ℝ) ≤ 4 * (polynomialVortex P z 2 ^ 2 +
    polynomialVortex P z 3 ^ 2)).trans (hS z)
  have hsq : ‖polynomialVortex P z‖ ^ 2 ≤ (2 * D + S + 1) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
    have h₀' := sq_le_sq' (abs_le.1 h₀).1 (abs_le.1 h₀).2
    have h₁' := sq_le_sq' (abs_le.1 h₁).1 (abs_le.1 h₁).2
    nlinarith [hS z]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith) two_ne_zero).1 hsq

/-- The vortex of a polynomial is essentially bounded. -/
theorem memLp_polynomialVortex (P : Polynomial ℂ) : MemLp (polynomialVortex P) ∞ μ⊤ := by
  obtain ⟨M, hM⟩ := exists_norm_polynomialVortex_le P
  exact memLp_top_of_bound (contDiff_polynomialVortex P).continuous.aestronglyMeasurable M
    (.of_forall hM)

/-- **The `L∞` class of the vortex of a polynomial**, the coefficient of the realization
`TauCeti.Vortex.sobolevGaugeFixedOperator` at that vortex. -/
def polynomialVortexLp (P : Polynomial ℂ) : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤ :=
  (memLp_polynomialVortex P).toLp _

/-- The `L∞` class of the vortex of `P` is represented by the vortex. -/
theorem polynomialVortexLp_ae_eq (P : Polynomial ℂ) :
    polynomialVortexLp P =ᵐ[μ⊤] polynomialVortex P :=
  (memLp_polynomialVortex P).coeFn_toLp

/-! ### The realization at the vortex of a polynomial -/

section Realization

variable (hP : P.Monic) (hm : 0 < P.natDegree)
include hP hm

/-- The squared modulus of the section of the vortex of a monic polynomial of positive degree
tends to one at infinity. -/
private theorem tendsto_normSq_polynomialVortex :
    Tendsto (fun z ↦ 4 * (polynomialVortex P z 2 ^ 2 + polynomialVortex P z 3 ^ 2))
      (cocompact ℂ) (𝓝 1) :=
  tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow (tendsto_sectionValue_polynomialVortex hP hm)

/-- **The realization at a vortex is onto.** At the vortex of a monic polynomial of positive
degree, `L_P : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` is surjective. -/
theorem sobolevGaugeFixedOperator_polynomialVortexLp_surjective :
    Function.Surjective (sobolevGaugeFixedOperator (polynomialVortexLp P)) :=
  sobolevGaugeFixedOperator_surjective ((contDiff_polynomialVortex P).of_le (by simp))
    (equation_polynomialVortex hP hm) (tendsto_normSq_polynomialVortex hP hm)
    (polynomialVortexLp_ae_eq P)

/-- At the vortex of a monic polynomial of positive degree, the kernel of
`L_P : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` is finite-dimensional. -/
theorem finiteDimensional_ker_sobolevGaugeFixedOperator_polynomialVortexLp :
    FiniteDimensional ℝ (sobolevGaugeFixedOperator (polynomialVortexLp P)).ker := by
  have hx := contDiff_polynomialVortex P
  exact finiteDimensional_ker_sobolevGaugeFixedOperator (hx.of_le (by simp))
    (equation_polynomialVortex hP hm) (tendsto_normSq_polynomialVortex hP hm)
    (tendsto_covariantDerivative_cocompact (contDiff_euclidean.1 hx 0).continuous
      ((contDiff_euclidean.1 hx 2).of_le (by simp)) ((contDiff_euclidean.1 hx 3).of_le (by simp))
      (equation_polynomialVortex hP hm) (tendsto_normSq_polynomialVortex hP hm) 1)
    (polynomialVortexLp_ae_eq P)

end Realization

/-! ### Continuity in the coefficients -/

/-- **Uniform convergence of the vortices.** If the coefficients of the polynomials `P i` converge
to those of a polynomial `Q` of positive degree, and eventually `deg P i ≤ deg Q`, then the
vortices of `P i` converge to that of `Q` uniformly on the plane. -/
theorem tendstoUniformly_polynomialVortex {ι : Type*} {l : Filter ι} {P : ι → Polynomial ℂ}
    {Q : Polynomial ℂ} (hQ : 0 < Q.natDegree) (hdeg : ∀ᶠ i in l, (P i).natDegree ≤ Q.natDegree)
    (hcoeff : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (Q.coeff k))) :
    TendstoUniformly (fun i ↦ polynomialVortex (P i)) (polynomialVortex Q) l := by
  obtain ⟨B, hB⟩ := exists_abs_reducedSolution_le Q
  exact tendstoUniformly_amplitudeField_backgroundAmplitude_add hdeg hcoeff
    (fun i ↦ (contDiff_reducedSolution (P i)).differentiable (by simp))
    ((contDiff_reducedSolution Q).differentiable (by simp)) (fun z ↦ (abs_le.1 (hB z)).2)
    (tendstoUniformly_reducedSolution hQ hdeg hcoeff)
    (tendstoUniformly_fderiv_reducedSolution hQ hdeg hcoeff)

variable {X : Type*} [TopologicalSpace X] {P : X → Polynomial ℂ} {m : ℕ}

/-- **Continuity of the `L∞` classes of the vortices.** For a family of polynomials of a fixed
positive degree whose coefficients depend continuously on a parameter, the `L∞` classes of their
vortices depend continuously on the parameter. -/
theorem continuous_polynomialVortexLp (hm : 0 < m) (hdeg : ∀ x, (P x).natDegree = m)
    (hcoeff : ∀ k, Continuous fun x ↦ (P x).coeff k) :
    Continuous fun x ↦ polynomialVortexLp (P x) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hu := Metric.tendstoUniformly_iff.1 (tendstoUniformly_polynomialVortex
    ((hdeg x₀).symm ▸ hm) (Eventually.of_forall fun y ↦ ((hdeg y).trans (hdeg x₀).symm).le)
    fun k ↦ (hcoeff k).continuousAt) (ε / 2) (half_pos hε)
  filter_upwards [hu] with x hx
  rw [dist_eq_norm]
  refine (Lp.norm_le_of_ae_bound_top (half_pos hε).le ?_).trans_lt (half_lt_self hε)
  filter_upwards [Lp.coeFn_sub (polynomialVortexLp (P x)) (polynomialVortexLp (P x₀)),
    polynomialVortexLp_ae_eq (P x), polynomialVortexLp_ae_eq (P x₀)] with z hz h₁ h₂
  rw [hz, Pi.sub_apply, h₁, h₂, ← dist_eq_norm, dist_comm]
  exact (hx z).le

variable (hm : 0 < m) (hmonic : ∀ x, (P x).Monic) (hdeg : ∀ x, (P x).natDegree = m)
  (hcoeff : ∀ k, Continuous fun x ↦ (P x).coeff k)
include hm hmonic hdeg hcoeff

/-- **Continuity of the kernel projections along the vortex family.** For a family of monic
polynomials of a fixed positive degree whose coefficients depend continuously on a parameter, the
projection of `H¹(ℂ)⁴` onto the kernel of `L_P : H¹ → L²` along its `L²`-orthogonal complement
depends continuously on the parameter, in operator norm. -/
theorem continuous_orthogonalKerProjection_sobolevGaugeFixedOperator_polynomialVortexLp :
    Continuous fun x ↦ ContinuousLinearMap.orthogonalKerProjection sobolevFieldValues
      (sobolevGaugeFixedOperator (polynomialVortexLp (P x))) :=
  continuous_orthogonalKerProjection_sobolevGaugeFixedOperator
    (continuous_polynomialVortexLp hm hdeg hcoeff)
    (fun x ↦ sobolevGaugeFixedOperator_polynomialVortexLp_surjective (hmonic x)
      ((hdeg x).symm ▸ hm))
    fun x ↦ finiteDimensional_ker_sobolevGaugeFixedOperator_polynomialVortexLp (hmonic x)
      ((hdeg x).symm ▸ hm)

/-- **Continuity of the right inverses along the vortex family.** For a family of monic
polynomials of a fixed positive degree whose coefficients depend continuously on a parameter, the
right inverse of `L_P : H¹ → L²` with values `L²`-orthogonal to its kernel depends continuously on
the parameter, in operator norm. -/
theorem continuous_orthogonalRightInverse_sobolevGaugeFixedOperator_polynomialVortexLp :
    Continuous fun x ↦ ContinuousLinearMap.orthogonalRightInverse sobolevFieldValues
      (sobolevGaugeFixedOperator (polynomialVortexLp (P x))) :=
  continuous_orthogonalRightInverse_sobolevGaugeFixedOperator
    (continuous_polynomialVortexLp hm hdeg hcoeff)
    (fun x ↦ sobolevGaugeFixedOperator_polynomialVortexLp_surjective (hmonic x)
      ((hdeg x).symm ▸ hm))
    fun x ↦ finiteDimensional_ker_sobolevGaugeFixedOperator_polynomialVortexLp (hmonic x)
      ((hdeg x).symm ▸ hm)

omit hm hmonic hdeg hcoeff

/-- **The kernel projections are bounded over a compact window of divisors.** For `m ≥ 1` and a
compact set `K` of coefficient tuples `c ∈ ℂᵐ`, symmetric coordinates on `Sym^m ℂ` that include
divisors with colliding zeros, the orthogonal kernel projections of `L_P` at the vortices of the
monic polynomials `P = TauCeti.Polynomial.monicOfCoeff c`, `c ∈ K`, are bounded in operator norm by
one constant. -/
theorem exists_norm_orthogonalKerProjection_sobolevGaugeFixedOperator_le_of_isCompact
    (hm : 0 < m) {K : Set (Fin m → ℂ)} (hK : IsCompact K) :
    ∃ C, ∀ c ∈ K, ‖ContinuousLinearMap.orthogonalKerProjection sobolevFieldValues
      (sobolevGaugeFixedOperator (polynomialVortexLp (Polynomial.monicOfCoeff c)))‖ ≤ C := by
  -- The codomain is given explicitly so that its operator norm is found.
  exact hK.exists_bound_of_continuousOn
    (E := (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2))
    (continuous_orthogonalKerProjection_sobolevGaugeFixedOperator_polynomialVortexLp hm
      Polynomial.monic_monicOfCoeff Polynomial.natDegree_monicOfCoeff
      Polynomial.continuous_coeff_monicOfCoeff).continuousOn

/-- **The right inverses are bounded over a compact window of divisors.** For `m ≥ 1` and a
compact set `K` of coefficient tuples `c ∈ ℂᵐ`, symmetric coordinates on `Sym^m ℂ` that include
divisors with colliding zeros, the right inverses of `L_P` orthogonal to its kernel at the vortices
of the monic polynomials `P = TauCeti.Polynomial.monicOfCoeff c`, `c ∈ K`, are bounded in operator
norm by one constant. -/
theorem exists_norm_orthogonalRightInverse_sobolevGaugeFixedOperator_le_of_isCompact
    (hm : 0 < m) {K : Set (Fin m → ℂ)} (hK : IsCompact K) :
    ∃ C, ∀ c ∈ K, ‖ContinuousLinearMap.orthogonalRightInverse sobolevFieldValues
      (sobolevGaugeFixedOperator (polynomialVortexLp (Polynomial.monicOfCoeff c)))‖ ≤ C := by
  -- The codomain is given explicitly so that its operator norm is found.
  exact hK.exists_bound_of_continuousOn
    (E := Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2))
    (continuous_orthogonalRightInverse_sobolevGaugeFixedOperator_polynomialVortexLp hm
      Polynomial.monic_monicOfCoeff Polynomial.natDegree_monicOfCoeff
      Polynomial.continuous_coeff_monicOfCoeff).continuousOn

end TauCeti.Vortex
