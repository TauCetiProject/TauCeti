/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import TauCeti.Analysis.Calculus.BumpFunction.Normed
public import TauCeti.Analysis.Calculus.IteratedFDeriv.IntegrationByParts
public import TauCeti.Analysis.MvPolynomial.TaylorPolynomial
public import TauCeti.MeasureTheory.Function.Lp.Restriction
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.MeasureTheory.Function.Holder
import TauCeti.LinearAlgebra.Multilinear.Basis
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.OddSymmetric

/-!
# The averaged Taylor polynomial on `L¹` and `Lᵖ`

Pointwise Taylor expansion `TauCeti.taylorPolynomial ℝ m u y` requires `m` classical derivatives of
`u` at the expansion center `y`, which do not exist for a general Sobolev or integrable function.
Following Sobolev and Brenner–Scott (Chapter 4, §4.1), averaging `T^m_y u (x)` against a smooth
compactly supported cutoff `φ` and integrating every `y`-derivative of `u` by parts onto
`z ↦ (∏ l, (x (I l) - z (I l))) * φ z` yields the **averaged Taylor kernel**
`TauCeti.averagedTaylorKernel φ m x y`:

`Ψ_m(x, y) = ∑_{j = 0}^m ((-1)^j / j!) ∑_{I : Fin j → ι}
  D_{e_{I 0}, …, e_{I (j - 1)}} (z ↦ (∏_{l : Fin j} (x_{I l} - z_{I l})) φ(z)) (y)`.

Only `φ` is differentiated in `Ψ_m(x, y)`. Consequently, whenever `φ` is `C^m` with compact
support:

1. For each `y`, `x ↦ Ψ_m(x, y)` lies in `TauCeti.polynomialsDegLE ι m`, and for every integrable
   `f`, `x ↦ ∫ y, f y * Ψ_m(x, y) ∂μ` also lies in `polynomialsDegLE ι m`.
2. Pairing against `Ψ_m` defines a continuous linear operator
   `TauCeti.averagedTaylorPolynomial μ m φ hφ hsupp : Lp ℝ 1 μ →L[ℝ] polynomialsDegLE ι m`
   for any Borel measure `μ` on `EuclideanSpace ℝ ι`, and by restriction to `tsupport φ` a
   continuous linear operator
   `TauCeti.averagedTaylorPolynomialLp μ p m φ hφ hsupp : Lp ℝ p μ →L[ℝ] polynomialsDegLE ι m`
   for any measure `μ` finite on compact sets (including `μ.restrict Ω` for any domain `Ω`) and any
   exponent `1 ≤ p`.
3. On an additive Haar measure `μ`, if `u` is `C^m` at every point of `tsupport φ`, iterated
   integration by parts recovers the literal cutoff average of the classical Taylor polynomial
   (`TauCeti.integral_mul_averagedTaylorKernel_eq_integral_taylorPolynomial`):
   `∫ y, u y * Ψ_m(x, y) ∂μ = ∫ y, taylorPolynomial ℝ m u y x * φ y ∂μ`,
   with immediate corollaries for `averagedTaylorPolynomial` and `averagedTaylorPolynomialLp`
   both on `μ` and on `μ.restrict Ω` (`tsupport φ ⊆ Ω`).
4. Combining (3) with polynomial reproduction of `taylorPolynomial` shows that if `tsupport φ ⊆ Ω`
   and `∫ y, φ y ∂μ = 1`, both `averagedTaylorPolynomial (μ.restrict Ω)` and
   `averagedTaylorPolynomialLp (μ.restrict Ω)` reproduce every polynomial of degree at most `m`
   (`TauCeti.averagedTaylorPolynomial_toLp_eq_self`,
   `TauCeti.averagedTaylorPolynomialLp_toLp_eq_self`).

Degree `m` is sharp: for any even `C¹` compactly supported cutoff `φ`, the degree-`1` averaged
Taylor polynomial sends the coordinate quadratic `x ↦ (x i) ^ 2` to the constant
`-∫ y, (y i) ^ 2 * φ y ∂μ` (`TauCeti.averagedTaylorPolynomial_sq_one_of_even`), which is strictly
negative when `φ` is nonnegative with nontrivial support (as for `(ballBump 0 hρ).normed μ`). In
particular, `TauCeti.averagedTaylorPolynomial_normed_ballBump_sq_one_ne_self` shows that degree-`1`
averaging does not reproduce `x ↦ (x i) ^ 2`, whereas `averagedTaylorPolynomial_toLp_eq_self`
reproduces it at `m = 2`.

## Main definitions

* `TauCeti.averagedTaylorKernel`: the smooth integration-by-parts kernel `Ψ_m(x, y)`.
* `TauCeti.averagedTaylorPolynomial`: continuous linear operator
  `Lp ℝ 1 μ →L[ℝ] polynomialsDegLE ι m`.
* `TauCeti.averagedTaylorPolynomialLp`: continuous linear operator
  `Lp ℝ p μ →L[ℝ] polynomialsDegLE ι m` for `[IsFiniteMeasureOnCompacts μ]` and `1 ≤ p`.

## Main results

* `TauCeti.averagedTaylorKernel_one`: explicit `m = 1` formula
  `Ψ_1(x, y) = (1 + card ι) * φ y - fderiv ℝ φ y (x - y)`.
* `TauCeti.averagedTaylorKernel_mem_polynomialsDegLE`: `Ψ_m(·, y) ∈ polynomialsDegLE ι m`.
* `TauCeti.integral_mul_averagedTaylorKernel_eq_integral_taylorPolynomial`,
  `TauCeti.averagedTaylorPolynomial_eq_integral_taylorPolynomial`,
  `TauCeti.averagedTaylorPolynomialLp_eq_integral_taylorPolynomial`: on `C^m` representatives,
  `Q^m f (x) = ∫ y, T^m_y u (x) * φ y ∂μ`.
* `TauCeti.averagedTaylorPolynomial_toLp_eq_self`,
  `TauCeti.averagedTaylorPolynomialLp_toLp_eq_self`: reproduction of `polynomialsDegLE ι m`.
* `TauCeti.averagedTaylorPolynomial_sq_one_of_even`,
  `TauCeti.averagedTaylorPolynomial_normed_ballBump_sq_one_ne_self`,
  `TauCeti.averagedTaylorPolynomial_zero_halfBall_eq_half`: explicit evaluations on coordinate
  quadratics and discontinuous half-ball indicators.

## References

* Susanne C. Brenner and L. Ridgway Scott, *The Mathematical Theory of Finite Element Methods*,
  3rd ed., Springer (2008), Chapter 4, §§4.1–4.2 (Definition 4.1.3 and Proposition 4.1.9).
-/

public section

noncomputable section

open Filter MeasureTheory Metric MvPolynomial Set
open scoped ContDiff ENNReal Topology

namespace TauCeti

section Kernel

variable {ι : Type*} [Fintype ι]

/-- List of coordinate basis directions `[e_{I 0}, …, e_{I (j - 1)}]` in `EuclideanSpace ℝ ι`. -/
private def coordDirections {j : ℕ} (I : Fin j → ι) : List (EuclideanSpace ℝ ι) :=
  List.ofFn fun l ↦ EuclideanSpace.basisFun ι ℝ (I l)

private theorem length_coordDirections {j : ℕ} (I : Fin j → ι) :
    (coordDirections I).length = j :=
  List.length_ofFn

/-- Single-multi-index test function `z ↦ (∏ l, (x (I l) - z (I l))) * φ z` differentiated in
`averagedTaylorKernel`. -/
private def kernelTestTerm (φ : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι)
    {j : ℕ} (I : Fin j → ι) (z : EuclideanSpace ℝ ι) : ℝ :=
  (∏ l : Fin j, (x (I l) - z (I l))) * φ z

/-- **Averaged Taylor kernel.** For a cutoff `φ : EuclideanSpace ℝ ι → ℝ`, degree `m : ℕ`, target
point `x`, and integration variable `y`, `averagedTaylorKernel φ m x y` is the formal adjoint of
averaging `taylorPolynomial ℝ m · y x` against `φ y`. -/
def averagedTaylorKernel (φ : EuclideanSpace ℝ ι → ℝ) (m : ℕ) (x y : EuclideanSpace ℝ ι) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
    ∑ I : Fin j → ι,
      iteratedFDerivAlong ℝ (List.ofFn fun l ↦ EuclideanSpace.basisFun ι ℝ (I l))
        (fun z ↦ (∏ l : Fin j, (x (I l) - z (I l))) * φ z) y

theorem averagedTaylorKernel_def (φ : EuclideanSpace ℝ ι → ℝ) (m : ℕ)
    (x y : EuclideanSpace ℝ ι) :
    averagedTaylorKernel φ m x y =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
        ∑ I : Fin j → ι,
          iteratedFDerivAlong ℝ (List.ofFn fun l ↦ EuclideanSpace.basisFun ι ℝ (I l))
            (fun z ↦ (∏ l : Fin j, (x (I l) - z (I l))) * φ z) y :=
  (rfl)

private theorem averagedTaylorKernel_eq_sum_kernelTestTerm (φ : EuclideanSpace ℝ ι → ℝ) (m : ℕ)
    (x y : EuclideanSpace ℝ ι) :
    averagedTaylorKernel φ m x y =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
        ∑ I : Fin j → ι,
          iteratedFDerivAlong ℝ (coordDirections I) (kernelTestTerm φ x I) y :=
  (rfl)

/-- At order `0`, the averaged Taylor kernel is simply `φ y` (independent of `x`). -/
@[simp]
theorem averagedTaylorKernel_zero (φ : EuclideanSpace ℝ ι → ℝ) (x y : EuclideanSpace ℝ ι) :
    averagedTaylorKernel φ 0 x y = φ y := by
  simp [averagedTaylorKernel_def]

/-- Recurrence separating the top-order derivative sum of `averagedTaylorKernel`. -/
theorem averagedTaylorKernel_succ (φ : EuclideanSpace ℝ ι → ℝ) (m : ℕ)
    (x y : EuclideanSpace ℝ ι) :
    averagedTaylorKernel φ (m + 1) x y =
      averagedTaylorKernel φ m x y +
        ((-1 : ℝ) ^ (m + 1) / ((m + 1).factorial : ℝ)) *
          ∑ I : Fin (m + 1) → ι,
            iteratedFDerivAlong ℝ (List.ofFn fun l ↦ EuclideanSpace.basisFun ι ℝ (I l))
              (fun z ↦ (∏ l : Fin (m + 1), (x (I l) - z (I l))) * φ z) y := by
  simp only [averagedTaylorKernel_def, Finset.sum_range_succ]

/-- Explicit first-order formula: when `φ` is differentiable at `y`,
`averagedTaylorKernel φ 1 x y = (1 + card ι) * φ y - fderiv ℝ φ y (x - y)`. -/
theorem averagedTaylorKernel_one {φ : EuclideanSpace ℝ ι → ℝ} {y : EuclideanSpace ℝ ι}
    (hφ : DifferentiableAt ℝ φ y) (x : EuclideanSpace ℝ ι) :
    averagedTaylorKernel φ 1 x y =
      (1 + Fintype.card ι : ℝ) * φ y - fderiv ℝ φ y (x - y) := by
  classical
  set b := EuclideanSpace.basisFun ι ℝ
  have hsum : (∑ I : Fin 1 → ι,
      iteratedFDerivAlong ℝ (List.ofFn fun l ↦ b (I l))
        (fun z ↦ (∏ l : Fin 1, (x (I l) - z (I l))) * φ z) y) =
      ∑ i : ι, ((x i - y i) * fderiv ℝ φ y (b i) - φ y) := by
    rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hderiv := ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y i).const_sub (x i)).fun_mul
      hφ.hasFDerivAt
    simp [hderiv.fderiv, b, EuclideanSpace.basisFun_apply]
    ring
  have hlin : ∑ i : ι, (x i - y i) * fderiv ℝ φ y (b i) = fderiv ℝ φ y (x - y) := by
    conv_rhs => rw [← b.sum_repr (x - y), map_sum]
    simp [b]
  rw [averagedTaylorKernel_succ, hsum, Finset.sum_sub_distrib, hlin]
  simp
  ring

/-- For every target point `x`, the support in `y` of `averagedTaylorKernel φ m x` is contained in
`tsupport φ`. -/
theorem tsupport_averagedTaylorKernel_subset (φ : EuclideanSpace ℝ ι → ℝ) (m : ℕ)
    (x : EuclideanSpace ℝ ι) :
    tsupport (averagedTaylorKernel φ m x) ⊆ tsupport φ := by
  refine closure_minimal (fun y hy ↦ by_contra fun hyφ ↦ Function.mem_support.mp hy ?_)
    (isClosed_tsupport φ)
  rw [averagedTaylorKernel_def]
  exact Finset.sum_eq_zero fun j _ ↦ mul_eq_zero_of_right _ (Finset.sum_eq_zero fun I _ ↦
    image_eq_zero_of_notMem_tsupport fun h ↦
      hyφ ((tsupport_iteratedFDerivAlong_subset _ _).trans tsupport_mul_subset_right h))

/-- Compact support of `φ` passes to `y ↦ averagedTaylorKernel φ m x y` for every `x`. -/
theorem hasCompactSupport_averagedTaylorKernel {φ : EuclideanSpace ℝ ι → ℝ}
    (hsupp : HasCompactSupport φ) (m : ℕ) (x : EuclideanSpace ℝ ι) :
    HasCompactSupport (averagedTaylorKernel φ m x) :=
  hsupp.of_isClosed_subset (isClosed_tsupport _) (tsupport_averagedTaylorKernel_subset φ m x)

/-- If `φ` is `C^n` and `k + m ≤ n`, then `y ↦ averagedTaylorKernel φ m x y` is `C^k`. -/
theorem contDiff_averagedTaylorKernel_right {φ : EuclideanSpace ℝ ι → ℝ} {n k : ℕ∞ω} {m : ℕ}
    (hφ : ContDiff ℝ n φ) (hkm : k + m ≤ n) (x : EuclideanSpace ℝ ι) :
    ContDiff ℝ k (averagedTaylorKernel φ m x) := by
  rw [funext (averagedTaylorKernel_eq_sum_kernelTestTerm φ m x)]
  refine ContDiff.sum fun j hj ↦ contDiff_const.mul (ContDiff.sum fun I _ ↦ ?_)
  have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  refine ((contDiff_prod fun l _ ↦
    contDiff_const.sub (EuclideanSpace.proj (𝕜 := ℝ) (I l)).contDiff).mul hφ).iteratedFDerivAlong
    (coordDirections I) ?_
  rw [length_coordDirections]
  exact (add_le_add_right (by exact_mod_cast hjle) k).trans hkm

/-- If `φ` is `C^m`, then `y ↦ averagedTaylorKernel φ m x y` is continuous for every `x`. -/
theorem continuous_averagedTaylorKernel_right {φ : EuclideanSpace ℝ ι → ℝ} {m : ℕ}
    (hφ : ContDiff ℝ m φ) (x : EuclideanSpace ℝ ι) :
    Continuous (averagedTaylorKernel φ m x) :=
  (contDiff_averagedTaylorKernel_right (k := 0) hφ (by simp) x).continuous

/-- Auxiliary `x`-independent weight appearing when `∏ l, (x (I l) - z (I l))` is expanded into
monomials in `x`. -/
private def kernelMonomialWeight (φ : EuclideanSpace ℝ ι → ℝ) {j : ℕ} (I : Fin j → ι)
    (S : Finset (Fin j)) (y : EuclideanSpace ℝ ι) : ℝ :=
  iteratedFDerivAlong ℝ (coordDirections I)
    (fun z ↦ (∏ l ∈ Finset.univ \ S, -z (I l)) * φ z) y

private theorem contDiff_kernelMonomialWeight {φ : EuclideanSpace ℝ ι → ℝ} {m j : ℕ}
    (hφ : ContDiff ℝ m φ) (hj : j ≤ m) (I : Fin j → ι) (S : Finset (Fin j)) :
    ContDiff ℝ 0 (kernelMonomialWeight φ I S) := by
  refine ((contDiff_prod fun l _ ↦
    (EuclideanSpace.proj (𝕜 := ℝ) (I l)).contDiff.neg).mul hφ).iteratedFDerivAlong
    (coordDirections I) ?_
  rw [length_coordDirections, zero_add]; exact_mod_cast hj

private theorem hasCompactSupport_kernelMonomialWeight {φ : EuclideanSpace ℝ ι → ℝ}
    (hsupp : HasCompactSupport φ) {j : ℕ} (I : Fin j → ι) (S : Finset (Fin j)) :
    HasCompactSupport (kernelMonomialWeight φ I S) :=
  (hsupp.mul_left).iteratedFDerivAlong (coordDirections I)

/-- Monomial expansion of `averagedTaylorKernel φ m x y` separating the `x`-monomials from the
`y`-weights. -/
private theorem averagedTaylorKernel_eq_sum_monomial {φ : EuclideanSpace ℝ ι → ℝ} {m : ℕ}
    (hφ : ContDiff ℝ m φ) (x y : EuclideanSpace ℝ ι) :
    averagedTaylorKernel φ m x y =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
        ∑ I : Fin j → ι, ∑ S ∈ (Finset.univ : Finset (Fin j)).powerset,
          (∏ l ∈ S, x (I l)) * kernelMonomialWeight φ I S y := by
  rw [averagedTaylorKernel_eq_sum_kernelTestTerm]
  refine Finset.sum_congr rfl fun j hj ↦ congrArg _ (Finset.sum_congr rfl fun I _ ↦ ?_)
  let F (S : Finset (Fin j)) : EuclideanSpace ℝ ι → ℝ :=
    (∏ l ∈ S, x (I l)) • fun z ↦ (∏ l ∈ Finset.univ \ S, -z (I l)) * φ z
  have hcont (S : Finset (Fin j)) : ContDiff ℝ m
      (fun z : EuclideanSpace ℝ ι ↦ (∏ l ∈ Finset.univ \ S, -z (I l)) * φ z) :=
    (contDiff_prod fun l _ ↦ (EuclideanSpace.proj (𝕜 := ℝ) (I l)).contDiff.neg).mul hφ
  have hlen : ((coordDirections I).length : ℕ∞ω) ≤ m := by
    rw [length_coordDirections]; exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hdecomp : kernelTestTerm φ x I =
      ∑ S ∈ (Finset.univ : Finset (Fin j)).powerset, F S := by
    ext z
    simp_rw [Finset.sum_apply, kernelTestTerm, sub_eq_add_neg]
    rw [Finset.prod_add (fun l ↦ x (I l)) (fun l ↦ -z (I l)) Finset.univ, Finset.sum_mul]
    simp [F, mul_assoc]
  rw [hdecomp, congrFun (iteratedFDerivAlong_sum (f := F) _
    (fun S _ ↦ (hcont S).const_smul (∏ l ∈ S, x (I l))) (coordDirections I) hlen) y,
    Finset.sum_apply]
  exact Finset.sum_congr rfl fun S _ ↦ by
    simpa [F, kernelMonomialWeight] using congrFun
      (iteratedFDerivAlong_const_smul (hcont S) (∏ l ∈ S, x (I l)) (coordDirections I) hlen) y

/-- For every fixed `y`, if `φ` is `C^m`, the map `x ↦ averagedTaylorKernel φ m x y` is a
polynomial of total degree at most `m`. -/
theorem averagedTaylorKernel_mem_polynomialsDegLE {φ : EuclideanSpace ℝ ι → ℝ} {m : ℕ}
    (hφ : ContDiff ℝ m φ) (y : EuclideanSpace ℝ ι) :
    (fun x ↦ averagedTaylorKernel φ m x y) ∈ polynomialsDegLE ι m := by
  convert Submodule.sum_mem (polynomialsDegLE ι m) (t := Finset.range (m + 1)) fun j hj ↦
    Submodule.smul_mem _ ((-1 : ℝ) ^ j / (j.factorial : ℝ)) <|
      Submodule.sum_mem _ (t := Finset.univ) fun (I : Fin j → ι) _ ↦
        Submodule.sum_mem _ (t := (Finset.univ : Finset (Fin j)).powerset) fun S _ ↦
          Submodule.smul_mem _ (kernelMonomialWeight φ I S y) <|
            polynomialsDegLE_mono ι
              ((Finset.card_le_univ S).trans (by
                simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
              (prod_coord_mem_polynomialsDegLE S I) using 1
  ext x
  rw [averagedTaylorKernel_eq_sum_monomial hφ]
  simp [Finset.mul_sum, mul_comm]

end Kernel

section Operator

variable {ι : Type*} [Fintype ι]

/-- Monomial expansion of `x ↦ ∫ y, f y * averagedTaylorKernel φ m x y ∂μ` obtained by
interchanging the finite monomial sum with integration against `f`. -/
private theorem integral_mul_averagedTaylorKernel_eq_sum_monomial
    {μ : Measure (EuclideanSpace ℝ ι)} {m : ℕ} {φ f : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hf : Integrable f μ) :
    (fun x ↦ ∫ y, f y * averagedTaylorKernel φ m x y ∂μ) =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) •
        ∑ I : Fin j → ι, ∑ S ∈ (Finset.univ : Finset (Fin j)).powerset,
          (∫ y, f y * kernelMonomialWeight φ I S y ∂μ) •
            fun x : EuclideanSpace ℝ ι ↦ ∏ l ∈ S, x (I l) := by
  have hint_w {j : ℕ} (hj : j ≤ m) (I : Fin j → ι) (S : Finset (Fin j)) :
      Integrable (fun y ↦ f y * kernelMonomialWeight φ I S y) μ :=
    hf.mul_of_top_left
      ((contDiff_kernelMonomialWeight hφ hj I S).continuous.memLp_top_of_hasCompactSupport
        (hasCompactSupport_kernelMonomialWeight hsupp I S) μ)
  ext x
  have hpt (y : EuclideanSpace ℝ ι) : f y * averagedTaylorKernel φ m x y =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
        ∑ I : Fin j → ι, ∑ S ∈ (Finset.univ : Finset (Fin j)).powerset,
          (∏ l ∈ S, x (I l)) * (f y * kernelMonomialWeight φ I S y) := by
    rw [averagedTaylorKernel_eq_sum_monomial hφ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← mul_assoc, mul_comm (f y), mul_assoc, Finset.mul_sum]
    exact congrArg _ (Finset.sum_congr rfl fun I _ ↦ by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun S _ ↦ by ring)
  simp_rw [hpt]
  rw [integral_finsetSum _ fun j hj ↦ (integrable_finsetSum _ fun I _ ↦ integrable_finsetSum _
    fun S _ ↦ (hint_w (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) I S).const_mul _).const_mul _]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjle := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [integral_const_mul, integral_finsetSum _ fun I _ ↦
    integrable_finsetSum _ fun S _ ↦ (hint_w hjle I S).const_mul _]
  refine congrArg _ (Finset.sum_congr rfl fun I _ ↦ ?_)
  rw [integral_finsetSum _ fun S _ ↦ (hint_w hjle I S).const_mul _]
  exact Finset.sum_congr rfl fun S _ ↦ by rw [integral_const_mul, mul_comm]

/-- Integrating any `Integrable f μ` against `averagedTaylorKernel φ m` produces a polynomial of
total degree at most `m`. -/
theorem integral_mul_averagedTaylorKernel_mem_polynomialsDegLE
    {μ : Measure (EuclideanSpace ℝ ι)} {m : ℕ} {φ f : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hf : Integrable f μ) :
    (fun x ↦ ∫ y, f y * averagedTaylorKernel φ m x y ∂μ) ∈ polynomialsDegLE ι m := by
  rw [integral_mul_averagedTaylorKernel_eq_sum_monomial hφ hsupp hf]
  exact Submodule.sum_mem _ fun j hj ↦ Submodule.smul_mem _ _ <|
    Submodule.sum_mem _ fun I _ ↦ Submodule.sum_mem _ fun S _ ↦ Submodule.smul_mem _ _ <|
      polynomialsDegLE_mono ι
        ((Finset.card_le_univ S).trans (by
          simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
        (prod_coord_mem_polynomialsDegLE S I)

/-- Since `y ↦ averagedTaylorKernel φ m x y` is supported in `tsupport φ`, integrating
`f y * averagedTaylorKernel φ m x y` over any superset `s` of `tsupport φ` equals the
full-space integral. -/
theorem setIntegral_mul_averagedTaylorKernel_eq_integral
    {μ : Measure (EuclideanSpace ℝ ι)} {s : Set (EuclideanSpace ℝ ι)}
    {m : ℕ} {φ f : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι}
    (hs : tsupport φ ⊆ s) :
    ∫ y in s, f y * averagedTaylorKernel φ m x y ∂μ =
      ∫ y, f y * averagedTaylorKernel φ m x y ∂μ :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
    simp [image_eq_zero_of_notMem_tsupport
      fun h ↦ hy (hs (tsupport_averagedTaylorKernel_subset φ m x h))]

/-- Pointwise evaluation `f ↦ ∫ y, f y * averagedTaylorKernel φ m x y ∂μ` expressed as Mathlib's
`L¹`–`L^∞` Hölder pairing `ContinuousLinearMap.lpPairing`. -/
private theorem averagedTaylorEval_eq_lpPairing (μ : Measure (EuclideanSpace ℝ ι)) (m : ℕ)
    {φ : EuclideanSpace ℝ ι → ℝ} (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (x : EuclideanSpace ℝ ι) (f : Lp ℝ 1 μ) :
    ∫ y, f y * averagedTaylorKernel φ m x y ∂μ =
      ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ 1 (∞ : ℝ≥0∞)).flip
        (((continuous_averagedTaylorKernel_right hφ x).memLp_top_of_hasCompactSupport
          (hasCompactSupport_averagedTaylorKernel hsupp m x) μ).toLp
          (averagedTaylorKernel φ m x)) f := by
  rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing_eq_integral]
  exact integral_congr_ae
    ((((continuous_averagedTaylorKernel_right hφ x).memLp_top_of_hasCompactSupport
      (hasCompactSupport_averagedTaylorKernel hsupp m x) μ).coeFn_toLp).mono fun y hy ↦ by
      simp [hy])

/-- **The averaged Taylor polynomial on `L¹`.** For any Borel measure `μ` on `EuclideanSpace ℝ ι`
and any `C^m` compactly supported cutoff `φ`, pairing `f ∈ Lp ℝ 1 μ` against
`averagedTaylorKernel φ m` defines a continuous linear map into `polynomialsDegLE ι m`. -/
def averagedTaylorPolynomial (μ : Measure (EuclideanSpace ℝ ι)) (m : ℕ)
    (φ : EuclideanSpace ℝ ι → ℝ) (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) :
    Lp ℝ 1 μ →L[ℝ] polynomialsDegLE ι m where
  toFun f := ⟨fun x ↦ ∫ y, f y * averagedTaylorKernel φ m x y ∂μ,
    integral_mul_averagedTaylorKernel_mem_polynomialsDegLE hφ hsupp (L1.integrable_coeFn f)⟩
  map_add' f g := by
    ext x; simp_rw [Submodule.coe_add, Pi.add_apply, averagedTaylorEval_eq_lpPairing μ m hφ hsupp x]
    exact map_add _ f g
  map_smul' c f := by
    ext x; simp_rw [Submodule.coe_smul_of_tower, Pi.smul_apply, RingHom.id_apply,
      averagedTaylorEval_eq_lpPairing μ m hφ hsupp x]
    exact map_smul _ c f
  cont := by
    rw [Topology.IsInducing.subtypeVal.continuous_iff]
    refine continuous_pi fun x ↦ ?_
    simp only [Function.comp_def, averagedTaylorEval_eq_lpPairing μ m hφ hsupp x]
    exact ContinuousLinearMap.continuous _

/-- Pointwise evaluation formula for `averagedTaylorPolynomial`. -/
@[simp]
theorem averagedTaylorPolynomial_apply (μ : Measure (EuclideanSpace ℝ ι)) (m : ℕ)
    (φ : EuclideanSpace ℝ ι → ℝ) (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (f : Lp ℝ 1 μ) (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomial μ m φ hφ hsupp f : EuclideanSpace ℝ ι → ℝ) x =
      ∫ y, f y * averagedTaylorKernel φ m x y ∂μ :=
  (rfl)

/-- At order `0`, `averagedTaylorPolynomial` sends `f` to the constant function
`∫ y, f y * φ y ∂μ`. -/
theorem averagedTaylorPolynomial_zero_order (μ : Measure (EuclideanSpace ℝ ι))
    (φ : EuclideanSpace ℝ ι → ℝ) (hφ : ContDiff ℝ (0 : ℕ) φ) (hsupp : HasCompactSupport φ)
    (f : Lp ℝ 1 μ) (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomial μ 0 φ hφ hsupp f : EuclideanSpace ℝ ι → ℝ) x =
      ∫ y, f y * φ y ∂μ := by
  simp [averagedTaylorPolynomial_apply]

section AddHaar

variable {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]

private theorem contDiff_kernelTestTerm {φ : EuclideanSpace ℝ ι → ℝ} {m j : ℕ}
    (hφ : ContDiff ℝ m φ) (hj : j ≤ m) (x : EuclideanSpace ℝ ι) (I : Fin j → ι) :
    ContDiff ℝ j (kernelTestTerm φ x I) :=
  ((contDiff_prod fun l _ ↦
    contDiff_const.sub (EuclideanSpace.proj (𝕜 := ℝ) (I l)).contDiff).mul hφ).of_le
    (by exact_mod_cast hj)

private theorem integrable_mul_iteratedFDerivAlong_kernelTestTerm
    {m j : ℕ} {φ u : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y) (hj : j ≤ m) (x : EuclideanSpace ℝ ι)
    (I : Fin j → ι) :
    Integrable
      (fun y ↦ u y * iteratedFDerivAlong ℝ (coordDirections I) (kernelTestTerm φ x I) y) μ := by
  simpa only [smul_eq_mul] using
    ((contDiff_kernelTestTerm hφ hj x I).iteratedFDerivAlong (m := 0) (coordDirections I)
      (by simp [length_coordDirections])).continuous.integrable_smul_of_continuousOn
      (hsupp.mul_left.iteratedFDerivAlong _)
      ((tsupport_iteratedFDerivAlong_subset _ _).trans tsupport_mul_subset_right)
      fun y hy ↦ (hu y hy).continuousAt.continuousWithinAt

private theorem integrable_iteratedFDeriv_mul_kernelTestTerm
    {m j : ℕ} {φ u : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y) (hj : j ≤ m) (x : EuclideanSpace ℝ ι)
    (I : Fin j → ι) :
    Integrable (fun y ↦
      iteratedFDeriv ℝ j u y (fun l ↦ EuclideanSpace.basisFun ι ℝ (I l)) *
        kernelTestTerm φ x I y) μ := by
  have ha : ContinuousOn (fun y ↦
      iteratedFDeriv ℝ j u y (fun l ↦ EuclideanSpace.basisFun ι ℝ (I l))) (tsupport φ) :=
    fun y hy ↦ ((continuous_eval_const _).continuousAt.comp
      ((hu y hy).continuousAt_iteratedFDeriv (by exact_mod_cast hj))).continuousWithinAt
  simpa only [smul_eq_mul] using
    (contDiff_kernelTestTerm hφ hj x I).continuous.integrable_smul_of_continuousOn
      hsupp.mul_left tsupport_mul_subset_right ha

/-- Single-`(j, I)` integration-by-parts identity moving `coordDirections I` from
`kernelTestTerm φ x I` onto `u` and identifying the reversed directional derivative with
`iteratedFDeriv ℝ j u y`. -/
private theorem averagedTaylor_ibp_term
    {m j : ℕ} {φ u : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y) (hj : j ≤ m)
    (x : EuclideanSpace ℝ ι) (I : Fin j → ι) :
    ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
      (∫ y, u y * iteratedFDerivAlong ℝ (coordDirections I) (kernelTestTerm φ x I) y ∂μ) =
    (j.factorial : ℝ)⁻¹ * ∫ y,
      iteratedFDeriv ℝ j u y (fun l ↦ EuclideanSpace.basisFun ι ℝ (I l)) *
        kernelTestTerm φ x I y ∂μ := by
  set b := EuclideanSpace.basisFun ι ℝ
  have hibp := integral_mul_iteratedFDerivAlong_eq (μ := μ) (coordDirections I)
    (f := u) (g := kernelTestTerm φ x I)
    (fun y hy ↦ by
      rw [length_coordDirections]
      exact (hu y (tsupport_mul_subset_right hy)).of_le (by exact_mod_cast hj))
    (by simpa [length_coordDirections] using contDiff_kernelTestTerm hφ hj x I)
    hsupp.mul_left
  rw [length_coordDirections] at hibp
  have hpt : (fun y ↦
      iteratedFDerivAlong ℝ (coordDirections I).reverse u y * kernelTestTerm φ x I y) =
      fun y ↦ iteratedFDeriv ℝ j u y (fun l ↦ b (I l)) * kernelTestTerm φ x I y := by
    ext y; by_cases hy : y ∈ tsupport φ
    · have huy : ContDiffAt ℝ j u y := (hu y hy).of_le (by exact_mod_cast hj)
      rw [(List.reverse_perm (coordDirections I)).iteratedFDerivAlong_eq_of_contDiffAt huy
          (by simp [List.length_reverse, length_coordDirections])]
      simp only [coordDirections, huy.iteratedFDerivAlong_ofFn_eq_iteratedFDeriv le_rfl, b]
    · simp [kernelTestTerm, image_eq_zero_of_notMem_tsupport hy]
  rw [hibp, hpt, ← mul_assoc, div_mul_eq_mul_div, ← mul_pow]; norm_num

/-- Expanding `∫ y, u y * averagedTaylorKernel φ m x y ∂μ` into its finite `(j, I)` sum of
individual derivative integrals. -/
private theorem integral_mul_averagedTaylorKernel_eq_sum_ibp
    {m : ℕ} {φ u : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y) (x : EuclideanSpace ℝ ι) :
    ∫ y, u y * averagedTaylorKernel φ m x y ∂μ =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
        ∑ I : Fin j → ι, ∫ y,
          u y * iteratedFDerivAlong ℝ (coordDirections I) (kernelTestTerm φ x I) y ∂μ := by
  have hpt (y : EuclideanSpace ℝ ι) : u y * averagedTaylorKernel φ m x y =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
        ∑ I : Fin j → ι,
          u y * iteratedFDerivAlong ℝ (coordDirections I) (kernelTestTerm φ x I) y := by
    rw [averagedTaylorKernel_eq_sum_kernelTestTerm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← mul_assoc, mul_comm (u y), mul_assoc, Finset.mul_sum]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun j hj ↦ (integrable_finsetSum _ fun I _ ↦
    integrable_mul_iteratedFDerivAlong_kernelTestTerm hφ hsupp hu
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) x I).const_mul _]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [integral_const_mul, integral_finsetSum _ fun I _ ↦
    integrable_mul_iteratedFDerivAlong_kernelTestTerm hφ hsupp hu
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) x I]

/-- **Kernel-adjoint identity for the averaged Taylor kernel.** On `EuclideanSpace ℝ ι` with an
additive Haar measure `μ`, if `φ` is `C^m` with compact support and `u` is `C^m` at every point of
`tsupport φ`, then pairing `u` against `averagedTaylorKernel φ m x` recovers the cutoff average of
the classical `m`-th Taylor polynomial of `u`. -/
theorem integral_mul_averagedTaylorKernel_eq_integral_taylorPolynomial
    {m : ℕ} {φ u : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y) (x : EuclideanSpace ℝ ι) :
    ∫ y, u y * averagedTaylorKernel φ m x y ∂μ =
      ∫ y, taylorPolynomial ℝ m u y x * φ y ∂μ := by
  rw [integral_mul_averagedTaylorKernel_eq_sum_ibp hφ hsupp hu x]
  calc
    -- Move derivatives from `kernelTestTerm` onto `u` term by term.
    (∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
        ∑ I : Fin j → ι, ∫ y,
          u y * iteratedFDerivAlong ℝ (coordDirections I) (kernelTestTerm φ x I) y ∂μ)
      = ∑ j ∈ Finset.range (m + 1),
          ∑ I : Fin j → ι, (j.factorial : ℝ)⁻¹ *
            ∫ y, iteratedFDeriv ℝ j u y (fun l ↦ EuclideanSpace.basisFun ι ℝ (I l)) *
              kernelTestTerm φ x I y ∂μ :=
        Finset.sum_congr rfl fun j hj ↦ by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun I _ ↦ averagedTaylor_ibp_term hφ hsupp hu
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) x I
    -- Pull the finite `(j, I)` sums back inside the integral.
    _ = ∫ y, (∑ j ∈ Finset.range (m + 1),
          ∑ I : Fin j → ι, (j.factorial : ℝ)⁻¹ *
            (iteratedFDeriv ℝ j u y (fun l ↦ EuclideanSpace.basisFun ι ℝ (I l)) *
              kernelTestTerm φ x I y)) ∂μ := by
        have hint {j : ℕ} (hj : j ∈ Finset.range (m + 1)) (I : Fin j → ι) :=
          (integrable_iteratedFDeriv_mul_kernelTestTerm (μ := μ) hφ hsupp hu
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) x I).const_mul (j.factorial : ℝ)⁻¹
        rw [integral_finsetSum _ fun j hj ↦ integrable_finsetSum _ fun I _ ↦ hint hj I]
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rw [integral_finsetSum _ fun I _ ↦ hint hj I]
        exact Finset.sum_congr rfl fun I _ ↦ (integral_const_mul _ _).symm
    -- Reassemble the coordinate sums into `taylorPolynomial ℝ m u y x * φ y`.
    _ = ∫ y, taylorPolynomial ℝ m u y x * φ y ∂μ := by
        congr 1; ext y; rw [taylorPolynomial_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        have hcoord : iteratedFDeriv ℝ j u y (fun _ ↦ x - y) =
            ∑ I : Fin j → ι, (∏ l : Fin j, (x (I l) - y (I l))) *
              iteratedFDeriv ℝ j u y (fun l ↦ EuclideanSpace.basisFun ι ℝ (I l)) := by
          simpa only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
            EuclideanSpace.basisFun_repr, PiLp.sub_apply, ContinuousMultilinearMap.coe_coe,
            smul_eq_mul] using
            (iteratedFDeriv ℝ j u y).toMultilinearMap.apply_eq_sum_prod_repr_smul
              (fun _ ↦ (EuclideanSpace.basisFun ι ℝ).toBasis) (fun _ ↦ x - y)
        rw [smul_eq_mul, hcoord, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun I _ ↦ by simp only [kernelTestTerm]; ring

/-- **Integration-by-parts identity for `averagedTaylorPolynomial` on `L¹(μ)`.** If `u` is `C^m` at
every point of `tsupport φ` and `f ∈ Lp ℝ 1 μ` agrees with `u` almost everywhere, then
`averagedTaylorPolynomial μ m φ hφ hsupp f` coincides with the cutoff average of the classical
`m`-th Taylor polynomial of `u`. -/
theorem averagedTaylorPolynomial_eq_integral_taylorPolynomial
    {m : ℕ} {φ u : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y)
    {f : Lp ℝ 1 μ} (hf : (f : EuclideanSpace ℝ ι → ℝ) =ᵐ[μ] u) (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomial μ m φ hφ hsupp f : EuclideanSpace ℝ ι → ℝ) x =
      ∫ y, taylorPolynomial ℝ m u y x * φ y ∂μ := by
  rw [averagedTaylorPolynomial_apply, integral_congr_ae (hf.mono fun y hy ↦ by rw [hy])]
  exact integral_mul_averagedTaylorKernel_eq_integral_taylorPolynomial hφ hsupp hu x

/-- **Integration-by-parts identity for `averagedTaylorPolynomial` on `L¹(μ.restrict B)`.** If `u`
is `C^m` at every point of `tsupport φ ⊆ B` and `f ∈ Lp ℝ 1 (μ.restrict B)` agrees with `u` almost
everywhere on `B`, then `averagedTaylorPolynomial (μ.restrict B) m φ hφ hsupp f` coincides with the
cutoff average of the classical `m`-th Taylor polynomial of `u`. -/
theorem averagedTaylorPolynomial_restrict_eq_integral_taylorPolynomial
    {B : Set (EuclideanSpace ℝ ι)} {m : ℕ} {φ u : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hB : tsupport φ ⊆ B)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y)
    {f : Lp ℝ 1 (μ.restrict B)} (hf : (f : EuclideanSpace ℝ ι → ℝ) =ᵐ[μ.restrict B] u)
    (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomial (μ.restrict B) m φ hφ hsupp f : EuclideanSpace ℝ ι → ℝ) x =
      ∫ y, taylorPolynomial ℝ m u y x * φ y ∂μ := by
  rw [averagedTaylorPolynomial_apply, integral_congr_ae (hf.mono fun y hy ↦ by rw [hy]),
    setIntegral_mul_averagedTaylorKernel_eq_integral hB]
  exact integral_mul_averagedTaylorKernel_eq_integral_taylorPolynomial hφ hsupp hu x

/-- **Polynomial reproduction on `L¹`.** If `tsupport φ ⊆ B` and `∫ y, φ y ∂μ = 1` for an additive
Haar measure `μ`, then `averagedTaylorPolynomial (μ.restrict B) m φ hφ hsupp` reproduces every
polynomial `q ∈ polynomialsDegLE ι m` whose restriction to `B` belongs to `L¹`. -/
theorem averagedTaylorPolynomial_toLp_eq_self
    {B : Set (EuclideanSpace ℝ ι)} {m : ℕ} {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hB : tsupport φ ⊆ B)
    (hint1 : ∫ y, φ y ∂μ = 1)
    {q : EuclideanSpace ℝ ι → ℝ} (hq : q ∈ polynomialsDegLE ι m)
    (hqL1 : MemLp q 1 (μ.restrict B)) :
    averagedTaylorPolynomial (μ.restrict B) m φ hφ hsupp (hqL1.toLp q) = ⟨q, hq⟩ := by
  ext x
  rw [averagedTaylorPolynomial_restrict_eq_integral_taylorPolynomial hφ hsupp hB
    (fun _ _ ↦ (contDiff_of_mem_polynomialsDegLE hq).contDiffAt) hqL1.coeFn_toLp]
  simp [taylorPolynomial_eq_self_of_mem_polynomialsDegLE hq, integral_const_mul, hint1]

end AddHaar

section LpDomain

/-- **The averaged Taylor polynomial on `Lᵖ`.** For any measure `μ` finite on compact sets,
exponent `1 ≤ p`, and `C^m` compactly supported cutoff `φ`, composing `averagedTaylorPolynomial`
with restriction to `tsupport φ` via `Set.LpToL1RestrictCLM` defines a continuous linear operator
`Lp ℝ p μ →L[ℝ] polynomialsDegLE ι m`. -/
def averagedTaylorPolynomialLp (μ : Measure (EuclideanSpace ℝ ι))
    [IsFiniteMeasureOnCompacts μ] (p : ℝ≥0∞) [Fact (1 ≤ p)] (m : ℕ)
    (φ : EuclideanSpace ℝ ι → ℝ) (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) :
    Lp ℝ p μ →L[ℝ] polynomialsDegLE ι m :=
  (averagedTaylorPolynomial (μ.restrict (tsupport φ)) m φ hφ hsupp).comp
    (Set.LpToL1RestrictCLM (𝕜 := ℝ) (tsupport φ) hsupp.measure_lt_top)

theorem averagedTaylorPolynomialLp_def (μ : Measure (EuclideanSpace ℝ ι))
    [IsFiniteMeasureOnCompacts μ] (p : ℝ≥0∞) [Fact (1 ≤ p)] (m : ℕ)
    (φ : EuclideanSpace ℝ ι → ℝ) (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) :
    averagedTaylorPolynomialLp μ p m φ hφ hsupp =
      (averagedTaylorPolynomial (μ.restrict (tsupport φ)) m φ hφ hsupp).comp
        (Set.LpToL1RestrictCLM (𝕜 := ℝ) (tsupport φ) hsupp.measure_lt_top) :=
  (rfl)

/-- Unconditional integral evaluation formula for `averagedTaylorPolynomialLp`. -/
@[simp]
theorem averagedTaylorPolynomialLp_apply (μ : Measure (EuclideanSpace ℝ ι))
    [IsFiniteMeasureOnCompacts μ] (p : ℝ≥0∞) [Fact (1 ≤ p)] (m : ℕ)
    (φ : EuclideanSpace ℝ ι → ℝ) (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (f : Lp ℝ p μ) (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomialLp μ p m φ hφ hsupp f : EuclideanSpace ℝ ι → ℝ) x =
      ∫ y, f y * averagedTaylorKernel φ m x y ∂μ := by
  simp only [averagedTaylorPolynomialLp_def, ContinuousLinearMap.comp_apply,
    averagedTaylorPolynomial_apply]
  rw [integral_congr_ae ((Set.LpToL1RestrictCLM_coeFn (𝕜 := ℝ) (tsupport φ)
      hsupp.measure_lt_top f).mono fun y hy ↦ by rw [hy]),
    setIntegral_mul_averagedTaylorKernel_eq_integral Subset.rfl]

/-- **Integration-by-parts identity for `averagedTaylorPolynomialLp` on `Lᵖ(μ)`.** If `u` is `C^m`
at every point of `tsupport φ` and `f ∈ Lp ℝ p μ` agrees with `u` almost everywhere, then
`averagedTaylorPolynomialLp μ p m φ hφ hsupp f` coincides with the cutoff average of the classical
`m`-th Taylor polynomial of `u`. -/
theorem averagedTaylorPolynomialLp_eq_integral_taylorPolynomial
    {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {m : ℕ} {φ u : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y)
    {f : Lp ℝ p μ} (hf : (f : EuclideanSpace ℝ ι → ℝ) =ᵐ[μ] u) (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomialLp μ p m φ hφ hsupp f : EuclideanSpace ℝ ι → ℝ) x =
      ∫ y, taylorPolynomial ℝ m u y x * φ y ∂μ := by
  rw [averagedTaylorPolynomialLp_apply, integral_congr_ae (hf.mono fun y hy ↦ by rw [hy])]
  exact integral_mul_averagedTaylorKernel_eq_integral_taylorPolynomial hφ hsupp hu x

/-- **Integration-by-parts identity for `averagedTaylorPolynomialLp` on `Lᵖ(μ.restrict Ω)`.** If
`u` is `C^m` at every point of `tsupport φ ⊆ Ω` and `f ∈ Lp ℝ p (μ.restrict Ω)` agrees with `u`
almost everywhere on `Ω`, then `averagedTaylorPolynomialLp (μ.restrict Ω) p m φ hφ hsupp f`
coincides with the cutoff average of the classical `m`-th Taylor polynomial of `u`. -/
theorem averagedTaylorPolynomialLp_restrict_eq_integral_taylorPolynomial
    {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {Ω : Set (EuclideanSpace ℝ ι)}
    {m : ℕ} {φ u : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hΩ : tsupport φ ⊆ Ω)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y)
    {f : Lp ℝ p (μ.restrict Ω)} (hf : (f : EuclideanSpace ℝ ι → ℝ) =ᵐ[μ.restrict Ω] u)
    (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomialLp (μ.restrict Ω) p m φ hφ hsupp f : EuclideanSpace ℝ ι → ℝ) x =
      ∫ y, taylorPolynomial ℝ m u y x * φ y ∂μ := by
  rw [averagedTaylorPolynomialLp_apply, integral_congr_ae (hf.mono fun y hy ↦ by rw [hy]),
    setIntegral_mul_averagedTaylorKernel_eq_integral hΩ]
  exact integral_mul_averagedTaylorKernel_eq_integral_taylorPolynomial hφ hsupp hu x

/-- **Polynomial reproduction on `Lᵖ(Ω)`.** If `tsupport φ ⊆ Ω` and `∫ y, φ y ∂μ = 1` for an
additive Haar measure `μ`, then `averagedTaylorPolynomialLp (μ.restrict Ω)` reproduces every
`q ∈ polynomialsDegLE ι m` belonging to `Lᵖ(μ.restrict Ω)`. In particular, when `Ω` is nonempty and
star-shaped with respect to `Metric.ball x₀ ρ` (`0 < ρ`), `Metric.ball x₀ ρ ⊆ Ω` holds by
`StarConvex.mem` and `φ = (ballBump x₀ hρ).normed μ` satisfies all cutoff hypotheses. -/
theorem averagedTaylorPolynomialLp_toLp_eq_self
    {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {Ω : Set (EuclideanSpace ℝ ι)}
    {m : ℕ} {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hΩ : tsupport φ ⊆ Ω)
    (hint1 : ∫ y, φ y ∂μ = 1)
    {q : EuclideanSpace ℝ ι → ℝ} (hq : q ∈ polynomialsDegLE ι m)
    (hqLp : MemLp q p (μ.restrict Ω)) :
    averagedTaylorPolynomialLp (μ.restrict Ω) p m φ hφ hsupp (hqLp.toLp q) = ⟨q, hq⟩ := by
  ext x
  rw [averagedTaylorPolynomialLp_restrict_eq_integral_taylorPolynomial p hφ hsupp hΩ
    (fun _ _ ↦ (contDiff_of_mem_polynomialsDegLE hq).contDiffAt) hqLp.coeFn_toLp]
  simp [taylorPolynomial_eq_self_of_mem_polynomialsDegLE hq, integral_const_mul, hint1]

end LpDomain

end Operator

section Examples

/-! ### Explicit evaluations on coordinate quadratics and half-balls -/

variable {ι : Type*} [Fintype ι]

/-- On `EuclideanSpace ℝ ι` equipped with an additive Haar measure `μ`, if `φ` is `C¹`, compactly
supported in `B`, and even (`∀ y, φ (-y) = φ y`), then for every coordinate `i : ι` the first-order
averaged Taylor polynomial sends the quadratic `q(x) = (x i) ^ 2` to the constant
`-∫ y, (y i) ^ 2 * φ y ∂μ`. -/
theorem averagedTaylorPolynomial_sq_one_of_even
    {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
    {B : Set (EuclideanSpace ℝ ι)} {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ (1 : ℕ) φ) (hsupp : HasCompactSupport φ) (hB : tsupport φ ⊆ B)
    (heven : ∀ y, φ (-y) = φ y) (i : ι)
    (hqL1 : MemLp (fun z : EuclideanSpace ℝ ι ↦ (z i) ^ 2) 1 (μ.restrict B))
    (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomial (μ.restrict B) 1 φ hφ hsupp
      (hqL1.toLp fun z ↦ (z i) ^ 2) : EuclideanSpace ℝ ι → ℝ) x =
      -∫ y, (y i) ^ 2 * φ y ∂μ := by
  let q₂ : EuclideanSpace ℝ ι → ℝ := fun z ↦ (z i) ^ 2
  have hq₂_smooth : ContDiff ℝ (1 : ℕ) q₂ := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.pow 2
  rw [averagedTaylorPolynomial_restrict_eq_integral_taylorPolynomial hφ hsupp hB
    (fun _ _ ↦ hq₂_smooth.contDiffAt) hqL1.coeFn_toLp]
  have htaylor (y : EuclideanSpace ℝ ι) :
      taylorPolynomial ℝ 1 q₂ y x = 2 * x i * y i - (y i) ^ 2 := by
    have hderiv := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y i).pow 2
    simp [taylorPolynomial_succ, iteratedFDeriv_one_apply, q₂, hderiv.fderiv]
    ring
  simp_rw [htaylor, sub_mul]
  have hint1 : Integrable (fun y : EuclideanSpace ℝ ι ↦ 2 * x i * y i * φ y) μ :=
    ((continuous_const.mul (PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i)).mul
      hφ.continuous).integrable_of_hasCompactSupport hsupp.mul_left
  have hint2 : Integrable (fun y : EuclideanSpace ℝ ι ↦ (y i) ^ 2 * φ y) μ :=
    (((PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i).pow 2).mul
      hφ.continuous).integrable_of_hasCompactSupport hsupp.mul_left
  rw [integral_sub hint1 hint2,
    MeasureTheory.integral_eq_zero_of_odd (g := fun y : EuclideanSpace ℝ ι ↦ 2 * x i * y i * φ y)
      fun y ↦ by simp [heven y], zero_sub]

/-- Degree `m` is sharp: on `Metric.ball 0 ρ` (`0 < ρ`) in `EuclideanSpace ℝ ι` with cutoff
`(ballBump 0 hρ).normed μ` and any coordinate `i : ι`, the degree-`1` averaged Taylor polynomial
does **not** reproduce `z ↦ (z i) ^ 2` (whereas `averagedTaylorPolynomial_toLp_eq_self` shows that
the degree-`2` averaged Taylor polynomial reproduces it identically). -/
theorem averagedTaylorPolynomial_normed_ballBump_sq_one_ne_self
    {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure] {ρ : ℝ} (hρ : 0 < ρ) (i : ι)
    (hqL1 : MemLp (fun z : EuclideanSpace ℝ ι ↦ (z i) ^ 2) 1 (μ.restrict (ball 0 ρ))) :
    (averagedTaylorPolynomial (μ.restrict (ball 0 ρ)) 1 ((ballBump 0 hρ).normed μ)
        ((ballBump 0 hρ).contDiff_normed (n := (1 : ℕ)))
        (ballBump 0 hρ).hasCompactSupport_normed
        (hqL1.toLp fun z ↦ (z i) ^ 2) : EuclideanSpace ℝ ι → ℝ) ≠
      fun z ↦ (z i) ^ 2 := by
  classical
  intro heq
  set φ := (ballBump (0 : EuclideanSpace ℝ ι) hρ).normed μ
  have hval := congrFun heq 0
  rw [averagedTaylorPolynomial_sq_one_of_even ((ballBump 0 hρ).contDiff_normed (n := (1 : ℕ)))
      (ballBump 0 hρ).hasCompactSupport_normed (tsupport_normed_ballBump_subset_ball μ 0 hρ)
      (fun y ↦ (ballBump 0 hρ).normed_neg y) i hqL1 0,
    PiLp.zero_apply, zero_pow two_ne_zero] at hval
  have hcont : Continuous (fun y : EuclideanSpace ℝ ι ↦ (y i) ^ 2 * φ y) :=
    ((PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i).pow 2).mul (ballBump 0 hρ).continuous_normed
  have hpos : 0 < ∫ y : EuclideanSpace ℝ ι, (y i) ^ 2 * φ y ∂μ := by
    refine (integral_pos_iff_support_of_nonneg
      (fun y ↦ mul_nonneg (sq_nonneg _) ((ballBump 0 hρ).nonneg_normed y))
      (hcont.integrable_of_hasCompactSupport
        (ballBump 0 hρ).hasCompactSupport_normed.mul_left)).mpr ?_
    let z₀ : EuclideanSpace ℝ ι := (ρ / 4) • EuclideanSpace.basisFun ι ℝ i
    have hz₀_ball : z₀ ∈ Function.support φ := by
      rw [(ballBump 0 hρ).support_normed_eq, ballBump_rOut, mem_ball_zero_iff, norm_smul,
        (EuclideanSpace.basisFun ι ℝ).orthonormal.1 i, mul_one, Real.norm_of_nonneg (by positivity)]
      linarith
    refine (isOpen_compl_singleton.preimage hcont).measure_pos μ ⟨z₀, ?_⟩
    simp only [mem_preimage, mem_compl_iff, mem_singleton_iff]
    have hz₀i : z₀ i = ρ / 4 := by simp [z₀, EuclideanSpace.basisFun_apply]
    exact hz₀i ▸ mul_ne_zero (pow_ne_zero 2 (by linarith)) (Function.mem_support.mp hz₀_ball)
  linarith

/-- Evaluating `averagedTaylorPolynomial` at order `0` with `(ballBump 0 hρ).normed μ` on the
discontinuous `L¹` indicator of the positive half-ball `{y ∈ ball 0 ρ | 0 ≤ y i}` yields the
constant polynomial `1 / 2`. -/
theorem averagedTaylorPolynomial_zero_halfBall_eq_half
    {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure] {ρ : ℝ} (hρ : 0 < ρ) (i : ι)
    (hHm : MeasurableSet {y ∈ ball (0 : EuclideanSpace ℝ ι) ρ | 0 ≤ y i})
    (hHfin : μ {y ∈ ball (0 : EuclideanSpace ℝ ι) ρ | 0 ≤ y i} ≠ (∞ : ℝ≥0∞)) :
    (averagedTaylorPolynomial μ 0 ((ballBump 0 hρ).normed μ)
      ((ballBump 0 hρ).contDiff_normed (n := (0 : ℕ)))
      (ballBump 0 hρ).hasCompactSupport_normed
      (indicatorConstLp 1 hHm hHfin (1 : ℝ)) : EuclideanSpace ℝ ι → ℝ) =
      fun _ ↦ (1 : ℝ) / 2 := by
  classical
  set H : Set (EuclideanSpace ℝ ι) := {y ∈ ball 0 ρ | 0 ≤ y i}
  let P : Set (EuclideanSpace ℝ ι) := {y | 0 ≤ EuclideanSpace.proj (𝕜 := ℝ) i y}
  have hPm : MeasurableSet P :=
    (isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) i).continuous).measurableSet
  ext x; rw [averagedTaylorPolynomial_zero_order]
  set φ := (ballBump (0 : EuclideanSpace ℝ ι) hρ).normed μ
  have hHP : ∫ y, H.indicator φ y ∂μ = ∫ y in P, φ y ∂μ := by
    rw [← integral_indicator hPm]; congr 1; ext y
    by_cases hyφ : φ y = 0
    · by_cases h1 : y ∈ H <;> by_cases h2 : y ∈ P <;> simp [h1, h2, hyφ]
    · have hyb := tsupport_normed_ballBump_subset_ball μ 0 hρ
        (subset_tsupport _ (Function.mem_support.mpr hyφ))
      simp [H, P, Set.indicator_apply, mem_ball_zero_iff.mp hyb]
  rw [integral_congr_ae (g := H.indicator φ)
      ((indicatorConstLp_coeFn (μ := μ) (p := 1) (hs := hHm) (hμs := hHfin) (c := (1 : ℝ))).mono
        fun y hy ↦ by rw [hy]; by_cases hyH : y ∈ H <;> simp [hyH]),
    hHP]
  exact (ballBump 0 hρ).setIntegral_normed_halfSpace μ fun h0 ↦ one_ne_zero (α := ℝ) <| by
    simpa [EuclideanSpace.basisFun_apply] using
      congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] ℝ ↦ L (EuclideanSpace.basisFun ι ℝ i)) h0

end Examples

end TauCeti
