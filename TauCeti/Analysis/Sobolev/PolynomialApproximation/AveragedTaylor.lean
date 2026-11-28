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
public import TauCeti.Analysis.Calculus.Taylor.Polynomial
public import TauCeti.MeasureTheory.Function.LocallyIntegrable
public import TauCeti.MeasureTheory.Function.Lp.Restriction
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.MeasureTheory.Function.Holder
import TauCeti.Algebra.BigOperators.Ring.Finset
import TauCeti.Analysis.Calculus.Taylor.Pairing.Basic
import TauCeti.LinearAlgebra.Multilinear.Basis
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.OddSymmetric

/-!
# The averaged Taylor polynomial on `L¹` and `Lᵖ`

Classically, `TauCeti.taylorPolynomial m u y x` requires `m` derivatives of `u` at `y` (in Lean it
defaults to `0` at non-differentiable steps, while integration by parts assumes ambient
`ContDiffAt ℝ m u y` at every `y ∈ tsupport φ`). Following Sobolev and Brenner–Scott
(Chapter 4, §4.1), averaging against a `C^m` compactly supported cutoff `φ` and integrating every
`y`-derivative onto `z ↦ (∏ l, (x (I l) - z (I l))) * φ z` yields the **averaged Taylor kernel**
`TauCeti.averagedTaylorKernel φ m x y`:

`Ψ_m(x, y) = ∑_{j = 0}^m ((-1)^j / j!) ∑_{I : Fin j → ι}
  D_{e_{I 0}, …, e_{I (j - 1)}} (z ↦ (∏ l, (x (I l) - z (I l))) * φ z) (y)`.

Because the derivatives act on the kernel rather than the input `f`, whenever `φ` is `C^m` with
compact support:

1. `x ↦ Ψ_m(x, y)` lies in `TauCeti.polynomialsDegLE ι m`.
2. Pairing against `Ψ_m` defines `TauCeti.averagedTaylorPolynomial : Lp ℝ 1 μ →L[ℝ]
   polynomialsDegLE ι m` for any Borel measure `μ`, and `TauCeti.averagedTaylorPolynomialLp :
   Lp ℝ p μ →L[ℝ] polynomialsDegLE ι m` (`[IsFiniteMeasureOnCompacts μ]`, `1 ≤ p`, agreeing with
   `averagedTaylorPolynomial` at `p = 1`).
3. Both operators expand into the weighted `iteratedFDeriv` pairing form matching
   `TauCeti.Wkp.fullContractL_iteratedGradientChain_sum_setIntegral_iteratedFDeriv`, using only
   `L¹`/`Lᵖ` membership and cutoff regularity.
4. On an additive Haar measure `μ`, when `u` is `C^m` at every point of `tsupport φ`, integration
   by parts gives `Q^m f (x) = ∫ y, taylorPolynomial m u y x * φ y ∂μ`, reproducing every
   `q ∈ polynomialsDegLE ι m` in `L¹(μ.restrict Ω)` / `Lᵖ(μ.restrict Ω)` whenever `tsupport φ ⊆ Ω`
   and `∫ y, φ y ∂μ = 1`.

Limit of polynomial reproduction: on `EuclideanSpace ℝ ι` with an additive Haar measure `μ` and an
even `C¹` compactly supported cutoff `φ` supported in `B`, `averagedTaylorPolynomial (μ.restrict B)
1 φ` sends `x ↦ (x i) ^ 2` (when `L¹` on `B`) to `-∫ y, (y i) ^ 2 * φ y ∂μ`
(`TauCeti.averagedTaylorPolynomial_sq_one_of_even`), so order-`1` averaging with
`(ballBump 0 hρ).normed μ` fails to reproduce `x ↦ (x i) ^ 2`
(`TauCeti.averagedTaylorPolynomial_normed_ballBump_sq_one_ne_self`), whereas
`averagedTaylorPolynomial_toLp_eq_self` reproduces any `L¹`-admissible quadratic at order `2`
whenever `∫ y, φ y ∂μ = 1` (in particular for `(ballBump 0 hρ).normed μ`).

## Main definitions

* `TauCeti.averagedTaylorKernelTerm`, `TauCeti.averagedTaylorKernel`: order-`j` summand
  (specializing `TauCeti.taylorKernelTerm` to `EuclideanSpace.basisFun`) and total kernel `Ψ_m`.
* `TauCeti.averagedTaylorPolynomial`, `TauCeti.averagedTaylorPolynomialLp`: continuous linear
  operators into `polynomialsDegLE ι m` on `L¹(μ)` and `Lᵖ(μ)` (`1 ≤ p`).

## Main results

* `TauCeti.averagedTaylorKernel_one`, `TauCeti.averagedTaylorKernel_mem_polynomialsDegLE`:
  explicit `m = 1` formula and polynomial-degree membership in `x`.
* `TauCeti.setIntegral_mul_averagedTaylorKernel_eq_sum_setIntegral_iteratedFDeriv`,
  `TauCeti.averagedTaylorPolynomial_eq_sum_integral_iteratedFDeriv`,
  `TauCeti.averagedTaylorPolynomial_restrict_eq_sum_setIntegral_iteratedFDeriv`,
  `TauCeti.averagedTaylorPolynomialLp_eq_sum_integral_iteratedFDeriv`,
  `TauCeti.averagedTaylorPolynomialLp_restrict_eq_sum_setIntegral_iteratedFDeriv`,
  `TauCeti.averagedTaylorPolynomialLp_one`: weighted `iteratedFDeriv` pairing identities and `p = 1`
  specialization.
* `TauCeti.integral_mul_averagedTaylorKernel_eq_integral_taylorPolynomial`,
  `TauCeti.averagedTaylorPolynomial_eq_integral_taylorPolynomial`,
  `TauCeti.averagedTaylorPolynomial_restrict_eq_integral_taylorPolynomial`,
  `TauCeti.averagedTaylorPolynomialLp_eq_integral_taylorPolynomial`,
  `TauCeti.averagedTaylorPolynomialLp_restrict_eq_integral_taylorPolynomial`,
  `TauCeti.averagedTaylorPolynomial_toLp_eq_self`,
  `TauCeti.averagedTaylorPolynomialLp_toLp_eq_self`:
  Haar-measure integration by parts and polynomial reproduction.
* `TauCeti.averagedTaylorPolynomial_sq_one_of_even`,
  `TauCeti.averagedTaylorPolynomial_normed_ballBump_sq_one_ne_self`,
  `TauCeti.averagedTaylorPolynomial_zero_halfBall_eq_half`: coordinate-quadratic and half-ball
  examples.

## References

* Susanne C. Brenner and L. Ridgway Scott, *The Mathematical Theory of Finite Element Methods*,
  3rd ed., Springer (2008), Chapter 4, §§4.1–4.2 (Definition 4.1.3 and Proposition 4.1.9).
-/

public section

noncomputable section

open Filter MeasureTheory Metric MvPolynomial Set
open scoped ContDiff ENNReal InnerProductSpace Topology

namespace TauCeti

section Kernel

variable {ι : Type*} [Fintype ι]

/-- List of coordinate basis directions `[e_{I 0}, …, e_{I (j - 1)}]` in `EuclideanSpace ℝ ι`. -/
private def coordDirections {j : ℕ} (I : Fin j → ι) : List (EuclideanSpace ℝ ι) :=
  List.ofFn fun l ↦ EuclideanSpace.basisFun ι ℝ (I l)

/-- Single-multi-index test function `z ↦ (∏ l, (x (I l) - z (I l))) * φ z` differentiated in
`averagedTaylorKernel`. -/
private def kernelTestTerm (φ : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι)
    {j : ℕ} (I : Fin j → ι) (z : EuclideanSpace ℝ ι) : ℝ :=
  (∏ l : Fin j, (x (I l) - z (I l))) * φ z

private theorem contDiff_kernelTestTerm {φ : EuclideanSpace ℝ ι → ℝ} {n : ℕ∞ω}
    (hφ : ContDiff ℝ n φ) (x : EuclideanSpace ℝ ι) {j : ℕ} (I : Fin j → ι) :
    ContDiff ℝ n (kernelTestTerm φ x I) :=
  (contDiff_prod fun l _ ↦ contDiff_const.sub (EuclideanSpace.proj (𝕜 := ℝ) (I l)).contDiff).mul hφ

/-- Order-`j` weighted summand of `averagedTaylorKernel`, specializing `TauCeti.taylorKernelTerm`
to the standard coordinate orthonormal basis `EuclideanSpace.basisFun ι ℝ`. -/
def averagedTaylorKernelTerm (φ : EuclideanSpace ℝ ι → ℝ) (j : ℕ)
    (x y : EuclideanSpace ℝ ι) : ℝ :=
  taylorKernelTerm (EuclideanSpace.basisFun ι ℝ) φ j x y

/-- Explicit coordinate formula for `averagedTaylorKernelTerm`. -/
theorem averagedTaylorKernelTerm_def (φ : EuclideanSpace ℝ ι → ℝ) (j : ℕ)
    (x y : EuclideanSpace ℝ ι) :
    averagedTaylorKernelTerm φ j x y =
      ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
        ∑ I : Fin j → ι,
          iteratedFDerivAlong ℝ (List.ofFn fun l ↦ EuclideanSpace.basisFun ι ℝ (I l))
            (fun z ↦ (∏ l : Fin j, (x (I l) - z (I l))) * φ z) y := by
  simp [averagedTaylorKernelTerm, taylorKernelTerm_def, EuclideanSpace.basisFun_inner,
    Function.comp_def]

/-- **Averaged Taylor kernel.** For a cutoff `φ : EuclideanSpace ℝ ι → ℝ`, order `m : ℕ`, target
point `x`, and integration variable `y`, `y ↦ averagedTaylorKernel φ m x y` is the formal adjoint
of `u ↦ (y ↦ taylorPolynomial m u y x)` applied to `φ`. -/
def averagedTaylorKernel (φ : EuclideanSpace ℝ ι → ℝ) (m : ℕ) (x y : EuclideanSpace ℝ ι) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), averagedTaylorKernelTerm φ j x y

theorem averagedTaylorKernel_def (φ : EuclideanSpace ℝ ι → ℝ) (m : ℕ)
    (x y : EuclideanSpace ℝ ι) :
    averagedTaylorKernel φ m x y =
      ∑ j ∈ Finset.range (m + 1), averagedTaylorKernelTerm φ j x y := by rfl

/-- At order `0`, the averaged Taylor kernel is simply `φ y` (independent of `x`). -/
@[simp]
theorem averagedTaylorKernel_zero (φ : EuclideanSpace ℝ ι → ℝ) (x y : EuclideanSpace ℝ ι) :
    averagedTaylorKernel φ 0 x y = φ y := by
  simp [averagedTaylorKernel_def, averagedTaylorKernelTerm]

/-- Recurrence separating the top-order derivative sum of `averagedTaylorKernel`. -/
theorem averagedTaylorKernel_succ (φ : EuclideanSpace ℝ ι → ℝ) (m : ℕ)
    (x y : EuclideanSpace ℝ ι) :
    averagedTaylorKernel φ (m + 1) x y =
      averagedTaylorKernel φ m x y + averagedTaylorKernelTerm φ (m + 1) x y := by
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
    have hderiv := ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y i).const_sub (x i)).fun_mul hφ.hasFDerivAt
    simp [hderiv.fderiv, b, EuclideanSpace.basisFun_apply]; ring
  have hlin : ∑ i : ι, (x i - y i) * fderiv ℝ φ y (b i) = fderiv ℝ φ y (x - y) := by
    conv_rhs => rw [← b.sum_repr (x - y), map_sum]
    simp [b]
  rw [averagedTaylorKernel_succ, averagedTaylorKernel_zero, averagedTaylorKernelTerm_def,
    hsum, Finset.sum_sub_distrib, hlin]
  simp; ring

/-- For every target point `x`, the support in `y` of `averagedTaylorKernel φ m x` is contained in
`tsupport φ`. -/
theorem tsupport_averagedTaylorKernel_subset (φ : EuclideanSpace ℝ ι → ℝ) (m : ℕ)
    (x : EuclideanSpace ℝ ι) :
    tsupport (averagedTaylorKernel φ m x) ⊆ tsupport φ := by
  refine closure_minimal (fun y hy ↦ by_contra fun hyφ ↦ Function.mem_support.mp hy ?_)
    (isClosed_tsupport φ)
  rw [averagedTaylorKernel_def]
  exact Finset.sum_eq_zero fun j _ ↦ image_eq_zero_of_notMem_tsupport fun h ↦
    hyφ (tsupport_taylorKernelTerm_subset (EuclideanSpace.basisFun ι ℝ) φ j x h)

/-- Compact support of `φ` passes to `y ↦ averagedTaylorKernel φ m x y` for every `x`. -/
theorem hasCompactSupport_averagedTaylorKernel {φ : EuclideanSpace ℝ ι → ℝ}
    (hsupp : HasCompactSupport φ) (m : ℕ) (x : EuclideanSpace ℝ ι) :
    HasCompactSupport (averagedTaylorKernel φ m x) :=
  hsupp.of_isClosed_subset (isClosed_tsupport _) (tsupport_averagedTaylorKernel_subset φ m x)

/-- If `φ` is `C^n` and `k + m ≤ n`, then `y ↦ averagedTaylorKernel φ m x y` is `C^k`. -/
theorem contDiff_averagedTaylorKernel_right {φ : EuclideanSpace ℝ ι → ℝ} {n k : ℕ∞ω} {m : ℕ}
    (hφ : ContDiff ℝ n φ) (hkm : k + m ≤ n) (x : EuclideanSpace ℝ ι) :
    ContDiff ℝ k (averagedTaylorKernel φ m x) := by
  unfold averagedTaylorKernel averagedTaylorKernelTerm
  exact ContDiff.sum fun j hj ↦ contDiff_taylorKernelTerm_right (EuclideanSpace.basisFun ι ℝ) hφ
    ((add_le_add_right (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) k).trans
      hkm) x

/-- If `φ` is `C^m`, then `y ↦ averagedTaylorKernel φ m x y` is continuous for every `x`. -/
theorem continuous_averagedTaylorKernel_right {φ : EuclideanSpace ℝ ι → ℝ} {m : ℕ}
    (hφ : ContDiff ℝ m φ) (x : EuclideanSpace ℝ ι) :
    Continuous (averagedTaylorKernel φ m x) :=
  (contDiff_averagedTaylorKernel_right (k := 0) hφ (by simp) x).continuous

/-- Undifferentiated `x`-independent factor in the monomial expansion of `taylorKernelTerm`. -/
private def kernelMonomialTerm (φ : EuclideanSpace ℝ ι → ℝ) {j : ℕ} (I : Fin j → ι)
    (S : Finset (Fin j)) (z : EuclideanSpace ℝ ι) : ℝ :=
  (∏ l ∈ Finset.univ \ S, -⟪EuclideanSpace.basisFun ι ℝ (I l), z⟫_ℝ) * φ z

private theorem contDiff_kernelMonomialTerm {φ : EuclideanSpace ℝ ι → ℝ} {n : ℕ∞ω}
    (hφ : ContDiff ℝ n φ) {j : ℕ} (I : Fin j → ι) (S : Finset (Fin j)) :
    ContDiff ℝ n (kernelMonomialTerm φ I S) :=
  ((contDiff_prod fun l _ ↦
    (innerSL ℝ (EuclideanSpace.basisFun ι ℝ (I l))).contDiff.neg).of_le le_top).mul hφ

/-- Auxiliary `x`-independent weight appearing when `∏ l, (x (I l) - z (I l))` is expanded into
monomials in `x`. -/
private def kernelMonomialWeight (φ : EuclideanSpace ℝ ι → ℝ) {j : ℕ} (I : Fin j → ι)
    (S : Finset (Fin j)) (y : EuclideanSpace ℝ ι) : ℝ :=
  iteratedFDerivAlong ℝ (List.ofFn (EuclideanSpace.basisFun ι ℝ ∘ I))
    (kernelMonomialTerm φ I S) y

private theorem contDiff_kernelMonomialWeight {φ : EuclideanSpace ℝ ι → ℝ} {m j : ℕ}
    (hφ : ContDiff ℝ m φ) (hj : j ≤ m) (I : Fin j → ι) (S : Finset (Fin j)) :
    ContDiff ℝ 0 (kernelMonomialWeight φ I S) :=
  (contDiff_kernelMonomialTerm hφ I S).iteratedFDerivAlong _ (by simp [hj])

private theorem hasCompactSupport_kernelMonomialWeight {φ : EuclideanSpace ℝ ι → ℝ}
    (hsupp : HasCompactSupport φ) {j : ℕ} (I : Fin j → ι) (S : Finset (Fin j)) :
    HasCompactSupport (kernelMonomialWeight φ I S) :=
  (hsupp.mul_left).iteratedFDerivAlong ℝ _

/-- Monomial expansion of `averagedTaylorKernel φ m x y` separating the `x`-monomials from the
`y`-weights, reusing `TauCeti.iteratedFDerivAlong_prod_inner_sub_mul_eq_sum`. -/
private theorem averagedTaylorKernel_eq_sum_monomial {φ : EuclideanSpace ℝ ι → ℝ} {m : ℕ}
    (hφ : ContDiff ℝ m φ) (x y : EuclideanSpace ℝ ι) :
    averagedTaylorKernel φ m x y =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
        ∑ I : Fin j → ι, ∑ S ∈ (Finset.univ : Finset (Fin j)).powerset,
          (∏ l ∈ S, x (I l)) * kernelMonomialWeight φ I S y := by
  simp_rw [averagedTaylorKernel, averagedTaylorKernelTerm, taylorKernelTerm_def]
  refine Finset.sum_congr rfl fun j hj ↦ congrArg _ (Finset.sum_congr rfl fun I _ ↦ ?_)
  have hlen : (List.ofFn (EuclideanSpace.basisFun ι ℝ ∘ I)).length ≤ (m : ℕ∞ω) := by
    simp only [List.length_ofFn, Nat.cast_le]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [show List.ofFn (⇑(EuclideanSpace.basisFun ι ℝ) ∘ I) =
      List.ofFn (fun l ↦ EuclideanSpace.basisFun ι ℝ (I l)) from rfl,
    iteratedFDerivAlong_prod_inner_sub_mul_eq_sum (𝕜 := ℝ) Finset.univ
      (fun l ↦ EuclideanSpace.basisFun ι ℝ (I l)) hφ
      (List.ofFn fun l ↦ EuclideanSpace.basisFun ι ℝ (I l)) hlen x y]
  refine Finset.sum_congr rfl fun S _ ↦ congrArg (· * kernelMonomialWeight φ I S y) ?_
  simp [EuclideanSpace.basisFun_inner]

/-- Monomial basis function `x ↦ ∏ l ∈ S, x (I l)` packaged in `polynomialsDegLE ι m` for
`j ≤ m`. -/
private def kernelMonomialElem (m : ℕ) {j : ℕ} (hj : j ≤ m) (I : Fin j → ι)
    (S : Finset (Fin j)) : polynomialsDegLE ι m :=
  ⟨fun x ↦ ∏ l ∈ S, x (I l),
    polynomialsDegLE_mono ι ((Finset.card_le_univ S).trans (by simpa using hj))
      (prod_coord_mem_polynomialsDegLE S I)⟩

/-- Shared weighted `(j, I, S)` monomial assembler for both scalar coefficients (into
`polynomialsDegLE ι m`) and continuous-linear coefficients (into `F →L[ℝ] polynomialsDegLE ι m`). -/
private def assembleKernelMonomial {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (m : ℕ) (term : ∀ j : Fin (m + 1), (Fin j → ι) → Finset (Fin j) → M) : M :=
  ∑ j : Fin (m + 1), ((-1 : ℝ) ^ (j : ℕ) / ((j : ℕ).factorial : ℝ)) •
    ∑ I : Fin j → ι, ∑ S ∈ (Finset.univ : Finset (Fin j)).powerset, term j I S

/-- Pointwise evaluation of the scalar monomial assembler. -/
private theorem assembleKernelMonomial_apply (m : ℕ)
    (coeff : ∀ j : Fin (m + 1), (Fin j → ι) → Finset (Fin j) → ℝ) (x : EuclideanSpace ℝ ι) :
    ((assembleKernelMonomial (M := polynomialsDegLE ι m) m (fun j I S ↦
        coeff j I S • kernelMonomialElem m (Nat.le_of_lt_succ j.isLt) I S) :
      polynomialsDegLE ι m) : EuclideanSpace ℝ ι → ℝ) x =
      ∑ j : Fin (m + 1), ((-1 : ℝ) ^ (j : ℕ) / ((j : ℕ).factorial : ℝ)) *
        ∑ I : Fin j → ι, ∑ S ∈ (Finset.univ : Finset (Fin j)).powerset,
          (∏ l ∈ S, x (I l)) * coeff j I S := by
  simp only [assembleKernelMonomial, Submodule.coe_sum, Finset.sum_apply,
    SetLike.val_smul, Pi.smul_apply, smul_eq_mul, kernelMonomialElem, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun I _ ↦
    Finset.sum_congr rfl fun S _ ↦ by ring

/-- Pointwise evaluation of the continuous-linear-map monomial assembler via `smulRight`. -/
private theorem assembleKernelMonomial_clm_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (m : ℕ)
    (coeff : ∀ j : Fin (m + 1), (Fin j → ι) → Finset (Fin j) → (F →L[ℝ] ℝ))
    (f : F) (x : EuclideanSpace ℝ ι) :
    ((assembleKernelMonomial m (fun j I S ↦
        (coeff j I S).smulRight (kernelMonomialElem m (Nat.le_of_lt_succ j.isLt) I S)) f :
      polynomialsDegLE ι m) : EuclideanSpace ℝ ι → ℝ) x =
      ((assembleKernelMonomial (M := polynomialsDegLE ι m) m (fun j I S ↦
        (coeff j I S f) • kernelMonomialElem m (Nat.le_of_lt_succ j.isLt) I S) :
        polynomialsDegLE ι m) : EuclideanSpace ℝ ι → ℝ) x := by
  simp [assembleKernelMonomial]

/-- For every fixed `y`, if `φ` is `C^m`, the map `x ↦ averagedTaylorKernel φ m x y` is a
polynomial of total degree at most `m`. -/
theorem averagedTaylorKernel_mem_polynomialsDegLE {φ : EuclideanSpace ℝ ι → ℝ} {m : ℕ}
    (hφ : ContDiff ℝ m φ) (y : EuclideanSpace ℝ ι) :
    (fun x ↦ averagedTaylorKernel φ m x y) ∈ polynomialsDegLE ι m := by
  let P : polynomialsDegLE ι m := assembleKernelMonomial m fun j I S ↦
    kernelMonomialWeight φ I S y • kernelMonomialElem m (Nat.le_of_lt_succ j.isLt) I S
  convert P.property using 1
  ext x; dsimp only [P]
  rw [averagedTaylorKernel_eq_sum_monomial hφ, ← Fin.sum_univ_eq_sum_range,
    assembleKernelMonomial_apply]

end Kernel

section Operator

variable {ι : Type*} [Fintype ι]

private theorem memLp_top_kernelMonomialWeight (μ : Measure (EuclideanSpace ℝ ι)) {m j : ℕ}
    {φ : EuclideanSpace ℝ ι → ℝ} (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (hj : j ≤ m) (I : Fin j → ι) (S : Finset (Fin j)) :
    MemLp (kernelMonomialWeight φ I S) ∞ μ :=
  (contDiff_kernelMonomialWeight hφ hj I S).continuous.memLp_top_of_hasCompactSupport
    (hasCompactSupport_kernelMonomialWeight hsupp I S) μ

/-- Monomial expansion of `x ↦ ∫ y, f y * averagedTaylorKernel φ m x y ∂μ`, applying
`TauCeti.setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_sum` termwise on `Set.univ`. -/
private theorem integral_mul_averagedTaylorKernel_eq_sum_monomial
    {μ : Measure (EuclideanSpace ℝ ι)} {m : ℕ} {φ f : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hf : Integrable f μ) :
    (fun x ↦ ∫ y, f y * averagedTaylorKernel φ m x y ∂μ) =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) •
        ∑ I : Fin j → ι, ∑ S ∈ (Finset.univ : Finset (Fin j)).powerset,
          (∫ y, f y * kernelMonomialWeight φ I S y ∂μ) •
            fun x : EuclideanSpace ℝ ι ↦ ∏ l ∈ S, x (I l) := by
  let b := EuclideanSpace.basisFun ι ℝ
  ext x
  have hlen (j : ℕ) (hj : j ∈ Finset.range (m + 1)) (I : Fin j → ι) :
      (List.ofFn fun l ↦ b (I l)).length ≤ (m : ℕ∞ω) := by
    simp only [List.length_ofFn, Nat.cast_le]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hint (j : ℕ) (hj : j ∈ Finset.range (m + 1)) (I : Fin j → ι) :
      Integrable (fun y ↦ iteratedFDerivAlong ℝ (List.ofFn fun l ↦ b (I l))
        (fun z ↦ (∏ l : Fin j, ⟪b (I l), x - z⟫_ℝ) * φ z) y * f y) μ := by
    have hcont : ContDiff ℝ 0 (iteratedFDerivAlong ℝ (List.ofFn fun l ↦ b (I l))
        (fun z ↦ (∏ l : Fin j, ⟪b (I l), x - z⟫_ℝ) * φ z)) :=
      (((contDiff_prod fun l _ ↦ (innerSL ℝ (b (I l))).contDiff.comp
        (contDiff_const.sub contDiff_id)).of_le le_top).mul hφ).iteratedFDerivAlong _
        (by simpa only [zero_add] using hlen j hj I)
    exact (hf.mul_of_top_left (hcont.continuous.memLp_top_of_hasCompactSupport
      (hsupp.mul_left.iteratedFDerivAlong ℝ _) μ)).congr (.of_forall fun _ ↦ mul_comm _ _)
  have hpt (y : EuclideanSpace ℝ ι) : f y * averagedTaylorKernel φ m x y =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
        ∑ I : Fin j → ι, iteratedFDerivAlong ℝ (List.ofFn fun l ↦ b (I l))
          (fun z ↦ (∏ l : Fin j, ⟪b (I l), x - z⟫_ℝ) * φ z) y * f y := by
    rw [averagedTaylorKernel, mul_comm (f y)]
    simp_rw [averagedTaylorKernelTerm, taylorKernelTerm_def, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [mul_assoc, Finset.sum_mul]; rfl
  simp_rw [hpt]
  rw [MeasureTheory.integral_sum_mul_sum (Finset.range (m + 1))
    (fun j ↦ (Finset.univ : Finset (Fin j → ι)))
    (fun j ↦ (-1 : ℝ) ^ j / (j.factorial : ℝ)) _ fun j hj I _ ↦ hint j hj I]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j hj ↦ congrArg _ (Finset.sum_congr rfl fun I _ ↦ ?_)
  rw [← setIntegral_univ, setIntegral_iteratedFDerivAlong_prod_inner_sub_mul_eq_sum (𝕜 := ℝ)
    Finset.univ (fun l ↦ b (I l)) hφ hsupp (subset_univ _) (List.ofFn fun l ↦ b (I l))
    (hlen j hj I) (hf.locallyIntegrable.locallyIntegrableOn Set.univ) x]
  simp_rw [setIntegral_univ, b]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  have hS : (∏ l ∈ S, ⟪EuclideanSpace.basisFun ι ℝ (I l), x⟫_ℝ) = ∏ l ∈ S, x (I l) := by
    simp [EuclideanSpace.basisFun_inner]
  rw [hS, mul_comm (∏ l ∈ S, x (I l))]
  congr 1; exact integral_congr_ae (.of_forall fun _ ↦ mul_comm _ _)

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

/-- Express pairing against `averagedTaylorKernel` on a set `s` containing `tsupport φ` in the
weighted `iteratedFDeriv` pairing form matching
`TauCeti.Wkp.fullContractL_iteratedGradientChain_sum_setIntegral_iteratedFDeriv`,
assuming only local integrability of `f` on `s` and `C^m` compact support of `φ`. -/
theorem setIntegral_mul_averagedTaylorKernel_eq_sum_setIntegral_iteratedFDeriv
    {μ : Measure (EuclideanSpace ℝ ι)} {s : Set (EuclideanSpace ℝ ι)}
    {m : ℕ} {φ f : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hs : tsupport φ ⊆ s)
    (hf : LocallyIntegrableOn f s μ) (x : EuclideanSpace ℝ ι) :
    ∫ y in s, f y * averagedTaylorKernel φ m x y ∂μ =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
        ∑ I : Fin j → ι, ∫ y in s,
          iteratedFDeriv ℝ j (fun z ↦
            (∏ l : Fin j, ⟪EuclideanSpace.basisFun ι ℝ (I l), x - z⟫_ℝ) * φ z)
            y (EuclideanSpace.basisFun ι ℝ ∘ I) * f y ∂μ := by
  have hint (j : ℕ) (hj : j ∈ Finset.range (m + 1)) :
      IntegrableOn (fun y ↦ averagedTaylorKernelTerm φ j x y * f y) s μ := by
    have hjm : (j : ℕ∞ω) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact (hf.integrable_smul_left_of_hasCompactSupport
      (contDiff_taylorKernelTerm_right (EuclideanSpace.basisFun ι ℝ) hφ
        (by rw [zero_add]; exact hjm) x).continuous.continuousOn
      (hasCompactSupport_taylorKernelTerm (EuclideanSpace.basisFun ι ℝ) hsupp j x)
      ((tsupport_taylorKernelTerm_subset (EuclideanSpace.basisFun ι ℝ) φ j x).trans
        hs)).integrableOn
  have hpt : (fun y ↦ f y * averagedTaylorKernel φ m x y) = fun y ↦
      ∑ j ∈ Finset.range (m + 1), averagedTaylorKernelTerm φ j x y * f y := funext fun y ↦ by
    rw [mul_comm, averagedTaylorKernel_def, Finset.sum_mul]
  rw [hpt, integral_finsetSum _ fun j hj ↦ hint j hj]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjm : (j : ℕ∞ω) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact setIntegral_taylorKernelTerm_mul_eq (EuclideanSpace.basisFun ι ℝ) (hφ.of_le hjm) hsupp hs
    hf x

/-- Scalar continuous linear functional `f ↦ ∫ y, f y * kernelMonomialWeight φ I S y ∂μ` via
Mathlib's `L¹`–`L^∞` Hölder pairing `ContinuousLinearMap.lpPairing`. -/
private def kernelMonomialPairing (μ : Measure (EuclideanSpace ℝ ι)) (m : ℕ)
    {φ : EuclideanSpace ℝ ι → ℝ} (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    {j : ℕ} (hj : j ≤ m) (I : Fin j → ι) (S : Finset (Fin j)) :
    Lp ℝ 1 μ →L[ℝ] ℝ :=
  ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ 1 (∞ : ℝ≥0∞)).flip
    ((memLp_top_kernelMonomialWeight μ hφ hsupp hj I S).toLp (kernelMonomialWeight φ I S))

private theorem kernelMonomialPairing_apply (μ : Measure (EuclideanSpace ℝ ι)) (m : ℕ)
    {φ : EuclideanSpace ℝ ι → ℝ} (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    {j : ℕ} (hj : j ≤ m) (I : Fin j → ι) (S : Finset (Fin j)) (f : Lp ℝ 1 μ) :
    kernelMonomialPairing μ m hφ hsupp hj I S f =
      ∫ y, f y * kernelMonomialWeight φ I S y ∂μ := by
  rw [kernelMonomialPairing, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  exact integral_congr_ae
    ((memLp_top_kernelMonomialWeight μ hφ hsupp hj I S).coeFn_toLp.mono fun y hy ↦ by
      simp [hy])

/-- **The averaged Taylor polynomial on `L¹`.** For any Borel measure `μ` on `EuclideanSpace ℝ ι`
and any `C^m` compactly supported cutoff `φ`, this continuous linear map into
`polynomialsDegLE ι m` sends `f ∈ Lp ℝ 1 μ` to the polynomial whose value at `x` is
`∫ y, f y * averagedTaylorKernel φ m x y ∂μ` (`TauCeti.averagedTaylorPolynomial_apply`),
constructed by pairing `f` against each `kernelMonomialWeight` and lifting via
`ContinuousLinearMap.smulRight`. -/
def averagedTaylorPolynomial (μ : Measure (EuclideanSpace ℝ ι)) (m : ℕ)
    (φ : EuclideanSpace ℝ ι → ℝ) (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) :
    Lp ℝ 1 μ →L[ℝ] polynomialsDegLE ι m :=
  assembleKernelMonomial m fun j I S ↦
    (kernelMonomialPairing μ m hφ hsupp (Nat.le_of_lt_succ j.isLt) I S).smulRight
      (kernelMonomialElem m (Nat.le_of_lt_succ j.isLt) I S)

/-- Pointwise evaluation formula for `averagedTaylorPolynomial`. -/
@[simp]
theorem averagedTaylorPolynomial_apply (μ : Measure (EuclideanSpace ℝ ι)) (m : ℕ)
    (φ : EuclideanSpace ℝ ι → ℝ) (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (f : Lp ℝ 1 μ) (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomial μ m φ hφ hsupp f : EuclideanSpace ℝ ι → ℝ) x =
      ∫ y, f y * averagedTaylorKernel φ m x y ∂μ := by
  have hexp := congrFun (integral_mul_averagedTaylorKernel_eq_sum_monomial hφ hsupp
    (L1.integrable_coeFn f)) x
  rw [averagedTaylorPolynomial, assembleKernelMonomial_clm_apply, assembleKernelMonomial_apply,
    hexp, ← Fin.sum_univ_eq_sum_range]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, kernelMonomialPairing_apply]
  exact Finset.sum_congr rfl fun j _ ↦ congrArg _ (Finset.sum_congr rfl fun I _ ↦
    Finset.sum_congr rfl fun S _ ↦ mul_comm _ _)

/-- Weighted `iteratedFDeriv` pairing evaluation formula for `averagedTaylorPolynomial` on
`L¹(μ)`, requiring only `L¹` membership and cutoff regularity. -/
theorem averagedTaylorPolynomial_eq_sum_integral_iteratedFDeriv
    (μ : Measure (EuclideanSpace ℝ ι)) (m : ℕ)
    (φ : EuclideanSpace ℝ ι → ℝ) (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (f : Lp ℝ 1 μ) (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomial μ m φ hφ hsupp f : EuclideanSpace ℝ ι → ℝ) x =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
        ∑ I : Fin j → ι, ∫ y,
          iteratedFDeriv ℝ j (fun z ↦
            (∏ l : Fin j, ⟪EuclideanSpace.basisFun ι ℝ (I l), x - z⟫_ℝ) * φ z)
            y (EuclideanSpace.basisFun ι ℝ ∘ I) * f y ∂μ := by
  rw [averagedTaylorPolynomial_apply, ← setIntegral_univ,
    setIntegral_mul_averagedTaylorKernel_eq_sum_setIntegral_iteratedFDeriv hφ hsupp
      (subset_univ _) ((L1.integrable_coeFn f).locallyIntegrable.locallyIntegrableOn Set.univ) x]
  simp_rw [setIntegral_univ]

/-- Weighted `iteratedFDeriv` pairing evaluation formula for `averagedTaylorPolynomial` on
`L¹(μ.restrict Ω)` when `tsupport φ ⊆ Ω`, matching
`TauCeti.Wkp.fullContractL_iteratedGradientChain_sum_setIntegral_iteratedFDeriv`. -/
theorem averagedTaylorPolynomial_restrict_eq_sum_setIntegral_iteratedFDeriv
    {μ : Measure (EuclideanSpace ℝ ι)} {Ω : Set (EuclideanSpace ℝ ι)} {m : ℕ}
    {φ : EuclideanSpace ℝ ι → ℝ} (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (hΩ : tsupport φ ⊆ Ω) (f : Lp ℝ 1 (μ.restrict Ω)) (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomial (μ.restrict Ω) m φ hφ hsupp f : EuclideanSpace ℝ ι → ℝ) x =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
        ∑ I : Fin j → ι, ∫ y in Ω,
          iteratedFDeriv ℝ j (fun z ↦
            (∏ l : Fin j, ⟪EuclideanSpace.basisFun ι ℝ (I l), x - z⟫_ℝ) * φ z)
            y (EuclideanSpace.basisFun ι ℝ ∘ I) * f y ∂μ := by
  rw [averagedTaylorPolynomial_apply]
  exact setIntegral_mul_averagedTaylorKernel_eq_sum_setIntegral_iteratedFDeriv hφ hsupp hΩ
    (locallyIntegrableOn_of_locallyIntegrable_restrict (L1.integrable_coeFn f).locallyIntegrable)
    x

/-- If `φ` is `C^m` and compactly supported, integrating any `Integrable f μ` against
`averagedTaylorKernel φ m` produces a polynomial of total degree at most `m`. -/
theorem integral_mul_averagedTaylorKernel_mem_polynomialsDegLE
    {μ : Measure (EuclideanSpace ℝ ι)} {m : ℕ} {φ f : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hf : Integrable f μ) :
    (fun x ↦ ∫ y, f y * averagedTaylorKernel φ m x y ∂μ) ∈ polynomialsDegLE ι m := by
  have hf1 : MemLp f 1 μ := memLp_one_iff_integrable.mpr hf
  have heq : (fun x ↦ ∫ y, f y * averagedTaylorKernel φ m x y ∂μ) =
      (averagedTaylorPolynomial μ m φ hφ hsupp (hf1.toLp f) : EuclideanSpace ℝ ι → ℝ) := by
    ext x
    rw [averagedTaylorPolynomial_apply]
    exact integral_congr_ae (hf1.coeFn_toLp.mono fun y hy ↦ by dsimp only; rw [hy])
  rw [heq]
  exact (averagedTaylorPolynomial μ m φ hφ hsupp (hf1.toLp f)).property

section AddHaar

variable {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]

private theorem integrable_mul_iteratedFDerivAlong_kernelTestTerm
    {m j : ℕ} {φ u : EuclideanSpace ℝ ι → ℝ} (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y) (hj : j ≤ m) (x : EuclideanSpace ℝ ι)
    (I : Fin j → ι) :
    Integrable
      (fun y ↦ u y * iteratedFDerivAlong ℝ (coordDirections I) (kernelTestTerm φ x I) y) μ := by
  unfold kernelTestTerm
  have hcont : ContDiff ℝ m (fun z ↦ (∏ l : Fin j, (x (I l) - z (I l))) * φ z) :=
    contDiff_kernelTestTerm hφ x I
  simpa only [smul_eq_mul] using
    (hcont.iteratedFDerivAlong (m := 0) (coordDirections I)
      (by simp only [coordDirections, List.length_ofFn, zero_add]; exact_mod_cast hj)).continuous
      |>.integrable_smul_of_continuousOn (hsupp.mul_left.iteratedFDerivAlong ℝ _)
      ((tsupport_iteratedFDerivAlong_subset ℝ _ _).trans tsupport_mul_subset_right)
      fun y hy ↦ (hu y hy).continuousAt.continuousWithinAt

private theorem integrable_iteratedFDeriv_mul_kernelTestTerm
    {m j : ℕ} {φ u : EuclideanSpace ℝ ι → ℝ} (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y) (hj : j ≤ m) (x : EuclideanSpace ℝ ι)
    (I : Fin j → ι) :
    Integrable (fun y ↦
      iteratedFDeriv ℝ j u y (fun l ↦ EuclideanSpace.basisFun ι ℝ (I l)) *
        kernelTestTerm φ x I y) μ := by
  unfold kernelTestTerm
  have ha : ContinuousOn (fun y ↦
      iteratedFDeriv ℝ j u y (fun l ↦ EuclideanSpace.basisFun ι ℝ (I l))) (tsupport φ) :=
    fun y hy ↦ ((continuous_eval_const _).continuousAt.comp
      ((hu y hy).continuousAt_iteratedFDeriv (by exact_mod_cast hj))).continuousWithinAt
  simpa only [smul_eq_mul, kernelTestTerm] using
    (contDiff_kernelTestTerm hφ x I).continuous.integrable_smul_of_continuousOn
      hsupp.mul_left tsupport_mul_subset_right ha

/-- Single-`(j, I)` integration-by-parts identity moving `coordDirections I` from
`kernelTestTerm φ x I` onto `u` and identifying the reversed directional derivative with
`iteratedFDeriv ℝ j u y`. -/
private theorem averagedTaylor_ibp_term
    {m j : ℕ} {φ u : EuclideanSpace ℝ ι → ℝ} (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y) (hj : j ≤ m) (x : EuclideanSpace ℝ ι)
    (I : Fin j → ι) :
    ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
      (∫ y, u y * iteratedFDerivAlong ℝ (coordDirections I) (kernelTestTerm φ x I) y ∂μ) =
    (j.factorial : ℝ)⁻¹ * ∫ y,
      iteratedFDeriv ℝ j u y (fun l ↦ EuclideanSpace.basisFun ι ℝ (I l)) *
        kernelTestTerm φ x I y ∂μ := by
  unfold kernelTestTerm
  set b := EuclideanSpace.basisFun ι ℝ
  have hlen : (coordDirections I).length = j := List.length_ofFn
  have hibp := integral_mul_iteratedFDerivAlong_eq (μ := μ) (coordDirections I)
    (f := u) (g := fun z ↦ (∏ l : Fin j, (x (I l) - z (I l))) * φ z)
    (fun y hy ↦ by
      rw [hlen]; exact (hu y (tsupport_mul_subset_right hy)).of_le (by exact_mod_cast hj))
    ((contDiff_kernelTestTerm hφ x I).of_le (by rw [hlen]; exact_mod_cast hj)) hsupp.mul_left
  rw [hlen] at hibp
  have hpt : (fun y ↦
      iteratedFDerivAlong ℝ (coordDirections I).reverse u y *
        ((∏ l : Fin j, (x (I l) - y (I l))) * φ y)) =
      fun y ↦ iteratedFDeriv ℝ j u y (fun l ↦ b (I l)) *
        ((∏ l : Fin j, (x (I l) - y (I l))) * φ y) := by
    ext y; by_cases hy : y ∈ tsupport φ
    · have huy : ContDiffAt ℝ j u y := (hu y hy).of_le (by exact_mod_cast hj)
      rw [(List.reverse_perm (coordDirections I)).iteratedFDerivAlong_eq_of_contDiffAt huy
          (by simp [List.length_reverse, hlen])]
      simp only [coordDirections, huy.iteratedFDerivAlong_ofFn_eq_iteratedFDeriv le_rfl, b]
    · simp [image_eq_zero_of_notMem_tsupport hy]
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
    simp_rw [averagedTaylorKernel_def, averagedTaylorKernelTerm_def]
    rw [Finset.mul_sum_mul_sum (Finset.range (m + 1)) (fun j ↦ (Finset.univ : Finset (Fin j → ι)))
      (fun j ↦ (-1 : ℝ) ^ j / (j.factorial : ℝ)) (u y)]
    rfl
  simp_rw [hpt]
  exact MeasureTheory.integral_sum_mul_sum (Finset.range (m + 1))
    (fun j ↦ (Finset.univ : Finset (Fin j → ι)))
    (fun j ↦ (-1 : ℝ) ^ j / (j.factorial : ℝ))
    (fun j I y ↦ u y * iteratedFDerivAlong ℝ (coordDirections I) (kernelTestTerm φ x I) y)
    fun j hj I _ ↦ integrable_mul_iteratedFDerivAlong_kernelTestTerm hφ hsupp hu
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) x I

/-- **Kernel-adjoint identity for the averaged Taylor kernel.** On `EuclideanSpace ℝ ι` with an
additive Haar measure `μ`, if `φ` is `C^m` with compact support and `u` is `C^m` at every point of
`tsupport φ`, then pairing `u` against `averagedTaylorKernel φ m x` recovers the cutoff average of
the classical `m`-th Taylor polynomial of `u`. -/
theorem integral_mul_averagedTaylorKernel_eq_integral_taylorPolynomial
    {m : ℕ} {φ u : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y) (x : EuclideanSpace ℝ ι) :
    ∫ y, u y * averagedTaylorKernel φ m x y ∂μ =
      ∫ y, taylorPolynomial m u y x * φ y ∂μ := by
  rw [integral_mul_averagedTaylorKernel_eq_sum_ibp hφ hsupp hu x]
  calc
    -- Move derivatives from `kernelTestTerm` onto `u` term by term.
    (∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
        ∑ I : Fin j → ι, ∫ y,
          u y * iteratedFDerivAlong ℝ (coordDirections I) (kernelTestTerm φ x I) y ∂μ)
      = ∑ j ∈ Finset.range (m + 1), (j.factorial : ℝ)⁻¹ *
          ∑ I : Fin j → ι,
            ∫ y, iteratedFDeriv ℝ j u y (fun l ↦ EuclideanSpace.basisFun ι ℝ (I l)) *
              kernelTestTerm φ x I y ∂μ :=
        Finset.sum_congr rfl fun j hj ↦ by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun I _ ↦ averagedTaylor_ibp_term hφ hsupp hu
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) x I
    -- Pull the finite `(j, I)` sums back inside the integral.
    _ = ∫ y, (∑ j ∈ Finset.range (m + 1), (j.factorial : ℝ)⁻¹ *
          ∑ I : Fin j → ι,
            iteratedFDeriv ℝ j u y (fun l ↦ EuclideanSpace.basisFun ι ℝ (I l)) *
              kernelTestTerm φ x I y) ∂μ :=
        (MeasureTheory.integral_sum_mul_sum (Finset.range (m + 1))
          (fun j ↦ (Finset.univ : Finset (Fin j → ι))) (fun j ↦ (j.factorial : ℝ)⁻¹)
          (fun j I y ↦ iteratedFDeriv ℝ j u y (fun l ↦ EuclideanSpace.basisFun ι ℝ (I l)) *
            kernelTestTerm φ x I y)
          fun j hj I _ ↦ integrable_iteratedFDeriv_mul_kernelTestTerm hφ hsupp hu
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) x I).symm
    -- Reassemble the coordinate sums into `taylorPolynomial m u y x * φ y`.
    _ = ∫ y, taylorPolynomial m u y x * φ y ∂μ := by
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
        rw [smul_eq_mul, hcoord, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun I _ ↦ by simp only [kernelTestTerm]; ring

/-- Shared representative-replacement and kernel-adjoint step on `μ.restrict s`
(`tsupport φ ⊆ s`). -/
private theorem setIntegral_mul_averagedTaylorKernel_eq_integral_taylorPolynomial_of_ae_eq
    {s : Set (EuclideanSpace ℝ ι)} {m : ℕ} {φ f u : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hs : tsupport φ ⊆ s)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y)
    (hf : f =ᵐ[μ.restrict s] u) (x : EuclideanSpace ℝ ι) :
    ∫ y in s, f y * averagedTaylorKernel φ m x y ∂μ =
      ∫ y, taylorPolynomial m u y x * φ y ∂μ := by
  rw [integral_congr_ae (hf.mono fun y hy ↦ congrArg (· * averagedTaylorKernel φ m x y) hy),
    setIntegral_mul_averagedTaylorKernel_eq_integral hs]
  exact integral_mul_averagedTaylorKernel_eq_integral_taylorPolynomial hφ hsupp hu x

/-- **Integration-by-parts identity for `averagedTaylorPolynomial` on `L¹(μ)`.** On an additive
Haar measure `μ`, if `φ` is `C^m` with compact support, `u` is `C^m` on `tsupport φ`, and
`f =ᵐ[μ] u`, then `averagedTaylorPolynomial μ m φ hφ hsupp f` evaluates to
`∫ y, taylorPolynomial m u y x * φ y ∂μ`. -/
theorem averagedTaylorPolynomial_eq_integral_taylorPolynomial
    {m : ℕ} {φ u : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y)
    {f : Lp ℝ 1 μ} (hf : (f : EuclideanSpace ℝ ι → ℝ) =ᵐ[μ] u) (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomial μ m φ hφ hsupp f : EuclideanSpace ℝ ι → ℝ) x =
      ∫ y, taylorPolynomial m u y x * φ y ∂μ := by
  rw [averagedTaylorPolynomial_apply, ← setIntegral_univ]
  exact setIntegral_mul_averagedTaylorKernel_eq_integral_taylorPolynomial_of_ae_eq
    hφ hsupp (subset_univ _) hu (by simpa using hf) x

/-- **Integration-by-parts identity for `averagedTaylorPolynomial` on `L¹(μ.restrict B)`.** On an
additive Haar measure `μ`, if `φ` is `C^m` with compact support `tsupport φ ⊆ B`, `u` is `C^m` on
`tsupport φ`, and `f =ᵐ[μ.restrict B] u`, then `averagedTaylorPolynomial (μ.restrict B)` evaluates
to `∫ y, taylorPolynomial m u y x * φ y ∂μ`. -/
theorem averagedTaylorPolynomial_restrict_eq_integral_taylorPolynomial
    {B : Set (EuclideanSpace ℝ ι)} {m : ℕ} {φ u : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hB : tsupport φ ⊆ B)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y)
    {f : Lp ℝ 1 (μ.restrict B)} (hf : (f : EuclideanSpace ℝ ι → ℝ) =ᵐ[μ.restrict B] u)
    (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomial (μ.restrict B) m φ hφ hsupp f : EuclideanSpace ℝ ι → ℝ) x =
      ∫ y, taylorPolynomial m u y x * φ y ∂μ := by
  rw [averagedTaylorPolynomial_apply]
  exact setIntegral_mul_averagedTaylorKernel_eq_integral_taylorPolynomial_of_ae_eq
    hφ hsupp hB hu hf x

/-- **Polynomial reproduction on `L¹`.** If `tsupport φ ⊆ B` and `∫ y, φ y ∂μ = 1` for an additive
Haar measure `μ`, then `averagedTaylorPolynomial (μ.restrict B) m φ hφ hsupp` reproduces every
polynomial `q ∈ polynomialsDegLE ι m` belonging to `L¹(μ.restrict B)`. -/
theorem averagedTaylorPolynomial_toLp_eq_self
    {B : Set (EuclideanSpace ℝ ι)} {m : ℕ} {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hB : tsupport φ ⊆ B)
    (hint1 : ∫ y, φ y ∂μ = 1) {q : EuclideanSpace ℝ ι → ℝ} (hq : q ∈ polynomialsDegLE ι m)
    (hqL1 : MemLp q 1 (μ.restrict B)) :
    averagedTaylorPolynomial (μ.restrict B) m φ hφ hsupp (hqL1.toLp q) = ⟨q, hq⟩ := by
  ext x
  rw [averagedTaylorPolynomial_restrict_eq_integral_taylorPolynomial hφ hsupp hB
    (fun _ _ ↦ (contDiff_of_mem_polynomialsDegLE hq).contDiffAt) hqL1.coeFn_toLp]
  simp [taylorPolynomial_eq_of_mem_polynomialsDegLE hq, integral_const_mul, hint1]

end AddHaar

section LpDomain

/-- **The averaged Taylor polynomial on `Lᵖ`.** For a measure `μ` finite on compact sets, exponent
`1 ≤ p`, and `C^m` compactly supported cutoff `φ`, this continuous linear operator sends `f ∈ Lᵖ(μ)`
to `x ↦ ∫ y, f y * averagedTaylorKernel φ m x y ∂μ`, constructed via `Set.LpToL1RestrictCLM`. -/
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
        (Set.LpToL1RestrictCLM (𝕜 := ℝ) (tsupport φ) hsupp.measure_lt_top) := by rfl

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

/-- At exponent `p = 1`, `averagedTaylorPolynomialLp` coincides with `averagedTaylorPolynomial`. -/
@[simp]
theorem averagedTaylorPolynomialLp_one (μ : Measure (EuclideanSpace ℝ ι))
    [IsFiniteMeasureOnCompacts μ] (m : ℕ) (φ : EuclideanSpace ℝ ι → ℝ)
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) :
    averagedTaylorPolynomialLp μ 1 m φ hφ hsupp = averagedTaylorPolynomial μ m φ hφ hsupp := by
  ext f x; simp [averagedTaylorPolynomialLp_apply, averagedTaylorPolynomial_apply]

/-- Weighted `iteratedFDeriv` pairing evaluation formula for `averagedTaylorPolynomialLp` on
`Lᵖ(μ)`, requiring only `Lᵖ` membership and cutoff regularity. -/
theorem averagedTaylorPolynomialLp_eq_sum_integral_iteratedFDeriv
    (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasureOnCompacts μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (m : ℕ) (φ : EuclideanSpace ℝ ι → ℝ)
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (f : Lp ℝ p μ) (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomialLp μ p m φ hφ hsupp f : EuclideanSpace ℝ ι → ℝ) x =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
        ∑ I : Fin j → ι, ∫ y,
          iteratedFDeriv ℝ j (fun z ↦
            (∏ l : Fin j, ⟪EuclideanSpace.basisFun ι ℝ (I l), x - z⟫_ℝ) * φ z)
            y (EuclideanSpace.basisFun ι ℝ ∘ I) * f y ∂μ := by
  rw [averagedTaylorPolynomialLp_apply, ← setIntegral_univ,
    setIntegral_mul_averagedTaylorKernel_eq_sum_setIntegral_iteratedFDeriv hφ hsupp
      (subset_univ _) (((Lp.memLp f).locallyIntegrable Fact.out).locallyIntegrableOn Set.univ) x]
  simp_rw [setIntegral_univ]

/-- Weighted `iteratedFDeriv` pairing evaluation formula for `averagedTaylorPolynomialLp` on
`Lᵖ(μ.restrict Ω)` when `tsupport φ ⊆ Ω`, matching
`TauCeti.Wkp.fullContractL_iteratedGradientChain_sum_setIntegral_iteratedFDeriv`. -/
theorem averagedTaylorPolynomialLp_restrict_eq_sum_setIntegral_iteratedFDeriv
    {μ : Measure (EuclideanSpace ℝ ι)} [IsFiniteMeasureOnCompacts μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {Ω : Set (EuclideanSpace ℝ ι)} {m : ℕ}
    {φ : EuclideanSpace ℝ ι → ℝ} (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (hΩ : tsupport φ ⊆ Ω) (f : Lp ℝ p (μ.restrict Ω)) (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomialLp (μ.restrict Ω) p m φ hφ hsupp f :
      EuclideanSpace ℝ ι → ℝ) x =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
        ∑ I : Fin j → ι, ∫ y in Ω,
          iteratedFDeriv ℝ j (fun z ↦
            (∏ l : Fin j, ⟪EuclideanSpace.basisFun ι ℝ (I l), x - z⟫_ℝ) * φ z)
            y (EuclideanSpace.basisFun ι ℝ ∘ I) * f y ∂μ := by
  rw [averagedTaylorPolynomialLp_apply]
  exact setIntegral_mul_averagedTaylorKernel_eq_sum_setIntegral_iteratedFDeriv hφ hsupp hΩ
    (Lp.locallyIntegrableOn f Fact.out) x

/-- **Integration-by-parts identity for `averagedTaylorPolynomialLp` on `Lᵖ(μ)`.** On an additive
Haar measure `μ`, if `φ` is `C^m` with compact support, `u` is `C^m` on `tsupport φ`, and
`f =ᵐ[μ] u`, then `averagedTaylorPolynomialLp μ p m φ hφ hsupp f` evaluates to
`∫ y, taylorPolynomial m u y x * φ y ∂μ`. -/
theorem averagedTaylorPolynomialLp_eq_integral_taylorPolynomial
    {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {m : ℕ} {φ u : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y)
    {f : Lp ℝ p μ} (hf : (f : EuclideanSpace ℝ ι → ℝ) =ᵐ[μ] u) (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomialLp μ p m φ hφ hsupp f : EuclideanSpace ℝ ι → ℝ) x =
      ∫ y, taylorPolynomial m u y x * φ y ∂μ := by
  rw [averagedTaylorPolynomialLp_apply, ← setIntegral_univ]
  exact setIntegral_mul_averagedTaylorKernel_eq_integral_taylorPolynomial_of_ae_eq
    hφ hsupp (subset_univ _) hu (by simpa using hf) x

/-- **Integration-by-parts identity for `averagedTaylorPolynomialLp` on `Lᵖ(μ.restrict Ω)`.** On an
additive Haar measure `μ`, if `φ` is `C^m` with compact support `tsupport φ ⊆ Ω`, `u` is `C^m` on
`tsupport φ`, and `f =ᵐ[μ.restrict Ω] u`, then `averagedTaylorPolynomialLp (μ.restrict Ω)`
evaluates to `∫ y, taylorPolynomial m u y x * φ y ∂μ`. -/
theorem averagedTaylorPolynomialLp_restrict_eq_integral_taylorPolynomial
    {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {Ω : Set (EuclideanSpace ℝ ι)}
    {m : ℕ} {φ u : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hΩ : tsupport φ ⊆ Ω)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y)
    {f : Lp ℝ p (μ.restrict Ω)} (hf : (f : EuclideanSpace ℝ ι → ℝ) =ᵐ[μ.restrict Ω] u)
    (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomialLp (μ.restrict Ω) p m φ hφ hsupp f : EuclideanSpace ℝ ι → ℝ) x =
      ∫ y, taylorPolynomial m u y x * φ y ∂μ := by
  rw [averagedTaylorPolynomialLp_apply]
  exact setIntegral_mul_averagedTaylorKernel_eq_integral_taylorPolynomial_of_ae_eq
    hφ hsupp hΩ hu hf x

/-- **Polynomial reproduction on `Lᵖ(Ω)`.** If `tsupport φ ⊆ Ω` and `∫ y, φ y ∂μ = 1` for an
additive Haar measure `μ`, then `averagedTaylorPolynomialLp (μ.restrict Ω)` reproduces every
`q ∈ polynomialsDegLE ι m` belonging to `Lᵖ(μ.restrict Ω)`. In particular, when `Ω` is nonempty and
star-shaped with respect to `Metric.ball x₀ ρ` (`0 < ρ`), `Metric.ball x₀ ρ ⊆ Ω` holds by
`Set.Nonempty.subset_of_forall_starConvex` and `φ = (ballBump x₀ hρ).normed μ` satisfies all
cutoff hypotheses. -/
theorem averagedTaylorPolynomialLp_toLp_eq_self
    {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {Ω : Set (EuclideanSpace ℝ ι)}
    {m : ℕ} {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hΩ : tsupport φ ⊆ Ω)
    (hint1 : ∫ y, φ y ∂μ = 1) {q : EuclideanSpace ℝ ι → ℝ} (hq : q ∈ polynomialsDegLE ι m)
    (hqLp : MemLp q p (μ.restrict Ω)) :
    averagedTaylorPolynomialLp (μ.restrict Ω) p m φ hφ hsupp (hqLp.toLp q) = ⟨q, hq⟩ := by
  ext x
  rw [averagedTaylorPolynomialLp_restrict_eq_integral_taylorPolynomial p hφ hsupp hΩ
    (fun _ _ ↦ (contDiff_of_mem_polynomialsDegLE hq).contDiffAt) hqLp.coeFn_toLp]
  simp [taylorPolynomial_eq_of_mem_polynomialsDegLE hq, integral_const_mul, hint1]

end LpDomain

end Operator

section Examples

/-! ### Explicit evaluations on coordinate quadratics and half-balls -/

variable {ι : Type*} [Fintype ι]

/-- On `EuclideanSpace ℝ ι` with an additive Haar measure `μ`, if `φ` is `C¹`, compactly supported
in `B`, and even (`∀ y, φ (-y) = φ y`), then for every coordinate `i : ι` such that
`z ↦ (z i) ^ 2` belongs to `L¹(μ.restrict B)`, the first-order averaged Taylor polynomial sends
`q(x) = (x i) ^ 2` to the constant `-∫ y, (y i) ^ 2 * φ y ∂μ`. -/
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
      taylorPolynomial 1 q₂ y x = 2 * x i * y i - (y i) ^ 2 := by
    have hderiv := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y i).pow 2
    simp [taylorPolynomial_succ, iteratedFDeriv_one_apply, q₂, hderiv.fderiv]; ring
  have hpi : Continuous (fun z : EuclideanSpace ℝ ι ↦ z i) :=
    PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i
  have hint1 : Integrable (fun y : EuclideanSpace ℝ ι ↦ 2 * x i * y i * φ y) μ :=
    ((continuous_const.mul hpi).mul hφ.continuous).integrable_of_hasCompactSupport hsupp.mul_left
  have hint2 : Integrable (fun y : EuclideanSpace ℝ ι ↦ (y i) ^ 2 * φ y) μ :=
    ((hpi.pow 2).mul hφ.continuous).integrable_of_hasCompactSupport hsupp.mul_left
  simp_rw [htaylor, sub_mul]
  rw [integral_sub hint1 hint2,
    MeasureTheory.integral_eq_zero_of_odd (g := fun y : EuclideanSpace ℝ ι ↦ 2 * x i * y i * φ y)
      (ae_of_all _ fun y ↦ by simp [heven y]), zero_sub]

/-- Limit of polynomial reproduction: on `Metric.ball 0 ρ` (`0 < ρ`) in `EuclideanSpace ℝ ι`
with cutoff `(ballBump 0 hρ).normed μ` and any coordinate `i : ι`, the order-`1` averaged Taylor
polynomial does **not** reproduce `z ↦ (z i) ^ 2` (whereas `averagedTaylorPolynomial_toLp_eq_self`
reproduces it at order `2`). -/
theorem averagedTaylorPolynomial_normed_ballBump_sq_one_ne_self
    {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure] {ρ : ℝ} (hρ : 0 < ρ) (i : ι) :
    let hqL1 : MemLp (fun z : EuclideanSpace ℝ ι ↦ (z i) ^ 2) 1 (μ.restrict (ball 0 ρ)) :=
      ((PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i).pow 2).memLp_restrict_of_isBounded
        isBounded_ball 1
    (averagedTaylorPolynomial (μ.restrict (ball 0 ρ)) 1 ((ballBump 0 hρ).normed μ)
        ((ballBump 0 hρ).contDiff_normed (n := (1 : ℕ)))
        (ballBump 0 hρ).hasCompactSupport_normed
        (hqL1.toLp fun z ↦ (z i) ^ 2) : EuclideanSpace ℝ ι → ℝ) ≠
      fun z ↦ (z i) ^ 2 := by
  classical
  intro hqL1 heq
  set φ := (ballBump (0 : EuclideanSpace ℝ ι) hρ).normed μ
  have hval := congrFun heq 0
  rw [averagedTaylorPolynomial_sq_one_of_even ((ballBump 0 hρ).contDiff_normed (n := (1 : ℕ)))
      (ballBump 0 hρ).hasCompactSupport_normed (tsupport_normed_ballBump_subset_ball μ 0 hρ)
      (fun y ↦ (ballBump 0 hρ).normed_neg y) i hqL1 0,
    PiLp.zero_apply, zero_pow two_ne_zero] at hval
  let z₀ : EuclideanSpace ℝ ι := (ρ / 4) • EuclideanSpace.basisFun ι ℝ i
  have hz₀_ball : z₀ ∈ Function.support φ := by
    rw [(ballBump 0 hρ).support_normed_eq, ballBump_rOut, mem_ball_zero_iff, norm_smul,
      (EuclideanSpace.basisFun ι ℝ).orthonormal.1 i, mul_one, Real.norm_of_nonneg (by positivity)]
    linarith
  have hpos : 0 < ∫ y : EuclideanSpace ℝ ι, (y i) ^ 2 * φ y ∂μ :=
    (((PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i).pow 2).mul
        (ballBump 0 hρ).continuous_normed).integral_pos_of_hasCompactSupport_nonneg_ne_zero
      (x := z₀) (ballBump 0 hρ).hasCompactSupport_normed.mul_left
      (fun y ↦ mul_nonneg (sq_nonneg _) ((ballBump 0 hρ).nonneg_normed y))
      ((show z₀ i = ρ / 4 by simp [z₀, EuclideanSpace.basisFun_apply]) ▸
        mul_ne_zero (pow_ne_zero 2 (by linarith)) (Function.mem_support.mp hz₀_ball))
  linarith

/-- Evaluating `averagedTaylorPolynomial` at order `0` with `(ballBump 0 hρ).normed μ` on the
discontinuous `L¹` indicator of the positive half-ball `{y ∈ ball 0 ρ | 0 ≤ y i}` yields the
constant polynomial `1 / 2`. -/
theorem averagedTaylorPolynomial_zero_halfBall_eq_half
    {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure] {ρ : ℝ} (hρ : 0 < ρ) (i : ι) :
    let hHm : MeasurableSet {y ∈ ball (0 : EuclideanSpace ℝ ι) ρ | 0 ≤ y i} :=
      measurableSet_ball.inter
        (isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) i).continuous).measurableSet
    let hHfin : μ {y ∈ ball (0 : EuclideanSpace ℝ ι) ρ | 0 ≤ y i} ≠ (∞ : ℝ≥0∞) :=
      ((measure_mono (sep_subset _ _)).trans_lt measure_ball_lt_top).ne
    (averagedTaylorPolynomial μ 0 ((ballBump 0 hρ).normed μ)
      ((ballBump 0 hρ).contDiff_normed (n := (0 : ℕ)))
      (ballBump 0 hρ).hasCompactSupport_normed
      (indicatorConstLp 1 hHm hHfin (1 : ℝ)) : EuclideanSpace ℝ ι → ℝ) =
      fun _ ↦ (1 : ℝ) / 2 := by
  classical
  intro hHm hHfin
  set H : Set (EuclideanSpace ℝ ι) := {y ∈ ball 0 ρ | 0 ≤ y i}
  set φ := (ballBump (0 : EuclideanSpace ℝ ι) hρ).normed μ
  ext x; simp only [averagedTaylorPolynomial_apply, averagedTaylorKernel_zero]
  have hind : (fun y ↦ (indicatorConstLp 1 hHm hHfin (1 : ℝ)) y * φ y) =ᵐ[μ] H.indicator φ :=
    (indicatorConstLp_coeFn (μ := μ) (p := 1) (hs := hHm) (hμs := hHfin) (c := (1 : ℝ))).mono
      fun y hy ↦ by dsimp only; rw [hy, ← Set.indicator_mul_left]; simp
  have hHP : ∫ y in H, φ y ∂μ = ∫ y in {y | 0 ≤ EuclideanSpace.proj (𝕜 := ℝ) i y}, φ y ∂μ := by
    symm
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) i).continuous).measurableSet
      (fun _ hy ↦ hy.2) fun y hy ↦ ?_
    by_contra hyφ
    exact hy.2 ⟨tsupport_normed_ballBump_subset_ball μ 0 hρ
      (subset_tsupport _ (Function.mem_support.mpr hyφ)), hy.1⟩
  rw [integral_congr_ae hind, integral_indicator hHm, hHP]
  exact (ballBump 0 hρ).setIntegral_normed_halfSpace μ fun h0 ↦ one_ne_zero (α := ℝ) <| by
    simpa [EuclideanSpace.basisFun_apply] using
      congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] ℝ ↦ L (EuclideanSpace.basisFun ι ℝ i)) h0

end Examples

end TauCeti
