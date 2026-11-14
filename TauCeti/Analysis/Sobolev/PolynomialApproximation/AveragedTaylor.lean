/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import TauCeti.Analysis.Calculus.IteratedFDeriv.IntegrationByParts
public import TauCeti.Analysis.MvPolynomial.TaylorPolynomial
public import TauCeti.Analysis.Sobolev.PolynomialApproximation.StarShaped
public import TauCeti.MeasureTheory.Function.Lp.Restriction
import Mathlib.MeasureTheory.Function.Holder
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.MeasureTheory.Function.LocallyIntegrable

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
   for any Borel measure `μ` on `EuclideanSpace ℝ ι`, and by restriction a continuous linear
   operator `TauCeti.averagedTaylorPolynomialLp` on `Lp ℝ p (μ.restrict Ω)` (`1 ≤ p`) whenever
   `B ⊆ Ω` has finite measure.
3. On an additive Haar measure `μ`, if `u` is `C^m` at every point of `tsupport φ ⊆ B` and agrees
   almost everywhere on `B` with `f`, iterated integration by parts recovers the literal cutoff
   average of the classical Taylor polynomial
   (`TauCeti.averagedTaylorPolynomial_eq_integral_taylorPolynomial`):
   `averagedTaylorPolynomial (μ.restrict B) m φ hφ hsupp f x =
     ∫ y in B, taylorPolynomial ℝ m u y x * φ y ∂μ`.
4. Combining (3) with polynomial reproduction of `taylorPolynomial` shows that if `tsupport φ ⊆ B`
   and `∫ y, φ y ∂μ = 1`, `averagedTaylorPolynomial` reproduces every polynomial of degree at most
   `m` (`TauCeti.averagedTaylorPolynomial_toLp_eq_self`,
   `TauCeti.averagedTaylorPolynomialLp_toLp_eq_self`).

Degree `m` is sharp, and `averagedTaylorPolynomial` is an oblique (non-orthogonal) projection: with
an even unit-mass cutoff `φ`, the degree-`1` averaged Taylor polynomial sends the coordinate
quadratic `x ↦ (x i) ^ 2` to the strictly negative constant `-∫ y, (y i) ^ 2 * φ y`
(`TauCeti.averagedTaylorPolynomial_sq_one_of_even`,
`TauCeti.averagedTaylorPolynomial_ballCutoff_sq_one_ne_self`), whereas at `m = 2` it reproduces
`x ↦ (x i) ^ 2`.

## Main definitions

* `TauCeti.averagedTaylorKernel`: the smooth integration-by-parts kernel `Ψ_m(x, y)`.
* `TauCeti.averagedTaylorPolynomial`: continuous linear operator
  `Lp ℝ 1 μ →L[ℝ] polynomialsDegLE ι m`.
* `TauCeti.averagedTaylorPolynomialLp`: continuous linear operator
  `Lp ℝ p (μ.restrict Ω) →L[ℝ] polynomialsDegLE ι m` via restriction to `B ⊆ Ω` (`μ B < ∞`).

## Main results

* `TauCeti.averagedTaylorKernel_one`: explicit `m = 1` formula
  `Ψ_1(x, y) = (1 + card ι) * φ y - fderiv ℝ φ y (x - y)`.
* `TauCeti.averagedTaylorKernel_mem_polynomialsDegLE`: `Ψ_m(·, y) ∈ polynomialsDegLE ι m`.
* `TauCeti.averagedTaylorPolynomial_eq_integral_taylorPolynomial`: on `C^m` representatives,
  `Q^m f (x) = ∫ y in B, T^m_y u (x) * φ y ∂μ`.
* `TauCeti.averagedTaylorPolynomial_toLp_eq_self`,
  `TauCeti.averagedTaylorPolynomialLp_toLp_eq_self`: reproduction of `polynomialsDegLE ι m`.
* `TauCeti.averagedTaylorPolynomial_sq_one_of_even`,
  `TauCeti.averagedTaylorPolynomial_ballCutoff_sq_one_ne_self`,
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
  set b := EuclideanSpace.basisFun ι ℝ
  have hbi (i : ι) : (b i) i = 1 := by
    rw [← EuclideanSpace.basisFun_inner, real_inner_self_eq_norm_mul_norm,
      b.orthonormal.1 i, mul_one]
  rw [averagedTaylorKernel_succ, averagedTaylorKernel_zero, zero_add, Nat.factorial_one,
    Nat.cast_one, pow_one, div_one, neg_one_mul]
  have hsum : (∑ I : Fin 1 → ι,
      iteratedFDerivAlong ℝ (List.ofFn fun l ↦ b (I l))
        (fun z ↦ (∏ l : Fin 1, (x (I l) - z (I l))) * φ z) y) =
      ∑ i : ι, ((x i - y i) * fderiv ℝ φ y (b i) - φ y) := by
    rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hfn : (List.ofFn fun l : Fin 1 ↦ b ((Equiv.funUnique (Fin 1) ι).symm i l)) = [b i] := by
      simp
    have hprod : (fun z : EuclideanSpace ℝ ι ↦
        (∏ l : Fin 1, (x ((Equiv.funUnique (Fin 1) ι).symm i l) -
          z ((Equiv.funUnique (Fin 1) ι).symm i l))) * φ z) =
        fun z ↦ (x i - z i) * φ z := by
      ext z
      simp
    rw [hfn, hprod, iteratedFDerivAlong_cons_apply, iteratedFDerivAlong_nil]
    have hcoord : HasFDerivAt (fun z : EuclideanSpace ℝ ι ↦ x i - z i)
        (-(EuclideanSpace.proj (𝕜 := ℝ) i)) y :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.const_sub (x i)
    rw [(hcoord.fun_mul hφ.hasFDerivAt).fderiv]
    simp [hbi i, mul_comm (φ y)]
    ring
  have hlin : ∑ i : ι, (x i - y i) * fderiv ℝ φ y (b i) = fderiv ℝ φ y (x - y) := by
    conv_rhs => rw [← b.sum_repr (x - y), map_sum]
    simp [b]
  rw [hsum, Finset.sum_sub_distrib, hlin, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- For every target point `x`, the support in `y` of `averagedTaylorKernel φ m x` is contained in
`tsupport φ`. -/
theorem tsupport_averagedTaylorKernel_subset (φ : EuclideanSpace ℝ ι → ℝ) (m : ℕ)
    (x : EuclideanSpace ℝ ι) :
    tsupport (averagedTaylorKernel φ m x) ⊆ tsupport φ := by
  refine closure_minimal (fun y hy ↦ ?_) (isClosed_tsupport φ)
  rw [Function.mem_support] at hy
  by_contra hyφ
  refine hy ?_
  rw [averagedTaylorKernel_def]
  refine Finset.sum_eq_zero fun j _ ↦ mul_eq_zero_of_right _ (Finset.sum_eq_zero fun I _ ↦ ?_)
  have hsub : tsupport (iteratedFDerivAlong ℝ (coordDirections I)
      (fun z ↦ (∏ l : Fin j, (x (I l) - z (I l))) * φ z)) ⊆ tsupport φ :=
    (tsupport_iteratedFDerivAlong_subset _ _).trans tsupport_mul_subset_right
  exact image_eq_zero_of_notMem_tsupport fun h ↦ hyφ (hsub h)

/-- Compact support of `φ` passes to `y ↦ averagedTaylorKernel φ m x y` for every `x`. -/
theorem hasCompactSupport_averagedTaylorKernel {φ : EuclideanSpace ℝ ι → ℝ}
    (hsupp : HasCompactSupport φ) (m : ℕ) (x : EuclideanSpace ℝ ι) :
    HasCompactSupport (averagedTaylorKernel φ m x) :=
  hsupp.of_isClosed_subset (isClosed_tsupport _) (tsupport_averagedTaylorKernel_subset φ m x)

/-- If `φ` is `C^n` and `k + m ≤ n`, then `y ↦ averagedTaylorKernel φ m x y` is `C^k`. -/
theorem contDiff_averagedTaylorKernel_right {φ : EuclideanSpace ℝ ι → ℝ} {n k : ℕ∞ω} {m : ℕ}
    (hφ : ContDiff ℝ n φ) (hkm : k + m ≤ n) (x : EuclideanSpace ℝ ι) :
    ContDiff ℝ k (averagedTaylorKernel φ m x) := by
  have hfun : averagedTaylorKernel φ m x =
      fun y ↦ ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
        ∑ I : Fin j → ι,
          iteratedFDerivAlong ℝ (coordDirections I)
            (fun z ↦ (∏ l : Fin j, (x (I l) - z (I l))) * φ z) y :=
    (rfl)
  rw [hfun]
  refine ContDiff.sum fun j hj ↦ contDiff_const.mul (ContDiff.sum fun I _ ↦ ?_)
  have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hpoly : ContDiff ℝ n (fun z : EuclideanSpace ℝ ι ↦ ∏ l : Fin j, (x (I l) - z (I l))) :=
    contDiff_prod fun l _ ↦ contDiff_const.sub (EuclideanSpace.proj (𝕜 := ℝ) (I l)).contDiff
  refine (hpoly.mul hφ).iteratedFDerivAlong (coordDirections I) ?_
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
  have hpoly : ContDiff ℝ m (fun z : EuclideanSpace ℝ ι ↦ ∏ l ∈ Finset.univ \ S, -z (I l)) :=
    contDiff_prod fun l _ ↦ (EuclideanSpace.proj (𝕜 := ℝ) (I l)).contDiff.neg
  refine (hpoly.mul hφ).iteratedFDerivAlong (coordDirections I) ?_
  rw [length_coordDirections, zero_add]
  exact_mod_cast hj

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
  rw [averagedTaylorKernel_def]
  refine Finset.sum_congr rfl fun j hj ↦ congrArg _ (Finset.sum_congr rfl fun I _ ↦ ?_)
  have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  let F : Finset (Fin j) → EuclideanSpace ℝ ι → ℝ :=
    fun S ↦ (∏ l ∈ S, x (I l)) • (fun z ↦ (∏ l ∈ Finset.univ \ S, -z (I l)) * φ z)
  have hexp : (fun z : EuclideanSpace ℝ ι ↦ (∏ l : Fin j, (x (I l) - z (I l))) * φ z) =
      fun z ↦ ∑ S ∈ (Finset.univ : Finset (Fin j)).powerset, F S z := by
    ext z
    simp_rw [sub_eq_add_neg]
    rw [Finset.prod_add (fun l ↦ x (I l)) (fun l ↦ -z (I l)) Finset.univ, Finset.sum_mul]
    simp [F, mul_assoc]
  have hcont (S : Finset (Fin j)) : ContDiff ℝ m
      (fun z : EuclideanSpace ℝ ι ↦ (∏ l ∈ Finset.univ \ S, -z (I l)) * φ z) :=
    (contDiff_prod fun l _ ↦ (EuclideanSpace.proj (𝕜 := ℝ) (I l)).contDiff.neg).mul hφ
  have hlen : ((coordDirections I).length : ℕ∞ω) ≤ m := by
    rw [length_coordDirections]
    exact_mod_cast hjle
  have hF (S : Finset (Fin j)) : ContDiff ℝ m (F S) :=
    (hcont S).const_smul (∏ l ∈ S, x (I l))
  have hdir : (List.ofFn fun l ↦ EuclideanSpace.basisFun ι ℝ (I l)) = coordDirections I := rfl
  rw [hdir, hexp, congrFun (iteratedFDerivAlong_sum (f := F) _ (fun S _ ↦ hF S)
    (coordDirections I) hlen) y]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  have hsmul := congrFun (iteratedFDerivAlong_const_smul (hcont S) (∏ l ∈ S, x (I l))
    (coordDirections I) hlen) y
  simpa [F, kernelMonomialWeight] using hsmul

/-- For every fixed `y`, if `φ` is `C^m`, the map `x ↦ averagedTaylorKernel φ m x y` is a
polynomial of total degree at most `m`. -/
theorem averagedTaylorKernel_mem_polynomialsDegLE {φ : EuclideanSpace ℝ ι → ℝ} {m : ℕ}
    (hφ : ContDiff ℝ m φ) (y : EuclideanSpace ℝ ι) :
    (fun x ↦ averagedTaylorKernel φ m x y) ∈ polynomialsDegLE ι m := by
  have hfun : (fun x ↦ averagedTaylorKernel φ m x y) =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) •
        ∑ I : Fin j → ι, ∑ S ∈ (Finset.univ : Finset (Fin j)).powerset,
          kernelMonomialWeight φ I S y • fun x : EuclideanSpace ℝ ι ↦ ∏ l ∈ S, x (I l) := by
    ext x
    rw [averagedTaylorKernel_eq_sum_monomial hφ]
    simp [Finset.mul_sum, mul_comm]
  rw [hfun]
  refine Submodule.sum_mem _ fun j hj ↦ Submodule.smul_mem _ _ ?_
  have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  refine Submodule.sum_mem _ fun I _ ↦ Submodule.sum_mem _ fun S _ ↦ Submodule.smul_mem _ _ ?_
  exact prod_coord_mem_polynomialsDegLE hjle I S

end Kernel

/-- Every bounded-degree polynomial function belongs to `Lᵖ(μ.restrict Ω)` on any bounded set `Ω`
under any Borel measure `μ` finite on compact sets and any exponent `p : ℝ≥0∞`. -/
theorem memLp_restrict_of_mem_polynomialsDegLE_of_isBounded
    {ι : Type*} [Finite ι] {μ : Measure (EuclideanSpace ℝ ι)} [IsFiniteMeasureOnCompacts μ]
    {Ω : Set (EuclideanSpace ℝ ι)} (hΩ : Bornology.IsBounded Ω) (p : ℝ≥0∞)
    {m : ℕ} {q : EuclideanSpace ℝ ι → ℝ} (hq : q ∈ polynomialsDegLE ι m) :
    MemLp q p (μ.restrict Ω) := by
  have := Fintype.ofFinite ι
  have hq_cont : Continuous q := (contDiff_of_mem_polynomialsDegLE (n := 0) hq).continuous
  exact (hq_cont.continuousOn.memLp_restrict_of_subset_isCompact hΩ.isCompact_closure
    measurableSet_closure Subset.rfl p).mono_measure (Measure.restrict_mono subset_closure le_rfl)

section Operator

variable {ι : Type*} [Fintype ι]

/-- Integrating any `Integrable f μ` against `averagedTaylorKernel φ m` produces a polynomial of
total degree at most `m`. -/
theorem integral_mul_averagedTaylorKernel_mem_polynomialsDegLE
    {μ : Measure (EuclideanSpace ℝ ι)} {m : ℕ} {φ f : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hf : Integrable f μ) :
    (fun x ↦ ∫ y, f y * averagedTaylorKernel φ m x y ∂μ) ∈ polynomialsDegLE ι m := by
  have hint_w : ∀ {j : ℕ}, j ≤ m → ∀ (I : Fin j → ι) (S : Finset (Fin j)),
      Integrable (fun y ↦ f y * kernelMonomialWeight φ I S y) μ :=
    fun hj I S ↦ hf.mul_of_top_left
      ((contDiff_kernelMonomialWeight hφ hj I S).continuous.memLp_top_of_hasCompactSupport
        (hasCompactSupport_kernelMonomialWeight hsupp I S) μ)
  have hfun : (fun x ↦ ∫ y, f y * averagedTaylorKernel φ m x y ∂μ) =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) •
        ∑ I : Fin j → ι, ∑ S ∈ (Finset.univ : Finset (Fin j)).powerset,
          (∫ y, f y * kernelMonomialWeight φ I S y ∂μ) •
            fun x : EuclideanSpace ℝ ι ↦ ∏ l ∈ S, x (I l) := by
    ext x
    have hpt (y : EuclideanSpace ℝ ι) : f y * averagedTaylorKernel φ m x y =
        ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
          ∑ I : Fin j → ι, ∑ S ∈ (Finset.univ : Finset (Fin j)).powerset,
            (∏ l ∈ S, x (I l)) * (f y * kernelMonomialWeight φ I S y) := by
      rw [averagedTaylorKernel_eq_sum_monomial hφ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← mul_assoc, mul_comm (f y), mul_assoc, Finset.mul_sum]
      refine congrArg _ (Finset.sum_congr rfl fun I _ ↦ ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun S _ ↦ by ring
    simp_rw [hpt]
    rw [integral_finsetSum]
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [integral_const_mul, integral_finsetSum]
      · refine congrArg _ (Finset.sum_congr rfl fun I _ ↦ ?_)
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl fun S _ ↦ ?_
          rw [integral_const_mul, mul_comm]
        · exact fun S _ ↦ (hint_w hjle I S).const_mul _
      · exact fun I _ ↦ integrable_finsetSum _ fun S _ ↦ (hint_w hjle I S).const_mul _
    · intro j hj
      have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      exact (integrable_finsetSum _ fun I _ ↦
        integrable_finsetSum _ fun S _ ↦ (hint_w hjle I S).const_mul _).const_mul _
  rw [hfun]
  refine Submodule.sum_mem _ fun j hj ↦ Submodule.smul_mem _ _ ?_
  have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  refine Submodule.sum_mem _ fun I _ ↦ Submodule.sum_mem _ fun S _ ↦ Submodule.smul_mem _ _ ?_
  exact prod_coord_mem_polynomialsDegLE hjle I S

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
  refine integral_congr_ae ?_
  filter_upwards [((continuous_averagedTaylorKernel_right hφ x).memLp_top_of_hasCompactSupport
    (hasCompactSupport_averagedTaylorKernel hsupp m x) μ).coeFn_toLp] with y hy
  simp [hy]

/-- **The averaged Taylor polynomial on `L¹`.** For any Borel measure `μ` on `EuclideanSpace ℝ ι`
and any `C^m` compactly supported cutoff `φ`, pairing `f ∈ Lp ℝ 1 μ` against
`averagedTaylorKernel φ m` defines a continuous linear map into `polynomialsDegLE ι m`. -/
def averagedTaylorPolynomial (μ : Measure (EuclideanSpace ℝ ι)) (m : ℕ)
    (φ : EuclideanSpace ℝ ι → ℝ) (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) :
    Lp ℝ 1 μ →L[ℝ] polynomialsDegLE ι m where
  toFun f := ⟨fun x ↦ ∫ y, f y * averagedTaylorKernel φ m x y ∂μ,
    integral_mul_averagedTaylorKernel_mem_polynomialsDegLE hφ hsupp (L1.integrable_coeFn f)⟩
  map_add' f g := by
    ext x
    simp_rw [Submodule.coe_add, Pi.add_apply, averagedTaylorEval_eq_lpPairing μ m hφ hsupp x]
    exact map_add _ f g
  map_smul' c f := by
    ext x
    simp_rw [Submodule.coe_smul_of_tower, Pi.smul_apply, RingHom.id_apply,
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

/-- Set-integral evaluation formula when `averagedTaylorPolynomial` is applied on `μ.restrict B`. -/
theorem averagedTaylorPolynomial_restrict_apply (μ : Measure (EuclideanSpace ℝ ι))
    (B : Set (EuclideanSpace ℝ ι)) (m : ℕ) (φ : EuclideanSpace ℝ ι → ℝ)
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (f : Lp ℝ 1 (μ.restrict B)) (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomial (μ.restrict B) m φ hφ hsupp f : EuclideanSpace ℝ ι → ℝ) x =
      ∫ y in B, f y * averagedTaylorKernel φ m x y ∂μ :=
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

/-- Single-multi-index test function `z ↦ (∏ l, (x (I l) - z (I l))) * φ z` differentiated in
`averagedTaylorKernel`. -/
private def kernelTestTerm (φ : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι)
    {j : ℕ} (I : Fin j → ι) (z : EuclideanSpace ℝ ι) : ℝ :=
  (∏ l : Fin j, (x (I l) - z (I l))) * φ z

private theorem contDiff_kernelTestTerm {φ : EuclideanSpace ℝ ι → ℝ} {m j : ℕ}
    (hφ : ContDiff ℝ m φ) (hj : j ≤ m) (x : EuclideanSpace ℝ ι) (I : Fin j → ι) :
    ContDiff ℝ j (kernelTestTerm φ x I) :=
  ((contDiff_prod fun l _ ↦
    contDiff_const.sub (EuclideanSpace.proj (𝕜 := ℝ) (I l)).contDiff).mul hφ).of_le
    (by exact_mod_cast hj)

omit [Fintype ι] in
private theorem tsupport_kernelTestTerm_subset (φ : EuclideanSpace ℝ ι → ℝ)
    (x : EuclideanSpace ℝ ι) {j : ℕ} (I : Fin j → ι) :
    tsupport (kernelTestTerm φ x I) ⊆ tsupport φ :=
  tsupport_mul_subset_right

omit [Fintype ι] in
private theorem hasCompactSupport_kernelTestTerm {φ : EuclideanSpace ℝ ι → ℝ}
    (hsupp : HasCompactSupport φ) (x : EuclideanSpace ℝ ι) {j : ℕ} (I : Fin j → ι) :
    HasCompactSupport (kernelTestTerm φ x I) :=
  hsupp.mul_left

private theorem integrableOn_mul_iteratedFDerivAlong_kernelTestTerm
    {B : Set (EuclideanSpace ℝ ι)} {m j : ℕ} {φ u U : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hU : ContDiff ℝ m U)
    (hUu : ∀ y ∈ tsupport φ, U =ᶠ[𝓝 y] u) (hj : j ≤ m) (x : EuclideanSpace ℝ ι)
    (I : Fin j → ι) :
    IntegrableOn
      (fun y ↦ u y * iteratedFDerivAlong ℝ (coordDirections I) (kernelTestTerm φ x I) y) B μ := by
  have heq :
      (fun y ↦ u y * iteratedFDerivAlong ℝ (coordDirections I) (kernelTestTerm φ x I) y) =
      fun y ↦ U y * iteratedFDerivAlong ℝ (coordDirections I) (kernelTestTerm φ x I) y := by
    ext y
    by_cases hy : y ∈ tsupport φ
    · rw [(hUu y hy).eq_of_nhds]
    · have hy' : y ∉ tsupport (iteratedFDerivAlong ℝ (coordDirections I) (kernelTestTerm φ x I)) :=
        fun h ↦ hy ((tsupport_iteratedFDerivAlong_subset _ _).trans
          (tsupport_kernelTestTerm_subset φ x I) h)
      simp [image_eq_zero_of_notMem_tsupport hy']
  rw [heq]
  have hcont_k : Continuous (iteratedFDerivAlong ℝ (coordDirections I) (kernelTestTerm φ x I)) :=
    ((contDiff_kernelTestTerm hφ hj x I).iteratedFDerivAlong (m := 0) (coordDirections I)
      (by simp [length_coordDirections])).continuous
  exact (Continuous.integrable_of_hasCompactSupport (hU.continuous.mul hcont_k)
    ((hasCompactSupport_kernelTestTerm hsupp x I).iteratedFDerivAlong _).mul_left).integrableOn

private theorem integrableOn_iteratedFDeriv_mul_kernelTestTerm
    {B : Set (EuclideanSpace ℝ ι)} {m j : ℕ} {φ u U : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hU : ContDiff ℝ m U)
    (hUu : ∀ y ∈ tsupport φ, U =ᶠ[𝓝 y] u) (hj : j ≤ m) (x : EuclideanSpace ℝ ι)
    (I : Fin j → ι) :
    IntegrableOn (fun y ↦
      iteratedFDeriv ℝ j u y (fun l ↦ EuclideanSpace.basisFun ι ℝ (I l)) *
        kernelTestTerm φ x I y) B μ := by
  set b := EuclideanSpace.basisFun ι ℝ
  have heq :
      (fun y ↦ iteratedFDeriv ℝ j u y (fun l ↦ b (I l)) * kernelTestTerm φ x I y) =
      fun y ↦ iteratedFDeriv ℝ j U y (fun l ↦ b (I l)) * kernelTestTerm φ x I y := by
    ext y
    by_cases hy : y ∈ tsupport φ
    · rw [((hUu y hy).iteratedFDeriv ℝ j).eq_of_nhds]
    · simp [kernelTestTerm, image_eq_zero_of_notMem_tsupport hy]
  rw [heq]
  have hcont_d : Continuous (fun y ↦ iteratedFDeriv ℝ j U y (fun l ↦ b (I l))) := by
    have hfn : (fun y ↦ iteratedFDeriv ℝ j U y (fun l ↦ b (I l))) =
        iteratedFDerivAlong ℝ (coordDirections I) U := by
      ext y
      simp only [coordDirections]
      have hUy : ContDiffAt ℝ j U y := (hU.of_le (by exact_mod_cast hj)).contDiffAt
      exact (hUy.iteratedFDerivAlong_ofFn_eq_iteratedFDeriv (fun l ↦ b (I l))).symm
    rw [hfn]
    exact (hU.iteratedFDerivAlong (m := 0) (coordDirections I)
      (by rw [length_coordDirections, zero_add]; exact_mod_cast hj)).continuous
  exact (Continuous.integrable_of_hasCompactSupport
    (hcont_d.mul (contDiff_kernelTestTerm hφ hj x I).continuous)
    (hasCompactSupport_kernelTestTerm hsupp x I).mul_left).integrableOn

/-- Single-`(j, I)` integration-by-parts identity moving `coordDirections I` from
`kernelTestTerm φ x I` onto `u` and identifying the reversed directional derivative with
`iteratedFDeriv ℝ j u y`. -/
private theorem averagedTaylor_ibp_term
    {B : Set (EuclideanSpace ℝ ι)} {m j : ℕ} {φ u : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hB : tsupport φ ⊆ B)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y) (hj : j ≤ m)
    (x : EuclideanSpace ℝ ι) (I : Fin j → ι) :
    ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
      (∫ y in B, u y * iteratedFDerivAlong ℝ (coordDirections I) (kernelTestTerm φ x I) y ∂μ) =
    (j.factorial : ℝ)⁻¹ * ∫ y in B,
      iteratedFDeriv ℝ j u y (fun l ↦ EuclideanSpace.basisFun ι ℝ (I l)) *
        kernelTestTerm φ x I y ∂μ := by
  set b := EuclideanSpace.basisFun ι ℝ
  have hibp := setIntegral_mul_iteratedFDerivAlong_eq (μ := μ) (coordDirections I)
    (f := u) (g := kernelTestTerm φ x I) (s := B)
    (fun y hy ↦ by
      rw [length_coordDirections]
      exact (hu y (tsupport_kernelTestTerm_subset φ x I hy)).of_le (by exact_mod_cast hj))
    (by simpa [length_coordDirections] using contDiff_kernelTestTerm hφ hj x I)
    (hasCompactSupport_kernelTestTerm hsupp x I)
    ((tsupport_kernelTestTerm_subset φ x I).trans hB)
  rw [length_coordDirections] at hibp
  have hpt : (fun y ↦
      iteratedFDerivAlong ℝ (coordDirections I).reverse u y * kernelTestTerm φ x I y) =
      fun y ↦ iteratedFDeriv ℝ j u y (fun l ↦ b (I l)) * kernelTestTerm φ x I y := by
    ext y
    by_cases hy : y ∈ tsupport φ
    · have huy : ContDiffAt ℝ j u y := (hu y hy).of_le (by exact_mod_cast hj)
      have hperm : iteratedFDerivAlong ℝ (coordDirections I).reverse u y =
          iteratedFDerivAlong ℝ (coordDirections I) u y :=
        (List.reverse_perm (coordDirections I)).iteratedFDerivAlong_eq_apply
          (by simpa [List.length_reverse, length_coordDirections] using huy)
      rw [hperm]
      simp only [coordDirections]
      rw [huy.iteratedFDerivAlong_ofFn_eq_iteratedFDeriv]
    · simp [kernelTestTerm, image_eq_zero_of_notMem_tsupport hy]
  rw [hibp, hpt, ← mul_assoc]
  have hsign : ((-1 : ℝ) ^ j / (j.factorial : ℝ)) * (-1 : ℝ) ^ j = (j.factorial : ℝ)⁻¹ := by
    have h1 : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      ((-1 : ℝ) ^ j / (j.factorial : ℝ)) * (-1 : ℝ) ^ j =
          ((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) * (j.factorial : ℝ)⁻¹ := by ring
      _ = (j.factorial : ℝ)⁻¹ := by rw [h1, one_mul]
  rw [hsign]

/-- **Integration-by-parts identity for the averaged Taylor polynomial.** If `u` is `C^m` at every
point of `tsupport φ`, `tsupport φ ⊆ B`, and `f ∈ Lp ℝ 1 (μ.restrict B)` agrees with `u` almost
everywhere on `B`, then `averagedTaylorPolynomial (μ.restrict B) m φ hφ hsupp f` coincides with the
cutoff average of the classical `m`-th Taylor polynomial of `u`:
`Q^m f (x) = ∫ y in B, taylorPolynomial ℝ m u y x * φ y ∂μ`. -/
theorem averagedTaylorPolynomial_eq_integral_taylorPolynomial
    {B : Set (EuclideanSpace ℝ ι)} {m : ℕ} {φ u : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hB : tsupport φ ⊆ B)
    (hu : ∀ y ∈ tsupport φ, ContDiffAt ℝ m u y)
    {f : Lp ℝ 1 (μ.restrict B)} (hf : (f : EuclideanSpace ℝ ι → ℝ) =ᵐ[μ.restrict B] u)
    (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomial (μ.restrict B) m φ hφ hsupp f : EuclideanSpace ℝ ι → ℝ) x =
      ∫ y in B, taylorPolynomial ℝ m u y x * φ y ∂μ := by
  rw [averagedTaylorPolynomial_restrict_apply]
  have hf_eq : ∫ y in B, f y * averagedTaylorKernel φ m x y ∂μ =
      ∫ y in B, u y * averagedTaylorKernel φ m x y ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf] with y hy
    rw [hy]
  rw [hf_eq]
  -- Extend `u` from `{y | ContDiffAt ℝ m u y}` to a globally `C^m` map `U` for termwise
  -- integrability when interchanging the finite `(j, I)` sums with the integral.
  let V : Set (EuclideanSpace ℝ ι) := {y | ContDiffAt ℝ m u y}
  have hV : IsOpen V := isOpen_iff_mem_nhds.2 fun y hy ↦ ContDiffAt.eventually hy (by simp)
  have huV : ContDiffOn ℝ (m : ℕ∞) u V := fun y hy ↦ by simpa using hy.contDiffWithinAt
  obtain ⟨U, hU_raw, -, -, -, hUu⟩ := huV.exists_contDiff_eventuallyEq_on_isCompact hsupp hV hu
  have hU : ContDiff ℝ m U := by simpa using hU_raw
  set b := EuclideanSpace.basisFun ι ℝ
  have hlhs_expand : ∫ y in B, u y * averagedTaylorKernel φ m x y ∂μ =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
        ∑ I : Fin j → ι, ∫ y in B,
          u y * iteratedFDerivAlong ℝ (coordDirections I) (kernelTestTerm φ x I) y ∂μ := by
    have hpt (y : EuclideanSpace ℝ ι) : u y * averagedTaylorKernel φ m x y =
        ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
          ∑ I : Fin j → ι,
            u y * iteratedFDerivAlong ℝ (coordDirections I) (kernelTestTerm φ x I) y := by
      rw [averagedTaylorKernel_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← mul_assoc, mul_comm (u y), mul_assoc, Finset.mul_sum]
      rfl
    simp_rw [hpt]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [integral_const_mul, integral_finsetSum _ fun I _ ↦
        integrableOn_mul_iteratedFDerivAlong_kernelTestTerm hφ hsupp hU hUu hjle x I]
    · intro j hj
      have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      exact (integrable_finsetSum _ fun I _ ↦
        integrableOn_mul_iteratedFDerivAlong_kernelTestTerm hφ hsupp hU hUu hjle x I).const_mul _
  rw [hlhs_expand]
  calc
    (∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j / (j.factorial : ℝ)) *
        ∑ I : Fin j → ι, ∫ y in B,
          u y * iteratedFDerivAlong ℝ (coordDirections I) (kernelTestTerm φ x I) y ∂μ)
      = ∑ j ∈ Finset.range (m + 1),
          ∑ I : Fin j → ι, (j.factorial : ℝ)⁻¹ *
            ∫ y in B, iteratedFDeriv ℝ j u y (fun l ↦ b (I l)) * kernelTestTerm φ x I y ∂μ := by
          refine Finset.sum_congr rfl fun j hj ↦ ?_
          have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun I _ ↦ averagedTaylor_ibp_term hφ hsupp hB hu hjle x I
    _ = ∫ y in B, (∑ j ∈ Finset.range (m + 1),
          ∑ I : Fin j → ι, (j.factorial : ℝ)⁻¹ *
            (iteratedFDeriv ℝ j u y (fun l ↦ b (I l)) * kernelTestTerm φ x I y)) ∂μ := by
          rw [integral_finsetSum]
          · refine Finset.sum_congr rfl fun j hj ↦ ?_
            have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            rw [integral_finsetSum]
            · exact Finset.sum_congr rfl fun I _ ↦ (integral_const_mul _ _).symm
            · exact fun I _ ↦
                (integrableOn_iteratedFDeriv_mul_kernelTestTerm hφ hsupp hU hUu hjle x
                  I).const_mul _
          · intro j hj
            have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            exact integrable_finsetSum _ fun I _ ↦
              (integrableOn_iteratedFDeriv_mul_kernelTestTerm hφ hsupp hU hUu hjle x I).const_mul _
    _ = ∫ y in B, taylorPolynomial ℝ m u y x * φ y ∂μ := by
          congr 1
          ext y
          rw [taylorPolynomial_apply, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          have hmulti : iteratedFDeriv ℝ j u y (fun _ ↦ x - y) =
              ∑ I : Fin j → ι, (∏ l : Fin j, (x (I l) - y (I l))) *
                iteratedFDeriv ℝ j u y (fun l ↦ b (I l)) := by
            set A := (iteratedFDeriv ℝ j u y).toMultilinearMap
            have hA : iteratedFDeriv ℝ j u y (fun _ ↦ x - y) = A (fun _ ↦ x - y) := rfl
            rw [hA]
            conv_lhs => rw [← b.sum_repr (x - y), A.map_sum]
            simp [A.map_smul_univ, A, b]
          rw [smul_eq_mul, hmulti, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun I _ ↦ ?_
          simp only [kernelTestTerm]
          ring

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
  rw [averagedTaylorPolynomial_eq_integral_taylorPolynomial hφ hsupp hB
    (fun y _ ↦ (contDiff_of_mem_polynomialsDegLE hq).contDiffAt) (hqL1.coeFn_toLp)]
  simp only [taylorPolynomial_eq_self_of_mem_polynomialsDegLE hq]
  have hset : ∫ y in B, q x * φ y ∂μ = ∫ y, q x * φ y ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hyB ↦ ?_
    have hy : y ∉ tsupport φ := fun h ↦ hyB (hB h)
    simp [image_eq_zero_of_notMem_tsupport hy]
  rw [hset, integral_const_mul, hint1, mul_one]

end AddHaar

section LpDomain

/-- **The averaged Taylor polynomial on `Lᵖ(Ω)`.** When `1 ≤ p` and `B ⊆ Ω` has finite `μ`-measure,
composing `averagedTaylorPolynomial` with restriction `Set.LpToL1RestrictCLM` yields a continuous
linear operator `Lp ℝ p (μ.restrict Ω) →L[ℝ] polynomialsDegLE ι m`. -/
def averagedTaylorPolynomialLp (μ : Measure (EuclideanSpace ℝ ι))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (Ω B : Set (EuclideanSpace ℝ ι))
    (hμB : μ B < (∞ : ℝ≥0∞)) (m : ℕ) (φ : EuclideanSpace ℝ ι → ℝ)
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) :
    Lp ℝ p (μ.restrict Ω) →L[ℝ] polynomialsDegLE ι m :=
  (averagedTaylorPolynomial ((μ.restrict Ω).restrict B) m φ hφ hsupp).comp
    (Set.LpToL1RestrictCLM (𝕜 := ℝ) B ((μ.restrict_apply_le Ω B).trans_lt hμB))

/-- Set-integral evaluation formula for `averagedTaylorPolynomialLp` when `B ⊆ Ω`. -/
theorem averagedTaylorPolynomialLp_apply (μ : Measure (EuclideanSpace ℝ ι))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {Ω B : Set (EuclideanSpace ℝ ι)} (hBΩ : B ⊆ Ω)
    (hμB : μ B < (∞ : ℝ≥0∞)) (m : ℕ) (φ : EuclideanSpace ℝ ι → ℝ)
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ)
    (f : Lp ℝ p (μ.restrict Ω)) (x : EuclideanSpace ℝ ι) :
    (averagedTaylorPolynomialLp μ p Ω B hμB m φ hφ hsupp f : EuclideanSpace ℝ ι → ℝ) x =
      ∫ y in B, f y * averagedTaylorKernel φ m x y ∂μ := by
  simp only [averagedTaylorPolynomialLp, ContinuousLinearMap.comp_apply,
    averagedTaylorPolynomial_apply]
  have hcongr : (fun y ↦ Set.LpToL1RestrictCLM (𝕜 := ℝ) B
      ((μ.restrict_apply_le Ω B).trans_lt hμB) f y * averagedTaylorKernel φ m x y)
      =ᵐ[(μ.restrict Ω).restrict B]
      fun y ↦ f y * averagedTaylorKernel φ m x y := by
    filter_upwards [Set.LpToL1RestrictCLM_coeFn (𝕜 := ℝ) B
      ((μ.restrict_apply_le Ω B).trans_lt hμB) f] with y hy
    rw [hy]
  rw [integral_congr_ae hcongr, Measure.restrict_restrict_of_subset hBΩ]

/-- **Polynomial reproduction on `Lᵖ(Ω)`.** If `B ⊆ Ω` has finite Haar measure, `tsupport φ ⊆ B`,
and `∫ y, φ y ∂μ = 1`, then `averagedTaylorPolynomialLp` reproduces every `q ∈ polynomialsDegLE ι m`
belonging to `Lᵖ(μ.restrict Ω)`. In particular, when `Ω` is nonempty and star-shaped with respect to
`B = Metric.ball x₀ ρ` (`0 < ρ`), `B ⊆ Ω` holds automatically by
`Set.Nonempty.subset_of_forall_starConvex` and `φ = ballCutoff μ x₀ hρ` satisfies all cutoff
hypotheses. -/
theorem averagedTaylorPolynomialLp_toLp_eq_self
    {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {Ω B : Set (EuclideanSpace ℝ ι)} (hBΩ : B ⊆ Ω)
    (hμB : μ B < (∞ : ℝ≥0∞)) {m : ℕ} {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : ContDiff ℝ m φ) (hsupp : HasCompactSupport φ) (hB : tsupport φ ⊆ B)
    (hint1 : ∫ y, φ y ∂μ = 1)
    {q : EuclideanSpace ℝ ι → ℝ} (hq : q ∈ polynomialsDegLE ι m)
    (hqLp : MemLp q p (μ.restrict Ω)) :
    averagedTaylorPolynomialLp μ p Ω B hμB m φ hφ hsupp (hqLp.toLp q) = ⟨q, hq⟩ := by
  ext x
  rw [averagedTaylorPolynomialLp_apply μ p hBΩ hμB m φ hφ hsupp]
  have hqB : (hqLp.toLp q : EuclideanSpace ℝ ι → ℝ) =ᵐ[μ.restrict B] q :=
    ae_mono (Measure.restrict_mono hBΩ le_rfl) hqLp.coeFn_toLp
  have hqL1 : MemLp q 1 (μ.restrict B) := by
    have : IsFiniteMeasure (μ.restrict B) := isFiniteMeasure_restrict.2 hμB.ne
    exact (hqLp.mono_measure (Measure.restrict_mono hBΩ le_rfl)).mono_exponent (Fact.out : 1 ≤ p)
  have hcongr :
      ∫ y in B, (hqLp.toLp q : EuclideanSpace ℝ ι → ℝ) y * averagedTaylorKernel φ m x y ∂μ =
        ∫ y in B, (hqL1.toLp q : EuclideanSpace ℝ ι → ℝ) y * averagedTaylorKernel φ m x y ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hqB, hqL1.coeFn_toLp] with y hy1 hy2
    rw [hy1, hy2]
  rw [hcongr, ← averagedTaylorPolynomial_restrict_apply μ B m φ hφ hsupp,
    averagedTaylorPolynomial_toLp_eq_self hφ hsupp hB hint1 hq hqL1]

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
  have hq₂_smooth : ContDiff ℝ (1 : ℕ) q₂ :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.pow 2
  rw [averagedTaylorPolynomial_eq_integral_taylorPolynomial hφ hsupp hB
    (fun y _ ↦ hq₂_smooth.contDiffAt) hqL1.coeFn_toLp]
  have htaylor (y : EuclideanSpace ℝ ι) :
      taylorPolynomial ℝ 1 q₂ y x = 2 * x i * y i - (y i) ^ 2 := by
    have hfd : HasFDerivAt q₂ ((2 • y i ^ (2 - 1)) • EuclideanSpace.proj (𝕜 := ℝ) i) y :=
      ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := y)).pow 2
    rw [taylorPolynomial_succ, taylorPolynomial_zero, zero_add, Nat.factorial_one, Nat.cast_one,
      inv_one, one_smul, iteratedFDeriv_one_apply, hfd.fderiv]
    simp [q₂]
    ring
  simp_rw [htaylor]
  have hset : ∫ y in B, (2 * x i * y i - (y i) ^ 2) * φ y ∂μ =
      ∫ y, (2 * x i * y i - (y i) ^ 2) * φ y ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hyB ↦ ?_
    have hy : y ∉ tsupport φ := fun h ↦ hyB (hB h)
    simp [image_eq_zero_of_notMem_tsupport hy]
  rw [hset]
  have hint_lin : Integrable (fun y : EuclideanSpace ℝ ι ↦ (2 * x i * y i) * φ y) μ :=
    Continuous.integrable_of_hasCompactSupport
      (((continuous_const.mul (EuclideanSpace.proj (𝕜 := ℝ) i).continuous)).mul hφ.continuous)
      hsupp.mul_left
  have hint_sq : Integrable (fun y : EuclideanSpace ℝ ι ↦ (y i) ^ 2 * φ y) μ :=
    Continuous.integrable_of_hasCompactSupport
      (((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.pow 2).mul hφ.continuous)
      hsupp.mul_left
  have hsub : (fun y : EuclideanSpace ℝ ι ↦ (2 * x i * y i - (y i) ^ 2) * φ y) =
      fun y ↦ (2 * x i * y i) * φ y - (y i) ^ 2 * φ y := by
    ext y
    ring
  rw [hsub, integral_sub hint_lin hint_sq]
  have hodd : ∫ y : EuclideanSpace ℝ ι, (2 * x i * y i) * φ y ∂μ = 0 := by
    have hneg : ∫ y : EuclideanSpace ℝ ι, (2 * x i * y i) * φ y ∂μ =
        -∫ y : EuclideanSpace ℝ ι, (2 * x i * y i) * φ y ∂μ := by
      conv_lhs => rw [← integral_neg_eq_self]
      have hfn : (fun y : EuclideanSpace ℝ ι ↦ (2 * x i * (-y) i) * φ (-y)) =
          fun y ↦ -((2 * x i * y i) * φ y) := by
        ext y
        simp [heven y]
      rw [hfn, integral_neg]
    linarith
  rw [hodd, zero_sub]

/-- Degree `m` is sharp: on `Metric.ball 0 ρ` (`0 < ρ`) in `EuclideanSpace ℝ ι` with cutoff
`ballCutoff μ 0 hρ` and any coordinate `i : ι`, the degree-`1` averaged Taylor polynomial does
**not** reproduce `z ↦ (z i) ^ 2` (its value at `0` is strictly negative), whereas the degree-`2`
averaged Taylor polynomial reproduces `z ↦ (z i) ^ 2` identically. -/
theorem averagedTaylorPolynomial_ballCutoff_sq_one_ne_self
    {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure] {ρ : ℝ} (hρ : 0 < ρ) (i : ι)
    (hqL1 : MemLp (fun z : EuclideanSpace ℝ ι ↦ (z i) ^ 2) 1 (μ.restrict (ball 0 ρ))) :
    (averagedTaylorPolynomial (μ.restrict (ball 0 ρ)) 1 (ballCutoff μ 0 hρ)
        (contDiff_ballCutoff μ 0 hρ) (hasCompactSupport_ballCutoff μ 0 hρ)
        (hqL1.toLp fun z ↦ (z i) ^ 2) : EuclideanSpace ℝ ι → ℝ) ≠
        (fun z ↦ (z i) ^ 2) ∧
      (averagedTaylorPolynomial (μ.restrict (ball 0 ρ)) 2 (ballCutoff μ 0 hρ)
        (contDiff_ballCutoff μ 0 hρ) (hasCompactSupport_ballCutoff μ 0 hρ)
        (hqL1.toLp fun z ↦ (z i) ^ 2) : EuclideanSpace ℝ ι → ℝ) =
        fun z ↦ (z i) ^ 2 := by
  let q₂ : EuclideanSpace ℝ ι → ℝ := fun z ↦ (z i) ^ 2
  have hq₂ : q₂ ∈ polynomialsDegLE ι 2 := by
    have hfn : q₂ = (fun z : EuclideanSpace ℝ ι ↦ z i) * fun z ↦ z i := by
      ext z
      exact sq (z i)
    rw [hfn]
    exact mul_mem_polynomialsDegLE
      ((coordinate_mem_polynomialsDegLE_iff ι 1 i).2 le_rfl)
      ((coordinate_mem_polynomialsDegLE_iff ι 1 i).2 le_rfl)
  refine ⟨fun heq ↦ ?_, ?_⟩
  · have hval := congrFun heq 0
    rw [averagedTaylorPolynomial_sq_one_of_even (contDiff_ballCutoff μ 0 hρ)
      (hasCompactSupport_ballCutoff μ 0 hρ) (tsupport_ballCutoff_subset_ball μ 0 hρ)
      (ballCutoff_neg μ hρ) i hqL1 0] at hval
    have h0 : (0 : EuclideanSpace ℝ ι) i = 0 := rfl
    rw [h0, zero_pow two_ne_zero] at hval
    have hpos : 0 < ∫ y : EuclideanSpace ℝ ι, (y i) ^ 2 * ballCutoff μ 0 hρ y ∂μ := by
      have hcont : Continuous (fun y : EuclideanSpace ℝ ι ↦ (y i) ^ 2 * ballCutoff μ 0 hρ y) :=
        ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.pow 2).mul (continuous_ballCutoff μ 0 hρ)
      have hint : Integrable (fun y : EuclideanSpace ℝ ι ↦ (y i) ^ 2 * ballCutoff μ 0 hρ y) μ :=
        hcont.integrable_of_hasCompactSupport (hasCompactSupport_ballCutoff μ 0 hρ).mul_left
      refine (integral_pos_iff_support_of_nonneg
        (fun y ↦ mul_nonneg (sq_nonneg _) (nonneg_ballCutoff μ 0 hρ y)) hint).mpr ?_
      let z₀ : EuclideanSpace ℝ ι := (ρ / 4) • EuclideanSpace.basisFun ι ℝ i
      have hz₀_norm : ‖z₀‖ = ρ / 4 := by
        rw [norm_smul, (EuclideanSpace.basisFun ι ℝ).orthonormal.1 i, mul_one,
          Real.norm_of_nonneg (by positivity)]
      have hz₀_ball : z₀ ∈ Function.support (ballCutoff μ 0 hρ) := by
        rw [support_ballCutoff, mem_ball_zero_iff, hz₀_norm]
        linarith
      have hz₀_coord : z₀ i = ρ / 4 := by
        have hbi : (EuclideanSpace.basisFun ι ℝ i) i = 1 := by
          rw [← EuclideanSpace.basisFun_inner, real_inner_self_eq_norm_mul_norm,
            (EuclideanSpace.basisFun ι ℝ).orthonormal.1 i, mul_one]
        simp [z₀, hbi]
      have hz₀_supp : z₀ ∈ Function.support
          (fun y : EuclideanSpace ℝ ι ↦ (y i) ^ 2 * ballCutoff μ 0 hρ y) := by
        rw [Function.mem_support, hz₀_coord]
        exact mul_ne_zero (pow_ne_zero 2 (by linarith)) (Function.mem_support.mp hz₀_ball)
      exact (isOpen_compl_singleton.preimage hcont).measure_pos μ ⟨z₀, hz₀_supp⟩
    linarith
  · exact congrArg Subtype.val (averagedTaylorPolynomial_toLp_eq_self
      (contDiff_ballCutoff μ 0 hρ) (hasCompactSupport_ballCutoff μ 0 hρ)
      (tsupport_ballCutoff_subset_ball μ 0 hρ) (integral_ballCutoff μ 0 hρ) hq₂ hqL1)

/-- Evaluating `averagedTaylorPolynomial` at order `0` with `ballCutoff μ 0 hρ` on the
discontinuous `L¹` indicator of the positive half-ball `{y ∈ ball 0 ρ | 0 ≤ y i}` yields the
constant polynomial `1 / 2`. -/
theorem averagedTaylorPolynomial_zero_halfBall_eq_half
    {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure] {ρ : ℝ} (hρ : 0 < ρ) (i : ι)
    (hHm : MeasurableSet {y ∈ ball (0 : EuclideanSpace ℝ ι) ρ | 0 ≤ y i})
    (hHfin : μ {y ∈ ball (0 : EuclideanSpace ℝ ι) ρ | 0 ≤ y i} ≠ (∞ : ℝ≥0∞)) :
    (averagedTaylorPolynomial μ 0 (ballCutoff μ 0 hρ)
      (contDiff_ballCutoff μ 0 hρ) (hasCompactSupport_ballCutoff μ 0 hρ)
      (indicatorConstLp 1 hHm hHfin (1 : ℝ)) : EuclideanSpace ℝ ι → ℝ) =
      fun _ ↦ (1 : ℝ) / 2 := by
  let H : Set (EuclideanSpace ℝ ι) := {y ∈ ball 0 ρ | 0 ≤ y i}
  let P : Set (EuclideanSpace ℝ ι) := {y | 0 ≤ EuclideanSpace.proj (𝕜 := ℝ) i y}
  have hPm : MeasurableSet P :=
    (isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) i).continuous).measurableSet
  ext x
  rw [averagedTaylorPolynomial_zero_order]
  set φ := ballCutoff μ (0 : EuclideanSpace ℝ ι) hρ
  have hcongr : (fun y ↦ ⇑(indicatorConstLp 1 hHm hHfin (1 : ℝ)) y * φ y) =ᵐ[μ]
      H.indicator φ := by
    filter_upwards [indicatorConstLp_coeFn (μ := μ) (p := 1) (hs := hHm) (hμs := hHfin)
      (c := (1 : ℝ))] with y hy
    rw [hy]
    by_cases hyH : y ∈ H
    · rw [Set.indicator_of_mem hyH, Set.indicator_of_mem hyH, one_mul]
    · rw [Set.indicator_of_notMem hyH, Set.indicator_of_notMem hyH, zero_mul]
  rw [integral_congr_ae hcongr, integral_indicator hHm]
  have hHP : ∫ y in H, φ y ∂μ = ∫ y in P, φ y ∂μ := by
    have hind : H.indicator φ = P.indicator φ := by
      ext y
      by_cases hyφ : φ y = 0
      · by_cases h1 : y ∈ H <;> by_cases h2 : y ∈ P <;> simp [h1, h2, hyφ]
      · have hy_ball : y ∈ ball (0 : EuclideanSpace ℝ ι) ρ :=
          ball_subset_ball (by linarith)
            ((support_ballCutoff μ 0 hρ) ▸ Function.mem_support.mpr hyφ)
        by_cases hy0 : 0 ≤ y i
        · have hyH : y ∈ H := ⟨hy_ball, hy0⟩
          have hyP : y ∈ P := hy0
          rw [Set.indicator_of_mem hyH, Set.indicator_of_mem hyP]
        · have hyH : y ∉ H := fun h ↦ hy0 h.2
          have hyP : y ∉ P := hy0
          rw [Set.indicator_of_notMem hyH, Set.indicator_of_notMem hyP]
    rw [← integral_indicator hHm, ← integral_indicator hPm]
    exact congrArg (fun g ↦ ∫ y, g y ∂μ) hind
  have hproj_ne : (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ ι →L[ℝ] ℝ) ≠ 0 := by
    intro h0
    have hbi : (EuclideanSpace.basisFun ι ℝ i) i = 1 := by
      rw [← EuclideanSpace.basisFun_inner, real_inner_self_eq_norm_mul_norm,
        (EuclideanSpace.basisFun ι ℝ).orthonormal.1 i, mul_one]
    have hbi0 : (EuclideanSpace.basisFun ι ℝ i) i = 0 :=
      congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] ℝ ↦ L (EuclideanSpace.basisFun ι ℝ i)) h0
    linarith
  rw [hHP]
  exact setIntegral_ballCutoff_halfSpace μ hρ hproj_ne

end Examples

end TauCeti
