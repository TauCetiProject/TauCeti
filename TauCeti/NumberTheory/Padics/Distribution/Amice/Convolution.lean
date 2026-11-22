/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.Comultiplication
public import TauCeti.NumberTheory.Padics.Distribution.Amice.Transform
public import TauCeti.NumberTheory.Padics.Distribution.Convolution
public import TauCeti.NumberTheory.Padics.Measure.Moments

/-!
# The Amice transform as a `K`-algebra homomorphism and equivalence

Let `K` be a complete nontrivially normed field with contractive `ℤ_p`-action. In
`TauCeti.NumberTheory.Padics.Distribution.Convolution`, the space
`TauCeti.LocallyAnalyticDistribution p K` of locally analytic distributions on `ℤ_p` is equipped
with point masses `dirac x` and with its stage-by-stage additive convolution `K`-algebra structure.
This file shows that the Amice transform intertwines this intrinsic convolution with formal power
series multiplication:

* stage comultiplication in `TauCeti.NumberTheory.Padics.Distribution.Amice.Comultiplication`
  expands Amice's polynomial `e_{h,n}` into the Vandermonde sum of outer products
  `∑_{i + j = n} prodMul e_{h,i} e_{h,j}` for `n < p ^ h`
  (`TauCeti.AnalyticStage.comul_amiceTerm_of_lt`);
* right convolution acts on locally analytic Mahler terms via the Vandermonde formula with the
  moments of `ν` (`TauCeti.LocallyAnalyticDistribution.convolveFunRight_mahlerTerm`), proving
  `amiceTransform (μ * ν) = amiceTransform μ * amiceTransform ν` over any such field `K`,
  including in positive characteristic, and bundling `amiceTransform` into the injective
  `K`-algebra homomorphism `amiceTransformAlgHom` (whence `LocallyAnalyticDistribution p K` is an
  integral domain);
* composing `amiceTransformAlgHom` with `ofMulMeasure` recovers Mathlib's measure-algebra Amice
  transform `AbstractMeasure.amiceTransformₐ`;
* when `K` is a normed `ℚ_p`-algebra, `amiceTransformEquiv` upgrades to the `K`-algebra
  isomorphism `amiceTransformAlgEquiv` onto `PowerSeries.OnOpenDisc.subring K 1`, identifying
  locally analytic distributions under convolution with formal power series converging on the open
  unit disc under multiplication.

## Main definitions

* `TauCeti.LocallyAnalyticDistribution.amiceTransformAlgHom`: the Amice transform as an injective
  `K`-algebra homomorphism `LocallyAnalyticDistribution p K →ₐ[K] PowerSeries K`.
* `TauCeti.LocallyAnalyticDistribution.amiceTransformAlgEquiv`: for `[NormedAlgebra ℚ_[p] K]`, the
  Amice transform as a `K`-algebra isomorphism onto `PowerSeries.OnOpenDisc.subring K 1`.

## Main results

* `TauCeti.LocallyAnalyticDistribution.convolveFunRight_mahlerTerm`: Vandermonde action of
  `convolveFunRight` on locally analytic Mahler terms.
* `TauCeti.LocallyAnalyticDistribution.amiceTransform_dirac`: the Amice transform of `dirac x` is
  `PowerSeries.binomialSeries K x`.
* `TauCeti.LocallyAnalyticDistribution.amiceTransform_mul`: the Amice transform sends distribution
  convolution to power series multiplication.
* `TauCeti.LocallyAnalyticDistribution.amiceTransformAlgHom_comp_ofMulMeasure`: compatibility with
  `AbstractMeasure.amiceTransformₐ`.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.2.
* P. Schneider and J. Teitelbaum, *p-adic Fourier theory*, Documenta Math. 6 (2001), 447–481.
-/

public section

open ZeroAtInftyContinuousMap
open scoped AbstractMeasure PowerSeries ZeroAtInfty

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

namespace LocallyAnalyticDistribution

open AnalyticStage LocallyAnalytic

variable {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

private theorem div_pow_eq_zero_of_mem_antidiagonal {p h n : ℕ} {ij : ℕ × ℕ}
    (hn : n < p ^ h) (hij : ij ∈ Finset.antidiagonal n) :
    ij.1 / p ^ h = 0 ∧ ij.2 / p ^ h = 0 := by
  rw [Finset.mem_antidiagonal] at hij
  exact ⟨Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)⟩

/-- Right convolution acts on locally analytic Mahler terms via the Vandermonde formula with the
moments of `ν`. -/
theorem convolveFunRight_mahlerTerm (ν : LocallyAnalyticDistribution p K) (n : ℕ) :
    convolveFunRight ν (mahlerTerm p K 1 n) =
      ∑ ij ∈ Finset.antidiagonal n, (amiceTransform ν).coeff ij.2 • mahlerTerm p K 1 ij.1 := by
  have hlt : n < p ^ n := Nat.lt_pow_self hp.out.one_lt
  have hn : n / p ^ n = 0 := Nat.div_eq_of_lt hlt
  rw [mahlerTerm_def, convolveFunRight_ofStage]
  have hstage : convolveFunRightStage (stage n ν) (amiceTerm p n n (1 : K)) =
      ∑ ij ∈ Finset.antidiagonal n, amiceTerm p n ij.1 ((amiceTransform ν).coeff ij.2) := by
    ext i
    simp only [convolveFunRightStage_apply, comulCurried_amiceTerm,
      ZeroAtInftyContinuousMap.coe_sum, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun ij hij ↦ ?_
    obtain ⟨hi, hj⟩ := div_pow_eq_zero_of_mem_antidiagonal hlt hij
    have hcoeff : stage n ν (amiceTerm p n ij.2 (1 : K)) = (amiceTransform ν).coeff ij.2 := by
      simp [hj]
    simp [hn, hi, hj, hcoeff]
  rw [hstage, map_sum]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  obtain ⟨hi, -⟩ := div_pow_eq_zero_of_mem_antidiagonal hlt hij
  simp [hi, ← mahlerTerm_smul]

/-- The Amice transform of the point mass `dirac x` is the binomial series `(1 + X) ^ x`. -/
@[simp]
theorem amiceTransform_dirac (x : ℤ_[p]) :
    amiceTransform (dirac (p := p) (K := K) x) = PowerSeries.binomialSeries K x := by
  rw [← ofMeasure_dirac, amiceTransform_ofMeasure, AbstractMeasure.amiceTransform_dirac]

/-- The Amice transform of the convolution unit `1 = dirac 0` is `1`. -/
@[simp]
theorem amiceTransform_one :
    amiceTransform (1 : LocallyAnalyticDistribution p K) = 1 := by
  rw [one_def, amiceTransform_dirac, PowerSeries.binomialSeries_zero]

/-- **The Amice transform sends distribution convolution to power series multiplication.** Holds
over every complete ultrametric field `K` with contractive `ℤ_p`-action, including in positive
characteristic. -/
@[simp]
theorem amiceTransform_mul (μ ν : LocallyAnalyticDistribution p K) :
    amiceTransform (μ * ν) = amiceTransform μ * amiceTransform ν := by
  ext n
  rw [coeff_amiceTransform, coe_mul_apply, convolveFunRight_mahlerTerm, map_sum,
    PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  simp [mul_comm]

/-- **The Amice transform as a `K`-algebra homomorphism** from locally analytic distributions under
additive convolution to formal power series. -/
noncomputable def amiceTransformAlgHom :
    LocallyAnalyticDistribution p K →ₐ[K] PowerSeries K :=
  AlgHom.ofLinearMap amiceTransform amiceTransform_one amiceTransform_mul

/-- The underlying function of `amiceTransformAlgHom` is `amiceTransform`. -/
theorem coe_amiceTransformAlgHom :
    ⇑(amiceTransformAlgHom (p := p) (K := K)) = amiceTransform := (rfl)

/-- Forgetting multiplication on `amiceTransformAlgHom` recovers `amiceTransform`. -/
@[simp]
theorem amiceTransformAlgHom_toLinearMap :
    (amiceTransformAlgHom (p := p) (K := K)).toLinearMap = amiceTransform := (rfl)

/-- The Amice transform sends convolution powers to power series powers. -/
@[simp]
theorem amiceTransform_pow (μ : LocallyAnalyticDistribution p K) (n : ℕ) :
    amiceTransform (μ ^ n) = amiceTransform μ ^ n :=
  map_pow (amiceTransformAlgHom (p := p) (K := K)) μ n

/-- The Amice transform sends scalar distributions `algebraMap K _ a` to constant series `C a`. -/
@[simp]
theorem amiceTransform_algebraMap (a : K) :
    amiceTransform (algebraMap K (LocallyAnalyticDistribution p K) a) = PowerSeries.C a := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, amiceTransform_one,
    ← Algebra.algebraMap_eq_smul_one, PowerSeries.algebraMap_eq]

/-- `amiceTransformAlgHom` is injective. -/
theorem amiceTransformAlgHom_injective :
    Function.Injective (amiceTransformAlgHom (p := p) (K := K)) :=
  amiceTransform_injective

instance : IsDomain (LocallyAnalyticDistribution p K) :=
  amiceTransformAlgHom_injective.isDomain (amiceTransformAlgHom (p := p) (K := K))

/-- On a multiplicative `ℤ_p`-measure embedded via `ofMulMeasure`, the distribution Amice transform
agrees with Mathlib's `AbstractMeasure.amiceTransformₐ`. -/
@[simp]
theorem amiceTransform_ofMulMeasure (μ : D(Multiplicative ℤ_[p], K)) :
    amiceTransform (ofMulMeasure (p := p) (K := K) μ) = AbstractMeasure.amiceTransformₐ μ := by
  ext n
  rw [ofMulMeasure_apply, amiceTransform_ofMeasure, AbstractMeasure.coeff_amiceTransform,
    AbstractMeasure.coeff_amiceTransformₐ, AbstractMeasure.arrowCongrLeft_apply]
  exact congrArg μ (ContinuousMap.ext fun x ↦ by simp [AbstractMeasure.mulMahler_apply])

/-- Composing `amiceTransformAlgHom` with `ofMulMeasure` recovers `AbstractMeasure.amiceTransformₐ`.
-/
@[simp]
theorem amiceTransformAlgHom_comp_ofMulMeasure :
    (amiceTransformAlgHom (p := p) (K := K)).comp ofMulMeasure =
      AbstractMeasure.amiceTransformₐ :=
  AlgHom.ext amiceTransform_ofMulMeasure

section NormedAlgebra

variable [NormedAlgebra ℚ_[p] K]

/-- The inverse Amice transform sends `1` on the open unit disc to the unit distribution `1`. -/
@[simp]
theorem ofOnOpenDisc_one :
    ofOnOpenDisc p (PowerSeries.onOpenDisc_one (R := K) (R₀ := 1)) = 1 :=
  amiceTransform_injective <| (amiceTransform_ofOnOpenDisc p _).trans amiceTransform_one.symm

/-- The inverse Amice transform sends products of open-unit-disc power series to convolutions of
distributions. -/
@[simp]
theorem ofOnOpenDisc_mul {F G : PowerSeries K} (hF : F.OnOpenDisc 1) (hG : G.OnOpenDisc 1) :
    ofOnOpenDisc p (hF.mul hG) = ofOnOpenDisc p hF * ofOnOpenDisc p hG :=
  amiceTransform_injective <| by
    rw [amiceTransform_ofOnOpenDisc, amiceTransform_mul, amiceTransform_ofOnOpenDisc,
      amiceTransform_ofOnOpenDisc]

/-- The inverse Amice transform sends powers of an open-unit-disc power series to convolution
powers. -/
@[simp]
theorem ofOnOpenDisc_pow {F : PowerSeries K} (hF : F.OnOpenDisc 1) (n : ℕ) :
    ofOnOpenDisc p (hF.pow n) = ofOnOpenDisc p hF ^ n :=
  amiceTransform_injective <| by
    rw [amiceTransform_ofOnOpenDisc, amiceTransform_pow, amiceTransform_ofOnOpenDisc]

/-- **Amice's algebra isomorphism for locally analytic distributions.** When `K` is a complete
ultrametric normed `ℚ_p`-algebra, the Amice transform is a `K`-algebra isomorphism from
`LocallyAnalyticDistribution p K` under additive convolution onto the subring
`PowerSeries.OnOpenDisc.subring K 1` of formal power series converging on the open unit disc. -/
noncomputable def amiceTransformAlgEquiv :
    LocallyAnalyticDistribution p K ≃ₐ[K] PowerSeries.OnOpenDisc.subring K 1 :=
  AlgEquiv.ofLinearEquiv amiceTransformEquiv
    (Subtype.ext <| by simp)
    fun _ _ ↦ Subtype.ext <| by simp

/-- The underlying power series of `amiceTransformAlgEquiv μ` is `amiceTransform μ`. -/
@[simp]
theorem coe_amiceTransformAlgEquiv (μ : LocallyAnalyticDistribution p K) :
    (amiceTransformAlgEquiv μ : PowerSeries K) = amiceTransform μ :=
  coe_amiceTransformEquiv μ

/-- Forgetting multiplication recovers `amiceTransformEquiv`. -/
@[simp]
theorem amiceTransformAlgEquiv_toLinearEquiv :
    (amiceTransformAlgEquiv (p := p) (K := K)).toLinearEquiv = amiceTransformEquiv := (rfl)

/-- The inverse of `amiceTransformAlgEquiv` is `ofOnOpenDisc`. -/
@[simp]
theorem amiceTransformAlgEquiv_symm_apply (F : PowerSeries.OnOpenDisc.subring K 1) :
    amiceTransformAlgEquiv.symm F =
      ofOnOpenDisc p (PowerSeries.OnOpenDisc.mem_subring.mp F.property) :=
  amiceTransformEquiv_symm_apply F

end NormedAlgebra

-- Point-mass convolution matches multiplication of binomial power series.
example (x y : ℤ_[3]) :
    amiceTransform (dirac (p := 3) (K := ℚ_[3]) x * dirac y) =
      PowerSeries.binomialSeries ℚ_[3] (x + y) := by
  rw [← dirac_add, amiceTransform_dirac]

-- Squaring the non-measure distribution associated to `log (1 + X)` gives `(log (1 + X)) ^ 2`.
example :
    amiceTransform (ofOnOpenDisc 3 (PowerSeries.onOpenDisc_log (K := ℚ_[3])) ^ 2) =
      PowerSeries.log ℚ_[3] ^ 2 := by
  rw [← ofOnOpenDisc_pow, amiceTransform_ofOnOpenDisc]

end LocallyAnalyticDistribution

end TauCeti
