/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.BinomialSeries
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

* at analytic level `h`, for every `n : ℕ` and every complete ultrametric `ℤ_p`-module `E`
  (including torsion modules), stage comultiplication expands Amice's basis vector
  `amiceTerm p h n e` into the weighted Vandermonde sum with integral factorial multiplier
  `TauCeti.amiceComulCoeff p h i j = ⌊(i + j) / pʰ⌋! / (⌊i / pʰ⌋! ⌊j / pʰ⌋!)`
  (`TauCeti.AnalyticStage.comul_amiceTerm`), which simplifies to `1` when `n < p ^ h`
  (`comul_amiceTerm_of_lt_pow`, `comul_amiceTerm_of_lt`);
* evaluating at level `h = n` proves `amiceTransform (μ * ν) = amiceTransform μ * amiceTransform ν`
  over any such field `K`, including in positive characteristic, bundling `amiceTransform` into the
  injective `K`-algebra homomorphism `amiceTransformAlgHom` (whence
  `LocallyAnalyticDistribution p K` is an integral domain);
* composing `amiceTransformAlgHom` with `ofMulMeasure` recovers Mathlib's measure-algebra Amice
  transform `AbstractMeasure.amiceTransformₐ`;
* when `K` is a normed `ℚ_p`-algebra, `amiceTransformEquiv` upgrades to the `K`-algebra
  isomorphism `amiceTransformAlgEquiv` onto `PowerSeries.OnOpenDisc.subring K 1`, identifying
  locally analytic distributions under convolution with formal power series converging on the open
  unit disc under multiplication, with `ofOnOpenDisc_binomialSeries` recovering `dirac x` from
  `(1 + X) ^ x`.

## Main definitions

* `TauCeti.amiceComulCoeff`: the integral factorial multiplier
  `⌊(i + j) / pʰ⌋! / (⌊i / pʰ⌋! ⌊j / pʰ⌋!)` in `ℤ_p`.
* `TauCeti.LocallyAnalyticDistribution.amiceTransformAlgHom`: the Amice transform as an injective
  `K`-algebra homomorphism `LocallyAnalyticDistribution p K →ₐ[K] PowerSeries K`.
* `TauCeti.LocallyAnalyticDistribution.amiceTransformAlgEquiv`: for `[NormedAlgebra ℚ_[p] K]`, the
  Amice transform as a `K`-algebra isomorphism onto `PowerSeries.OnOpenDisc.subring K 1`.

## Main results

* `TauCeti.AnalyticStage.comul_amiceTerm`: weighted Vandermonde expansion of `comul` on Amice's
  basis at all degrees `n : ℕ` for every complete ultrametric `ℤ_p`-module `E`, specializing to
  `comul_amiceTerm_of_lt_pow` and `comul_amiceTerm_of_lt` when `n < p ^ h`.
* `TauCeti.LocallyAnalyticDistribution.amiceTransform_dirac` and
  `TauCeti.LocallyAnalyticDistribution.ofOnOpenDisc_binomialSeries`: `dirac x` corresponds under the
  Amice bijection to `PowerSeries.binomialSeries K x`.
* `TauCeti.LocallyAnalyticDistribution.amiceTransform_mul`: the Amice transform sends distribution
  convolution to power series multiplication.
* `TauCeti.LocallyAnalyticDistribution.amiceTransformAlgHom_comp_ofMulMeasure`: compatibility with
  `AbstractMeasure.amiceTransformₐ`.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4 and §II.2.
* P. Schneider and J. Teitelbaum, *p-adic Fourier theory*, Documenta Math. 6 (2001), 447–481.
-/

public section

open ZeroAtInftyContinuousMap
open scoped AbstractMeasure PowerSeries ZeroAtInfty

namespace TauCeti

variable (p : ℕ) [hp : Fact p.Prime]

/-- The integral factorial multiplier `⌊(i + j) / pʰ⌋! / (⌊i / pʰ⌋! ⌊j / pʰ⌋!)` in `ℤ_p` for stage
comultiplication in Amice's basis. -/
noncomputable def amiceComulCoeff (h i j : ℕ) : ℤ_[p] :=
  (((i + j) / p ^ h).factorial / ((i / p ^ h).factorial * (j / p ^ h).factorial) : ℕ)

variable {p}

/-- `amiceComulCoeff p h i j` is the natural quotient `⌊(i + j) / pʰ⌋! / (⌊i / pʰ⌋! ⌊j / pʰ⌋!)`
cast to `ℤ_p`. -/
theorem amiceComulCoeff_def (h i j : ℕ) :
    amiceComulCoeff p h i j =
      (((i + j) / p ^ h).factorial / ((i / p ^ h).factorial * (j / p ^ h).factorial) : ℕ) :=
  (rfl)

/-- Multiplying `amiceComulCoeff p h i j` by `⌊i / pʰ⌋! ⌊j / pʰ⌋!` recovers `⌊(i + j) / pʰ⌋!`. -/
theorem factorial_mul_amiceComulCoeff (h i j : ℕ) :
    ((i / p ^ h).factorial : ℤ_[p]) * ((j / p ^ h).factorial : ℤ_[p]) *
      amiceComulCoeff p h i j = (((i + j) / p ^ h).factorial : ℤ_[p]) := by
  have hd : (i / p ^ h).factorial * (j / p ^ h).factorial ∣ ((i + j) / p ^ h).factorial :=
    (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
      (Nat.factorial_dvd_factorial Nat.div_add_div_le_add_div)
  rw [amiceComulCoeff, ← Nat.cast_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hd]

/-- None of the Amice comultiplication multipliers vanishes. -/
theorem amiceComulCoeff_ne_zero (h i j : ℕ) : amiceComulCoeff p h i j ≠ 0 := by
  intro hz
  have heq := factorial_mul_amiceComulCoeff (p := p) h i j
  rw [hz, mul_zero] at heq
  have hne : (((i + j) / p ^ h).factorial : ℤ_[p]) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero ((i + j) / p ^ h)
  exact hne heq.symm

/-- `amiceComulCoeff` is symmetric in `i` and `j`. -/
theorem amiceComulCoeff_comm (h i j : ℕ) :
    amiceComulCoeff p h j i = amiceComulCoeff p h i j := by
  simp [amiceComulCoeff, add_comm, mul_comm]

/-- Setting the second index to `0` gives multiplier `1`. -/
@[simp]
theorem amiceComulCoeff_zero_right (h i : ℕ) : amiceComulCoeff p h i 0 = 1 := by
  have hne : (i / p ^ h).factorial ≠ 0 := Nat.factorial_ne_zero _
  simp [amiceComulCoeff, Nat.div_self (Nat.pos_of_ne_zero hne)]

/-- Setting the first index to `0` gives multiplier `1`. -/
@[simp]
theorem amiceComulCoeff_zero_left (h j : ℕ) : amiceComulCoeff p h 0 j = 1 := by
  rw [amiceComulCoeff_comm, amiceComulCoeff_zero_right]

/-- Below degree `pʰ`, all three quotient factorials are `1`, so `amiceComulCoeff` is `1`. -/
@[simp]
theorem amiceComulCoeff_of_lt_pow {h i j : ℕ} (hij : i + j < p ^ h) :
    amiceComulCoeff p h i j = 1 := by
  simp [amiceComulCoeff, Nat.div_eq_of_lt hij,
    Nat.div_eq_of_lt ((Nat.le_add_right i j).trans_lt hij),
    Nat.div_eq_of_lt ((Nat.le_add_left j i).trans_lt hij)]

/-- In `ℚ_p`, `amiceComulCoeff` is the ratio `⌊(i + j) / pʰ⌋! / (⌊i / pʰ⌋! ⌊j / pʰ⌋!)`. -/
@[simp]
theorem coe_amiceComulCoeff (h i j : ℕ) :
    (amiceComulCoeff p h i j : ℚ_[p]) =
      (((i + j) / p ^ h).factorial : ℚ_[p]) /
        (((i / p ^ h).factorial : ℚ_[p]) * ((j / p ^ h).factorial : ℚ_[p])) := by
  have h1 : (((i / p ^ h).factorial : ℚ_[p]) * ((j / p ^ h).factorial : ℚ_[p])) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _)
      (by exact_mod_cast Nat.factorial_ne_zero _)
  refine (eq_div_iff h1).2 ?_
  rw [mul_comm]
  simpa only [PadicInt.coe_mul, PadicInt.coe_natCast, mul_assoc] using
    congrArg (fun x : ℤ_[p] ↦ (x : ℚ_[p])) (factorial_mul_amiceComulCoeff (p := p) h i j)

/-- The `p`-adic norm of `amiceComulCoeff p h i j` is the ratio of the norms of the three quotient
factorials. -/
theorem norm_amiceComulCoeff (h i j : ℕ) :
    ‖amiceComulCoeff p h i j‖ =
      ‖(((i + j) / p ^ h).factorial : ℤ_[p])‖ /
        (‖((i / p ^ h).factorial : ℤ_[p])‖ * ‖((j / p ^ h).factorial : ℤ_[p])‖) := by
  have hne : ‖((i / p ^ h).factorial : ℤ_[p])‖ * ‖((j / p ^ h).factorial : ℤ_[p])‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr (by exact_mod_cast Nat.factorial_ne_zero _))
      (norm_ne_zero_iff.mpr (by exact_mod_cast Nat.factorial_ne_zero _))
  refine (eq_div_iff hne).2 ?_
  rw [mul_comm, ← norm_mul, ← norm_mul, factorial_mul_amiceComulCoeff]

namespace AnalyticStage

private theorem comul_amiceTerm_padicInt (h n : ℕ) :
    comul ℤ_[p] (amiceTerm p h n (1 : ℤ_[p])) =
      ∑ ij ∈ Finset.antidiagonal n,
        amiceComulCoeff p h ij.1 ij.2 •
          prodSMul (amiceTerm p h ij.1 (1 : ℤ_[p])) (amiceTerm p h ij.2 (1 : ℤ_[p])) := by
  apply (curryEquiv ℤ_[p] ℤ_[p]).injective
  rw [curryEquiv_comul, map_sum]
  apply eval_injective ℤ_[p] PadicInt.isSMulRegular_natCast_p.zeroAtInftyContinuousMap
  refine ContinuousMap.ext fun x ↦ ?_
  apply eval_injective ℤ_[p] PadicInt.isSMulRegular_natCast_p
  refine ContinuousMap.ext fun y ↦ ?_
  rw [eval_eval_comulCurried ℤ_[p], eval_amiceTerm ℤ_[p]]
  simp only [PadicInt.mahlerTerm_apply, mahler_apply, smul_eq_mul, nsmul_eq_mul, mul_one,
    Ring.add_choose_eq n (Commute.all x y), Finset.sum_mul, map_sum, ContinuousMap.coe_sum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  rw [Finset.mem_antidiagonal] at hij
  simp only [map_smul, ContinuousMap.smul_apply, eval_curryEquiv_prodSMul ℤ_[p],
    eval_amiceTerm ℤ_[p], PadicInt.mahlerTerm_apply, mahler_apply, smul_eq_mul, nsmul_eq_mul,
    mul_one]
  have hfac := factorial_mul_amiceComulCoeff (p := p) h ij.1 ij.2
  rw [hij] at hfac
  linear_combination (Ring.choose x ij.1 * Ring.choose y ij.2) * hfac.symm

/-- **Weighted Vandermonde formula for `comul` on Amice's basis** at level `h`, valid for every
degree `n : ℕ` and every complete ultrametric `ℤ_p`-module `E`, including torsion modules. -/
theorem comul_amiceTerm {h : ℕ} {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E]
    [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E]
    (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]
    (n : ℕ) (e : E) :
    comul S (amiceTerm p h n e) =
      ∑ ij ∈ Finset.antidiagonal n,
        amiceComulCoeff p h ij.1 ij.2 •
          prodSMul (amiceTerm p h ij.1 (1 : ℤ_[p])) (amiceTerm p h ij.2 e) := by
  let φ : ℤ_[p] →L[ℤ_[p]] E := ContinuousLinearMap.toSpanSingleton ℤ_[p] e
  have hφ : ∃ C, ∀ r : ℤ_[p], ‖φ r‖ ≤ C * ‖r‖ :=
    ContinuousLinearMap.exists_norm_toSpanSingleton_apply_le ℤ_[p] e
  have hterm (m : ℕ) : compLeft φ hφ (amiceTerm p h m (1 : ℤ_[p])) = amiceTerm p h m e := by
    ext i; simp [φ]
  rw [comul_eq_comul_padicInt S, ← hterm n, comul_compLeft ℤ_[p] φ hφ,
    comul_amiceTerm_padicInt h n, map_sum]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  rw [map_smul]
  ext q
  simp [φ, mul_smul]

/-- Below degree `pʰ`, `comul S` expands `amiceTerm p h n e` into the unweighted Vandermonde sum
for every complete ultrametric `ℤ_p`-module `E`. -/
theorem comul_amiceTerm_of_lt_pow {h n : ℕ} {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E]
    [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E]
    (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]
    (hn : n < p ^ h) (e : E) :
    comul S (amiceTerm p h n e) =
      ∑ ij ∈ Finset.antidiagonal n,
        prodSMul (amiceTerm p h ij.1 (1 : ℤ_[p])) (amiceTerm p h ij.2 e) := by
  rw [comul_amiceTerm S n e]
  exact Finset.sum_congr rfl fun ij hij ↦ by
    rw [amiceComulCoeff_of_lt_pow ((Finset.mem_antidiagonal.mp hij).trans_lt hn), one_smul]

/-- **Vandermonde formula for `comul` on unweighted scalar Amice basis vectors.** When `n < p ^ h`,
so that `⌊n / pʰ⌋! = 1` and `amiceTerm p h n 1` represents `x choose n`, stage comultiplication
expands `amiceTerm p h n 1` into `∑_{i + j = n} prodSMul (amiceTerm p h i 1) (amiceTerm p h j 1)`.
-/
theorem comul_amiceTerm_of_lt {h n : ℕ} {R : Type*} [NormedRing R] [Algebra ℤ_[p] R]
    [IsBoundedSMul ℤ_[p] R] [IsUltrametricDist R] [CompleteSpace R]
    (S : Type*) [Semiring S] [Module S R] [ContinuousConstSMul S R] [SMulCommClass ℤ_[p] S R]
    (hn : n < p ^ h) :
    comul S (amiceTerm p h n (1 : R)) =
      ∑ ij ∈ Finset.antidiagonal n,
        prodSMul (amiceTerm p h ij.1 (1 : R)) (amiceTerm p h ij.2 (1 : R)) := by
  rw [comul_amiceTerm_of_lt_pow S hn (1 : R)]
  refine Finset.sum_congr rfl fun ij _ ↦ ZeroAtInftyContinuousMap.ext fun q ↦ ?_
  simp [Algebra.smul_def]

end AnalyticStage

namespace LocallyAnalyticDistribution

open AnalyticStage LocallyAnalytic

variable {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

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
  have hn : n < p ^ n := Nat.lt_pow_self hp.out.one_lt
  rw [coeff_amiceTransform, mahlerTerm_def, ← stage_apply, stage_mul,
    ContinuousLinearMap.comp_apply, comul_amiceTerm_of_lt K hn, map_sum, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  have hij' := Finset.mem_antidiagonal.mp hij
  have hij1 : ij.1 < p ^ n := by omega
  have hij2 : ij.2 < p ^ n := by omega
  rw [prodFunctional_prodSMul, stage_amiceTerm, stage_amiceTerm]
  simp [Nat.div_eq_of_lt hij1, Nat.div_eq_of_lt hij2]

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

/-- The inverse Amice transform recovers the point mass `dirac x` from the binomial series
`(1 + X) ^ x`. -/
@[simp]
theorem ofOnOpenDisc_binomialSeries (x : ℤ_[p])
    (hx : (PowerSeries.binomialSeries K x).OnOpenDisc 1) :
    ofOnOpenDisc p hx = dirac x :=
  amiceTransform_injective <| (amiceTransform_ofOnOpenDisc p hx).trans (amiceTransform_dirac x).symm

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

-- Reconstructing a distribution from `(1 + X) ^ x` on the open unit disc recovers `dirac x`.
example (x : ℤ_[3]) :
    ofOnOpenDisc 3 (x.onOpenDisc_binomialSeries (R := ℚ_[3])) = dirac x := by
  simp

-- Squaring the non-measure distribution associated to `log (1 + X)` gives `(log (1 + X)) ^ 2`.
example :
    amiceTransform (ofOnOpenDisc 3 (PowerSeries.onOpenDisc_log (K := ℚ_[3])) ^ 2) =
      PowerSeries.log ℚ_[3] ^ 2 := by
  rw [← ofOnOpenDisc_pow, amiceTransform_ofOnOpenDisc]

end LocallyAnalyticDistribution

end TauCeti
