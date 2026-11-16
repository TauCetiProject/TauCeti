/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.Transform
public import TauCeti.NumberTheory.Padics.Distribution.Convolution
public import TauCeti.NumberTheory.Padics.Measure.Moments

/-!
# Convolution and the Amice transform of locally analytic distributions

Under `AnalyticStage.addComul`, Amice's basis `amiceTerm p h n e` satisfies a weighted Vandermonde
identity with integral multiplier `TauCeti.amiceComulCoeff p h i j` for every complete ultrametric
`ℤ_p`-module `E`, including torsion modules (`addComul_amiceTerm`), reducing to `1` for `n < pʰ`
(`addComul_amiceTerm_of_lt_pow`). Reading the `n`-th moment at level `h = n` upgrades
`amiceTransform` to a `K`-algebra homomorphism `amiceTransformₐ` extending
`AbstractMeasure.amiceTransformₐ` along `ofMulMeasure`, and for a normed `ℚ_p`-algebra `K` to the
`K`-algebra isomorphism
`amiceTransformEquivₐ : LocallyAnalyticDistribution p K ≃ₐ[K] PowerSeries.OnOpenDisc.subring K 1`.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4 and §II.2.
* P. Schneider and J. Teitelbaum, *p-adic Fourier theory*, Documenta Math. 6 (2001), 447–481.
-/

public section

open ZeroAtInftyContinuousMap
open scoped AbstractMeasure Nat PowerSeries ZeroAtInfty

namespace TauCeti

variable (p : ℕ) [hp : Fact p.Prime]

/-- The integral factorial multiplier `⌊(i + j) / pʰ⌋! / (⌊i / pʰ⌋! ⌊j / pʰ⌋!)` in `ℤ_p`. -/
noncomputable def amiceComulCoeff (h i j : ℕ) : ℤ_[p] :=
  (((i + j) / p ^ h).factorial / ((i / p ^ h).factorial * (j / p ^ h).factorial) : ℕ)

variable {p}

/-- Multiplying `amiceComulCoeff p h i j` by `⌊i / pʰ⌋! ⌊j / pʰ⌋!` recovers `⌊(i + j) / pʰ⌋!`. -/
theorem factorial_mul_amiceComulCoeff (h i j : ℕ) :
    ((i / p ^ h).factorial : ℤ_[p]) * ((j / p ^ h).factorial : ℤ_[p]) *
      amiceComulCoeff p h i j = (((i + j) / p ^ h).factorial : ℤ_[p]) := by
  have hab : i / p ^ h + j / p ^ h ≤ (i + j) / p ^ h :=
    (Nat.le_div_iff_mul_le (pow_pos hp.out.pos h)).mpr <| by
      rw [add_mul]; exact add_le_add (Nat.div_mul_le_self i _) (Nat.div_mul_le_self j _)
  have hd : (i / p ^ h).factorial * (j / p ^ h).factorial ∣ ((i + j) / p ^ h).factorial :=
    (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans (Nat.factorial_dvd_factorial hab)
  rw [amiceComulCoeff, ← Nat.cast_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hd]

/-- `amiceComulCoeff` is symmetric in `i` and `j`. -/
theorem amiceComulCoeff_comm (h i j : ℕ) :
    amiceComulCoeff p h j i = amiceComulCoeff p h i j := by
  simp [amiceComulCoeff, add_comm, mul_comm]

/-- Below degree `pʰ`, all three quotient factorials are `1`, so `amiceComulCoeff` is `1`. -/
@[simp] theorem amiceComulCoeff_of_lt_pow {h i j : ℕ} (hij : i + j < p ^ h) :
    amiceComulCoeff p h i j = 1 := by
  simp [amiceComulCoeff, Nat.div_eq_of_lt hij,
    Nat.div_eq_of_lt ((Nat.le_add_right i j).trans_lt hij),
    Nat.div_eq_of_lt ((Nat.le_add_left j i).trans_lt hij)]

/-! ### Vandermonde comultiplication on Amice's basis -/

namespace AnalyticStage

variable {h : ℕ} {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- **Vandermonde comultiplication on Amice's basis** at level `h`, valid for every complete
ultrametric `ℤ_p`-module `E` including torsion modules. -/
theorem addComul_amiceTerm (n : ℕ) (e : E) :
    addComul S (amiceTerm p h n e) =
      ∑ ij ∈ Finset.antidiagonal n,
        amiceComulCoeff p h ij.1 ij.2 •
          prodSMul (amiceTerm p h ij.1 (1 : ℤ_[p])) (amiceTerm p h ij.2 e) := by
  have hZp : addComul ℤ_[p] (amiceTerm p h n (1 : ℤ_[p])) =
      ∑ ij ∈ Finset.antidiagonal n, amiceComulCoeff p h ij.1 ij.2 •
        prodSMul (amiceTerm p h ij.1 (1 : ℤ_[p])) (amiceTerm p h ij.2 (1 : ℤ_[p])) := by
    apply eval₂_injective ℤ_[p] (IsSMulRegular.of_ne_zero (Nat.cast_ne_zero.mpr hp.out.ne_zero))
    refine ContinuousMap.ext fun ⟨x, y⟩ ↦ ?_
    rw [eval₂_addComul, eval_amiceTerm ℤ_[p], map_sum, ContinuousMap.sum_apply]
    simp only [PadicInt.mahlerTerm_apply, mahler_apply, smul_eq_mul, nsmul_eq_mul, mul_one,
      Ring.add_choose_eq n (Commute.all x y), Finset.sum_mul]
    refine Finset.sum_congr rfl fun ij hij ↦ ?_
    rw [Finset.mem_antidiagonal] at hij
    rw [map_smul (eval₂ ℤ_[p]), ContinuousMap.smul_apply, eval₂_prodSMul, eval_amiceTerm ℤ_[p],
      eval_amiceTerm ℤ_[p]]
    simp only [PadicInt.mahlerTerm_apply, mahler_apply, smul_eq_mul, nsmul_eq_mul, mul_one]
    have hfac := factorial_mul_amiceComulCoeff (p := p) h ij.1 ij.2
    rw [hij] at hfac
    linear_combination (Ring.choose x ij.1 * Ring.choose y ij.2) * hfac.symm
  let w : ℤ_[p] →L[ℤ_[p]] E := ContinuousLinearMap.smulRight (1 : ℤ_[p] →L[ℤ_[p]] ℤ_[p]) e
  have hw : ∃ C, ∀ r : ℤ_[p], ‖w r‖ ≤ C * ‖r‖ :=
    ⟨‖e‖, fun r ↦ by simpa [w, mul_comm] using norm_smul_le r e⟩
  have hcomm := congr($(compLeft_addComul (p := p) (h := h) ℤ_[p] w hw)
    (amiceTerm p h n (1 : ℤ_[p])))
  simp only [ContinuousLinearMap.comp_apply,
    show compLeft w hw (amiceTerm p h n (1 : ℤ_[p])) = amiceTerm p h n e by ext; simp [w]] at hcomm
  rw [addComul_eq_of_scalars S ℤ_[p], ← hcomm, hZp, map_sum]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  rw [map_smul]; ext ⟨_, _⟩; simp [w, mul_smul]

/-- Below degree `pʰ`, `addComul S` expands `amiceTerm p h n e` by the unweighted Vandermonde sum.
-/
theorem addComul_amiceTerm_of_lt_pow {n : ℕ} (hn : n < p ^ h) (e : E) :
    addComul S (amiceTerm p h n e) =
      ∑ ij ∈ Finset.antidiagonal n,
        prodSMul (amiceTerm p h ij.1 (1 : ℤ_[p])) (amiceTerm p h ij.2 e) := by
  rw [addComul_amiceTerm S n e]
  exact Finset.sum_congr rfl fun ij hij ↦ by
    rw [amiceComulCoeff_of_lt_pow ((Finset.mem_antidiagonal.mp hij).trans_lt hn), one_smul]

end AnalyticStage

/-! ### Multiplicativity of the Amice transform -/

namespace LocallyAnalyticDistribution

open AnalyticStage LocallyAnalytic

variable {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

/-- The binomial series `(1 + X) ^ x` for `x ∈ ℤ_p` converges on the open unit disc. -/
theorem onOpenDisc_binomialSeries {R : Type*} [NormedRing R] [Algebra ℤ_[p] R]
    [IsBoundedSMul ℤ_[p] R] (x : ℤ_[p]) : (PowerSeries.binomialSeries R x).OnOpenDisc 1 :=
  PowerSeries.onOpenDisc_of_bddAbove_norm_coeff ⟨‖(1 : R)‖, by
    rintro _ ⟨n, rfl⟩
    dsimp only; rw [PowerSeries.binomialSeries_coeff]
    exact (norm_smul_le (Ring.choose x n) (1 : R)).trans
      (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _))⟩

/-- **The Amice transform of a Dirac distribution** is the binomial series `(1 + X) ^ x`. -/
@[simp] theorem amiceTransform_dirac (x : ℤ_[p]) :
    amiceTransform (dirac K x) = PowerSeries.binomialSeries K x := by
  rw [dirac_def, amiceTransform_ofMeasure, AbstractMeasure.amiceTransform_dirac]

/-- The Amice transform sends `1 = dirac K 0` to `1`. -/
@[simp] theorem amiceTransform_one : amiceTransform (1 : LocallyAnalyticDistribution p K) = 1 := by
  rw [one_def, amiceTransform_dirac, PowerSeries.binomialSeries_zero]

/-- **The Amice transform turns additive convolution into power series multiplication.** -/
@[simp] theorem amiceTransform_mul (μ ν : LocallyAnalyticDistribution p K) :
    amiceTransform (μ * ν) = amiceTransform μ * amiceTransform ν := by
  ext n
  have hn : n < p ^ n := Nat.lt_pow_self hp.out.one_lt
  rw [coeff_amiceTransform, mahlerTerm_def, ← stage_apply, stage_mul_apply,
    addComul_amiceTerm_of_lt_pow K hn, map_sum, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  have hij' : ij.1 + ij.2 < p ^ n := (Finset.mem_antidiagonal.mp hij).trans_lt hn
  rw [show prodSMul (amiceTerm p n ij.1 (1 : ℤ_[p])) (amiceTerm p n ij.2 (1 : K)) =
      prodSMul (amiceTerm p n ij.1 (1 : K)) (amiceTerm p n ij.2 (1 : K)) by
        ext ⟨_, _⟩; simp [Algebra.smul_def],
    prodPairing_prodSMul, stage_amiceTerm, stage_amiceTerm,
    Nat.div_eq_of_lt ((Nat.le_add_right ij.1 ij.2).trans_lt hij'),
    Nat.div_eq_of_lt ((Nat.le_add_left ij.2 ij.1).trans_lt hij')]
  simp

/-- The Amice transform sends `μ ^ n` to `(amiceTransform μ) ^ n`. -/
@[simp] theorem amiceTransform_pow (μ : LocallyAnalyticDistribution p K) (n : ℕ) :
    amiceTransform (μ ^ n) = amiceTransform μ ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, amiceTransform_mul, ih]

/-- **The Amice transform as a `K`-algebra homomorphism** into `PowerSeries K`. -/
noncomputable def amiceTransformₐ : LocallyAnalyticDistribution p K →ₐ[K] PowerSeries K :=
  AlgHom.ofLinearMap amiceTransform amiceTransform_one amiceTransform_mul

/-- `amiceTransformₐ` has underlying map `amiceTransform`. -/
@[simp] theorem coe_amiceTransformₐ (μ : LocallyAnalyticDistribution p K) :
    amiceTransformₐ μ = amiceTransform μ := (rfl)

/-- `amiceTransformₐ` extends `AbstractMeasure.amiceTransformₐ` along `ofMulMeasure`. -/
@[simp] theorem amiceTransformₐ_comp_ofMulMeasure :
    (amiceTransformₐ (p := p) (K := K)).comp ofMulMeasure = AbstractMeasure.amiceTransformₐ := by
  ext μ n
  simp only [AlgHom.comp_apply, coe_amiceTransformₐ, ofMulMeasure_def, amiceTransform_ofMeasure,
    AbstractMeasure.coeff_amiceTransform, AbstractMeasure.coeff_amiceTransformₐ,
    AbstractMeasure.arrowCongrLeft_apply]
  congr 1

section NormedAlgebra

variable [NormedAlgebra ℚ_[p] K]

/-- **Amice's theorem as a `K`-algebra isomorphism** with `PowerSeries.OnOpenDisc.subring K 1`. -/
noncomputable def amiceTransformEquivₐ :
    LocallyAnalyticDistribution p K ≃ₐ[K] PowerSeries.OnOpenDisc.subring K 1 :=
  AlgEquiv.ofLinearEquiv amiceTransformEquiv
    (Subtype.ext (by simp)) (fun _ _ ↦ Subtype.ext (by simp))

/-- `amiceTransformEquivₐ` has `amiceTransform` as its underlying power series. -/
@[simp] theorem coe_amiceTransformEquivₐ (μ : LocallyAnalyticDistribution p K) :
    (amiceTransformEquivₐ μ : PowerSeries K) = amiceTransform μ := coe_amiceTransformEquiv μ

/-- `amiceTransformEquivₐ` extends `amiceTransformEquiv`. -/
@[simp] theorem amiceTransformEquivₐ_toLinearEquiv :
    (amiceTransformEquivₐ (p := p) (K := K)).toLinearEquiv = amiceTransformEquiv := (rfl)

/-- The inverse of `amiceTransformEquivₐ` applies `ofOnOpenDisc`. -/
@[simp] theorem amiceTransformEquivₐ_symm_apply (F : PowerSeries.OnOpenDisc.subring K 1) :
    amiceTransformEquivₐ.symm F = ofOnOpenDisc p (PowerSeries.OnOpenDisc.mem_subring.mp F.2) :=
  amiceTransformEquiv_symm_apply F

/-- `ofOnOpenDisc` sends `1` to `1`. -/
@[simp] theorem ofOnOpenDisc_one (h1 : (1 : PowerSeries K).OnOpenDisc 1) :
    ofOnOpenDisc p h1 = 1 := amiceTransform_injective (by simp)

/-- `ofOnOpenDisc` turns power series multiplication into distribution convolution. -/
theorem ofOnOpenDisc_mul {F G : PowerSeries K} (hF : F.OnOpenDisc 1) (hG : G.OnOpenDisc 1) :
    ofOnOpenDisc p (hF.mul hG) = ofOnOpenDisc p hF * ofOnOpenDisc p hG :=
  amiceTransform_injective (by simp)

/-- `ofOnOpenDisc` recovers `dirac K x` from `(1 + X) ^ x`. -/
@[simp] theorem ofOnOpenDisc_binomialSeries (x : ℤ_[p])
    (hx : (PowerSeries.binomialSeries K x).OnOpenDisc 1) :
    ofOnOpenDisc p hx = dirac K x := amiceTransform_injective (by simp)

end NormedAlgebra

end LocallyAnalyticDistribution

end TauCeti
