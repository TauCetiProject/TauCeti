/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.Transform
public import TauCeti.NumberTheory.Padics.Measure.Moments

/-!
# Additive convolution of locally analytic distributions

The convolution of two distributions `μ, ν` on `ℤ_p` is the two-variable pairing

`(μ * ν)(f) = μ(x ↦ ν(y ↦ f(x + y)))`.

This file constructs the inner function `x ↦ ν(y ↦ f(x + y))` as a locally analytic function,
stage by stage, in Amice's coordinates. Write `m_h(n) = ⌊n / pʰ⌋!` and
`e_{h,n}(x) = m_h(n) (x choose n)` for Amice's orthonormal basis of the stage `LA_h`. Vandermonde's
identity `(x + y choose n) = ∑_{i + j = n} (x choose i) (y choose j)` gives

`e_{h,i+j}(x + y) = ∑ N_h(i, j) e_{h,i}(x) e_{h,j}(y)`,  `N_h(i, j) = m_h(i+j) / (m_h(i) m_h(j))`,

where `N_h(i, j)` is an integer (`TauCeti.amiceConvCoeff`) because
`⌊i / pʰ⌋ + ⌊j / pʰ⌋ ≤ ⌊(i + j) / pʰ⌋`. So for a continuous linear functional `ℓ` on `LA_h(K)`,
the function `x ↦ ℓ(y ↦ e_{h,n}(x + y))` has the finite expansion
`∑_{i ≤ n} N_h(i, n - i) ℓ(e_{h,n-i}) e_{h,i}`. These columns define a matrix with entries bounded
by `‖ℓ‖`, hence a continuous linear operator `TauCeti.AnalyticStage.convolveFunRight ℓ` on
`LA_h(K)` of norm at most `‖ℓ‖`. The operators are compatible with re-expansion between the
levels, so a distribution `ν` gives a linear operator
`TauCeti.LocallyAnalyticDistribution.convolveFunRight ν` on the algebraic direct limit
`LA(ℤ_p, K)`. On Mahler terms it is Vandermonde's identity
(`TauCeti.LocallyAnalyticDistribution.convolveFunRight_mahlerTerm`):

`ν(y ↦ (x + y choose n)) = ∑_{i ≤ n} ν(y ↦ (y choose n - i)) (x choose i)`.

When `ν` comes from a measure, the operator evaluates to the function `x ↦ ν(y ↦ f(x + y))` for
every locally analytic `f` (`TauCeti.LocallyAnalyticDistribution.eval_convolveFunRight_ofMeasure`).

The convolution `μ * ν` is the composite `μ ∘ convolveFunRight ν`, following Mathlib's
`AbstractMeasure.mul_apply` for measures on a monoid. On each stage it is bounded by the product
of the stage seminorms, and its moments are the Cauchy products of the moments of `μ` and `ν`:
the Amice transform takes convolution to multiplication of power series
(`TauCeti.LocallyAnalyticDistribution.amiceTransform_mul`). Since the Amice transform is
injective, convolution makes the distributions a commutative `K`-algebra with unit the Dirac
distribution at `0`, and the Amice transform is a `K`-algebra homomorphism
(`TauCeti.LocallyAnalyticDistribution.amiceTransformAlgHom`). Dirac distributions multiply as
`δ_x * δ_y = δ_{x+y}`, their transforms being the binomial series `(1 + T) ^ x`.

## Main definitions

* `TauCeti.amiceConvCoeff p h i j`: the integer `⌊(i+j) / pʰ⌋! / (⌊i / pʰ⌋! ⌊j / pʰ⌋!)`.
* `TauCeti.AnalyticStage.convolveFunRight ℓ`: the right convolution operator on `LA_h(K)` by a
  continuous linear functional `ℓ` on `LA_h(K)`.
* `TauCeti.LocallyAnalyticDistribution.convolveFunRight ν`: the right convolution operator on
  `LA(ℤ_p, K)` by a distribution `ν`.
* `TauCeti.LocallyAnalyticDistribution.amiceTransformAlgHom`: the Amice transform as a
  `K`-algebra homomorphism from the convolution algebra of distributions.

## Main results

* `TauCeti.AnalyticStage.transition_convolveFunRight`: the stage operators commute with
  re-expansion.
* `TauCeti.LocallyAnalyticDistribution.eval_convolveFunRight_ofMeasure`: for a measure `ν`,
  right convolution is `f ↦ (x ↦ ν(y ↦ f(x + y)))`.
* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_mul_le`: the stage seminorms are
  submultiplicative for convolution.
* `TauCeti.LocallyAnalyticDistribution.amiceTransform_mul`: the Amice transform of a convolution
  is the product of the Amice transforms.
* `TauCeti.LocallyAnalyticDistribution.ofMeasure_dirac_mul_ofMeasure_dirac`: `δ_x * δ_y = δ_{x+y}`.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.2.
* P. Schneider and J. Teitelbaum, *p-adic Fourier theory*, Documenta Math. 6 (2001), 447–481.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.
-/

public section

open Nat Filter Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

namespace TauCeti

section ConvCoeff

variable (p : ℕ)

/-- The integer `N_h(i, j) = ⌊(i + j) / pʰ⌋! / (⌊i / pʰ⌋! ⌊j / pʰ⌋!)`, the coefficient of
`e_{h,i}(x) e_{h,j}(y)` in the expansion of Amice's polynomial `e_{h,i+j}(x + y)`, where
`e_{h,n}(x) = ⌊n / pʰ⌋! (x choose n)`. -/
def amiceConvCoeff (h i j : ℕ) : ℕ :=
  ((i + j) / p ^ h)! / ((i / p ^ h)! * (j / p ^ h)!)

variable {p}

/-- The defining identity `⌊i / pʰ⌋! ⌊j / pʰ⌋! N_h(i, j) = ⌊(i + j) / pʰ⌋!`. -/
theorem factorial_mul_factorial_mul_amiceConvCoeff (h i j : ℕ) :
    (i / p ^ h)! * (j / p ^ h)! * amiceConvCoeff p h i j = ((i + j) / p ^ h)! :=
  Nat.mul_div_cancel' <| (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
    (Nat.factorial_dvd_factorial Nat.div_add_div_le_add_div)

/-- In the first block, `N_h(i, j) = 1`. -/
theorem amiceConvCoeff_of_lt {h i j : ℕ} (hij : i + j < p ^ h) : amiceConvCoeff p h i j = 1 := by
  rw [amiceConvCoeff, Nat.div_eq_of_lt hij, Nat.div_eq_of_lt ((Nat.le_add_right i j).trans_lt hij),
    Nat.div_eq_of_lt ((Nat.le_add_left j i).trans_lt hij), factorial_zero]

variable [hp : Fact p.Prime]

/-- Raising the level from `h` to `h + 1` is compatible with the coefficients `N_h`: in terms of
the diagonal transition multipliers `t_h(n) = ⌊n / pʰ⌋! / ⌊n / p^(h+1)⌋!`,
`t_h(i + j) N_{h+1}(i, j) = t_h(i) t_h(j) N_h(i, j)`. -/
theorem amiceTransitionCoeff_add_mul_amiceConvCoeff (h i j : ℕ) :
    amiceTransitionCoeff p h (i + j) * (amiceConvCoeff p (h + 1) i j : ℤ_[p]) =
      amiceTransitionCoeff p h i * amiceTransitionCoeff p h j *
        (amiceConvCoeff p h i j : ℤ_[p]) := by
  have hne : ((i / p ^ (h + 1))! * (j / p ^ (h + 1))! : ℤ_[p]) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)
  have hN (k : ℕ) : ((i / p ^ k)! * (j / p ^ k)! * amiceConvCoeff p k i j : ℤ_[p]) =
      ((i + j) / p ^ k)! := by
    exact_mod_cast factorial_mul_factorial_mul_amiceConvCoeff (p := p) k i j
  refine mul_right_cancel₀ hne ?_
  linear_combination (amiceTransitionCoeff p h (i + j)) * hN (h + 1) +
    factorial_mul_amiceTransitionCoeff (p := p) h (i + j) - hN h -
    ((j / p ^ (h + 1))! * amiceTransitionCoeff p h j * (amiceConvCoeff p h i j : ℤ_[p])) *
      factorial_mul_amiceTransitionCoeff (p := p) h i -
    ((i / p ^ h)! * (amiceConvCoeff p h i j : ℤ_[p])) *
      factorial_mul_amiceTransitionCoeff (p := p) h j

end ConvCoeff

variable {p : ℕ} [hp : Fact p.Prime]
  {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

namespace AnalyticStage

variable {h : ℕ}

/-- The matrix, in Amice's coordinates, of `f ↦ (x ↦ ℓ(y ↦ f(x + y)))` on `LA_h(K)`: its entry at
`(i, n)` is `N_h(i, n - i) ℓ(e_{h,n-i})` for `i ≤ n`, and zero otherwise. -/
private noncomputable def convolveMatrix (ℓ : AnalyticStage p h K →L[K] K) : Matrix ℕ ℕ K :=
  fun i n ↦ if i ≤ n then (amiceConvCoeff p h i (n - i) : K) * ℓ (amiceTerm p h (n - i) 1) else 0

omit [IsBoundedSMul ℤ_[p] K] [CompleteSpace K] in
private theorem tendsto_convolveMatrix (ℓ : AnalyticStage p h K →L[K] K) (n : ℕ) :
    Tendsto (fun i ↦ convolveMatrix ℓ i n) cofinite (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_gt_atTop n] with i hi
  simp [convolveMatrix, Nat.not_le.2 hi]

omit [CompleteSpace K] in
private theorem norm_convolveMatrix_le (ℓ : AnalyticStage p h K →L[K] K) (i n : ℕ) :
    ‖convolveMatrix ℓ i n‖ ≤ ‖ℓ‖ := by
  unfold convolveMatrix
  split_ifs
  · rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _)
      (IsUltrametricDist.norm_natCast_le_one K _)).trans ?_
    simpa using ℓ.le_opNorm_of_le (norm_amiceTerm_le (p := p) (h := h) (n - i) (1 : K))
  · rw [norm_zero]
    exact norm_nonneg ℓ

/-- **Right convolution on an analytic stage** by a continuous linear functional `ℓ` on
`LA_h(K)`: the continuous linear operator sending Amice's vector `e_{h,n}` to the expansion
`∑_{i ≤ n} N_h(i, n - i) ℓ(e_{h,n-i}) e_{h,i}` of `x ↦ ℓ(y ↦ e_{h,n}(x + y))`
(`convolveFunRight_amiceTerm`). For the restriction of a measure it is
`f ↦ (x ↦ ℓ(y ↦ f(x + y)))` (`LocallyAnalyticDistribution.eval_convolveFunRight_ofMeasure`). -/
noncomputable def convolveFunRight (ℓ : AnalyticStage p h K →L[K] K) :
    AnalyticStage p h K →L[K] AnalyticStage p h K :=
  (amiceEquiv p h K (E := K) : C₀(ℕ, K) →L[K] AnalyticStage p h K) ∘L
    (convolveMatrix ℓ).toZeroAtInftySMulCLM K (tendsto_convolveMatrix ℓ)
      ⟨‖ℓ‖, norm_convolveMatrix_le ℓ⟩ ∘L
    ((amiceEquiv p h K (E := K)).symm : AnalyticStage p h K →L[K] C₀(ℕ, K))

/-- Right convolution on Amice's vectors: `x ↦ ℓ(y ↦ e_{h,n}(x + y)) • e` is
`∑_{i ≤ n} N_h(i, n - i) ℓ(e_{h,n-i}) e_{h,i} • e`. -/
theorem convolveFunRight_amiceTerm (ℓ : AnalyticStage p h K →L[K] K) (n : ℕ) (e : K) :
    convolveFunRight ℓ (amiceTerm p h n e) = ∑ i ∈ Finset.range (n + 1),
      amiceTerm p h i (((amiceConvCoeff p h i (n - i) : K) * ℓ (amiceTerm p h (n - i) 1)) * e) := by
  apply (amiceEquiv p h K (E := K)).symm.injective
  simp only [convolveFunRight, ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'',
    amiceEquiv_symm_amiceTerm, LinearIsometryEquiv.symm_apply_apply, map_sum]
  ext i
  rw [Matrix.toZeroAtInftySMulCLM_single_apply, coe_sum, Finset.sum_apply]
  by_cases hi : i ≤ n
  · rw [Finset.sum_eq_single i (fun k _ hk ↦ single_eq_of_ne (Ne.symm hk) _)
      (fun hi' ↦ absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) hi')]
    simp [convolveMatrix, hi]
  · rw [Finset.sum_eq_zero fun k hk ↦ single_eq_of_ne
      (by rintro rfl; exact hi (Nat.le_of_lt_succ (Finset.mem_range.1 hk))) _]
    simp [convolveMatrix, hi]

omit [IsBoundedSMul ℤ_[p] K] [CompleteSpace K] in
/-- A functional takes Amice's vector with integral coefficient `t` to `t` times its value on
Amice's vector with coefficient `1`. -/
private theorem apply_amiceTerm_smul_one {k : ℕ} (ℓ : AnalyticStage p k K →L[K] K) (j : ℕ)
    (t : ℤ_[p]) :
    ℓ (amiceTerm p k j (t • (1 : K))) = algebraMap ℤ_[p] K t * ℓ (amiceTerm p k j 1) := by
  rw [← algebraMap_smul K t (1 : K), amiceTerm_smul, map_smul, smul_eq_mul]

/-- **Right convolution commutes with re-expansion.** For a functional `ℓ` on `LA_{h+1}(K)`,
re-expanding `x ↦ (ℓ ∘ transition)(y ↦ f(x + y))` gives `x ↦ ℓ(y ↦ (transition f)(x + y))`. -/
theorem transition_convolveFunRight (ℓ : AnalyticStage p (h + 1) K →L[K] K)
    (c : AnalyticStage p h K) :
    transition K (convolveFunRight (ℓ ∘L transition K) c) =
      convolveFunRight ℓ (transition K c) := by
  have key : transition K ∘L convolveFunRight (ℓ ∘L transition K) =
      convolveFunRight ℓ ∘L transition K := by
    refine continuousLinearMap_ext_amiceTerm fun n ↦ ?_
    simp only [ContinuousLinearMap.comp_apply, convolveFunRight_amiceTerm, map_sum,
      transition_amiceTerm, apply_amiceTerm_smul_one]
    refine Finset.sum_congr rfl fun i hi ↦ congrArg (amiceTerm p (h + 1) i) ?_
    have hin : i + (n - i) = n := Nat.add_sub_cancel' (Nat.le_of_lt_succ (Finset.mem_range.1 hi))
    have hcoeff := congrArg (algebraMap ℤ_[p] K)
      (amiceTransitionCoeff_add_mul_amiceConvCoeff (p := p) h i (n - i))
    simp only [hin, map_mul, map_natCast] at hcoeff
    rw [Algebra.smul_def, Algebra.smul_def, mul_one]
    linear_combination (-ℓ (amiceTerm p (h + 1) (n - i) 1)) * hcoeff
  exact DFunLike.congr_fun key c

/-- Right convolution commutes with re-expansion between any two levels. -/
theorem transitionLE_convolveFunRight {k : ℕ} (hhk : h ≤ k) (ℓ : AnalyticStage p k K →L[K] K)
    (c : AnalyticStage p h K) :
    transitionLE K hhk (convolveFunRight (ℓ ∘L transitionLE K hhk) c) =
      convolveFunRight ℓ (transitionLE K hhk c) := by
  induction k, hhk using Nat.le_induction generalizing c with
  | base => simp [transitionLE_self]
  | succ k hhk ih =>
    rw [transitionLE_succ K hhk, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.comp_assoc, ih, transition_convolveFunRight]

/-- Right convolution is bounded by the norm of the functional. -/
theorem norm_convolveFunRight_apply_le (ℓ : AnalyticStage p h K →L[K] K)
    (c : AnalyticStage p h K) : ‖convolveFunRight ℓ c‖ ≤ ‖ℓ‖ * ‖c‖ := by
  simp only [convolveFunRight, ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'',
    LinearIsometryEquiv.norm_map]
  simpa using (convolveMatrix ℓ).norm_toZeroAtInftySMulCLM_apply_le K (tendsto_convolveMatrix ℓ)
    ⟨‖ℓ‖, norm_convolveMatrix_le ℓ⟩ (norm_nonneg ℓ) (norm_convolveMatrix_le ℓ)
    ((amiceEquiv p h K (E := K)).symm c)

/-- The operator norm of right convolution is at most the norm of the functional. -/
theorem opNorm_convolveFunRight_le (ℓ : AnalyticStage p h K →L[K] K) :
    ‖convolveFunRight ℓ‖ ≤ ‖ℓ‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg ℓ) (norm_convolveFunRight_apply_le ℓ)

end AnalyticStage

namespace LocallyAnalyticDistribution

open AnalyticStage LocallyAnalytic

/-- **Right convolution by a distribution**, `f ↦ (x ↦ ν(y ↦ f(x + y)))`: the linear operator on
locally analytic functions induced by the stage operators
`AnalyticStage.convolveFunRight (stage h ν)`, which are compatible with re-expansion. On Mahler
terms it is given by Vandermonde's identity (`convolveFunRight_mahlerTerm`), and for a measure it
evaluates to the pairing above (`eval_convolveFunRight_ofMeasure`). -/
noncomputable def convolveFunRight (ν : LocallyAnalyticDistribution p K) :
    LocallyAnalytic p K K →ₗ[K] LocallyAnalytic p K K :=
  Module.DirectLimit.lift K ℕ (fun k ↦ AnalyticStage p k K)
    (fun _ _ hhk ↦ (transitionLE K hhk).toLinearMap)
    (fun h ↦ ofStage K h ∘ₗ (AnalyticStage.convolveFunRight (stage h ν)).toLinearMap)
    fun h k hhk c ↦ by
      simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply]
      rw [← stage_comp_transitionLE ν hhk, ← transitionLE_convolveFunRight, ofStage_transitionLE]

/-- Right convolution by `ν` on the class of a stage vector is the stage operator of the
restriction of `ν`. -/
@[simp]
theorem convolveFunRight_ofStage (ν : LocallyAnalyticDistribution p K) (h : ℕ)
    (c : AnalyticStage p h K) :
    convolveFunRight ν (ofStage K h c) =
      ofStage K h (AnalyticStage.convolveFunRight (stage h ν) c) :=
  lift_ofStage K _ _ h c

/-- **Vandermonde's identity.** Right convolution by `ν` sends the Mahler term
`x ↦ (x choose n) • e` to `x ↦ ∑_{i ≤ n} (x choose i) • (e bₙ₋ᵢ)`, where `bⱼ = ν(y ↦ (y choose j))`
is the `j`-th moment of `ν`. -/
theorem convolveFunRight_mahlerTerm (ν : LocallyAnalyticDistribution p K) (e : K) (n : ℕ) :
    convolveFunRight ν (mahlerTerm p K e n) =
      ∑ i ∈ Finset.range (n + 1), mahlerTerm p K ((amiceTransform ν).coeff (n - i) * e) i := by
  have hn := Nat.lt_pow_self (n := n) hp.out.one_lt
  rw [mahlerTerm_def, convolveFunRight_ofStage, convolveFunRight_amiceTerm, map_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hi)
  rw [ofStage_amiceTerm, stage_amiceTerm,
    amiceConvCoeff_of_lt ((Nat.add_sub_cancel' hi).trans_lt hn), Nat.div_eq_of_lt (hi.trans_lt hn),
    Nat.div_eq_of_lt ((Nat.sub_le n i).trans_lt hn)]
  simp

/-- On the stage `LA_h(K)`, evaluating at `x` the right convolution by a measure `ν` agrees with
integrating against `ν` the translate by `x`: both are continuous linear functionals, and on
Amice's vectors they agree by Vandermonde's identity
`(x + y choose n) = ∑_{i ≤ n} (x choose i) (y choose n - i)`. -/
private theorem evalCLM_comp_convolveFunRight_ofMeasure (ν : AbstractMeasure ℤ_[p] K K) (h : ℕ)
    (x : ℤ_[p]) :
    ContinuousMap.evalCLM K x ∘L AnalyticStage.eval K ∘L
        AnalyticStage.convolveFunRight (stage h (ofMeasure ν)) =
      AbstractMeasure.toCLMEquiv ν ∘L ContinuousMap.compCLM K K ⟨fun y ↦ x + y, by fun_prop⟩ ∘L
        AnalyticStage.eval K := by
  refine continuousLinearMap_ext_amiceTerm fun n ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, convolveFunRight_amiceTerm, map_sum,
    eval_amiceTerm, stage_amiceTerm, ContinuousMap.evalCLM_apply, ContinuousMap.compCLM_apply,
    AbstractMeasure.coe_toCLMEquiv, amiceTransform_ofMeasure,
    AbstractMeasure.coeff_amiceTransform]
  -- Vandermonde's identity for the translate of the Mahler term of degree `n`.
  have hfun : (PadicInt.mahlerTerm ((n / p ^ h)! • (1 : K)) n).comp ⟨fun y ↦ x + y, by fun_prop⟩ =
      ∑ i ∈ Finset.range (n + 1),
        ((mahler i : C(ℤ_[p], ℤ_[p])) x • ((n / p ^ h)! : K)) •
          ((mahler (n - i) : C(ℤ_[p], ℤ_[p])) • 1 : C(ℤ_[p], K)) := by
    ext y
    simp only [ContinuousMap.comp_apply, PadicInt.mahlerTerm_apply, ContinuousMap.coe_sum,
      Finset.sum_apply, ContinuousMap.smul_apply, ContinuousMap.smul_apply',
      ContinuousMap.one_apply, mahler_apply, ContinuousMap.coe_mk]
    rw [Ring.add_choose_eq _ (Commute.all x y), Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Algebra.smul_def, map_sum, map_mul, mul_one, Finset.sum_mul,
      Algebra.algebraMap_self, RingHom.id_apply, eq_natCast]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  rw [hfun, map_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  -- The weights match: `⌊i / pʰ⌋! ⌊(n - i) / pʰ⌋! N_h(i, n - i) = ⌊n / pʰ⌋!`.
  have hK : ((i / p ^ h)! : K) * ((n - i) / p ^ h)! * amiceConvCoeff p h i (n - i) =
      (n / p ^ h)! := by
    have := factorial_mul_factorial_mul_amiceConvCoeff (p := p) h i (n - i)
    rw [Nat.add_sub_cancel' (Nat.le_of_lt_succ (Finset.mem_range.1 hi))] at this
    simpa using congrArg (Nat.cast : ℕ → K) this
  rw [map_smul ν ((mahler i : C(ℤ_[p], ℤ_[p])) x • ((n / p ^ h)! : K)),
    PadicInt.mahlerTerm_apply, smul_eq_mul]
  simp only [Algebra.smul_def, mul_one, eq_natCast]
  linear_combination
    (algebraMap ℤ_[p] K ((mahler i : C(ℤ_[p], ℤ_[p])) x) *
      ν ((mahler (n - i) : C(ℤ_[p], ℤ_[p])) • 1)) * hK

/-- **Right convolution by a measure is the two-variable pairing**: for a measure `ν`, right
convolution by its distribution sends `f` to the function `x ↦ ν(y ↦ f(x + y))`. -/
theorem eval_convolveFunRight_ofMeasure (ν : AbstractMeasure ℤ_[p] K K)
    (f : LocallyAnalytic p K K) (x : ℤ_[p]) :
    eval K (convolveFunRight (ofMeasure ν) f) x = ν ⟨fun y ↦ eval K f (x + y), by fun_prop⟩ := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  have hc := DFunLike.congr_fun (evalCLM_comp_convolveFunRight_ofMeasure ν h x) c
  simp only [ContinuousLinearMap.comp_apply, AbstractMeasure.coe_toCLMEquiv,
    ContinuousMap.compCLM_apply, ContinuousMap.evalCLM_apply] at hc
  rw [← ofStage_def, convolveFunRight_ofStage]
  simp only [eval_ofStage]
  exact hc

/-- The **convolution** of locally analytic distributions,
`(μ * ν)(f) = μ(x ↦ ν(y ↦ f(x + y)))` (`mul_apply`). Its restriction to each stage is the
composite of continuous maps (`stage_mul`), so it is again a distribution. -/
noncomputable instance instMul : Mul (LocallyAnalyticDistribution p K) where
  mul μ ν := ⟨(μ : Module.Dual K (LocallyAnalytic p K K)) ∘ₗ convolveFunRight ν,
    mem_iff.mpr fun h ↦ by
      refine (stage h μ ∘L AnalyticStage.convolveFunRight (stage h ν)).continuous.congr
        fun c ↦ ?_
      simp⟩

/-- The convolution of `μ` and `ν` evaluates `μ` on the right convolution of `f` by `ν`. -/
theorem mul_apply (μ ν : LocallyAnalyticDistribution p K) (f : LocallyAnalytic p K K) :
    ((μ * ν : LocallyAnalyticDistribution p K) : Module.Dual K (LocallyAnalytic p K K)) f =
      (μ : Module.Dual K (LocallyAnalytic p K K)) (convolveFunRight ν f) :=
  (rfl)

/-- On the stage `LA_h(K)`, convolution by `ν` is the stage operator of the restriction of `ν`. -/
theorem stage_mul (μ ν : LocallyAnalyticDistribution p K) (h : ℕ) :
    stage h (μ * ν) = stage h μ ∘L AnalyticStage.convolveFunRight (stage h ν) := by
  ext c
  simp [mul_apply]

/-- **The stage seminorms are submultiplicative for convolution.** -/
theorem stageSeminorm_mul_le (μ ν : LocallyAnalyticDistribution p K) (h : ℕ) :
    stageSeminorm h (μ * ν) ≤ stageSeminorm h μ * stageSeminorm h ν := by
  simp only [stageSeminorm_apply, stage_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (opNorm_convolveFunRight_le _) (norm_nonneg _))

/-- **The Amice transform takes convolution to multiplication.** The moments of `μ * ν` are the
Cauchy products of the moments of `μ` and `ν`. -/
@[simp]
theorem amiceTransform_mul (μ ν : LocallyAnalyticDistribution p K) :
    amiceTransform (μ * ν) = amiceTransform μ * amiceTransform ν := by
  ext n
  rw [coeff_amiceTransform, mul_apply, convolveFunRight_mahlerTerm, map_sum, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← mul_one ((amiceTransform ν).coeff (n - i)), ← smul_eq_mul _ (1 : K), mahlerTerm_smul,
    map_smul, smul_eq_mul, mul_one, mul_comm]
  simp

/-! ### The convolution algebra -/

/-- The Amice transform of the Dirac distribution at `x` is the binomial series `(1 + T) ^ x`. -/
theorem amiceTransform_ofMeasure_dirac (x : ℤ_[p]) :
    amiceTransform (ofMeasure (AbstractMeasure.dirac K x)) = PowerSeries.binomialSeries K x := by
  rw [amiceTransform_ofMeasure, AbstractMeasure.amiceTransform_dirac]

/-- The unit for convolution is the Dirac distribution at `0`. -/
noncomputable instance instOne : One (LocallyAnalyticDistribution p K) :=
  ⟨ofMeasure (AbstractMeasure.dirac K 0)⟩

/-- The unit for convolution is the Dirac distribution at `0`. -/
theorem one_def :
    (1 : LocallyAnalyticDistribution p K) = ofMeasure (AbstractMeasure.dirac K 0) :=
  (rfl)

/-- The unit for convolution evaluates a locally analytic function at `0`. -/
@[simp]
theorem one_apply (f : LocallyAnalytic p K K) :
    ((1 : LocallyAnalyticDistribution p K) : Module.Dual K (LocallyAnalytic p K K)) f =
      LocallyAnalytic.eval K f 0 := by
  rw [one_def, coe_ofMeasure_apply, AbstractMeasure.dirac_apply]

/-- The Amice transform of the unit is `1`. -/
@[simp]
theorem amiceTransform_one : amiceTransform (1 : LocallyAnalyticDistribution p K) = 1 := by
  rw [one_def, amiceTransform_ofMeasure_dirac, PowerSeries.binomialSeries_zero]

/-- The natural number `n` as a distribution is `n` times the unit. -/
noncomputable instance instNatCast : NatCast (LocallyAnalyticDistribution p K) :=
  ⟨fun n ↦ (n : K) • 1⟩

/-- The integer `n` as a distribution is `n` times the unit. -/
noncomputable instance instIntCast : IntCast (LocallyAnalyticDistribution p K) :=
  ⟨fun n ↦ (n : K) • 1⟩

/-- Iterated convolution. -/
noncomputable instance instPow : Pow (LocallyAnalyticDistribution p K) ℕ :=
  ⟨fun μ n ↦ npowRec n μ⟩

/-- **The convolution algebra.** Convolution makes the locally analytic distributions on `ℤ_p` a
commutative ring, with unit the Dirac distribution at `0`. The ring laws are transported along the
injective Amice transform (`amiceTransform_injective`, `amiceTransform_mul`). -/
noncomputable instance instCommRing : CommRing (LocallyAnalyticDistribution p K) :=
  amiceTransform_injective.commRing _ (map_zero _) amiceTransform_one (map_add _) amiceTransform_mul
    (map_neg _) (map_sub _) (fun _ _ ↦ map_nsmul _ _ _) (fun _ _ ↦ map_zsmul _ _ _)
    (fun μ n ↦ by
      -- unfold the power instance above to its recursive definition
      change amiceTransform (npowRec n μ) = _
      induction n with
      | zero => rw [npowRec, amiceTransform_one, pow_zero]
      | succ n ih => rw [npowRec, amiceTransform_mul, ih, pow_succ])
    (fun n ↦ by
      -- unfold the cast instance above
      change amiceTransform ((n : K) • (1 : LocallyAnalyticDistribution p K)) = n
      rw [map_smul, amiceTransform_one, Nat.cast_smul_eq_nsmul, nsmul_one])
    (fun n ↦ by
      -- unfold the cast instance above
      change amiceTransform ((n : K) • (1 : LocallyAnalyticDistribution p K)) = n
      rw [map_smul, amiceTransform_one, Int.cast_smul_eq_zsmul, zsmul_one])

/-- Convolution is `K`-bilinear, so the distributions form a commutative `K`-algebra. -/
noncomputable instance instAlgebra : Algebra K (LocallyAnalyticDistribution p K) :=
  Algebra.ofModule
    (fun r μ ν ↦ amiceTransform_injective (by simp [amiceTransform_mul]))
    (fun r μ ν ↦ amiceTransform_injective (by simp [amiceTransform_mul]))

variable (p K) in
/-- **The Amice transform is a `K`-algebra homomorphism** from the convolution algebra of locally
analytic distributions to the power series over `K`. It is injective
(`amiceTransform_injective`), with image the power series on the open unit disc when `K` is a
normed `ℚ_p`-algebra (`mem_range_amiceTransform_iff`). -/
noncomputable def amiceTransformAlgHom : LocallyAnalyticDistribution p K →ₐ[K] PowerSeries K :=
  AlgHom.ofLinearMap amiceTransform amiceTransform_one amiceTransform_mul

/-- The algebra homomorphism `amiceTransformAlgHom` is the Amice transform. -/
@[simp]
theorem coe_amiceTransformAlgHom :
    ⇑(amiceTransformAlgHom p K) = amiceTransform :=
  (rfl)

/-- **Dirac distributions multiply by adding their points**: `δ_x * δ_y = δ_{x+y}`. -/
theorem ofMeasure_dirac_mul_ofMeasure_dirac (x y : ℤ_[p]) :
    ofMeasure (AbstractMeasure.dirac K x) * ofMeasure (AbstractMeasure.dirac K y) =
      ofMeasure (AbstractMeasure.dirac K (x + y)) :=
  amiceTransform_injective <| by
    rw [amiceTransform_mul, amiceTransform_ofMeasure_dirac, amiceTransform_ofMeasure_dirac,
      amiceTransform_ofMeasure_dirac, PowerSeries.binomialSeries_add]

end LocallyAnalyticDistribution

end TauCeti
