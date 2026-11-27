/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree.Basic
public import TauCeti.NumberTheory.NumberField.Quadratic.EmbeddingBound
public import TauCeti.NumberTheory.NumberField.Quadratic.Model
public import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm

import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Checks for the Arakelov degree of hermitian lines

Checks for the degree `log #(E / 𝓞 K • s) - Σ_σ log ‖s‖_σ` of
`TauCeti.HermitianMetric.sectionDegree`.

* Degrees of hermitian lines: the Gaussian ideal `(1 + i)` of `ℚ(i)` with its standard metric
  has degree `-log 2` and normalized degree `-(1/2) log 2`; over `ℚ`, `(ℤ, r |·|)` has degree
  `-log r`.
* Independence of the section, term by term: in `Ō_ℚ`, the section `2` has finite term `log 2`
  and archimedean term `log 2`. In `ℚ(√2)`, the unit `1 + √2` leaves the finite term and the sum
  of the archimedean terms unchanged, although it changes the norm at the embedding `√2 ↦ √2`.
  On the trivial line over `ℚ(i)`, replacing `1` by `2` raises the finite term by `log 4`
  and the sum over the two complex embeddings by `2 log 2`, whereas the sum over the single
  complex place, without its multiplicity `2`, is only `log 2`.

`ℚ(i)` and `ℚ(√2)` are the models `QuadraticAlgebra ℚ d 0`, whose rings of integers are compared
with `ℤ[√d]` by `QuadraticAlgebra.ringOfIntegersEquiv`.
-/

public section

open scoped NumberField TensorProduct nonZeroDivisors
open NumberField TauCeti

local instance TauCeti.ArakelovDegreeChecks.instFactNotIsSquareNegOne :
    Fact (¬ IsSquare (-1 : ℤ)) :=
  ⟨not_isSquare_of_neg (by norm_num)⟩

local instance TauCeti.ArakelovDegreeChecks.instFactNotIsSquareTwo :
    Fact (¬ IsSquare (2 : ℤ)) :=
  ⟨Int.prime_two.not_isSquare⟩

namespace TauCeti.ArakelovDegreeChecks

/-- The Gaussian rationals `ℚ(i)`. -/
abbrev K := QuadraticAlgebra ℚ ((-1 : ℤ) : ℚ) 0

/-- The real quadratic field `ℚ(√2)`. -/
abbrev L := QuadraticAlgebra ℚ ((2 : ℤ) : ℚ) 0

/-- `1 + √d` is a nonzero element of `ℤ[√d] ⊆ 𝓞 ℚ(√d)`. -/
private theorem coe_ringOfIntegersEquiv_symm_one_one_ne_zero {d : ℤ} [Fact (¬ IsSquare d)]
    (hsf : Squarefree d) (hd4 : d % 4 ≠ 1) :
    ((QuadraticAlgebra.ringOfIntegersEquiv hsf hd4).symm ⟨1, 1⟩ :
      QuadraticAlgebra ℚ (d : ℚ) 0) ≠ 0 := by
  rw [QuadraticAlgebra.ringOfIntegersEquiv_symm_apply_coe]
  intro h
  simpa using congrArg QuadraticAlgebra.re h

/-- The ideal `(2)` of `𝓞 F` has index `2 ^ [F : ℚ]`. -/
private theorem cardQuot_span_two (F : Type*) [Field F] [NumberField F] :
    ((Submodule.span (𝓞 F) {(2 : 𝓞 F)}).cardQuot : ℝ) = 2 ^ Module.finrank ℚ F := by
  rw [← Ideal.absNorm_apply, ← Nat.cast_ofNat (R := 𝓞 F) (n := 2), Ideal.absNorm_span_natCast,
    RingOfIntegers.rank]
  norm_num

/-- The embedding `√2 ↦ √2` sends `1 + √2 ∈ 𝓞 ℚ(√2)` to the real number `1 + √2`. -/
private theorem sqrtEmbedding_ringOfIntegersEquiv_symm_one_one :
    QuadraticAlgebra.sqrtEmbedding ((2 : ℤ) : ℚ)
        ((QuadraticAlgebra.ringOfIntegersEquiv (d := 2) Int.prime_two.squarefree (by norm_num)).symm
          ⟨1, 1⟩ : L) = ((1 + √2 : ℝ) : ℂ) := by
  rw [QuadraticAlgebra.ringOfIntegersEquiv_symm_apply_coe, QuadraticAlgebra.sqrtEmbedding_apply,
    QuadraticAlgebra.sqrtRadicand_of_nonneg (by norm_num)]
  norm_num

/-! ### Degrees of hermitian lines -/

/-- `(ℤ, r |·|)` over `ℚ`, the trivial line with every norm multiplied by `r = e^{log r}`, has
degree `-log r`. -/
example (r : ℝ) (hr : 0 < r) (σ : ℚ →+* ℂ) :
    ((HermitianMetric.trivial ℚ).rescale (-Real.log r)).norm σ (1 ⊗ₜ 1) = r ∧
      ((HermitianMetric.trivial ℚ).rescale (-Real.log r)).sectionDegree 1 = -Real.log r := by
  refine ⟨by simp [Real.exp_log hr], ?_⟩
  rw [HermitianMetric.sectionDegree_rescale _ _ one_ne_zero,
    HermitianMetric.sectionDegree_trivial_one, Module.finrank_self]
  simp

/-- The Gaussian ideal `(1 + i)` with its standard metric (all weights `0`) has degree `-log 2`
and normalized degree `-(1/2) log 2`. -/
example :
    let e := QuadraticAlgebra.ringOfIntegersEquiv (d := -1) isUnit_neg_one.squarefree
      (by norm_num)
    ∃ (hI : ((Ideal.span {e.symm ⟨1, 1⟩} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0)
      (s : (((Ideal.span {e.symm ⟨1, 1⟩} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K)), s ≠ 0 ∧
      (HermitianMetric.fractionalIdeal _ hI 0).sectionDegree s = -Real.log 2 ∧
      (HermitianMetric.fractionalIdeal _ hI 0).sectionDegree s / Module.finrank ℚ K =
        -(1 / 2) * Real.log 2 := by
  intro e
  have hmem : (e.symm ⟨1, 1⟩ : K) ∈ (((Ideal.span {e.symm ⟨1, 1⟩} : Ideal (𝓞 K)) :
      FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.subset_span rfl, rfl⟩
  have hne : (e.symm ⟨1, 1⟩ : K) ≠ 0 := coe_ringOfIntegersEquiv_symm_one_one_ne_zero _ _
  have hI : ((Ideal.span {e.symm ⟨1, 1⟩} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]
    exact fun h ↦ hne (by rw [h, RingOfIntegers.coe_eq_algebraMap, map_zero])
  have hs : (⟨_, hmem⟩ : (((Ideal.span {e.symm ⟨1, 1⟩} : Ideal (𝓞 K)) :
      FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) ≠ 0 :=
    fun h ↦ hne (congrArg Subtype.val h)
  have hdeg : (HermitianMetric.fractionalIdeal _ hI 0).sectionDegree ⟨_, hmem⟩ = -Real.log 2 := by
    rw [HermitianMetric.sectionDegree_fractionalIdeal _ _ hs, FractionalIdeal.coeIdeal_absNorm]
    norm_num [e, Ideal.absNorm_span_singleton, QuadraticAlgebra.norm_ringOfIntegersEquiv_symm]
  refine ⟨hI, ⟨_, hmem⟩, hs, hdeg, ?_⟩
  rw [hdeg, QuadraticAlgebra.finrank_eq_two]
  ring

/-! ### Independence of the section -/

/-- In `Ō_ℚ`, the section `2` has finite term `log #(ℤ / 2) = log 2` and archimedean term
`log |2| = log 2`, so its degree is `0`, as for the section `1`. -/
example :
    Real.log (Submodule.span (𝓞 ℚ) {(2 : 𝓞 ℚ)}).cardQuot = Real.log 2 ∧
      ∑ σ : ℚ →+* ℂ, Real.log ((HermitianMetric.trivial ℚ).norm σ (1 ⊗ₜ (2 : 𝓞 ℚ))) =
        Real.log 2 := by
  constructor
  · rw [cardQuot_span_two, Module.finrank_self, pow_one]
  · simp [HermitianMetric.norm_trivial_tmul, NumberField.Embeddings.card, map_ofNat]

/-- In `ℚ(√2)`, replacing the section `1` of `Ō_K` by the unit `1 + √2` leaves the finite term
and the sum of the archimedean terms unchanged, although the norm at the embedding `√2 ↦ √2`
changes. -/
example :
    let e := QuadraticAlgebra.ringOfIntegersEquiv (d := 2) Int.prime_two.squarefree
      (by norm_num)
    Real.log (Submodule.span (𝓞 L) {e.symm ⟨1, 1⟩}).cardQuot =
        Real.log (Submodule.span (𝓞 L) {(1 : 𝓞 L)}).cardQuot ∧
      ∑ σ : L →+* ℂ, Real.log ((HermitianMetric.trivial L).norm σ (1 ⊗ₜ e.symm ⟨1, 1⟩)) =
        ∑ σ : L →+* ℂ, Real.log ((HermitianMetric.trivial L).norm σ (1 ⊗ₜ 1)) ∧
      (HermitianMetric.trivial L).norm (QuadraticAlgebra.sqrtEmbedding ((2 : ℤ) : ℚ))
          (1 ⊗ₜ e.symm ⟨1, 1⟩) ≠
        (HermitianMetric.trivial L).norm (QuadraticAlgebra.sqrtEmbedding ((2 : ℤ) : ℚ))
          (1 ⊗ₜ 1) := by
  intro e
  refine ⟨?_, ?_, ?_⟩
  · rw [← Ideal.absNorm_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton,
      Ideal.absNorm_span_singleton]
    norm_num [e, QuadraticAlgebra.norm_ringOfIntegersEquiv_symm]
  · simp only [HermitianMetric.norm_trivial_tmul]
    have hu : (e.symm ⟨1, 1⟩ : L) ≠ 0 := coe_ringOfIntegersEquiv_symm_one_one_ne_zero _ _
    rw [← Real.log_prod (fun σ _ ↦ norm_ne_zero_iff.2 ((map_ne_zero σ).2 hu)),
      ← Real.log_prod (fun σ _ ↦ by simp)]
    rw [NumberField.prod_norm_embedding_eq_abs_norm, NumberField.prod_norm_embedding_eq_abs_norm,
      ← Algebra.coe_norm_int, ← Algebra.coe_norm_int]
    norm_num [e, QuadraticAlgebra.norm_ringOfIntegersEquiv_symm]
  · rw [HermitianMetric.norm_trivial_tmul, HermitianMetric.norm_trivial_tmul, RingHom.coe_coe,
      sqrtEmbedding_ringOfIntegersEquiv_symm_one_one, RingOfIntegers.coe_eq_algebraMap (1 : 𝓞 L),
      map_one, map_one, norm_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have : 0 < √2 := by positivity
    linarith

/-- On the trivial line over `ℚ(i)`, replacing the section `1` by `2` raises the finite term by
`log 4` and the sum over the two complex embeddings by `2 log 2`, so the degree is unchanged.
Summed over the single complex place without its multiplicity `2`, the archimedean term would
only rise by `log 2`, and the degree would change. -/
example :
    Real.log (Submodule.span (𝓞 K) {(2 : 𝓞 K)}).cardQuot =
        Real.log (Submodule.span (𝓞 K) {(1 : 𝓞 K)}).cardQuot + Real.log 4 ∧
      ∑ σ : K →+* ℂ, Real.log ((HermitianMetric.trivial K).norm σ (1 ⊗ₜ 2)) =
        ∑ σ : K →+* ℂ, Real.log ((HermitianMetric.trivial K).norm σ (1 ⊗ₜ 1)) + 2 * Real.log 2 ∧
      ∑ v : InfinitePlace K, Real.log ((HermitianMetric.trivial K).placeNorm v 2) =
        Real.log 2 := by
  have h2 : ((2 : 𝓞 K) : K) = 2 := by rw [RingOfIntegers.coe_eq_algebraMap, map_ofNat]
  refine ⟨?_, ?_, ?_⟩
  · rw [cardQuot_span_two, QuadraticAlgebra.finrank_eq_two, ← Ideal.absNorm_apply,
      Ideal.absNorm_span_singleton]
    norm_num
  · simp only [HermitianMetric.norm_trivial_tmul (K := K)]
    have h1 : ((1 : 𝓞 K) : K) = 1 := by rw [RingOfIntegers.coe_eq_algebraMap, map_one]
    simp only [h1, h2, map_ofNat, map_one, norm_one, Real.log_one, Finset.sum_const_zero,
      zero_add, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
      QuadraticAlgebra.finrank_eq_two, nsmul_eq_mul, Nat.cast_ofNat, Complex.norm_ofNat]
  · simp only [HermitianMetric.placeNorm_trivial (K := K)]
    have hv (v : InfinitePlace K) : v 2 = 2 := by simpa using v.map_natCast 2
    have := QuadraticAlgebra.isTotallyComplex_iff.mpr (by norm_num : ((-1 : ℤ) : ℚ) < 0)
    have hcard : Fintype.card (InfinitePlace K) = 1 := by
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        QuadraticAlgebra.nrComplexPlaces_eq_one (by norm_num),
        IsTotallyComplex.nrRealPlaces_eq_zero]
    simp only [h2, hv, Finset.sum_const, Finset.card_univ, hcard, one_smul]

end TauCeti.ArakelovDegreeChecks
