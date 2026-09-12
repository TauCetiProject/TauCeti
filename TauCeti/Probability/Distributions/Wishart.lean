/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.HasLaw
public import TauCeti.MeasureTheory.Measure.Dirac
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix
public import TauCeti.Probability.Distributions.Gaussian.Affine

import Mathlib.MeasureTheory.Group.Convolution
import TauCeti.Analysis.Matrix.Sqrt

/-!
# The Gaussian-Gram Wishart family

The Gaussian-Gram Wishart law `TauCeti.wishartGramMeasure ν S` is the law of the Gram sum
`∑ r, X r * (X r)ᵀ` of `ν` independent centred multivariate Gaussian vectors with covariance
matrix `S`, carried by the symmetric-matrix subspace of
`TauCeti.MeasureTheory.Measure.SymmetricMatrix`.  It is defined for every natural degree `ν` and
every square matrix `S`, with no branch on `S`: Mathlib totalizes `multivariateGaussian 0 S` to
`Measure.dirac 0` when `S` is not positive semidefinite, and the Gram law inherits that
totalization.  That is what lets this family carry the legitimately singular Wishart laws, which
a density definition cannot.

## Main definitions

* `TauCeti.wishartGram` — the Gram sum of a finite family of Euclidean vectors, bundled into the
  symmetric-matrix subspace.
* `TauCeti.wishartGramMeasure` — the Gaussian-Gram Wishart law.

## Main results

* `TauCeti.isProbabilityMeasure_wishartGramMeasure` — it is a probability measure, at every
  degree and every scale matrix.
* `TauCeti.hasLaw_wishartGram_gaussian` — the Gram sum of an independent centred Gaussian
  family has this law.
* `TauCeti.wishartGramMeasure_of_not_posSemidef` — outside the positive-semidefinite cone the law
  is the Dirac mass at zero.
* `TauCeti.map_symmetricCongruenceLinearMap_wishartGramMeasure` — a rectangular congruence carries
  the law of scale `S` to the law of scale `M * S * Mᵀ`, and
  `TauCeti.wishartGramMeasure_eq_map_sqrt` specializes it to the square root of the scale.
* `TauCeti.wishartGramMeasure_conv_wishartGramMeasure` — the degrees add under convolution.
* `TauCeti.wishartGramMeasure_setOf_posSemidef` — the law is carried by the positive-semidefinite
  cone.
* `TauCeti.ae_posSemidef_wishartGramMeasure` — the sampled matrix is positive semidefinite almost
  everywhere.
* `TauCeti.wishartGramMeasure_setOf_rank_le` — the rank is at most `min ν S.rank`.
* `TauCeti.ae_rank_le_wishartGramMeasure` — the same rank bound holds almost everywhere.
* `TauCeti.mutuallySingular_wishartGramMeasure_symmetricLebesgue` — below that rank threshold the
  law has no density against `TauCeti.symmetricLebesgue`.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, chapter 3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal Matrix MatrixOrder

namespace TauCeti

variable {ι : Type*} [Fintype ι] {p ν : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}

/-! ### The Gram sum of a family of Euclidean vectors -/

/-- The matrix whose rows are a given finite family of Euclidean vectors.  The Gram sum below is
its Gram matrix, which is what makes the rank bound available. -/
private def rowMatrix (X : ι → EuclideanSpace ℝ (Fin p)) : Matrix ι (Fin p) ℝ :=
  Matrix.of fun r i => X r i

private theorem sum_vecMulVec_eq (X : ι → EuclideanSpace ℝ (Fin p)) :
    ∑ r, Matrix.vecMulVec (X r).ofLp (X r).ofLp = (rowMatrix X)ᵀ * rowMatrix X := by
  ext i j
  simp [rowMatrix, Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]

private theorem posSemidef_sum_vecMulVec (X : ι → EuclideanSpace ℝ (Fin p)) :
    (∑ r, Matrix.vecMulVec (X r).ofLp (X r).ofLp).PosSemidef := by
  refine Matrix.posSemidef_sum Finset.univ fun r _ => ?_
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (X r).ofLp

/-- The **Gram sum** `∑ r, X r * (X r)ᵀ` of a finite family of Euclidean vectors, as an element of
the symmetric-matrix subspace.  This is the statistic whose law is the Gaussian-Gram Wishart
family. -/
def wishartGram (X : ι → EuclideanSpace ℝ (Fin p)) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) :=
  ⟨∑ r, Matrix.vecMulVec (X r).ofLp (X r).ofLp,
    Matrix.isHermitian_iff_isSelfAdjoint.1 (posSemidef_sum_vecMulVec X).isHermitian⟩

@[simp]
theorem coe_wishartGram (X : ι → EuclideanSpace ℝ (Fin p)) :
    (wishartGram X : Matrix (Fin p) (Fin p) ℝ) =
      ∑ r, Matrix.vecMulVec (X r).ofLp (X r).ofLp :=
  (rfl)

/-- The Gram sum of a family of Euclidean vectors is positive semidefinite. -/
theorem posSemidef_coe_wishartGram (X : ι → EuclideanSpace ℝ (Fin p)) :
    (wishartGram X : Matrix (Fin p) (Fin p) ℝ).PosSemidef :=
  posSemidef_sum_vecMulVec X

/-- The Gram sum of a family of vectors has rank at most the size of the family. -/
theorem rank_coe_wishartGram_le (X : ι → EuclideanSpace ℝ (Fin p)) :
    (wishartGram X : Matrix (Fin p) (Fin p) ℝ).rank ≤ Fintype.card ι := by
  rw [coe_wishartGram, sum_vecMulVec_eq, Matrix.rank_transpose_mul_self]
  exact (rowMatrix X).rank_le_card_height

/-- A linear image of the vectors congruates their Gram sum. -/
theorem wishartGram_toEuclideanLin {q : ℕ} (M : Matrix (Fin q) (Fin p) ℝ)
    (X : ι → EuclideanSpace ℝ (Fin p)) :
    wishartGram (fun r => Matrix.toEuclideanLin M (X r)) =
      Matrix.symmetricCongruenceLinearMap M (wishartGram X) := by
  refine Subtype.ext ?_
  rw [Matrix.coe_symmetricCongruenceLinearMap_apply, coe_wishartGram, coe_wishartGram]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]

/-- The Gram sum is continuous in the family of vectors. -/
theorem continuous_wishartGram : Continuous (wishartGram (p := p) (ι := ι)) := by
  refine Continuous.subtype_mk (continuous_finsetSum _ fun r _ => ?_) _
  refine continuous_matrix fun i j => ?_
  simp only [Matrix.vecMulVec_apply]
  refine Continuous.mul ?_ ?_ <;>
    exact (PiLp.continuous_apply 2 _ _).comp (continuous_apply r)

/-- The Gram sum is measurable in the family of vectors. -/
@[fun_prop]
theorem measurable_wishartGram : Measurable (wishartGram (p := p) (ι := ι)) :=
  continuous_wishartGram.measurable

/-! ### The Gaussian-Gram Wishart law -/

/-- The **Gaussian-Gram Wishart law** of degree `ν` and scale `S`: the law of the Gram sum of `ν`
independent centred multivariate Gaussian vectors with covariance `S`.  When `S` is not positive
semidefinite Mathlib's `multivariateGaussian 0 S` is `Measure.dirac 0`, and this law is then
`Measure.dirac 0` too. -/
def wishartGramMeasure (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  (Measure.pi fun _ : Fin ν => multivariateGaussian 0 S).map wishartGram

/-- The defining pushforward representation, so that importing modules need not unfold the
definition. -/
theorem wishartGramMeasure_eq_map_pi (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ) :
    wishartGramMeasure ν S =
      (Measure.pi fun _ : Fin ν => multivariateGaussian 0 S).map wishartGram :=
  (rfl)

instance isProbabilityMeasure_wishartGramMeasure (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ) :
    IsProbabilityMeasure (wishartGramMeasure ν S) := by
  rw [wishartGramMeasure_eq_map_pi]
  exact (Measure.isProbabilityMeasure_map_iff measurable_wishartGram.aemeasurable).2 inferInstance

/-- At degree zero the Gaussian-Gram law is the Dirac mass at the zero matrix. -/
@[simp]
theorem wishartGramMeasure_zero (S : Matrix (Fin p) (Fin p) ℝ) :
    wishartGramMeasure 0 S = Measure.dirac 0 := by
  rw [wishartGramMeasure_eq_map_pi]
  have h : (wishartGram (p := p) (ι := Fin 0)) = fun _ => 0 :=
    funext fun _ => Subtype.ext (by simp)
  rw [h, Measure.map_const]
  simp

/-- With a scale matrix outside the positive-semidefinite cone, Mathlib totalizes the Gaussian
factor to a Dirac mass, and the Gaussian-Gram law is then the Dirac mass at the zero matrix. -/
@[simp]
theorem wishartGramMeasure_of_not_posSemidef (ν : ℕ) (hS : ¬ S.PosSemidef) :
    wishartGramMeasure ν S = Measure.dirac 0 := by
  rw [wishartGramMeasure_eq_map_pi]
  simp only [multivariateGaussian_of_not_posSemidef 0 hS]
  rw [Measure.pi_dirac fun _ : Fin ν => (0 : EuclideanSpace ℝ (Fin p)),
    Measure.map_dirac' measurable_wishartGram]
  exact congrArg _ (Subtype.ext (by simp))

/-- **The Gram sum of an independent centred Gaussian family is Gaussian-Gram Wishart.** -/
theorem hasLaw_wishartGram_gaussian {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Fin ν → Ω → EuclideanSpace ℝ (Fin p)}
    (hX : ∀ r, HasLaw (X r) (multivariateGaussian 0 S) P) (hindep : iIndepFun X P) :
    HasLaw (fun ω => wishartGram fun r => X r ω) (wishartGramMeasure ν S) P :=
  (hasLaw_map measurable_wishartGram.aemeasurable).comp (hindep.hasLaw_pi hX)

/-! ### Congruence -/

/-- **Congruence by a rectangular matrix carries the Gaussian-Gram law of scale `S` to the one of
scale `M * S * Mᵀ`.**  No rank hypothesis on `M` is needed. -/
theorem map_symmetricCongruenceLinearMap_wishartGramMeasure {q : ℕ} (ν : ℕ)
    (M : Matrix (Fin q) (Fin p) ℝ) (hS : S.PosSemidef) :
    (wishartGramMeasure ν S).map (Matrix.symmetricCongruenceLinearMap M) =
      wishartGramMeasure ν (M * S * Mᵀ) := by
  have hmap : (multivariateGaussian 0 S).map (Matrix.toEuclideanLin M) =
      multivariateGaussian 0 (M * S * Mᵀ) := by
    have h := map_affine_multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) hS M 0
    have hfun : (fun x : EuclideanSpace ℝ (Fin p) =>
        Matrix.toEuclideanLin M x + (0 : EuclideanSpace ℝ (Fin q))) =
        ⇑(Matrix.toEuclideanLin M) := funext fun x => by rw [add_zero]
    rw [hfun] at h
    simpa using h
  have hcong : Continuous (Matrix.symmetricCongruenceLinearMap M) :=
    LinearMap.continuous_of_finiteDimensional _
  have : ∀ _ : Fin ν, SigmaFinite
      ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S).map
        (Matrix.toEuclideanLin M)) := fun _ => by rw [hmap]; infer_instance
  rw [wishartGramMeasure_eq_map_pi, wishartGramMeasure_eq_map_pi,
    Measure.map_map hcong.measurable measurable_wishartGram]
  have hfun : (Matrix.symmetricCongruenceLinearMap M) ∘ (wishartGram (p := p) (ι := Fin ν)) =
      wishartGram ∘ fun X r => Matrix.toEuclideanLin M (X r) :=
    funext fun X => (wishartGram_toEuclideanLin M X).symm
  rw [hfun, ← Measure.map_map measurable_wishartGram (by fun_prop),
    Measure.pi_map_pi fun _ => (by fun_prop : Measurable _).aemeasurable, hmap]

/-- The Gaussian-Gram law of a positive-semidefinite scale `S` is the standard Gaussian-Gram law
pushed forward by the congruence with `CFC.sqrt S`. -/
theorem wishartGramMeasure_eq_map_sqrt (ν : ℕ) (hS : S.PosSemidef) :
    wishartGramMeasure ν S =
      (wishartGramMeasure ν 1).map (Matrix.symmetricCongruenceLinearMap (CFC.sqrt S)) := by
  rw [map_symmetricCongruenceLinearMap_wishartGramMeasure ν _ Matrix.PosSemidef.one]
  refine congrArg _ ?_
  rw [Matrix.mul_one, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg S)).isHermitian.eq,
    CFC.sqrt_mul_sqrt_self S hS.nonneg]

/-! ### Support, rank and singularity -/

/-- **The Gaussian-Gram law is carried by the positive-semidefinite cone.** -/
theorem wishartGramMeasure_setOf_posSemidef (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ) :
    wishartGramMeasure ν S
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef} = 1 := by
  refine le_antisymm prob_le_one ?_
  rw [wishartGramMeasure_eq_map_pi]
  calc (1 : ℝ≥0∞)
      = (Measure.pi fun _ : Fin ν => multivariateGaussian 0 S) Set.univ := (measure_univ).symm
    _ = (Measure.pi fun _ : Fin ν => multivariateGaussian 0 S)
          (wishartGram ⁻¹' {A | (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef}) := by
        exact congrArg _ (Set.eq_univ_of_forall fun X => posSemidef_coe_wishartGram X).symm
    _ ≤ _ := Measure.le_map_apply measurable_wishartGram.aemeasurable _

/-- A Gaussian-Gram Wishart matrix is positive semidefinite almost everywhere. -/
theorem ae_posSemidef_wishartGramMeasure (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ) :
    ∀ᵐ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ∂wishartGramMeasure ν S,
      (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef := by
  refine (ae_iff_prob_eq_one ?_).2 (wishartGramMeasure_setOf_posSemidef ν S)
  apply measurableSet_setOfPred.mp
  exact (Matrix.posSemidef_is_closed (n := Fin p) (𝕜 := ℝ)).measurableSet.preimage
    continuous_subtype_val.measurable

/-- Every value of the congruated Gram sum has rank at most `min ν S.rank`: the Gram sum of `ν`
vectors caps the rank at `ν`, and congruating by the square root of `S` caps it at `S.rank`. -/
private theorem rank_coe_symmetricCongruence_wishartGram_le (hS : S.PosSemidef)
    (X : Fin ν → EuclideanSpace ℝ (Fin p)) :
    ((Matrix.symmetricCongruenceLinearMap (CFC.sqrt S) (wishartGram X) :
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ).rank ≤ min ν S.rank := by
  rw [Matrix.coe_symmetricCongruenceLinearMap_apply]
  have hstep := Matrix.rank_mul_le_left (CFC.sqrt S * (wishartGram X : Matrix (Fin p) (Fin p) ℝ))
    (CFC.sqrt S)ᵀ
  refine le_min (hstep.trans ((Matrix.rank_mul_le_right _ _).trans ?_))
    (hstep.trans ((Matrix.rank_mul_le_left _ _).trans ?_))
  · simpa using rank_coe_wishartGram_le X
  · exact hS.rank_sqrt.le

/-- **The Gaussian-Gram law of degree `ν` has rank at most `min ν S.rank`.**  With fewer Gaussian
samples than dimensions, or a singular scale matrix, the law lives on singular matrices. -/
theorem wishartGramMeasure_setOf_rank_le (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ) :
    wishartGramMeasure ν S
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).rank ≤ min ν S.rank} = 1 := by
  by_cases hS : S.PosSemidef
  · refine le_antisymm prob_le_one ?_
    rw [wishartGramMeasure_eq_map_sqrt ν hS, wishartGramMeasure_eq_map_pi,
      Measure.map_map (LinearMap.continuous_of_finiteDimensional _).measurable
        measurable_wishartGram]
    calc (1 : ℝ≥0∞)
        = (Measure.pi fun _ : Fin ν => multivariateGaussian 0 1) Set.univ := (measure_univ).symm
      _ = (Measure.pi fun _ : Fin ν => multivariateGaussian 0 1)
            ((⇑(Matrix.symmetricCongruenceLinearMap (CFC.sqrt S)) ∘ wishartGram) ⁻¹'
              {A | (A : Matrix (Fin p) (Fin p) ℝ).rank ≤ min ν S.rank}) :=
          congrArg _ (Set.eq_univ_of_forall fun X =>
            rank_coe_symmetricCongruence_wishartGram_le hS X).symm
      _ ≤ _ := Measure.le_map_apply
            (((LinearMap.continuous_of_finiteDimensional _).measurable.comp
              measurable_wishartGram).aemeasurable) _
  · rw [wishartGramMeasure_of_not_posSemidef ν hS]
    refine Measure.dirac_apply_of_mem ?_
    simp

/-- A Gaussian-Gram Wishart matrix has rank at most `min ν S.rank` almost everywhere. -/
theorem ae_rank_le_wishartGramMeasure (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ) :
    ∀ᵐ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ∂wishartGramMeasure ν S,
      (A : Matrix (Fin p) (Fin p) ℝ).rank ≤ min ν S.rank := by
  refine (ae_iff_prob_eq_one ?_).2 (wishartGramMeasure_setOf_rank_le ν S)
  exact measurableSet_setOfPred.mp (measurableSet_setOfPred_rank_le (min ν S.rank))

/-- **Below the rank threshold the Gaussian-Gram law has no density.**  It is then carried by the
singular symmetric matrices, which are `TauCeti.symmetricLebesgue`-null. -/
theorem mutuallySingular_wishartGramMeasure_symmetricLebesgue (ν : ℕ)
    (S : Matrix (Fin p) (Fin p) ℝ) (hrank : min ν S.rank < p) :
    (wishartGramMeasure ν S).MutuallySingular (symmetricLebesgue p) := by
  refine ⟨{A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).det = 0}ᶜ, (measurableSet_setOfPred_det_eq_zero p).compl,
    ?_, ?_⟩
  · refine measure_mono_null (fun A hA => ?_) (ae_iff.1 (ae_rank_le_wishartGramMeasure ν S))
    have hdet : (A : Matrix (Fin p) (Fin p) ℝ).det ≠ 0 := hA
    have hrk : (A : Matrix (Fin p) (Fin p) ℝ).rank = p := by
      rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)),
        Fintype.card_fin]
    exact fun hle => absurd (hrk.symm.trans_le hle) (not_le.2 hrank)
  · rw [compl_compl, symmetricLebesgue_setOf_det_eq_zero]

/-! ### Convolution -/

/-- Splitting a family indexed by a sum type splits its Gram sum. -/
private theorem wishartGram_piCongrLeft {ν₁ ν₂ : ℕ}
    (Z : Fin ν₁ ⊕ Fin ν₂ → EuclideanSpace ℝ (Fin p)) :
    wishartGram (Equiv.piCongrLeft (fun _ : Fin (ν₁ + ν₂) => EuclideanSpace ℝ (Fin p))
        finSumFinEquiv Z) =
      wishartGram (fun r => Z (Sum.inl r)) + wishartGram (fun r => Z (Sum.inr r)) := by
  refine Subtype.ext ?_
  have hsplit : ∑ i : Fin ν₁ ⊕ Fin ν₂, Matrix.vecMulVec (Z i).ofLp (Z i).ofLp =
      (∑ r : Fin ν₁, Matrix.vecMulVec (Z (Sum.inl r)).ofLp (Z (Sum.inl r)).ofLp) +
        ∑ r : Fin ν₂, Matrix.vecMulVec (Z (Sum.inr r)).ofLp (Z (Sum.inr r)).ofLp :=
    Fintype.sum_sum_type _
  rw [Submodule.coe_add, coe_wishartGram, coe_wishartGram, coe_wishartGram, ← hsplit]
  refine (Fintype.sum_equiv finSumFinEquiv _ _ fun i => ?_).symm
  rw [Equiv.piCongrLeft_apply_apply]

/-- **The degrees of the Gaussian-Gram family add under convolution.** -/
theorem wishartGramMeasure_conv_wishartGramMeasure (ν₁ ν₂ : ℕ)
    (S : Matrix (Fin p) (Fin p) ℝ) :
    wishartGramMeasure ν₁ S ∗ wishartGramMeasure ν₂ S = wishartGramMeasure (ν₁ + ν₂) S := by
  have hsum := (measurePreserving_sumPiEquivProdPi
    fun _ : Fin ν₁ ⊕ Fin ν₂ => multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S).map_eq
  have hcongr := (measurePreserving_piCongrLeft
    (fun _ : Fin (ν₁ + ν₂) => multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S)
    finSumFinEquiv).map_eq
  rw [Measure.conv, wishartGramMeasure_eq_map_pi, wishartGramMeasure_eq_map_pi,
    Measure.map_prod_map _ _ measurable_wishartGram measurable_wishartGram, ← hsum,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop),
    wishartGramMeasure_eq_map_pi, ← hcongr, Measure.map_map measurable_wishartGram (by fun_prop)]
  congr 1
  funext Z
  rw [MeasurableEquiv.coe_piCongrLeft, Function.comp_apply, Function.comp_apply,
    Function.comp_apply, wishartGram_piCongrLeft]
  rfl

end TauCeti
