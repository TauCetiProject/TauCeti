/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate

import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Topology.Instances.RealVectorSpace
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.Probability.Distributions.Gaussian.TailMoment

/-!
# Second moments of finite Gaussian sums

The Gaussian second moment of a finite family in a real normed space is the square root
of the expected squared norm of its sum with independent standard Gaussian coefficients.
The coefficient space is the native Euclidean space with its standard Gaussian measure.
In particular the definition works for empty families and does not require completeness
of the target space.

We record the basic properties of `gaussianSecondMoment` paralleling
`TauCeti.rademacherSecondMoment`: nonnegativity, separation (`norm_le_gaussianSecondMoment` and
`gaussianSecondMoment_eq_zero_iff`), subadditivity (`gaussianSecondMoment_add_le`), homogeneity over
any normed field with commuting scalar action, invariance under reindexing, comparison along bounded
additive maps, the exact value on multiples of a single vector, and its equality with the `ℓ²` norm
in an inner product space.

## Main declarations

* `TauCeti.gaussianSecondMoment`: the Gaussian second moment `G₂(x)`.
* `TauCeti.norm_le_gaussianSecondMoment` and `TauCeti.gaussianSecondMoment_eq_zero_iff`: coordinate
  lower bound and separation of families.
* `TauCeti.gaussianSecondMoment_add_le`: subadditivity `G₂(x + y) ≤ G₂(x) + G₂(y)`.
* `TauCeti.gaussianSecondMoment_smul`: homogeneity `G₂(c • x) = ‖c‖ * G₂(x)`.
* `TauCeti.gaussianSecondMoment_comp_equiv`: invariance under reindexing.
* `TauCeti.gaussianSecondMoment_map_le` and `TauCeti.gaussianSecondMoment_le_mul_map`: comparison
  along bounded additive or real-linear maps.
* `TauCeti.gaussianSecondMoment_smul_const` and `TauCeti.gaussianSecondMoment_const`: families of
  multiples of a single vector.
* `TauCeti.gaussianSecondMoment_eq_norm_toLp_two`: in an inner product space, `G₂(y) = ‖y‖₂`.

## References

* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*,
  §3, pp. 33–37.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

variable {ι κ Y : Type*} [Fintype ι] [Fintype κ] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A finite Gaussian sum has every finite moment, even in an incomplete target. -/
theorem memLp_gaussianSum (x : ι → Y) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun g : EuclideanSpace ℝ ι ↦ ∑ i, g i • x i) p
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  let T : EuclideanSpace ℝ ι →L[ℝ] Y :=
    ∑ i, (EuclideanSpace.proj i).smulRight (x i)
  simpa only [T, Function.comp_def, id_eq, sum_apply,
    ContinuousLinearMap.smulRight_apply, EuclideanSpace.coe_proj] using
    T.comp_memLp' (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ ι)) p hp)

/-- The squared norm of a finite Gaussian sum is integrable. -/
theorem integrable_norm_sq_gaussianSum (x : ι → Y) :
    Integrable (fun g : EuclideanSpace ℝ ι ↦ ‖∑ i, g i • x i‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ ι)) :=
  (memLp_gaussianSum x 2 (by simp)).integrable_norm_pow (by norm_num)

/-- The Gaussian second moment of a finite family, with independent real standard Gaussian
coefficients. -/
def gaussianSecondMoment (x : ι → Y) : ℝ :=
  √(∫ g : EuclideanSpace ℝ ι, ‖∑ i, g i • x i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι))

/-- The defining integral of the Gaussian second moment. -/
theorem gaussianSecondMoment_def (x : ι → Y) :
    gaussianSecondMoment x =
      √(∫ g : EuclideanSpace ℝ ι, ‖∑ i, g i • x i‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι)) :=
  (rfl)

/-- Gaussian second moments are nonnegative. -/
theorem gaussianSecondMoment_nonneg (x : ι → Y) : 0 ≤ gaussianSecondMoment x :=
  Real.sqrt_nonneg _

/-- Squaring the Gaussian second moment recovers the expected squared norm. -/
theorem gaussianSecondMoment_sq (x : ι → Y) :
    gaussianSecondMoment x ^ 2 =
      ∫ g : EuclideanSpace ℝ ι, ‖∑ i, g i • x i‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι) :=
  Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _)

/-- A bound on the expected squared norm of the Gaussian sum bounds the Gaussian second moment. -/
theorem gaussianSecondMoment_le_of_sq_le {x : ι → Y} {c : ℝ} (hc : 0 ≤ c)
    (h : ∫ g : EuclideanSpace ℝ ι, ‖∑ i, g i • x i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) ≤
      c ^ 2) :
    gaussianSecondMoment x ≤ c :=
  Real.sqrt_le_iff.2 ⟨hc, h⟩

/-- Multiplying a family by a scalar in a normed field whose action commutes with `ℝ` multiplies
its Gaussian second moment by the norm of that scalar. -/
theorem gaussianSecondMoment_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 Y]
    [SMulCommClass ℝ 𝕜 Y] (x : ι → Y) (c : 𝕜) :
    gaussianSecondMoment (fun i ↦ c • x i) = ‖c‖ * gaussianSecondMoment x := by
  have hs (g : EuclideanSpace ℝ ι) :
      (∑ i, g i • (c • x i)) = c • ∑ i, g i • x i := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _
  apply (sq_eq_sq₀ (gaussianSecondMoment_nonneg _)
    (mul_nonneg (norm_nonneg _) (gaussianSecondMoment_nonneg _))).1
  rw [mul_pow, gaussianSecondMoment_sq, gaussianSecondMoment_sq]
  simp_rw [hs, norm_smul, mul_pow]
  rw [integral_const_mul]

/-- The Gaussian second moment is subadditive: `G₂(x + y) ≤ G₂(x) + G₂(y)`. -/
theorem gaussianSecondMoment_add_le (x y : ι → Y) :
    gaussianSecondMoment (x + y) ≤ gaussianSecondMoment x + gaussianSecondMoment y := by
  have hx := memLp_gaussianSum x 2 (by simp)
  have hy := memLp_gaussianSum y 2 (by simp)
  have hxy_mem := memLp_gaussianSum (x + y) 2 (by simp)
  have hxy : (fun g : EuclideanSpace ℝ ι ↦ ∑ i, g i • (x + y) i) =
      (fun g ↦ ∑ i, g i • x i) + (fun g ↦ ∑ i, g i • y i) := by
    ext g
    simp [smul_add, Finset.sum_add_distrib]
  have hle : eLpNorm (fun g : EuclideanSpace ℝ ι ↦ ∑ i, g i • (x + y) i) 2
        (stdGaussian (EuclideanSpace ℝ ι)) ≤
      eLpNorm (fun g : EuclideanSpace ℝ ι ↦ ∑ i, g i • x i) 2
        (stdGaussian (EuclideanSpace ℝ ι)) +
      eLpNorm (fun g : EuclideanSpace ℝ ι ↦ ∑ i, g i • y i) 2
        (stdGaussian (EuclideanSpace ℝ ι)) := by
    rw [hxy]
    exact eLpNorm_add_le one_le_two
  rw [hxy_mem.eLpNorm_two_eq_ofReal_sqrt_integral, hx.eLpNorm_two_eq_ofReal_sqrt_integral,
    hy.eLpNorm_two_eq_ofReal_sqrt_integral,
    ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at hle
  exact hle

/-- Reindexing a family along an equivalence preserves its Gaussian second moment. -/
theorem gaussianSecondMoment_comp_equiv (e : κ ≃ ι) (x : ι → Y) :
    gaussianSecondMoment (x ∘ e) = gaussianSecondMoment x := by
  let f : EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  let e' : EuclideanSpace ℝ κ ≃ᵐ EuclideanSpace ℝ ι := f.toHomeomorph.toMeasurableEquiv
  have hmap : (stdGaussian (EuclideanSpace ℝ κ)).map e' = stdGaussian (EuclideanSpace ℝ ι) :=
    stdGaussian_map f
  have hsum (g : EuclideanSpace ℝ κ) :
      ∑ i : ι, (e' g) i • x i = ∑ j : κ, g j • (x ∘ e) j := by
    refine Fintype.sum_equiv e.symm _ _ fun i ↦ ?_
    simp [e', f]
  rw [gaussianSecondMoment_def, gaussianSecondMoment_def]
  congr 1
  have hm := integral_map_equiv (μ := stdGaussian (EuclideanSpace ℝ κ))
    e' (fun h : EuclideanSpace ℝ ι ↦ ‖∑ i, h i • x i‖ ^ 2)
  rw [hmap] at hm
  simp_rw [← hsum]
  exact hm.symm

/-- Pointwise domination of Gaussian sums implies domination of Gaussian second moments. -/
theorem gaussianSecondMoment_le_mul {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {x : ι → Y} {z : ι → Z} {K : ℝ}
    (h : ∀ g : EuclideanSpace ℝ ι, ‖∑ i, g i • x i‖ ≤ K * ‖∑ i, g i • z i‖) :
    gaussianSecondMoment x ≤ K * gaussianSecondMoment z := by
  by_cases hzero : ∀ g : EuclideanSpace ℝ ι, ‖∑ i, g i • z i‖ = 0
  · have hx0 (g : EuclideanSpace ℝ ι) : ‖∑ i, g i • x i‖ = 0 :=
      le_antisymm ((h g).trans (by simp [hzero g])) (norm_nonneg _)
    simp [gaussianSecondMoment_def, hzero, hx0]
  · push Not at hzero
    obtain ⟨g₀, hg₀⟩ := hzero
    have hK : 0 ≤ K := by
      have hpos : 0 < ‖∑ i, g₀ i • z i‖ := (norm_nonneg _).lt_of_ne' hg₀
      nlinarith [h g₀, norm_nonneg (∑ i, g₀ i • x i)]
    refine gaussianSecondMoment_le_of_sq_le (mul_nonneg hK (gaussianSecondMoment_nonneg z)) ?_
    rw [mul_pow, gaussianSecondMoment_sq, ← integral_const_mul]
    refine integral_mono (integrable_norm_sq_gaussianSum x)
      ((integrable_norm_sq_gaussianSum z).const_mul (K ^ 2)) fun g ↦ ?_
    have hsq := sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _)) |>.2 (h g)
    simpa [mul_pow] using hsq

/-- An additive map with `‖f x‖ ≤ M * ‖x‖` is automatically continuous and `ℝ`-linear, and hence
multiplies Gaussian second moments by at most `M`. -/
theorem gaussianSecondMoment_map_le {Z 𝓕 : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FunLike 𝓕 Y Z] [AddMonoidHomClass 𝓕 Y Z] (f : 𝓕) {M : ℝ} (hM : ∀ y, ‖f y‖ ≤ M * ‖y‖)
    (x : ι → Y) :
    gaussianSecondMoment (fun i ↦ f (x i)) ≤ M * gaussianSecondMoment x := by
  have hcont : Continuous f := by
    refine (LipschitzWith.of_dist_le_mul (K := ⟨max M 0, le_max_right M 0⟩) fun u v ↦ ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact (hM (u - v)).trans (mul_le_mul_of_nonneg_right (le_max_left M 0) (norm_nonneg _))
  refine gaussianSecondMoment_le_mul fun g ↦ ?_
  have hlin : f (∑ i, g i • x i) = ∑ i, g i • f (x i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ map_real_smul f hcont (g i) (x i)
  simpa only [hlin] using hM (∑ i, g i • x i)

/-- A real-linear map with `‖x‖ ≤ K * ‖f x‖` divides Gaussian second moments by at most `K`. -/
theorem gaussianSecondMoment_le_mul_map {Z 𝓕 : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FunLike 𝓕 Y Z] [LinearMapClass 𝓕 ℝ Y Z] (f : 𝓕) {K : ℝ} (hK : ∀ y, ‖y‖ ≤ K * ‖f y‖)
    (x : ι → Y) :
    gaussianSecondMoment x ≤ K * gaussianSecondMoment (fun i ↦ f (x i)) := by
  refine gaussianSecondMoment_le_mul fun g ↦ ?_
  simpa only [map_sum, map_smul] using hK (∑ i, g i • x i)

/-- The Gaussian second moment of scalar multiples of a single vector is the `ℓ²` norm of the
scalars times the norm of the vector. -/
theorem gaussianSecondMoment_smul_const (a : ι → ℝ) (y : Y) :
    gaussianSecondMoment (fun i ↦ a i • y) = ‖WithLp.toLp 2 a‖ * ‖y‖ := by
  have hsum (g : EuclideanSpace ℝ ι) :
      ‖∑ i, g i • (a i • y)‖ ^ 2 = (∑ i, a i * g i) ^ 2 * ‖y‖ ^ 2 := by
    have hvec : ∑ i, g i • (a i • y) = (∑ i, a i * g i) • y := by
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [smul_smul, mul_comm]
    rw [hvec, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hint_id : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) := by
    simpa [Real.norm_eq_abs, sq_abs] using
      (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)).integrable_norm_pow (by norm_num)
  have hsq : ∫ g : EuclideanSpace ℝ ι, (∑ i, a i * g i) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ ι) = ∑ i, a i ^ 2 := by
    have h := Probability.integral_sum_mul_odd_sq_stdGaussian (φ := id) (fun _ ↦ rfl) measurable_id
      hint_id a
    simpa [Probability.integral_sq_gaussianReal] using h
  rw [gaussianSecondMoment_def]
  simp_rw [hsum]
  rw [integral_mul_const, hsq, Real.sqrt_mul (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
    Real.sqrt_sq (norm_nonneg y), PiLp.norm_eq_of_L2]
  simp [Real.norm_eq_abs, sq_abs]

/-- `card ι` copies of a vector `y` have Gaussian second moment `√(card ι) * ‖y‖`. -/
theorem gaussianSecondMoment_const (y : Y) :
    gaussianSecondMoment (fun _ : ι ↦ y) = √(Fintype.card ι) * ‖y‖ := by
  have h := gaussianSecondMoment_smul_const (fun _ : ι ↦ (1 : ℝ)) y
  simp only [one_smul] at h
  rw [h, PiLp.norm_eq_of_L2]
  simp

section InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]

variable (𝕜) in
include 𝕜 in
/-- In an inner product space, the expected squared norm of a finite Gaussian sum is the sum of
the squared norms of its members. -/
theorem integral_norm_sq_gaussianSum_eq_sum (y : ι → H) :
    ∫ g : EuclideanSpace ℝ ι, ‖∑ i, g i • y i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) =
      ∑ i, ‖y i‖ ^ 2 := by
  classical
  have hexp (g : EuclideanSpace ℝ ι) : ‖∑ i, g i • y i‖ ^ 2 =
      ∑ i, ∑ j, (g i * g j) * RCLike.re (inner 𝕜 (y i) (y j)) := by
    rw [norm_sq_eq_re_inner (𝕜 := 𝕜), sum_inner, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [inner_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hsmul (r : ℝ) (v : H) : r • v = (r : 𝕜) • v := (algebraMap_smul 𝕜 r v).symm
    simp only [hsmul, inner_smul_left, inner_smul_right, RCLike.conj_ofReal]
    rw [← mul_assoc, mul_comm ((g j : ℝ) : 𝕜), ← RCLike.ofReal_mul, RCLike.re_ofReal_mul]
  have hint_id : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) := by
    simpa [Real.norm_eq_abs, sq_abs] using
      (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)).integrable_norm_pow (by norm_num)
  have hint_prod (i j : ι) : Integrable (fun g : EuclideanSpace ℝ ι ↦ g i * g j)
      (stdGaussian (EuclideanSpace ℝ ι)) :=
    Probability.integrable_comp_eval_mul_stdGaussian (φ := id) measurable_id hint_id i j
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    (hint_prod i j).mul_const _]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ (hint_prod i j).mul_const _]
  have hterm (j : ι) :
      ∫ g : EuclideanSpace ℝ ι, (g i * g j) * RCLike.re (inner 𝕜 (y i) (y j))
          ∂stdGaussian (EuclideanSpace ℝ ι) =
        if j = i then ‖y i‖ ^ 2 else 0 := by
    rw [integral_mul_const]
    split_ifs with hji
    · subst j
      have hsq (g : EuclideanSpace ℝ ι) : g i * g i = g i ^ 2 := (sq _).symm
      simp_rw [hsq]
      rw [Probability.integral_eval_sq_stdGaussian i, one_mul, norm_sq_eq_re_inner (𝕜 := 𝕜)]
    · rw [Probability.integral_comp_eval_mul_eq_zero_of_odd (φ := fun x ↦ x) (fun _ ↦ rfl)
        (Ne.symm hji), zero_mul]
  simp_rw [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

variable (𝕜) in
include 𝕜 in
/-- In an inner product space, the Gaussian second moment of a finite family is its `ℓ²` norm. -/
theorem gaussianSecondMoment_eq_norm_toLp_two (y : ι → H) :
    gaussianSecondMoment y = ‖WithLp.toLp 2 y‖ := by
  rw [gaussianSecondMoment_def, integral_norm_sq_gaussianSum_eq_sum 𝕜, PiLp.norm_eq_of_L2]

end InnerProductSpace

@[simp]
theorem gaussianSecondMoment_zero : gaussianSecondMoment (0 : ι → Y) = 0 := by
  simp [gaussianSecondMoment]

/-- An empty Gaussian sum has second moment zero. -/
@[simp]
theorem gaussianSecondMoment_of_isEmpty [IsEmpty ι] (x : ι → Y) :
    gaussianSecondMoment x = 0 := by
  simp [gaussianSecondMoment]

/-- Each vector in a finite family has norm at most the family's Gaussian second moment. -/
theorem norm_le_gaussianSecondMoment (x : ι → Y) (i : ι) :
    ‖x i‖ ≤ gaussianSecondMoment x := by
  classical
  let ε : ι → ℤˣ := Pi.mulSingle i (-1)
  have hdiff (g : EuclideanSpace ℝ ι) :
      (∑ j, g j • x j) - (∑ j, (Probability.signFlipEquiv ε g) j • x j) =
        (2 : ℝ) • (g i • x i) := by
    rw [← Finset.sum_sub_distrib, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hrest : ∑ j ∈ Finset.univ.erase i,
        (g j • x j - (Probability.signFlipEquiv ε g) j • x j) = 0 :=
      Finset.sum_eq_zero fun j hj ↦ by simp [ε, Finset.ne_of_mem_erase hj]
    rw [hrest, add_zero, show (2 : ℝ) • (g i • x i) = g i • x i + g i • x i by rw [two_smul]]
    simp [ε, sub_neg_eq_add]
  have hpt (g : EuclideanSpace ℝ ι) :
      g i ^ 2 * ‖x i‖ ^ 2 ≤
        (‖∑ j, g j • x j‖ ^ 2 + ‖∑ j, (Probability.signFlipEquiv ε g) j • x j‖ ^ 2) / 2 := by
    have htr : 2 * (|g i| * ‖x i‖) ≤
        ‖∑ j, g j • x j‖ + ‖∑ j, (Probability.signFlipEquiv ε g) j • x j‖ := by
      calc 2 * (|g i| * ‖x i‖) = ‖(2 : ℝ) • (g i • x i)‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]; norm_num
        _ = ‖(∑ j, g j • x j) - (∑ j, (Probability.signFlipEquiv ε g) j • x j)‖ := by
            rw [hdiff g]
        _ ≤ _ := norm_sub_le _ _
    have hsq := sq_le_sq₀ (by positivity) (by positivity) |>.2 htr
    nlinarith [sq_nonneg (‖∑ j, g j • x j‖ - ‖∑ j, (Probability.signFlipEquiv ε g) j • x j‖),
      sq_abs (g i)]
  have hint_flip : Integrable
      (fun g : EuclideanSpace ℝ ι ↦ ‖∑ j, (Probability.signFlipEquiv ε g) j • x j‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
    have hsum_eq (g : EuclideanSpace ℝ ι) :
        ∑ j, (Probability.signFlipEquiv ε g) j • x j = ∑ j, g j • (ε j • x j) := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rcases Int.units_eq_one_or (ε j) with h | h <;> simp [h]
    simpa only [hsum_eq] using integrable_norm_sq_gaussianSum (fun j ↦ ε j • x j)
  apply (sq_le_sq₀ (norm_nonneg _) (gaussianSecondMoment_nonneg _)).1
  calc ‖x i‖ ^ 2 = ∫ g : EuclideanSpace ℝ ι, g i ^ 2 * ‖x i‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι) := by
        rw [integral_mul_const, Probability.integral_eval_sq_stdGaussian i, one_mul]
    _ ≤ ∫ g : EuclideanSpace ℝ ι,
          (‖∑ j, g j • x j‖ ^ 2 + ‖∑ j, (Probability.signFlipEquiv ε g) j • x j‖ ^ 2) / 2
          ∂stdGaussian (EuclideanSpace ℝ ι) :=
        integral_mono ((Probability.integrable_eval_sq_stdGaussian i).mul_const _)
          (((integrable_norm_sq_gaussianSum x).add hint_flip).div_const 2) hpt
    _ = gaussianSecondMoment x ^ 2 := by
        rw [integral_div, integral_add (integrable_norm_sq_gaussianSum x) hint_flip,
          Probability.integral_comp_signFlipEquiv_stdGaussian ε
            (fun g : EuclideanSpace ℝ ι ↦ ‖∑ j, g j • x j‖ ^ 2),
          ← gaussianSecondMoment_sq]
        ring

/-- The Gaussian second moment separates finite families in a normed space. -/
@[simp]
theorem gaussianSecondMoment_eq_zero_iff (x : ι → Y) :
    gaussianSecondMoment x = 0 ↔ x = 0 := by
  refine ⟨fun hx ↦ funext fun i ↦ ?_, fun hx ↦ hx ▸ gaussianSecondMoment_zero⟩
  exact norm_eq_zero.1 (le_antisymm (hx ▸ norm_le_gaussianSecondMoment x i) (norm_nonneg _))

end TauCeti
