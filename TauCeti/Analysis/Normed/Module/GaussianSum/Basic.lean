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
import TauCeti.Probability.Distributions.Gaussian.L2

/-!
# Second moments of finite Gaussian sums

The Gaussian second moment of a finite family in a real normed space is the square root
of the expected squared norm of its sum with independent standard Gaussian coefficients.
The coefficient space is the native Euclidean space with its standard Gaussian measure.
In particular the definition works for empty families and does not require completeness
of the target space.

We also record the basic invariance and structural properties used to compare Gaussian sums:
coordinatewise sign-flip invariance of `stdGaussian`, invariance under reindexing, zero-padding,
and coordinatewise sign changes, subadditivity (the `L²` triangle inequality), comparison along
bounded additive maps, and the exact value on constant and single-element families.

## References

* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*,
  §3, pp. 33–37.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace TauCeti

variable {ι Y : Type*} [Fintype ι] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

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

/-- A bound on the expected squared norm bounds the Gaussian second moment. -/
theorem gaussianSecondMoment_le_of_sq_le {x : ι → Y} {c : ℝ} (hc : 0 ≤ c)
    (h : ∫ g : EuclideanSpace ℝ ι, ‖∑ i, g i • x i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) ≤
      c ^ 2) :
    gaussianSecondMoment x ≤ c :=
  Real.sqrt_le_iff.2 ⟨hc, h⟩

/-- Multiplying a family by a real scalar multiplies its Gaussian second moment by the
absolute value of that scalar. -/
theorem gaussianSecondMoment_smul (x : ι → Y) (c : ℝ) :
    gaussianSecondMoment (fun i ↦ c • x i) = |c| * gaussianSecondMoment x := by
  have hs (g : EuclideanSpace ℝ ι) :
      (∑ i, g i • (c • x i)) = c • ∑ i, g i • x i := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _
  apply (sq_eq_sq₀ (gaussianSecondMoment_nonneg _)
    (mul_nonneg (abs_nonneg _) (gaussianSecondMoment_nonneg _))).1
  rw [mul_pow, gaussianSecondMoment_sq, gaussianSecondMoment_sq]
  simp_rw [hs, norm_smul, mul_pow]
  rw [integral_const_mul, Real.norm_eq_abs]

@[simp]
theorem gaussianSecondMoment_zero : gaussianSecondMoment (0 : ι → Y) = 0 := by
  simp [gaussianSecondMoment]

/-- An empty Gaussian sum has second moment zero. -/
@[simp]
theorem gaussianSecondMoment_of_isEmpty [IsEmpty ι] (x : ι → Y) :
    gaussianSecondMoment x = 0 := by
  simp [gaussianSecondMoment]

/-- Coordinatewise sign changes preserve the standard Gaussian measure on `EuclideanSpace ℝ ι`. -/
theorem stdGaussian_map_units_smul (ε : ι → ℤˣ) :
    (stdGaussian (EuclideanSpace ℝ ι)).map
        (fun g : EuclideanSpace ℝ ι ↦ WithLp.toLp 2 fun i ↦ ε i • g i) =
      stdGaussian (EuclideanSpace ℝ ι) := by
  let L : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
    { toFun g := WithLp.toLp 2 fun i ↦ ε i • g i
      invFun g := WithLp.toLp 2 fun i ↦ ε i • g i
      left_inv g := by
        ext i
        rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h]
      right_inv g := by
        ext i
        rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h]
      map_add' g h := by
        ext i
        simp [smul_add]
      map_smul' c g := by
        ext i
        rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h]
      norm_map' g := by
        simp only [PiLp.norm_eq_of_L2]
        congr 1
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h] }
  exact stdGaussian_map L

/-- Flipping the signs of a family does not change its Gaussian second moment. -/
theorem gaussianSecondMoment_units_smul (ε : ι → ℤˣ) (x : ι → Y) :
    gaussianSecondMoment (fun i ↦ ε i • x i) = gaussianSecondMoment x := by
  rw [gaussianSecondMoment_def, gaussianSecondMoment_def]
  congr 1
  have hmap := stdGaussian_map_units_smul ε
  conv_rhs => rw [← hmap, integral_map (by fun_prop) (by fun_prop)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  dsimp only
  congr 2
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h]

/-- Reindexing a finite family along an equivalence preserves its Gaussian second moment. -/
theorem gaussianSecondMoment_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (x : ι → Y) :
    gaussianSecondMoment (x ∘ e) = gaussianSecondMoment x := by
  rw [gaussianSecondMoment_def, gaussianSecondMoment_def]
  congr 1
  let L : EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  conv_rhs => rw [← stdGaussian_map L, integral_map (by fun_prop) (by fun_prop)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  dsimp only
  congr 2
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp [L, LinearIsometryEquiv.piLpCongrLeft_apply]

/-- The Gaussian second moment satisfies the triangle inequality. -/
theorem gaussianSecondMoment_add_le (x y : ι → Y) :
    gaussianSecondMoment (x + y) ≤ gaussianSecondMoment x + gaussianSecondMoment y := by
  have hx := memLp_gaussianSum x 2 (by simp)
  have hy := memLp_gaussianSum y 2 (by simp)
  have hxy : (fun g : EuclideanSpace ℝ ι ↦ ∑ i, g i • (x + y) i) =
      (fun g ↦ ∑ i, g i • x i) + (fun g ↦ ∑ i, g i • y i) := by
    ext g
    simp [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  have hle : eLpNorm ((fun g : EuclideanSpace ℝ ι ↦ ∑ i, g i • x i) +
        fun g ↦ ∑ i, g i • y i) 2 (stdGaussian (EuclideanSpace ℝ ι)) ≤
      eLpNorm (fun g : EuclideanSpace ℝ ι ↦ ∑ i, g i • x i) 2 (stdGaussian (EuclideanSpace ℝ ι)) +
      eLpNorm (fun g : EuclideanSpace ℝ ι ↦ ∑ i, g i • y i) 2 (stdGaussian (EuclideanSpace ℝ ι)) :=
    eLpNorm_add_le one_le_two
  rw [← hxy, (memLp_gaussianSum (x + y) 2 (by simp)).eLpNorm_two_eq_ofReal_sqrt_integral,
    hx.eLpNorm_two_eq_ofReal_sqrt_integral, hy.eLpNorm_two_eq_ofReal_sqrt_integral,
    ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at hle
  exact hle

/-- Projecting a standard Gaussian vector on `ι ⊕ κ` onto its left coordinates yields a standard
Gaussian vector on `ι`. -/
private theorem stdGaussian_map_inl {κ : Type*} [Fintype κ] :
    (stdGaussian (EuclideanSpace ℝ (ι ⊕ κ))).map
        (fun g : EuclideanSpace ℝ (ι ⊕ κ) ↦ WithLp.toLp 2 (g ∘ Sum.inl)) =
      stdGaussian (EuclideanSpace ℝ ι) := by
  let P : EuclideanSpace ℝ (ι ⊕ κ) →L[ℝ] EuclideanSpace ℝ ι :=
    LinearMap.mkContinuous
      { toFun g := WithLp.toLp 2 (g ∘ Sum.inl)
        map_add' _ _ := by ext; simp
        map_smul' _ _ := by ext; simp }
      1 fun g ↦ by
        rw [one_mul, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
        exact Real.sqrt_le_sqrt (by
          rw [Fintype.sum_sum_type]
          exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
  let I : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (ι ⊕ κ) :=
    LinearMap.mkContinuous
      { toFun h := WithLp.toLp 2 (Sum.elim h 0)
        map_add' _ _ := by ext k; cases k <;> simp
        map_smul' _ _ := by ext k; cases k <;> simp }
      1 fun h ↦ by
        rw [one_mul, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
        exact Real.sqrt_le_sqrt (by simp [Fintype.sum_sum_type])
  have hP : ‖P‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hI : ‖I‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hPI : P ∘L I = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι) := by
    ext h i; simp [P, I]
  apply Measure.ext_of_charFunDual
  ext L
  have hnorm : ‖L ∘L P‖ = ‖L‖ := by
    refine le_antisymm ((L.opNorm_comp_le P).trans (mul_le_of_le_one_right (norm_nonneg L) hP)) ?_
    have hL : L = (L ∘L P) ∘L I := by
      rw [ContinuousLinearMap.comp_assoc, hPI, ContinuousLinearMap.comp_id]
    conv_lhs => rw [hL]
    exact ((L ∘L P).opNorm_comp_le I).trans (mul_le_of_le_one_right (norm_nonneg _) hI)
  calc
    charFunDual ((stdGaussian (EuclideanSpace ℝ (ι ⊕ κ))).map P) L
        = charFunDual (stdGaussian (EuclideanSpace ℝ (ι ⊕ κ))) (L ∘L P) := by
      rw [charFunDual_apply, charFunDual_apply, integral_map (by fun_prop) (by fun_prop)]
      rfl
    _ = charFunDual (stdGaussian (EuclideanSpace ℝ ι)) L := by
      rw [charFunDual_stdGaussian, charFunDual_stdGaussian, hnorm]

/-- Padding a finite family with zeros does not change its Gaussian second moment. -/
theorem gaussianSecondMoment_sumElim_zero {κ : Type*} [Fintype κ] (x : ι → Y) :
    gaussianSecondMoment (Sum.elim x (0 : κ → Y)) = gaussianSecondMoment x := by
  rw [gaussianSecondMoment_def, gaussianSecondMoment_def]
  congr 1
  conv_rhs => rw [← stdGaussian_map_inl (ι := ι) (κ := κ), integral_map (by fun_prop) (by fun_prop)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  simp [Fintype.sum_sum_type]

/-- The Gaussian second moment of a concatenated family is at most the sum of the Gaussian second
moments of its two parts. -/
theorem gaussianSecondMoment_sumElim_le {κ : Type*} [Fintype κ] (x : ι → Y) (y : κ → Y) :
    gaussianSecondMoment (Sum.elim x y) ≤ gaussianSecondMoment x + gaussianSecondMoment y := by
  have hsplit : Sum.elim x y = Sum.elim x (0 : κ → Y) + Sum.elim (0 : ι → Y) y := by
    ext k; cases k <;> simp
  have hright : gaussianSecondMoment (Sum.elim (0 : ι → Y) y) = gaussianSecondMoment y := by
    have hcomm : Sum.elim (0 : ι → Y) y = Sum.elim y (0 : ι → Y) ∘ Equiv.sumComm ι κ := by
      ext k; cases k <;> simp
    rw [hcomm, gaussianSecondMoment_comp_equiv, gaussianSecondMoment_sumElim_zero]
  rw [hsplit]
  exact (gaussianSecondMoment_add_le _ _).trans_eq
    (by rw [gaussianSecondMoment_sumElim_zero, hright])

/-- A bounded additive map `f` with `‖f y‖ ≤ M * ‖y‖` multiplies Gaussian second moments by at most
`M`. -/
theorem gaussianSecondMoment_map_le {F 𝓕 : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FunLike 𝓕 Y F] [AddMonoidHomClass 𝓕 Y F] (f : 𝓕) {M : ℝ} (hM : ∀ y, ‖f y‖ ≤ M * ‖y‖)
    (x : ι → Y) :
    gaussianSecondMoment (fun i ↦ f (x i)) ≤ M * gaussianSecondMoment x := by
  rcases subsingleton_or_nontrivial Y with hY | hY
  · have hx : x = 0 := Subsingleton.elim _ _
    have hfx : (fun i ↦ f (x i)) = (0 : ι → F) := by ext i; simp [hx]
    rw [hfx, hx, gaussianSecondMoment_zero, gaussianSecondMoment_zero, mul_zero]
  obtain ⟨y₀, hy₀⟩ := exists_ne (0 : Y)
  have hM0 : 0 ≤ M := by
    have h0 := (norm_nonneg (f y₀)).trans (hM y₀)
    exact nonneg_of_mul_nonneg_left h0 (norm_pos_iff.2 hy₀)
  have hf_cont : Continuous f := AddMonoidHomClass.continuous_of_bound f M hM
  refine gaussianSecondMoment_le_of_sq_le (mul_nonneg hM0 (gaussianSecondMoment_nonneg x)) ?_
  rw [mul_pow, gaussianSecondMoment_sq, ← integral_const_mul]
  refine integral_mono (integrable_norm_sq_gaussianSum _)
    ((integrable_norm_sq_gaussianSum x).const_mul _) fun g ↦ ?_
  have hsum : ∑ i, g i • f (x i) = f (∑ i, g i • x i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (map_real_smul f hf_cont (g i) (x i)).symm
  rw [hsum, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hM _) 2

/-- The Gaussian second moment of `card ι` copies of a vector `y` is `√(card ι) * ‖y‖`. -/
theorem gaussianSecondMoment_const (y : Y) :
    gaussianSecondMoment (fun _ : ι ↦ y) = √(Fintype.card ι) * ‖y‖ := by
  have hs (g : EuclideanSpace ℝ ι) :
      ∑ i, g i • y = ⟪WithLp.toLp 2 (fun _ : ι ↦ (1 : ℝ)), g⟫ • y := by
    rw [← Finset.sum_smul]
    congr 1
    simp [PiLp.inner_apply, mul_comm]
  rw [gaussianSecondMoment_def]
  have hint : ∫ g : EuclideanSpace ℝ ι, ‖∑ i, g i • y‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) =
      (Fintype.card ι : ℝ) * ‖y‖ ^ 2 := by
    simp_rw [hs, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [integral_mul_const, TauCeti.Probability.integral_sq_inner_stdGaussian]
    simp [PiLp.norm_sq_eq_of_L2]
  rw [hint, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- A one-element family has Gaussian second moment equal to the norm of its sole vector. -/
@[simp]
theorem gaussianSecondMoment_unique [Unique ι] (x : ι → Y) :
    gaussianSecondMoment x = ‖x default‖ := by
  have hx : x = fun _ ↦ x default := funext fun i ↦ congrArg x (Unique.eq_default i)
  rw [hx, gaussianSecondMoment_const]
  simp

end TauCeti
