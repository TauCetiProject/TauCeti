/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.MeanInequalities

/-!
# Young's inequality and weighted `ℓ²` estimates for discrete convolution

This file proves the basic `ℓᵖ` estimates for Mathlib's discrete convolution
`DiscreteConvolution.addConvolution` on an additive group, and the resulting **algebra property
of weighted `ℓ²` spaces**: for `s > 1 / 2`, the sequences `a : ℤ → E` with
`∑ₙ ((1 + |n|) ^ s ‖a n‖)² < ∞` are closed under convolution through a continuous bilinear map,
with an explicit bound. Through Fourier coefficients these are the Sobolev spaces `H^s` of the
circle, and convolution of coefficients is multiplication of functions, so this is the coefficient
form of the statement that `H^s` of the circle is an algebra for `s > 1 / 2`.

All estimates are first proved for unconditional sums in `ℝ≥0∞`, where they need no summability
hypotheses, and then transferred to real sums.

## Main statements

* `DiscreteConvolution.addConvolution_eq_tsum_sub`: on an additive group,
  `(f ⋆₊[L] g) x = ∑' y, L (f (x - y)) (g y)`.
* `DiscreteConvolution.addConvolutionExists_of_memℓp`: the convolution of a bounded family with a
  summable one exists.
* `DiscreteConvolution.enorm_addConvolution_le`: `‖(f ⋆ g) x‖ₑ ≤ ‖L‖ₑ (‖f‖ₑ ⋆ ‖g‖ₑ) x`.
* `DiscreteConvolution.tsum_addRingConvolution_sq_le`: **Young's inequality**
  `‖f ⋆ g‖₂ ≤ ‖g‖₁ ‖f‖₂` for `ℝ≥0∞`-valued families, in squared form.
* `DiscreteConvolution.tsum_sq_mul_addRingConvolution_le`: the weighted (tame) estimate
  `‖ω (f ⋆ g)‖₂² ≤ 2 c² (‖g‖₁² ‖ω f‖₂² + ‖f‖₁² ‖ω g‖₂²)` for a weight with
  `ω (x + y) ≤ c (ω x + ω y)`.
* `DiscreteConvolution.tsum_sq_one_add_norm_rpow_mul_enorm_addConvolution_le`: the weighted `ℓ²`
  algebra estimate with weights `(1 + ‖x‖) ^ s`, in `ℝ≥0∞`.
* `DiscreteConvolution.summable_sq_one_add_abs_rpow_mul_norm_addConvolution` and
  `DiscreteConvolution.tsum_sq_one_add_abs_rpow_mul_norm_addConvolution_le`: for `s > 1 / 2`,
  the weighted `ℓ²` spaces on `ℤ` are closed under convolution, with
  `‖(1 + |n|) ^ s (a ⋆ b)‖₂² ≤ 4 ^ (s + 1) ‖L‖² (∑ₙ (1 + |n|) ^ (-2 s)) ‖(1 + |n|) ^ s a‖₂²
  ‖(1 + |n|) ^ s b‖₂²`.
* `DiscreteConvolution.addConvolutionExists_of_summable_sq_one_add_abs_rpow_mul_norm`: for
  `s > 1 / 2` and a complete target, the convolution of two such sequences exists, so `a ⋆ b` is
  the pointwise convolution sum. The estimates themselves need no completeness: they bound
  `‖(a ⋆ b) n‖`, whatever value the sum takes.

## References

* M. E. Taylor, *Partial Differential Equations III*, Chapter 13, Section 3 (Sobolev spaces as
  algebras, and the tame product estimate).
* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  Proposition 8.9 (Young's inequality).
-/

public section

open scoped ENNReal DiscreteConvolution

private theorem rpow_one_div_two_mul_self (a : ℝ≥0∞) :
    a ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) = a := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
  norm_num

namespace TauCeti

/-- The weight `(1 + ‖x‖) ^ s` is subadditive up to a constant: for `s ≥ 0`,
`(1 + ‖x + y‖) ^ s ≤ 2 ^ s ((1 + ‖x‖) ^ s + (1 + ‖y‖) ^ s)`. -/
theorem one_add_norm_add_rpow_le {E : Type*} [SeminormedAddGroup E] {s : ℝ} (hs : 0 ≤ s)
    (x y : E) :
    (1 + ‖x + y‖) ^ s ≤ 2 ^ s * ((1 + ‖x‖) ^ s + (1 + ‖y‖) ^ s) := by
  have hx : 0 ≤ 1 + ‖x‖ := by positivity
  have hy : 0 ≤ 1 + ‖y‖ := by positivity
  calc (1 + ‖x + y‖) ^ s ≤ (2 * max (1 + ‖x‖) (1 + ‖y‖)) ^ s := by
        gcongr
        linarith [norm_add_le x y, le_max_left (1 + ‖x‖) (1 + ‖y‖),
          le_max_right (1 + ‖x‖) (1 + ‖y‖)]
    _ = 2 ^ s * max (1 + ‖x‖) (1 + ‖y‖) ^ s :=
        Real.mul_rpow zero_le_two (hx.trans (le_max_left _ _))
    _ ≤ 2 ^ s * ((1 + ‖x‖) ^ s + (1 + ‖y‖) ^ s) := by
        gcongr
        rcases le_total (1 + ‖x‖) (1 + ‖y‖) with h | h
        · rw [max_eq_right h]
          exact le_add_of_nonneg_left (Real.rpow_nonneg hx s)
        · rw [max_eq_left h]
          exact le_add_of_nonneg_right (Real.rpow_nonneg hy s)

/-- The weights `(1 + |n|) ^ r` are summable over `ℤ` for `r < -1`. -/
theorem summable_one_add_abs_int_rpow {r : ℝ} (hr : r < -1) :
    Summable fun n : ℤ ↦ (1 + |(n : ℝ)|) ^ r := by
  refine Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow (b := -r) (by linarith))
    ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
  rw [neg_neg, Real.norm_of_nonneg (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (abs_pos.2 (Int.cast_ne_zero.2 hn))
    (le_add_of_nonneg_left zero_le_one) (by linarith)

/-- **Weighted `ℓ²` bounds `ℓ¹`.** By the Cauchy–Schwarz inequality,
`(∑' x, h x) ^ 2 ≤ (∑' x, (1 + ‖x‖) ^ (-2 s)) * ∑' x, ((1 + ‖x‖) ^ s * h x) ^ 2`
for every family `h` in `ℝ≥0∞`. On `ℤ` the first factor is finite for `s > 1 / 2`
(`TauCeti.summable_one_add_abs_int_rpow`). -/
theorem sq_tsum_le_tsum_one_add_norm_rpow_mul {G : Type*} [SeminormedAddGroup G] (s : ℝ)
    (h : G → ℝ≥0∞) :
    (∑' x, h x) ^ 2 ≤ (∑' x : G, ENNReal.ofReal ((1 + ‖x‖) ^ (-2 * s))) *
      ∑' x, (ENNReal.ofReal ((1 + ‖x‖) ^ s) * h x) ^ 2 := by
  have hw (x : G) : 0 < 1 + ‖x‖ := by positivity
  -- Write `h x = (1 + ‖x‖) ^ (-s) * ((1 + ‖x‖) ^ s * h x)` and apply Cauchy–Schwarz.
  have hsplit (x : G) : h x =
      ENNReal.ofReal ((1 + ‖x‖) ^ (-s)) * (ENNReal.ofReal ((1 + ‖x‖) ^ s) * h x) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add (hw x),
      neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
  have hsq (x : G) : ENNReal.ofReal ((1 + ‖x‖) ^ (-s)) ^ (2 : ℝ) =
      ENNReal.ofReal ((1 + ‖x‖) ^ (-2 * s)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) zero_le_two, ← Real.rpow_mul (hw x).le,
      mul_comm (-s), neg_mul, mul_neg]
  have hCS := ENNReal.inner_le_Lp_mul_Lq_tsum (fun x ↦ ENNReal.ofReal ((1 + ‖x‖) ^ (-s)))
    (fun x ↦ ENNReal.ofReal ((1 + ‖x‖) ^ s) * h x) Real.HolderConjugate.two_two
  simp only [hsq, ENNReal.rpow_two, ← hsplit] at hCS
  calc (∑' x, h x) ^ 2 ≤ ((∑' x, ENNReal.ofReal ((1 + ‖x‖) ^ (-2 * s))) ^ (1 / 2 : ℝ) *
        (∑' x, (ENNReal.ofReal ((1 + ‖x‖) ^ s) * h x) ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = _ := by rw [mul_pow, sq, sq, rpow_one_div_two_mul_self, rpow_one_div_two_mul_self]

end TauCeti

namespace DiscreteConvolution

section AddGroup

variable {M S E E' F R : Type*} [AddGroup M]

/-- On an additive group, the fibre of addition at `x` is parametrised by its second coordinate,
so additive convolution is the familiar sum `(f ⋆₊[L] g) x = ∑' y, L (f (x - y)) (g y)`. -/
theorem addConvolution_eq_tsum_sub [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E']
    [AddCommMonoid F] [Module S E] [Module S E'] [Module S F] [TopologicalSpace F]
    (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') (x : M) :
    (f ⋆₊[L] g) x = ∑' y, L (f (x - y)) (g y) := by
  let e : M ≃ addFiber x :=
    { toFun y := ⟨(x - y, y), mem_addFiber.2 (sub_add_cancel x y)⟩
      invFun ab := ab.1.2
      left_inv _ := rfl
      right_inv ab := Subtype.ext <| Prod.ext (eq_sub_of_add_eq (mem_addFiber.1 ab.2)).symm rfl }
  rw [addConvolution]
  exact (e.tsum_eq fun ab ↦ L (f ab.1.1) (g ab.1.2)).symm

/-- On an additive group, `(f ⋆ᵣ₊ g) x = ∑' y, f (x - y) * g y`. -/
theorem addRingConvolution_eq_tsum_sub [NonUnitalNonAssocSemiring R] [TopologicalSpace R]
    (f g : M → R) (x : M) :
    (f ⋆ᵣ₊ g) x = ∑' y, f (x - y) * g y :=
  addConvolution_eq_tsum_sub _ f g x

end AddGroup

section Existence

variable {𝕜 M E E' F : Type*} [NontriviallyNormedField 𝕜] [AddGroup M]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The convolution of a bounded family with a summable family exists. -/
theorem addConvolutionExists_of_memℓp [CompleteSpace F] (L : E →L[𝕜] E' →L[𝕜] F) {f : M → E}
    {g : M → E'} (hf : Memℓp f ∞) (hg : Memℓp g 1) :
    AddConvolutionExists L.toLinearMap₁₂ f g := by
  intro x
  obtain ⟨C, hC⟩ := memℓp_infty_iff.1 hf
  have hg' : Summable fun y ↦ ‖g y‖ := by simpa using (memℓp_gen_iff (by simp)).1 hg
  -- The second coordinate is injective on the fibre at `x`.
  have hinj : Function.Injective fun ab : addFiber x ↦ ab.1.2 := fun ab ab' h ↦ by
    have h₁ := mem_addFiber.1 ab.2
    have h₂ := mem_addFiber.1 ab'.2
    have h' : ab.1.2 = ab'.1.2 := h
    refine Subtype.ext <| Prod.ext (add_right_cancel (b := ab.1.2) ?_) h
    rw [h₁, h', h₂]
  refine Summable.of_norm_bounded ((hg'.comp_injective hinj).mul_left (‖L‖ * C)) fun ab ↦ ?_
  calc ‖L.toLinearMap₁₂ (f ab.1.1) (g ab.1.2)‖ ≤ ‖L‖ * ‖f ab.1.1‖ * ‖g ab.1.2‖ :=
        L.le_opNorm₂ _ _
    _ ≤ ‖L‖ * C * ‖g ab.1.2‖ := by
        gcongr
        exact hC ⟨_, rfl⟩

end Existence

section ENNReal

variable {G : Type*}

/-- **Young's inequality** `‖f ⋆ g‖₂ ≤ ‖g‖₁ ‖f‖₂` for families in `ℝ≥0∞` on an additive group,
in squared form. No summability hypotheses are needed. -/
theorem tsum_addRingConvolution_sq_le [AddGroup G] (f g : G → ℝ≥0∞) :
    ∑' x, (f ⋆ᵣ₊ g) x ^ 2 ≤ (∑' x, g x) ^ 2 * ∑' x, f x ^ 2 := by
  -- Each correlation `∑' x, f (x - y) * f (x - z)` of two translates of `f` is at most
  -- `∑' x, f x ^ 2`, by the Cauchy–Schwarz inequality.
  have hcorr (y z : G) : ∑' x, f (x - y) * f (x - z) ≤ ∑' x, f x ^ 2 := by
    have hshift (w : G) : ∑' x, f (x - w) ^ (2 : ℝ) = ∑' x, f x ^ 2 := by
      simpa only [ENNReal.rpow_two, Equiv.subRight_apply] using
        (Equiv.subRight w).tsum_eq fun x ↦ f x ^ (2 : ℝ)
    calc ∑' x, f (x - y) * f (x - z)
        ≤ (∑' x, f (x - y) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * (∑' x, f (x - z) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
          ENNReal.inner_le_Lp_mul_Lq_tsum _ _ Real.HolderConjugate.two_two
      _ = ∑' x, f x ^ 2 := by rw [hshift, hshift, rpow_one_div_two_mul_self]
  -- Expand the square and sum over `x` first.
  calc ∑' x, (f ⋆ᵣ₊ g) x ^ 2
      = ∑' y, ∑' z, g y * g z * ∑' x, f (x - y) * f (x - z) := by
        simp_rw [addRingConvolution_eq_tsum_sub, sq, ← ENNReal.tsum_mul_right,
          ← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun y ↦ ?_
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun z ↦ tsum_congr fun x ↦ by ring
    _ ≤ ∑' y, ∑' z, g y * g z * ∑' x, f x ^ 2 :=
        ENNReal.tsum_le_tsum fun y ↦ ENNReal.tsum_le_tsum fun z ↦ mul_le_mul_right (hcorr y z) _
    _ = (∑' x, g x) ^ 2 * ∑' x, f x ^ 2 := by
        simp only [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, sq]

/-- **Young's inequality** `‖f ⋆ g‖₂ ≤ ‖f‖₁ ‖g‖₂` for families in `ℝ≥0∞` on a commutative
additive group, in squared form. -/
theorem tsum_addRingConvolution_sq_le' [AddCommGroup G] (f g : G → ℝ≥0∞) :
    ∑' x, (f ⋆ᵣ₊ g) x ^ 2 ≤ (∑' x, f x) ^ 2 * ∑' x, g x ^ 2 := by
  rw [addRingConvolution_comm]
  exact tsum_addRingConvolution_sq_le g f

/-- **The weighted (tame) convolution estimate.** If the weight `ω` satisfies
`ω (x + y) ≤ c (ω x + ω y)`, then
`‖ω (f ⋆ g)‖₂² ≤ 2 c² (‖g‖₁² ‖ω f‖₂² + ‖f‖₁² ‖ω g‖₂²)`. -/
theorem tsum_sq_mul_addRingConvolution_le [AddCommGroup G] {ω : G → ℝ≥0∞} {c : ℝ≥0∞}
    (hω : ∀ x y, ω (x + y) ≤ c * (ω x + ω y)) (f g : G → ℝ≥0∞) :
    ∑' x, (ω x * (f ⋆ᵣ₊ g) x) ^ 2 ≤
      2 * c ^ 2 * ((∑' x, g x) ^ 2 * (∑' x, (ω x * f x) ^ 2) +
        (∑' x, f x) ^ 2 * ∑' x, (ω x * g x) ^ 2) := by
  -- Splitting the weight between the two factors bounds the weighted convolution pointwise.
  have hpt (x : G) : ω x * (f ⋆ᵣ₊ g) x ≤
      c * (((fun y ↦ ω y * f y) ⋆ᵣ₊ g) x + (f ⋆ᵣ₊ fun y ↦ ω y * g y) x) := by
    simp_rw [addRingConvolution_eq_tsum_sub, ← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun y ↦ ?_
    calc ω x * (f (x - y) * g y) ≤ c * (ω (x - y) + ω y) * (f (x - y) * g y) := by
          gcongr
          simpa using hω (x - y) y
      _ = c * (ω (x - y) * f (x - y) * g y + f (x - y) * (ω y * g y)) := by ring
  calc ∑' x, (ω x * (f ⋆ᵣ₊ g) x) ^ 2
      ≤ ∑' x, 2 * c ^ 2 * (((fun y ↦ ω y * f y) ⋆ᵣ₊ g) x ^ 2 +
          (f ⋆ᵣ₊ fun y ↦ ω y * g y) x ^ 2) := by
        refine ENNReal.tsum_le_tsum fun x ↦ ?_
        grw [hpt x, mul_pow, ENNReal.add_sq_le]
        exact le_of_eq (by ring)
    _ ≤ 2 * c ^ 2 * ((∑' x, g x) ^ 2 * (∑' x, (ω x * f x) ^ 2) +
          (∑' x, f x) ^ 2 * ∑' x, (ω x * g x) ^ 2) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
        gcongr
        · exact tsum_addRingConvolution_sq_le _ _
        · exact tsum_addRingConvolution_sq_le' _ _

end ENNReal

section Seminormed

variable {𝕜 E E' F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The norm of a convolution is bounded by `‖L‖ₑ` times the convolution of the norms. -/
theorem enorm_addConvolution_le (L : E →L[𝕜] E' →L[𝕜] F) {M : Type*} [AddGroup M] (f : M → E)
    (g : M → E') (x : M) :
    ‖(f ⋆₊[L.toLinearMap₁₂] g) x‖ₑ ≤ ‖L‖ₑ * ((‖f ·‖ₑ) ⋆ᵣ₊ (‖g ·‖ₑ)) x := by
  rw [addConvolution_eq_tsum_sub, addRingConvolution_eq_tsum_sub, ← ENNReal.tsum_mul_left]
  refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun y ↦ ?_)
  rw [← mul_assoc]
  exact L.le_opENorm₂ _ _

/-- **The weighted `ℓ²` algebra estimate.** For `s ≥ 0`, convolution through a continuous bilinear
map `L` satisfies, with the weights `(1 + ‖x‖) ^ s`,
`‖(1 + ‖x‖) ^ s (a ⋆ b)‖₂² ≤ 4 ^ (s + 1) ‖L‖² (∑' x, (1 + ‖x‖) ^ (-2 s)) ‖(1 + ‖x‖) ^ s a‖₂²
‖(1 + ‖x‖) ^ s b‖₂²`.
The sums are unconditional sums in `ℝ≥0∞`; the bound is finite when `s > 1 / 2` on `ℤ`
(`TauCeti.summable_one_add_abs_int_rpow`). -/
theorem tsum_sq_one_add_norm_rpow_mul_enorm_addConvolution_le {G : Type*}
    [SeminormedAddCommGroup G] (L : E →L[𝕜] E' →L[𝕜] F) {s : ℝ} (hs : 0 ≤ s) (a : G → E)
    (b : G → E') :
    ∑' x, (ENNReal.ofReal ((1 + ‖x‖) ^ s) * ‖(a ⋆₊[L.toLinearMap₁₂] b) x‖ₑ) ^ 2 ≤
      ENNReal.ofReal (4 ^ (s + 1)) * ‖L‖ₑ ^ 2 *
        (∑' x : G, ENNReal.ofReal ((1 + ‖x‖) ^ (-2 * s))) *
        (∑' x, (ENNReal.ofReal ((1 + ‖x‖) ^ s) * ‖a x‖ₑ) ^ 2) *
        ∑' x, (ENNReal.ofReal ((1 + ‖x‖) ^ s) * ‖b x‖ₑ) ^ 2 := by
  set ω : G → ℝ≥0∞ := fun x ↦ ENNReal.ofReal ((1 + ‖x‖) ^ s) with hω_def
  set K := ∑' x : G, ENNReal.ofReal ((1 + ‖x‖) ^ (-2 * s))
  set α : G → ℝ≥0∞ := fun x ↦ ‖a x‖ₑ with hα
  set β : G → ℝ≥0∞ := fun x ↦ ‖b x‖ₑ with hβ
  -- The weight is submultiplicative up to the constant `2 ^ s`.
  have hω (x y : G) : ω (x + y) ≤ ENNReal.ofReal (2 ^ s) * (ω x + ω y) := by
    simp only [hω_def]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (TauCeti.one_add_norm_add_rpow_le hs x y)
  have hc : 2 * ENNReal.ofReal (2 ^ s) ^ 2 * 2 = ENNReal.ofReal (4 ^ (s + 1)) := by
    have h4 : (4 : ℝ) ^ (s + 1) = 2 * (2 ^ s) ^ 2 * 2 := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one, show (4 : ℝ) = 2 * 2 by norm_num,
        Real.mul_rpow zero_le_two zero_le_two]
      ring
    rw [h4, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_ofNat]
  calc ∑' x, (ω x * ‖(a ⋆₊[L.toLinearMap₁₂] b) x‖ₑ) ^ 2
      ≤ ∑' x, (‖L‖ₑ * (ω x * (α ⋆ᵣ₊ β) x)) ^ 2 := by
        refine ENNReal.tsum_le_tsum fun x ↦ ?_
        rw [mul_left_comm]
        gcongr
        exact enorm_addConvolution_le L a b x
    _ = ‖L‖ₑ ^ 2 * ∑' x, (ω x * (α ⋆ᵣ₊ β) x) ^ 2 := by
        simp_rw [mul_pow, ENNReal.tsum_mul_left]
    _ ≤ ‖L‖ₑ ^ 2 * (2 * ENNReal.ofReal (2 ^ s) ^ 2 * ((∑' x, β x) ^ 2 *
          (∑' x, (ω x * α x) ^ 2) + (∑' x, α x) ^ 2 * ∑' x, (ω x * β x) ^ 2)) := by
        gcongr
        exact tsum_sq_mul_addRingConvolution_le hω α β
    _ ≤ ‖L‖ₑ ^ 2 * (2 * ENNReal.ofReal (2 ^ s) ^ 2 * (K * (∑' x, (ω x * β x) ^ 2) *
          (∑' x, (ω x * α x) ^ 2) + K * (∑' x, (ω x * α x) ^ 2) * ∑' x, (ω x * β x) ^ 2)) := by
        gcongr
        · exact TauCeti.sq_tsum_le_tsum_one_add_norm_rpow_mul s β
        · exact TauCeti.sq_tsum_le_tsum_one_add_norm_rpow_mul s α
    _ = _ := by simp only [hω_def, hα, hβ]; rw [← hc]; ring

private theorem ofReal_sq_one_add_abs_rpow_mul_norm {X : Type*} [SeminormedAddGroup X] (s : ℝ)
    (n : ℤ) (v : X) :
    ENNReal.ofReal (((1 + |(n : ℝ)|) ^ s * ‖v‖) ^ 2) =
      (ENNReal.ofReal ((1 + ‖n‖) ^ s) * ‖v‖ₑ) ^ 2 := by
  rw [Int.norm_eq_abs, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity),
    ofReal_norm]

/-- The weighted `ℓ²` algebra estimate on `ℤ`, as an inequality in `ℝ≥0∞` between real sums. -/
private theorem ofReal_tsum_sq_one_add_abs_rpow_mul_norm_addConvolution_le
    (L : E →L[𝕜] E' →L[𝕜] F) {s : ℝ} (hs : 1 / 2 < s) {a : ℤ → E} {b : ℤ → E'}
    (ha : Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖a n‖) ^ 2)
    (hb : Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖b n‖) ^ 2) :
    ∑' n : ℤ, ENNReal.ofReal (((1 + |(n : ℝ)|) ^ s * ‖(a ⋆₊[L.toLinearMap₁₂] b) n‖) ^ 2) ≤
      ENNReal.ofReal (4 ^ (s + 1) * ‖L‖ ^ 2 * (∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-2 * s)) *
        (∑' n : ℤ, ((1 + |(n : ℝ)|) ^ s * ‖a n‖) ^ 2) *
        ∑' n : ℤ, ((1 + |(n : ℝ)|) ^ s * ‖b n‖) ^ 2) := by
  have hK := TauCeti.summable_one_add_abs_int_rpow (r := -2 * s) (by linarith)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (norm_nonneg L), ofReal_norm,
    ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hK,
    ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) ha,
    ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hb]
  simp only [ofReal_sq_one_add_abs_rpow_mul_norm]
  simp only [← Int.norm_eq_abs]
  exact tsum_sq_one_add_norm_rpow_mul_enorm_addConvolution_le L (by linarith) a b

/-- **Weighted `ℓ²` spaces on `ℤ` are algebras under convolution.** For `s > 1 / 2`, if
`(1 + |n|) ^ s ‖a n‖` and `(1 + |n|) ^ s ‖b n‖` are square-summable, so is
`(1 + |n|) ^ s ‖(a ⋆ b) n‖`. For a complete target the convolution exists
(`DiscreteConvolution.addConvolutionExists_of_summable_sq_one_add_abs_rpow_mul_norm`). -/
theorem summable_sq_one_add_abs_rpow_mul_norm_addConvolution (L : E →L[𝕜] E' →L[𝕜] F) {s : ℝ}
    (hs : 1 / 2 < s) {a : ℤ → E} {b : ℤ → E'}
    (ha : Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖a n‖) ^ 2)
    (hb : Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖b n‖) ^ 2) :
    Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖(a ⋆₊[L.toLinearMap₁₂] b) n‖) ^ 2 :=
  (ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (ofReal_tsum_sq_one_add_abs_rpow_mul_norm_addConvolution_le L hs ha hb))).congr
    fun _ ↦ ENNReal.toReal_ofReal (sq_nonneg _)

/-- **The weighted `ℓ²` algebra estimate on `ℤ`.** For `s > 1 / 2`,
`∑ₙ ((1 + |n|) ^ s ‖(a ⋆ b) n‖)² ≤ 4 ^ (s + 1) ‖L‖² (∑ₙ (1 + |n|) ^ (-2 s))
(∑ₙ ((1 + |n|) ^ s ‖a n‖)²) (∑ₙ ((1 + |n|) ^ s ‖b n‖)²)`. -/
theorem tsum_sq_one_add_abs_rpow_mul_norm_addConvolution_le (L : E →L[𝕜] E' →L[𝕜] F) {s : ℝ}
    (hs : 1 / 2 < s) {a : ℤ → E} {b : ℤ → E'}
    (ha : Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖a n‖) ^ 2)
    (hb : Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖b n‖) ^ 2) :
    ∑' n : ℤ, ((1 + |(n : ℝ)|) ^ s * ‖(a ⋆₊[L.toLinearMap₁₂] b) n‖) ^ 2 ≤
      4 ^ (s + 1) * ‖L‖ ^ 2 * (∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-2 * s)) *
        (∑' n : ℤ, ((1 + |(n : ℝ)|) ^ s * ‖a n‖) ^ 2) *
        ∑' n : ℤ, ((1 + |(n : ℝ)|) ^ s * ‖b n‖) ^ 2 := by
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_tsum_of_nonneg
    (fun _ ↦ sq_nonneg _) (summable_sq_one_add_abs_rpow_mul_norm_addConvolution L hs ha hb)]
  exact ofReal_tsum_sq_one_add_abs_rpow_mul_norm_addConvolution_le L hs ha hb

/-- For `s > 1 / 2` and a complete target, the convolution of two weighted `ℓ²` sequences on `ℤ`
exists, so `a ⋆ b` in the two estimates above is the pointwise convolution sum. -/
theorem addConvolutionExists_of_summable_sq_one_add_abs_rpow_mul_norm [CompleteSpace F]
    (L : E →L[𝕜] E' →L[𝕜] F) {s : ℝ} (hs : 1 / 2 < s) {a : ℤ → E} {b : ℤ → E'}
    (ha : Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖a n‖) ^ 2)
    (hb : Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖b n‖) ^ 2) :
    AddConvolutionExists L.toLinearMap₁₂ a b := by
  have hK : ∑' n : ℤ, ENNReal.ofReal ((1 + ‖n‖) ^ (-2 * s)) ≠ ∞ := by
    simp only [Int.norm_eq_abs]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity)
      (TauCeti.summable_one_add_abs_int_rpow (r := -2 * s) (by linarith))]
    exact ENNReal.ofReal_ne_top
  -- Weighted `ℓ²` sequences on `ℤ` are summable.
  have hl1 (h : ℤ → ℝ≥0∞) (hh : ∑' n, (ENNReal.ofReal ((1 + ‖n‖) ^ s) * h n) ^ 2 ≠ ∞) :
      ∑' n, h n ≠ ∞ := fun htop ↦ ENNReal.mul_ne_top hK hh <| top_le_iff.1 <| by
    simpa [htop] using TauCeti.sq_tsum_le_tsum_one_add_norm_rpow_mul s h
  have ha' : ∑' n, ‖a n‖ₑ ≠ ∞ := hl1 _ <| by
    simp only [← ofReal_sq_one_add_abs_rpow_mul_norm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) ha]
    exact ENNReal.ofReal_ne_top
  have hb' : ∑' n, ‖b n‖ₑ ≠ ∞ := hl1 _ <| by
    simp only [← ofReal_sq_one_add_abs_rpow_mul_norm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hb]
    exact ENNReal.ofReal_ne_top
  intro x
  unfold AddConvolutionExistsAt
  refine Summable.of_norm <| tsum_enorm_ne_top_iff_summable_norm.1 <| ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (enorm_ne_top (x := L)) (ENNReal.mul_ne_top ha' hb')) ?_
  calc ∑' ab : addFiber x, ‖L.toLinearMap₁₂ (a ab.1.1) (b ab.1.2)‖ₑ
      ≤ ∑' p : ℤ × ℤ, ‖L.toLinearMap₁₂ (a p.1) (b p.2)‖ₑ :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
          fun p : ℤ × ℤ ↦ ‖L.toLinearMap₁₂ (a p.1) (b p.2)‖ₑ
    _ ≤ ∑' p : ℤ × ℤ, ‖L‖ₑ * ‖a p.1‖ₑ * ‖b p.2‖ₑ :=
        ENNReal.tsum_le_tsum fun p ↦ L.le_opENorm₂ _ _
    _ = ‖L‖ₑ * ((∑' n, ‖a n‖ₑ) * ∑' n, ‖b n‖ₑ) := by
        rw [ENNReal.tsum_prod (f := fun m n ↦ ‖L‖ₑ * ‖a m‖ₑ * ‖b n‖ₑ)]
        simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, mul_assoc]

end Seminormed

end DiscreteConvolution
