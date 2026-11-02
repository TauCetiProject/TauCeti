/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import TauCeti.Topology.Algebra.InfiniteSum.DiscreteConvolution
import Mathlib.Analysis.MeanInequalitiesPow
import TauCeti.Analysis.MeanInequalities
import TauCeti.Analysis.Normed.Lp.WeightedSum
import TauCeti.Analysis.PSeries
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Young's inequality and weighted `ℓ²` estimates for discrete convolution

This file proves the basic `ℓᵖ` estimates for Mathlib's discrete convolution
`DiscreteConvolution.addConvolution`, and the resulting **bilinear
convolution estimate for weighted `ℓ²` spaces**: for `s > 1 / 2`, convolution through a continuous
bilinear map `L : E →L E' →L F` sends a pair of sequences `a : ℤ → E`, `b : ℤ → E'` with
`∑ₙ ((1 + |n|) ^ s ‖a n‖)² < ∞` and `∑ₙ ((1 + |n|) ^ s ‖b n‖)² < ∞` to a sequence `ℤ → F` with
the same property, with an explicit bound. Through Fourier coefficients these are the Sobolev
spaces `H^s` of the circle, and convolution of coefficients is multiplication of functions, so
taking `E = E' = F` and `L` the multiplication gives the coefficient form of the statement that
`H^s` of the circle is an algebra for `s > 1 / 2`.

All estimates are first proved for unconditional sums in `ℝ≥0∞`, where they need no summability
hypotheses, and then transferred to real sums.

## Main statements

* `DiscreteConvolution.addConvolutionExists_of_memℓp`: on a right-cancellative additive monoid,
  the convolution of a bounded family with a summable one exists.
* `DiscreteConvolution.enorm_addConvolution_le`: on an additive monoid,
  `‖(f ⋆ g) x‖ₑ ≤ ‖L‖ₑ (‖f‖ₑ ⋆ ‖g‖ₑ) x`.
* `DiscreteConvolution.tsum_addRingConvolution_sq_le` and
  `DiscreteConvolution.tsum_addRingConvolution_sq_le'`: **Young's inequality**
  `‖f ⋆ g‖₂ ≤ ‖g‖₁ ‖f‖₂` and `‖f ⋆ g‖₂ ≤ ‖f‖₁ ‖g‖₂` for `ℝ≥0∞`-valued families, in squared form.
* `DiscreteConvolution.tsum_sq_mul_addRingConvolution_le`: the weighted (tame) estimate
  `‖ω (f ⋆ g)‖₂² ≤ 2 c² (‖g‖₁² ‖ω f‖₂² + ‖f‖₁² ‖ω g‖₂²)` for a weight with
  `ω (x + y) ≤ c (ω x + ω y)`.
* `DiscreteConvolution.tsum_sq_one_add_norm_rpow_mul_enorm_addConvolution_le`: the weighted `ℓ²`
  bilinear convolution estimate with weights `(1 + ‖x‖) ^ s`, in `ℝ≥0∞`.
* `DiscreteConvolution.tsum_sq_one_add_abs_rpow_mul_norm_addConvolution_le` and
  `addConvolutionExists_and_summable_sq_one_add_abs_rpow_mul_norm_addConvolution`: for `s > 1 / 2`
  and a complete target, convolution maps the weighted `ℓ²` spaces of `E` and `E'` on `ℤ` into
  that of `F`: the convolution `a ⋆ b` exists, and
  `‖(1 + |n|) ^ s (a ⋆ b)‖₂² ≤ 4 ^ (s + 1) ‖L‖² (∑ₙ (1 + |n|) ^ (-2 s)) ‖(1 + |n|) ^ s a‖₂²
  ‖(1 + |n|) ^ s b‖₂²`.

## References

* M. E. Taylor, *Partial Differential Equations III*, Chapter 13, Section 3 (Sobolev spaces as
  algebras, and the tame product estimate).
* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  Proposition 8.9 (Young's inequality).
-/

public section

open scoped ENNReal DiscreteConvolution

namespace DiscreteConvolution

section Existence

variable {𝕜 M E E' F : Type*} [NontriviallyNormedField 𝕜] [AddRightCancelMonoid M]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- On a right-cancellative additive monoid, the convolution of a bounded family with a
summable family exists. -/
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
      _ = ∑' x, f x ^ 2 := by
          rw [hshift, hshift, ← sq, ← ENNReal.rpow_mul_natCast]
          norm_num
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

/-- **Young's inequality** in the other orientation, `‖f ⋆ g‖₂ ≤ ‖f‖₁ ‖g‖₂`, for families in
`ℝ≥0∞` on an additive group, in squared form. On a noncommutative group it does not follow from
`tsum_addRingConvolution_sq_le` by commutativity; it is that inequality on the opposite group. -/
theorem tsum_addRingConvolution_sq_le' [AddGroup G] (f g : G → ℝ≥0∞) :
    ∑' x, (f ⋆ᵣ₊ g) x ^ 2 ≤ (∑' x, f x) ^ 2 * ∑' x, g x ^ 2 := by
  -- Convolution on `G` is convolution in the opposite order on `Gᵃᵒᵖ`.
  have hop (x : G) : (f ⋆ᵣ₊ g) x =
      ((g ∘ AddOpposite.unop) ⋆ᵣ₊ (f ∘ AddOpposite.unop)) (AddOpposite.op x) := by
    rw [addRingConvolution_eq_tsum_neg_add, addRingConvolution_eq_tsum_sub,
      ← (AddOpposite.opEquiv (α := G)).tsum_eq]
    exact tsum_congr fun y ↦ mul_comm _ _
  calc ∑' x, (f ⋆ᵣ₊ g) x ^ 2
      = ∑' x : Gᵃᵒᵖ, ((g ∘ AddOpposite.unop) ⋆ᵣ₊ (f ∘ AddOpposite.unop)) x ^ 2 := by
        simp only [hop]
        exact AddOpposite.opEquiv.tsum_eq fun x ↦
          ((g ∘ AddOpposite.unop) ⋆ᵣ₊ (f ∘ AddOpposite.unop)) x ^ 2
    _ ≤ _ := tsum_addRingConvolution_sq_le _ _
    _ = (∑' x, f x) ^ 2 * ∑' x, g x ^ 2 := by
        rw [← AddOpposite.opEquiv.symm.tsum_eq f, ← AddOpposite.opEquiv.symm.tsum_eq (g · ^ 2)]
        simp only [AddOpposite.opEquiv_symm_apply, Function.comp_apply]

/-- **The weighted (tame) convolution estimate.** If the weight `ω` satisfies
`ω (x + y) ≤ c (ω x + ω y)`, then
`‖ω (f ⋆ g)‖₂² ≤ 2 c² (‖g‖₁² ‖ω f‖₂² + ‖f‖₁² ‖ω g‖₂²)`. -/
theorem tsum_sq_mul_addRingConvolution_le [AddGroup G] {ω : G → ℝ≥0∞} {c : ℝ≥0∞}
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
  -- `(a + b) ^ 2 ≤ 2 (a ^ 2 + b ^ 2)`, the power mean inequality with exponent `2`.
  have hsq (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b one_le_two
    norm_num [ENNReal.rpow_two] at h
    exact h
  calc ∑' x, (ω x * (f ⋆ᵣ₊ g) x) ^ 2
      ≤ ∑' x, 2 * c ^ 2 * (((fun y ↦ ω y * f y) ⋆ᵣ₊ g) x ^ 2 +
          (f ⋆ᵣ₊ fun y ↦ ω y * g y) x ^ 2) := by
        refine ENNReal.tsum_le_tsum fun x ↦ ?_
        grw [hpt x, mul_pow, hsq]
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

/-- On an additive monoid, the norm of a convolution is bounded by `‖L‖ₑ` times the convolution
of the norms. -/
theorem enorm_addConvolution_le (L : E →L[𝕜] E' →L[𝕜] F) {M : Type*} [AddMonoid M] (f : M → E)
    (g : M → E') (x : M) :
    ‖(f ⋆₊[L.toLinearMap₁₂] g) x‖ₑ ≤ ‖L‖ₑ * ((‖f ·‖ₑ) ⋆ᵣ₊ (‖g ·‖ₑ)) x := by
  simp only [addRingConvolution_apply, addConvolution, ← ENNReal.tsum_mul_left]
  refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun ab ↦ ?_)
  rw [← mul_assoc]
  exact L.le_opENorm₂ _ _

/-- **The weighted `ℓ²` convolution estimate.** For `s ≥ 0`, convolution through a continuous
bilinear map `L` satisfies, with the weights `(1 + ‖x‖) ^ s`,
`‖(1 + ‖x‖) ^ s (a ⋆ b)‖₂² ≤ 4 ^ (s + 1) ‖L‖² (∑' x, (1 + ‖x‖) ^ (-2 s)) ‖(1 + ‖x‖) ^ s a‖₂²
‖(1 + ‖x‖) ^ s b‖₂²`.
The sums are unconditional sums in `ℝ≥0∞`. On `ℤ`, the inverse-weight sum
`∑' x, (1 + ‖x‖) ^ (-2 s)` is finite when `s > 1 / 2` (`TauCeti.summable_one_add_abs_int_rpow`),
so the bound is finite whenever the weighted square sums of `a` and `b` are also finite. -/
theorem tsum_sq_one_add_norm_rpow_mul_enorm_addConvolution_le {G : Type*}
    [SeminormedAddGroup G] (L : E →L[𝕜] E' →L[𝕜] F) {s : ℝ} (hs : 0 ≤ s) (a : G → E)
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
      rw [Real.rpow_add (by norm_num), Real.rpow_one, ← Real.rpow_natCast,
        ← Real.rpow_mul zero_le_two, mul_comm s, Real.rpow_mul zero_le_two]
      norm_num
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

/-- The weighted `ℓ²` convolution estimate on `ℤ`, as an inequality in `ℝ≥0∞` between real sums. -/
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
  simp only [TauCeti.ofReal_sq_one_add_abs_rpow_mul_norm]
  simp only [← Int.norm_eq_abs]
  exact tsum_sq_one_add_norm_rpow_mul_enorm_addConvolution_le L (by linarith) a b

/-- For `s > 1 / 2` and a complete target, the convolution of two weighted `ℓ²` sequences on `ℤ`
exists. -/
private theorem addConvolutionExists_of_summable_sq_one_add_abs_rpow_mul_norm [CompleteSpace F]
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
    simp only [← TauCeti.ofReal_sq_one_add_abs_rpow_mul_norm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) ha]
    exact ENNReal.ofReal_ne_top
  have hb' : ∑' n, ‖b n‖ₑ ≠ ∞ := hl1 _ <| by
    simp only [← TauCeti.ofReal_sq_one_add_abs_rpow_mul_norm]
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

/-- The total convolution of two weighted square-summable sequences on `ℤ` is weighted
square-summable for `s > 1 / 2`, without requiring completeness of its target. -/
theorem summable_sq_one_add_abs_rpow_mul_norm_addConvolution
    (L : E →L[𝕜] E' →L[𝕜] F) {s : ℝ} (hs : 1 / 2 < s) {a : ℤ → E} {b : ℤ → E'}
    (ha : Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖a n‖) ^ 2)
    (hb : Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖b n‖) ^ 2) :
    Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖(a ⋆₊[L.toLinearMap₁₂] b) n‖) ^ 2 :=
  (ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (ofReal_tsum_sq_one_add_abs_rpow_mul_norm_addConvolution_le L hs ha hb))).congr
    fun _ ↦ ENNReal.toReal_ofReal (sq_nonneg _)

/-- **Convolution of weighted `ℓ²` sequences on `ℤ` is weighted `ℓ²`.** For `s > 1 / 2` and a
complete target, if `(1 + |n|) ^ s ‖a n‖` and `(1 + |n|) ^ s ‖b n‖` are square-summable, then the
convolution `a ⋆ b` exists, so it is the pointwise convolution sum, and
`(1 + |n|) ^ s ‖(a ⋆ b) n‖` is square-summable. -/
theorem addConvolutionExists_and_summable_sq_one_add_abs_rpow_mul_norm_addConvolution
    [CompleteSpace F] (L : E →L[𝕜] E' →L[𝕜] F) {s : ℝ} (hs : 1 / 2 < s) {a : ℤ → E} {b : ℤ → E'}
    (ha : Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖a n‖) ^ 2)
    (hb : Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖b n‖) ^ 2) :
    AddConvolutionExists L.toLinearMap₁₂ a b ∧
      Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖(a ⋆₊[L.toLinearMap₁₂] b) n‖) ^ 2 :=
  ⟨addConvolutionExists_of_summable_sq_one_add_abs_rpow_mul_norm L hs ha hb,
    summable_sq_one_add_abs_rpow_mul_norm_addConvolution L hs ha hb⟩

/-- **The weighted `ℓ²` convolution estimate on `ℤ`.** For `s > 1 / 2`,
`∑ₙ ((1 + |n|) ^ s ‖(a ⋆ b) n‖)² ≤ 4 ^ (s + 1) ‖L‖² (∑ₙ (1 + |n|) ^ (-2 s))
(∑ₙ ((1 + |n|) ^ s ‖a n‖)²) (∑ₙ ((1 + |n|) ^ s ‖b n‖)²)`. -/
theorem tsum_sq_one_add_abs_rpow_mul_norm_addConvolution_le
    (L : E →L[𝕜] E' →L[𝕜] F) {s : ℝ} (hs : 1 / 2 < s) {a : ℤ → E} {b : ℤ → E'}
    (ha : Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖a n‖) ^ 2)
    (hb : Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖b n‖) ^ 2) :
    ∑' n : ℤ, ((1 + |(n : ℝ)|) ^ s * ‖(a ⋆₊[L.toLinearMap₁₂] b) n‖) ^ 2 ≤
      4 ^ (s + 1) * ‖L‖ ^ 2 * (∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-2 * s)) *
        (∑' n : ℤ, ((1 + |(n : ℝ)|) ^ s * ‖a n‖) ^ 2) *
        ∑' n : ℤ, ((1 + |(n : ℝ)|) ^ s * ‖b n‖) ^ 2 := by
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_tsum_of_nonneg
    (fun _ ↦ sq_nonneg _)
    (summable_sq_one_add_abs_rpow_mul_norm_addConvolution L hs ha hb)]
  exact ofReal_tsum_sq_one_add_abs_rpow_mul_norm_addConvolution_le L hs ha hb

end Seminormed

end DiscreteConvolution
