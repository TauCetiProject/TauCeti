/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import TauCeti.Analysis.Convex.Uniform.Modulus
public import TauCeti.Analysis.Convex.Uniform.Smoothness
import TauCeti.Analysis.Normed.Module.Dual.Basic
import TauCeti.Analysis.Normed.Module.DualitySet

/-!
# Two-uniform convexity and smoothness

A seminormed group `E` is *two-uniformly convex with constant `c`* if
`‖x‖ ^ 2 + c * ‖y‖ ^ 2 ≤ (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2` for all `x` and `y`, and
*two-uniformly smooth with constant `c`* if the reverse inequality
`(‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2 ≤ ‖x‖ ^ 2 + c * ‖y‖ ^ 2` holds for all `x` and `y`. By the
parallelogram law, inner product spaces have both properties with constant `1`. These are the
sharp convexity and smoothness inequalities of Ball, Carlen and Lieb: `Lᵖ` spaces and the
Schatten classes are two-uniformly convex with constant `p - 1` for `1 < p ≤ 2`, and
two-uniformly smooth with constant `p - 1` for `2 ≤ p < ∞`.

This file derives from the two inequalities the quadratic bounds on the moduli of convexity and
smoothness, and proves that the two notions are dual to each other.

* Two-uniform convexity with constant `c` bounds the modulus of convexity below by
  `1 - √(1 - c ε ^ 2 / 4)` for `0 ≤ ε`, hence by `c ε ^ 2 / 8` when moreover `c ≤ 1` and
  `ε ≤ 2`; for `0 < c` the real normed space is then uniformly convex.
* Two-uniform smoothness with constant `0 ≤ c` bounds the modulus of smoothness above by
  `√(1 + c t ^ 2) - 1`, hence by `c t ^ 2 / 2`; so `ρ(t) / t → 0` as `t → 0⁺` for every
  two-uniformly smooth space: it is uniformly smooth.
* Duality: for `0 < c`, a normed space over `ℝ` or `ℂ` is two-uniformly convex with constant `c`
  exactly when its dual is two-uniformly smooth with constant `c⁻¹`, and two-uniformly smooth
  with constant `c` exactly when its dual is two-uniformly convex with constant `c⁻¹`. Through
  the duality `(Lᵖ)* = Lᵖ'`, the convexity inequality for an exponent `1 < p ≤ 2` thus gives the
  smoothness inequality for the dual exponent `p'`, with constant `(p - 1)⁻¹ = p' - 1`.

## Main declarations

* `TauCeti.IsTwoUniformlyConvex`, `TauCeti.IsTwoUniformlySmooth`: the two inequalities.
* `TauCeti.isTwoUniformlyConvex_one_of_innerProductSpace`,
  `TauCeti.isTwoUniformlySmooth_one_of_innerProductSpace`: inner product spaces.
* `TauCeti.IsTwoUniformlyConvex.mul_sq_div_eight_le_modulusOfConvexity`,
  `TauCeti.IsTwoUniformlyConvex.uniformConvexSpace`: the quadratic modulus of convexity and
  uniform convexity.
* `TauCeti.IsTwoUniformlySmooth.modulusOfSmoothness_le_mul_sq_div_two`,
  `TauCeti.IsTwoUniformlySmooth.tendsto_modulusOfSmoothness_div`: the quadratic modulus of
  smoothness and uniform smoothness.
* `TauCeti.isTwoUniformlySmooth_strongDual_iff`, `TauCeti.isTwoUniformlyConvex_strongDual_iff`:
  duality.

## References

* K. Ball, E. A. Carlen and E. H. Lieb, *Sharp uniform convexity and smoothness inequalities for
  trace norms*, Invent. Math. 115 (1994), 463–482.
* J. Lindenstrauss and L. Tzafriri, *Classical Banach Spaces II*, Springer, 1979, §1.e.
-/

public section

open Filter Set Topology RCLike

namespace TauCeti

section Defs

variable (E : Type*) [SeminormedAddCommGroup E] (c : ℝ)

/-- `E` is *two-uniformly convex with constant `c`*:
`‖x‖ ^ 2 + c * ‖y‖ ^ 2 ≤ (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2` for all `x` and `y`. Inner product spaces
satisfy it with `c = 1`, and `Lᵖ` spaces with `c = p - 1` for `1 < p ≤ 2`. -/
def IsTwoUniformlyConvex : Prop :=
  ∀ x y : E, ‖x‖ ^ 2 + c * ‖y‖ ^ 2 ≤ (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2

/-- `E` is *two-uniformly smooth with constant `c`*:
`(‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2 ≤ ‖x‖ ^ 2 + c * ‖y‖ ^ 2` for all `x` and `y`. Inner product spaces
satisfy it with `c = 1`, and `Lᵖ` spaces with `c = p - 1` for `2 ≤ p < ∞`. -/
def IsTwoUniformlySmooth : Prop :=
  ∀ x y : E, (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2 ≤ ‖x‖ ^ 2 + c * ‖y‖ ^ 2

variable {E c}

theorem isTwoUniformlyConvex_iff : IsTwoUniformlyConvex E c ↔
    ∀ x y : E, ‖x‖ ^ 2 + c * ‖y‖ ^ 2 ≤ (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2 := Iff.rfl

theorem isTwoUniformlySmooth_iff : IsTwoUniformlySmooth E c ↔
    ∀ x y : E, (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2 ≤ ‖x‖ ^ 2 + c * ‖y‖ ^ 2 := Iff.rfl

/-- Two-uniform convexity passes to smaller constants. -/
theorem IsTwoUniformlyConvex.mono {c' : ℝ} (h : IsTwoUniformlyConvex E c) (hc : c' ≤ c) :
    IsTwoUniformlyConvex E c' := fun x y ↦ le_trans (by gcongr) (h x y)

/-- Two-uniform smoothness passes to larger constants. -/
theorem IsTwoUniformlySmooth.mono {c' : ℝ} (h : IsTwoUniformlySmooth E c) (hc : c ≤ c') :
    IsTwoUniformlySmooth E c' := fun x y ↦ (h x y).trans (by gcongr)

variable {R F : Type*} [Semiring R] [Module R E] [SeminormedAddCommGroup F] [Module R F]

/-- Two-uniform convexity passes to a space with an isometric linear copy inside a two-uniformly
convex space, with the same constant. -/
theorem IsTwoUniformlyConvex.of_linearIsometry (h : IsTwoUniformlyConvex F c) (f : E →ₗᵢ[R] F) :
    IsTwoUniformlyConvex E c := fun x y ↦ by
  simpa only [← map_add, ← map_sub, f.norm_map] using h (f x) (f y)

/-- Two-uniform smoothness passes to a space with an isometric linear copy inside a two-uniformly
smooth space, with the same constant. -/
theorem IsTwoUniformlySmooth.of_linearIsometry (h : IsTwoUniformlySmooth F c) (f : E →ₗᵢ[R] F) :
    IsTwoUniformlySmooth E c := fun x y ↦ by
  simpa only [← map_add, ← map_sub, f.norm_map] using h (f x) (f y)

end Defs

section InnerProductSpace

variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

include 𝕜 in
/-- An inner product space is two-uniformly convex with constant `1`. -/
theorem isTwoUniformlyConvex_one_of_innerProductSpace : IsTwoUniformlyConvex E 1 := fun x y ↦ by
  have := parallelogram_law_with_norm 𝕜 x y
  simp only [sq]
  linarith

include 𝕜 in
/-- An inner product space is two-uniformly smooth with constant `1`. -/
theorem isTwoUniformlySmooth_one_of_innerProductSpace : IsTwoUniformlySmooth E 1 := fun x y ↦ by
  have := parallelogram_law_with_norm 𝕜 x y
  simp only [sq]
  linarith

end InnerProductSpace

section Moduli

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ}

/-- Two-uniform convexity with constant `c` bounds the modulus of convexity below:
`1 - √(1 - c ε ^ 2 / 4) ≤ δ(ε)` for `0 ≤ ε`. For inner product spaces, where `c = 1`, this is the
exact value of the modulus at `ε ≤ 2` in dimension at least two. -/
theorem IsTwoUniformlyConvex.one_sub_sqrt_le_modulusOfConvexity (h : IsTwoUniformlyConvex E c)
    {ε : ℝ} (hε : 0 ≤ ε) : 1 - √(1 - c * ε ^ 2 / 4) ≤ modulusOfConvexity E ε := by
  rcases lt_or_ge c 0 with hc | hc
  · -- For a negative constant the left side is not positive.
    have : 1 ≤ √(1 - c * ε ^ 2 / 4) := (Real.le_sqrt' one_pos).2 (by nlinarith [sq_nonneg ε])
    linarith [modulusOfConvexity_nonneg E ε]
  refine (le_modulusOfConvexity_iff E).2
    ⟨by linarith [Real.sqrt_nonneg (1 - c * ε ^ 2 / 4)], fun x y hx hy hxy ↦ ?_⟩
  -- Apply the inequality to the midpoint and the half difference of `x` and `y`.
  have hm := h ((2⁻¹ : ℝ) • (x + y)) ((2⁻¹ : ℝ) • (x - y))
  rw [show (2⁻¹ : ℝ) • (x + y) + (2⁻¹ : ℝ) • (x - y) = x by module,
    show (2⁻¹ : ℝ) • (x + y) - (2⁻¹ : ℝ) • (x - y) = y by module, norm_smul, norm_smul,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹)] at hm
  have hsq : (‖x + y‖ / 2) ^ 2 ≤ 1 - c * ε ^ 2 / 4 := by
    have hε' : ε ^ 2 ≤ ‖x - y‖ ^ 2 := pow_le_pow_left₀ hε hxy 2
    have hx' : ‖x‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg x) hx
    have hy' : ‖y‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg y) hy
    nlinarith [mul_le_mul_of_nonneg_left hε' hc]
  have := Real.abs_le_sqrt hsq
  rw [abs_of_nonneg (by positivity)] at this
  linarith

/-- **Quadratic modulus of convexity.** Two-uniform convexity with constant `c ≤ 1` gives
`c ε ^ 2 / 8 ≤ δ(ε)` for `0 ≤ ε ≤ 2`. -/
theorem IsTwoUniformlyConvex.mul_sq_div_eight_le_modulusOfConvexity
    (h : IsTwoUniformlyConvex E c) (hc : c ≤ 1) {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₂ : ε ≤ 2) :
    c * ε ^ 2 / 8 ≤ modulusOfConvexity E ε := by
  refine le_trans ?_ (h.one_sub_sqrt_le_modulusOfConvexity hε₀)
  have ha : c * ε ^ 2 / 4 ≤ 1 := by nlinarith [sq_nonneg ε]
  have : √(1 - c * ε ^ 2 / 4) ≤ 1 - c * ε ^ 2 / 8 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith [sq_nonneg (c * ε ^ 2)]
  linarith

/-- A real seminormed space that is two-uniformly convex with a positive constant is uniformly
convex. -/
theorem IsTwoUniformlyConvex.uniformConvexSpace (h : IsTwoUniformlyConvex E c) (hc : 0 < c) :
    UniformConvexSpace E :=
  (uniformConvexSpace_iff_modulusOfConvexity_pos E).2 fun ε hε ↦ by
    refine lt_of_lt_of_le ?_ (h.one_sub_sqrt_le_modulusOfConvexity hε.le)
    have : √(1 - c * ε ^ 2 / 4) < 1 := by
      rw [Real.sqrt_lt' one_pos]
      nlinarith [mul_pos hc (pow_pos hε 2)]
    linarith

/-- Two-uniform smoothness with constant `0 ≤ c` bounds the modulus of smoothness above:
`ρ(t) ≤ √(1 + c t ^ 2) - 1`. -/
theorem IsTwoUniformlySmooth.modulusOfSmoothness_le_sqrt_sub_one (h : IsTwoUniformlySmooth E c)
    (hc : 0 ≤ c) (t : ℝ) : modulusOfSmoothness E t ≤ √(1 + c * t ^ 2) - 1 := by
  have h₁ : 1 ≤ √(1 + c * t ^ 2) := (Real.le_sqrt' one_pos).2 (by nlinarith [sq_nonneg t])
  refine (modulusOfSmoothness_le_iff E).2 ⟨by linarith, fun x y hx hy ↦ ?_⟩
  have hs := h x (t • y)
  rw [norm_smul, Real.norm_eq_abs, hx, hy, mul_one, sq_abs, one_pow] at hs
  have hsq : ((‖x + t • y‖ + ‖x - t • y‖) / 2) ^ 2 ≤ 1 + c * t ^ 2 := by
    nlinarith [sq_nonneg (‖x + t • y‖ - ‖x - t • y‖)]
  have := Real.abs_le_sqrt hsq
  rw [abs_of_nonneg (by positivity)] at this
  linarith

/-- **Quadratic modulus of smoothness.** Two-uniform smoothness with constant `0 ≤ c` gives
`ρ(t) ≤ c t ^ 2 / 2`. -/
theorem IsTwoUniformlySmooth.modulusOfSmoothness_le_mul_sq_div_two (h : IsTwoUniformlySmooth E c)
    (hc : 0 ≤ c) (t : ℝ) : modulusOfSmoothness E t ≤ c * t ^ 2 / 2 := by
  refine (h.modulusOfSmoothness_le_sqrt_sub_one hc t).trans ?_
  have : √(1 + c * t ^ 2) ≤ 1 + c * t ^ 2 / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg (c * t ^ 2)]
  linarith

/-- **Uniform smoothness.** In a two-uniformly smooth space, `ρ(t) / t → 0` as `t → 0⁺`. -/
theorem IsTwoUniformlySmooth.tendsto_modulusOfSmoothness_div (h : IsTwoUniformlySmooth E c) :
    Tendsto (fun t ↦ modulusOfSmoothness E t / t) (𝓝[>] 0) (𝓝 0) := by
  -- A larger constant is allowed, so we may assume `0 ≤ c`.
  have h' := h.mono (le_max_left c 0)
  have hup : Tendsto (fun t : ℝ ↦ max c 0 * t / 2) (𝓝[>] 0) (𝓝 0) := by
    have : Continuous fun t : ℝ ↦ max c 0 * t / 2 := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact div_nonneg (modulusOfSmoothness_nonneg E t) ht.le
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [div_le_iff₀ ht]
    have := h'.modulusOfSmoothness_le_mul_sq_div_two (le_max_right c 0) t
    nlinarith

end Moduli

section Duality

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {c : ℝ}

/-- The scaled Fenchel–Young inequality `2 re (f x) ≤ ‖f‖ ^ 2 / c + c ‖x‖ ^ 2` for `0 < c`. -/
private theorem two_mul_re_apply_le (f : StrongDual 𝕜 E) (x : E) (hc : 0 < c) :
    2 * re (f x) ≤ ‖f‖ ^ 2 / c + c * ‖x‖ ^ 2 := by
  have h₁ : re (f x) ≤ ‖f‖ * ‖x‖ := (re_le_norm _).trans (f.le_opNorm x)
  have h₂ : 0 ≤ (‖f‖ - c * ‖x‖) ^ 2 / c := by positivity
  have h₃ : (‖f‖ - c * ‖x‖) ^ 2 / c = ‖f‖ ^ 2 / c - 2 * (‖f‖ * ‖x‖) + c * ‖x‖ ^ 2 := by
    field_simp
    ring
  linarith

/-- The scaled Fenchel–Young inequality is attained at every vector: a functional in the duality
set of `x`, rescaled by `c`, realizes it. -/
private theorem exists_le_two_mul_re_apply_sub (x : E) (hc : 0 < c) :
    ∃ f : StrongDual 𝕜 E, c * ‖x‖ ^ 2 ≤ 2 * re (f x) - ‖f‖ ^ 2 / c := by
  obtain ⟨J, hJ⟩ := dualitySet_nonempty 𝕜 x
  obtain ⟨hJx, hJ⟩ := mem_dualitySet_iff.1 hJ
  refine ⟨(c : 𝕜) • J, le_of_eq ?_⟩
  rw [smul_apply, hJx, smul_eq_mul, ← ofReal_pow, ← ofReal_mul, ofReal_re, norm_smul, norm_ofReal,
    abs_of_pos hc, hJ]
  field_simp
  ring

/-- The scaled Fenchel–Young inequality determines the dual norm: if
`2 re (f x) - c ‖x‖ ^ 2 ≤ B` for every `x`, then `‖f‖ ^ 2 / c ≤ B`. -/
private theorem sq_norm_div_le_of_forall {f : StrongDual 𝕜 E} {B : ℝ} (hc : 0 < c)
    (h : ∀ x, 2 * re (f x) - c * ‖x‖ ^ 2 ≤ B) : ‖f‖ ^ 2 / c ≤ B := by
  have hB : 0 ≤ B := by simpa using h 0
  by_contra! hlt
  -- Otherwise `r = √(c B) < ‖f‖`, and a vector on which `re f` exceeds `r ‖x‖`, suitably
  -- rescaled, violates the bound.
  have hf : 0 < ‖f‖ := (norm_nonneg f).lt_of_ne fun h₀ ↦ by
    rw [← h₀] at hlt
    simp at hlt
    linarith
  have hr : √(c * B) < ‖f‖ := by
    rw [Real.sqrt_lt' hf]
    rwa [lt_div_iff₀ hc, mul_comm] at hlt
  obtain ⟨x, hx⟩ := f.exists_mul_norm_lt_re_apply (Real.sqrt_nonneg _) hr
  have hfx : 0 < re (f x) := lt_of_le_of_lt (by positivity) hx
  have hx₀ : 0 < ‖x‖ := (norm_nonneg x).lt_of_ne fun h₀ ↦ by
    have := (re_le_norm (f x)).trans (f.le_opNorm x)
    rw [← h₀, mul_zero] at this
    linarith
  have hcx : 0 < c * ‖x‖ ^ 2 := mul_pos hc (pow_pos hx₀ 2)
  set s : ℝ := re (f x) / (c * ‖x‖ ^ 2)
  have hs := h ((s : 𝕜) • x)
  rw [map_smul, smul_eq_mul, re_ofReal_mul, norm_smul, norm_ofReal,
    abs_of_pos (div_pos hfx hcx)] at hs
  have e : 2 * (s * re (f x)) - c * (s * ‖x‖) ^ 2 = re (f x) ^ 2 / (c * ‖x‖ ^ 2) := by
    have := hx₀.ne'
    simp only [s]
    field_simp
    ring
  rw [e, div_le_iff₀ hcx] at hs
  have h₁ : (√(c * B) * ‖x‖) ^ 2 < re (f x) ^ 2 := pow_lt_pow_left₀ hx (by positivity) two_ne_zero
  rw [mul_pow, Real.sq_sqrt (by positivity)] at h₁
  nlinarith

private theorem re_apply_add_add_re_apply_sub (f g : StrongDual 𝕜 E) (x y : E) :
    re ((f + g) (x + y)) + re ((f - g) (x - y)) = 2 * re (f x) + 2 * re (g y) := by
  simp only [add_apply, sub_apply, map_add, map_sub]
  ring

variable (𝕜) in
/-- The dual of a two-uniformly convex space with constant `0 < c` is two-uniformly smooth with
constant `c⁻¹`. -/
theorem IsTwoUniformlyConvex.isTwoUniformlySmooth_strongDual (h : IsTwoUniformlyConvex E c)
    (hc : 0 < c) : IsTwoUniformlySmooth (StrongDual 𝕜 E) c⁻¹ := by
  intro f g
  -- The inequality between the two suprema defining `‖f + g‖ ^ 2` and `‖f - g‖ ^ 2`.
  have core (x y : E) : 2 * re ((f + g) x) - 1 * ‖x‖ ^ 2 + (2 * re ((f - g) y) - 1 * ‖y‖ ^ 2) ≤
      2 * ‖f‖ ^ 2 + 2 * (‖g‖ ^ 2 / c) := by
    have hconv := h ((2⁻¹ : 𝕜) • (x + y)) ((2⁻¹ : 𝕜) • (x - y))
    rw [show (2⁻¹ : 𝕜) • (x + y) + (2⁻¹ : 𝕜) • (x - y) = x by module,
      show (2⁻¹ : 𝕜) • (x + y) - (2⁻¹ : 𝕜) • (x - y) = y by module] at hconv
    have h₁ := two_mul_re_apply_le f ((2⁻¹ : 𝕜) • (x + y)) one_pos
    have h₂ := two_mul_re_apply_le g ((2⁻¹ : 𝕜) • (x - y)) hc
    have hre := re_apply_add_add_re_apply_sub f g ((2⁻¹ : 𝕜) • (x + y)) ((2⁻¹ : 𝕜) • (x - y))
    rw [show (2⁻¹ : 𝕜) • (x + y) + (2⁻¹ : 𝕜) • (x - y) = x by module,
      show (2⁻¹ : 𝕜) • (x + y) - (2⁻¹ : 𝕜) • (x - y) = y by module] at hre
    rw [div_one] at h₁
    linarith
  have hsub (x : E) : ‖f - g‖ ^ 2 / 1 ≤
      2 * ‖f‖ ^ 2 + 2 * (‖g‖ ^ 2 / c) - (2 * re ((f + g) x) - 1 * ‖x‖ ^ 2) :=
    sq_norm_div_le_of_forall one_pos fun y ↦ by linarith [core x y]
  have hadd : ‖f + g‖ ^ 2 / 1 ≤ 2 * ‖f‖ ^ 2 + 2 * (‖g‖ ^ 2 / c) - ‖f - g‖ ^ 2 / 1 :=
    sq_norm_div_le_of_forall one_pos fun x ↦ by linarith [hsub x]
  rw [div_one, div_one] at hadd
  rw [inv_mul_eq_div]
  linarith

variable (𝕜) in
/-- The dual of a two-uniformly smooth space with constant `0 < c` is two-uniformly convex with
constant `c⁻¹`. -/
theorem IsTwoUniformlySmooth.isTwoUniformlyConvex_strongDual (h : IsTwoUniformlySmooth E c)
    (hc : 0 < c) : IsTwoUniformlyConvex (StrongDual 𝕜 E) c⁻¹ := by
  intro f g
  -- The inequality between the two suprema defining `‖f‖ ^ 2` and `‖g‖ ^ 2 / c`.
  have core (x y : E) : 2 * re (f x) - 1 * ‖x‖ ^ 2 + (2 * re (g y) - c * ‖y‖ ^ 2) ≤
      (‖f + g‖ ^ 2 + ‖f - g‖ ^ 2) / 2 := by
    have h₁ := two_mul_re_apply_le (f + g) (x + y) one_pos
    have h₂ := two_mul_re_apply_le (f - g) (x - y) one_pos
    have hre := re_apply_add_add_re_apply_sub f g x y
    rw [div_one] at h₁ h₂
    linarith [h x y]
  have hf (y : E) : ‖f‖ ^ 2 / 1 ≤ (‖f + g‖ ^ 2 + ‖f - g‖ ^ 2) / 2 - (2 * re (g y) - c * ‖y‖ ^ 2) :=
    sq_norm_div_le_of_forall one_pos fun x ↦ by linarith [core x y]
  have hg : ‖g‖ ^ 2 / c ≤ (‖f + g‖ ^ 2 + ‖f - g‖ ^ 2) / 2 - ‖f‖ ^ 2 / 1 :=
    sq_norm_div_le_of_forall hc fun y ↦ by linarith [hf y]
  rw [div_one] at hg
  rw [inv_mul_eq_div]
  linarith

/-- **Duality of two-uniform convexity and smoothness.** For `0 < c`, the dual of `E` is
two-uniformly smooth with constant `c⁻¹` exactly when `E` is two-uniformly convex with
constant `c`. -/
theorem isTwoUniformlySmooth_strongDual_iff (hc : 0 < c) :
    IsTwoUniformlySmooth (StrongDual 𝕜 E) c⁻¹ ↔ IsTwoUniformlyConvex E c := by
  refine ⟨fun h x y ↦ ?_, fun h ↦ h.isTwoUniformlySmooth_strongDual 𝕜 hc⟩
  obtain ⟨f, hf⟩ := exists_le_two_mul_re_apply_sub (𝕜 := 𝕜) x one_pos
  obtain ⟨g, hg⟩ := exists_le_two_mul_re_apply_sub (𝕜 := 𝕜) y hc
  have h₁ := two_mul_re_apply_le (f + g) (x + y) one_pos
  have h₂ := two_mul_re_apply_le (f - g) (x - y) one_pos
  have hre := re_apply_add_add_re_apply_sub f g x y
  have hs := h f g
  rw [inv_mul_eq_div] at hs
  rw [div_one] at hf h₁ h₂
  linarith

/-- **Duality of two-uniform smoothness and convexity.** For `0 < c`, the dual of `E` is
two-uniformly convex with constant `c⁻¹` exactly when `E` is two-uniformly smooth with
constant `c`. -/
theorem isTwoUniformlyConvex_strongDual_iff (hc : 0 < c) :
    IsTwoUniformlyConvex (StrongDual 𝕜 E) c⁻¹ ↔ IsTwoUniformlySmooth E c := by
  refine ⟨fun h x y ↦ ?_, fun h ↦ h.isTwoUniformlyConvex_strongDual 𝕜 hc⟩
  obtain ⟨F, hF⟩ := exists_le_two_mul_re_apply_sub (𝕜 := 𝕜) (x + y) one_pos
  obtain ⟨G, hG⟩ := exists_le_two_mul_re_apply_sub (𝕜 := 𝕜) (x - y) one_pos
  -- Write `F = f + g` and `G = f - g`.
  have hfg := h ((2⁻¹ : 𝕜) • (F + G)) ((2⁻¹ : 𝕜) • (F - G))
  have h₁ := two_mul_re_apply_le ((2⁻¹ : 𝕜) • (F + G)) x one_pos
  have h₂ := two_mul_re_apply_le ((2⁻¹ : 𝕜) • (F - G)) y hc
  have hre := re_apply_add_add_re_apply_sub ((2⁻¹ : 𝕜) • (F + G)) ((2⁻¹ : 𝕜) • (F - G)) x y
  rw [show (2⁻¹ : 𝕜) • (F + G) + (2⁻¹ : 𝕜) • (F - G) = F by module,
    show (2⁻¹ : 𝕜) • (F + G) - (2⁻¹ : 𝕜) • (F - G) = G by module] at hfg hre
  rw [inv_mul_eq_div] at hfg
  rw [div_one] at hF hG h₁
  linarith

end Duality

end TauCeti
