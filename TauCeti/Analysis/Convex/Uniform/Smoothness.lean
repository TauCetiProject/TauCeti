/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import TauCeti.Analysis.Convex.Uniform.Modulus
import Mathlib.Tactic.Module
import TauCeti.Analysis.Normed.Module.Dual.Basic

/-!
# The modulus of smoothness

The modulus of smoothness of a real normed space `E` is

`ρ(t) = sup {(‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 | ‖x‖ = ‖y‖ = 1}`,

with value zero when `E` has no unit vector. It measures how far the unit sphere is from being
flat at scale `t`, and `E` is *uniformly smooth* when `ρ(t) / t → 0` as `t → 0⁺`. Together with
the modulus of convexity `TauCeti.modulusOfConvexity` it quantifies the geometry of the unit ball,
and the two moduli are dual to each other: by **Lindenstrauss's formula**, for a nontrivial `E`
and `0 ≤ t`,

`ρ_{E*}(t) = sup {t * ε / 2 - δ_E(ε) | 0 ≤ ε ≤ 2}`.

## Main declarations

* `TauCeti.modulusOfSmoothness`: the modulus of smoothness. It is nonnegative, even, convex,
  nondecreasing on `[0, ∞)` and at most `|t|`, it vanishes at `0` and in the zero space, and it can
  only grow when passing to a space containing an isometric copy.
* `TauCeti.modulusOfSmoothness_le_sqrt_sub_one`, `TauCeti.modulusOfSmoothness_le_mul_sq_div_two`:
  a space satisfying the two-point inequality
  `(‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2 ≤ ‖x‖ ^ 2 + C * ‖y‖ ^ 2` has `ρ(t) ≤ √(1 + C t ^ 2) - 1`,
  hence `ρ(t) ≤ C t ^ 2 / 2`. For `Lᵖ`, `2 ≤ p < ∞`, the reversed Ball–Carlen–Lieb inequality
  gives this inequality with `C = p - 1`.
* `TauCeti.modulusOfSmoothness_eq_of_inner_eq_zero`,
  `TauCeti.modulusOfConvexity_eq_of_inner_eq_zero`: in a real inner product space with two
  orthogonal unit vectors, `ρ(t) = √(1 + t ^ 2) - 1` and `δ(ε) = 1 - √(1 - ε ^ 2 / 4)` for
  `0 ≤ ε`.
* `TauCeti.UniformSmoothSpace`: uniformly smooth spaces. A modulus of power type,
  `ρ(t) ≤ C * t ^ q` with `1 < q`, makes a space uniformly smooth
  (`TauCeti.UniformSmoothSpace.of_modulusOfSmoothness_le_mul_rpow`); real inner product spaces and
  the dual of a uniformly convex space are uniformly smooth.
* `TauCeti.modulusOfSmoothness_strongDual_le`, `TauCeti.le_modulusOfSmoothness_strongDual`,
  `TauCeti.modulusOfSmoothness_strongDual_eq_iSup`: Lindenstrauss's formula.
* `TauCeti.modulusOfSmoothness_strongDual_le_sq_div`: a quadratic lower bound `c ε ^ 2 ≤ δ_E(ε)`
  gives the quadratic upper bound `ρ_{E*}(t) ≤ t ^ 2 / (16 c)`.

## References

* J. Lindenstrauss, *On the modulus of smoothness and divergent series in Banach spaces*,
  Michigan Math. J. 10 (1963), 241–252.
* J. Lindenstrauss and L. Tzafriri, *Classical Banach Spaces II*, Springer, 1979, §1.e.
* K. Ball, E. A. Carlen and E. H. Lieb, *Sharp uniform convexity and smoothness inequalities for
  trace norms*, Invent. Math. 115 (1994), 463–482.
-/

public section

open Set Filter Topology

namespace TauCeti

variable (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The modulus of smoothness `ρ(t) = sup {(‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 | ‖x‖ = ‖y‖ = 1}`,
with value zero if there is no unit vector. -/
noncomputable def modulusOfSmoothness (t : ℝ) : ℝ :=
  sSup (insert 0 {r | ∃ x y : E, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
    r = (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1})

/-- The defining supremum of averaged two-sided norms, including the zero-space convention. -/
theorem modulusOfSmoothness_def (t : ℝ) :
    modulusOfSmoothness E t =
      sSup (insert 0 {r | ∃ x y : E, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
        r = (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1}) := (rfl)

variable {E} in
private theorem norm_add_smul_add_norm_sub_smul_le {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (t : ℝ) : (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 ≤ |t| := by
  have h₁ := norm_add_le x (t • y)
  have h₂ := norm_sub_le x (t • y)
  rw [norm_smul, Real.norm_eq_abs, hx, hy, mul_one] at h₁ h₂
  linarith

private theorem smoothness_bddAbove (t : ℝ) :
    BddAbove (insert 0 {r | ∃ x y : E, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      r = (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1}) := by
  refine ⟨|t|, ?_⟩
  rintro r (rfl | ⟨x, y, hx, hy, rfl⟩)
  · exact abs_nonneg t
  · exact norm_add_smul_add_norm_sub_smul_le hx hy t

/-- A number bounds the modulus of smoothness exactly when it is nonnegative and bounds the
averaged two-sided norm of every pair of unit vectors. -/
theorem modulusOfSmoothness_le_iff {t a : ℝ} :
    modulusOfSmoothness E t ≤ a ↔ 0 ≤ a ∧
      ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 ≤ a := by
  rw [modulusOfSmoothness, csSup_le_iff (smoothness_bddAbove E t) (insert_nonempty _ _)]
  constructor
  · intro h
    exact ⟨h _ (mem_insert _ _), fun x y hx hy ↦
      h _ (mem_insert_of_mem _ ⟨x, y, hx, hy, rfl⟩)⟩
  · rintro ⟨ha, h⟩ r (rfl | ⟨x, y, hx, hy, rfl⟩)
    · exact ha
    · exact h x y hx hy

/-- The modulus of smoothness bounds the averaged two-sided norm of each pair of unit vectors. -/
theorem le_modulusOfSmoothness (t : ℝ) {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 ≤ modulusOfSmoothness E t :=
  le_csSup (smoothness_bddAbove E t) (mem_insert_of_mem _ ⟨x, y, hx, hy, rfl⟩)

/-- The modulus of smoothness is nonnegative. -/
theorem modulusOfSmoothness_nonneg (t : ℝ) : 0 ≤ modulusOfSmoothness E t :=
  le_csSup (smoothness_bddAbove E t) (mem_insert _ _)

/-- The modulus of smoothness at `t` is at most `|t|`. -/
theorem modulusOfSmoothness_le_abs (t : ℝ) : modulusOfSmoothness E t ≤ |t| :=
  (modulusOfSmoothness_le_iff E).2
    ⟨abs_nonneg t, fun _ _ hx hy ↦ norm_add_smul_add_norm_sub_smul_le hx hy t⟩

/-- The modulus of smoothness is even. -/
@[simp]
theorem modulusOfSmoothness_neg (t : ℝ) : modulusOfSmoothness E (-t) = modulusOfSmoothness E t := by
  suffices h : ∀ s, modulusOfSmoothness E (-s) ≤ modulusOfSmoothness E s by
    exact le_antisymm (h t) (by simpa using h (-t))
  refine fun s ↦ (modulusOfSmoothness_le_iff E).2
    ⟨modulusOfSmoothness_nonneg E s, fun x y hx hy ↦ ?_⟩
  rw [neg_smul, ← sub_eq_add_neg, sub_neg_eq_add, add_comm ‖x - s • y‖]
  exact le_modulusOfSmoothness E s hx hy

/-- The modulus of smoothness vanishes at `0`. -/
@[simp]
theorem modulusOfSmoothness_zero : modulusOfSmoothness E 0 = 0 :=
  le_antisymm ((modulusOfSmoothness_le_iff E).2 ⟨le_rfl, fun x _ hx _ ↦ by simp [hx]⟩)
    (modulusOfSmoothness_nonneg E 0)

/-- In the zero space, the modulus of smoothness vanishes identically. -/
@[simp]
theorem modulusOfSmoothness_eq_zero_of_subsingleton [Subsingleton E] (t : ℝ) :
    modulusOfSmoothness E t = 0 := by
  refine le_antisymm ((modulusOfSmoothness_le_iff E).2 ⟨le_rfl, fun x _ hx _ ↦ ?_⟩)
    (modulusOfSmoothness_nonneg E t)
  simp [Subsingleton.elim x 0] at hx

/-- The modulus of smoothness is a convex function. -/
theorem convexOn_modulusOfSmoothness : ConvexOn ℝ univ (modulusOfSmoothness E) := by
  refine ⟨convex_univ, fun s _ t _ a b ha hb hab ↦ ?_⟩
  simp only [smul_eq_mul]
  refine (modulusOfSmoothness_le_iff E).2 ⟨by
    have := modulusOfSmoothness_nonneg E s
    have := modulusOfSmoothness_nonneg E t
    positivity, fun x y hx hy ↦ ?_⟩
  -- Split `x + (a u + b v) y` as the convex combination of `x + u y` and `x + v y`.
  have key : ∀ u v : ℝ, ‖x + (a * u + b * v) • y‖ ≤ a * ‖x + u • y‖ + b * ‖x + v • y‖ :=
    fun u v ↦ by
      obtain rfl : a = 1 - b := by linarith
      calc ‖x + ((1 - b) * u + b * v) • y‖
          = ‖(1 - b) • (x + u • y) + b • (x + v • y)‖ := by congr 1; module
        _ ≤ ‖(1 - b) • (x + u • y)‖ + ‖b • (x + v • y)‖ := norm_add_le _ _
        _ = (1 - b) * ‖x + u • y‖ + b * ‖x + v • y‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have h₁ := key s t
  have h₂ := key (-s) (-t)
  rw [show a * -s + b * -t = -(a * s + b * t) by ring] at h₂
  simp only [neg_smul, ← sub_eq_add_neg] at h₂
  have hs := mul_le_mul_of_nonneg_left (le_modulusOfSmoothness E s hx hy) ha
  have ht := mul_le_mul_of_nonneg_left (le_modulusOfSmoothness E t hx hy) hb
  nlinarith

/-- The modulus of smoothness is nondecreasing on `[0, ∞)`. -/
theorem monotoneOn_modulusOfSmoothness : MonotoneOn (modulusOfSmoothness E) (Ici 0) := by
  intro s hs t ht hst
  rcases (mem_Ici.1 ht).eq_or_lt with rfl | ht
  · rw [le_antisymm hst hs]
  -- Write `s` as the convex combination `(s / t) t + (1 - s / t) 0`.
  have hst' : s / t ≤ 1 := div_le_one_of_le₀ hst ht.le
  have h := (convexOn_modulusOfSmoothness E).2 (mem_univ t) (mem_univ 0)
    (div_nonneg hs ht.le) (sub_nonneg.2 hst') (add_sub_cancel _ _)
  simp only [smul_eq_mul, mul_zero, add_zero, modulusOfSmoothness_zero,
    div_mul_cancel₀ s ht.ne'] at h
  exact h.trans (mul_le_of_le_one_left (modulusOfSmoothness_nonneg E t) hst')

/-! ### Quadratic bounds from two-point inequalities -/

/-- The two-point inequality `(‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2 ≤ ‖x‖ ^ 2 + C * ‖y‖ ^ 2` bounds the
modulus of smoothness by `√(1 + C * t ^ 2) - 1`. -/
theorem modulusOfSmoothness_le_sqrt_sub_one {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y : E, (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2 ≤ ‖x‖ ^ 2 + C * ‖y‖ ^ 2) (t : ℝ) :
    modulusOfSmoothness E t ≤ √(1 + C * t ^ 2) - 1 := by
  refine (modulusOfSmoothness_le_iff E).2
    ⟨sub_nonneg.2 (Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg t])), fun x y hx hy ↦ ?_⟩
  have hxy := h x (t • y)
  rw [norm_smul, Real.norm_eq_abs, hx, hy, mul_one, sq_abs, one_pow] at hxy
  have : (‖x + t • y‖ + ‖x - t • y‖) / 2 ≤ √(1 + C * t ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (‖x + t • y‖ - ‖x - t • y‖)])
  linarith

/-- The two-point inequality `(‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2 ≤ ‖x‖ ^ 2 + C * ‖y‖ ^ 2` bounds the
modulus of smoothness by the quadratic `C * t ^ 2 / 2`. -/
theorem modulusOfSmoothness_le_mul_sq_div_two {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y : E, (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 2 ≤ ‖x‖ ^ 2 + C * ‖y‖ ^ 2) (t : ℝ) :
    modulusOfSmoothness E t ≤ C * t ^ 2 / 2 := by
  refine (modulusOfSmoothness_le_sqrt_sub_one E hC h t).trans ?_
  have : √(1 + C * t ^ 2) ≤ 1 + C * t ^ 2 / 2 :=
    Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [sq_nonneg (C * t ^ 2)]⟩
  linarith

/-! ### Uniformly smooth spaces -/

/-- A real normed space is *uniformly smooth* if its modulus of smoothness satisfies
`ρ(t) / t → 0` as `t → 0⁺`. -/
class UniformSmoothSpace : Prop where
  tendsto_modulusOfSmoothness_div :
    Tendsto (fun t ↦ modulusOfSmoothness E t / t) (𝓝[>] 0) (𝓝 0)

/-- A space whose modulus of smoothness is bounded by a power `C * t ^ q` with `1 < q` is uniformly
smooth. -/
theorem UniformSmoothSpace.of_modulusOfSmoothness_le_mul_rpow {C q : ℝ} (hq : 1 < q)
    (h : ∀ t, 0 < t → modulusOfSmoothness E t ≤ C * t ^ q) : UniformSmoothSpace E := by
  have hC : Tendsto (fun t : ℝ ↦ C * t ^ (q - 1)) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 (q - 1) (Or.inr (by linarith))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))).const_mul C
    rwa [Real.zero_rpow (by linarith), mul_zero] at this
  refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC ?_ ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact div_nonneg (modulusOfSmoothness_nonneg E t) ht.le
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [Real.rpow_sub_one ht.ne', mul_div_assoc']
    exact div_le_div_of_nonneg_right (h t ht) ht.le

end TauCeti

namespace LinearIsometry

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F]

/-- Passing to a space containing an isometric linear copy can only increase the modulus of
smoothness. -/
theorem modulusOfSmoothness_le (f : E →ₗᵢ[ℝ] F) (t : ℝ) :
    TauCeti.modulusOfSmoothness E t ≤ TauCeti.modulusOfSmoothness F t := by
  refine (TauCeti.modulusOfSmoothness_le_iff E).2
    ⟨TauCeti.modulusOfSmoothness_nonneg F t, fun x y hx hy ↦ ?_⟩
  simpa only [← map_smul, ← map_add, ← map_sub, f.norm_map] using
    TauCeti.le_modulusOfSmoothness F t (x := f x) (y := f y) (by simpa using hx)
      (by simpa using hy)

end LinearIsometry

namespace LinearIsometryEquiv

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F]

/-- Linearly isometric spaces have the same modulus of smoothness. -/
theorem modulusOfSmoothness_eq (f : E ≃ₗᵢ[ℝ] F) (t : ℝ) :
    TauCeti.modulusOfSmoothness E t = TauCeti.modulusOfSmoothness F t :=
  le_antisymm (f.toLinearIsometry.modulusOfSmoothness_le t)
    (f.symm.toLinearIsometry.modulusOfSmoothness_le t)

end LinearIsometryEquiv

namespace TauCeti

/-! ### Inner product spaces -/

section InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- In a real inner product space, `ρ(t) = √(1 + t ^ 2) - 1` as soon as there are two orthogonal
unit vectors. -/
theorem modulusOfSmoothness_eq_of_inner_eq_zero {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) (t : ℝ) : modulusOfSmoothness F t = √(1 + t ^ 2) - 1 := by
  refine le_antisymm ?_ ?_
  · simpa using modulusOfSmoothness_le_sqrt_sub_one F zero_le_one
      (fun u v ↦ by linarith [parallelogram_law_with_norm ℝ u v]) t
  · -- By Pythagoras, `‖x + s • y‖ = √(1 + s ^ 2)` for every real `s`.
    have key : ∀ s : ℝ, ‖x + s • y‖ = √(1 + s ^ 2) := fun s ↦ by
      have hxy' : inner ℝ x (s • y) = 0 := by rw [real_inner_smul_right, hxy, mul_zero]
      rw [← Real.sqrt_sq (norm_nonneg _), sq, norm_add_sq_eq_norm_sq_add_norm_sq_real hxy',
        norm_smul, hx, hy, Real.norm_eq_abs, mul_one, mul_one, abs_mul_abs_self, sq]
    have h := le_modulusOfSmoothness F t hx hy
    rw [key, sub_eq_add_neg x, ← neg_smul, key, neg_sq] at h
    linarith

/-- In a real inner product space, `δ(ε) = 1 - √(1 - ε ^ 2 / 4)` for `0 ≤ ε` as soon as there are
two orthogonal unit vectors. -/
theorem modulusOfConvexity_eq_of_inner_eq_zero {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) {ε : ℝ} (hε₀ : 0 ≤ ε) :
    modulusOfConvexity F ε = 1 - √(1 - ε ^ 2 / 4) := by
  have hpar : ∀ u v : F, ‖u‖ ^ 2 + 1 * ‖v‖ ^ 2 ≤ (‖u + v‖ ^ 2 + ‖u - v‖ ^ 2) / 2 := fun u v ↦ by
    linarith [parallelogram_law_with_norm ℝ u v]
  refine le_antisymm ?_ (by simpa using one_sub_sqrt_le_modulusOfConvexity F hpar hε₀)
  rcases lt_or_ge 2 ε with hε | hε
  · rw [modulusOfConvexity_eq_one_of_two_lt F hε, Real.sqrt_eq_zero_of_nonpos (by nlinarith),
      sub_zero]
  -- The pair `a x ± (ε / 2) y` with `a = √(1 - ε ^ 2 / 4)` attains the bound.
  set a := √(1 - ε ^ 2 / 4)
  have ha : a ^ 2 = 1 - ε ^ 2 / 4 := Real.sq_sqrt (by nlinarith)
  have ha₀ : 0 ≤ a := Real.sqrt_nonneg _
  have horth : inner ℝ (a • x) ((ε / 2) • y) = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, hxy, mul_zero, mul_zero]
  have hnorm : ‖a • x‖ * ‖a • x‖ + ‖(ε / 2) • y‖ * ‖(ε / 2) • y‖ = 1 := by
    rw [norm_smul, norm_smul, hx, hy, Real.norm_of_nonneg ha₀, Real.norm_of_nonneg (by linarith)]
    nlinarith
  have hu : ‖a • x + (ε / 2) • y‖ ≤ 1 := by
    rw [← abs_norm, ← abs_one, ← sq_le_sq, sq, sq,
      norm_add_sq_eq_norm_sq_add_norm_sq_real horth, hnorm, one_mul]
  have hv : ‖a • x - (ε / 2) • y‖ ≤ 1 := by
    rw [← abs_norm, ← abs_one, ← sq_le_sq, sq, sq,
      norm_sub_sq_eq_norm_sq_add_norm_sq_real horth, hnorm, one_mul]
  have hsub : a • x + (ε / 2) • y - (a • x - (ε / 2) • y) = ε • y := by module
  have hadd : a • x + (ε / 2) • y + (a • x - (ε / 2) • y) = (2 * a) • x := by module
  have h := modulusOfConvexity_le F hu hv
    (by rw [hsub, norm_smul, hy, Real.norm_of_nonneg hε₀, mul_one])
  rw [hadd, norm_smul, hx, Real.norm_of_nonneg (by positivity)] at h
  linarith

/-- A real inner product space is uniformly smooth. -/
instance (priority := 100) InnerProductSpace.toUniformSmoothSpace : UniformSmoothSpace F :=
  UniformSmoothSpace.of_modulusOfSmoothness_le_mul_rpow F (C := 1 / 2) one_lt_two fun t _ ↦ by
    have := modulusOfSmoothness_le_mul_sq_div_two F zero_le_one
      (fun u v ↦ by linarith [parallelogram_law_with_norm ℝ u v]) t
    rw [Real.rpow_two]
    linarith

end InnerProductSpace

/-! ### Lindenstrauss's duality formula -/

section Duality

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- One half of **Lindenstrauss's formula**: for `0 ≤ t`, any nonnegative upper bound of
`t * ε / 2 - δ_E(ε)` over `0 ≤ ε ≤ 2` bounds the modulus of smoothness of the dual at `t`. -/
theorem modulusOfSmoothness_strongDual_le {t a : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a)
    (h : ∀ ε, 0 ≤ ε → ε ≤ 2 → t * ε / 2 - modulusOfConvexity E ε ≤ a) :
    modulusOfSmoothness (StrongDual ℝ E) t ≤ a := by
  refine (modulusOfSmoothness_le_iff _).2 ⟨ha, fun f g hf hg ↦ ?_⟩
  refine le_of_forall_pos_lt_add fun η hη ↦ ?_
  -- Nearly norm `f + t g` and `f - t g` by points `x` and `y` of the unit ball.
  obtain ⟨x, hx, hfx⟩ := (f + t • g).exists_lt_re_apply_of_lt_norm (sub_lt_self _ hη)
  obtain ⟨y, hy, hfy⟩ := (f - t • g).exists_lt_re_apply_of_lt_norm (sub_lt_self _ hη)
  simp only [RCLike.re_to_real, add_apply, sub_apply, smul_apply, smul_eq_mul] at hfx hfy
  -- Their sum is `f (x + y) + t g (x - y) ≤ ‖x + y‖ + t ‖x - y‖`.
  have hf : f (x + y) ≤ ‖x + y‖ := by
    simpa [hf] using (le_abs_self _).trans (f.le_opNorm (x + y))
  have hg : g (x - y) ≤ ‖x - y‖ := by
    simpa [hg] using (le_abs_self _).trans (g.le_opNorm (x - y))
  rw [map_add] at hf
  rw [map_sub] at hg
  have hδ := modulusOfConvexity_le E hx hy (le_refl ‖x - y‖)
  have hε := h ‖x - y‖ (norm_nonneg _) ((norm_sub_le x y).trans (by linarith))
  nlinarith


/-- A quadratic lower bound `c * ε ^ 2 ≤ δ_E(ε)` on `0 ≤ ε ≤ 2` gives the quadratic upper bound
`ρ_{E*}(t) ≤ t ^ 2 / (16 * c)` for the modulus of smoothness of the dual. -/
theorem modulusOfSmoothness_strongDual_le_sq_div {c : ℝ} (hc : 0 < c)
    (h : ∀ ε, 0 ≤ ε → ε ≤ 2 → c * ε ^ 2 ≤ modulusOfConvexity E ε) (t : ℝ) :
    modulusOfSmoothness (StrongDual ℝ E) t ≤ t ^ 2 / (16 * c) := by
  wlog ht : 0 ≤ t generalizing t
  · simpa using this (-t) (by linarith)
  refine modulusOfSmoothness_strongDual_le ht (by positivity) fun ε hε₀ hε ↦ ?_
  have := mul_le_mul_of_nonneg_left (h ε hε₀ hε) (by positivity : (0 : ℝ) ≤ 16 * c)
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (t - 4 * c * ε)]

/-- The dual of a uniformly convex space is uniformly smooth. -/
instance uniformSmoothSpace_strongDual [UniformConvexSpace E] :
    UniformSmoothSpace (StrongDual ℝ E) := by
  refine ⟨tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩⟩
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact ha.trans_le (div_nonneg (modulusOfSmoothness_nonneg _ t) ht.le)
  -- For `0 < t < δ_E(a)`, Lindenstrauss's formula gives `ρ_{E*}(t) ≤ t a / 2`.
  have hd := modulusOfConvexity_pos E ha
  filter_upwards [Ioo_mem_nhdsGT hd] with t ⟨ht, htd⟩
  rw [div_lt_iff₀ ht]
  refine (modulusOfSmoothness_strongDual_le ht.le (a := t * a / 2) (by positivity)
    fun ε _ hε ↦ ?_).trans_lt (by nlinarith [mul_pos ha ht])
  rcases le_total ε a with hεa | hεa
  · nlinarith [modulusOfConvexity_nonneg E ε]
  · nlinarith [monotone_modulusOfConvexity E hεa]

end Duality

section NormedDuality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

/-- The other half of **Lindenstrauss's formula**: for `0 ≤ t` and `ε ≤ 2`, the modulus of
smoothness of the dual at `t` is at least `t * ε / 2 - δ_E(ε)`. -/
theorem le_modulusOfSmoothness_strongDual {t ε : ℝ} (ht : 0 ≤ t) (hε : ε ≤ 2) :
    t * ε / 2 - modulusOfConvexity E ε ≤ modulusOfSmoothness (StrongDual ℝ E) t := by
  -- Norming `x + y` and `x - y` by unit functionals `f` and `g` bounds the midpoint deficit of
  -- each admissible pair `x, y` below through `(f + t g) x + (f - t g) y`.
  have pair : ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ε ≤ ‖x - y‖ →
      t * ε / 2 - modulusOfSmoothness (StrongDual ℝ E) t ≤ 1 - ‖x + y‖ / 2 := by
    intro x y hx hy hxy
    obtain ⟨f, hf, hfxy⟩ := exists_dual_vector' ℝ (x + y)
    obtain ⟨g, hg, hgxy⟩ := exists_dual_vector' ℝ (x - y)
    have h := le_modulusOfSmoothness (StrongDual ℝ E) t hf hg
    have h₁ : (f + t • g) x ≤ ‖f + t • g‖ :=
      (le_abs_self _).trans <| ((f + t • g).le_opNorm x).trans <|
        mul_le_of_le_one_right (norm_nonneg _) hx
    have h₂ : (f - t • g) y ≤ ‖f - t • g‖ :=
      (le_abs_self _).trans <| ((f - t • g).le_opNorm y).trans <|
        mul_le_of_le_one_right (norm_nonneg _) hy
    simp only [add_apply, sub_apply, smul_apply, smul_eq_mul] at h₁ h₂
    simp only [map_add, map_sub, RCLike.ofReal_real_eq_id, id_eq] at hfxy hgxy
    nlinarith [mul_le_mul_of_nonneg_left hxy ht]
  -- The antipodal pair `x, -x` shows that the bound is at most one.
  obtain ⟨x, hx⟩ := exists_norm_eq E zero_le_one
  have hx₂ : ε ≤ ‖x - -x‖ := by
    rwa [sub_neg_eq_add, ← two_smul ℝ x, norm_smul, Real.norm_of_nonneg zero_le_two, hx, mul_one]
  have := (le_modulusOfConvexity_iff E).2
    ⟨by simpa using pair x (-x) hx.le (by simpa using hx.le) hx₂, pair⟩
  linarith

/-- **Lindenstrauss's formula**: for `0 ≤ t`, the modulus of smoothness of the dual of a
nontrivial real normed space is `ρ_{E*}(t) = sup {t * ε / 2 - δ_E(ε) | 0 ≤ ε ≤ 2}`. -/
theorem modulusOfSmoothness_strongDual_eq_iSup {t : ℝ} (ht : 0 ≤ t) :
    modulusOfSmoothness (StrongDual ℝ E) t =
      ⨆ ε : Icc (0 : ℝ) 2, (t * ε / 2 - modulusOfConvexity E ε) := by
  have hbdd : BddAbove (range fun ε : Icc (0 : ℝ) 2 ↦ t * ε / 2 - modulusOfConvexity E ε) :=
    ⟨_, by rintro _ ⟨ε, rfl⟩; exact le_modulusOfSmoothness_strongDual ht ε.2.2⟩
  have h₀ := le_ciSup hbdd ⟨0, le_rfl, zero_le_two⟩
  simp only [mul_zero, zero_div, modulusOfConvexity_zero, sub_zero] at h₀
  have : Nonempty (Icc (0 : ℝ) 2) := ⟨⟨0, le_rfl, zero_le_two⟩⟩
  exact le_antisymm
    (modulusOfSmoothness_strongDual_le ht h₀ fun ε hε₀ hε ↦ le_ciSup hbdd ⟨ε, hε₀, hε⟩)
    (ciSup_le fun ε ↦ le_modulusOfSmoothness_strongDual ht ε.2.2)

end NormedDuality

end TauCeti
