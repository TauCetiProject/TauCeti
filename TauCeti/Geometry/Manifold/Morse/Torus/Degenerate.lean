/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.MinCriticalCount
public import TauCeti.Geometry.Manifold.Morse.Torus.Basic
import TauCeti.Geometry.Manifold.Morse.Perfect

/-!
# A function with three critical points on the two-torus

On the two-torus `T² = ∀ i : Fin 2, AddCircle (p i)`, with angles `θᵢ = 2π xᵢ / pᵢ`, the
**sine sum**

`torusSineSum p x = sin θ₀ + sin θ₁ + sin (θ₀ + θ₁)`

has exactly three critical points (`TauCeti.criticalPoints_torusSineSum`): the points with
`θ₀ = θ₁ = π / 3` and `θ₀ = θ₁ = -π / 3`, where it takes the values `3√3 / 2` and `-3√3 / 2`, and
the point with `θ₀ = θ₁ = π`, where it vanishes. Writing `u = e^{iθ₀}` and `v = e^{iθ₁}`, the two
partial derivatives vanish exactly when `Re u + Re (u v) = 0` and `Re v + Re (u v) = 0`. Then
`Re u = Re v`, so `v = u` or `v = ū`. If `v = ū` then `u v = 1` and `u = -1`; if `v = u` then
`Re u + Re u² = 2 (Re u)² + Re u - 1 = 0`, so `Re u = 1 / 2` or `u = -1`.

Every smooth function on `T²` has at least three critical points, by the Lusternik–Schnirelmann
bound (`TauCeti.card_add_one_le_minCriticalCount_torus`), so the sine sum attains the minimal
number of critical points: `c(T²) = 3` (`TauCeti.minCriticalCount_torus_fin_two`). Every Morse
function on `T²` has at least four critical points, the sum of the Betti numbers
(`TauCeti.IsMorse.two_pow_card_le_totalCriticalCount_torus`), so the sine sum is not a Morse
function (`TauCeti.not_isMorse_torusSineSum`). So on `T²` the bound `c(M)` of the degenerate
Arnold comparison (`TauCeti.SmoothTwoForm.DegenerateArnoldCriticalNumberStatement`) is `3`, strictly
below the bound `4` of the nondegenerate Arnold conjecture, the sum of the Betti numbers.

## Main declarations

* `TauCeti.torusSineSum`: the function `sin θ₀ + sin θ₁ + sin (θ₀ + θ₁)` on the two-torus, with
  `TauCeti.torusSineSum_coe` evaluating it at the class of a real vector.
* `TauCeti.contMDiff_torusSineSum`: it is smooth.
* `TauCeti.mem_criticalPoints_torusSineSum_iff` and `TauCeti.criticalPoints_torusSineSum`: its
  critical points are the three diagonal points with angles `π`, `π / 3` and `-π / 3`.
* `TauCeti.totalCriticalCount_torusSineSum`: it has exactly three critical points.
* `TauCeti.not_isMorse_torusSineSum`: it is not a Morse function.
* `TauCeti.minCriticalCount_torus_fin_two`: the minimal number of critical points of a smooth
  function on the two-torus is `3`.

## References

* O. Cornea, G. Lupton, J. Oprea and D. Tanré, *Lusternik–Schnirelmann Category*, Mathematical
  Surveys and Monographs 103, American Mathematical Society, 2003, Chapter 1.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Chapter 11, the Arnold conjecture and its degenerate form.
-/

public section

open Set Filter Function Topology AddCircle
open scoped Manifold ContDiff Real

namespace TauCeti

/-- **The critical equations of the sine sum on the circle.** For `u = e^{iθ₀}` and `v = e^{iθ₁}`,
the equations `cos θ₀ + cos (θ₀ + θ₁) = 0` and `cos θ₁ + cos (θ₀ + θ₁) = 0` hold exactly when
`u = v` is `-1`, `e^{iπ/3}` or `e^{-iπ/3}`. -/
private theorem re_add_re_mul_eq_zero_iff (u v : Circle) :
    (u : ℂ).re + ((u * v : Circle) : ℂ).re = 0 ∧ (v : ℂ).re + ((u * v : Circle) : ℂ).re = 0 ↔
      (u = Circle.exp π ∧ v = Circle.exp π) ∨
        (u = Circle.exp (π / 3) ∧ v = Circle.exp (π / 3)) ∨
          (u = Circle.exp (-(π / 3)) ∧ v = Circle.exp (-(π / 3))) := by
  have hu : (u : ℂ).re ^ 2 + (u : ℂ).im ^ 2 = 1 := by
    have := Circle.normSq_coe u
    rw [Complex.normSq_apply] at this
    linarith
  have hv : (v : ℂ).re ^ 2 + (v : ℂ).im ^ 2 = 1 := by
    have := Circle.normSq_coe v
    rw [Complex.normSq_apply] at this
    linarith
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [Circle.coe_mul, Complex.mul_re, Circle.ext_iff, Complex.ext_iff, Circle.coe_exp,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_pi, Real.sin_pi,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_three, Real.sin_pi_div_three]
  set a := (u : ℂ).re
  set b := (u : ℂ).im
  set c := (v : ℂ).re
  set d := (v : ℂ).im
  clear_value a b c d
  constructor
  · rintro ⟨h₁, h₂⟩
    have hac : a = c := by linarith
    subst hac
    have hbd : b = d ∨ b = -d := sq_eq_sq_iff_eq_or_eq_neg.1 (by linarith)
    rcases hbd with rfl | rfl
    · -- `v = u`, and `2 a² + a - 1 = (2 a - 1) (a + 1) = 0`.
      have ha : (2 * a - 1) * (a + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 ha with ha | ha
      · have ha : a = 1 / 2 := by linarith
        have hb : (b - √3 / 2) * (b + √3 / 2) = 0 := by nlinarith
        rcases mul_eq_zero.1 hb with hb | hb
        · exact Or.inr (Or.inl ⟨⟨ha, by linarith⟩, ha, by linarith⟩)
        · exact Or.inr (Or.inr ⟨⟨ha, by linarith⟩, ha, by linarith⟩)
      · have ha : a = -1 := by linarith
        have hb : b = 0 := by nlinarith
        exact Or.inl ⟨⟨ha, hb⟩, ha, hb⟩
    · -- `v = ū`, so `u v = 1` and `a = -1`.
      have ha : a = -1 := by nlinarith
      have hd : d = 0 := by nlinarith
      exact Or.inl ⟨⟨ha, by rw [hd, neg_zero]⟩, ha, hd⟩
  · rintro (⟨⟨ha, hb⟩, hc, hd⟩ | ⟨⟨ha, hb⟩, hc, hd⟩ | ⟨⟨ha, hb⟩, hc, hd⟩) <;>
      rw [ha, hb, hc, hd] <;> constructor <;> nlinarith

/-! ### The sine sum -/

variable (p : Fin 2 → ℝ)

/-- **The sine sum on the two-torus** `∀ i : Fin 2, AddCircle (p i)`: in the angles
`θᵢ = 2π xᵢ / pᵢ`, the function `sin θ₀ + sin θ₁ + sin (θ₀ + θ₁)`, written with the imaginary
parts of `AddCircle.toCircle`. -/
noncomputable def torusSineSum (x : ∀ i, AddCircle (p i)) : ℝ :=
  (toCircle (x 0) : ℂ).im + (toCircle (x 1) : ℂ).im +
    ((toCircle (x 0) * toCircle (x 1) : Circle) : ℂ).im

/-- The sine sum is the sum of the imaginary parts of `AddCircle.toCircle` of the two coordinates
and of their product. -/
theorem torusSineSum_def (x : ∀ i, AddCircle (p i)) :
    torusSineSum p x = (toCircle (x 0) : ℂ).im + (toCircle (x 1) : ℂ).im +
      ((toCircle (x 0) * toCircle (x 1) : Circle) : ℂ).im :=
  (rfl)

/-- At the class of a real vector `t`, the sine sum is
`sin (2π t₀ / p₀) + sin (2π t₁ / p₁) + sin (2π t₀ / p₀ + 2π t₁ / p₁)`. -/
@[simp]
theorem torusSineSum_coe (t : Fin 2 → ℝ) :
    torusSineSum p (fun i ↦ (t i : AddCircle (p i))) =
      Real.sin (2 * π / p 0 * t 0) + Real.sin (2 * π / p 1 * t 1) +
        Real.sin (2 * π / p 0 * t 0 + 2 * π / p 1 * t 1) := by
  rw [torusSineSum, toCircle_apply_mk, toCircle_apply_mk, ← Circle.exp_add]
  simp only [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]

variable [∀ i, Fact (0 < p i)]

/-- **The sine sum in the preferred charts.** Near the image of `x` in its preferred chart, the
coordinate expression of the sine sum is
`y ↦ sin (2π y₀ / p₀) + sin (2π y₁ / p₁) + sin (2π y₀ / p₀ + 2π y₁ / p₁)`. -/
theorem torusSineSum_comp_extChartAt_symm_eventuallyEq (x : ∀ i, AddCircle (p i)) :
    torusSineSum p ∘ (extChartAt (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) x).symm
      =ᶠ[𝓝 (extChartAt (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) x x)]
      fun y ↦ Real.sin (2 * π / p 0 * y 0) + Real.sin (2 * π / p 1 * y 1) +
        Real.sin (2 * π / p 0 * y 0 + 2 * π / p 1 * y 1) := by
  filter_upwards [extChartAt_target_mem_nhds (I := ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) x]
    with y hy
  rw [comp_apply, extChartAt_pi_symm_apply x hy, torusSineSum_coe]

/-- The sine sum on the two-torus is smooth. -/
theorem contMDiff_torusSineSum :
    ContMDiff (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) 𝓘(ℝ) ∞ (torusSineSum p) := by
  intro x
  exact contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.2 <|
    ContDiffAt.congr_of_eventuallyEq (by fun_prop)
      (torusSineSum_comp_extChartAt_symm_eventuallyEq p x)

/-- The derivative of `y ↦ sin (a y₀) + sin (b y₁) + sin (a y₀ + b y₁)` vanishes exactly when
`cos (a y₀) + cos (a y₀ + b y₁)` and `cos (b y₁) + cos (a y₀ + b y₁)` vanish, for `a, b ≠ 0`. -/
private theorem fderiv_sineSum_eq_zero_iff {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (y : Fin 2 → ℝ) :
    fderiv ℝ (fun y : Fin 2 → ℝ ↦ Real.sin (a * y 0) + Real.sin (b * y 1) +
        Real.sin (a * y 0 + b * y 1)) y = 0 ↔
      Real.cos (a * y 0) + Real.cos (a * y 0 + b * y 1) = 0 ∧
        Real.cos (b * y 1) + Real.cos (a * y 0 + b * y 1) = 0 := by
  have h₀ := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) y).const_mul a
  have h₁ := (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) y).const_mul b
  have hd : HasFDerivAt (fun y : Fin 2 → ℝ ↦ Real.sin (a * y 0) + Real.sin (b * y 1) +
      Real.sin (a * y 0 + b * y 1)) _ y := (h₀.sin.add h₁.sin).add (h₀.add h₁).sin
  set c₀ := Real.cos (a * y 0) + Real.cos (a * y 0 + b * y 1)
  set c₁ := Real.cos (b * y 1) + Real.cos (a * y 0 + b * y 1)
  -- The derivative is `v ↦ a c₀ v₀ + b c₁ v₁`.
  have hL (v : Fin 2 → ℝ) : fderiv ℝ (fun y : Fin 2 → ℝ ↦ Real.sin (a * y 0) +
      Real.sin (b * y 1) + Real.sin (a * y 0 + b * y 1)) y v = a * c₀ * v 0 + b * c₁ * v 1 := by
    simp only [hd.fderiv, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, c₀, c₁]
    ring
  constructor
  · intro h
    have e₀ := hL (Pi.single 0 1)
    have e₁ := hL (Pi.single 1 1)
    simp only [h, zero_apply, Pi.single_eq_same, ne_eq, zero_ne_one,
      one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne, mul_one, mul_zero, add_zero,
      zero_add] at e₀ e₁
    exact ⟨(mul_eq_zero.1 e₀.symm).resolve_left ha, (mul_eq_zero.1 e₁.symm).resolve_left hb⟩
  · rintro ⟨e₀, e₁⟩
    refine ContinuousLinearMap.ext fun v ↦ ?_
    rw [hL, e₀, e₁, zero_apply]
    ring

/-- **The critical equations of the sine sum.** A point `x` of the two-torus is a critical point of
the sine sum exactly when `cos θ₀ + cos (θ₀ + θ₁) = 0` and `cos θ₁ + cos (θ₀ + θ₁) = 0`, written
with the real parts of `u = e^{iθ₀}`, `v = e^{iθ₁}` and `u v`. -/
private theorem mem_criticalPoints_torusSineSum_iff_re {x : ∀ i, AddCircle (p i)} :
    x ∈ criticalPoints (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (torusSineSum p) ↔
      (toCircle (x 0) : ℂ).re + ((toCircle (x 0) * toCircle (x 1) : Circle) : ℂ).re = 0 ∧
        (toCircle (x 1) : ℂ).re + ((toCircle (x 0) * toCircle (x 1) : Circle) : ℂ).re = 0 := by
  have hp (i : Fin 2) : 2 * π / p i ≠ 0 := div_ne_zero (by positivity) (Fact.out : 0 < p i).ne'
  obtain ⟨y, hy⟩ : ∃ y, extChartAt (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) x x = y :=
    ⟨_, rfl⟩
  have hxy (i : Fin 2) : ((y i : ℝ) : AddCircle (p i)) = x i := by
    rw [← hy, extChartAt_pi_apply, coe_extChartAt_self]
  rw [mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero,
    (torusSineSum_comp_extChartAt_symm_eventuallyEq p x).fderiv_eq,
    fderiv_sineSum_eq_zero_iff (hp 0) (hp 1), hy, ← hxy 0, ← hxy 1, toCircle_apply_mk,
    toCircle_apply_mk, ← Circle.exp_add]
  simp only [Circle.coe_exp, Complex.exp_ofReal_mul_I_re]

/-- The angle `2π (q / 2) / q` is `π`. -/
private theorem two_pi_div_mul_half {q : ℝ} (hq : q ≠ 0) : 2 * π / q * (q / 2) = π := by
  field_simp

/-- The angle `2π (q / 6) / q` is `π / 3`. -/
private theorem two_pi_div_mul_sixth {q : ℝ} (hq : q ≠ 0) : 2 * π / q * (q / 6) = π / 3 := by
  field_simp; ring

/-- The angle `2π (-(q / 6)) / q` is `-(π / 3)`. -/
private theorem two_pi_div_mul_neg_sixth {q : ℝ} (hq : q ≠ 0) :
    2 * π / q * -(q / 6) = -(π / 3) := by
  field_simp; ring

/-- **Critical points of the sine sum.** A point of the two-torus is a critical point of the sine
sum exactly when its angles are both `π`, both `π / 3` or both `-π / 3`. -/
theorem mem_criticalPoints_torusSineSum_iff {x : ∀ i, AddCircle (p i)} :
    x ∈ criticalPoints (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (torusSineSum p) ↔
      x = (fun i ↦ ((p i / 2 : ℝ) : AddCircle (p i))) ∨
        x = (fun i ↦ ((p i / 6 : ℝ) : AddCircle (p i))) ∨
          x = (fun i ↦ ((-(p i / 6) : ℝ) : AddCircle (p i))) := by
  -- A point `↑a` of `AddCircle (p i)` is determined by its image `e^{2πia / pᵢ}` in the circle.
  have hcircle (i : Fin 2) (a : ℝ) (z : AddCircle (p i)) :
      z = (a : AddCircle (p i)) ↔ toCircle z = Circle.exp (2 * π / p i * a) := by
    rw [← toCircle_apply_mk, (injective_toCircle (Fact.out : 0 < p i).ne').eq_iff]
  have hp (i : Fin 2) : p i ≠ 0 := (Fact.out : 0 < p i).ne'
  rw [mem_criticalPoints_torusSineSum_iff_re, re_add_re_mul_eq_zero_iff]
  simp only [funext_iff, Fin.forall_fin_two, hcircle, two_pi_div_mul_half (hp _),
    two_pi_div_mul_sixth (hp _), two_pi_div_mul_neg_sixth (hp _)]

/-- **The sine sum has three critical points**: the diagonal points of the two-torus with angles
`π`, `π / 3` and `-π / 3`. -/
theorem criticalPoints_torusSineSum :
    criticalPoints (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (torusSineSum p) =
      {fun i ↦ ((p i / 2 : ℝ) : AddCircle (p i)), fun i ↦ ((p i / 6 : ℝ) : AddCircle (p i)),
        fun i ↦ ((-(p i / 6) : ℝ) : AddCircle (p i))} := by
  ext x
  rw [mem_criticalPoints_torusSineSum_iff, mem_insert_iff, mem_insert_iff, mem_singleton_iff]

/-- The sine sum on the two-torus has exactly three critical points. -/
theorem totalCriticalCount_torusSineSum :
    totalCriticalCount (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (torusSineSum p) = 3 := by
  -- The three critical points are told apart by the imaginary part `sin θ₀` of their first
  -- coordinate, which is `0`, `√3 / 2` and `-√3 / 2`.
  have hp : p 0 ≠ 0 := (Fact.out : 0 < p 0).ne'
  have hs : 0 < √3 / 2 := by positivity
  have h₁ : (toCircle ((p 0 / 2 : ℝ) : AddCircle (p 0)) : ℂ).im = 0 := by
    rw [im_toCircle_coe, two_pi_div_mul_half hp, Real.sin_pi]
  have h₂ : (toCircle ((p 0 / 6 : ℝ) : AddCircle (p 0)) : ℂ).im = √3 / 2 := by
    rw [im_toCircle_coe, two_pi_div_mul_sixth hp, Real.sin_pi_div_three]
  have h₃ : (toCircle ((-(p 0 / 6) : ℝ) : AddCircle (p 0)) : ℂ).im = -(√3 / 2) := by
    rw [im_toCircle_coe, two_pi_div_mul_neg_sixth hp, Real.sin_neg, Real.sin_pi_div_three]
  rw [totalCriticalCount_def, criticalPoints_torusSineSum, encard_eq_three]
  refine ⟨_, _, _, fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_, rfl⟩ <;>
    have := congrArg (fun x : ∀ i, AddCircle (p i) ↦ (toCircle (x 0) : ℂ).im) h <;>
    simp only [h₁, h₂, h₃] at this <;>
    linarith

/-- **The sine sum is not a Morse function**: every Morse function on the two-torus has at least
`4` critical points (`TauCeti.IsMorse.two_pow_card_le_totalCriticalCount_torus`), and the sine sum
has three. -/
theorem not_isMorse_torusSineSum :
    ¬IsMorse (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (torusSineSum p) := fun h ↦ by
  have := h.two_pow_card_le_totalCriticalCount_torus
  rw [totalCriticalCount_torusSineSum, Fintype.card_fin] at this
  norm_num at this

/-- **The minimal number of critical points of the two-torus is `3`**: every smooth function on
`T²` has at least three critical points by the Lusternik–Schnirelmann bound
(`TauCeti.card_add_one_le_minCriticalCount_torus`), and the sine sum `TauCeti.torusSineSum` has
exactly three. A Morse function has at least four. -/
theorem minCriticalCount_torus_fin_two :
    minCriticalCount (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) = 3 := by
  refine le_antisymm ?_ ?_
  · exact (minCriticalCount_le (contMDiff_torusSineSum p)).trans_eq
      (totalCriticalCount_torusSineSum p)
  · refine le_of_eq_of_le ?_ (card_add_one_le_minCriticalCount_torus p)
    rw [Fintype.card_fin]
    norm_num

end TauCeti

end
