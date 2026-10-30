/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Analytic compressions of the height coordinate

On a cylinder `E × ℝ`, with base point `u` and height `t`, Łojasiewicz straightens an ordered
family of graphs by an analytic automorphism `g = g₂ ∘ g₁` which first rescales the base
coordinate by a positive analytic function of the height, and then compresses the height of the
point `(u, t)` according to the size of `t` relative to `√(1 + ‖u‖²)`. This file constructs both
automorphisms and shows that they and their inverses are analytic.

* `TauCeti.normalizedArsinh`: the inverse `β` of the normalized hyperbolic sine
  `t ↦ sinh t / sinh 1 = (eᵗ - e⁻ᵗ) / (e - e⁻¹)`. It is an increasing analytic function with
  `β (± 1) = ± 1`, and its derivative satisfies `0 < β' s ≤ 2` and `|s| * β' s ≤ 1`.
* `TauCeti.baseScaling h hh`: the automorphism `g₁ (u, t) = (h t • u, t)` of `E × 𝕜`, for a
  nowhere-vanishing `h : 𝕜 → 𝕜`. It is analytic, with analytic inverse, wherever `h` is.
* `TauCeti.heightCompression E`: the automorphism `g₂ (u, t) = (u, β (t / √(1 + ‖u‖²)))` of
  `E × ℝ`. It is increasing on every vertical line and sends `(u, t)` into the strip `|s| < 1`
  exactly when `t² < 1 + ‖u‖²` (`TauCeti.abs_heightCompression_snd_lt_one_iff`). When `E` is a
  real inner product space, it is analytic with analytic inverse.
* `TauCeti.mapsTo_heightCompression_comp_baseScaling`: if `√(t² - 1) < |h t| * γ t` whenever
  `|t| ≥ 1`, then `g₂ ∘ g₁` maps every point `(u, t)` with `γ t ≤ ‖u‖` into the strip `|s| < 1`.
  This is how the composite pushes the complement of a neighbourhood of the vertical axis, which
  contains the tube `‖u‖ ≤ γ t`, into a bounded strip.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §2, Lemma 10.
-/

public section

open Real Set

namespace TauCeti

/-! ### The inverse of the normalized hyperbolic sine -/

/-- The inverse `β` of the normalized hyperbolic sine `t ↦ sinh t / sinh 1`, that is, of
`t ↦ (eᵗ - e⁻ᵗ) / (e - e⁻¹)`: `β s = arsinh (sinh 1 * s)`. It is an increasing analytic
bijection of `ℝ` fixing `0` and `± 1`. -/
noncomputable def normalizedArsinh (s : ℝ) : ℝ :=
  arsinh (sinh 1 * s)

theorem normalizedArsinh_apply (s : ℝ) : normalizedArsinh s = arsinh (sinh 1 * s) :=
  (rfl)

@[simp]
theorem sinh_normalizedArsinh_div (s : ℝ) : sinh (normalizedArsinh s) / sinh 1 = s := by
  rw [normalizedArsinh_apply, sinh_arsinh, mul_div_cancel_left₀ _ (sinh_pos_iff.2 one_pos).ne']

@[simp]
theorem normalizedArsinh_sinh_div (t : ℝ) : normalizedArsinh (sinh t / sinh 1) = t := by
  rw [normalizedArsinh_apply, mul_div_cancel₀ _ (sinh_pos_iff.2 one_pos).ne', arsinh_sinh]

theorem normalizedArsinh_strictMono : StrictMono normalizedArsinh := by
  rw [funext normalizedArsinh_apply]
  exact arsinh_strictMono.comp (strictMono_mul_left_of_pos (sinh_pos_iff.2 one_pos))

@[simp]
theorem normalizedArsinh_lt_normalizedArsinh {s s' : ℝ} :
    normalizedArsinh s < normalizedArsinh s' ↔ s < s' :=
  normalizedArsinh_strictMono.lt_iff_lt

@[simp]
theorem normalizedArsinh_le_normalizedArsinh {s s' : ℝ} :
    normalizedArsinh s ≤ normalizedArsinh s' ↔ s ≤ s' :=
  normalizedArsinh_strictMono.le_iff_le

@[simp]
theorem normalizedArsinh_zero : normalizedArsinh 0 = 0 := by
  simp [normalizedArsinh_apply]

@[simp]
theorem normalizedArsinh_one : normalizedArsinh 1 = 1 := by
  simp [normalizedArsinh_apply]

@[simp]
theorem normalizedArsinh_neg (s : ℝ) : normalizedArsinh (-s) = -normalizedArsinh s := by
  simp [normalizedArsinh_apply]

/-- `β` maps the open interval `(-1, 1)` onto itself, and its complement onto its complement. -/
theorem abs_normalizedArsinh_lt_one_iff {s : ℝ} : |normalizedArsinh s| < 1 ↔ |s| < 1 := by
  conv_lhs => rw [← normalizedArsinh_one]
  rw [abs_lt, abs_lt, ← normalizedArsinh_neg, normalizedArsinh_lt_normalizedArsinh,
    normalizedArsinh_lt_normalizedArsinh]

@[fun_prop]
theorem contDiff_normalizedArsinh {n : WithTop ℕ∞} : ContDiff ℝ n normalizedArsinh := by
  rw [funext normalizedArsinh_apply]
  fun_prop

@[fun_prop]
theorem analyticAt_normalizedArsinh (s : ℝ) : AnalyticAt ℝ normalizedArsinh s :=
  contDiff_normalizedArsinh.contDiffAt.analyticAt

theorem hasDerivAt_normalizedArsinh (s : ℝ) :
    HasDerivAt normalizedArsinh (sinh 1 / √(1 + (sinh 1 * s) ^ 2)) s := by
  rw [funext normalizedArsinh_apply]
  simpa [div_eq_inv_mul] using ((hasDerivAt_id s).const_mul (sinh 1)).arsinh

theorem deriv_normalizedArsinh (s : ℝ) :
    deriv normalizedArsinh s = sinh 1 / √(1 + (sinh 1 * s) ^ 2) :=
  (hasDerivAt_normalizedArsinh s).deriv

theorem deriv_normalizedArsinh_pos (s : ℝ) : 0 < deriv normalizedArsinh s := by
  rw [deriv_normalizedArsinh]
  exact div_pos (sinh_pos_iff.2 one_pos) (sqrt_pos.2 (by positivity))

/-- The derivative of `β` is at most `2`. -/
theorem deriv_normalizedArsinh_le_two (s : ℝ) : deriv normalizedArsinh s ≤ 2 := by
  have hsinh : sinh 1 < 2 := by
    rw [sinh_eq]
    linarith [exp_pos (-1), exp_one_lt_d9]
  rw [deriv_normalizedArsinh]
  refine (div_le_self (sinh_pos_iff.2 one_pos).le ?_).trans hsinh.le
  exact one_le_sqrt.2 (le_add_of_nonneg_right (sq_nonneg _))

/-- The derivative of `β` at `s` is at most `1 / |s|`, in the form `|s| * β' s ≤ 1`, which also
holds at `s = 0`. -/
theorem abs_mul_deriv_normalizedArsinh_le_one (s : ℝ) : |s| * deriv normalizedArsinh s ≤ 1 := by
  have h1 : 0 < sinh 1 := sinh_pos_iff.2 one_pos
  calc |s| * deriv normalizedArsinh s = |sinh 1 * s| / √(1 + (sinh 1 * s) ^ 2) := by
        rw [deriv_normalizedArsinh, abs_mul, abs_of_pos h1]; ring
    _ ≤ 1 := div_le_one_of_le₀ (abs_le_sqrt (le_add_of_nonneg_left zero_le_one)) (sqrt_nonneg _)

/-! ### Rescaling the base by a function of the height -/

section baseScaling

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {h : 𝕜 → 𝕜} (hh : ∀ t, h t ≠ 0)

/-- For a nowhere-vanishing function `h` of the height, the automorphism `(u, t) ↦ (h t • u, t)`
of the cylinder `E × 𝕜`, rescaling each horizontal slice by the factor `h t`. -/
def baseScaling : E × 𝕜 ≃ E × 𝕜 :=
  Equiv.prodCongrLeft fun t ↦ (LinearEquiv.smulOfNeZero 𝕜 E (h t) (hh t)).toEquiv

@[simp]
theorem baseScaling_apply (p : E × 𝕜) : baseScaling hh p = (h p.2 • p.1, p.2) :=
  (rfl)

@[simp]
theorem baseScaling_symm_apply (p : E × 𝕜) :
    (baseScaling hh).symm p = ((h p.2)⁻¹ • p.1, p.2) :=
  (rfl)

variable {hh}

theorem analyticAt_baseScaling {p : E × 𝕜} (hp : AnalyticAt 𝕜 h p.2) :
    AnalyticAt 𝕜 (baseScaling hh) p := by
  rw [funext (baseScaling_apply hh)]
  have : AnalyticAt 𝕜 (fun q : E × 𝕜 ↦ h q.2) p := hp.comp analyticAt_snd
  exact (this.smul analyticAt_fst).prod analyticAt_snd

theorem analyticAt_baseScaling_symm {p : E × 𝕜} (hp : AnalyticAt 𝕜 h p.2) :
    AnalyticAt 𝕜 (baseScaling hh).symm p := by
  rw [funext (baseScaling_symm_apply hh)]
  have : AnalyticAt 𝕜 (fun q : E × 𝕜 ↦ (h q.2)⁻¹) p := (hp.comp analyticAt_snd).inv (hh p.2)
  exact (this.smul analyticAt_fst).prod analyticAt_snd

end baseScaling

/-! ### Compressing the height -/

section heightCompression

variable (E : Type*) [NormedAddCommGroup E]

/-- The automorphism `(u, t) ↦ (u, β (t / √(1 + ‖u‖²)))` of the cylinder `E × ℝ`, where `β` is
`TauCeti.normalizedArsinh`. On the vertical line over `u` it is an increasing bijection taking the
heights `± √(1 + ‖u‖²)` to `± 1`. -/
noncomputable def heightCompression : E × ℝ ≃ E × ℝ where
  toFun p := (p.1, normalizedArsinh (p.2 / √(1 + ‖p.1‖ ^ 2)))
  invFun p := (p.1, √(1 + ‖p.1‖ ^ 2) * (sinh p.2 / sinh 1))
  left_inv p := by
    have : √(1 + ‖p.1‖ ^ 2) ≠ 0 := (sqrt_pos.2 (by positivity)).ne'
    simp [mul_div_cancel₀ _ this]
  right_inv p := by
    have : √(1 + ‖p.1‖ ^ 2) ≠ 0 := (sqrt_pos.2 (by positivity)).ne'
    simp [mul_div_cancel_left₀ _ this]

variable {E}

@[simp]
theorem heightCompression_apply (p : E × ℝ) :
    heightCompression E p = (p.1, normalizedArsinh (p.2 / √(1 + ‖p.1‖ ^ 2))) :=
  (rfl)

@[simp]
theorem heightCompression_symm_apply (p : E × ℝ) :
    (heightCompression E).symm p = (p.1, √(1 + ‖p.1‖ ^ 2) * (sinh p.2 / sinh 1)) :=
  (rfl)

/-- The height compression is increasing on every vertical line. -/
theorem strictMono_heightCompression_snd (u : E) :
    StrictMono fun t ↦ (heightCompression E (u, t)).2 := fun t t' htt' ↦ by
  simpa using div_lt_div_of_pos_right htt' (sqrt_pos.2 (by positivity))

/-- The height compression sends `(u, t)` into the strip `|s| < 1` exactly when
`t² < 1 + ‖u‖²`. -/
theorem abs_heightCompression_snd_lt_one_iff {p : E × ℝ} :
    |(heightCompression E p).2| < 1 ↔ p.2 ^ 2 < 1 + ‖p.1‖ ^ 2 := by
  have hpos : 0 < √(1 + ‖p.1‖ ^ 2) := sqrt_pos.2 (by positivity)
  rw [heightCompression_apply, abs_normalizedArsinh_lt_one_iff, abs_div, abs_of_pos hpos,
    div_lt_one hpos, lt_sqrt (abs_nonneg _), sq_abs]

/-- If `√(t² - 1) < |h t| * γ t` whenever `|t| ≥ 1`, then rescaling the base by the
nowhere-vanishing function `h` and compressing the height maps every point `(u, t)` with
`γ t ≤ ‖u‖` into the strip `|s| < 1`. -/
theorem mapsTo_heightCompression_comp_baseScaling [NormedSpace ℝ E] {h γ : ℝ → ℝ}
    (hh : ∀ t, h t ≠ 0) (hhγ : ∀ t, 1 ≤ |t| → √(t ^ 2 - 1) < |h t| * γ t) :
    MapsTo (heightCompression E ∘ baseScaling hh) {p | γ p.2 ≤ ‖p.1‖} {p | |p.2| < 1} := by
  rintro ⟨u, t⟩ (hu : γ t ≤ ‖u‖)
  simp only [mem_ofPred_eq, Function.comp_apply, abs_heightCompression_snd_lt_one_iff,
    baseScaling_apply, norm_smul, norm_eq_abs]
  rcases lt_or_ge |t| 1 with ht | ht
  · have : t ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one t).2 ht
    nlinarith [sq_nonneg (|h t| * ‖u‖)]
  · have h1 : √(t ^ 2 - 1) < |h t| * ‖u‖ :=
      (hhγ t ht).trans_le (mul_le_mul_of_nonneg_left hu (abs_nonneg _))
    have h2 := (sqrt_lt' ((sqrt_nonneg _).trans_lt h1)).1 h1
    rw [mul_pow] at h2
    linarith

variable [InnerProductSpace ℝ E]

theorem contDiff_heightCompression {n : WithTop ℕ∞} : ContDiff ℝ n (heightCompression E) := by
  rw [funext heightCompression_apply]
  have hpos (p : E × ℝ) : 0 < √(1 + ‖p.1‖ ^ 2) := sqrt_pos.2 (by positivity)
  have : ContDiff ℝ n fun p : E × ℝ ↦ √(1 + ‖p.1‖ ^ 2) :=
    (contDiff_const.add ((contDiff_norm_sq ℝ).comp contDiff_fst)).sqrt fun p ↦
      (by positivity : (0 : ℝ) < 1 + ‖p.1‖ ^ 2).ne'
  exact contDiff_fst.prodMk (contDiff_normalizedArsinh.comp
    (contDiff_snd.div this fun p ↦ (hpos p).ne'))

theorem contDiff_heightCompression_symm {n : WithTop ℕ∞} :
    ContDiff ℝ n (heightCompression E).symm := by
  rw [funext heightCompression_symm_apply]
  have : ContDiff ℝ n fun p : E × ℝ ↦ √(1 + ‖p.1‖ ^ 2) :=
    (contDiff_const.add ((contDiff_norm_sq ℝ).comp contDiff_fst)).sqrt fun p ↦
      (by positivity : (0 : ℝ) < 1 + ‖p.1‖ ^ 2).ne'
  exact contDiff_fst.prodMk (this.mul (by fun_prop))

theorem analyticAt_heightCompression (p : E × ℝ) : AnalyticAt ℝ (heightCompression E) p :=
  contDiff_heightCompression.contDiffAt.analyticAt

theorem analyticAt_heightCompression_symm (p : E × ℝ) :
    AnalyticAt ℝ (heightCompression E).symm p :=
  contDiff_heightCompression_symm.contDiffAt.analyticAt

end heightCompression

end TauCeti
