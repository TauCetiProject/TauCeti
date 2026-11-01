/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Analysis.SpecialFunctions.Arsinh

/-!
# Analytic compressions of the height coordinate

On a cylinder `E × ℝ`, with base point `u` and height `t`, Łojasiewicz straightens an ordered
family of graphs by an analytic automorphism `g = g₂ ∘ g₁` which first rescales the base
coordinate by a positive analytic function of the height, and then compresses the height of the
point `(u, t)` according to the size of `t` relative to `√(1 + ‖u‖²)`. This file constructs both
automorphisms and shows that they and their inverses are analytic. The height compression uses
the inverse `β` of the normalized hyperbolic sine `t ↦ sinh t / sinh 1`, which is
`TauCeti.normalizedArsinh` from `TauCeti/Analysis/SpecialFunctions/Arsinh.lean`.

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

/-- The base scaling `(u, t) ↦ (h t • u, t)` is analytic at every point `(u, t)` at whose
height `t` the scaling function `h` is analytic. -/
@[fun_prop]
theorem analyticAt_baseScaling {p : E × 𝕜} (hp : AnalyticAt 𝕜 h p.2) :
    AnalyticAt 𝕜 (baseScaling hh) p := by
  rw [funext (baseScaling_apply hh)]
  have : AnalyticAt 𝕜 (fun q : E × 𝕜 ↦ h q.2) p := hp.comp analyticAt_snd
  exact (this.smul analyticAt_fst).prod analyticAt_snd

/-- The inverse `(u, t) ↦ ((h t)⁻¹ • u, t)` of the base scaling is analytic at every point
`(u, t)` at whose height `t` the scaling function `h` is analytic. -/
@[fun_prop]
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

/-- On a real inner product space, the height compression is `C^n` for every `n`, including
`n = ω`. -/
@[fun_prop]
theorem contDiff_heightCompression {n : WithTop ℕ∞} : ContDiff ℝ n (heightCompression E) := by
  rw [funext heightCompression_apply]
  have hpos (p : E × ℝ) : 0 < √(1 + ‖p.1‖ ^ 2) := sqrt_pos.2 (by positivity)
  have : ContDiff ℝ n fun p : E × ℝ ↦ √(1 + ‖p.1‖ ^ 2) :=
    (contDiff_const.add ((contDiff_norm_sq ℝ).comp contDiff_fst)).sqrt fun p ↦
      (by positivity : (0 : ℝ) < 1 + ‖p.1‖ ^ 2).ne'
  exact contDiff_fst.prodMk (contDiff_normalizedArsinh.comp
    (contDiff_snd.div this fun p ↦ (hpos p).ne'))

/-- On a real inner product space, the inverse of the height compression is `C^n` for every `n`,
including `n = ω`. -/
@[fun_prop]
theorem contDiff_heightCompression_symm {n : WithTop ℕ∞} :
    ContDiff ℝ n (heightCompression E).symm := by
  rw [funext heightCompression_symm_apply]
  have : ContDiff ℝ n fun p : E × ℝ ↦ √(1 + ‖p.1‖ ^ 2) :=
    (contDiff_const.add ((contDiff_norm_sq ℝ).comp contDiff_fst)).sqrt fun p ↦
      (by positivity : (0 : ℝ) < 1 + ‖p.1‖ ^ 2).ne'
  exact contDiff_fst.prodMk (this.mul (by fun_prop))

/-- On a real inner product space, the height compression is analytic at every point. -/
@[fun_prop]
theorem analyticAt_heightCompression (p : E × ℝ) : AnalyticAt ℝ (heightCompression E) p :=
  contDiff_heightCompression.contDiffAt.analyticAt

/-- On a real inner product space, the inverse of the height compression is analytic at every
point. -/
@[fun_prop]
theorem analyticAt_heightCompression_symm (p : E × ℝ) :
    AnalyticAt ℝ (heightCompression E).symm p :=
  contDiff_heightCompression_symm.contDiffAt.analyticAt

end heightCompression

end TauCeti
