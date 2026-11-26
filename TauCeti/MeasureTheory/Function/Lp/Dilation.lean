/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import TauCeti.MeasureTheory.Function.Lp.Precomposition

/-!
# Dilation scaling of the `Lᵖ` seminorm

Dilating the variable of a function on a finite-dimensional real normed space `E` by `r⁻¹`, for
`r ≠ 0`, multiplies its `Lᵖ` seminorm against an additive Haar measure by `|r| ^ (n / p)`, where
`n` is the dimension of `E`. Here `n / p` stands for `n / p.toReal`, which is `0` at `p = 0` and
`p = ∞` by Lean's conventions `ENNReal.toReal ∞ = 0` and `x / 0 = 0`, so at those two exponents
the factor is `1`. This is the `eLpNorm` counterpart of the lower Lebesgue integral law
`MeasureTheory.Measure.lintegral_comp_inv_smul`.

Normalizing by the inverse factor turns dilation into a linear isometric equivalence
`f ↦ r ^ (-n / p) • f (r⁻¹ • ·)` of `Lᵖ`, and these equivalences form an action of the positive
reals. They are linear over every normed field `𝕜` of scalars of the codomain that commute with
the real scalars, for instance `ℂ`-linear on complex-valued functions, and their underlying maps do
not depend on the choice of `𝕜`. They describe the dilations
of scale-invariant problems such as the sharp Sobolev inequality: dilating a homogeneous Sobolev
function acts by the normalized dilation at exponent `p` on its gradient and at the
Sobolev-conjugate exponent `p⋆` on the function itself, so both the `Lᵖ` norm of the gradient and
the critical `L^{p⋆}` norm are invariant.

More generally, composing with a linear automorphism `e` multiplies the `Lᵖ` seminorm by
`|det e|^(-1 / p)`, and the `Lᵖ` seminorm on a preimage `e ⁻¹' s` by the same factor relative to
the `Lᵖ` seminorm on `s`, for any set `s`. The codomain only needs a continuous extended norm.

## Main declarations

* `MeasureTheory.Measure.eLpNorm_comp_inv_smul`: `‖u (r⁻¹ • ·)‖_p = |r| ^ (n / p) * ‖u‖_p`, and
  `MeasureTheory.Measure.eLpNorm_comp_inv_smul_restrict_smul`, the same law for the `Lᵖ` seminorms
  on `r • s` and on `s`.
* `MeasureTheory.Measure.dilateLp`: the normalized dilation of `Lᵖ`, and
  `MeasureTheory.Measure.eLpNorm_dilateLp`, its effect `r ^ (n / q - n / p)` on every `Lᵠ`
  seminorm.
* `MeasureTheory.Measure.eLpNorm_comp_continuousLinearEquiv`:
  `‖u ∘ e‖_p = |det e|^(-1 / p) * ‖u‖_p`.
* `MeasureTheory.Measure.eLpNorm_comp_continuousLinearEquiv_restrict_preimage`: the same identity
  for the `Lᵖ` seminorms on `e ⁻¹' s` and on `s`.
* `MeasureTheory.Measure.eLpNorm_comp_smul_restrict_preimage`: the dilation case,
  `‖u (c • ·)‖_{Lᵖ((c • ·)⁻¹' s)} = |c| ^ (-n / p) * ‖u‖_{Lᵖ(s)}`.
* `MeasureTheory.MemLp.comp_continuousLinearEquiv`: so composing with `e` preserves `Lᵖ`, and
  `MeasureTheory.MemLp.comp_continuousLinearEquiv_restrict_preimage` carries `Lᵖ` on `s` to `Lᵖ`
  on `e ⁻¹' s`.
-/

public section

namespace MeasureTheory.Measure

open Module
open scoped ENNReal Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
  {G : Type*} [TopologicalSpace G] [ContinuousENorm G]

/-- **Dilation scaling of the `Lᵖ` seminorm on a set:**
`‖u (r⁻¹ • ·)‖_{Lᵖ(r • s)} = |r| ^ (n / p) * ‖u‖_{Lᵖ(s)}` for `r ≠ 0`, where `n` is the dimension
of the ambient space. The set `s` need not be measurable. The exponent `n / p` is `n / p.toReal`,
which is `0` at `p = 0` and `p = ∞`, where the factor is thus `1`. -/
theorem eLpNorm_comp_inv_smul_restrict_smul (u : E → G) {r : ℝ} (hr : r ≠ 0) (p : ℝ≥0∞)
    (s : Set E) :
    eLpNorm (fun x => u (r⁻¹ • x)) p (μ.restrict (r • s)) =
      ENNReal.ofReal (|r| ^ ((finrank ℝ E : ℝ) / p.toReal)) * eLpNorm u p (μ.restrict s) := by
  have hr' : r⁻¹ ≠ 0 := inv_ne_zero hr
  have he := measurableEmbedding_const_smul₀ (α := E) hr'
  rw [← Function.comp_def, ← Set.preimage_smul_inv₀ hr, ← he.eLpNorm_map_measure, ← he.restrict_map,
    map_addHaar_smul μ hr', restrict_smul, eLpNorm_smul_measure_of_ne_zero (by positivity),
    smul_eq_mul]
  congr 1
  -- The measure factor is `|(r⁻¹ ^ n)⁻¹| = |r| ^ n`, raised to the power `1 / p`.
  rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) ENNReal.toReal_nonneg]
  simp [div_eq_mul_inv, Real.rpow_natCast_mul (abs_nonneg r)]

/-- **Dilation scaling of the `Lᵖ` seminorm:** `‖u (r⁻¹ • ·)‖_p = |r| ^ (n / p) * ‖u‖_p` for
`r ≠ 0`, where `n` is the dimension of the ambient space. The exponent `n / p` is `n / p.toReal`,
which is `0` at `p = 0` and `p = ∞`, where the factor is thus `1`. -/
theorem eLpNorm_comp_inv_smul (u : E → G) {r : ℝ} (hr : r ≠ 0) (p : ℝ≥0∞) :
    eLpNorm (fun x => u (r⁻¹ • x)) p μ =
      ENNReal.ofReal (|r| ^ ((finrank ℝ E : ℝ) / p.toReal)) * eLpNorm u p μ := by
  simpa [Set.smul_set_univ₀ hr] using eLpNorm_comp_inv_smul_restrict_smul μ u hr p Set.univ

/-- **Linear change of variables in the `Lᵖ` seminorm on a set:** composing with a linear
automorphism `e` multiplies the `Lᵖ` seminorm on `e ⁻¹' s`, against an additive Haar measure, by
`|det e|^(-1 / p)` relative to the `Lᵖ` seminorm of the function on `s`. The set `s` need not be
measurable. -/
theorem eLpNorm_comp_continuousLinearEquiv_restrict_preimage
    (u : E → G) (e : E ≃L[ℝ] E) (p : ℝ≥0∞) {s : Set E} :
    eLpNorm (u ∘ e) p (μ.restrict (e ⁻¹' s)) =
      ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal *
        eLpNorm u p (μ.restrict s) := by
  have hdet : LinearMap.det (e : E →ₗ[ℝ] E) ≠ 0 := (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hmap : map e μ = ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| • μ :=
    map_linearMap_addHaar_eq_smul_addHaar μ hdet
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  rw [← he.eLpNorm_map_measure, ← he.restrict_map, hmap, restrict_smul,
    eLpNorm_smul_measure_of_ne_zero (by simpa using hdet), smul_eq_mul]

/-- **Linear change of variables in the `Lᵖ` seminorm:** composing with a linear automorphism `e`
multiplies the `Lᵖ` seminorm against an additive Haar measure by `|det e|^(-1 / p)`. The exponent
`1 / p` is `(1 / p).toReal`, which is `0` at `p = 0` and `p = ∞`, where the factor is thus `1`. -/
theorem eLpNorm_comp_continuousLinearEquiv (u : E → G) (e : E ≃L[ℝ] E) (p : ℝ≥0∞) :
    eLpNorm (u ∘ e) p μ = ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal *
      eLpNorm u p μ := by
  simpa using eLpNorm_comp_continuousLinearEquiv_restrict_preimage μ u e p (s := Set.univ)

/-- **Dilation scaling of the `Lᵖ` seminorm on a set:** for `c ≠ 0` and any set `s`,
`‖u (c • ·)‖_{Lᵖ((c • ·)⁻¹' s)} = |c| ^ (-n / p) * ‖u‖_{Lᵖ(s)}`, where `n` is the dimension of the
ambient space. This is the dilation case of `eLpNorm_comp_continuousLinearEquiv_restrict_preimage`,
the restricted counterpart of `eLpNorm_comp_inv_smul`. The exponent `n / p` is `n / p.toReal`,
which is `0` at `p = 0` and `p = ∞`, where the factor is thus `1`. -/
theorem eLpNorm_comp_smul_restrict_preimage (u : E → G) {c : ℝ} (hc : c ≠ 0) (p : ℝ≥0∞)
    (s : Set E) :
    eLpNorm (fun x => u (c • x)) p (μ.restrict ((c • ·) ⁻¹' s)) =
      ENNReal.ofReal (|c| ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹ * eLpNorm u p (μ.restrict s) := by
  -- Scaling by `c` as a linear automorphism, whose determinant is `c ^ n`.
  let e : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  have he : ⇑e = (c • ·) := by ext; simp [e]
  have hlin : (e : E →ₗ[ℝ] E) = c • LinearMap.id := by ext; simp [e]
  have hdet : LinearMap.det (e : E →ₗ[ℝ] E) = c ^ finrank ℝ E := by
    rw [hlin, LinearMap.det_smul, LinearMap.det_id, mul_one]
  -- The Jacobian factor: `|c ^ n|⁻¹ ^ (1 / p) = (|c| ^ (n / p))⁻¹`.
  have hfac : ENNReal.ofReal |(c ^ finrank ℝ E)⁻¹| ^ (1 / p).toReal =
      ENNReal.ofReal (|c| ^ ((finrank ℝ E : ℝ) / p.toReal))⁻¹ := by
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) ENNReal.toReal_nonneg, abs_inv, abs_pow,
      Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg c)]
    simp [div_eq_mul_inv]
  simpa only [Function.comp_def, he, hdet, hfac] using
    eLpNorm_comp_continuousLinearEquiv_restrict_preimage μ u e p (s := s)

variable {μ} in
/-- Precomposition with a linear automorphism `e` maps `Lᵖ` on a set `s` to `Lᵖ` on `e ⁻¹' s`, for
an additive Haar measure. -/
theorem _root_.MeasureTheory.MemLp.comp_continuousLinearEquiv_restrict_preimage {p : ℝ≥0∞}
    {u : E → G} {s : Set E} (hu : MemLp u p (μ.restrict s)) (e : E ≃L[ℝ] E) :
    MemLp (fun x ↦ u (e x)) p (μ.restrict (e ⁻¹' s)) := by
  rw [memLp_iff, ← Function.comp_def, eLpNorm_comp_continuousLinearEquiv_restrict_preimage]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
    ENNReal.ofReal_ne_top) hu.eLpNorm_lt_top

variable {μ} in
/-- Precomposition with a linear automorphism preserves `Lᵖ` for an additive Haar measure. -/
theorem _root_.MeasureTheory.MemLp.comp_continuousLinearEquiv {p : ℝ≥0∞} {u : E → G}
    (hu : MemLp u p μ) (e : E ≃L[ℝ] E) : MemLp (fun x ↦ u (e x)) p μ := by
  simpa using (hu.restrict Set.univ).comp_continuousLinearEquiv_restrict_preimage e

variable {μ} {𝕜 F : Type*} [NormedField 𝕜] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] {p : ℝ≥0∞} [Fact (1 ≤ p)] {r s : ℝ}

variable (𝕜 μ p) in
/-- **The normalized dilation of `Lᵖ`** by a factor `r > 0`, as a `𝕜`-linear isometric
equivalence: almost everywhere it sends `f` to `r ^ (-n / p) • f (r⁻¹ • ·)`, where `n` is the
dimension of `E` (`MeasureTheory.Measure.coeFn_dilateLp`), and its inverse is the dilation by
`r⁻¹` (`MeasureTheory.Measure.dilateLp_symm`). The exponent `n / p` is `n / p.toReal`, which is
`0` at `p = ∞`, where the dilation is plain precomposition. It is `𝕜`-linear because the real
normalizing factor `r ^ (-n / p)` commutes with the scalars `𝕜`, and its underlying map is the
same for every `𝕜` (`MeasureTheory.Measure.coe_dilateLp_eq_coe_dilateLp`). -/
noncomputable def dilateLp (r : ℝ) (hr : 0 < r) : Lp F p μ ≃ₗᵢ[𝕜] Lp F p μ :=
  let P : Lp F p μ ≃L[𝕜] Lp F p μ :=
    Lp.compEquivOfMapLeSmul 𝕜 (measurable_const_smul r⁻¹).aemeasurable ENNReal.ofReal_ne_top
      (map_addHaar_smul μ (inv_ne_zero hr.ne')).le (measurable_const_smul r).aemeasurable
      ENNReal.ofReal_ne_top (map_addHaar_smul μ hr.ne').le
      (fun x ↦ smul_inv_smul₀ hr.ne' x) (fun x ↦ inv_smul_smul₀ hr.ne' x)
  { (P.toLinearEquiv.trans (DistribMulAction.toLinearEquiv 𝕜 _
      (Units.mk0 _ (Real.rpow_pos_of_pos hr (-((finrank ℝ E : ℝ) / p.toReal))).ne'))) with
    norm_map' f := by
      have hae : (P f : E → F) =ᵐ[μ] fun x ↦ f (r⁻¹ • x) := by
        rw [Lp.compEquivOfMapLeSmul_apply]
        exact Lp.coeFn_compOfMapLeSmul _ _ _ f
      have hPf : ‖P f‖ = r ^ ((finrank ℝ E : ℝ) / p.toReal) * ‖f‖ := by
        rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hae, eLpNorm_comp_inv_smul μ _ hr.ne',
          abs_of_pos hr, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
      simp only [LinearEquiv.trans_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
        DistribMulAction.toLinearEquiv_apply, Units.smul_mk0, norm_smul,
        Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr _), hPf, ← mul_assoc,
        ← Real.rpow_add hr, neg_add_cancel, Real.rpow_zero, one_mul] }

/-- The normalized dilation is almost everywhere `f ↦ r ^ (-n / p) • f (r⁻¹ • ·)`. -/
theorem coeFn_dilateLp (hr : 0 < r) (f : Lp F p μ) :
    ⇑(dilateLp μ 𝕜 p r hr f) =ᵐ[μ]
      fun x ↦ r ^ (-((finrank ℝ E : ℝ) / p.toReal)) • f (r⁻¹ • x) := by
  -- The dilation is, by construction, the scalar multiple of the precomposition `g`.
  let g := Lp.compOfMapLeSmul 𝕜 (measurable_const_smul r⁻¹).aemeasurable ENNReal.ofReal_ne_top
    (map_addHaar_smul μ (inv_ne_zero hr.ne')).le f
  have h : dilateLp μ 𝕜 p r hr f = r ^ (-((finrank ℝ E : ℝ) / p.toReal)) • g := by
    simp only [dilateLp, LinearIsometryEquiv.coe_mk, LinearEquiv.trans_apply,
      ContinuousLinearEquiv.coe_toLinearEquiv, Lp.compEquivOfMapLeSmul_apply,
      DistribMulAction.toLinearEquiv_apply, Units.smul_mk0, g]
  rw [h]
  filter_upwards [Lp.coeFn_smul (r ^ (-((finrank ℝ E : ℝ) / p.toReal))) g,
    Lp.coeFn_compOfMapLeSmul (𝕜 := 𝕜) (measurable_const_smul r⁻¹).aemeasurable
      ENNReal.ofReal_ne_top
      (map_addHaar_smul μ (inv_ne_zero hr.ne')).le f] with x hx hy
  rw [hx, Pi.smul_apply, hy, Function.comp_apply]

variable (𝕜) in
/-- The normalized dilation does not depend on the field of scalars: its `𝕜`-linear and
`𝕜'`-linear versions have the same underlying map. For instance, the `ℂ`-linear dilation of
complex-valued functions is the `ℝ`-linear one. -/
theorem coe_dilateLp_eq_coe_dilateLp (𝕜' : Type*) [NormedField 𝕜'] [NormedSpace 𝕜' F]
    [SMulCommClass ℝ 𝕜' F] (hr : 0 < r) :
    ⇑(dilateLp (F := F) μ 𝕜 p r hr) = ⇑(dilateLp μ 𝕜' p r hr) := by
  ext1 f
  apply Lp.ext
  filter_upwards [coeFn_dilateLp (𝕜 := 𝕜) hr f, coeFn_dilateLp (𝕜 := 𝕜') hr f] with x hx hy
  rw [hx, hy]

/-- The normalized dilation of a class with representative `g` is almost everywhere
`r ^ (-n / p) • g (r⁻¹ • ·)`. -/
theorem coeFn_dilateLp_of_ae_eq (hr : 0 < r) {f : Lp F p μ} {g : E → F} (hf : f =ᵐ[μ] g) :
    ⇑(dilateLp μ 𝕜 p r hr f) =ᵐ[μ]
      fun x ↦ r ^ (-((finrank ℝ E : ℝ) / p.toReal)) • g (r⁻¹ • x) := by
  filter_upwards [coeFn_dilateLp (𝕜 := 𝕜) hr f,
    (quasiMeasurePreserving_smul μ (inv_ne_zero hr.ne')).ae_eq_comp hf] with x hx hy
  simp only [Function.comp_apply] at hy
  rw [hx, hy]

/-- At `p = ∞` the normalized dilation carries no weight: it is almost everywhere the plain
precomposition `f (r⁻¹ • ·)`. -/
theorem coeFn_dilateLp_top (hr : 0 < r) (f : Lp F ∞ μ) :
    ⇑(dilateLp μ 𝕜 ∞ r hr f) =ᵐ[μ] fun x ↦ f (r⁻¹ • x) := by
  simpa using coeFn_dilateLp (𝕜 := 𝕜) hr f

/-- At `p = ∞` the normalized dilation of a class with representative `g` is almost everywhere
`g (r⁻¹ • ·)`. -/
theorem coeFn_dilateLp_top_of_ae_eq (hr : 0 < r) {f : Lp F ∞ μ} {g : E → F} (hf : f =ᵐ[μ] g) :
    ⇑(dilateLp μ 𝕜 ∞ r hr f) =ᵐ[μ] fun x ↦ g (r⁻¹ • x) := by
  simpa using coeFn_dilateLp_of_ae_eq (𝕜 := 𝕜) hr hf

variable (μ) in
/-- **`Lᵠ` seminorm of a dilate with an arbitrary normalization:**
`‖r ^ (-a) • u (r⁻¹ • ·)‖_q = r ^ (n / q - a) * ‖u‖_q` for `r > 0`. The exponent `n / q` is
`n / q.toReal`, which is `0` at `q = 0` and `q = ∞`. -/
theorem eLpNorm_rpow_neg_smul_comp_inv_smul (u : E → F) (hr : 0 < r) (a : ℝ) (q : ℝ≥0∞) :
    eLpNorm (fun x ↦ r ^ (-a) • u (r⁻¹ • x)) q μ =
      ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) / q.toReal - a)) * eLpNorm u q μ := by
  have h : (fun x ↦ r ^ (-a) • u (r⁻¹ • x)) = r ^ (-a) • fun x ↦ u (r⁻¹ • x) := rfl
  rw [h, eLpNorm_const_smul, eLpNorm_comp_inv_smul μ u hr.ne', ← mul_assoc, abs_of_pos hr,
    Real.eNorm_eq_ofReal (by positivity), ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hr,
    neg_add_eq_sub]

/-- **`Lᵠ` seminorm of a normalized dilate:** the normalized dilation of `Lᵖ` by `r > 0`
multiplies every `Lᵠ` seminorm by `r ^ (n / q - n / p)`, so it preserves the `Lᵖ` norm. -/
theorem eLpNorm_dilateLp (hr : 0 < r) (f : Lp F p μ) (q : ℝ≥0∞) :
    eLpNorm (dilateLp μ 𝕜 p r hr f) q μ =
      ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) / q.toReal - finrank ℝ E / p.toReal)) *
        eLpNorm f q μ := by
  rw [eLpNorm_congr_ae (coeFn_dilateLp (𝕜 := 𝕜) hr f), eLpNorm_rpow_neg_smul_comp_inv_smul μ _ hr]

/-- The dilation by `1` is the identity. -/
@[simp]
theorem dilateLp_one (f : Lp F p μ) : dilateLp μ 𝕜 p 1 one_pos f = f := by
  apply Lp.ext
  filter_upwards [coeFn_dilateLp (𝕜 := 𝕜) one_pos f] with x hx
  simp [hx]

/-- Dilating by `r * s` is dilating by `s` and then by `r`. -/
theorem dilateLp_mul (hr : 0 < r) (hs : 0 < s) :
    dilateLp (F := F) μ 𝕜 p (r * s) (mul_pos hr hs) =
      (dilateLp μ 𝕜 p s hs).trans (dilateLp μ 𝕜 p r hr) := by
  refine LinearIsometryEquiv.ext fun f ↦ Lp.ext ?_
  filter_upwards [coeFn_dilateLp (𝕜 := 𝕜) (mul_pos hr hs) f,
    coeFn_dilateLp (𝕜 := 𝕜) hr (dilateLp μ 𝕜 p s hs f),
    (quasiMeasurePreserving_smul μ (inv_ne_zero hr.ne')).ae_eq_comp
      (coeFn_dilateLp (𝕜 := 𝕜) hs f)] with x hx hy hz
  simp only [Function.comp_apply] at hz
  rw [hx, LinearIsometryEquiv.trans_apply, hy, hz]
  simp only [smul_smul, Real.mul_rpow hr.le hs.le, mul_inv_rev]

/-- The inverse of the dilation by `r` is the dilation by `r⁻¹`. -/
@[simp]
theorem dilateLp_symm (hr : 0 < r) :
    (dilateLp (F := F) μ 𝕜 p r hr).symm = dilateLp μ 𝕜 p r⁻¹ (inv_pos.2 hr) := by
  refine LinearIsometryEquiv.ext fun f ↦ (dilateLp μ 𝕜 p r hr).injective ?_
  rw [LinearIsometryEquiv.apply_symm_apply, ← LinearIsometryEquiv.trans_apply, ← dilateLp_mul]
  simp only [mul_inv_cancel₀ hr.ne', dilateLp_one]

end MeasureTheory.Measure
