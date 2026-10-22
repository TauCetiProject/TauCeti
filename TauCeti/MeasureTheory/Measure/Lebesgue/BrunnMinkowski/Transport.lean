/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import TauCeti.Analysis.Convex.Body.Measure
public import TauCeti.Analysis.Convex.Measure
public import TauCeti.Analysis.MeanInequalities
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Section

/-!
# Equality in Brunn–Minkowski and volume distributions along a direction

Let `K` and `L` be convex bodies of the same positive volume `V` in a finite-dimensional real
inner product space, and let `0 < θ < 1`. By the Brunn–Minkowski inequality the convex
combination `M = (1 - θ) • K + θ • L` has volume at least `V`. This file shows that if `M` has
volume at most `V`, so that equality holds, then along every unit vector `e` the volume
distributions of `K` and `L` are translates of each other: there is a real number `c` with

`volume {x ∈ L | ⟪e, x⟫ ≤ t + c} = volume {x ∈ K | ⟪e, x⟫ ≤ t}` for every `t : ℝ`.

The proof is the one-dimensional transport argument of Kneser and Süss. Write `F_K` for the
volume of the part of `K` below height `t` along `e`, and `σ_K(t)` for the volume of the
hyperplane section of `K` at height `t`. For a positive-volume convex body, `F_K` maps the
interval of heights of `K` increasingly onto `[0, V]`, and its inverse `z_K`, the volume
quantile, is differentiable on `(0, V)` with derivative `1 / σ_K(z_K τ)`. The section of `M`
at height `(1 - θ) z_K τ + θ z_L τ` contains the weighted sum of the sections of `K` and `L`
at heights `z_K τ` and `z_L τ`. Changing variables along `τ` and applying the multiplicative
Brunn–Minkowski inequality in the hyperplane gives

`volume M ≥ ∫ τ in (0, V), ((1 - θ) / a τ + θ / b τ) * (a τ ^ (1 - θ) * b τ ^ θ) ≥ V`,

with `a τ = σ_K(z_K τ)` and `b τ = σ_L(z_L τ)`. The second inequality is the weighted
arithmetic–geometric mean inequality, which is strict unless `a τ = b τ`. Equality therefore
forces equal section volumes at equal volume quantiles, so the quantile functions of `K` and
`L` have the same derivative and differ by a constant.

Combined with an identification of centroids, this is the step of the classical proof of
the equality case of the Brunn–Minkowski inequality for convex bodies that compares the bodies
in one direction at a time.

## Main results

* `ConvexBody.exists_forall_volume_sep_inner_le_add_eq`: equality in Brunn–Minkowski for
  convex bodies of equal volume makes their volume distributions along every
  direction translates of each other.

## References

* H. Kneser and W. Süss, *Die Volumina in linearen Scharen konvexer Körper*, Mat. Tidsskr. B
  (1932), 19–25, for the transport argument and the equality case.
* R. J. Gardner, *The Brunn–Minkowski inequality*, Bull. Amer. Math. Soc. **39** (2002),
  355–405, Section 4, for the one-dimensional transport proof of Brunn–Minkowski.
* R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, 2nd ed., Cambridge University
  Press, 2014, Section 7.1, for the equality case and its history (Kneser and Süss).
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise RealInnerProductSpace

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Volume quantiles of a convex body.** For a positive-volume convex body `K` of volume
`V` and a unit vector `e`, the heights of `K` form an interval `[a, b]` with `a < b`, and the
volume below height `t` maps `(a, b)` increasingly onto `(0, V)`. Its inverse `z` is
differentiable on `(0, V)`, with derivative the reciprocal of the positive section volume, and
the section volume along `z` is continuous. -/
private theorem exists_volume_quantile (K : ConvexBody E) (hK : 0 < volume (K : Set E)) {e : E}
    (he : ‖e‖ = 1) :
    ∃ a b : ℝ, ∃ z : ℝ → ℝ, a < b ∧ (∀ x ∈ (K : Set E), ⟪e, x⟫ ∈ Icc a b) ∧
      z '' Ioo 0 (volume.real (K : Set E)) = Ioo a b ∧
      StrictMonoOn z (Ioo 0 (volume.real (K : Set E))) ∧
      ContinuousOn (fun τ ↦ volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + z τ • e ∈ (K : Set E)})
        (Ioo 0 (volume.real (K : Set E))) ∧
      ∀ τ ∈ Ioo 0 (volume.real (K : Set E)),
        volume.real {x ∈ (K : Set E) | ⟪e, x⟫ ≤ z τ} = τ ∧
        0 < volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + z τ • e ∈ (K : Set E)} ∧
        HasDerivAt z (volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + z τ • e ∈ (K : Set E)})⁻¹ τ := by
  obtain ⟨a, b, hab, hI⟩ := K.exists_image_inner_eq_Icc hK he
  set V := volume.real (K : Set E)
  set F : ℝ → ℝ := fun c ↦ volume.real {x ∈ (K : Set E) | ⟪e, x⟫ ≤ c}
  set σ : ℝ → ℝ := fun t ↦ volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ (K : Set E)}
  have hheight (x : E) (hx : x ∈ (K : Set E)) : ⟪e, x⟫ ∈ Icc a b := hI ▸ mem_image_of_mem _ hx
  have hKm := K.isCompact.measurableSet
  have hpos (t : ℝ) (ht : t ∈ Ioo a b) : 0 < σ t :=
    ENNReal.toReal_pos (K.convex.volume_hyperplaneSection_pos
      ((K.convex.addHaar_pos_iff_interior_nonempty (μ := volume)).1 hK) he
      (by rwa [hI, interior_Icc])).ne'
      (K.isCompact.isBounded.volume_hyperplaneSection_lt_top e t).ne
  have hderiv (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt F (σ t) t :=
    K.convex.hasDerivAt_volume_real_sep_inner_le K.isCompact.isBounded hKm he
      (by rwa [hI, interior_Icc])
  have hσcont : ContinuousOn σ (Ioo a b) := by
    have h := K.convex.continuousOn_volume_real_hyperplaneSection he
      fun t ↦ (K.isCompact.isBounded.volume_hyperplaneSection_lt_top e t).ne
    rwa [hI, interior_Icc] at h
  -- `F` is continuous on `[a, b]`, being a primitive of the integrable section volume.
  have hFcont : ContinuousOn F (Icc a b) := by
    have hσint : Integrable σ := integrable_toReal_of_lintegral_ne_top
      (TauCeti.measurable_volume_hyperplaneSection e he hKm).aemeasurable (by
        rw [← TauCeti.volume_eq_lintegral_volume_hyperplaneSection e he hKm.nullMeasurableSet]
        exact K.isCompact.measure_lt_top.ne)
    refine (intervalIntegral.continuous_primitive (fun _ _ ↦ hσint.intervalIntegrable)
      (a - 1)).continuousOn.congr fun c hc ↦ ?_
    exact TauCeti.volume_real_sep_inner_le_eq_integral K.isCompact.isBounded hKm he
      (fun x hx ↦ (sub_one_lt a).trans_le (hheight x hx).1) (by linarith [hc.1])
  have hFa : F a = 0 := by
    have hsub : {x ∈ (K : Set E) | ⟪e, x⟫ ≤ a} ⊆ {x ∈ (K : Set E) | ⟪e, x⟫ = a} :=
      fun x hx ↦ ⟨hx.1, le_antisymm hx.2 (hheight x hx.1).1⟩
    simp only [F]
    rw [measureReal_def,
      measure_mono_null hsub (TauCeti.volume_sep_inner_eq hKm.nullMeasurableSet he a),
      ENNReal.toReal_zero]
  have hFb : F b = V := by
    simp only [F, V]
    congr 1
    exact sep_eq_self_iff_mem_true.2 fun x hx ↦ (hheight x hx).2
  have hFmono : StrictMonoOn F (Icc a b) := strictMonoOn_of_deriv_pos (convex_Icc a b) hFcont
    fun t ht ↦ by
      rw [interior_Icc] at ht
      rw [(hderiv t ht).deriv]
      exact hpos t ht
  -- The inverse of `F` on `(a, b)`.
  have hsurj : Ioo 0 V ⊆ F '' Ioo a b := hFa ▸ hFb ▸ intermediate_value_Ioo hab.le hFcont
  set z := Function.invFunOn F (Ioo a b)
  have hz (τ : ℝ) (hτ : τ ∈ Ioo 0 V) : z τ ∈ Ioo a b ∧ F (z τ) = τ :=
    ⟨Function.invFunOn_mem (hsurj hτ), Function.invFunOn_eq (hsurj hτ)⟩
  have hzmono : StrictMonoOn z (Ioo 0 V) := by
    intro τ hτ τ' hτ' hlt
    by_contra hle
    have := hFmono.monotoneOn (Ioo_subset_Icc_self (hz τ' hτ').1)
      (Ioo_subset_Icc_self (hz τ hτ).1) (not_lt.1 hle)
    rw [(hz τ' hτ').2, (hz τ hτ).2] at this
    exact this.not_gt hlt
  have himage : z '' Ioo 0 V = Ioo a b := by
    refine Subset.antisymm (image_subset_iff.2 fun τ hτ ↦ (hz τ hτ).1) fun t ht ↦ ?_
    have hFt : F t ∈ Ioo 0 V := by
      refine ⟨hFa ▸ hFmono (left_mem_Icc.2 hab.le) (Ioo_subset_Icc_self ht) ht.1,
        hFb ▸ hFmono (Ioo_subset_Icc_self ht) (right_mem_Icc.2 hab.le) ht.2⟩
    exact ⟨F t, hFt, hFmono.injOn (Ioo_subset_Icc_self (hz _ hFt).1) (Ioo_subset_Icc_self ht)
      (hz _ hFt).2⟩
  have hzcont (τ : ℝ) (hτ : τ ∈ Ioo 0 V) : ContinuousAt z τ :=
    hzmono.continuousAt_of_image_mem_nhds (isOpen_Ioo.mem_nhds hτ)
      (himage ▸ isOpen_Ioo.mem_nhds (hz τ hτ).1)
  refine ⟨a, b, z, hab, hheight, himage, hzmono,
    hσcont.comp (fun τ hτ ↦ (hzcont τ hτ).continuousWithinAt) fun τ hτ ↦ (hz τ hτ).1,
    fun τ hτ ↦ ⟨(hz τ hτ).2, hpos _ (hz τ hτ).1, ?_⟩⟩
  exact HasDerivAt.of_local_left_inverse (hzcont τ hτ) (hderiv _ (hz τ hτ).1)
    (hpos _ (hz τ hτ).1).ne' (eventually_of_mem (isOpen_Ioo.mem_nhds hτ) fun τ' hτ' ↦
      (hz τ' hτ').2)

/-- The multiplicative Brunn–Minkowski inequality for hyperplane sections: the section of
`(1 - θ) • K + θ • L` at the weighted height dominates the weighted geometric mean of the
sections of `K` and `L`. -/
private theorem ofReal_mul_le_volume_hyperplaneSection (K L : ConvexBody E) {e : E}
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (s u : ℝ) :
    ENNReal.ofReal (volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + s • e ∈ (K : Set E)} ^ (1 - θ) *
      volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + u • e ∈ (L : Set E)} ^ θ) ≤
      volume {y : (ℝ ∙ e)ᗮ | (y : E) + ((1 - θ) * s + θ * u) • e ∈
        (1 - θ) • (K : Set E) + θ • (L : Set E)} := by
  have hclosed (C : ConvexBody E) (t : ℝ) :
      MeasurableSet {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ (C : Set E)} :=
    (C.isCompact.isClosed.preimage (by fun_prop)).measurableSet
  have hfin (C : ConvexBody E) (t : ℝ) :=
    (C.isCompact.isBounded.volume_hyperplaneSection_lt_top e t).ne
  simp only [measureReal_def]
  rw [ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (sub_pos.2 hθ₁).le,
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hθ₀.le,
    ENNReal.ofReal_toReal (hfin K s), ENNReal.ofReal_toReal (hfin L u)]
  refine (TauCeti.volume_rpow_mul_volume_rpow_le (hclosed K s).nullMeasurableSet
    (hclosed L u).nullMeasurableSet hθ₀ hθ₁).trans (measure_mono ?_)
  rintro _ ⟨_, ⟨y, hy, rfl⟩, _, ⟨y', hy', rfl⟩, rfl⟩
  refine ⟨_, smul_mem_smul_set hy, _, smul_mem_smul_set hy', ?_⟩
  simp only [Submodule.coe_add, Submodule.coe_smul, smul_add, add_smul, mul_smul]
  abel

/-- **Kneser–Süss transport along a direction.** If `K` and `L` are convex bodies of the same
volume and their convex combination `(1 - θ) • K + θ • L` has volume at most that of
`K`, then along every unit vector `e` the volume distributions of `K` and `L` are translates:
the volume of the part of `L` below height `t + c` equals the volume of the part of `K` below
height `t`, for a constant `c` and every `t`. By the Brunn–Minkowski inequality the volume
hypothesis is equivalent to equality. -/
theorem exists_forall_volume_sep_inner_le_add_eq (K L : ConvexBody E)
    (hKL : volume (L : Set E) = volume (K : Set E)) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hM : volume ((1 - θ) • (K : Set E) + θ • (L : Set E)) ≤ volume (K : Set E))
    {e : E} (he : ‖e‖ = 1) :
    ∃ c : ℝ, ∀ t : ℝ,
      volume {x ∈ (L : Set E) | ⟪e, x⟫ ≤ t + c} = volume {x ∈ (K : Set E) | ⟪e, x⟫ ≤ t} := by
  -- Structure: transport `(0, V)` to heights of `M` along the averaged quantile `Z`, bound the
  -- resulting integrand below by `1` using the arithmetic–geometric mean inequality, deduce
  -- equality of section volumes along the quantiles, and integrate the equal derivatives.
  rcases eq_zero_or_pos (volume (K : Set E)) with hK | hK
  · -- For null bodies every part is null.
    exact ⟨0, fun t ↦ by rw [measure_mono_null (sep_subset _ _) hK,
      measure_mono_null (sep_subset _ _) (hKL.trans hK)]⟩
  have hL : 0 < volume (L : Set E) := hKL ▸ hK
  have hV : volume.real (L : Set E) = volume.real (K : Set E) := by
    rw [measureReal_def, measureReal_def, hKL]
  obtain ⟨aK, bK, zK, habK, hhK, himK, hmonoK, hcontK, hzK⟩ := K.exists_volume_quantile hK he
  obtain ⟨aL, bL, zL, habL, hhL, himL, hmonoL, hcontL, hzL⟩ := L.exists_volume_quantile hL he
  rw [hV] at himL hmonoL hcontL hzL
  set V := volume.real (K : Set E) with hVdef
  set σK : ℝ → ℝ := fun τ ↦ volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + zK τ • e ∈ (K : Set E)}
  set σL : ℝ → ℝ := fun τ ↦ volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + zL τ • e ∈ (L : Set E)}
  -- The transport map `Z` and the integrand `g` of the change of variables.
  set Z : ℝ → ℝ := fun τ ↦ (1 - θ) * zK τ + θ * zL τ
  set D : ℝ → ℝ := fun τ ↦ (1 - θ) / σK τ + θ / σL τ
  set g : ℝ → ℝ := fun τ ↦ D τ * (σK τ ^ (1 - θ) * σL τ ^ θ)
  have hZderiv (τ : ℝ) (hτ : τ ∈ Ioo 0 V) : HasDerivAt Z (D τ) τ := by
    convert ((hzK τ hτ).2.2.const_mul (1 - θ)).add ((hzL τ hτ).2.2.const_mul θ) using 1
    simp only [D, σK, σL, div_eq_mul_inv]
  have hZmono : StrictMonoOn Z (Ioo 0 V) := fun τ hτ τ' hτ' hlt ↦
    add_lt_add (mul_lt_mul_of_pos_left (hmonoK hτ hτ' hlt) (sub_pos.2 hθ₁))
      (mul_lt_mul_of_pos_left (hmonoL hτ hτ' hlt) hθ₀)
  have hDpos (τ : ℝ) (hτ : τ ∈ Ioo 0 V) : 0 < D τ := by
    have := (hzK τ hτ).2.1
    have := (hzL τ hτ).2.1
    have : 0 < 1 - θ := sub_pos.2 hθ₁
    positivity
  have hg (τ : ℝ) (hτ : τ ∈ Ioo 0 V) := TauCeti.one_le_div_add_div_mul_rpow_mul_rpow
    (hzK τ hτ).2.1 (hzL τ hτ).2.1 hθ₀ hθ₁
  -- Change of variables: the integral of `g` over `(0, V)` is at most the volume of `M`.
  have hMm : MeasurableSet ((1 - θ) • (K : Set E) + θ • (L : Set E)) :=
    ((K.isCompact.smul _).add (L.isCompact.smul _)).measurableSet
  have hupper : ∫⁻ τ in Ioo 0 V, ENNReal.ofReal (g τ) ≤ ∫⁻ _ in Ioo 0 V, 1 := by
    calc ∫⁻ τ in Ioo 0 V, ENNReal.ofReal (g τ)
        ≤ ∫⁻ τ in Ioo 0 V, ENNReal.ofReal |D τ| * volume {y : (ℝ ∙ e)ᗮ |
            (y : E) + Z τ • e ∈ (1 - θ) • (K : Set E) + θ • (L : Set E)} := by
          refine setLIntegral_mono' measurableSet_Ioo fun τ hτ ↦ ?_
          rw [abs_of_pos (hDpos τ hτ), ENNReal.ofReal_mul (hDpos τ hτ).le]
          gcongr
          exact ofReal_mul_le_volume_hyperplaneSection K L hθ₀ hθ₁ _ _
      _ = ∫⁻ t in Z '' Ioo 0 V, volume {y : (ℝ ∙ e)ᗮ |
            (y : E) + t • e ∈ (1 - θ) • (K : Set E) + θ • (L : Set E)} :=
          (lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
            (fun τ hτ ↦ (hZderiv τ hτ).hasDerivWithinAt) hZmono.injOn (fun t ↦ volume
              {y : (ℝ ∙ e)ᗮ | (y : E) + t • e ∈ (1 - θ) • (K : Set E) + θ • (L : Set E)})).symm
      _ = volume {x ∈ (1 - θ) • (K : Set E) + θ • (L : Set E) | ⟪e, x⟫ ∈ Z '' Ioo 0 V} :=
          (TauCeti.volume_sep_inner_mem_eq_setLIntegral e he hMm.nullMeasurableSet
            (measurableSet_Ioo.image_of_monotoneOn hZmono.monotoneOn)).symm
      _ ≤ volume (K : Set E) := (measure_mono (sep_subset _ _)).trans hM
      _ = ∫⁻ _ in Ioo 0 V, 1 := by
          rw [setLIntegral_const, Real.volume_Ioo, one_mul, sub_zero, hVdef, measureReal_def,
            ENNReal.ofReal_toReal K.isCompact.measure_lt_top.ne]
  -- Hence `g = 1` almost everywhere on `(0, V)`, which forces `σK = σL` there.
  have hgcont : ContinuousOn g (Ioo 0 V) := by
    have hσK0 (τ : ℝ) (hτ : τ ∈ Ioo 0 V) : σK τ ≠ 0 := (hzK τ hτ).2.1.ne'
    have hσL0 (τ : ℝ) (hτ : τ ∈ Ioo 0 V) : σL τ ≠ 0 := (hzL τ hτ).2.1.ne'
    exact ((continuousOn_const.div hcontK hσK0).add (continuousOn_const.div hcontL hσL0)).mul
      ((hcontK.rpow_const fun τ hτ ↦ Or.inl (hσK0 τ hτ)).mul
        (hcontL.rpow_const fun τ hτ ↦ Or.inl (hσL0 τ hτ)))
  have hae : (fun _ ↦ (1 : ℝ≥0∞)) =ᵐ[volume.restrict (Ioo 0 V)] fun τ ↦ ENNReal.ofReal (g τ) :=
    ae_eq_of_ae_le_of_lintegral_le ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _
      fun τ hτ ↦ ENNReal.one_le_ofReal.2 (hg τ hτ).1)) (by simp [Real.volume_Ioo])
      ((ENNReal.continuous_ofReal.comp_continuousOn hgcont).aemeasurable measurableSet_Ioo)
      hupper
  have hσeq : EqOn σK σL (Ioo 0 V) := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_Ioo hcontK hcontL
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with τ hτ hτ'
    exact (hg τ hτ').2 (ENNReal.ofReal_eq_one.1 hτ.symm)
  -- The quantile functions have equal derivatives, so they differ by a constant.
  obtain ⟨c, hc⟩ := isOpen_Ioo.exists_eq_add_of_deriv_eq isPreconnected_Ioo
    (fun τ hτ ↦ (hzL τ hτ).2.2.differentiableAt.differentiableWithinAt)
    (fun τ hτ ↦ (hzK τ hτ).2.2.differentiableAt.differentiableWithinAt)
    (fun τ hτ ↦ by
      rw [(hzL τ hτ).2.2.deriv, (hzK τ hτ).2.2.deriv]
      exact congrArg _ (hσeq hτ).symm)
  -- The extreme heights of `L` are those of `K` shifted by `c`.
  have himc : Ioo aL bL = Ioo (aK + c) (bK + c) := by
    rw [← himL, ← image_add_const_Ioo, ← himK, image_image]
    exact image_congr hc
  have haL : aL = aK + c := by
    rw [← csInf_Ioo habL, himc, csInf_Ioo (by linarith)]
  have hbL : bL = bK + c := by
    rw [← csSup_Ioo habL, himc, csSup_Ioo (by linarith)]
  refine ⟨c, fun t ↦ ?_⟩
  rcases le_or_gt t aK with htK | htK
  · -- Below `K`: both parts are null.
    have hnull (C : ConvexBody E) (a s : ℝ) (hC : ∀ x ∈ (C : Set E), a ≤ ⟪e, x⟫) (hs : s ≤ a) :
        volume {x ∈ (C : Set E) | ⟪e, x⟫ ≤ s} = 0 := by
      have hsub : {x ∈ (C : Set E) | ⟪e, x⟫ ≤ s} ⊆ {x ∈ (C : Set E) | ⟪e, x⟫ = a} :=
        fun x hx ↦ ⟨hx.1, le_antisymm (hx.2.trans hs) (hC x hx.1)⟩
      exact measure_mono_null hsub
        (TauCeti.volume_sep_inner_eq C.isCompact.measurableSet.nullMeasurableSet he a)
    rw [hnull K aK t (fun x hx ↦ (hhK x hx).1) htK,
      hnull L aL (t + c) (fun x hx ↦ (hhL x hx).1) (by linarith)]
  rcases le_or_gt bK t with htK' | htK'
  · -- Above `K`: both parts are the whole bodies.
    rw [sep_eq_self_iff_mem_true.2 fun x hx ↦ (hhK x hx).2.trans htK',
      sep_eq_self_iff_mem_true.2 fun x hx ↦ (hhL x hx).2.trans (by linarith), hKL]
  · -- Inside: compare volume quantiles.
    obtain ⟨τ, hτ, rfl⟩ : t ∈ zK '' Ioo 0 V := himK ▸ ⟨htK, htK'⟩
    have hreal : volume.real {x ∈ (L : Set E) | ⟪e, x⟫ ≤ zK τ + c} =
        volume.real {x ∈ (K : Set E) | ⟪e, x⟫ ≤ zK τ} := by
      have hcτ : zL τ = zK τ + c := hc hτ
      rw [← hcτ, (hzL τ hτ).1, (hzK τ hτ).1]
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top_of_subset (sep_subset _ _)
      L.isCompact.measure_lt_top.ne) (measure_ne_top_of_subset (sep_subset _ _)
      K.isCompact.measure_lt_top.ne)).1 hreal

end ConvexBody
