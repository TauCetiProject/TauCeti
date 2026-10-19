/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.GeodesicIntegral.Basic
import TauCeti.Analysis.Complex.UpperHalfPlane.Primitive
import TauCeti.NumberTheory.ModularForms.Basic
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.Cusps.ModularGroup
import TauCeti.NumberTheory.ModularForms.Primitive

/-!
# Integrals along geodesics between cusps, and their additivity

For `F : ℍ → ℂ` and cusps `a, b ∈ ℙ¹(ℚ)`, this file defines the integral
`TauCeti.cuspIntegral F a b = ∫_a^b F(z) dz` of the one-form `F(z) dz` along the hyperbolic
geodesic from `a` to `b`: it is the geodesic integral `g.geodesicIntegral F` of
`TauCeti.NumberTheory.ModularForms.GeodesicIntegral.Basic` for any rational matrix `g` of positive
determinant with `g • 0 = a` and `g • ∞ = b`, which only depends on the endpoints.

The main result is **additivity**, `∫_a^b F(z) dz + ∫_b^c F(z) dz = ∫_a^c F(z) dz`: Cauchy's
theorem for the ideal triangle with vertices `a`, `b`, `c`, all three of which lie on the boundary.
It holds for holomorphic `F` whose weight-`2` slashes `F ∣[2] g` by rational matrices of positive
determinant are integrable near `i∞` along the imaginary axis and tend to `0` at `i∞` uniformly on
vertical strips; the period integrand `f(z) P(z, 1)` of a cusp form satisfies both conditions
(`TauCeti.NumberTheory.ModularForms.ModularSymbols.Period.Integral`). The proof uses a primitive `Φ`
of `F` on `ℍ` (`TauCeti.Analysis.Complex.UpperHalfPlane.Primitive`), whose composite with `g` is a
primitive of `F ∣[2] g`. The first condition gives `Φ` a limit at each cusp along each geodesic
ending there; the second shows that the limit at a cusp does not depend on the geodesic, since
after moving the cusp to `i∞` two such geodesics become vertical lines, joined by horizontal
segments on which `F ∣[2] g` is uniformly small. Each geodesic integral is then the difference of
the values of `Φ` at its endpoints, and additivity follows.

Additivity is what makes the periods of a cusp form a function of degree-zero divisors on the
cusps, the first step of the period pairing between cusp forms and modular symbols.

The same primitive also computes integrals from a point `τ ∈ ℍ` to `i∞` along the vertical ray
`z = τ + i t`, as its limit at `i∞` minus its value at `τ`. Comparing this with its values at the
cusps gives the substitution `z ↦ g • z` in such an integral: the image of the vertical ray from
`τ` ends at the cusp `g • ∞`, and is replaced by the vertical ray from `g • τ` followed by the
geodesic from `i∞` to `g • ∞`. This is how the Eichler integral `∫_τ^{i∞} f(z) (z - τ)ⁿ dz` of a
cusp form transforms under `SL(2, ℤ)` up to periods.

## Main definitions

* `TauCeti.cuspIntegral F a b`: the integral `∫_a^b F(z) dz` along the geodesic from the cusp `a`
  to the cusp `b`.

## Main results

* `TauCeti.cuspIntegral_smul_zero_smul_infty`: `∫_{g • 0}^{g • ∞} F(z) dz = g.geodesicIntegral F`.
* `TauCeti.cuspIntegral_same`, `TauCeti.cuspIntegral_symm`: `∫_a^a = 0` and `∫_b^a = -∫_a^b`.
* `TauCeti.cuspIntegral_slash`: the substitution `z ↦ γ • z`,
  `∫_a^b (F ∣[2] γ)(z) dz = ∫_{γ • a}^{γ • b} F(z) dz`.
* `TauCeti.cuspIntegral_zero`, `TauCeti.cuspIntegral_smul`: the integral of `0` vanishes, and the
  integral is homogeneous under scalar multiplication of the integrand.
* `TauCeti.cuspIntegral_add`, `TauCeti.cuspIntegral_sum`: additivity in the integrand, for
  integrands that are integrable along the geodesic.
* `TauCeti.cuspIntegral_add_adjacent`: additivity, `∫_a^b + ∫_b^c = ∫_a^c`.
* `TauCeti.integral_Ioi_slash_eq_add_cuspIntegral`: the substitution `z ↦ g • z` in an integral
  from a point of `ℍ` to `i∞`,
  `∫_τ^{i∞} (F ∣[2] g)(z) dz = ∫_{g • τ}^{i∞} F(z) dz + ∫_{i∞}^{g • ∞} F(z) dz`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §8.2.
* Y. I. Manin, *Parabolic points and zeta functions of modular curves*, Izv. Akad. Nauk SSSR
  Ser. Mat. **36** (1972), 19–66, §1.
-/

public section

open Complex Filter MeasureTheory Set Topology Matrix Matrix.GeneralLinearGroup
  Matrix.SpecialLinearGroup ModularGroup OnePoint
open UpperHalfPlane hiding I
open scoped Manifold MatrixGroups ModularForm

namespace TauCeti

/-! ### Primitives on the upper half-plane -/

section Primitive

variable {F : ℍ → ℂ} {Φ : ℂ → ℂ}

/-- The derivative of a primitive along the line `s ↦ z₀ + w s`. -/
private theorem hasDerivAt_line {Ψ : ℂ → ℂ} {G : ℍ → ℂ} (hΨ : ∀ τ : ℍ, HasDerivAt Ψ (G τ) τ)
    (z₀ w : ℂ) {t : ℝ} (ht : 0 < (z₀ + w * t).im) :
    HasDerivAt (fun s : ℝ ↦ Ψ (z₀ + w * s)) (G (ofComplex (z₀ + w * t)) * w) t := by
  have h := (hΨ ⟨z₀ + w * t, ht⟩).comp_of_eq (t : ℂ)
    (((hasDerivAt_id (t : ℂ)).const_mul w).const_add z₀) rfl
  rw [ofComplex_apply_of_im_pos ht]
  simpa using h.comp_ofReal

/-- A holomorphic function on `ℍ` has a primitive, the wedge integral from `i`. -/
private theorem exists_primitive (hF : MDiff F) : ∃ Φ : ℂ → ℂ, ∀ τ : ℍ, HasDerivAt Φ (F τ) τ :=
  ⟨fun w ↦ wedgeIntegral (UpperHalfPlane.I : ℂ) w (F ∘ ofComplex), fun τ ↦ by
    simpa [ofComplex_apply] using (UpperHalfPlane.mdifferentiable_iff.mp hF)
      |>.hasDerivAt_wedgeIntegral_upperHalfPlane UpperHalfPlane.I τ.2⟩

end Primitive

/-! ### Limits of a primitive at `i∞` -/

section Limits

variable {Ψ : ℂ → ℂ} {G : ℍ → ℂ}

/-- A primitive of `G` has a limit at `i∞` along the imaginary axis when the restriction of `G`
to the axis is integrable near `i∞`. -/
private theorem tendsto_limUnder_I_mul (hΨ : ∀ τ : ℍ, HasDerivAt Ψ (G τ) τ)
    (hG : IntegrableOn (resToImagAxis G) (Ici 1)) :
    Tendsto (fun t : ℝ ↦ Ψ (I * t)) atTop (𝓝 (limUnder atTop fun t : ℝ ↦ Ψ (I * t))) := by
  refine tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi (a := 1)
    (f' := fun t ↦ resToImagAxis G t * I) (fun t ht ↦ ?_)
    (Integrable.mul_const (hG.mono_set Ioi_subset_Ici_self) I)
  have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
  have h := hasDerivAt_line hΨ 0 I (t := t) (by simpa using ht0)
  rw [resToImagAxis_of_pos _ ht0, ← ofComplex_apply_of_im_pos (by simpa using ht0)]
  simpa using h

/-- **The limit at `i∞` does not depend on the vertical line.** If `G` tends to `0` at `i∞`
uniformly on vertical strips, then the values of a primitive of `G` on two vertical lines at the
same height become close: the difference is the integral of `G` over a horizontal segment. -/
private theorem tendsto_sub_vertical (hΨ : ∀ τ : ℍ, HasDerivAt Ψ (G τ) τ) (hGc : Continuous G)
    (hdecay : ∀ a b : ℝ, Tendsto G (atImInfty ⊓ 𝓟 {τ | τ.re ∈ Icc a b}) (𝓝 0)) (x : ℝ) :
    Tendsto (fun t : ℝ ↦ Ψ (x + I * t) - Ψ (I * t)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ := ε / (|x| + 1) with hδ_def
  have hδ : 0 < δ := by positivity
  have h1 := Metric.tendsto_nhds.mp (hdecay (min 0 x) (max 0 x)) δ hδ
  rw [eventually_inf_principal] at h1
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp h1
  filter_upwards [eventually_gt_atTop (max A 0)] with t ht
  have ht0 : 0 < t := (le_max_right _ _).trans_lt ht
  have hmem (s : ℝ) : 0 < (I * t + s : ℂ).im := by simpa using ht0
  -- the difference is the integral of `G` along the horizontal segment at height `t`
  have hFTC : ∫ s in (0 : ℝ)..x, G ⟨I * t + s, hmem s⟩ = Ψ (x + I * t) - Ψ (I * t) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s : ℝ ↦ Ψ (I * t + 1 * s))]
    · simp [add_comm]
    · intro s _
      have h := hasDerivAt_line hΨ (I * t) 1 (t := s) (by simpa using hmem s)
      rw [ofComplex_apply_of_im_pos (by simpa using hmem s)] at h
      simpa using h
    · have hc : Continuous fun s : ℝ ↦ (I * t + s : ℂ) := by fun_prop
      exact (hGc.comp (hc.upperHalfPlaneMk hmem)).intervalIntegrable _ _
  rw [dist_zero_right, ← hFTC]
  calc ‖∫ s in (0 : ℝ)..x, G ⟨I * t + s, hmem s⟩‖ ≤ δ * |x - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs ↦ ?_
        have := hA ⟨I * t + s, hmem s⟩ (by simpa using (le_max_left _ _).trans ht.le)
          (by simpa [uIcc] using Ioc_subset_Icc_self hs)
        rw [dist_zero_right] at this
        exact this.le
    _ < ε := by
        rw [sub_zero, hδ_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg x]

end Limits

/-! ### Values of a primitive at the cusps -/

section CuspValues

variable {F : ℍ → ℂ} {Φ : ℂ → ℂ}

/-- Composing with `S` keeps the determinant. -/
private theorem det_mul_mapGL_S_pos {g : GL (Fin 2) ℚ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) :
    0 < ((g * mapGL ℚ S : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
  rwa [Units.val_mul, Matrix.det_mul, ← Matrix.GeneralLinearGroup.val_det_apply (mapGL ℚ S),
    det_mapGL, Units.val_one, mul_one]

/-- The limit of `Φ` at the cusp `g • ∞` along the image under `g` of the imaginary axis. -/
private noncomputable def axisLimit (Φ : ℂ → ℂ) (g : GL (Fin 2) ℚ) : ℂ :=
  limUnder atTop fun t : ℝ ↦
    Φ (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g • ofComplex (I * t) : ℍ)

/-- The composite of a primitive of `F` with a rational matrix `g` of positive determinant has a
limit at `i∞` along the imaginary axis, which is `axisLimit Φ g`. -/
private theorem tendsto_axisLimit (hΦ : ∀ τ : ℍ, HasDerivAt Φ (F τ) τ) {g : GL (Fin 2) ℚ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det)
    (hint : IntegrableOn (resToImagAxis (F ∣[(2 : ℤ)] g)) (Ici 1)) :
    Tendsto (fun t : ℝ ↦
      Φ (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g • ofComplex (I * t) : ℍ)) atTop
      (𝓝 (axisLimit Φ g)) :=
  tendsto_limUnder_I_mul (hasDerivAt_comp_smul hΦ (ModularForm.det_map_ratCast_pos hg)) hint

/-- **The value of a primitive at a cusp is well defined.** Two rational matrices of positive
determinant sending `∞` to the same cusp give the same limit: they differ by an upper triangular
matrix, which carries the imaginary axis to a rescaled vertical line, and on vertical lines the
limits agree by `tendsto_sub_vertical`. -/
private theorem axisLimit_eq_of_smul_infty_eq (hΦ : ∀ τ : ℍ, HasDerivAt Φ (F τ) τ)
    (hF : MDiff F)
    (hint : ∀ g : GL (Fin 2) ℚ, 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det →
      IntegrableOn (resToImagAxis (F ∣[(2 : ℤ)] g)) (Ici 1))
    (hdecay : ∀ g : GL (Fin 2) ℚ, 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det → ∀ a b : ℝ,
      Tendsto (F ∣[(2 : ℤ)] g) (atImInfty ⊓ 𝓟 {τ | τ.re ∈ Icc a b}) (𝓝 0))
    {g g' : GL (Fin 2) ℚ} (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det)
    (hg' : 0 < (g' : Matrix (Fin 2) (Fin 2) ℚ).det) (h : g • (∞ : OnePoint ℚ) = g' • ∞) :
    axisLimit Φ g' = axisLimit Φ g := by
  -- `u = g⁻¹ g'` fixes `∞`, so it is upper triangular with a positive diagonal ratio
  set u := g⁻¹ * g' with hu
  have hg'u : g' = g * u := by rw [hu, mul_inv_cancel_left]
  have hu10 : u 1 0 = 0 :=
    OnePoint.smul_infty_eq_self_iff.mp (by rw [hu, mul_smul, ← h, inv_smul_smul])
  have hdet : 0 < (u : Matrix (Fin 2) (Fin 2) ℚ).det := by
    have hmem : u ∈ GLPos (Fin 2) ℚ :=
      Subgroup.mul_mem _
        (Subgroup.inv_mem _ ((mem_glpos g).mpr (by rwa [Matrix.GeneralLinearGroup.val_det_apply])))
        ((mem_glpos g').mpr (by rwa [Matrix.GeneralLinearGroup.val_det_apply]))
    rw [mem_glpos, Matrix.GeneralLinearGroup.val_det_apply] at hmem
    exact hmem
  have hdet' : 0 < u 0 0 * u 1 1 := by
    rw [Matrix.det_fin_two, hu10] at hdet
    simpa using hdet
  have hu11 : u 1 1 ≠ 0 := fun h0 ↦ by simp [h0] at hdet'
  set x : ℝ := ((u 0 1 / u 1 1 : ℚ) : ℝ) with hx
  set r : ℝ := ((u 0 0 / u 1 1 : ℚ) : ℝ) with hr_def
  have hr : 0 < r := by
    rw [hr_def, Rat.cast_pos]
    exact div_pos_iff.mpr (mul_pos_iff.mp hdet')
  -- `u` sends `i t` to `x + i r t`
  have hsmul (t : ℝ) (ht : 0 < t) :
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g' • ofComplex (I * t) : ℍ) =
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g • ofComplex (x + I * (r * t : ℝ)) := by
    have hrt : 0 < (x + I * (r * t : ℝ) : ℂ).im := by simpa using mul_pos hr ht
    rw [hg'u, map_mul, mul_smul]
    congr 1
    ext1
    rw [coe_smul_of_det_pos (ModularForm.det_map_ratCast_pos hdet),
      ofComplex_apply_of_im_pos (by simpa using ht), ofComplex_apply_of_im_pos hrt]
    simp only [num, denom, Matrix.GeneralLinearGroup.map_apply, eq_ratCast, hu10, hx, hr_def,
      Rat.cast_zero, Rat.cast_div]
    rw [Complex.ofReal_zero, zero_mul, zero_add]
    push_cast
    field_simp
    ring
  have hΨ := hasDerivAt_comp_smul hΦ (ModularForm.det_map_ratCast_pos hg)
  have hshift := tendsto_sub_vertical hΨ ((hF.slash 2 _).continuous) (hdecay g hg) x
  have hlim := tendsto_axisLimit hΦ hg (hint g hg)
  have hrt : Tendsto (fun t : ℝ ↦ r * t) atTop atTop := tendsto_id.const_mul_atTop hr
  refine Tendsto.limUnder_eq ((((hshift.comp hrt).add (hlim.comp hrt))).congr' ?_ |>.trans ?_)
  · filter_upwards [eventually_gt_atTop 0] with t ht
    simp [hsmul t ht]
  · simp

/-- **The geodesic integral as a difference of values of a primitive.** For `g` of positive
determinant, the integral of `F(z) dz` from `g • 0` to `g • ∞` is the limit of the primitive at
`g • ∞` minus its limit at `g • 0`, the latter read along the reversed axis through `g S`. -/
private theorem geodesicIntegral_eq_axisLimit_sub (hΦ : ∀ τ : ℍ, HasDerivAt Φ (F τ) τ)
    (hint : ∀ g : GL (Fin 2) ℚ, 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det →
      IntegrableOn (resToImagAxis (F ∣[(2 : ℤ)] g)) (Ici 1))
    {g : GL (Fin 2) ℚ} (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) :
    g.geodesicIntegral F = axisLimit Φ g - axisLimit Φ (g * mapGL ℚ S) := by
  have hgS := det_mul_mapGL_S_pos hg
  set h : ℝ → ℂ := fun t ↦
    Φ (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g • ofComplex (I * t) : ℍ) with h_def
  -- the derivative of `h` is `i` times the integrand
  have hderiv (t : ℝ) (ht : 0 < t) :
      HasDerivAt h (resToImagAxis (F ∣[(2 : ℤ)] g) t * I) t := by
    have h' := hasDerivAt_line (hasDerivAt_comp_smul hΦ (ModularForm.det_map_ratCast_pos hg))
      0 I (t := t) (by simpa using ht)
    rw [resToImagAxis_of_pos _ ht, ← ofComplex_apply_of_im_pos (by simpa using ht)]
    simp only [zero_add] at h'
    exact h'
  -- integrability along the whole axis, from both ends
  have hint₀ : IntegrableOn (resToImagAxis (F ∣[(2 : ℤ)] g)) (Ioi 0) := by
    refine integrableOn_resToImagAxis_Ioi_of_slash_S (hint g hg) ?_
    have := hint _ hgS
    rwa [SlashAction.slash_mul, ModularForm.rat_slash_mapGL,
      ← TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← ModularForm.SL_slash] at this
  -- the limit at the finite end `g • 0` is the limit at `i∞` for `g S`
  have hlim₀ : Tendsto h (𝓝[>] 0) (𝓝 (axisLimit Φ (g * mapGL ℚ S))) := by
    refine ((tendsto_axisLimit hΦ hgS (hint _ hgS)).comp tendsto_inv_nhdsGT_zero).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hS_smul : (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (mapGL ℚ S) •
        ofComplex (I * (t⁻¹ : ℝ)) : ℍ) = ofComplex (I * t) := by
      rw [Matrix.SpecialLinearGroup.map_mapGL, ← TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL,
        ← sl_moeb, modular_S_smul]
      ext1
      rw [ofComplex_apply_of_im_pos (by simpa using ht),
        ofComplex_apply_of_im_pos (by simpa using inv_pos.mpr ht)]
      have : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
      push_cast
      field_simp
      rw [Complex.I_sq]
    simp only [Function.comp_apply, h_def, map_mul, mul_smul, hS_smul]
  -- the fundamental theorem of calculus on `(0, ∞)`
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0)
    (f := Function.update h 0 (axisLimit Φ (g * mapGL ℚ S)))
    (by rw [continuousWithinAt_update_same, Ici_sdiff_left]; exact hlim₀)
    (fun t (ht : 0 < t) ↦ (hderiv t ht).congr_of_eventuallyEq
      (by filter_upwards [eventually_ne_nhds ht.ne'] with s hs using
        Function.update_of_ne hs _ _))
    (Integrable.mul_const hint₀ I)
    ((tendsto_axisLimit hΦ hg (hint g hg)).congr' (by
      filter_upwards [eventually_ne_atTop 0] with s hs using
        (Function.update_of_ne hs (axisLimit Φ (g * mapGL ℚ S)) h).symm))
  rw [Function.update_self, integral_mul_const] at hFTC
  rw [geodesicIntegral_def, mul_comm, hFTC]

end CuspValues

/-! ### Integrals between cusps -/

open scoped Classical in
/-- The integral `∫_a^b F(z) dz` of the one-form `F(z) dz` along the hyperbolic geodesic from the
cusp `a` to the cusp `b` of `ℙ¹(ℚ)`. For `a ≠ b` it is `g.geodesicIntegral F` for any rational
matrix `g` of positive determinant with `g • 0 = a` and `g • ∞ = b`, the choice not mattering
(`cuspIntegral_smul_zero_smul_infty`); for `a = b` it is `0`. Both endpoints are improper, and,
as for `Matrix.GeneralLinearGroup.geodesicIntegral`, the value is `0` when the integrand is not
integrable. -/
noncomputable def cuspIntegral (F : ℍ → ℂ) (a b : OnePoint ℚ) : ℂ :=
  if h : ∃ g : GL (Fin 2) ℚ, 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det ∧
      g • ((0 : ℚ) : OnePoint ℚ) = a ∧ g • (∞ : OnePoint ℚ) = b then
    h.choose.geodesicIntegral F
  else 0

/-- The integral between the cusps `g • 0` and `g • ∞` is the geodesic integral along `g`. -/
theorem cuspIntegral_smul_zero_smul_infty (F : ℍ → ℂ) {g : GL (Fin 2) ℚ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) :
    cuspIntegral F (g • ((0 : ℚ) : OnePoint ℚ)) (g • ∞) = g.geodesicIntegral F := by
  have h : ∃ g' : GL (Fin 2) ℚ, 0 < (g' : Matrix (Fin 2) (Fin 2) ℚ).det ∧
      g' • ((0 : ℚ) : OnePoint ℚ) = g • ((0 : ℚ) : OnePoint ℚ) ∧ g' • (∞ : OnePoint ℚ) = g • ∞ :=
    ⟨g, hg, rfl, rfl⟩
  rw [cuspIntegral, dite_eq_left h]
  obtain ⟨hg', h₀, hinf⟩ := h.choose_spec
  exact geodesicIntegral_eq_of_smul_eq hg' hg h₀ hinf F

/-- The integral from a cusp to itself vanishes. -/
@[simp]
theorem cuspIntegral_same (F : ℍ → ℂ) (a : OnePoint ℚ) : cuspIntegral F a a = 0 := by
  rw [cuspIntegral, dite_eq_right ?_]
  rintro ⟨g, -, h₀, hinf⟩
  exact OnePoint.coe_ne_infty _ (smul_left_cancel g (h₀.trans hinf.symm))

/-- Reversing the orientation changes the sign: `∫_b^a F(z) dz = -∫_a^b F(z) dz`. -/
theorem cuspIntegral_symm (F : ℍ → ℂ) (a b : OnePoint ℚ) :
    cuspIntegral F b a = -cuspIntegral F a b := by
  rcases eq_or_ne a b with rfl | hab
  · simp
  obtain ⟨g, hg, rfl, rfl⟩ := exists_smul_zero_smul_infty hab
  have h₀ : (g * mapGL ℚ S) • ((0 : ℚ) : OnePoint ℚ) = g • ∞ := by
    rw [mul_smul, mapGL_S_smul_zero]
  have hinf : (g * mapGL ℚ S) • (∞ : OnePoint ℚ) = g • ((0 : ℚ) : OnePoint ℚ) := by
    rw [mul_smul, mapGL_S_smul_infty]
  rw [cuspIntegral_smul_zero_smul_infty F hg, ← h₀, ← hinf,
    cuspIntegral_smul_zero_smul_infty F (det_mul_mapGL_S_pos hg), geodesicIntegral_mul_S]

/-- **The substitution `z ↦ γ • z`**: for `γ` of positive determinant, the integral of the
pulled-back one-form `(F ∣[2] γ)(z) dz` from `a` to `b` is the integral of `F(z) dz` from `γ • a`
to `γ • b`. -/
theorem cuspIntegral_slash (F : ℍ → ℂ) {γ : GL (Fin 2) ℚ}
    (hγ : 0 < (γ : Matrix (Fin 2) (Fin 2) ℚ).det) (a b : OnePoint ℚ) :
    cuspIntegral (F ∣[(2 : ℤ)] γ) a b = cuspIntegral F (γ • a) (γ • b) := by
  rcases eq_or_ne a b with rfl | hab
  · simp
  obtain ⟨g, hg, rfl, rfl⟩ := exists_smul_zero_smul_infty hab
  have hγg : 0 < ((γ * g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [Units.val_mul, Matrix.det_mul]
    exact mul_pos hγ hg
  rw [← mul_smul, ← mul_smul, cuspIntegral_smul_zero_smul_infty _ hg,
    cuspIntegral_smul_zero_smul_infty _ hγg, geodesicIntegral_mul]

/-- The integral between cusps is homogeneous under scalar multiplication of the integrand:
`∫_a^b c F(z) dz = c ∫_a^b F(z) dz`. Additivity in the integrand needs integrability, and holds
under the hypotheses of `TauCeti.cuspIntegral_add`. -/
theorem cuspIntegral_smul (c : ℂ) (F : ℍ → ℂ) (a b : OnePoint ℚ) :
    cuspIntegral (c • F) a b = c * cuspIntegral F a b := by
  rcases eq_or_ne a b with rfl | hab
  · simp
  obtain ⟨g, hg, rfl, rfl⟩ := exists_smul_zero_smul_infty hab
  rw [cuspIntegral_smul_zero_smul_infty _ hg, cuspIntegral_smul_zero_smul_infty _ hg,
    geodesicIntegral_smul hg]

/-- The integral of the zero integrand between two cusps vanishes. -/
@[simp]
theorem cuspIntegral_zero (a b : OnePoint ℚ) : cuspIntegral (0 : ℍ → ℂ) a b = 0 := by
  simpa only [zero_smul, zero_mul] using cuspIntegral_smul 0 (0 : ℍ → ℂ) a b

/-- The integral between the cusps `g • 0` and `g • ∞` is additive in the integrand when both
integrands are integrable along the geodesic `g`. -/
theorem cuspIntegral_add {F G : ℍ → ℂ} {g : GL (Fin 2) ℚ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det)
    (hF : IntegrableOn (resToImagAxis (F ∣[(2 : ℤ)] g)) (Ioi 0))
    (hG : IntegrableOn (resToImagAxis (G ∣[(2 : ℤ)] g)) (Ioi 0)) :
    cuspIntegral (F + G) (g • ((0 : ℚ) : OnePoint ℚ)) (g • ∞) =
      cuspIntegral F (g • ((0 : ℚ) : OnePoint ℚ)) (g • ∞) +
        cuspIntegral G (g • ((0 : ℚ) : OnePoint ℚ)) (g • ∞) := by
  rw [cuspIntegral_smul_zero_smul_infty _ hg, cuspIntegral_smul_zero_smul_infty _ hg,
    cuspIntegral_smul_zero_smul_infty _ hg, geodesicIntegral_add g hF hG]

/-- The integral between the cusps `g • 0` and `g • ∞` commutes with finite sums of integrands
that are integrable along the geodesic `g`. -/
theorem cuspIntegral_sum {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ} {g : GL (Fin 2) ℚ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det)
    (hF : ∀ i ∈ s, IntegrableOn (resToImagAxis (F i ∣[(2 : ℤ)] g)) (Ioi 0)) :
    cuspIntegral (∑ i ∈ s, F i) (g • ((0 : ℚ) : OnePoint ℚ)) (g • ∞) =
      ∑ i ∈ s, cuspIntegral (F i) (g • ((0 : ℚ) : OnePoint ℚ)) (g • ∞) := by
  have hres : resToImagAxis ((∑ i ∈ s, F i) ∣[(2 : ℤ)] g) =
      ∑ i ∈ s, resToImagAxis (F i ∣[(2 : ℤ)] g) := by
    funext t
    rcases le_or_gt t 0 with ht | ht <;> simp [resToImagAxis_of_pos, resToImagAxis_of_nonpos, ht]
  simp only [cuspIntegral_smul_zero_smul_infty _ hg, geodesicIntegral_def, hres, Finset.sum_apply]
  rw [integral_finsetSum s hF, Finset.mul_sum]

/-- **The values of a primitive at the cusps.** Under the hypotheses of
`TauCeti.cuspIntegral_add_adjacent`, a primitive `Φ` of `F` has a value `V x` at each cusp `x`,
its limit along any geodesic ending at `x`, and every integral between cusps is the difference of
these values at its endpoints. -/
private theorem exists_cuspValue {F : ℍ → ℂ} {Φ : ℂ → ℂ} (hΦ : ∀ τ : ℍ, HasDerivAt Φ (F τ) τ)
    (hF : MDiff F)
    (hint : ∀ g : GL (Fin 2) ℚ, 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det →
      IntegrableOn (resToImagAxis (F ∣[(2 : ℤ)] g)) (Ici 1))
    (hdecay : ∀ g : GL (Fin 2) ℚ, 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det → ∀ a b : ℝ,
      Tendsto (F ∣[(2 : ℤ)] g) (atImInfty ⊓ 𝓟 {τ | τ.re ∈ Icc a b}) (𝓝 0)) :
    ∃ V : OnePoint ℚ → ℂ,
      (∀ g : GL (Fin 2) ℚ, 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det → axisLimit Φ g = V (g • ∞)) ∧
        ∀ x y : OnePoint ℚ, cuspIntegral F x y = V y - V x := by
  -- the value `V x` of the primitive at a cusp `x`, read along any geodesic ending at `x`
  set V : OnePoint ℚ → ℂ := fun x ↦ axisLimit Φ (mapGL ℚ (OnePoint.exists_mem_SL2 ℤ x).choose)
  have hV (g : GL (Fin 2) ℚ) (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) :
      axisLimit Φ g = V (g • ∞) :=
    (axisLimit_eq_of_smul_infty_eq hΦ hF hint hdecay hg
      (by rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one]; exact one_pos)
      (OnePoint.exists_mem_SL2 ℤ (g • ∞)).choose_spec.symm).symm
  refine ⟨V, hV, fun x y ↦ ?_⟩
  rcases eq_or_ne x y with rfl | hxy
  · simp
  obtain ⟨g, hg, rfl, rfl⟩ := exists_smul_zero_smul_infty hxy
  rw [cuspIntegral_smul_zero_smul_infty F hg, geodesicIntegral_eq_axisLimit_sub hΦ hint hg,
    hV g hg, hV _ (det_mul_mapGL_S_pos hg), mul_smul, mapGL_S_smul_infty]

/-- **Additivity of integrals between cusps**: `∫_a^b F(z) dz + ∫_b^c F(z) dz = ∫_a^c F(z) dz`
for a holomorphic `F` whose weight-`2` slashes by rational matrices of positive determinant are
integrable near `i∞` along the imaginary axis and tend to `0` at `i∞` uniformly on vertical
strips. These are the conditions under which the integrals along the three sides of the ideal
triangle with vertices `a`, `b`, `c` are computed by a primitive `Φ` of `F`: each is the difference
of the limits of `Φ` at its two endpoints, and the limit of `Φ` at a cusp does not depend on the
geodesic along which the cusp is approached. -/
theorem cuspIntegral_add_adjacent {F : ℍ → ℂ} (hF : MDiff F)
    (hint : ∀ g : GL (Fin 2) ℚ, 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det →
      IntegrableOn (resToImagAxis (F ∣[(2 : ℤ)] g)) (Ici 1))
    (hdecay : ∀ g : GL (Fin 2) ℚ, 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det → ∀ a b : ℝ,
      Tendsto (F ∣[(2 : ℤ)] g) (atImInfty ⊓ 𝓟 {τ | τ.re ∈ Icc a b}) (𝓝 0))
    (a b c : OnePoint ℚ) :
    cuspIntegral F a b + cuspIntegral F b c = cuspIntegral F a c := by
  obtain ⟨Φ, hΦ⟩ := exists_primitive hF
  obtain ⟨V, -, key⟩ := exists_cuspValue hΦ hF hint hdecay
  rw [key, key, key]
  ring

/-! ### Integrals from a point of `ℍ` to `i∞` -/

/-- The integral of `G(z) dz` along the vertical ray from `τ` to `i∞` is the difference of the
limit `L` of a primitive `Ψ` at `i∞` and its value at `τ`, when `G` is integrable along the ray
and tends to `0` at `i∞` uniformly on vertical strips, so that the limit of `Ψ` along the ray is
its limit `L` along the imaginary axis. -/
private theorem integral_Ioi_eq_sub {Ψ : ℂ → ℂ} {G : ℍ → ℂ}
    (hΨ : ∀ τ : ℍ, HasDerivAt Ψ (G τ) τ) (hGc : Continuous G)
    (hdecay : ∀ a b : ℝ, Tendsto G (atImInfty ⊓ 𝓟 {τ | τ.re ∈ Icc a b}) (𝓝 0)) {L : ℂ}
    (hL : Tendsto (fun t : ℝ ↦ Ψ (I * t)) atTop (𝓝 L)) (τ : ℍ)
    (hray : IntegrableOn (fun t : ℝ ↦ G (ofComplex (τ + t * I))) (Ioi 0)) :
    ∫ t in Ioi (0 : ℝ), G (ofComplex (τ + t * I)) * I = L - Ψ τ := by
  have hpos (t : ℝ) (ht : 0 ≤ t) : 0 < ((τ : ℂ) + I * t).im := by
    simpa using add_pos_of_pos_of_nonneg τ.im_pos ht
  -- along the ray, `Ψ` tends to its limit along the imaginary axis
  have hlim : Tendsto (fun s : ℝ ↦ Ψ (τ + I * s)) atTop (𝓝 L) := by
    have hshift := (tendsto_sub_vertical hΨ hGc hdecay τ.re).comp
      (tendsto_atTop_add_const_left atTop τ.im tendsto_id)
    refine (by simpa using hshift.add (hL.comp
      (tendsto_atTop_add_const_left atTop τ.im tendsto_id)) :
        Tendsto (fun s : ℝ ↦ Ψ (τ.re + I * (τ.im + s : ℝ))) atTop (𝓝 L)).congr fun s ↦ ?_
    congr 1
    apply Complex.ext <;> simp
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (f := fun s : ℝ ↦ Ψ (τ + I * s)) (f' := fun t : ℝ ↦ G (ofComplex (τ + t * I)) * I)
    (fun t ht ↦ by simpa [mul_comm I] using hasDerivAt_line hΨ τ I (hpos t ht))
    (hray.mul_const I) hlim
  simpa using h

/-- **The substitution `z ↦ g • z` in an integral from a point of `ℍ` to `i∞`.** For `g` a
rational matrix of positive determinant and `τ ∈ ℍ`,

`∫_τ^{i∞} (F ∣[2] g)(z) dz = ∫_{g • τ}^{i∞} F(z) dz + ∫_{i∞}^{g • ∞} F(z) dz`,

the integrals from `τ` and from `g • τ` taken along the vertical rays `z = τ + i t` and
`z = g • τ + i t`, `t > 0`, and the last along the geodesic between the two cusps. The left side
is the integral of `F(z) dz` along the image under `g` of the vertical ray from `τ`, which ends at
the cusp `g • ∞`, and the identity is Cauchy's theorem for the triangle with vertices `g • τ`,
`g • ∞` and `i∞`. The hypotheses on `F` are those of `TauCeti.cuspIntegral_add_adjacent`, and
the two vertical integrands are assumed integrable. -/
theorem integral_Ioi_slash_eq_add_cuspIntegral {F : ℍ → ℂ} (hF : MDiff F)
    (hint : ∀ g : GL (Fin 2) ℚ, 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det →
      IntegrableOn (resToImagAxis (F ∣[(2 : ℤ)] g)) (Ici 1))
    (hdecay : ∀ g : GL (Fin 2) ℚ, 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det → ∀ a b : ℝ,
      Tendsto (F ∣[(2 : ℤ)] g) (atImInfty ⊓ 𝓟 {τ | τ.re ∈ Icc a b}) (𝓝 0))
    {g : GL (Fin 2) ℚ} (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) (τ : ℍ)
    (hτ : IntegrableOn (fun t : ℝ ↦ (F ∣[(2 : ℤ)] g) (ofComplex (τ + t * I))) (Ioi 0))
    (hgτ : IntegrableOn (fun t : ℝ ↦
      F (ofComplex ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g • τ : ℍ) + t * I))) (Ioi 0)) :
    ∫ t in Ioi (0 : ℝ), (F ∣[(2 : ℤ)] g) (ofComplex (τ + t * I)) * I =
      (∫ t in Ioi (0 : ℝ),
        F (ofComplex ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g • τ : ℍ) + t * I)) * I) +
        cuspIntegral F ∞ (g • ∞) := by
  obtain ⟨Φ, hΦ⟩ := exists_primitive hF
  obtain ⟨V, hV, key⟩ := exists_cuspValue hΦ hF hint hdecay
  have h1 : 0 < ((1 : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by simp
  -- the vertical ray from `g • τ`, through the primitive `Φ` of `F`
  have hlim₁ : Tendsto (fun t : ℝ ↦ Φ (I * t)) atTop (𝓝 (axisLimit Φ 1)) := by
    refine (tendsto_axisLimit hΦ h1 (hint 1 h1)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [map_one, one_smul, ofComplex_apply_of_im_pos (by simpa using ht)]
  have hF₁ := integral_Ioi_eq_sub hΦ hF.continuous
    (by simpa only [SlashAction.slash_one] using hdecay 1 h1) hlim₁ _ hgτ
  -- the vertical ray from `τ`, through the primitive `Φ ∘ g` of `F ∣[2] g`
  have hFg := integral_Ioi_eq_sub (G := F ∣[(2 : ℤ)] g)
    (hasDerivAt_comp_smul hΦ (ModularForm.det_map_ratCast_pos hg))
    (hF.slash 2 _).continuous (hdecay g hg) (tendsto_axisLimit hΦ hg (hint g hg)) τ hτ
  rw [ofComplex_apply] at hFg
  rw [hFg, hF₁, key, ← hV g hg, ← one_smul (GL (Fin 2) ℚ) (∞ : OnePoint ℚ), ← hV 1 h1]
  ring

end TauCeti
