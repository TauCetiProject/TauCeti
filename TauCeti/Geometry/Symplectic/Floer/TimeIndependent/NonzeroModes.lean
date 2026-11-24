/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator
public import TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Linearization
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.IntervalIntegral.Slice
import TauCeti.Analysis.Fourier.Wirtinger
import TauCeti.Analysis.InnerProductSpace.CompleteSquare
import TauCeti.Geometry.Symplectic.CompatibleMetric
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The nonzero Fourier modes of the linearized operator along a time-independent cylinder

Let `(V, ω)` be a symplectic vector space whose inner product is the metric `g = ω(·, J ·)` of a
constant compatible almost complex structure `J`. Along a time-independent cylinder
`u(s, t) = γ(s)` of an autonomous Hamiltonian `H`, the linearized Floer operator is

`D ξ = ∂s ξ + J (∂t ξ - dX_H(γ(s)) ξ)`

(`TauCeti.SymplecticForm.floerLinearization_const_eq`), and its slice average is the Morse operator
`M ζ = ζ' - J dX_H(γ) ζ` applied to the slice average `ξbar(s) = ∫₀¹ ξ(s, t) dt`
(`TauCeti.SymplecticForm.intervalIntegral_floerLinearization_comp_fst`): the zero Fourier mode of
`D` is `M`. This file proves the matching statement for the other modes, as an `L²` estimate over
rectangles `[s₀, s₁] × [0, 1]` for maps of period one in `t` that vanish on the two boundary slices
`s = s₀` and `s = s₁`. If `‖dX_H(γ(s))‖ ≤ a ≤ 2π`, the nonzero modes have the spectral gap `2π`
of `J ∂t` minus `a`, and the whole estimate for `D` reduces to the estimate for `M`.

* **The Cauchy–Riemann operator.** For such a map,
  `∫ ‖∂s ξ + J ∂t ξ‖² = ∫ (‖∂s ξ‖² + ‖∂t ξ‖²)`
  (`TauCeti.SymplecticForm.setIntegral_norm_fderiv_add_apply_fderiv_sq`): the cross term
  integrates to zero. This is the energy identity of the stationary cylinder operator
  (`TauCeti.Floer.setIntegral_associatedBilinForm_stationaryCylinderOperator`) for `S = 0`.
* **The gap on the nonzero modes.** If moreover every slice `t ↦ ξ(s, t)` has mean zero, and
  `f` is any square-integrable map with `‖∂s ξ + J ∂t ξ - f‖ ≤ a ‖ξ‖` for some `0 ≤ a ≤ 2π`, then
  `(2π - a)² ∫ ‖ξ‖² ≤ ∫ ‖f‖²` and `(2π - a)² ∫ (‖∂s ξ‖² + ‖∂t ξ‖²) ≤ (2π)² ∫ ‖f‖²`
  (`TauCeti.SymplecticForm.mul_setIntegral_norm_sq_le_of_norm_sub_le`,
  `TauCeti.SymplecticForm.mul_setIntegral_norm_fderiv_sq_add_le_of_norm_sub_le`). Wirtinger's
  inequality on the mean-zero slices gives `(2π)² ∫ ‖ξ‖² ≤ ∫ ‖∂t ξ‖²`
  (`TauCeti.mul_setIntegral_norm_sq_le_setIntegral_norm_fderiv_sq`), and the zeroth-order term
  costs at most `a`. Applied to `f = D ξ` this is the estimate of `D` on the nonzero modes
  (`TauCeti.SymplecticForm.mul_setIntegral_norm_sq_le_setIntegral_norm_floerLinearization_sq`, and
  `mul_setIntegral_norm_fderiv_sq_add_le_setIntegral_norm_floerLinearization_sq` in the same
  namespace for the derivatives).
  No bound on the second derivative of `X_H` or on `γ'` is needed, and `γ` need only be continuous.
* **Splitting off the zero mode.** For a `C¹` map `ξ` of period one in `t` and a `C²`
  Hamiltonian, `∫ ‖D ξ‖² = ∫ₛ ‖M ξbar‖² + ∫ ‖D (ξ - ξbar)‖²`
  (`TauCeti.SymplecticForm.setIntegral_norm_floerLinearization_sq_eq`), since the slice average of
  `D ξ` is `M ξbar` and `D (ξ - ξbar) = D ξ - M ξbar` has mean-zero slices
  (`TauCeti.setIntegral_norm_add_sq_eq`). Consequently, if `a < 2π`, an `L²` estimate
  `∫ ‖ζ‖² ≤ K ∫ ‖M ζ‖²` for the Morse operator on curves vanishing at `s₀` and `s₁` gives
  `∫ ‖ξ‖² ≤ max K (2π - a)⁻² ∫ ‖D ξ‖²` for the linearized Floer operator on maps vanishing on the
  two boundary slices
  (`TauCeti.SymplecticForm.setIntegral_norm_sq_le_max_mul_setIntegral_norm_floerLinearization_sq`).
  Conversely an estimate for `D` restricts to the same estimate for `M` on maps that do not depend
  on `t` (`TauCeti.SymplecticForm.setIntegral_norm_sq_le_mul_setIntegral_norm_deriv_sub_sq`), so `D`
  satisfies an `L²` estimate on such a rectangle exactly when `M` does.

These are the a priori estimates which, on the Sobolev completion, reduce the injectivity and closed
range of `D` along a time-independent cylinder to those of the Morse operator, the step of the
identification of the Floer cylinders of a small Morse Hamiltonian with its gradient lines that
concerns the linearized operator. The Sobolev realization itself and the surjectivity of `D` are not
treated here.

## References

* A. Floer, *Witten's complex and infinite dimensional Morse theory*, J. Differential Geom.
  **30** (1989), 207–221.
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360, on the linearized operator at
  time-independent solutions of a small Hamiltonian.
-/

public section

open Real Set MeasureTheory ContinuousLinearMap
open scoped RealInnerProductSpace

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {ξ : ℝ × ℝ → V} {s₀ s₁ : ℝ}

section CauchyRiemann

/-- **The Cauchy–Riemann energy identity.** If the inner product of `V` is the metric `ω(·, J ·)`
and `ξ` is a `C²` map of period one in `t` vanishing on the slices `s = s₀` and `s = s₁`, then
`∫ ‖∂s ξ + J ∂t ξ‖² = ∫ (‖∂s ξ‖² + ‖∂t ξ‖²)` over `[s₀, s₁] × [0, 1]`. -/
theorem setIntegral_norm_fderiv_add_apply_fderiv_sq (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hξ : ContDiff ℝ 2 ξ) (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (hs : s₀ ≤ s₁)
    (h₀ : ∀ t, ξ (s₀, t) = 0) (h₁ : ∀ t, ξ (s₁, t) = 0) :
    ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖fderiv ℝ ξ z (1, 0) + J (fderiv ℝ ξ z (0, 1))‖ ^ 2 =
      ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, (‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) := by
  have hid := Floer.setIntegral_associatedBilinForm_stationaryCylinderOperator (ω := ω)
    (J := fun _ ↦ J) (S := fun _ ↦ 0) (fun _ ↦ ω.invariant_of_apply_apply_eq_inner hg)
    (J.toLinearMap.toContinuousLinearMap.continuous.comp continuous_snd) (by simp)
    continuous_const hξ hper hs
  simpa only [Floer.stationaryCylinderOperator_def, associatedBilinForm_apply, hg,
    real_inner_self_eq_norm_sq, zero_apply, sub_zero, h₀, h₁, map_zero,
    intervalIntegral.integral_zero, add_zero, stdComplexLineReal_eq, stdComplexLineImag_eq]
    using hid

/-- The three integrated inequalities behind the estimate on the nonzero modes: for
`p = ∂s ξ + J ∂t ξ`, the integrals `X = ∫ ‖ξ‖²`, `Z = ∫ ‖p‖²` and `Y = ∫ ‖f‖²` satisfy
`(1 - a / 2π) Z - (2π - a) a X ≤ Y`, `(2π)² X ≤ Z` and `0 ≤ X`. -/
private theorem setIntegral_le_of_norm_sub_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a ≤ 2 * π) (hξ : ContDiff ℝ 2 ξ) (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t))
    (hmean : ∀ s, ∫ t in (0 : ℝ)..1, ξ (s, t) = 0) (hs : s₀ ≤ s₁) (h₀ : ∀ t, ξ (s₀, t) = 0)
    (h₁ : ∀ t, ξ (s₁, t) = 0) {f : ℝ × ℝ → V}
    (hf : IntegrableOn (fun z ↦ ‖f z‖ ^ 2) (Icc s₀ s₁ ×ˢ Icc 0 1))
    (hfξ : ∀ z ∈ Icc s₀ s₁ ×ˢ Icc 0 1,
      ‖fderiv ℝ ξ z (1, 0) + J (fderiv ℝ ξ z (0, 1)) - f z‖ ≤ a * ‖ξ z‖) :
    (1 - a / (2 * π)) * (∫ z in Icc s₀ s₁ ×ˢ Icc 0 1,
        (‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2)) -
        (2 * π - a) * a * ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 ≤
      ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖f z‖ ^ 2 ∧
    (2 * π) ^ 2 * ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 ≤
      ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, (‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) ∧
    0 ≤ ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 := by
  have hd := hξ.continuous_fderiv two_ne_zero
  have hds : Continuous fun z ↦ fderiv ℝ ξ z (1, 0) := hd.clm_apply continuous_const
  have hdt : Continuous fun z ↦ fderiv ℝ ξ z (0, 1) := hd.clm_apply continuous_const
  have hX : IntegrableOn (fun z ↦ ‖ξ z‖ ^ 2) (Icc s₀ s₁ ×ˢ Icc 0 1) :=
    (hξ.continuous.norm.pow 2).integrableOn_Icc_prod_Icc
  have hS : IntegrableOn (fun z ↦ ‖fderiv ℝ ξ z (1, 0)‖ ^ 2) (Icc s₀ s₁ ×ˢ Icc 0 1) :=
    (hds.norm.pow 2).integrableOn_Icc_prod_Icc
  have hT : IntegrableOn (fun z ↦ ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) (Icc s₀ s₁ ×ˢ Icc 0 1) :=
    (hdt.norm.pow 2).integrableOn_Icc_prod_Icc
  have hP : IntegrableOn (fun z ↦ ‖fderiv ℝ ξ z (1, 0) + J (fderiv ℝ ξ z (0, 1))‖ ^ 2)
      (Icc s₀ s₁ ×ˢ Icc 0 1) :=
    ((hds.add (J.toLinearMap.toContinuousLinearMap.continuous.comp hdt)).norm.pow 2)
      |>.integrableOn_Icc_prod_Icc
  -- Pointwise, `(1 - a / 2π) ‖p‖² - (2π - a) a ‖ξ‖² ≤ ‖f‖²` for `p = ∂s ξ + J ∂t ξ`.
  have hL : IntegrableOn (fun z ↦ (1 - a / (2 * π)) *
      ‖fderiv ℝ ξ z (1, 0) + J (fderiv ℝ ξ z (0, 1))‖ ^ 2 - (2 * π - a) * a * ‖ξ z‖ ^ 2)
      (Icc s₀ s₁ ×ˢ Icc 0 1) :=
    (hP.const_mul _).sub (hX.const_mul _)
  have hpt := setIntegral_mono_on hL hf (measurableSet_Icc.prod measurableSet_Icc) fun z hz ↦ by
    simpa only [sub_sub_cancel] using one_sub_div_mul_norm_sq_sub_le_norm_sub_sq ha0 ha
      (p := fderiv ℝ ξ z (1, 0) + J (fderiv ℝ ξ z (0, 1))) (hfξ z hz)
  rw [integral_sub (hP.const_mul _) (hX.const_mul _), integral_const_mul, integral_const_mul,
    setIntegral_norm_fderiv_add_apply_fderiv_sq hg hξ hper hs h₀ h₁] at hpt
  refine ⟨hpt, ?_, setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc)
    fun _ _ ↦ by positivity⟩
  -- Wirtinger on the slices, and `0 ≤ ∫ ‖∂s ξ‖²`.
  have hW := mul_setIntegral_norm_sq_le_setIntegral_norm_fderiv_sq (a₁ := s₀) (b₁ := s₁)
    zero_lt_one (hξ.of_le one_le_two) (fun s ↦ by simpa using (hper s 0).symm) hmean
  rw [sub_zero, div_one] at hW
  refine hW.trans ?_
  rw [integral_add hS hT]
  exact le_add_of_nonneg_left (setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc)
    fun _ _ ↦ by positivity)

/-- **The `L²` gap on the nonzero Fourier modes.** Let the inner product of `V` be the metric
`ω(·, J ·)`, and let `ξ` be a `C²` map of period one in `t`, vanishing on the slices `s = s₀` and
`s = s₁`, whose slices `t ↦ ξ(s, t)` all have mean zero. If `f` is square integrable on
`[s₀, s₁] × [0, 1]` and differs from `∂s ξ + J ∂t ξ` by at most `a ‖ξ‖` there, with
`0 ≤ a ≤ 2π`, then `(2π - a)² ∫ ‖ξ‖² ≤ ∫ ‖f‖²`. -/
theorem mul_setIntegral_norm_sq_le_of_norm_sub_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a ≤ 2 * π) (hξ : ContDiff ℝ 2 ξ) (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t))
    (hmean : ∀ s, ∫ t in (0 : ℝ)..1, ξ (s, t) = 0) (hs : s₀ ≤ s₁) (h₀ : ∀ t, ξ (s₀, t) = 0)
    (h₁ : ∀ t, ξ (s₁, t) = 0) {f : ℝ × ℝ → V}
    (hf : IntegrableOn (fun z ↦ ‖f z‖ ^ 2) (Icc s₀ s₁ ×ˢ Icc 0 1))
    (hfξ : ∀ z ∈ Icc s₀ s₁ ×ˢ Icc 0 1,
      ‖fderiv ℝ ξ z (1, 0) + J (fderiv ℝ ξ z (0, 1)) - f z‖ ≤ a * ‖ξ z‖) :
    (2 * π - a) ^ 2 * ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 ≤
      ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖f z‖ ^ 2 := by
  obtain ⟨h₁, h₂, hX⟩ := setIntegral_le_of_norm_sub_le hg ha0 ha hξ hper hmean hs h₀ h₁ hf hfξ
  have hπ : 0 < 2 * π := by positivity
  have hb : 0 ≤ 2 * π - a := sub_nonneg.2 ha
  have hc : 1 - a / (2 * π) = (2 * π - a) / (2 * π) := by field_simp
  rw [hc] at h₁
  have h₃ := mul_le_mul_of_nonneg_left h₂ (div_nonneg hb hπ.le)
  have h₄ : (2 * π - a) / (2 * π) * ((2 * π) ^ 2 * ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖ξ z‖ ^ 2) =
      (2 * π - a) * (2 * π) * ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 := by
    field_simp
  nlinarith

/-- **The `W^{1,2}` gap on the nonzero Fourier modes.** Under the hypotheses of
`TauCeti.SymplecticForm.mul_setIntegral_norm_sq_le_of_norm_sub_le`, the derivatives of `ξ` are
controlled as well: `(2π - a)² ∫ (‖∂s ξ‖² + ‖∂t ξ‖²) ≤ (2π)² ∫ ‖f‖²`. -/
theorem mul_setIntegral_norm_fderiv_sq_add_le_of_norm_sub_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 2 * π) (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (hmean : ∀ s, ∫ t in (0 : ℝ)..1, ξ (s, t) = 0)
    (hs : s₀ ≤ s₁) (h₀ : ∀ t, ξ (s₀, t) = 0) (h₁ : ∀ t, ξ (s₁, t) = 0) {f : ℝ × ℝ → V}
    (hf : IntegrableOn (fun z ↦ ‖f z‖ ^ 2) (Icc s₀ s₁ ×ˢ Icc 0 1))
    (hfξ : ∀ z ∈ Icc s₀ s₁ ×ˢ Icc 0 1,
      ‖fderiv ℝ ξ z (1, 0) + J (fderiv ℝ ξ z (0, 1)) - f z‖ ≤ a * ‖ξ z‖) :
    (2 * π - a) ^ 2 * ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1,
        (‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) ≤
      (2 * π) ^ 2 * ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖f z‖ ^ 2 := by
  have hgap := mul_setIntegral_norm_sq_le_of_norm_sub_le hg ha0 ha hξ hper hmean hs h₀ h₁ hf hfξ
  obtain ⟨h₁, -, hX⟩ := setIntegral_le_of_norm_sub_le hg ha0 ha hξ hper hmean hs h₀ h₁ hf hfξ
  have hπ : 0 < 2 * π := by positivity
  have hb : 0 ≤ 2 * π - a := sub_nonneg.2 ha
  have hc : 1 - a / (2 * π) = (2 * π - a) / (2 * π) := by field_simp
  rw [hc] at h₁
  -- Multiply by `2π (2π - a)` and use the `L²` gap `(2π - a)² X ≤ Y`.
  set Z := ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, (‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2)
  set X := ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖ξ z‖ ^ 2
  set Y := ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖f z‖ ^ 2
  have h₂ : (2 * π - a) * Z - (2 * π) * ((2 * π - a) * a * X) ≤ 2 * π * Y := by
    have := mul_le_mul_of_nonneg_left h₁ hπ.le
    rwa [mul_sub, ← mul_assoc, mul_div_cancel₀ _ hπ.ne'] at this
  have h₃ := mul_le_mul_of_nonneg_left h₂ hb
  nlinarith [mul_le_mul_of_nonneg_left hgap (mul_nonneg hπ.le ha0)]

end CauchyRiemann

section TimeIndependent

variable {H : V → ℝ} {γ : ℝ → V}

/-- Along a continuous curve `γ`, the linearized operator of a `C²` autonomous Hamiltonian maps
`C¹` maps to continuous maps. -/
private theorem continuous_floerLinearization_comp_fst (hH : ContDiff ℝ 2 H) (hγ : Continuous γ)
    (hξ : ContDiff ℝ 1 ξ) :
    Continuous (ω.floerLinearization (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1) ξ) := by
  have hd := hξ.continuous_fderiv one_ne_zero
  have hX : Continuous (fderiv ℝ (ω.hamiltonianVectorField H)) :=
    (ω.contDiff_hamiltonianVectorField (n := 1) hH).continuous_fderiv one_ne_zero
  have h : Continuous fun z : ℝ × ℝ ↦ fderiv ℝ ξ z (1, 0) +
      J (fderiv ℝ ξ z (0, 1) - fderiv ℝ (ω.hamiltonianVectorField H) (γ z.1) (ξ z)) :=
    (hd.clm_apply continuous_const).add (J.toLinearMap.toContinuousLinearMap.continuous.comp
      ((hd.clm_apply continuous_const).sub
        ((hX.comp (hγ.comp continuous_fst)).clm_apply hξ.continuous)))
  convert h using 1
  exact funext fun z ↦ floerLinearization_const_eq ω J H _ ξ z

/-- Along a continuous curve `γ`, the Morse operator `ζ ↦ ζ' - J dX_H(γ) ζ` of a `C²` autonomous
Hamiltonian maps `C¹` curves to continuous curves. -/
private theorem continuous_deriv_sub_fderiv_hamiltonianVectorField (hH : ContDiff ℝ 2 H)
    (hγ : Continuous γ) {ζ : ℝ → V} (hζ : ContDiff ℝ 1 ζ) :
    Continuous fun s ↦ deriv ζ s - J (fderiv ℝ (ω.hamiltonianVectorField H) (γ s) (ζ s)) :=
  (hζ.continuous_deriv le_rfl).sub (J.toLinearMap.toContinuousLinearMap.continuous.comp
    ((((ω.contDiff_hamiltonianVectorField (n := 1) hH).continuous_fderiv one_ne_zero).comp
      hγ).clm_apply hζ.continuous))

/-- The linearized operator along `(s, t) ↦ γ(s)` differs from `∂s ξ + J ∂t ξ` by
`J dX_H(γ(s)) ξ`, of norm at most `a ‖ξ‖` where `‖dX_H(γ(s))‖ ≤ a`. -/
private theorem norm_sub_floerLinearization_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {a : ℝ}
    (haγ : ∀ s ∈ Icc s₀ s₁, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a) :
    ∀ z ∈ Icc s₀ s₁ ×ˢ Icc 0 1, ‖fderiv ℝ ξ z (1, 0) + J (fderiv ℝ ξ z (0, 1)) -
      ω.floerLinearization (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun _ ↦ H) (fun z ↦ γ z.1) ξ z‖ ≤ a * ‖ξ z‖ := by
  intro z hz
  rw [floerLinearization_const_eq, map_sub, add_sub_add_left_eq_sub, sub_sub_cancel,
    ω.norm_apply_eq_norm_of_apply_apply_self_eq_inner fun v ↦ hg v v]
  exact ((fderiv ℝ (ω.hamiltonianVectorField H) (γ z.1)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (haγ z.1 hz.1) (norm_nonneg _))

/-- **The gap on the nonzero modes along a time-independent cylinder.** Let the inner product of
`V` be the metric `ω(·, J ·)`, let `H` be a `C²` autonomous Hamiltonian and `γ` a continuous curve
with `‖dX_H(γ(s))‖ ≤ a ≤ 2π` for `s ∈ [s₀, s₁]`. If `ξ` is a `C²` map of period one in `t`,
vanishing on the slices `s = s₀` and `s = s₁`, whose slices all have mean zero, then the linearized
Floer operator `D ξ = ∂s ξ + J (∂t ξ - dX_H(γ(s)) ξ)` along `(s, t) ↦ γ(s)` satisfies
`(2π - a)² ∫ ‖ξ‖² ≤ ∫ ‖D ξ‖²` over `[s₀, s₁] × [0, 1]`. -/
theorem mul_setIntegral_norm_sq_le_setIntegral_norm_floerLinearization_sq
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ}
    (ha : a ≤ 2 * π)
    (haγ : ∀ s ∈ Icc s₀ s₁, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    (hξ : ContDiff ℝ 2 ξ) (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t))
    (hmean : ∀ s, ∫ t in (0 : ℝ)..1, ξ (s, t) = 0) (hs : s₀ ≤ s₁) (h₀ : ∀ t, ξ (s₀, t) = 0)
    (h₁ : ∀ t, ξ (s₁, t) = 0) :
    (2 * π - a) ^ 2 * ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 ≤
      ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖ω.floerLinearization
        (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ ↦ H)
        (fun z ↦ γ z.1) ξ z‖ ^ 2 :=
  mul_setIntegral_norm_sq_le_of_norm_sub_le hg ((norm_nonneg _).trans (haγ s₀ ⟨le_rfl, hs⟩)) ha
    hξ hper hmean hs h₀ h₁
    ((continuous_floerLinearization_comp_fst hH hγ (hξ.of_le one_le_two)).norm.pow 2
      |>.integrableOn_Icc_prod_Icc)
    (norm_sub_floerLinearization_le hg haγ)

/-- **The `W^{1,2}` gap on the nonzero modes along a time-independent cylinder.** Under the
hypotheses of
`TauCeti.SymplecticForm.mul_setIntegral_norm_sq_le_setIntegral_norm_floerLinearization_sq`, the
derivatives of `ξ` are controlled as well:
`(2π - a)² ∫ (‖∂s ξ‖² + ‖∂t ξ‖²) ≤ (2π)² ∫ ‖D ξ‖²`. -/
theorem mul_setIntegral_norm_fderiv_sq_add_le_setIntegral_norm_floerLinearization_sq
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ}
    (ha : a ≤ 2 * π)
    (haγ : ∀ s ∈ Icc s₀ s₁, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    (hξ : ContDiff ℝ 2 ξ) (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t))
    (hmean : ∀ s, ∫ t in (0 : ℝ)..1, ξ (s, t) = 0) (hs : s₀ ≤ s₁) (h₀ : ∀ t, ξ (s₀, t) = 0)
    (h₁ : ∀ t, ξ (s₁, t) = 0) :
    (2 * π - a) ^ 2 * ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1,
        (‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) ≤
      (2 * π) ^ 2 * ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖ω.floerLinearization
        (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ ↦ H)
        (fun z ↦ γ z.1) ξ z‖ ^ 2 :=
  mul_setIntegral_norm_fderiv_sq_add_le_of_norm_sub_le hg
    ((norm_nonneg _).trans (haγ s₀ ⟨le_rfl, hs⟩)) ha hξ hper hmean hs h₀ h₁
    ((continuous_floerLinearization_comp_fst hH hγ (hξ.of_le one_le_two)).norm.pow 2
      |>.integrableOn_Icc_prod_Icc)
    (norm_sub_floerLinearization_le hg haγ)

/-- **Splitting off the zero mode.** Let `H` be a `C²` autonomous Hamiltonian and `γ` a
continuous curve, and let `ξ` be a `C¹` map of period one in `t`, with slice average
`ξbar(s) = ∫₀¹ ξ(s, t) dt`. Over `[s₀, s₁] × [0, 1]` the squared `L²` norm of the linearized Floer
operator `D ξ = ∂s ξ + J (∂t ξ - dX_H(γ(s)) ξ)` along `(s, t) ↦ γ(s)` is the sum of the squared
norm of the Morse operator `ξbar' - J dX_H(γ) ξbar` on the zero mode and that of `D` on the
mean-zero part `ξ - ξbar`. -/
theorem setIntegral_norm_floerLinearization_sq_eq (hH : ContDiff ℝ 2 H) (hγ : Continuous γ)
    (hξ : ContDiff ℝ 1 ξ) (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) :
    ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖ω.floerLinearization
        (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ ↦ H)
        (fun z ↦ γ z.1) ξ z‖ ^ 2 =
      (∫ s in Icc s₀ s₁, ‖deriv (fun s ↦ ∫ t in (0 : ℝ)..1, ξ (s, t)) s -
          J (fderiv ℝ (ω.hamiltonianVectorField H) (γ s) (∫ t in (0 : ℝ)..1, ξ (s, t)))‖ ^ 2) +
        ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖ω.floerLinearization
          (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ ↦ H)
          (fun z ↦ γ z.1) (fun z ↦ ξ z - ∫ t in (0 : ℝ)..1, ξ (z.1, t)) z‖ ^ 2 := by
  set D := ω.floerLinearization (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
    (fun _ ↦ H) (fun z ↦ γ z.1)
  set ξbar : ℝ → V := fun s ↦ ∫ t in (0 : ℝ)..1, ξ (s, t)
  set m : ℝ → V := fun s ↦
    deriv ξbar s - J (fderiv ℝ (ω.hamiltonianVectorField H) (γ s) (ξbar s))
  have hbar : ContDiff ℝ 1 ξbar := hξ.parametric_intervalIntegral (μ := volume)
  have hm : Continuous m := continuous_deriv_sub_fderiv_hamiltonianVectorField hH hγ hbar
  have hDξ : Continuous (D ξ) := continuous_floerLinearization_comp_fst hH hγ hξ
  have hsplit (z : ℝ × ℝ) : D ξ z = m z.1 + D (fun z ↦ ξ z - ξbar z.1) z :=
    eq_add_of_sub_eq' (floerLinearization_sub_intervalIntegral (ω := ω) (J := J) (H := H)
      γ hξ z).symm
  have hη (z : ℝ × ℝ) : D (fun z ↦ ξ z - ξbar z.1) z = D ξ z - m z.1 := by
    rw [hsplit z, add_sub_cancel_left]
  -- The slices of `D (ξ - ξbar) = D ξ - m` have integral zero, by the zero-mode identity.
  have hw0 (s : ℝ) : ∫ t in Icc (0 : ℝ) 1, D (fun z ↦ ξ z - ξbar z.1) (s, t) = 0 := by
    have h0 : ∫ t in (0 : ℝ)..1, D ξ (s, t) = m s :=
      intervalIntegral_floerLinearization_comp_fst (ω := ω) (J := J) (H := H) γ hξ hper s
    simp_rw [hη, ← h0]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    simpa only [interval_average_eq, sub_zero, inv_one, one_smul] using
      intervalIntegral_sub_intervalAverage (fun t ↦ D ξ (s, t)) 0 1
  have hw : Continuous (D (fun z ↦ ξ z - ξbar z.1)) := by
    rw [funext hη]
    exact hDξ.sub (hm.comp continuous_fst)
  simp_rw [hsplit]
  simpa only [sub_zero, one_mul] using setIntegral_norm_add_sq_eq zero_le_one hm hw hw0

/-- **The estimate of the linearized operator reduces to the Morse operator.** Let the inner
product of `V` be the metric `ω(·, J ·)`, let `H` be a `C²` autonomous Hamiltonian and `γ` a
continuous curve with `‖dX_H(γ(s))‖ ≤ a < 2π` for `s ∈ [s₀, s₁]`, and suppose that the Morse
operator `M ζ = ζ' - J dX_H(γ) ζ` satisfies `∫ ‖ζ‖² ≤ K ∫ ‖M ζ‖²` over `[s₀, s₁]` for every `C²`
curve `ζ` vanishing at `s₀` and `s₁`. Then every `C²` map `ξ` of period one in `t` vanishing on the
slices `s = s₀` and `s = s₁` satisfies `∫ ‖ξ‖² ≤ max K (2π - a)⁻² ∫ ‖D ξ‖²` over
`[s₀, s₁] × [0, 1]`, for the linearized Floer operator `D` along `(s, t) ↦ γ(s)`. -/
theorem setIntegral_norm_sq_le_max_mul_setIntegral_norm_floerLinearization_sq
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a K : ℝ}
    (ha : a < 2 * π)
    (haγ : ∀ s ∈ Icc s₀ s₁, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    (hM : ∀ ζ : ℝ → V, ContDiff ℝ 2 ζ → ζ s₀ = 0 → ζ s₁ = 0 →
      ∫ s in Icc s₀ s₁, ‖ζ s‖ ^ 2 ≤ K * ∫ s in Icc s₀ s₁,
        ‖deriv ζ s - J (fderiv ℝ (ω.hamiltonianVectorField H) (γ s) (ζ s))‖ ^ 2)
    (hξ : ContDiff ℝ 2 ξ) (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (hs : s₀ ≤ s₁)
    (h₀ : ∀ t, ξ (s₀, t) = 0) (h₁ : ∀ t, ξ (s₁, t) = 0) :
    ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 ≤
      max K ((2 * π - a) ^ 2)⁻¹ * ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖ω.floerLinearization
        (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ ↦ H)
        (fun z ↦ γ z.1) ξ z‖ ^ 2 := by
  set ξbar : ℝ → V := fun s ↦ ∫ t in (0 : ℝ)..1, ξ (s, t)
  set η : ℝ × ℝ → V := fun z ↦ ξ z - ξbar z.1
  have hbar : ContDiff ℝ 2 ξbar := hξ.parametric_intervalIntegral (μ := volume)
  have hη : ContDiff ℝ 2 η := hξ.sub (hbar.comp contDiff_fst)
  have hbar₀ : ξbar s₀ = 0 := by simp [ξbar, h₀]
  have hbar₁ : ξbar s₁ = 0 := by simp [ξbar, h₁]
  have hηmean (s : ℝ) : ∫ t in (0 : ℝ)..1, η (s, t) = 0 := by
    simpa only [interval_average_eq, sub_zero, inv_one, one_smul] using
      intervalIntegral_sub_intervalAverage (fun t ↦ ξ (s, t)) 0 1
  -- `∫ ‖ξ‖² = ∫ ‖ξbar‖² + ∫ ‖η‖²`, the zero mode and the mean-zero part.
  have hnorm : ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 =
      (∫ s in Icc s₀ s₁, ‖ξbar s‖ ^ 2) + ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖η z‖ ^ 2 := by
    have h := setIntegral_norm_add_sq_eq (a₁ := s₀) (b₁ := s₁) zero_le_one hbar.continuous
      hη.continuous
      fun s ↦ by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
        exact hηmean s
    simpa only [η, add_sub_cancel, sub_zero, one_mul] using h
  have hgap := mul_setIntegral_norm_sq_le_setIntegral_norm_floerLinearization_sq hg hH hγ ha.le
    haγ hη (fun s t ↦ by simp only [η, hper]) hηmean hs (fun t ↦ by simp [η, h₀, hbar₀])
    (fun t ↦ by simp [η, h₁, hbar₁])
  have hmorse := hM ξbar hbar hbar₀ hbar₁
  rw [setIntegral_norm_floerLinearization_sq_eq hH hγ (hξ.of_le one_le_two) hper, hnorm]
  -- Combine the two estimates, both of whose right sides are nonnegative.
  have hb : 0 < (2 * π - a) ^ 2 := by
    have : 0 < 2 * π - a := sub_pos.2 ha
    positivity
  have hX : ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖η z‖ ^ 2 ≤ ((2 * π - a) ^ 2)⁻¹ *
      ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖ω.floerLinearization
        (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ ↦ H)
        (fun z ↦ γ z.1) η z‖ ^ 2 := by
    rw [← div_eq_inv_mul, le_div_iff₀' hb]
    exact hgap
  have hA : 0 ≤ ∫ s in Icc s₀ s₁, ‖deriv ξbar s -
      J (fderiv ℝ (ω.hamiltonianVectorField H) (γ s) (ξbar s))‖ ^ 2 :=
    setIntegral_nonneg measurableSet_Icc fun _ _ ↦ by positivity
  have hB : 0 ≤ ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖ω.floerLinearization
      (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ ↦ H)
      (fun z ↦ γ z.1) η z‖ ^ 2 :=
    setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) fun _ _ ↦ by positivity
  rw [mul_add]
  exact add_le_add (hmorse.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hA))
    (hX.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hB))

/-- **The estimate of the Morse operator from that of the linearized operator.** Conversely to
`TauCeti.SymplecticForm.setIntegral_norm_sq_le_max_mul_setIntegral_norm_floerLinearization_sq`,
if the linearized Floer operator `D` along `(s, t) ↦ γ(s)` satisfies `∫ ‖ξ‖² ≤ C ∫ ‖D ξ‖²` over
`[s₀, s₁] × [0, 1]` for every `C²` map `ξ` of period one in `t` vanishing on the slices `s = s₀`
and `s = s₁`, then the Morse operator `M ζ = ζ' - J dX_H(γ) ζ` satisfies `∫ ‖ζ‖² ≤ C ∫ ‖M ζ‖²` over
`[s₀, s₁]` for every `C²` curve `ζ` vanishing at `s₀` and `s₁`: on maps that do not depend on `t`,
`D` is `M`. -/
theorem setIntegral_norm_sq_le_mul_setIntegral_norm_deriv_sub_sq {C : ℝ}
    (hD : ∀ ξ : ℝ × ℝ → V, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      (∀ t, ξ (s₀, t) = 0) → (∀ t, ξ (s₁, t) = 0) →
      ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 ≤ C * ∫ z in Icc s₀ s₁ ×ˢ Icc 0 1,
        ‖ω.floerLinearization (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (fun _ ↦ H) (fun z ↦ γ z.1) ξ z‖ ^ 2)
    {ζ : ℝ → V} (hζ : ContDiff ℝ 2 ζ) (hζ₀ : ζ s₀ = 0) (hζ₁ : ζ s₁ = 0) :
    ∫ s in Icc s₀ s₁, ‖ζ s‖ ^ 2 ≤ C * ∫ s in Icc s₀ s₁,
      ‖deriv ζ s - J (fderiv ℝ (ω.hamiltonianVectorField H) (γ s) (ζ s))‖ ^ 2 := by
  set m : ℝ → V := fun s ↦ deriv ζ s - J (fderiv ℝ (ω.hamiltonianVectorField H) (γ s) (ζ s))
  -- On the map `(s, t) ↦ ζ(s)`, the linearized operator is the Morse operator.
  have hDζ (z : ℝ × ℝ) : ω.floerLinearization (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1) (fun z ↦ ζ z.1) z = m z.1 :=
    floerLinearization_comp_fst_of_hasDerivAt γ ((hζ.differentiable two_ne_zero) z.1).hasDerivAt
  have h := hD (fun z ↦ ζ z.1) (hζ.comp contDiff_fst) (fun _ _ ↦ rfl) (fun _ ↦ hζ₀)
    fun _ ↦ hζ₁
  simp only [hDζ] at h
  -- A function of `s` integrates over `[s₀, s₁] × [0, 1]` to its integral over `[s₀, s₁]`.
  rwa [setIntegral_Icc_prod_comp_fst (fun s ↦ ‖ζ s‖ ^ 2) zero_le_one,
    setIntegral_Icc_prod_comp_fst (fun s ↦ ‖m s‖ ^ 2) zero_le_one, sub_zero, one_smul,
    one_smul] at h

end TimeIndependent

end TauCeti.SymplecticForm
