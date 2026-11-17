/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Plane.Basic
public import TauCeti.Geometry.Symplectic.Floer.Pullback

/-!
# The end charts of the PSS planes in real coordinates

Integrals and differential operators on the PSS planes are written in the real coordinates
`ℝ × ℝ ≃ ℂ` (`Complex.equivRealProdCLM`), where the coordinate formulas of
`TauCeti.Geometry.Symplectic.Floer.Energy` and `TauCeti.Geometry.Symplectic.Floer.Pullback` live.
This file transports the cylindrical end lift `z ↦ exp (2π ε z)` (`p.cylindricalEndLift`) of a PSS
plane `p` to these real coordinates as the end chart `φ_p` (`TauCeti.Floer.PSSPlane.endChart`),
adapting the punctured-surface end-chart interface of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart` to the PSS planes without target-space
restrictions (applicable to both manifold and vector-space targets).

Because `negative.cylindricalEndLift z = positive.cylindricalEndLift (-z)`, the two end charts
satisfy `φ_p(ε • z) = φ_+(z)`, so `φ_+ = positive.endChart` serves as the positive end chart for
both planes. Along `φ_p`, `p.perturbation H` pulls back to `p.endComponent H`; more generally, any
perturbation one-form `K` equal to `H(t) dt` beyond longitudinal height `T₀` on the end of `p`
pulls back along `φ_+` on `{s ≥ T₀}` to `H'_p(t) dt` for the positive-end Hamiltonian
`H'_p(t, x) = ε H(ε t, x)` (`TauCeti.Floer.PSSPlane.positiveEndHamiltonian`).

## Main definitions

* `TauCeti.Floer.PSSPlane.endChart`: the end lift `z ↦ exp (2π ε z)` of a PSS plane in the real
  coordinates `ℝ × ℝ ≃ ℂ`.

## Main results

* `TauCeti.Floer.PSSPlane.hasFDerivAt_endChart`, `TauCeti.Floer.PSSPlane.fderiv_endChart_apply`,
  `TauCeti.Floer.PSSPlane.det_fderiv_endChart_pos`,
  `TauCeti.Floer.PSSPlane.isComplexLinearMap_fderiv_endChart`: the end chart is smooth,
  holomorphic, and orientation-preserving.
* `TauCeti.Floer.PSSPlane.differentiableAt_comp_endChart_iff`,
  `TauCeti.Floer.PSSPlane.fderiv_comp_endChart`: differentiability and derivatives in `p.endChart`
  relate to `positive.endChart` by the sign reflection `z ↦ ε • z`.
* `TauCeti.Floer.PSSPlane.injOn_endChart_univ_prod_Ico`,
  `TauCeti.Floer.PSSPlane.image_endChart_positive_prod_Ico`,
  `TauCeti.Floer.PSSPlane.image_endChart_positive_Ioi_prod_Ico`,
  `TauCeti.Floer.PSSPlane.image_endChart_positive_Ici_prod_Ico`: `p.endChart` is injective on every
  band of angular width `1`, and `positive.endChart` maps `(a, ∞) × [0, 1)` and `[a, ∞) × [0, 1)`
  onto `{‖w‖ > exp (2πa)}` and `{‖w‖ ≥ exp (2πa)}`.
* `TauCeti.Floer.PSSPlane.perturbationPullback_endChart`,
  `TauCeti.Floer.PSSPlane.perturbationPullback_endChart_positive_stdComplexLineReal_of_le`,
  `TauCeti.Floer.PSSPlane.perturbationPullback_endChart_positive_stdComplexLineImag_of_le`:
  pullback of `p.perturbation H` along `p.endChart`, and pullback along `positive.endChart` of any
  perturbation `K` equal to `H(t) dt` beyond `T₀`.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Chapter 4 and
  Chapter 12.
-/

public section

open Set Real Function Filter
open TauCeti.Complex (realChart realChart_apply contDiff_realChart)
open scoped Topology

namespace TauCeti.Floer.PSSPlane

/-! ### Coordinates, derivatives, and sign reflection of the end chart -/

/-- The end lift `z ↦ exp (2π ε z)` of a PSS plane, written in the real coordinates `ℝ × ℝ ≃ ℂ`. -/
noncomputable def endChart (p : PSSPlane) : ℝ × ℝ → ℝ × ℝ :=
  realChart p.cylindricalEndLift

theorem endChart_def (p : PSSPlane) : p.endChart = realChart p.cylindricalEndLift :=
  (rfl)

theorem endChart_apply (p : PSSPlane) (z : ℝ × ℝ) :
    p.endChart z =
      Complex.equivRealProdCLM (p.cylindricalEndLift (Complex.equivRealProdCLM.symm z)) :=
  realChart_apply _ _

/-- The end chart at `(s, t)` is the end lift at `s + i t`, read in real coordinates. -/
theorem endChart_mk (p : PSSPlane) (s t : ℝ) :
    p.endChart (s, t) =
      Complex.equivRealProdCLM (p.cylindricalEndLift (↑s + ↑t * Complex.I)) := by
  simp [endChart_apply, Complex.equivRealProdCLM_symm_apply]

/-- In complex coordinates, the end chart is the end lift. -/
@[simp]
theorem equivRealProdCLM_symm_endChart (p : PSSPlane) (z : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (p.endChart z) =
      p.cylindricalEndLift (Complex.equivRealProdCLM.symm z) := by
  rw [endChart_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The image of any point under the end chart is away from the pole `0`. -/
theorem equivRealProdCLM_symm_endChart_ne_zero (p : PSSPlane) (z : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (p.endChart z) ≠ 0 := by
  rw [equivRealProdCLM_symm_endChart]
  exact p.cylindricalEndLift_ne_zero _

/-- The longitudinal coordinate at the image of `(s, t)` under the end chart is `s`. -/
theorem re_endCoord_endChart (p : PSSPlane) (z : ℝ × ℝ) :
    (p.endCoord (Complex.equivRealProdCLM.symm (p.endChart z))).re = z.1 := by
  rw [equivRealProdCLM_symm_endChart, re_endCoord_cylindricalEndLift,
    Complex.equivRealProdCLM_symm_apply_re]

/-- The norm of the image of `(s, t)` under the end chart is `exp (2π ε s)`. -/
theorem norm_equivRealProdCLM_symm_endChart (p : PSSPlane) (z : ℝ × ℝ) :
    ‖Complex.equivRealProdCLM.symm (p.endChart z)‖ =
      Real.exp (2 * π * (p.endSign * z.1)) := by
  rw [equivRealProdCLM_symm_endChart, norm_cylindricalEndLift,
    Complex.equivRealProdCLM_symm_apply_re]

/-- When `r ≤ exp (2π a)`, the half-cylinder `s > a` in `positive.endChart` lies in the exterior
`{‖w‖ > r}`. -/
theorem lt_norm_equivRealProdCLM_symm_endChart_positive {r a : ℝ}
    (hr : r ≤ Real.exp (2 * π * a)) {z : ℝ × ℝ} (hz : a < z.1) :
    r < ‖Complex.equivRealProdCLM.symm (positive.endChart z)‖ := by
  rw [norm_equivRealProdCLM_symm_endChart, endSign_positive, one_mul]
  exact hr.trans_lt (Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left hz Real.two_pi_pos))

/-- Given `T₀ < b` and `r < exp (2π b)`, there is a height `a < b` with `T₀ ≤ a` and
`r ≤ exp (2π a)`. -/
theorem exists_le_and_le_exp_and_lt {r T₀ b : ℝ} (hb : T₀ < b)
    (hbr : r < Real.exp (2 * π * b)) :
    ∃ a : ℝ, T₀ ≤ a ∧ r ≤ Real.exp (2 * π * a) ∧ a < b := by
  set M := max r (Real.exp (2 * π * T₀))
  have hMpos : 0 < M := (Real.exp_pos _).trans_le (le_max_right _ _)
  set a := Real.log M / (2 * π)
  have hexp : Real.exp (2 * π * a) = M := by
    rw [mul_div_cancel₀ _ Real.two_pi_pos.ne', Real.exp_log hMpos]
  refine ⟨a, ?_, hexp.symm ▸ le_max_left r _, ?_⟩
  · exact (mul_le_mul_iff_right₀ Real.two_pi_pos).1
      (Real.exp_le_exp.1 (hexp.symm ▸ le_max_right r _))
  · exact (mul_lt_mul_iff_right₀ Real.two_pi_pos).1
      (Real.exp_lt_exp.1 (hexp.symm ▸
        max_lt hbr (Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left hb Real.two_pi_pos))))

/-- For any `r` and `T₀`, there is a height `a` with `T₀ ≤ a` and `r ≤ exp (2π a)`. -/
theorem exists_le_and_le_exp (r T₀ : ℝ) : ∃ a : ℝ, T₀ ≤ a ∧ r ≤ Real.exp (2 * π * a) := by
  set M := max r (Real.exp (2 * π * T₀))
  have hMpos : 0 < M := (Real.exp_pos _).trans_le (le_max_right _ _)
  set a := Real.log M / (2 * π)
  have hexp : Real.exp (2 * π * a) = M := by
    rw [mul_div_cancel₀ _ Real.two_pi_pos.ne', Real.exp_log hMpos]
  exact ⟨a, (mul_le_mul_iff_right₀ Real.two_pi_pos).1
    (Real.exp_le_exp.1 (hexp.symm ▸ le_max_right r _)), hexp.symm ▸ le_max_left r _⟩

/-- The exterior `{z | r < ‖Complex.equivRealProdCLM.symm z‖}` is open in `ℝ × ℝ`. -/
theorem isOpen_lt_norm_equivRealProdCLM_symm (r : ℝ) :
    IsOpen {z : ℝ × ℝ | r < ‖Complex.equivRealProdCLM.symm z‖} :=
  isOpen_lt continuous_const (continuous_norm.comp Complex.equivRealProdCLM.symm.continuous)

/-- A map differentiable on `{‖w‖ > r}` is differentiable at `positive.endChart z` for every `z`
with `z.1 > a` whenever `r ≤ exp (2π a)`. -/
theorem differentiableAt_endChart_positive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ × ℝ → E} {r a : ℝ}
    (hu : DifferentiableOn ℝ u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (hr : r ≤ Real.exp (2 * π * a)) {z : ℝ × ℝ} (hz : a < z.1) :
    DifferentiableAt ℝ u (positive.endChart z) :=
  have hmem := lt_norm_equivRealProdCLM_symm_endChart_positive hr hz
  (hu _ hmem).differentiableAt ((isOpen_lt_norm_equivRealProdCLM_symm r).mem_nhds hmem)

/-- The end chart is `1`-periodic in the angular coordinate. -/
theorem endChart_add_one (p : PSSPlane) (s t : ℝ) :
    p.endChart (s, t + 1) = p.endChart (s, t) := by
  rw [endChart_mk, endChart_mk]
  exact congrArg Complex.equivRealProdCLM (by exact_mod_cast p.periodic_cylindricalEndLift s t)

/-- Scaling `(ε s, t)` by `ε` gives `(s, ε t)`. -/
theorem endSign_smul_endSign_mul_mk (p : PSSPlane) (s t : ℝ) :
    p.endSign • ((p.endSign * s, t) : ℝ × ℝ) = (s, p.endSign * t) := by
  simp [Prod.smul_mk, smul_eq_mul, endSign_mul_endSign_mul]

/-- The end chart of the negative plane is that of the positive plane composed with negation. -/
theorem endChart_negative (z : ℝ × ℝ) :
    negative.endChart z = positive.endChart (-z) := by
  rw [endChart_apply, endChart_apply, map_neg, cylindricalEndLift_negative]

/-- Scaling by the end sign turns the end chart of either plane into `positive.endChart`. -/
@[simp]
theorem endChart_endSign_smul (p : PSSPlane) (z : ℝ × ℝ) :
    p.endChart (p.endSign • z) = positive.endChart z := by
  cases p
  · simp [endSign_positive]
  · simp [endSign_negative, endChart_negative]

/-- The end chart of a PSS plane is `positive.endChart` composed with `z ↦ ε • z`. -/
theorem endChart_eq_positive_endChart_endSign_smul (p : PSSPlane) (z : ℝ × ℝ) :
    p.endChart z = positive.endChart (p.endSign • z) := by
  rw [← p.endChart_endSign_smul (p.endSign • z), smul_smul, endSign_mul_endSign, one_smul]

/-- The end chart at `(ε s, t)` is the positive end chart at `(s, ε t)`. -/
theorem endChart_endSign_mul (p : PSSPlane) (s t : ℝ) :
    p.endChart (p.endSign * s, t) = positive.endChart (s, p.endSign * t) := by
  rw [p.endChart_eq_positive_endChart_endSign_smul, endSign_smul_endSign_mul_mk]

/-- The end loop `t ↦ u(φ_p(ε s, t))` is the loop of `u ∘ φ_+` at height `s`, read at time `ε t`. -/
theorem comp_endChart_eq_comp_endChart_positive {α : Type*} (p : PSSPlane) (u : ℝ × ℝ → α)
    (s : ℝ) :
    (fun t ↦ u (p.endChart (p.endSign * s, t))) =
      (fun t ↦ (u ∘ positive.endChart) (s, t)) ∘ fun t ↦ p.endSign * t := by
  funext t
  simp only [comp_apply, endChart_endSign_mul]

/-- A family which is `J₀(t, u)` along the end of `p` beyond `T₀` is `J₀(ε t, u)` in
`positive.endChart`. -/
theorem eq_comp_endChart_positive {α β : Type*} {u : ℝ × ℝ → α} {J : ℝ × ℝ → β}
    {J₀ : ℝ → α → β} {p : PSSPlane} {T₀ : ℝ}
    (hJ : ∀ s t, T₀ ≤ s →
      J (p.endChart (p.endSign * s, t)) = J₀ t (u (p.endChart (p.endSign * s, t))))
    {z : ℝ × ℝ} (hz : T₀ ≤ z.1) :
    J (positive.endChart z) = J₀ (p.endSign * z.2) ((u ∘ positive.endChart) z) := by
  obtain ⟨s, t⟩ := z
  have h := hJ s (p.endSign * t) hz
  rwa [endChart_endSign_mul, endSign_mul_endSign_mul] at h

/-- If the end loops `t ↦ u(φ_p(ε s, t))` converge uniformly to `x`, then the loops of
`u ∘ positive.endChart` converge uniformly to `t ↦ x(ε t)`. -/
theorem tendstoUniformly_comp_endChart_positive {α : Type*} [UniformSpace α] {u : ℝ × ℝ → α}
    {p : PSSPlane} {x : ℝ → α} {l : Filter ℝ}
    (h : TendstoUniformly (fun s t ↦ u (p.endChart (p.endSign * s, t))) x l) :
    TendstoUniformly (fun s t ↦ (u ∘ positive.endChart) (s, t)) (fun t ↦ x (p.endSign * t)) l := by
  have hloop (s : ℝ) : (fun t ↦ (u ∘ positive.endChart) (s, t)) =
      (fun t ↦ u (p.endChart (p.endSign * s, t))) ∘ fun t ↦ p.endSign * t := by
    rw [comp_endChart_eq_comp_endChart_positive]
    funext t
    simp only [comp_apply, endSign_mul_endSign_mul]
  rw [funext hloop]
  exact h.comp _

/-- The derivative of `p.endChart` is multiplication by `deriv p.cylindricalEndLift` in real
coordinates. -/
theorem hasFDerivAt_endChart (p : PSSPlane) (z : ℝ × ℝ) :
    HasFDerivAt p.endChart
      ((Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ).comp
        (((ContinuousLinearMap.toSpanSingleton ℂ
          (deriv p.cylindricalEndLift (Complex.equivRealProdCLM.symm z))).restrictScalars ℝ).comp
            (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ))) z :=
  TauCeti.Complex.hasFDerivAt_realChart
    (p.hasDerivAt_cylindricalEndLift _).differentiableAt.hasDerivAt

/-- In real coordinates, `fderiv ℝ p.endChart z v` multiplies `v` by
`deriv p.cylindricalEndLift`. -/
theorem fderiv_endChart_apply (p : PSSPlane) (z v : ℝ × ℝ) :
    fderiv ℝ p.endChart z v =
      Complex.equivRealProdCLM
        (deriv p.cylindricalEndLift (Complex.equivRealProdCLM.symm z) *
          Complex.equivRealProdCLM.symm v) :=
  TauCeti.Complex.fderiv_realChart_apply
    (p.hasDerivAt_cylindricalEndLift _).differentiableAt.hasDerivAt v

/-- The end chart is smooth of every order. -/
theorem contDiff_endChart (p : PSSPlane) {n : WithTop ℕ∞} : ContDiff ℝ n p.endChart :=
  contDiff_realChart p.contDiff_cylindricalEndLift

/-- The end chart is a local diffeomorphism: its Jacobian determinant is everywhere positive. -/
theorem det_fderiv_endChart_pos (p : PSSPlane) (z : ℝ × ℝ) :
    0 < (fderiv ℝ p.endChart z).det := by
  rw [endChart_def, TauCeti.Complex.det_fderiv_realChart (p.hasDerivAt_cylindricalEndLift _)]
  simp [Complex.normSq_pos, Real.pi_ne_zero, p.cylindricalEndLift_ne_zero]

/-- The end chart is holomorphic: its derivative is complex linear everywhere. -/
theorem isComplexLinearMap_fderiv_endChart (p : PSSPlane) (z : ℝ × ℝ) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (AlmostComplexStructure.product ℝ)
      (fderiv ℝ p.endChart z : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by
  rw [endChart_def]
  exact Floer.isComplexLinearMap_fderiv_realChart (p.hasDerivAt_cylindricalEndLift _)

/-- A map composed with `p.endChart` is differentiable at `z` if and only if its composition with
`positive.endChart` is differentiable at `ε • z`. -/
theorem differentiableAt_comp_endChart_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : PSSPlane) (u : ℝ × ℝ → E) (z : ℝ × ℝ) :
    DifferentiableAt ℝ (u ∘ p.endChart) z ↔
      DifferentiableAt ℝ (u ∘ positive.endChart) (p.endSign • z) := by
  have h1 : u ∘ p.endChart = (u ∘ positive.endChart) ∘ (p.endSign • ·) :=
    funext fun w ↦ by simp [p.endChart_eq_positive_endChart_endSign_smul]
  have h2 : u ∘ positive.endChart = (u ∘ p.endChart) ∘ (p.endSign • ·) :=
    funext fun w ↦ by simp [p.endChart_eq_positive_endChart_endSign_smul, smul_smul]
  refine ⟨fun hd ↦ ?_, fun hd ↦ h1 ▸ hd.comp z (differentiableAt_id.const_smul p.endSign)⟩
  have hd0 : DifferentiableAt ℝ (u ∘ p.endChart) (p.endSign • (p.endSign • z)) := by
    simpa [smul_smul] using hd
  exact h2 ▸ hd0.comp (p.endSign • z) (differentiableAt_id.const_smul p.endSign)

/-- The derivative of `u ∘ p.endChart` at `z` is `ε` times the derivative of
`u ∘ positive.endChart` at `ε • z`. -/
theorem fderiv_comp_endChart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : PSSPlane) (u : ℝ × ℝ → E) (z : ℝ × ℝ) :
    fderiv ℝ (u ∘ p.endChart) z = p.endSign • fderiv ℝ (u ∘ positive.endChart) (p.endSign • z) := by
  have h : u ∘ p.endChart = fun w ↦ (u ∘ positive.endChart) (p.endSign • w) :=
    funext fun w ↦ by simp [p.endChart_eq_positive_endChart_endSign_smul]
  rw [h, fderiv_comp_smul]

/-! ### Injectivity and exterior images -/

/-- The end chart is injective on every horizontal strip `ℝ × [t₀, t₀ + 1)` of angular width
one. -/
theorem injOn_endChart_univ_prod_Ico (p : PSSPlane) (t₀ : ℝ) :
    InjOn p.endChart (univ ×ˢ Ico t₀ (t₀ + 1)) := by
  refine TauCeti.Complex.injOn_realChart ((p.injOn_cylindricalEndLift t₀).mono ?_)
  rintro _ ⟨z, hz, rfl⟩
  simpa [Complex.equivRealProdCLM_symm_apply_im] using hz.2

/-- For any set `P` of longitudinal coordinates, `positive.endChart` maps `P × [0, 1)` onto the set
of nonzero points `w` with `log ‖w‖ / (2π) ∈ P`. -/
theorem image_endChart_positive_prod_Ico (P : Set ℝ) :
    positive.endChart '' (P ×ˢ Ico 0 1) =
      {z | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Real.log ‖Complex.equivRealProdCLM.symm z‖ / (2 * π) ∈ P} := by
  ext z
  constructor
  · rintro ⟨ζ, hζ, rfl⟩
    rw [mem_ofPred_eq, equivRealProdCLM_symm_endChart]
    refine ⟨positive.cylindricalEndLift_ne_zero _, ?_⟩
    rw [norm_cylindricalEndLift, endSign_positive, one_mul,
      Complex.equivRealProdCLM_symm_apply_re, Real.log_exp,
      mul_div_cancel_left₀ _ Real.two_pi_pos.ne']
    exact hζ.1
  · rintro ⟨hw₀, hz⟩
    set w := Complex.equivRealProdCLM.symm z
    set ζ := positive.endCoord w
    have hζre : ζ.re = Real.log ‖w‖ / (2 * π) := by
      simpa [ζ, endSign_positive] using positive.endSign_mul_re_endCoord w
    refine ⟨(ζ.re, Int.fract ζ.im), ⟨hζre ▸ hz, Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_⟩
    have hper := (positive.periodic_cylindricalEndLift ζ.re).sub_int_mul_eq (x := ζ.im) ⌊ζ.im⌋
    rw [mul_one] at hper
    rw [endChart_mk, Int.fract, hper, Complex.re_add_im, positive.cylindricalEndLift_endCoord hw₀,
      ContinuousLinearEquiv.apply_symm_apply]

/-- The positive end chart maps `(a, ∞) × [0, 1)` onto the exterior `{‖w‖ > exp (2πa)}`. -/
theorem image_endChart_positive_Ioi_prod_Ico (a : ℝ) :
    positive.endChart '' (Ioi a ×ˢ Ico 0 1) =
      {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖} := by
  rw [image_endChart_positive_prod_Ico]
  ext z
  simp only [mem_ofPred_eq, mem_Ioi, lt_div_iff₀ Real.two_pi_pos, mul_comm a (2 * π)]
  exact ⟨fun ⟨hw, ha⟩ ↦ (Real.lt_log_iff_exp_lt (norm_pos_iff.2 hw)).1 ha,
    fun ha ↦ ⟨norm_pos_iff.1 ((Real.exp_pos _).trans ha),
      (Real.lt_log_iff_exp_lt ((Real.exp_pos _).trans ha)).2 ha⟩⟩

/-- The positive end chart maps `[a, ∞) × [0, 1)` onto the exterior `{‖w‖ ≥ exp (2πa)}`. -/
theorem image_endChart_positive_Ici_prod_Ico (a : ℝ) :
    positive.endChart '' (Ici a ×ˢ Ico 0 1) =
      {z | Real.exp (2 * π * a) ≤ ‖Complex.equivRealProdCLM.symm z‖} := by
  rw [image_endChart_positive_prod_Ico]
  ext z
  simp only [mem_ofPred_eq, mem_Ici, le_div_iff₀ Real.two_pi_pos, mul_comm a (2 * π)]
  exact ⟨fun ⟨hw, ha⟩ ↦ (Real.le_log_iff_exp_le (norm_pos_iff.2 hw)).1 ha,
    fun ha ↦ ⟨norm_pos_iff.1 ((Real.exp_pos _).trans_le ha),
      (Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le ha)).2 ha⟩⟩

/-! ### Pullback of perturbations along the end chart -/

/-- The pullback of `p.perturbation H` along `p.endChart`, evaluated on a tangent vector `v`, is
its component `p.endComponent H` along `v` in the end coordinates. -/
theorem perturbationPullback_endChart {X : Type*} (p : PSSPlane) (H : ℝ → X → ℝ) (v : ℝ × ℝ) :
    perturbationPullback p.endChart
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) v =
      p.endComponent H (Complex.equivRealProdCLM.symm v) := by
  funext z x
  have hz : Complex.equivRealProdCLM.symm z = ⟨z.1, z.2⟩ := Complex.ext (by simp) (by simp)
  rw [endChart_def, perturbationPullback_realChart _
    (p.hasDerivAt_cylindricalEndLift _).differentiableAt.hasDerivAt, endComponent_def, hz]

/-- The pullback of `p.perturbation H` along `p.endChart` has vanishing `ds` component. -/
theorem perturbationPullback_endChart_stdComplexLineReal {X : Type*} (p : PSSPlane)
    (H : ℝ → X → ℝ) :
    perturbationPullback p.endChart
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        stdComplexLineReal =
      fun _ _ ↦ 0 := by
  rw [perturbationPullback_endChart, equivRealProdCLM_symm_stdComplexLineReal, endComponent_one]

/-- The pullback of `p.perturbation H` along `p.endChart` has `dt` component
`β(ε s - 1) H(t)`. -/
theorem perturbationPullback_endChart_stdComplexLineImag {X : Type*} (p : PSSPlane)
    {H : ℝ → X → ℝ} (hH : Periodic H 1) :
    perturbationPullback p.endChart
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        stdComplexLineImag =
      fun z x ↦ smoothTransition (p.endSign * z.1 - 1) * H z.2 x := by
  rw [perturbationPullback_endChart, equivRealProdCLM_symm_stdComplexLineImag, endComponent_I hH]

/-- The pullback of a perturbation `K` along `p.endChart` at `p.endSign • ζ` relates to its
pullback along `positive.endChart` at `ζ` by multiplying by `p.endSign`. -/
theorem perturbationPullback_endChart_positive {X : Type*} {K : ℂ → X → ℂ →L[ℝ] ℝ} (p : PSSPlane)
    (v ζ : ℝ × ℝ) (x : X) :
    perturbationPullback positive.endChart
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) v ζ x =
      p.endSign * perturbationPullback p.endChart
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) v (p.endSign • ζ) x := by
  have hf : fderiv ℝ positive.endChart ζ v = p.endSign • fderiv ℝ p.endChart (p.endSign • ζ) v := by
    have h := congrArg (· v) (p.fderiv_comp_endChart id (p.endSign • ζ))
    simp only [id_comp, smul_apply, smul_smul, endSign_mul_endSign, one_smul] at h
    rw [h, smul_smul, endSign_mul_endSign, one_smul]
  simp only [perturbationPullback_apply, hf, p.endChart_endSign_smul, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- Where `K = H(t) dt` beyond `T₀` on the end of `p`, its pullback along `p.endChart` sends `∂_s`
to `0` and `∂_t` to `H(t)`. -/
theorem perturbationPullback_endChart_of_le {X : Type*} {K : ℂ → X → ℂ →L[ℝ] ℝ} {H : ℝ → X → ℝ}
    {T₀ : ℝ} {p : PSSPlane}
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (v : ℝ × ℝ) {ζ : ℝ × ℝ} (hζ : T₀ ≤ p.endSign * ζ.1) (x : X) :
    perturbationPullback p.endChart
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) v ζ x =
      (Complex.equivRealProdCLM.symm v).im * H ζ.2 x := by
  set z := Complex.equivRealProdCLM.symm ζ
  obtain ⟨k, hk⟩ := p.exists_endCoord_cylindricalEndLift z
  have hp : H (z.im + k) x = H ζ.2 x := by
    simpa [z, Complex.equivRealProdCLM_symm_apply_im] using congrFun (hH.int_mul k z.im) x
  have hre : T₀ ≤ p.endSign * (p.endCoord (p.cylindricalEndLift z)).re := by
    simpa [z, re_endCoord_cylindricalEndLift, Complex.equivRealProdCLM_symm_apply_re] using hζ
  rw [endChart_def, perturbationPullback_realChart _
    (p.hasDerivAt_cylindricalEndLift z).differentiableAt.hasDerivAt,
    hKH _ x (p.cylindricalEndLift_ne_zero z) hre, smul_apply,
    endAngularForm_cylindricalEndLift, hk]
  simp [hp, mul_comm]

/-- Where `K = H(t) dt` beyond `T₀` on the end of `p`, its pullback along `positive.endChart` on
`{s ≥ T₀}` sends `∂_s` to `0`. -/
theorem perturbationPullback_endChart_positive_stdComplexLineReal_of_le {X : Type*}
    {K : ℂ → X → ℂ →L[ℝ] ℝ} {H : ℝ → X → ℝ} {T₀ : ℝ} {p : PSSPlane}
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1) (x : X) :
    perturbationPullback positive.endChart
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal ζ x =
      0 := by
  rw [perturbationPullback_endChart_positive (p := p)]
  set z := Complex.equivRealProdCLM.symm (p.endSign • ζ)
  have hre : T₀ ≤ p.endSign * (p.endCoord (p.cylindricalEndLift z)).re := by
    simpa [z, re_endCoord_cylindricalEndLift, Complex.equivRealProdCLM_symm_apply_re,
      Prod.smul_fst, smul_eq_mul, endSign_mul_endSign_mul] using hζ
  rw [endChart_def, perturbationPullback_realChart _
    (p.hasDerivAt_cylindricalEndLift z).differentiableAt.hasDerivAt,
    hKH _ x (p.cylindricalEndLift_ne_zero z) hre, smul_apply,
    equivRealProdCLM_symm_stdComplexLineReal, endAngularForm_cylindricalEndLift]
  simp

/-- Where `K = H(t) dt` beyond `T₀` on the end of `p`, its pullback along `positive.endChart` on
`{s ≥ T₀}` sends `∂_t` to `p.positiveEndHamiltonian H ζ.2 x`. -/
theorem perturbationPullback_endChart_positive_stdComplexLineImag_of_le {X : Type*}
    {K : ℂ → X → ℂ →L[ℝ] ℝ} {H : ℝ → X → ℝ} {T₀ : ℝ} {p : PSSPlane}
    (hKH : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      K w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1) (x : X) :
    perturbationPullback positive.endChart
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag ζ x =
      p.positiveEndHamiltonian H ζ.2 x := by
  rw [perturbationPullback_endChart_positive (p := p),
    perturbationPullback_endChart_of_le hKH hH stdComplexLineImag
      (by simpa [Prod.smul_fst, smul_eq_mul, endSign_mul_endSign_mul] using hζ),
    equivRealProdCLM_symm_stdComplexLineImag, Complex.I_im, one_mul, Prod.smul_snd, smul_eq_mul,
    positiveEndHamiltonian_def]

end TauCeti.Floer.PSSPlane
