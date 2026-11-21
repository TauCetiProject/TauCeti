/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Order.MonotoneConvergence
import TauCeti.Analysis.Calculus.Deriv.Growth
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.ODE.GlobalSolution

/-!
# The Morse–Bott function `cos θ` on a torus with a sheared metric

On the torus with angular coordinates `(θ, φ)`, both modulo `2π`, the critical set of the
Morse–Bott function `f = cos θ` consists of two circles: the maximum circle `C₁ = {θ = 0}` and
the minimum circle `C₀ = {θ = π}`. This file computes the negative gradient flow of `f` for the
sheared metric

`g = h(θ) dθ² + (dφ - a(θ) dθ)²` (`TauCeti.shearedTorusMetric`),

where `h` is positive and `a` is a shear profile. This is the standard example in which the two
critical circles do not depend on the shear, but the endpoint maps of the trajectories between
them do: the two families of trajectories are rotated by different amounts, `∫₀^π a` and
`-∫_{-π}^0 a`, so for a shear supported in the upper semicircle only the upper family is rotated.

Everything is stated on the universal cover `ℝ × ℝ` of the torus, with `2π`-periodic data where
needed. A point of the torus is represented by a pair `(θ, φ)` of real lifts, and the circle `C₀`
appears both as `θ = π` and as `θ = -π`.

* **The negative gradient.** The metric `g` is positive definite where `h > 0`
  (`TauCeti.shearedTorusMetric_self_pos`), and the negative gradient of `cos θ` for `g` is

  `(sin θ / h θ) (∂_θ + a θ ∂_φ)` (`TauCeti.shearedTorusField`),

  that is, `g (V, w) = -d(cos θ)(w)` for every `w`, and `V` is the only vector with this property
  (`TauCeti.shearedTorusMetric_shearedTorusField`, `TauCeti.eq_shearedTorusField_iff`).
* **The complete flow.** When `h` is `C¹`, `2π`-periodic and positive and `a` is continuous,
  integral curves exist through every point for all times
  (`TauCeti.exists_hasDerivAt_shearedTorusField`).
* **A first integral.** Along an integral curve `dφ / dθ = a(θ)`, so `φ - ∫₀^θ a` is constant
  (`TauCeti.snd_sub_intervalIntegral_eq_of_hasDerivAt_shearedTorusField`).
* **Confinement and limits.** The angle `θ` never crosses a zero of `sin`
  (`TauCeti.fst_mem_Ioo_of_hasDerivAt_shearedTorusField`), so the integral curves through the
  open upper half `0 < θ < π` and the open lower half `-π < θ < 0` form two families. A curve of
  the upper family runs from `(0, c)` at `-∞` to `(π, c + ∫₀^π a)` at `+∞`, where `c` is its
  value of `φ - ∫₀^θ a`. A curve of the lower family runs from `(0, c)` to
  `(-π, c - ∫_{-π}^0 a)`. The lower family is the upper family for the reflected profiles
  `θ ↦ h (-θ)` and `θ ↦ a (-θ)`, under the reflection `(θ, φ) ↦ (-θ, -φ)`
  (`TauCeti.shearedTorusField_neg`).
* **Parametrization by the source angle.** In each family, an integral curve is determined up to
  translation in time by its source angle `c`, and every `c` occurs. So each family is a copy of
  the source circle, and its endpoint map sends `c` to `c + ∫₀^π a` for the upper family and to
  `c - ∫_{-π}^0 a` for the lower one.

For a profile `a` supported in the upper semicircle, `∫_{-π}^0 a = 0`, and with `A = ∫₀^π a`
the upper family ends at `φ + A` and the lower family at `φ`
(`TauCeti.tendsto_atTop_of_hasDerivAt_shearedTorusField_of_mem_Ioo_neg_pi_zero_of_eqOn`). This is
the pair of endpoint maps whose difference `R_A - id` is the Bott correspondence of the sheared
torus. For `a = 0` the two families end at the same angle and the contributions cancel already on
chains. Choosing `h` so that `g` is standard in the Morse–Bott coordinates near the critical
circles, and the transversality of the stable and unstable manifolds, are not treated here.

## Main declarations

* `TauCeti.shearedTorusMetric`: the metric `h(θ) dθ² + (dφ - a(θ) dθ)²`.
* `TauCeti.shearedTorusField`: its negative gradient of `cos θ`.
* `TauCeti.shearedTorusMetric_shearedTorusField`, `TauCeti.eq_shearedTorusField_iff`: the
  negative gradient property and its uniqueness.
* `TauCeti.exists_hasDerivAt_shearedTorusField`: the flow is complete.
* `TauCeti.tendsto_atBot_of_hasDerivAt_shearedTorusField_of_mem_Ioo_zero_pi`,
  `TauCeti.tendsto_atTop_of_hasDerivAt_shearedTorusField_of_mem_Ioo_zero_pi`: the limits of the
  upper family, and their analogues `..._of_mem_Ioo_neg_pi_zero` for the lower family.
* `TauCeti.exists_eq_comp_add_of_hasDerivAt_shearedTorusField_of_mem_Ioo_zero_pi` and
  `TauCeti.exists_hasDerivAt_shearedTorusField_and_fst_mem_Ioo_zero_pi_and_tendsto_atBot`: the
  upper family is parametrized by its source angle, and similarly `..._neg_pi_zero...` for the
  lower family.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.2 (Morse–Bott homology via trajectory correspondences
  between critical submanifolds).
-/

public section

noncomputable section

open Real Set Filter Topology Function

namespace TauCeti

variable {h a : ℝ → ℝ}

/-! ### The metric and its negative gradient -/

/-- The sheared metric `h(θ) dθ² + (dφ - a(θ) dθ)²` on the `(θ, φ)`-plane at angle `θ`, as a
bilinear form on tangent vectors `(dθ, dφ)`. -/
def shearedTorusMetric (h a : ℝ → ℝ) (θ : ℝ) : LinearMap.BilinForm ℝ (ℝ × ℝ) :=
  LinearMap.mk₂ ℝ (fun v w ↦ h θ * v.1 * w.1 + (v.2 - a θ * v.1) * (w.2 - a θ * w.1))
    (fun _ _ _ ↦ by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun _ _ _ ↦ by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun _ _ _ ↦ by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun _ _ _ ↦ by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

@[simp]
theorem shearedTorusMetric_apply (θ : ℝ) (v w : ℝ × ℝ) :
    shearedTorusMetric h a θ v w = h θ * v.1 * w.1 + (v.2 - a θ * v.1) * (w.2 - a θ * w.1) := by
  simp [shearedTorusMetric]

/-- The sheared metric is symmetric. -/
theorem isSymm_shearedTorusMetric (θ : ℝ) : (shearedTorusMetric h a θ).IsSymm :=
  LinearMap.BilinForm.isSymm_def.2 fun v w ↦ by simp only [shearedTorusMetric_apply]; ring

/-- The sheared metric is positive definite where `h` is positive. -/
theorem shearedTorusMetric_self_pos {θ : ℝ} (hθ : 0 < h θ) {v : ℝ × ℝ} (hv : v ≠ 0) :
    0 < shearedTorusMetric h a θ v v := by
  rw [shearedTorusMetric_apply]
  rcases eq_or_ne v.1 0 with h1 | h1
  · have h2 : v.2 ≠ 0 := fun h2 ↦ hv (Prod.ext h1 h2)
    simp only [h1, mul_zero, zero_add, sub_zero]
    exact mul_self_pos.2 h2
  · have : 0 < h θ * v.1 * v.1 := by
      rw [mul_assoc]
      exact mul_pos hθ (mul_self_pos.2 h1)
    linarith [mul_self_nonneg (v.2 - a θ * v.1)]

/-- The vector field `(sin θ / h θ) (∂_θ + a θ ∂_φ)`, the negative gradient of `cos θ` for the
sheared metric. -/
def shearedTorusField (h a : ℝ → ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (sin x.1 / h x.1, a x.1 * (sin x.1 / h x.1))

@[simp]
theorem shearedTorusField_apply (x : ℝ × ℝ) :
    shearedTorusField h a x = (sin x.1 / h x.1, a x.1 * (sin x.1 / h x.1)) := by
  simp only [shearedTorusField]

private theorem fderiv_cos_fst_apply (x w : ℝ × ℝ) :
    fderiv ℝ (fun y : ℝ × ℝ ↦ cos y.1) x w = -sin x.1 * w.1 := by
  rw [(hasFDerivAt_fst.cos (x := x)).fderiv]
  simp

/-- **The negative gradient of `cos θ`.** For the sheared metric, `shearedTorusField h a x`
represents minus the differential of `cos θ` at `x`. -/
theorem shearedTorusMetric_shearedTorusField {x : ℝ × ℝ} (hx : h x.1 ≠ 0) (w : ℝ × ℝ) :
    shearedTorusMetric h a x.1 (shearedTorusField h a x) w =
      -fderiv ℝ (fun y : ℝ × ℝ ↦ cos y.1) x w := by
  rw [fderiv_cos_fst_apply, shearedTorusMetric_apply, shearedTorusField_apply]
  field_simp
  ring

/-- **Uniqueness of the negative gradient.** Where `h` is positive, `shearedTorusField h a x` is
the only vector representing minus the differential of `cos θ` for the sheared metric. -/
theorem eq_shearedTorusField_iff {x U : ℝ × ℝ} (hx : 0 < h x.1) :
    U = shearedTorusField h a x ↔
      ∀ w, shearedTorusMetric h a x.1 U w = -fderiv ℝ (fun y : ℝ × ℝ ↦ cos y.1) x w := by
  refine ⟨fun hU ↦ hU ▸ shearedTorusMetric_shearedTorusField hx.ne', fun hU ↦ ?_⟩
  by_contra hne
  have hzero (w : ℝ × ℝ) : shearedTorusMetric h a x.1 (U - shearedTorusField h a x) w = 0 := by
    rw [LinearMap.map_sub₂, hU, shearedTorusMetric_shearedTorusField hx.ne', sub_self]
  exact (shearedTorusMetric_self_pos (a := a) hx (sub_ne_zero.2 hne)).ne' (hzero _)

/-- **Reflection of the field.** The reflection `(θ, φ) ↦ (-θ, -φ)` carries the field for the
profiles `h` and `a` to the field for the reflected profiles `θ ↦ h (-θ)` and `θ ↦ a (-θ)`. -/
theorem shearedTorusField_neg (x : ℝ × ℝ) :
    shearedTorusField (fun θ ↦ h (-θ)) (fun θ ↦ a (-θ)) (-x) = -shearedTorusField h a x := by
  simp [neg_div]

/-! ### The flow -/

private theorem contDiff_sin_div (hh : ContDiff ℝ 1 h) (hpos : ∀ θ, 0 < h θ) :
    ContDiff ℝ 1 fun θ ↦ sin θ / h θ :=
  contDiff_sin.div hh fun θ ↦ (hpos θ).ne'

private theorem periodic_comp_neg (hhp : Periodic h (2 * π)) :
    Periodic (fun θ ↦ h (-θ)) (2 * π) := fun θ ↦ by
  simp only [neg_add', hhp.sub_eq]

/-- The angular component `sin θ / h θ` of the field is Lipschitz. -/
private theorem exists_lipschitzWith_sin_div (hh : ContDiff ℝ 1 h) (hhp : Periodic h (2 * π))
    (hpos : ∀ θ, 0 < h θ) : ∃ K, LipschitzWith K fun θ ↦ sin θ / h θ :=
  (Real.sin_periodic.div hhp).exists_lipschitzWith two_pi_pos.ne' (contDiff_sin_div hh hpos)

/-- **The flow is complete.** For a `C¹`, `2π`-periodic `h > 0` and a continuous `a`, through every
point `x` there passes an integral curve `γ` of `shearedTorusField h a` defined for all times,
with `γ 0 = x`. -/
theorem exists_hasDerivAt_shearedTorusField (hh : ContDiff ℝ 1 h) (hhp : Periodic h (2 * π))
    (hpos : ∀ θ, 0 < h θ) (ha : Continuous a) (x : ℝ × ℝ) :
    ∃ γ : ℝ → ℝ × ℝ, γ 0 = x ∧ ∀ t, HasDerivAt γ (shearedTorusField h a (γ t)) t := by
  -- The angle solves `θ' = sin θ / h θ`, whose right-hand side is Lipschitz, and `φ` is
  -- recovered from the first integral `φ - ∫₀^θ a`.
  obtain ⟨K, hK⟩ := exists_lipschitzWith_sin_div hh hhp hpos
  set θ := ODE.globalSolution _ hK x.1
  refine ⟨fun t ↦ (θ t, x.2 + ((∫ s in (0 : ℝ)..θ t, a s) - ∫ s in (0 : ℝ)..x.1, a s)), ?_,
    fun t ↦ ?_⟩
  · simp [θ, ODE.globalSolution_zero]
  · have hθ := ODE.hasDerivAt_globalSolution _ hK x.1 t
    have hΦ := (ha.integral_hasStrictDerivAt 0 (θ t)).hasDerivAt.comp t hθ
    rw [shearedTorusField_apply]
    exact hθ.prodMk ((hΦ.sub_const (∫ s in (0 : ℝ)..x.1, a s)).const_add x.2)

/-- Two solutions of `θ' = sin θ / h θ` that agree at one time agree everywhere. -/
private theorem eq_of_hasDerivAt_sin_div (hh : ContDiff ℝ 1 h) (hhp : Periodic h (2 * π))
    (hpos : ∀ θ, 0 < h θ) {f g : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (sin (f t) / h (f t)) t)
    (hg : ∀ t, HasDerivAt g (sin (g t) / h (g t)) t) {t₀ : ℝ} (heq : f t₀ = g t₀) : f = g := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_sin_div hh hhp hpos
  exact ODE_solution_unique_univ (v := fun _ θ ↦ sin θ / h θ) (s := fun _ ↦ univ)
    (fun _ ↦ hK.lipschitzOnWith) (fun s ↦ ⟨hf s, trivial⟩) (fun s ↦ ⟨hg s, trivial⟩) heq

variable {γ : ℝ → ℝ × ℝ}

/-- Along an integral curve, the angle `θ` solves `θ' = sin θ / h θ`. -/
theorem hasDerivAt_fst_of_hasDerivAt_shearedTorusField
    (hγ : ∀ t, HasDerivAt γ (shearedTorusField h a (γ t)) t) (t : ℝ) :
    HasDerivAt (fun s ↦ (γ s).1) (sin (γ t).1 / h (γ t).1) t := by
  simpa only [ContinuousLinearMap.coe_fst', shearedTorusField_apply, comp_def] using
    hasFDerivAt_fst.comp_hasDerivAt t (hγ t)

/-- The angle of an integral curve is continuous. -/
private theorem continuous_fst_of_hasDerivAt_shearedTorusField
    (hγ : ∀ t, HasDerivAt γ (shearedTorusField h a (γ t)) t) : Continuous fun s ↦ (γ s).1 :=
  continuous_iff_continuousAt.2 fun s ↦
    (hasDerivAt_fst_of_hasDerivAt_shearedTorusField hγ s).continuousAt

private theorem hasDerivAt_snd_of_hasDerivAt_shearedTorusField
    (hγ : ∀ t, HasDerivAt γ (shearedTorusField h a (γ t)) t) (t : ℝ) :
    HasDerivAt (fun s ↦ (γ s).2) (a (γ t).1 * (sin (γ t).1 / h (γ t).1)) t := by
  simpa only [ContinuousLinearMap.coe_snd', shearedTorusField_apply, comp_def] using
    hasFDerivAt_snd.comp_hasDerivAt t (hγ t)

/-- The reflection `(θ, φ) ↦ (-θ, -φ)` of an integral curve is an integral curve for the
reflected profiles. -/
private theorem hasDerivAt_neg_shearedTorusField
    (hγ : ∀ t, HasDerivAt γ (shearedTorusField h a (γ t)) t) (t : ℝ) :
    HasDerivAt (fun s ↦ -γ s) (shearedTorusField (fun θ ↦ h (-θ)) (fun θ ↦ a (-θ)) (-γ t)) t := by
  rw [shearedTorusField_neg]
  exact (hγ t).neg

/-- **The first integral `φ - ∫₀^θ a`.** Along an integral curve `dφ / dθ = a(θ)`, so
`φ - ∫₀^θ a` keeps its initial value. -/
theorem snd_sub_intervalIntegral_eq_of_hasDerivAt_shearedTorusField (ha : Continuous a)
    (hγ : ∀ t, HasDerivAt γ (shearedTorusField h a (γ t)) t) (t : ℝ) :
    (γ t).2 - ∫ s in (0 : ℝ)..(γ t).1, a s = (γ 0).2 - ∫ s in (0 : ℝ)..(γ 0).1, a s := by
  have hd (s : ℝ) : HasDerivAt (fun s ↦ (γ s).2 - ∫ u in (0 : ℝ)..(γ s).1, a u) 0 s := by
    have h₂ := (ha.integral_hasStrictDerivAt 0 (γ s).1).hasDerivAt.comp s
      (hasDerivAt_fst_of_hasDerivAt_shearedTorusField hγ s)
    simpa only [sub_self, Pi.sub_def, comp_def] using
      (hasDerivAt_snd_of_hasDerivAt_shearedTorusField hγ s).sub h₂
  exact is_const_of_deriv_eq_zero (fun s ↦ (hd s).differentiableAt) (fun s ↦ (hd s).deriv) t 0

/-- If the angle of an integral curve is a zero of `sin` at one time, it is constant. -/
private theorem fst_eq_of_sin_eq_zero (hh : ContDiff ℝ 1 h) (hhp : Periodic h (2 * π))
    (hpos : ∀ θ, 0 < h θ) (hγ : ∀ t, HasDerivAt γ (shearedTorusField h a (γ t)) t) {t₁ : ℝ}
    (h₁ : sin (γ t₁).1 = 0) (t : ℝ) : (γ t).1 = (γ t₁).1 := by
  have heq := eq_of_hasDerivAt_sin_div hh hhp hpos (t₀ := t₁) (g := fun _ ↦ (γ t₁).1)
    (hasDerivAt_fst_of_hasDerivAt_shearedTorusField hγ)
    (fun _ ↦ by simpa [h₁] using hasDerivAt_const _ (γ t₁).1) rfl
  exact congrFun heq t

/-- **Confinement.** The angle of an integral curve never reaches a zero of `sin`: if it starts
strictly between two zeros `α < β` of `sin`, it stays there for all times. -/
theorem fst_mem_Ioo_of_hasDerivAt_shearedTorusField (hh : ContDiff ℝ 1 h)
    (hhp : Periodic h (2 * π)) (hpos : ∀ θ, 0 < h θ)
    (hγ : ∀ t, HasDerivAt γ (shearedTorusField h a (γ t)) t) {α β : ℝ} (hα : sin α = 0)
    (hβ : sin β = 0) (h0 : (γ 0).1 ∈ Ioo α β) (t : ℝ) : (γ t).1 ∈ Ioo α β := by
  have hcont := continuous_fst_of_hasDerivAt_shearedTorusField hγ
  by_contra hmem
  rcases not_and_or.1 hmem with hlt | hlt <;> rw [not_lt] at hlt
  · obtain ⟨s, hs⟩ := intermediate_value_univ t 0 hcont ⟨hlt, h0.1.le⟩
    have := fst_eq_of_sin_eq_zero hh hhp hpos hγ (t₁ := s) (by simpa [hs] using hα) 0
    exact h0.1.ne' (this.trans hs)
  · obtain ⟨s, hs⟩ := intermediate_value_univ 0 t hcont ⟨h0.2.le, hlt⟩
    have := fst_eq_of_sin_eq_zero hh hhp hpos hγ (t₁ := s) (by simpa [hs] using hβ) 0
    exact h0.2.ne (this.trans hs)

/-! ### Limits of the angle -/

/-- The limits of the angle of an integral curve in the upper half `0 < θ < π`: it increases
from `0` to `π`. -/
private theorem tendsto_fst_of_mem_Ioo_zero_pi (hh : ContDiff ℝ 1 h) (hhp : Periodic h (2 * π))
    (hpos : ∀ θ, 0 < h θ) (hγ : ∀ t, HasDerivAt γ (shearedTorusField h a (γ t)) t)
    (h0 : (γ 0).1 ∈ Ioo 0 π) :
    Tendsto (fun t ↦ (γ t).1) atBot (𝓝 0) ∧ Tendsto (fun t ↦ (γ t).1) atTop (𝓝 π) := by
  have hmem := fst_mem_Ioo_of_hasDerivAt_shearedTorusField hh hhp hpos hγ sin_zero sin_pi h0
  have hd := hasDerivAt_fst_of_hasDerivAt_shearedTorusField hγ
  have hF := (contDiff_sin_div hh hpos).continuous
  -- A limit of the angle is an equilibrium of `θ' = sin θ / h θ`, so a zero of `sin`.
  have hsin {L : ℝ} (hL : sin L / h L = 0) : sin L = 0 :=
    (div_eq_zero_iff.1 hL).resolve_right (hpos L).ne'
  have hmono : StrictMono fun t ↦ (γ t).1 := strictMono_of_deriv_pos fun t ↦ by
    rw [(hd t).deriv]
    exact div_pos (sin_pos_of_pos_of_lt_pi (hmem t).1 (hmem t).2) (hpos _)
  have hbddA : BddAbove (range fun t ↦ (γ t).1) := ⟨π, by
    rintro _ ⟨t, rfl⟩
    exact (hmem t).2.le⟩
  have hbddB : BddBelow (range fun t ↦ (γ t).1) := ⟨0, by
    rintro _ ⟨t, rfl⟩
    exact (hmem t).1.le⟩
  have htop := tendsto_atTop_ciSup hmono.monotone hbddA
  have hbot := tendsto_atBot_ciInf hmono.monotone hbddB
  refine ⟨?_, ?_⟩
  · convert hbot using 2
    set L := ⨅ t, (γ t).1
    have hL0 : 0 ≤ L := le_ciInf fun t ↦ (hmem t).1.le
    have hLπ : L < π := (ciInf_le hbddB 0).trans_lt h0.2
    by_contra hne
    exact (sin_pos_of_pos_of_lt_pi (lt_of_le_of_ne hL0 hne) hLπ).ne'
      (hsin (apply_eq_zero_of_tendsto_atBot_of_hasDerivAt (F := fun θ ↦ sin θ / h θ)
        hF.continuousAt (Eventually.of_forall hd) hbot))
  · convert htop using 2
    set L := ⨆ t, (γ t).1
    have hLπ : L ≤ π := ciSup_le fun t ↦ (hmem t).2.le
    have hL0 : 0 < L := h0.1.trans_le (le_ciSup hbddA 0)
    by_contra hne
    exact (sin_pos_of_pos_of_lt_pi hL0 (lt_of_le_of_ne hLπ (Ne.symm hne))).ne'
      (hsin (apply_eq_zero_of_tendsto_atTop_of_hasDerivAt (F := fun θ ↦ sin θ / h θ)
        hF.continuousAt (Eventually.of_forall hd) htop))

private theorem neg_mem_Ioo_zero_pi {θ : ℝ} (hθ : θ ∈ Ioo (-π) 0) : -θ ∈ Ioo 0 π :=
  ⟨neg_pos.2 hθ.2, neg_lt.1 hθ.1⟩

/-- The limits of the angle of an integral curve in the lower half `-π < θ < 0`: it decreases
from `0` to `-π`. This is the upper half under the reflection `(θ, φ) ↦ (-θ, -φ)`. -/
private theorem tendsto_fst_of_mem_Ioo_neg_pi_zero (hh : ContDiff ℝ 1 h)
    (hhp : Periodic h (2 * π)) (hpos : ∀ θ, 0 < h θ)
    (hγ : ∀ t, HasDerivAt γ (shearedTorusField h a (γ t)) t) (h0 : (γ 0).1 ∈ Ioo (-π) 0) :
    Tendsto (fun t ↦ (γ t).1) atBot (𝓝 0) ∧ Tendsto (fun t ↦ (γ t).1) atTop (𝓝 (-π)) := by
  have h := tendsto_fst_of_mem_Ioo_zero_pi (hh.comp contDiff_neg) (periodic_comp_neg hhp)
    (fun θ ↦ hpos (-θ)) (hasDerivAt_neg_shearedTorusField hγ) (neg_mem_Ioo_zero_pi h0)
  exact ⟨by simpa using h.1.neg, by simpa using h.2.neg⟩

/-! ### Limits of the integral curves -/

/-- An integral curve whose angle tends to `L` tends to `(L, c + ∫₀^L a)`, where `c` is its value
of the first integral `φ - ∫₀^θ a`. -/
private theorem tendsto_of_tendsto_fst (ha : Continuous a)
    (hγ : ∀ t, HasDerivAt γ (shearedTorusField h a (γ t)) t) {l : Filter ℝ} {L : ℝ}
    (hL : Tendsto (fun t ↦ (γ t).1) l (𝓝 L)) :
    Tendsto γ l (𝓝 (L, (γ 0).2 - (∫ s in (0 : ℝ)..(γ 0).1, a s) + ∫ s in (0 : ℝ)..L, a s)) := by
  have hsnd : Tendsto (fun t ↦ (γ t).2) l
      (𝓝 ((γ 0).2 - (∫ s in (0 : ℝ)..(γ 0).1, a s) + ∫ s in (0 : ℝ)..L, a s)) := by
    refine ((((intervalIntegral.continuous_primitive (fun _ _ ↦ ha.intervalIntegrable _ _)
      0).tendsto L).comp hL).const_add ((γ 0).2 - ∫ s in (0 : ℝ)..(γ 0).1, a s)).congr fun t ↦ ?_
    have := snd_sub_intervalIntegral_eq_of_hasDerivAt_shearedTorusField ha hγ t
    simp only [comp_apply]
    linarith
  exact hL.prodMk_nhds hsnd

/-- Reflecting the shear profile negates its primitive. -/
private theorem intervalIntegral_comp_neg (θ : ℝ) :
    ∫ s in (0 : ℝ)..-θ, a (-s) = -∫ s in (0 : ℝ)..θ, a s := by
  rw [intervalIntegral.integral_comp_neg, neg_neg, neg_zero, intervalIntegral.integral_symm]

section Limits

variable (hh : ContDiff ℝ 1 h) (hhp : Periodic h (2 * π)) (hpos : ∀ θ, 0 < h θ)
  (ha : Continuous a) (hγ : ∀ t, HasDerivAt γ (shearedTorusField h a (γ t)) t)
include hh hhp hpos ha hγ

/-- **The source of the upper family.** An integral curve through the upper half `0 < θ < π`
comes from the point `(0, c)` of the maximum circle, where `c = φ - ∫₀^θ a` along the curve. -/
theorem tendsto_atBot_of_hasDerivAt_shearedTorusField_of_mem_Ioo_zero_pi
    (h0 : (γ 0).1 ∈ Ioo 0 π) :
    Tendsto γ atBot (𝓝 (0, (γ 0).2 - ∫ s in (0 : ℝ)..(γ 0).1, a s)) := by
  simpa using tendsto_of_tendsto_fst ha hγ (tendsto_fst_of_mem_Ioo_zero_pi hh hhp hpos hγ h0).1

/-- **The target of the upper family.** An integral curve through the upper half `0 < θ < π`
goes to the point `(π, c + ∫₀^π a)` of the minimum circle, where `c = φ - ∫₀^θ a` along the
curve: the shear rotates its endpoint by `∫₀^π a`. -/
theorem tendsto_atTop_of_hasDerivAt_shearedTorusField_of_mem_Ioo_zero_pi
    (h0 : (γ 0).1 ∈ Ioo 0 π) :
    Tendsto γ atTop
      (𝓝 (π, (γ 0).2 - (∫ s in (0 : ℝ)..(γ 0).1, a s) + ∫ s in (0 : ℝ)..π, a s)) :=
  tendsto_of_tendsto_fst ha hγ (tendsto_fst_of_mem_Ioo_zero_pi hh hhp hpos hγ h0).2

/-- **The source of the lower family.** An integral curve through the lower half `-π < θ < 0`
comes from the point `(0, c)` of the maximum circle, where `c = φ - ∫₀^θ a` along the curve. -/
theorem tendsto_atBot_of_hasDerivAt_shearedTorusField_of_mem_Ioo_neg_pi_zero
    (h0 : (γ 0).1 ∈ Ioo (-π) 0) :
    Tendsto γ atBot (𝓝 (0, (γ 0).2 - ∫ s in (0 : ℝ)..(γ 0).1, a s)) := by
  have := (tendsto_atBot_of_hasDerivAt_shearedTorusField_of_mem_Ioo_zero_pi
    (hh.comp contDiff_neg) (periodic_comp_neg hhp) (fun θ ↦ hpos (-θ)) (ha.comp' continuous_neg)
    (hasDerivAt_neg_shearedTorusField hγ) (neg_mem_Ioo_zero_pi h0)).neg
  simp only [neg_neg, Prod.fst_neg, Prod.snd_neg, intervalIntegral_comp_neg] at this
  convert this using 2
  rw [Prod.neg_mk, neg_zero]
  congr 1
  ring

/-- **The target of the lower family.** An integral curve through the lower half `-π < θ < 0`
goes to the point `(-π, c - ∫_{-π}^0 a)` of the minimum circle, where `c = φ - ∫₀^θ a` along the
curve. -/
theorem tendsto_atTop_of_hasDerivAt_shearedTorusField_of_mem_Ioo_neg_pi_zero
    (h0 : (γ 0).1 ∈ Ioo (-π) 0) :
    Tendsto γ atTop
      (𝓝 (-π, (γ 0).2 - (∫ s in (0 : ℝ)..(γ 0).1, a s) - ∫ s in (-π)..0, a s)) := by
  have := (tendsto_atTop_of_hasDerivAt_shearedTorusField_of_mem_Ioo_zero_pi
    (hh.comp contDiff_neg) (periodic_comp_neg hhp) (fun θ ↦ hpos (-θ)) (ha.comp' continuous_neg)
    (hasDerivAt_neg_shearedTorusField hγ) (neg_mem_Ioo_zero_pi h0)).neg
  simp only [neg_neg, Prod.fst_neg, Prod.snd_neg, intervalIntegral_comp_neg] at this
  convert this using 2
  rw [Prod.neg_mk, intervalIntegral.integral_comp_neg, neg_zero]
  congr 1
  ring

/-- **The lower family is not sheared.** If the shear profile `a` vanishes on the lower half
`[-π, 0]`, an integral curve through the lower half goes from `(0, c)` to `(-π, c)`: its endpoint
angle is its source angle. -/
theorem tendsto_atTop_of_hasDerivAt_shearedTorusField_of_mem_Ioo_neg_pi_zero_of_eqOn
    (ha0 : EqOn a 0 (Icc (-π) 0)) (h0 : (γ 0).1 ∈ Ioo (-π) 0) :
    Tendsto γ atTop (𝓝 (-π, (γ 0).2 - ∫ s in (0 : ℝ)..(γ 0).1, a s)) := by
  have h := tendsto_atTop_of_hasDerivAt_shearedTorusField_of_mem_Ioo_neg_pi_zero hh hhp hpos ha
    hγ h0
  have hint : ∫ s in (-π)..0, a s = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun s hs ↦ ?_]
    · simp
    · rw [uIcc_of_le (by linarith [pi_pos])] at hs
      exact ha0 hs
  simpa only [hint, sub_zero] using h

end Limits

/-! ### Parametrization of the two families by the source angle -/

/-- Two integral curves with the same value of the first integral `φ - ∫₀^θ a`, whose angles
agree at the times `τ` and `0`, differ by the translation of time by `τ`. -/
private theorem eq_comp_add_of_fst_eq (hh : ContDiff ℝ 1 h) (hhp : Periodic h (2 * π))
    (hpos : ∀ θ, 0 < h θ) (ha : Continuous a) {γ₁ γ₂ : ℝ → ℝ × ℝ}
    (hγ₁ : ∀ t, HasDerivAt γ₁ (shearedTorusField h a (γ₁ t)) t)
    (hγ₂ : ∀ t, HasDerivAt γ₂ (shearedTorusField h a (γ₂ t)) t) {τ : ℝ}
    (hτ : (γ₁ τ).1 = (γ₂ 0).1)
    (hc : (γ₁ 0).2 - ∫ s in (0 : ℝ)..(γ₁ 0).1, a s = (γ₂ 0).2 - ∫ s in (0 : ℝ)..(γ₂ 0).1, a s)
    (t : ℝ) : γ₂ t = γ₁ (t + τ) := by
  have hfst := eq_of_hasDerivAt_sin_div hh hhp hpos (t₀ := 0) (g := fun t ↦ (γ₁ (t + τ)).1)
    (hasDerivAt_fst_of_hasDerivAt_shearedTorusField hγ₂)
    (fun s ↦ (hasDerivAt_fst_of_hasDerivAt_shearedTorusField hγ₁ (s + τ)).comp_add_const s τ)
    (by simp [hτ])
  have h1 : (γ₂ t).1 = (γ₁ (t + τ)).1 := congrFun hfst t
  have h₁ := snd_sub_intervalIntegral_eq_of_hasDerivAt_shearedTorusField ha hγ₁ (t + τ)
  have h₂ := snd_sub_intervalIntegral_eq_of_hasDerivAt_shearedTorusField ha hγ₂ t
  rw [← h1] at h₁
  exact Prod.ext h1 (by linarith)

/-- **The upper family is parametrized by the source angle: uniqueness.** Two integral curves
through the upper half `0 < θ < π` with the same source `(0, c)` on the maximum circle differ by a
translation of time. -/
theorem exists_eq_comp_add_of_hasDerivAt_shearedTorusField_of_mem_Ioo_zero_pi
    (hh : ContDiff ℝ 1 h) (hhp : Periodic h (2 * π)) (hpos : ∀ θ, 0 < h θ)
    (ha : Continuous a) {γ₁ γ₂ : ℝ → ℝ × ℝ}
    (hγ₁ : ∀ t, HasDerivAt γ₁ (shearedTorusField h a (γ₁ t)) t)
    (hγ₂ : ∀ t, HasDerivAt γ₂ (shearedTorusField h a (γ₂ t)) t) (h₁ : (γ₁ 0).1 ∈ Ioo 0 π)
    (h₂ : (γ₂ 0).1 ∈ Ioo 0 π) {c : ℝ} (hc₁ : Tendsto γ₁ atBot (𝓝 (0, c)))
    (hc₂ : Tendsto γ₂ atBot (𝓝 (0, c))) : ∃ τ, ∀ t, γ₂ t = γ₁ (t + τ) := by
  have hlim := tendsto_fst_of_mem_Ioo_zero_pi hh hhp hpos hγ₁ h₁
  obtain ⟨τ, -, hτ⟩ := isPreconnected_univ.intermediate_value_Ioo (by simp) (by simp)
    (continuous_fst_of_hasDerivAt_shearedTorusField hγ₁).continuousOn
    hlim.1 hlim.2 h₂
  have e₁ := tendsto_nhds_unique hc₁ <|
    tendsto_atBot_of_hasDerivAt_shearedTorusField_of_mem_Ioo_zero_pi hh hhp hpos ha
      hγ₁ h₁
  have e₂ := tendsto_nhds_unique hc₂ <|
    tendsto_atBot_of_hasDerivAt_shearedTorusField_of_mem_Ioo_zero_pi hh hhp hpos ha
      hγ₂ h₂
  exact ⟨τ, eq_comp_add_of_fst_eq hh hhp hpos ha hγ₁ hγ₂ hτ
    ((congrArg Prod.snd e₁).symm.trans (congrArg Prod.snd e₂))⟩

/-- **The upper family is parametrized by the source angle: existence.** For every angle `c`,
some integral curve through the upper half `0 < θ < π` comes from the point `(0, c)` of the
maximum circle. -/
theorem exists_hasDerivAt_shearedTorusField_and_fst_mem_Ioo_zero_pi_and_tendsto_atBot
    (hh : ContDiff ℝ 1 h) (hhp : Periodic h (2 * π)) (hpos : ∀ θ, 0 < h θ)
    (ha : Continuous a) (c : ℝ) :
    ∃ γ : ℝ → ℝ × ℝ, (∀ t, HasDerivAt γ (shearedTorusField h a (γ t)) t) ∧
      (γ 0).1 ∈ Ioo 0 π ∧ Tendsto γ atBot (𝓝 (0, c)) := by
  obtain ⟨γ, hγ0, hγ⟩ := exists_hasDerivAt_shearedTorusField hh hhp hpos ha
    (π / 2, c + ∫ s in (0 : ℝ)..π / 2, a s)
  have h0 : (γ 0).1 ∈ Ioo 0 π := by
    rw [hγ0]
    constructor <;> linarith [pi_pos]
  refine ⟨γ, hγ, h0, ?_⟩
  simpa [hγ0] using
    tendsto_atBot_of_hasDerivAt_shearedTorusField_of_mem_Ioo_zero_pi hh hhp hpos ha hγ h0

/-- **The lower family is parametrized by the source angle: uniqueness.** Two integral curves
through the lower half `-π < θ < 0` with the same source `(0, c)` on the maximum circle differ by
a translation of time. -/
theorem exists_eq_comp_add_of_hasDerivAt_shearedTorusField_of_mem_Ioo_neg_pi_zero
    (hh : ContDiff ℝ 1 h) (hhp : Periodic h (2 * π)) (hpos : ∀ θ, 0 < h θ)
    (ha : Continuous a) {γ₁ γ₂ : ℝ → ℝ × ℝ}
    (hγ₁ : ∀ t, HasDerivAt γ₁ (shearedTorusField h a (γ₁ t)) t)
    (hγ₂ : ∀ t, HasDerivAt γ₂ (shearedTorusField h a (γ₂ t)) t) (h₁ : (γ₁ 0).1 ∈ Ioo (-π) 0)
    (h₂ : (γ₂ 0).1 ∈ Ioo (-π) 0) {c : ℝ} (hc₁ : Tendsto γ₁ atBot (𝓝 (0, c)))
    (hc₂ : Tendsto γ₂ atBot (𝓝 (0, c))) : ∃ τ, ∀ t, γ₂ t = γ₁ (t + τ) := by
  obtain ⟨τ, hτ⟩ := exists_eq_comp_add_of_hasDerivAt_shearedTorusField_of_mem_Ioo_zero_pi
    (hh.comp contDiff_neg) (periodic_comp_neg hhp) (fun θ ↦ hpos (-θ)) (ha.comp' continuous_neg)
    (hasDerivAt_neg_shearedTorusField hγ₁) (hasDerivAt_neg_shearedTorusField hγ₂)
    (neg_mem_Ioo_zero_pi h₁) (neg_mem_Ioo_zero_pi h₂) (c := -c) (by simpa using hc₁.neg)
    (by simpa using hc₂.neg)
  exact ⟨τ, fun t ↦ neg_injective (hτ t)⟩

/-- **The lower family is parametrized by the source angle: existence.** For every angle `c`,
some integral curve through the lower half `-π < θ < 0` comes from the point `(0, c)` of the
maximum circle. -/
theorem exists_hasDerivAt_shearedTorusField_and_fst_mem_Ioo_neg_pi_zero_and_tendsto_atBot
    (hh : ContDiff ℝ 1 h) (hhp : Periodic h (2 * π)) (hpos : ∀ θ, 0 < h θ)
    (ha : Continuous a) (c : ℝ) :
    ∃ γ : ℝ → ℝ × ℝ, (∀ t, HasDerivAt γ (shearedTorusField h a (γ t)) t) ∧
      (γ 0).1 ∈ Ioo (-π) 0 ∧ Tendsto γ atBot (𝓝 (0, c)) := by
  obtain ⟨γ, hγ, h0, hc⟩ :=
    exists_hasDerivAt_shearedTorusField_and_fst_mem_Ioo_zero_pi_and_tendsto_atBot
      (hh.comp contDiff_neg) (periodic_comp_neg hhp) (fun θ ↦ hpos (-θ)) (ha.comp' continuous_neg)
      (-c)
  refine ⟨fun t ↦ -γ t, by simpa using hasDerivAt_neg_shearedTorusField hγ,
    ⟨neg_lt_neg h0.2, neg_neg_of_pos h0.1⟩, by simpa using hc.neg⟩

end TauCeti
