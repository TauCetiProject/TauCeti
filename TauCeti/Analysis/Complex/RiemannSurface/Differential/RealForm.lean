/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Complex
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Basic
public import TauCeti.Geometry.Manifold.Complex.Orientation
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ExtChartAt.Basic
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# A `1`-form on a Riemann surface as a real differential form

A `1`-form `ω` on a Riemann surface `X` (`TauCeti.RiemannSurface.OneForm X`) assigns to each point
a complex-linear covector on the tangent space. Forgetting complex linearity, it is a complex-valued
real differential form of degree one on the underlying real surface, modelled on `𝓘(ℝ, ℂ)`
(`TauCeti.RiemannSurface.OneForm.toRoughForm`). This is the form `f dz` that Stokes' theorem
integrates: in the preferred chart at any point, with coordinate `z`, the real form of `ω` reads
`f(z) dz`, where `f` is the coefficient of `ω` in that chart and `dz` is
`TauCeti.dzForm` (`TauCeti.RiemannSurface.OneForm.inChartAt_toRoughForm`).

Where `ω` is holomorphic, its real form is smooth
(`TauCeti.RiemannSurface.OneForm.contMDiffAt_toRoughForm`) and closed
(`TauCeti.RiemannSurface.OneForm.mextDeriv_toRoughForm_eq_zero`), since `d(f dz) = 0` for `f`
holomorphic. For a meromorphic `1`-form, multiplying by a smooth real function `ψ` that vanishes
near the poles gives a smooth real form `ψ ω`
(`TauCeti.RiemannSurface.OneForm.isSmoothForm_smul_toRoughForm`). Its exterior derivative is read
in a chart as the flat exterior derivative of `(ψ f) dz`
(`TauCeti.RiemannSurface.OneForm.inChartAt_mextDeriv_smul_toRoughForm`), and it vanishes wherever
`ψ` is locally constant (`TauCeti.RiemannSurface.OneForm.mextDeriv_smul_toRoughForm_eq_zero`). The
real and imaginary parts, the coefficient maps `Complex.reCLM` and `Complex.imCLM` of
`TauCeti.RoughForm.mapCoeff`, are real-valued smooth forms whose exterior derivatives are the real
and imaginary parts of the exterior derivative (`TauCeti.mextDeriv_mapCoeff` applied to
`TauCeti.RiemannSurface.OneForm.isSmoothForm_smul_toRoughForm`); the integration theory of top
forms applies to these exterior derivatives.

These are the ingredients of the proof of the residue theorem on a compact Riemann surface by
Stokes' theorem (Forster, Theorem 10.21): with `ψ = 1 - Σ χᵢ` for cutoffs `χᵢ` about the poles,
the real form of `ψ ω` is smooth, and its exterior derivative is supported in the coordinate discs
about the poles, where its integral computes the residues.

The real structure on `X` is the one underlying its complex structure
(`TauCeti.ComplexManifold.isManifold_real`, available after `open scoped TauCeti.ComplexManifold`).

## Main definitions

* `TauCeti.RiemannSurface.OneForm.toRoughForm`: the real form of a `1`-form.

## Main results

* `TauCeti.RiemannSurface.OneForm.inChartAt_toRoughForm`: `ω = f dz` in a chart.
* `TauCeti.RiemannSurface.OneForm.isSmoothForm_toRoughForm`,
  `TauCeti.RiemannSurface.OneForm.mextDeriv_toRoughForm`: a holomorphic `1`-form is a smooth closed
  real form.
* `TauCeti.RiemannSurface.OneForm.isSmoothForm_smul_toRoughForm`: a cutoff of a `1`-form,
  vanishing near the points where the form is not holomorphic, is smooth.
* `TauCeti.RiemannSurface.OneForm.inChartAt_mextDeriv_smul_toRoughForm`: its exterior derivative
  in a chart is `d((ψ f) dz)`.
* `TauCeti.RiemannSurface.OneForm.mextDeriv_smul_toRoughForm_eq_zero`: it is closed where the
  cutoff is locally constant.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §9 (differential forms on a Riemann surface, `ω = f dz` and `d(f dz) = 0` for `f` holomorphic)
  and Theorem 10.21 (the residue theorem).
-/

public noncomputable section

open Bundle Filter Function IsManifold Set Topology

open scoped Manifold TauCeti.ComplexManifold

namespace TauCeti.RiemannSurface.OneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {ω : OneForm X} {x : X}

/-- The **real form** of a `1`-form `ω` on a Riemann surface: the complex-valued real differential
form of degree one on the underlying real surface whose value at `x` is the covector `ω x`, regarded
as a real-linear map. In a chart it reads `f dz`
(`TauCeti.RiemannSurface.OneForm.inChartAt_toRoughForm`). -/
def toRoughForm (ω : OneForm X) : RoughForm 𝓘(ℝ, ℂ) X ℂ 1 :=
  fun x ↦ ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℂ (0 : Fin 1)
    ((ω x : ℂ →L[ℂ] ℂ).restrictScalars ℝ)

@[simp]
theorem toRoughForm_apply (ω : OneForm X) (x : X) (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) x) :
    ω.toRoughForm x v = ω x (v 0) :=
  (rfl)

@[simp]
theorem toRoughForm_add (ω η : OneForm X) : (ω + η).toRoughForm = ω.toRoughForm + η.toRoughForm :=
  (rfl)

@[simp]
theorem toRoughForm_smul (c : ℂ) (ω : OneForm X) : (c • ω).toRoughForm = c • ω.toRoughForm :=
  (rfl)

@[simp]
theorem toRoughForm_zero : (0 : OneForm X).toRoughForm = 0 :=
  (rfl)

/-- Multiplying a `1`-form by a real function multiplies its real form by that function. -/
theorem toRoughForm_ofReal_smul (ψ : X → ℝ) (ω : OneForm X) :
    toRoughForm (fun x ↦ (ψ x : ℂ) • ω x) = fun x ↦ ψ x • ω.toRoughForm x := by
  ext x v
  rw [toRoughForm_apply, ContinuousAlternatingMap.smul_apply, toRoughForm_apply]
  -- Both sides are `ψ x` times `ω x (v 0)`: on the left through `ℂ`, on the right through `ℝ`.
  exact (smul_apply (ω x) (ψ x : ℂ) (v 0)).trans (Complex.coe_smul _ _)

/-- **`ω = f dz` in a chart.** In the preferred chart at `x₀`, the real form of `ω` is its
coefficient in that chart times the complex `1`-form `dz`. -/
theorem inChartAt_toRoughForm [IsManifold 𝓘(ℂ) 1 X] (ω : OneForm X) (x₀ : X) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x₀).target) :
    ω.toRoughForm.inChartAt x₀ z = ω.coeff (chartAt ℂ x₀) z • dzForm := by
  set e := chartAt ℂ x₀
  have hd := mdifferentiableAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas (I := 𝓘(ℂ)) x₀) hz
  ext v
  -- The real derivative of the chart inverse is its complex derivative, both read in `ℂ`.
  have hv : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e.symm z (v 0) = mfderiv 𝓘(ℂ) 𝓘(ℂ) e.symm z (v 0) :=
    hd.mfderiv_modelWithCornersSelf_restrictScalars_apply ℝ (v 0)
  -- The vector `v 0` is `v 0` times the coordinate vector `∂/∂z`; the final `rfl` is Mathlib's
  -- identification of `TangentSpace 𝓘(ℂ) z` with `ℂ` through `NormedSpace.fromTangentSpace z`.
  have h1 : mfderiv 𝓘(ℂ) 𝓘(ℂ) e.symm z (v 0) =
      v 0 • mfderiv 𝓘(ℂ) 𝓘(ℂ) e.symm z ((NormedSpace.fromTangentSpace z).symm 1) := by
    rw [← map_smul, ← map_smul, smul_eq_mul, mul_one]
    rfl
  -- Since `ω = f dz` at `e.symm z` and `dz` takes the value `1` on `∂/∂z`, `ω (∂/∂z) = f`.
  have h2 : ω (e.symm z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) e.symm z ((NormedSpace.fromTangentSpace z).symm 1)) =
      ω.coeff e z := by
    rw [← ω.coeff_smul_mvfderiv (chart_mem_maximalAtlas x₀) hz, smul_apply,
      mvfderiv_mfderiv_symm (chart_mem_maximalAtlas x₀) hz, smul_eq_mul, mul_one]
  -- Normalize the chart: the left side is `ω` at `e.symm z` on the complex derivative of the chart
  -- inverse applied to `v 0`.
  have h3 : ω.toRoughForm.inChartAt x₀ z v =
      ω (e.symm z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) e.symm z (v 0)) := by
    rw [RoughForm.inChartAt_apply, toRoughForm_apply, extChartAt_model_symm_eq_chartAt_symm,
      ModelWithCorners.range_eq_univ, mfderivWithin_univ, hv]
  -- Evaluate: by `h1` and `h2` this is `v 0` times the coefficient, which is `(f dz) v`.
  simp [h3, h1, h2, mul_comm]

section IsManifold

variable [IsManifold 𝓘(ℂ) 1 X]

/-- Near every point of the target of the preferred chart at `x₀`, the real form of `ω` read in
that chart is `f dz`, with `f` the coefficient of `ω` in the chart. -/
theorem inChartAt_toRoughForm_eventuallyEq (ω : OneForm X) (x₀ : X) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x₀).target) :
    ω.toRoughForm.inChartAt x₀ =ᶠ[𝓝 z] fun y ↦ ω.coeff (chartAt ℂ x₀) y • dzForm := by
  filter_upwards [(chartAt ℂ x₀).open_target.mem_nhds hz] with y hy
  exact ω.inChartAt_toRoughForm x₀ hy

/-- The real form of a `1`-form is a `C^n` section near every point where the `1`-form is
holomorphic, for every `n`, including `n = ω` (real-analytic). -/
theorem contMDiffAt_toRoughForm {n : WithTop ℕ∞} (hω : ω.HolomorphicAt x) :
    ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ [⋀^Fin 1]→L[ℝ] ℂ)) n
      (fun y ↦ TotalSpace.mk' (ℂ [⋀^Fin 1]→L[ℝ] ℂ) y (ω.toRoughForm y)) x := by
  refine contMDiffAt_form_of_contDiffWithinAt_inChartAt_self ?_
  have hc : ContDiffAt ℝ n (fun y ↦ ω.coeff (chartAt ℂ x) y • dzForm) (chartAt ℂ x x) :=
    (((holomorphicAt_def ω x).1 hω).contDiffAt.restrict_scalars ℝ).smul contDiffAt_const
  exact (hc.congr_of_eventuallyEq
    (ω.inChartAt_toRoughForm_eventuallyEq x (mem_chart_target ℂ x))).contDiffWithinAt

/-- **A holomorphic `1`-form is a smooth real form**, of class `C^n` for every `n`. -/
theorem isSmoothForm_toRoughForm {n : WithTop ℕ∞} (hω : ∀ x, ω.HolomorphicAt x) :
    IsSmoothForm 𝓘(ℝ, ℂ) n ω.toRoughForm :=
  (isSmoothForm_def n _).2 fun x ↦ contMDiffAt_toRoughForm (hω x)

/-- **A holomorphic `1`-form is closed**: at a point where `ω = f dz` with `f` holomorphic, the
exterior derivative of its real form vanishes. -/
theorem mextDeriv_toRoughForm_eq_zero (hω : ω.HolomorphicAt x) :
    mextDeriv ω.toRoughForm x = 0 := by
  rw [mextDeriv_eq_extDeriv_inChartAt]
  exact ((ω.inChartAt_toRoughForm_eventuallyEq x (mem_chart_target ℂ x)).extDeriv_eq).trans
    ((holomorphicAt_def ω x).1 hω).differentiableAt.extDeriv_smul_dzForm

/-- The real form of a holomorphic `1`-form is closed. -/
theorem mextDeriv_toRoughForm (hω : ∀ x, ω.HolomorphicAt x) : mextDeriv ω.toRoughForm = 0 :=
  funext fun x ↦ mextDeriv_toRoughForm_eq_zero (hω x)

variable {ψ : X → ℝ}

/-- **Cutting off the singularities.** If the `C^n` real function `ψ` vanishes near every point
where `ω` is not holomorphic, the real form of `ψ ω` is `C^n`. For a meromorphic `1`-form, `ψ` is a
cutoff equal to `0` near the poles. -/
theorem isSmoothForm_smul_toRoughForm {n : WithTop ℕ∞} (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) n ψ)
    (hω : ∀ x ∈ tsupport ψ, ω.HolomorphicAt x) :
    IsSmoothForm 𝓘(ℝ, ℂ) n fun x ↦ ψ x • ω.toRoughForm x :=
  (isSmoothForm_def n _).2 <| hψ.contMDiffOn.smul_section_of_tsupport ω.isOpen_setOf_holomorphicAt
    hω fun _ hx ↦ (contMDiffAt_toRoughForm hx).contMDiffWithinAt

/-- **The exterior derivative of a cutoff `1`-form in a chart.** If the `C¹` real function `ψ`
vanishes near every point where `ω` is not holomorphic, then in the preferred chart at `x₀`,
where `ω = f dz`, the exterior derivative of the real form of `ψ ω` is the flat exterior derivative
of `(ψ f) dz`, with `ψ` read in the chart. -/
theorem inChartAt_mextDeriv_smul_toRoughForm (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 1 ψ)
    (hω : ∀ x ∈ tsupport ψ, ω.HolomorphicAt x) (x₀ : X) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x₀).target) :
    (mextDeriv fun x ↦ ψ x • ω.toRoughForm x).inChartAt x₀ z =
      extDeriv (fun y ↦ ((ψ ((chartAt ℂ x₀).symm y) : ℂ) * ω.coeff (chartAt ℂ x₀) y) • dzForm)
        z := by
  have : IsManifold 𝓘(ℝ, ℂ) 2 X := IsManifold.restrictScalars_of_ne_zero 2 one_ne_zero ‹_›
  have hint : z ∈ interior (extChartAt 𝓘(ℝ, ℂ) x₀).target := by
    simpa only [mfld_simps, (chartAt ℂ x₀).open_target.interior_eq] using hz
  rw [(isSmoothForm_smul_toRoughForm hψ hω).inChartAt_mextDeriv_eq_extDeriv x₀ hint]
  refine Filter.EventuallyEq.extDeriv_eq ?_
  filter_upwards [(chartAt ℂ x₀).open_target.mem_nhds hz] with y hy
  rw [RoughForm.inChartAt_fun_smul, ω.inChartAt_toRoughForm x₀ hy, mul_smul]
  exact (Complex.coe_smul _ _).symm

/-- **A cutoff `1`-form is closed where the cutoff is locally constant.** If `ψ` is equal to a
constant `c` near `x`, and `ω` is holomorphic at `x` unless `c = 0`, then the exterior derivative of
the real form of `ψ ω` vanishes at `x`. -/
theorem mextDeriv_smul_toRoughForm_eq_zero {c : ℝ} (hψ : ψ =ᶠ[𝓝 x] fun _ ↦ c)
    (hω : c ≠ 0 → ω.HolomorphicAt x) :
    mextDeriv (fun x ↦ ψ x • ω.toRoughForm x) x = 0 := by
  by_cases hc : c = 0
  · rw [mextDeriv_congr_of_eventuallyEq (η := 0) (by
      filter_upwards [hψ] with y hy
      simp [hy, hc]), mextDeriv_zero, Pi.zero_apply]
  · rw [mextDeriv_congr_of_eventuallyEq (η := c • ω.toRoughForm) (by
      filter_upwards [hψ] with y hy
      rw [hy, Pi.smul_apply]), mextDeriv_smul, Pi.smul_apply,
      mextDeriv_toRoughForm_eq_zero (hω hc), smul_zero]

end IsManifold

end TauCeti.RiemannSurface.OneForm
