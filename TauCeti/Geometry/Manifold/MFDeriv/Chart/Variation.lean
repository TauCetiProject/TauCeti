/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Chart variations of a curve

Let `γ : ℝ → M` be a curve, `ψ = extChartAt I x₀` the extended chart at a point `x₀`, `e` a
vector of the model space and `φ : ℝ → ℝ` a profile supported in a set `J` of parameters along
which `γ` stays in the chart. The **chart variation**
`TauCeti.Manifold.chartVariation I γ x₀ J φ e` is the two-parameter family
`(s, t) ↦ ψ⁻¹ (ψ (γ t) + (s φ(t)) • e)`, equal to `γ t` outside `J`: it pushes `γ` in the
direction of the coordinate vector `e`, with profile `φ`.

These variations are the test variations of first variation arguments: a curve along which a
functional is stationary for every chart variation satisfies the pointwise Euler–Lagrange
equation. On a manifold without boundary the chart variation is as regular as `γ`, `φ` and the
manifold, wherever the displaced points stay in the chart target, and its variation field is
`φ t` times the tangent vector at `γ t` with coordinates `e` in the tangent-bundle trivialization
at `x₀`.

The displaced points stay in the chart target only for small amplitudes. Variations defined on the
whole plane, as functionals on loops or paths require, use the amplitude `sin s` instead of `s`
(`TauCeti.Manifold.sinChartVariation`): it stays in `[-1, 1]` and has derivative `1` at `s = 0`.
So if the points displaced by amplitudes in `[-1, 1]` stay in the chart target, as they do for a
displacement `φ t • e` small enough along `J`, then the variation is `C^n` on the whole plane for
`C^n` data, and it has the same variation field at `s = 0`.

## Main definitions and results

* `TauCeti.Manifold.chartVariation`: the chart variation of a curve.
* `TauCeti.Manifold.chartVariation_zero`: its central curve is `γ`.
* `TauCeti.Manifold.contMDiffAt_chartVariation`: it is `C^n` at `(s, t)` when `γ` is `C^n` at `t`
  and the displaced point lies in the chart target.
* `TauCeti.Manifold.variationField_chartVariation`: its variation field.
* `TauCeti.Manifold.sinChartVariation`: the chart variation with amplitude `sin s`, a map of the
  plane.
* `TauCeti.Manifold.contMDiff_sinChartVariation`: it is `C^n` on the plane for `C^n` data when the
  points displaced by amplitudes in `[-1, 1]` stay in the chart target.
* `TauCeti.Manifold.mfderiv_sinChartVariation_of_mem`: its variation field at `s = 0` is `φ t`
  times the tangent vector of chart coordinates `e`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 9, §2, proof of Proposition 2.5
  (variations along a field `f V` supported near a parameter).
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞} {γ : ℝ → M} {x₀ : M} {J : Set ℝ} {φ : ℝ → ℝ} {e : E}

open scoped Classical in
variable (I) in
/-- The variation of `γ` which, at the parameters of `J`, pushes `γ t` in the direction of the
coordinate vector `e` of the extended chart at `x₀`, with profile `φ`:
`(s, t) ↦ ψ⁻¹ (ψ (γ t) + (s φ(t)) • e)` for `ψ = extChartAt I x₀`.  Outside `J` it is `γ`. -/
def chartVariation (γ : ℝ → M) (x₀ : M) (J : Set ℝ) (φ : ℝ → ℝ) (e : E) (s t : ℝ) : M :=
  if t ∈ J then (extChartAt I x₀).symm (extChartAt I x₀ (γ t) + (s * φ t) • e) else γ t

/-- At a parameter of `J`, the chart variation is given by the chart formula. -/
theorem chartVariation_of_mem {t : ℝ} (ht : t ∈ J) (s : ℝ) :
    chartVariation I γ x₀ J φ e s t =
      (extChartAt I x₀).symm (extChartAt I x₀ (γ t) + (s * φ t) • e) := by
  simp [chartVariation, ht]

/-- Outside `J`, the chart variation is `γ`. -/
@[simp]
theorem chartVariation_of_notMem {t : ℝ} (ht : t ∉ J) (s : ℝ) :
    chartVariation I γ x₀ J φ e s t = γ t := by
  simp [chartVariation, ht]

/-- Where the displacement `s φ(t)` vanishes, the chart variation is `γ`. -/
theorem chartVariation_of_mul_eq_zero (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source)
    {s t : ℝ} (h : s * φ t = 0) : chartVariation I γ x₀ J φ e s t = γ t := by
  by_cases htJ : t ∈ J
  · rw [chartVariation_of_mem htJ, h, zero_smul, add_zero]
    exact (extChartAt I x₀).left_inv (hJ t htJ)
  · exact chartVariation_of_notMem htJ s

/-- The central curve of the chart variation is `γ`. -/
theorem chartVariation_zero (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source) :
    chartVariation I γ x₀ J φ e 0 = γ :=
  funext fun _ ↦ chartVariation_of_mul_eq_zero hJ (zero_mul _)

section Boundaryless

variable [I.Boundaryless]

/-- On a `C^n` manifold without boundary, the chart variation of a curve which is `C^n` at `t`,
for a `C^n` profile supported in the open set `J`, is `C^n` at `(s, t)` provided that, if `t ∈ J`,
the displaced point `ψ (γ t) + (s φ(t)) • e` lies in the chart target. -/
theorem contMDiffAt_chartVariation [IsManifold I n M] (hJo : IsOpen J)
    (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source) (hφ : ContDiff ℝ n φ) (hφJ : tsupport φ ⊆ J)
    {s t : ℝ} (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hT : t ∈ J → extChartAt I x₀ (γ t) + (s * φ t) • e ∈ (extChartAt I x₀).target) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ chartVariation I γ x₀ J φ e z.1 z.2) (s, t) := by
  by_cases htJ : t ∈ J
  · -- near `(s, t)` the family is given by the chart formula
    have hc : ContDiffAt ℝ n (extChartAt I x₀ ∘ γ) t :=
      contMDiffAt_iff_contDiffAt.mp
        ((contMDiffAt_extChartAt' (by simpa using hJ t htJ)).comp t hγ)
    have hg : ContDiffAt ℝ n (fun z : ℝ × ℝ ↦ extChartAt I x₀ (γ z.2) + (z.1 * φ z.2) • e)
        (s, t) :=
      (hc.comp (s, t) contDiffAt_snd).add
        ((contDiffAt_fst.mul (hφ.contDiffAt.comp (s, t) contDiffAt_snd)).smul contDiffAt_const)
    have hmem := hT htJ
    have hsymm : ContMDiffAt 𝓘(ℝ, E) I n (extChartAt I x₀).symm
        (extChartAt I x₀ (γ t) + (s * φ t) • e) :=
      (contMDiffOn_extChartAt_symm x₀ _ hmem).contMDiffAt
        ((isOpen_extChartAt_target x₀).mem_nhds hmem)
    refine (hsymm.comp (s, t) (contMDiffAt_iff_contDiffAt.mpr hg)).congr_of_eventuallyEq ?_
    filter_upwards [continuousAt_snd.preimage_mem_nhds (hJo.mem_nhds htJ)] with z hz
    exact chartVariation_of_mem hz z.1
  · -- away from the support of `φ` the family is `γ`, which is `C^n` near `t`
    have hev : φ =ᶠ[𝓝 t] 0 := notMem_tsupport_iff_eventuallyEq.mp fun h ↦ htJ (hφJ h)
    refine (hγ.comp (s, t) contDiff_snd.contMDiff.contMDiffAt).congr_of_eventuallyEq ?_
    filter_upwards [continuousAt_snd.preimage_mem_nhds hev] with z hz
    exact chartVariation_of_mul_eq_zero hJ (by rw [hz, Pi.zero_apply, mul_zero])

variable [IsManifold I 1 M]

/-- At a parameter of `J`, the variation field of the chart variation is `φ t` times the tangent
vector at `γ t` with coordinates `e` in the tangent-bundle trivialization at `x₀`. -/
theorem variationField_chartVariation (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source)
    {t : ℝ} (htJ : t ∈ J) :
    variationField I (chartVariation I γ x₀ J φ e) t =
      φ t • (trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ t) e := by
  have hmem : extChartAt I x₀ (γ t) ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source (hJ t htJ)
  have hfun : (fun s ↦ chartVariation I γ x₀ J φ e s t) =
      (extChartAt I x₀).symm ∘ fun s : ℝ ↦ extChartAt I x₀ (γ t) + (s * φ t) • e :=
    funext fun s ↦ chartVariation_of_mem htJ s
  have hderiv : HasDerivAt (fun s : ℝ ↦ extChartAt I x₀ (γ t) + (s * φ t) • e) (φ t • e) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (φ t)).smul_const e).const_add
      (extChartAt I x₀ (γ t))
  have hmd : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x₀).symm (extChartAt I x₀ (γ t)) :=
    (mdifferentiableWithinAt_extChartAt_symm hmem).mdifferentiableAt
      (by rw [I.range_eq_univ]; exact univ_mem)
  -- the chain rule, with the base point `ψ (γ t) + (0 * φ t) • e` of the transverse curve
  -- normalized to `ψ (γ t)`
  have hvel : ∀ y, extChartAt I x₀ (γ t) + ((0 : ℝ) * φ t) • e = y →
      curveVelocity I ((extChartAt I x₀).symm ∘ fun s : ℝ ↦ extChartAt I x₀ (γ t) + (s * φ t) • e)
        0 = mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y (φ t • e) := by
    rintro y rfl
    exact MDifferentiableAt.curveVelocity_comp_mfderiv (by simpa using hmd) hderiv
  rw [variationField_apply, hfun, hvel (extChartAt I x₀ (γ t)) (by simp),
    TangentBundle.symmL_trivializationAt (by simpa using hJ t htJ), I.range_eq_univ,
    mfderivWithin_univ]
  exact (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm (extChartAt I x₀ (γ t))).map_smul (φ t) e

end Boundaryless

/-! ### Chart variations defined on the whole plane -/

section Sin

variable (I) in
/-- The chart variation of `γ` with amplitude `sin s`, as a map of the plane:
`(s, t) ↦ ψ⁻¹ (ψ (γ t) + (sin s * φ t) • e)` at the parameters of `J`, and `γ` outside `J`. As the
amplitude stays in `[-1, 1]`, the displaced points stay in the chart target for every `s` as soon as
those displaced by amplitudes in `[-1, 1]` do, for instance when `φ t • e` is small enough along
`J`. -/
def sinChartVariation (γ : ℝ → M) (x₀ : M) (J : Set ℝ) (φ : ℝ → ℝ) (e : E) (z : ℝ × ℝ) : M :=
  chartVariation I γ x₀ J φ e (Real.sin z.1) z.2

theorem sinChartVariation_apply (z : ℝ × ℝ) :
    sinChartVariation I γ x₀ J φ e z = chartVariation I γ x₀ J φ e (Real.sin z.1) z.2 :=
  (rfl)

/-- Outside `J`, the chart variation with amplitude `sin s` is `γ`. -/
@[simp]
theorem sinChartVariation_of_notMem {t : ℝ} (ht : t ∉ J) (s : ℝ) :
    sinChartVariation I γ x₀ J φ e (s, t) = γ t :=
  chartVariation_of_notMem ht _

/-- The central curve of the chart variation with amplitude `sin s` is `γ`. -/
theorem sinChartVariation_zero (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source) (t : ℝ) :
    sinChartVariation I γ x₀ J φ e (0, t) = γ t :=
  chartVariation_of_mul_eq_zero hJ (by rw [Real.sin_zero, zero_mul])

/-- Outside `J`, the variation field of the chart variation with amplitude `sin s` vanishes. -/
theorem mfderiv_sinChartVariation_of_notMem {t : ℝ}
    (hw : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (sinChartVariation I γ x₀ J φ e) (0, t))
    (htJ : t ∉ J) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I (sinChartVariation I γ x₀ J φ e) (0, t) (1, 0) = 0 :=
  mfderiv_apply_one_zero_eq_zero_of_apply_eq hw fun s ↦ sinChartVariation_of_notMem htJ s

variable [I.Boundaryless]

/-- On a `C^n` manifold without boundary, the chart variation with amplitude `sin s` of a `C^n`
curve, for a `C^n` profile supported in the open set `J` along which the points displaced by
amplitudes in `[-1, 1]` stay in the chart target, is `C^n` on the plane. -/
theorem contMDiff_sinChartVariation [IsManifold I n M] (hJo : IsOpen J)
    (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source)
    (hT : ∀ t ∈ J, ∀ c : ℝ, |c| ≤ 1 →
      extChartAt I x₀ (γ t) + (c * φ t) • e ∈ (extChartAt I x₀).target)
    (hφ : ContDiff ℝ n φ) (hφJ : tsupport φ ⊆ J) (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I n (sinChartVariation I γ x₀ J φ e) := by
  rintro ⟨s, t⟩
  exact (contMDiffAt_chartVariation hJo hJ hφ hφJ (hγ t)
    fun htJ ↦ hT t htJ _ (Real.abs_sin_le_one s)).comp (s, t)
    ((Real.contDiff_sin.prodMap contDiff_id).contMDiff (s, t))

/-- The variation field of the chart variation with amplitude `sin s`: at a parameter `t` of `J`
it is `φ t` times the tangent vector at `γ t` with coordinates `e` in the tangent-bundle
trivialization at `x₀`. -/
theorem mfderiv_sinChartVariation_of_mem [IsManifold I 1 M] (hJo : IsOpen J)
    (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source) (hφ : ContDiff ℝ 1 φ) (hφJ : tsupport φ ⊆ J)
    {t : ℝ} (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t)
    (hw : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (sinChartVariation I γ x₀ J φ e) (0, t)) (htJ : t ∈ J) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I (sinChartVariation I γ x₀ J φ e) (0, t) (1, 0) =
      φ t • (trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ t) e := by
  -- the transverse curve of the chart variation at `t` is differentiable at `s = 0`
  have hd : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s ↦ chartVariation I γ x₀ J φ e s t) 0 :=
    ((contMDiffAt_chartVariation (n := 1) (e := e) (s := 0) hJo hJ hφ hφJ hγ
      fun htJ ↦ by simpa using (extChartAt I x₀).map_source (hJ t htJ)).comp 0
      ((contDiff_id.prodMk contDiff_const).contMDiff 0)).mdifferentiableAt one_ne_zero
  -- reparametrizing by `s ↦ sin s`, whose derivative at `0` is `1`, with the base point `sin 0`
  -- normalized to `0`
  have hvel : ∀ y, Real.sin 0 = y →
      MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s ↦ chartVariation I γ x₀ J φ e s t) y →
      curveVelocity I (fun s ↦ sinChartVariation I γ x₀ J φ e (s, t)) 0 =
        curveVelocity I (fun s ↦ chartVariation I γ x₀ J φ e s t) y := by
    rintro y rfl hy
    have h := curveVelocity_comp (c := 1) (by simpa using Real.hasDerivAt_sin 0) hy
    rw [one_smul] at h
    exact h
  rw [← curveVelocity_eq_mfderiv_fst (f := fun a b ↦ sinChartVariation I γ x₀ J φ e (a, b)) hw,
    hvel 0 Real.sin_zero hd, ← variationField_apply, variationField_chartVariation hJ htJ]

end Sin

end TauCeti.Manifold

end
