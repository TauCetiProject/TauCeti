/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.GaugeFixed
public import TauCeti.Analysis.PDE.Vortex.RightInverse
public import TauCeti.Analysis.PDE.Vortex.VacuumOperator.Sobolev
import TauCeti.MeasureTheory.Function.L2Space

/-!
# Weak solutions of the gauge-fixed vortex equation lie in `H¹`

A square-integrable field `y` is a weak solution of `L_x y = f` if
`∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every compactly supported `C²` test field `η`
(see `TauCeti.Analysis.PDE.Vortex.RightInverse`). This file proves the first step of elliptic
regularity for these solutions: if the field `x` is bounded and `f ∈ L²`, then `y ∈ H¹`
(`TauCeti.Vortex.mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq`).

The derivative part of `L_x*` has constant coefficients and does not depend on `x`: it is the
derivative part of the vacuum adjoint `L₀*`. The remaining zero-order part is linear in `x`, so
`L_x* η = L₀* η + M_{x - x₀} η`, where `x₀` is the vacuum field and `M_w` is a matrix depending
linearly on `w`. Hence a weak solution of `L_x y = f` is a weak solution of `L₀ y = g` with
`g = f - M_{x - x₀}ᵀ y`, and `g ∈ L²` because `x` is bounded. Read through the tempered
distributions of the components of `y` and `g`, this is the identity `L₀ y = g` of tempered
fields (`TauCeti.Vortex.temperedField`): compactly supported real test fields determine a
tempered field (`TauCeti.Vortex.eq_of_sum_apply_eq`), and on Schwartz fields the transpose of
the tempered vacuum operator is `vacuumAdjoint`
(`TauCeti.Vortex.sum_temperedVacuumOperator_apply`). Since `L₀ : H¹ → L²` is bijective on
tempered fields (`TauCeti.Vortex.memSobolev_temperedVacuumOperator_iff`), `y ∈ H¹`.

A continuous field of the affine space `A_m^s`, `s > 1`, is bounded, so at such a field the
weak kernel of `L_x` lies in `H¹`, and so does the image of the weak right inverse `Q` of
`TauCeti.Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`
(`exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_and_mem_sobolevFields`).
These are the regularity statements that place the weak theory of `L_x` on the Sobolev scale
`H¹ → L²`; higher regularity and the Fredholm property are not treated here.

## Main results

* `TauCeti.Vortex.mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq`: at a bounded
  field, an `L²` weak solution of `L_x y = f ∈ L²` lies in `H¹`.
* `TauCeti.Vortex.mem_sobolevFields_one_of_mem_framedFieldSpace`: the same at a continuous field
  of `A_m^s`, `s > 1`, which is bounded by `TauCeti.Vortex.exists_norm_le_of_mem_framedFieldSpace`.
* `exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_and_mem_sobolevFields`: at a
  `C¹` vortex of `A_m^s`, `s > 1`, the weak right inverse of `L_x` takes values in `H¹`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* M. Taylor, *Partial Differential Equations I*, Chapter 4, §1 (the Sobolev spaces `H^s`).
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap LineDeriv RealInnerProductSpace Topology

/-! ### The zero-order part of `L_x*` -/

/-- The transpose of the zero-order part of `L_x*` at a point where `x` takes the value `w`,
applied to `v`: `⟪v, M_w η⟫ = ⟪couplingFun w v, η⟫`. -/
private def couplingFun (w v : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) :=
  !₂[-w 3 * v 2 + w 2 * v 3, w 2 * v 2 + w 3 * v 3,
    -w 3 * v 0 - w 2 * v 1 - w 1 * v 2 - w 0 * v 3,
    w 2 * v 0 - w 3 * v 1 + w 0 * v 2 - w 1 * v 3]

/-- `couplingFun` as a continuous bilinear map. -/
private def coupling :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ couplingFun
        (fun _ _ _ ↦ by ext i; fin_cases i <;> simp [couplingFun] <;> ring)
        (fun _ _ _ ↦ by ext i; fin_cases i <;> simp [couplingFun] <;> ring)
        (fun _ _ _ ↦ by ext i; fin_cases i <;> simp [couplingFun] <;> ring)
        (fun _ _ _ ↦ by ext i; fin_cases i <;> simp [couplingFun] <;> ring))

private theorem coupling_apply (w v : EuclideanSpace ℝ (Fin 4)) :
    coupling w v = couplingFun w v :=
  rfl

/-- `L_x* η = L₀* η + M_{x - x₀} η`, paired with a vector `v`. -/
private theorem inner_gaugeFixedAdjoint (x η : ℂ → EuclideanSpace ℝ (Fin 4))
    (v : EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    ⟪v, gaugeFixedAdjoint x η z⟫ = ⟪v, gaugeFixedAdjoint vacuumField η z⟫ +
      ⟪coupling (x z - vacuumField z) v, η z⟫ := by
  simp [coupling_apply, couplingFun, PiLp.inner_apply, Fin.sum_univ_four, vacuumField_apply]
  ring

/-! ### `H¹` regularity -/

/-- **Weak solutions of the gauge-fixed vortex equation lie in `H¹`.** Let `x` be an essentially
bounded field and `f ∈ L²(ℂ; ℝ⁴)`. If `y ∈ L²(ℂ; ℝ⁴)` is a weak solution of `L_x y = f`, that is
`∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every compactly supported `C²` field `η`, then `y ∈ H¹`. -/
theorem mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : AEStronglyMeasurable x volume) {C : ℝ}
    (hC : ∀ᵐ z, ‖x z‖ ≤ C) (hy : MemLp y 2 volume) (hf : MemLp f 2 volume)
    (h : ∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    y ∈ sobolevFields 1 := by
  -- The zero-order part of `L_x - L₀` applied to `y` is square integrable.
  set k : ℂ → EuclideanSpace ℝ (Fin 4) := fun z ↦ coupling (x z - vacuumField z) (y z)
  have hk : MemLp k 2 volume := by
    refine hy.of_le_mul (c := ‖coupling‖ * (C + ‖vacuumField 0‖))
      (coupling.aestronglyMeasurable_comp₂ (hx.sub (continuous_const.congr fun z ↦
        (vacuumField_apply z).symm).aestronglyMeasurable) hy.aestronglyMeasurable) ?_
    filter_upwards [hC] with z hz
    calc ‖k z‖ ≤ ‖coupling‖ * ‖x z - vacuumField z‖ * ‖y z‖ := coupling.le_opNorm₂ _ _
      _ ≤ ‖coupling‖ * (C + ‖vacuumField 0‖) * ‖y z‖ := by
        gcongr
        rw [vacuumField_apply, ← vacuumField_apply 0]
        exact (norm_sub_le _ _).trans (add_le_add hz le_rfl)
  have hg : MemLp (f - k) 2 volume := hf.sub hk
  -- `y` is a weak solution of `L₀ y = f - k` against compactly supported Schwartz fields.
  have hvac (η : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) (hη : HasCompactSupport η) :
      ∫ z, ⟪y z, vacuumAdjoint η z⟫ = ∫ z, ⟪(f - k) z, η z⟫ := by
    have hw := h η (η.smooth 2) hη
    have hη₂ := η.memLp 2 (μ := volume)
    simp_rw [inner_gaugeFixedAdjoint x η, gaugeFixedAdjoint_vacuumField] at hw
    rw [integral_add (hy.integrable_inner ((vacuumAdjoint η).memLp 2))
      (hk.integrable_inner hη₂)] at hw
    simp_rw [Pi.sub_apply, inner_sub_left]
    rw [integral_sub (hf.integrable_inner hη₂) (hk.integrable_inner hη₂)]
    linarith
  -- Hence `L₀` maps the tempered field of `y` to that of `f - k`.
  have hT : temperedVacuumOperator (temperedField hy) = temperedField hg :=
    eq_of_sum_apply_eq fun η hη ↦ by
      rw [sum_temperedVacuumOperator_apply, sum_temperedField_apply, sum_temperedField_apply,
        hvac η hη]
  refine (mem_sobolevFields_iff_memSobolev_temperedField hy).2 <|
    memSobolev_temperedVacuumOperator_iff.1 fun i ↦ ?_
  rw [hT, sub_self]
  exact memSobolev_zero_temperedField hg i

/-! ### Fields of `A_m^s` and plane vortices -/

/-- **Weak solutions at a field of `A_m^s` lie in `H¹`.** Let `x` be a continuous field of the
affine space `A_m^s`, `s > 1`, and `f ∈ L²(ℂ; ℝ⁴)`. Every `L²` weak solution of `L_x y = f` lies
in `H¹`; in particular the weak kernel of `L_x` lies in `H¹`. -/
theorem mem_sobolevFields_one_of_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)} {m : ℕ} {s : ℝ}
    (hs : 1 < s) {x y g : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m s)
    (hcont : Continuous x) (hy : MemLp y 2 volume) (hg : MemLp g 2 volume)
    (h : ∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪g z, η z⟫) :
    y ∈ sobolevFields 1 :=
  let ⟨_, hC⟩ := exists_norm_le_of_mem_framedFieldSpace hs hx hcont
  mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq hcont.aestronglyMeasurable
    (ae_of_all _ hC) hy hg h

/-- **The weak right inverse at a plane vortex takes values in `H¹`.** Let `x` be a `C¹` solution
of the plane vortex equation in the affine space `A_m^s`, `s > 1`. Then there is a bounded
operator `Q` on `L²(ℂ; ℝ⁴)` such that, for every `g ∈ L²`, `Q g` is a weak solution of
`L_x y = g`, orthogonal to the weak kernel of `L_x`, and lies in `H¹`. -/
theorem exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_and_mem_sobolevFields
    {f : ContDiffBump (0 : ℝ)} {m : ℕ} {s : ℝ} (hs : 1 < s) {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedFieldSpace f m s) (hx₁ : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) →L[ℝ]
        Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ),
      (∀ g η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪Q g z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪g z, η z⟫) ∧
      (∀ g u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ),
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0) →
        ∫ z, ⟪Q g z, u z⟫ = 0) ∧
      ∀ g, (Q g : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields 1 := by
  obtain ⟨Q, hQ, hQK⟩ := exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq
    (μ := volume) hx₁ hsol (tendsto_normSq_of_mem_framedFieldSpace hs hx hx₁.continuous)
  exact ⟨Q, hQ, hQK, fun g ↦ mem_sobolevFields_one_of_mem_framedFieldSpace hs hx hx₁.continuous
    (Lp.memLp _) (Lp.memLp g) (hQ g)⟩

end TauCeti.Vortex
