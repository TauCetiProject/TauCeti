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
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
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
fields: compactly supported real test functions determine a tempered distribution
(`TemperedDistribution.ext_real`), and on Schwartz fields the transpose of the tempered vacuum
operator is `vacuumAdjoint`. Since `L₀ : H¹ → L²` is bijective on tempered fields
(`TauCeti.Vortex.memSobolev_temperedVacuumOperator_iff`), `y ∈ H¹`.

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

/-! ### Tempered distributions of square-integrable fields -/

private theorem memLp_apply {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y 2 volume)
    (i : Fin 4) : MemLp (fun z ↦ y z i) 2 volume :=
  (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ).comp_memLp' hy

/-- The field of complex tempered distributions of the components of a square-integrable
field. -/
private def temperedField {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y 2 volume) :
    Fin 4 → 𝓢'(ℂ, ℂ) :=
  fun i ↦ Lp.toTemperedDistribution (ofRealCLM.compLp ((memLp_apply hy i).toLp _))

private theorem temperedField_apply {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y 2 volume)
    (i : Fin 4) (ψ : 𝓢(ℂ, ℂ)) : temperedField hy i ψ = ∫ z, ψ z * (y z i : ℂ) := by
  rw [temperedField, Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [ofRealCLM.coeFn_compLp (p := 2) (μ := volume) ((memLp_apply hy i).toLp _),
    (memLp_apply hy i).coeFn_toLp] with z h₁ h₂
  rw [h₁, smul_eq_mul, ofRealCLM_apply, h₂]

/-- The components of a real Schwartz field, as complex Schwartz functions. -/
private abbrev cpt (η : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) (i : Fin 4) : 𝓢(ℂ, ℂ) :=
  η.postcompCLM (ofRealCLM ∘L EuclideanSpace.proj i)

@[simp]
private theorem cpt_apply (η : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) (i : Fin 4) (z : ℂ) :
    cpt η i z = (η z i : ℂ) :=
  rfl

/-- Pairing the tempered field of `y` with a real Schwartz field `η` gives `∫ ⟪y, η⟫`. -/
private theorem sum_temperedField_apply {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : MemLp y 2 volume) (η : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    ∑ i, temperedField hy i (cpt η i) = ((∫ z, ⟪y z, η z⟫ : ℝ) : ℂ) := by
  have hint (i : Fin 4) : Integrable (fun z ↦ η z i * y z i) volume :=
    (memLp_apply (η.memLp 2) i).integrable_mul (memLp_apply hy i)
  simp_rw [temperedField_apply, cpt_apply, ← ofReal_mul, integral_complex_ofReal, ← ofReal_sum,
    ← integral_finsetSum _ fun i _ ↦ hint i]
  simp_rw [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]

/-- On real Schwartz fields, the transpose of the tempered vacuum operator is `vacuumAdjoint`. -/
private theorem sum_temperedVacuumOperator_apply (T : Fin 4 → 𝓢'(ℂ, ℂ))
    (η : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    ∑ i, temperedVacuumOperator T i (cpt η i) = ∑ i, T i (cpt (vacuumAdjoint η) i) := by
  have h₀ : cpt (vacuumAdjoint η) 0 =
      -cpt (∂_{(1 : ℂ)} η) 0 - cpt (∂_{I} η) 1 + (1 / 2 : ℂ) • cpt η 3 := by
    ext z; simp [div_eq_inv_mul]
  have h₁ : cpt (vacuumAdjoint η) 1 =
      -cpt (∂_{I} η) 0 + cpt (∂_{(1 : ℂ)} η) 1 - (1 / 2 : ℂ) • cpt η 2 := by
    ext z; simp [div_eq_inv_mul]
  have h₂ : cpt (vacuumAdjoint η) 2 =
      -cpt (∂_{(1 : ℂ)} η) 2 - cpt (∂_{I} η) 3 + (1 / 2 : ℂ) • cpt η 1 := by
    ext z; simp [div_eq_inv_mul]
  have h₃ : cpt (vacuumAdjoint η) 3 =
      cpt (∂_{I} η) 2 - cpt (∂_{(1 : ℂ)} η) 3 + (1 / 2 : ℂ) • cpt η 0 := by
    ext z; simp [div_eq_inv_mul]
  simp only [Fin.sum_univ_four, h₀, h₁, h₂, h₃, temperedVacuumOperator_apply_zero,
    temperedVacuumOperator_apply_one, temperedVacuumOperator_apply_two,
    temperedVacuumOperator_apply_three, add_apply, sub_apply, smul_apply, lineDerivOp_apply_apply,
    TauCeti.lineDerivOp_postcompCLM, map_add, map_sub, map_neg, map_smul, real_smul, smul_eq_mul]
  push_cast
  ring

/-- Two tempered fields agree if their pairings with all compactly supported real Schwartz fields
agree. -/
private theorem eq_of_sum_apply_eq {U V : Fin 4 → 𝓢'(ℂ, ℂ)}
    (h : ∀ η : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4)), HasCompactSupport η →
      ∑ i, U i (cpt η i) = ∑ i, V i (cpt η i)) : U = V := by
  funext j
  refine ext_real fun φ hφ ↦ ?_
  set η : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) :=
    φ.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single j (1 : ℝ)))
  have hη : HasCompactSupport η := by
    have : (η : ℂ → EuclideanSpace ℝ (Fin 4)) =
        ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single j (1 : ℝ)) ∘ φ :=
      funext fun _ ↦ rfl
    rw [this]
    exact hφ.comp_left (map_zero _)
  have hc (i : Fin 4) :
      cpt η i = if i = j then φ.postcompCLM ofRealCLM else 0 := by
    ext z
    by_cases hij : i = j
    · subst hij; simp [η]
    · simp [η, hij]
  simpa [hc, apply_ite] using h η hη

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
  have hS : ∀ i, MemSobolev 1 2 (temperedField hy i) := by
    refine memSobolev_temperedVacuumOperator_iff.1 fun i ↦ ?_
    rw [hT, sub_self]
    exact memSobolev_zero_iff.2 ⟨_, rfl⟩
  exact mem_sobolevFields.2 fun i ↦
    mem_realSobolevFunctions.2 ⟨_, (memLp_apply hy i).coeFn_toLp, hS i⟩

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
