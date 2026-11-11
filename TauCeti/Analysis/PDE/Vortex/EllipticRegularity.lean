/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.RightInverse
public import TauCeti.Analysis.PDE.Vortex.VacuumOperator.Sobolev
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.MeasureTheory.Function.L2Space

/-!
# Weak solutions of the gauge-fixed vortex operator lie in `H¹`

At a field `x = (A₁, A₂, P, Q)`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁`
(`TauCeti.Vortex.gaugeFixedOperator`) is a first-order operator on fields `ℂ → ℝ⁴`. Its
derivative part does not depend on `x`: it is the derivative part of the vacuum operator `L₀`
(`TauCeti.Vortex.vacuumOperator`), two copies of a Cauchy–Riemann operator. The coefficients of
`x` enter only through a zeroth-order term, bilinear in `x` and the variation. Hence

`L_x y = L₀ y + (Z(x) - Z(x₀)) y`,

where `x₀` is the vacuum and `Z(x) y` is the zeroth-order part of `L_x y`.

A square-integrable field `y` is a weak solution of `L_x y = f`, for `f ∈ L²(ℂ; ℝ⁴)`, if
`∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every compactly supported smooth field `η`; this is the notion of
`TauCeti.Analysis.PDE.Vortex.RightInverse`. When `x` is essentially bounded, the zeroth-order term
`(Z(x) - Z(x₀)) y` is square integrable, so `y` is a weak solution of `L₀ y = g` with
`g = f - (Z(x) - Z(x₀)) y ∈ L²`. Viewing the components of `y` as tempered distributions, this says
that the tempered vacuum operator (`TauCeti.Vortex.temperedVacuumOperator`) sends `y` to `g`, and
since `L₀ : H¹ → L²` is a bijection on the Sobolev scale
(`TauCeti.Vortex.memSobolev_temperedVacuumOperator_iff`), `y` lies in `H¹`
(`TauCeti.Vortex.mem_sobolevFields_one_of_forall_integral_inner_gaugeFixedAdjoint_eq`). No
regularity of `x` beyond boundedness and measurability is needed, and no cutoff: the comparison
with the vacuum is global.

In particular the weak kernel of `L_x` lies in `H¹`, and at a bounded plane vortex with
`|α| → 1`, where the weak cokernel vanishes
(`TauCeti.Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`), every
`f ∈ L²` is `L_x y` for a weak solution `y ∈ H¹`
(`TauCeti.Vortex.exists_mem_sobolevFields_one_forall_integral_inner_gaugeFixedAdjoint_eq`). This
is the first step of elliptic regularity for `L_x`; the higher Sobolev orders, which need
derivatives of `x`, are not treated here.

## Main results

* `TauCeti.Vortex.mem_sobolevFields_one_of_forall_integral_inner_gaugeFixedAdjoint_eq`: a weak
  `L²` solution of `L_x y = f ∈ L²` at an essentially bounded field `x` lies in `H¹`.
* `TauCeti.Vortex.exists_mem_sobolevFields_one_forall_integral_inner_gaugeFixedAdjoint_eq`: at a
  bounded `C¹` plane vortex with `|α| → 1`, every `f ∈ L²` has a weak solution `y ∈ H¹` of
  `L_x y = f`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* M. Taylor, *Partial Differential Equations I*, Chapter 4, §1 (the Sobolev spaces `H^s`).
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap LineDeriv RealInnerProductSpace ContDiff Topology

/-- The zeroth-order part of `L_x` at a point where the field takes the value `u`, applied to the
value `v` of a variation. -/
private def zerothOrder (u v : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) :=
  !₂[u 2 * v 3 - u 3 * v 2, u 2 * v 2 + u 3 * v 3,
    -(u 0 * v 3) - v 0 * u 3 - u 1 * v 2 - v 1 * u 2,
    u 0 * v 2 + v 0 * u 2 - u 1 * v 3 - v 1 * u 3]

/-- The formal adjoint `L_x*` differs from the vacuum adjoint only by the transpose of the
zeroth-order part. -/
private theorem inner_gaugeFixedAdjoint_eq (x η : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ)
    (v : EuclideanSpace ℝ (Fin 4)) :
    ⟪v, gaugeFixedAdjoint x η z⟫ = ⟪v, gaugeFixedAdjoint vacuumField η z⟫ +
      ⟪zerothOrder (x z) v - zerothOrder (vacuumField z) v, η z⟫ := by
  simp [zerothOrder, vacuumField_apply, PiLp.inner_apply, Fin.sum_univ_four,
    gaugeFixedAdjoint_apply_zero, gaugeFixedAdjoint_apply_one, gaugeFixedAdjoint_apply_two,
    gaugeFixedAdjoint_apply_three]
  ring

/-- The zeroth-order part of `L_x` at an essentially bounded field `x`, applied to an `L²`
variation, is square integrable. -/
private theorem memLp_zerothOrder {x y : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : MemLp x ⊤ volume)
    (hy : MemLp y 2 volume) (i : Fin 4) :
    MemLp (fun z ↦ zerothOrder (x z) (y z) i) 2 volume := by
  have hxc (j : Fin 4) : MemLp (fun z ↦ x z j) ⊤ volume :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp' hx
  have hyc (j : Fin 4) : MemLp (fun z ↦ y z j) 2 volume :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp' hy
  have hm (a b : Fin 4) : MemLp (fun z ↦ x z a * y z b) 2 volume := (hxc a).fun_mul (hyc b)
  have hm' (a b : Fin 4) : MemLp (fun z ↦ y z b * x z a) 2 volume := (hyc b).fun_mul (hxc a)
  fin_cases i <;> simp only [zerothOrder, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Fin.isValue, PiLp.toLp_apply, Matrix.cons_val]
  exacts [(hm 2 3).sub (hm 3 2), (hm 2 2).add (hm 3 3),
    ((((hm 0 3).neg).sub (hm' 3 0)).sub (hm 1 2)).sub (hm' 2 1),
    (((hm 0 2).add (hm' 2 0)).sub (hm 1 3)).sub (hm' 3 1)]

/-- The tempered distribution of the `j`-th component of a real square-integrable field. -/
private abbrev componentDistribution {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : ∀ j, MemLp (fun z ↦ y z j) 2 volume) (j : Fin 4) : 𝓢'(ℂ, ℂ) :=
  ((ofRealCLM.compLp ((hy j).toLp _) : Lp ℂ 2 volume) : 𝓢'(ℂ, ℂ))

/-- The real Schwartz field `φ eᵢ`. -/
private abbrev singleField (i : Fin 4) (φ : 𝓢(ℂ, ℝ)) : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) :=
  φ.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i 1))

/-- **Transposition of the tempered vacuum operator.** On a real Schwartz function `φ`, the
`i`-th component of `L₀` applied to the tempered field of a real `L²` field `y` is the integral of
`⟪y, L₀* (φ eᵢ)⟫`. -/
private theorem temperedVacuumOperator_componentDistribution_apply
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : ∀ j, MemLp (fun z ↦ y z j) 2 volume) (i : Fin 4)
    (φ : 𝓢(ℂ, ℝ)) :
    temperedVacuumOperator (componentDistribution hy) i (φ.postcompCLM ofRealCLM) =
      ((∫ z, ⟪y z, vacuumAdjoint (singleField i φ) z⟫ : ℝ) : ℂ) := by
  have hpair (j : Fin 4) (ψ : 𝓢(ℂ, ℝ)) :
      componentDistribution hy j (ψ.postcompCLM ofRealCLM) = ((∫ z, ψ z * y z j : ℝ) : ℂ) := by
    rw [Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM,
      integral_congr_ae ((hy j).coeFn_toLp.mono fun z hz ↦ by rw [hz])]
  have hderiv (j : Fin 4) (v : ℂ) :
      (∂_{v} (componentDistribution hy j)) (φ.postcompCLM ofRealCLM) =
        -((∫ z, ∂_{v} φ z * y z j : ℝ) : ℂ) := by
    rw [lineDerivOp_apply_apply, TauCeti.lineDerivOp_postcompCLM, map_neg, hpair]
  -- Expand the `L²` pairing with the Schwartz field `L₀* (φ eᵢ)` into its components.
  have hint (j : Fin 4) : Integrable (fun z ↦ vacuumAdjoint (singleField i φ) z j * y z j) volume :=
    ((EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp'
      ((vacuumAdjoint (singleField i φ)).memLp 2)).integrable_mul (hy j)
  rw [integral_congr_ae (g := fun z ↦ ∑ j, vacuumAdjoint (singleField i φ) z j * y z j)
      (.of_forall fun z ↦ by simp [PiLp.inner_apply, mul_comm]),
    integral_finsetSum _ fun j _ ↦ hint j]
  fin_cases i <;>
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      temperedVacuumOperator_apply_zero, temperedVacuumOperator_apply_one,
      temperedVacuumOperator_apply_two, temperedVacuumOperator_apply_three]
    simp [hderiv, hpair, Fin.sum_univ_four, div_mul_eq_mul_div, integral_div, integral_neg]
    ring

/-- **The weak equation as a tempered equation for `L₀`.** If `y ∈ L²` is a weak solution of
`L_x y = f` at an essentially bounded field `x`, then the tempered vacuum operator sends the
components of `y` to those of `g = f - (Z(x) - Z(x₀)) y`. -/
private theorem temperedVacuumOperator_componentDistribution_eq
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : MemLp x ⊤ volume) (hy : MemLp y 2 volume)
    (hf : MemLp f 2 volume)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫)
    (hyc : ∀ j, MemLp (fun z ↦ y z j) 2 volume) (hvac : MemLp vacuumField ⊤ volume) (i : Fin 4)
    (hg : MemLp (fun z ↦
      f z i - (zerothOrder (x z) (y z) - zerothOrder (vacuumField z) (y z)) i) 2 volume) :
    temperedVacuumOperator (componentDistribution hyc) i =
      ((ofRealCLM.compLp (hg.toLp _) : Lp ℂ 2 volume) : 𝓢'(ℂ, ℂ)) := by
  -- The zeroth-order coupling `c = (Z(x) - Z(x₀)) y` is square integrable.
  have hc : MemLp
      (fun z ↦ (zerothOrder (x z) (y z) - zerothOrder (vacuumField z) (y z)) i) 2 volume :=
    ((memLp_zerothOrder hx hy i).sub (memLp_zerothOrder hvac hy i)).ae_eq
      (.of_forall fun z ↦ by simp)
  have hfc : MemLp (fun z ↦ f z i) 2 volume := (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hf
  refine ext_real fun φ hφ ↦ ?_
  have hrhs : ((ofRealCLM.compLp (hg.toLp _) : Lp ℂ 2 volume) : 𝓢'(ℂ, ℂ))
      (φ.postcompCLM ofRealCLM) = ((∫ z, φ z *
        (f z i - (zerothOrder (x z) (y z) - zerothOrder (vacuumField z) (y z)) i) : ℝ) : ℂ) := by
    rw [Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM]
    exact congrArg _ (integral_congr_ae (hg.coeFn_toLp.mono fun z hz ↦ by simp only [hz]))
  rw [temperedVacuumOperator_componentDistribution_apply, hrhs]
  congr 1
  have hη : ⇑(singleField i φ) = fun z ↦ φ z • EuclideanSpace.single i (1 : ℝ) := by
    ext z : 1
    simp [singleField]
  have hinner (v : EuclideanSpace ℝ (Fin 4)) (z : ℂ) : ⟪v, singleField i φ z⟫ = v i * φ z := by
    simp [PiLp.inner_apply, mul_comm]
  -- The weak equation tested against `φ eᵢ`, split into its vacuum and zeroth-order parts.
  have h := hweak (singleField i φ) ((singleField i φ).smooth ⊤) (hη ▸ hφ.smul_right)
  simp only [inner_gaugeFixedAdjoint_eq x, gaugeFixedAdjoint_vacuumField, hinner] at h
  rw [integral_add (g := fun z ↦
      (zerothOrder (x z) (y z) - zerothOrder (vacuumField z) (y z)) i * φ z)
    (hy.integrable_inner ((vacuumAdjoint (singleField i φ)).memLp 2))
    (hc.integrable_mul (φ.memLp 2))] at h
  rw [eq_sub_of_add_eq h, ← integral_sub (f := fun z ↦ f z i * φ z) (g := fun z ↦
      (zerothOrder (x z) (y z) - zerothOrder (vacuumField z) (y z)) i * φ z)
    (hfc.integrable_mul (φ.memLp 2)) (hc.integrable_mul (φ.memLp 2))]
  refine integral_congr_ae (.of_forall fun z ↦ ?_)
  ring

/-- **Weak solutions of the gauge-fixed vortex operator lie in `H¹`.** Let `x` be an essentially
bounded field, and let `y ∈ L²(ℂ; ℝ⁴)` be a weak solution of `L_x y = f` with `f ∈ L²(ℂ; ℝ⁴)`:
`∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every compactly supported smooth field `η`. Then `y` lies in the
Sobolev space `H¹(ℂ; ℝ⁴)`. -/
theorem mem_sobolevFields_one_of_forall_integral_inner_gaugeFixedAdjoint_eq
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : MemLp x ⊤ volume) (hy : MemLp y 2 volume)
    (hf : MemLp f 2 volume)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    y ∈ sobolevFields 1 := by
  have hyc (j : Fin 4) : MemLp (fun z ↦ y z j) 2 volume :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp' hy
  have hvac : MemLp vacuumField ⊤ volume := by
    rw [show vacuumField = fun _ ↦ !₂[0, 0, 1 / 2, 0] from funext vacuumField_apply]
    exact memLp_top_const _
  -- The right-hand side `g = f - (Z(x) - Z(x₀)) y` of `L₀ y = g` is square integrable.
  have hg (i : Fin 4) : MemLp (fun z ↦
      f z i - (zerothOrder (x z) (y z) - zerothOrder (vacuumField z) (y z)) i) 2 volume :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hf).sub
      (((memLp_zerothOrder hx hy i).sub (memLp_zerothOrder hvac hy i)).ae_eq
        (.of_forall fun z ↦ by simp))
  -- Since `L₀ : H¹ → L²` is a bijection, the components of `y` lie in `H¹`.
  have hY := memSobolev_temperedVacuumOperator_iff (s := 1).1 fun i ↦ by
    rw [sub_self, temperedVacuumOperator_componentDistribution_eq hx hy hf hweak hyc hvac i (hg i)]
    exact memSobolev_zero_iff.2 ⟨_, rfl⟩
  exact mem_sobolevFields.2 fun i ↦
    mem_realSobolevFunctions.2 ⟨(hyc i).toLp _, (hyc i).coeFn_toLp, hY i⟩

/-- **At a bounded plane vortex, every `L²` field is weakly the image of an `H¹` field under
`L_x`.** Let `x` be an essentially bounded `C¹` solution of the plane vortex equation with
`|α| → 1` at infinity. For every `f ∈ L²(ℂ; ℝ⁴)` there is `y ∈ H¹(ℂ; ℝ⁴)` with `L_x y = f` weakly:
`∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every compactly supported `C²` field `η`. -/
theorem exists_mem_sobolevFields_one_forall_integral_inner_gaugeFixedAdjoint_eq
    {x f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ 1 x) (hxb : MemLp x ⊤ volume)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hf : MemLp f 2 volume) :
    ∃ y ∈ sobolevFields 1, ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η →
      HasCompactSupport η → ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫ := by
  obtain ⟨Q, hQ, -⟩ :=
    exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq (μ := volume) hx hsol hlim
  have hQf (η : ℂ → EuclideanSpace ℝ (Fin 4)) (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
      ∫ z, ⟪Q (hf.toLp f) z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫ := by
    rw [hQ _ η hη hηc]
    exact integral_congr_ae (hf.coeFn_toLp.mono fun z hz ↦ by simp only [hz])
  exact ⟨_, mem_sobolevFields_one_of_forall_integral_inner_gaugeFixedAdjoint_eq hxb (Lp.memLp _)
    hf fun η hη hηc ↦ hQf η (hη.of_le (by norm_cast)) hηc, hQf⟩

end TauCeti.Vortex
