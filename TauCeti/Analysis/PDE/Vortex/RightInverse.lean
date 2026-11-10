/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Analysis.PDE.Vortex.SpectralGap
public import TauCeti.Analysis.InnerProductSpace.WeakSolution
public import TauCeti.MeasureTheory.Function.L2Space

/-!
# The weak right inverse of the gauge-fixed operator at a plane vortex

At a field `x`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) is a
first-order operator on fields `ℂ → ℝ⁴`, with formal adjoint `L_x*` (`gaugeFixedAdjoint`). A
square-integrable field `y` is a *weak solution* of `L_x y = f`, for `f ∈ L²(ℂ; ℝ⁴)`, if

`∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫`

for every compactly supported `C²` test field `η`. This extends the classical notion: by the
integration-by-parts identity `integral_inner_gaugeFixedOperator`, when `x` is continuous a
compactly supported `C¹` field `y` is a weak solution of `L_x y = f` for `f` its classical image
under `L_x`. The *weak kernel* of `L_x` consists of the weak solutions of `L_x y = 0`.

This file shows that the weak cokernel of `L_x` vanishes at a plane vortex, with a bounded right
inverse. If `L_x*` is bounded below on test fields, `c ∫ |η|² ≤ ∫ |L_x* η|²` with `c > 0`, there
is a bounded operator `Q` on `L²(ℂ; ℝ⁴)` of norm at most `c^(-1/2)` such that `Q f` is a weak
solution of `L_x y = f` for every `f`, and `Q f` is orthogonal to the weak kernel
(`TauCeti.Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_of_mul_le`). Thus
`Q f` is the weak solution of least norm, and `Q` is the right inverse `L_x* (L_x L_x*)⁻¹` on the
`L²`-orthogonal complement of the weak kernel. At an actual vortex with `|α| → 1`, the spectral
gap `exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint` supplies the lower
bound (`TauCeti.Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`).

These are statements about weak solutions in `L²`. That `Q f` lies in `H¹`, and the Fredholm
property and dimension of the kernel of the Sobolev realization of `L_x`, are not proved here.

## Main results

* `TauCeti.Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_of_mul_le`: a
  lower bound on `L_x*` gives a bounded weak right inverse of `L_x` orthogonal to its weak kernel.
* `TauCeti.Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`: the weak
  right inverse at a plane vortex with `|α| → 1`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

namespace TauCeti.Vortex

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure] {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- The compactly supported `C²` test fields. -/
private abbrev TestField := TestFunction (⊤ : TopologicalSpace.Opens ℂ) (EuclideanSpace ℝ (Fin 4)) 2

private theorem memLp_gaugeFixedAdjoint (hx : Continuous x) (η : TestField) :
    MemLp (gaugeFixedAdjoint x η) 2 μ :=
  (continuous_gaugeFixedAdjoint hx (η.contDiff.of_le (by norm_cast))).memLp_of_hasCompactSupport
    (hasCompactSupport_gaugeFixedAdjoint η.hasCompactSupport)

/-- The inclusion of the test fields into `L²`. -/
private noncomputable def testFieldToLp (μ : Measure ℂ) [μ.IsAddHaarMeasure] :
    TestField →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ where
  toFun η := (η.continuous.memLp_of_hasCompactSupport η.hasCompactSupport).toLp η
  map_add' η ν := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (.of_eq (FunLike.coe_add η ν))
  map_smul' t η := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (.of_eq (FunLike.coe_smul t η))

/-- The formal adjoint `L_x*` on test fields, with values in `L²`. -/
private noncomputable def gaugeFixedAdjointToLp (μ : Measure ℂ) [μ.IsAddHaarMeasure]
    (hx : Continuous x) : TestField →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ where
  toFun η := (memLp_gaugeFixedAdjoint hx η).toLp (gaugeFixedAdjoint x η)
  map_add' η ν := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun z ↦ ?_)
    rw [FunLike.coe_add, Pi.add_apply]
    exact gaugeFixedAdjoint_add x (η.contDiff.differentiable (by norm_num) z)
      (ν.contDiff.differentiable (by norm_num) z)
  map_smul' t η := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun z ↦ ?_)
    rw [FunLike.coe_smul, Pi.smul_apply]
    exact gaugeFixedAdjoint_smul x η t z

/-- **Weak right inverse from a lower bound on the formal adjoint.** Let `x` be a continuous
field and suppose that `c ∫ |η|² ≤ ∫ |L_x* η|²` for every compactly supported `C²` field `η`,
with `c > 0`. Then there is a bounded operator `Q` on `L²(ℂ; ℝ⁴)` with `‖Q‖ ≤ c^(-1/2)` such
that

* `Q f` is a weak solution of `L_x y = f`: `∫ ⟪Q f, L_x* η⟫ = ∫ ⟪f, η⟫` for every compactly
  supported `C²` field `η`;
* `Q f` is orthogonal to the weak kernel: `∫ ⟪Q f, u⟫ = 0` for every `u ∈ L²` with
  `∫ ⟪u, L_x* η⟫ = 0` for all such `η`. -/
theorem exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_of_mul_le
    (hx : Continuous x) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      ‖Q‖ ≤ (√c)⁻¹ ∧
      (∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪Q f z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ) ∧
      ∀ f u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
        ∫ z, ⟪Q f z, u z⟫ ∂μ = 0 := by
  set S := gaugeFixedAdjointToLp μ hx
  set ι := testFieldToLp μ
  have hS (u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) (η : TestField) :
      ⟪u, S η⟫ = ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ :=
    L2.inner_toLp u (memLp_gaugeFixedAdjoint hx η)
  have hι (u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) (η : TestField) :
      ⟪u, ι η⟫ = ∫ z, ⟪u z, η z⟫ ∂μ :=
    L2.inner_toLp u (η.continuous.memLp_of_hasCompactSupport η.hasCompactSupport)
  have hnorm {g : ℂ → EuclideanSpace ℝ (Fin 4)} (hg : MemLp g 2 μ) :
      ‖hg.toLp g‖ ^ 2 = ∫ z, ‖g z‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_toLp]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp] with z hz
    rw [hz, real_inner_self_eq_norm_sq]
  -- The gap is the lower bound `√c ‖η‖ ≤ ‖L_x* η‖` in `L²`.
  have hbound (η : TestField) : √c * ‖ι η‖ ≤ ‖S η‖ := by
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    have hιη : ι η = (η.continuous.memLp_of_hasCompactSupport η.hasCompactSupport).toLp η := rfl
    have hSη : S η = (memLp_gaugeFixedAdjoint hx η).toLp (gaugeFixedAdjoint x η) := rfl
    rw [mul_pow, Real.sq_sqrt hc.le, hιη, hSη, hnorm, hnorm]
    exact hgap η η.contDiff η.hasCompactSupport
  obtain ⟨Q, hQn, hQK, hQ⟩ := LinearMap.exists_continuousLinearMap_inner_apply_eq_of_mul_norm_le
    S ι (Real.sqrt_pos.2 hc) hbound
  refine ⟨Q, hQn, fun f η hη hηc ↦ ?_, fun f u hu ↦ ?_⟩
  · have h := hQ f ⟨η, hη, hηc, by simp⟩
    rwa [hS, hι] at h
  · -- `u` lies in the weak kernel `(range S)ᗮ`, and `Q f` in its orthogonal complement.
    have huK : u ∈ (LinearMap.range S)ᗮ := by
      rw [Submodule.mem_orthogonal]
      rintro _ ⟨η, rfl⟩
      rw [real_inner_comm, hS]
      exact hu η η.contDiff η.hasCompactSupport
    rw [← L2.inner_def]
    exact Submodule.inner_left_of_mem_orthogonal huK (hQK f)

/-- **Weak right inverse at a plane vortex.** Let `x` be a `C¹` solution of the plane vortex
equation with `|α| → 1` at infinity. Then there is a bounded operator `Q` on `L²(ℂ; ℝ⁴)` such
that `Q f` is a weak solution of `L_x y = f` for every `f ∈ L²`, orthogonal to the weak kernel of
`L_x`. In particular the weak cokernel of `L_x` vanishes. -/
theorem exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪Q f z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ) ∧
      ∀ f u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
        ∫ z, ⟪Q f z, u z⟫ ∂μ = 0 := by
  obtain ⟨c, hc, hgap⟩ :=
    exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := μ) hx hsol hlim
  obtain ⟨Q, -, hQ⟩ :=
    exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_of_mul_le hx.continuous hc hgap
  exact ⟨Q, hQ⟩

end TauCeti.Vortex
