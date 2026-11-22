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
import TauCeti.Analysis.Distribution.TestFunction.Lp
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.PDE.Vortex.WeightedEstimate
import TauCeti.MeasureTheory.Integral.MeanInequalities
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.Adjoint
import TauCeti.MeasureTheory.Integral.Lebesgue.Truncation

/-!
# The weak right inverse of the gauge-fixed operator at a plane vortex

At a field `x`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) is a
first-order operator on fields `ℂ → ℝ⁴`, with formal adjoint `L_x*` (`gaugeFixedAdjoint`). A
square-integrable field `y` is a *weak solution* of `L_x y = f`, for `f ∈ L²(ℂ; ℝ⁴)`, if

`∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫`

for every compactly supported `C²` test field `η` (`TauCeti.Vortex.IsGaugeFixedWeakSolution`).
This extends the classical notion: by the integration-by-parts identity
`integral_inner_gaugeFixedOperator`, when `x` is continuous a compactly supported `C¹` field `y`
is a weak solution of `L_x y = f` for `f` its classical image under `L_x`. The *weak kernel* of
`L_x` consists of the weak solutions of `L_x y = 0`, and a weak solution of `L_x y = f` is
*minimal* if it is orthogonal to the weak kernel
(`TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution`). At a continuous field the minimal weak
solution is unique (`TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution.unique`) and has least norm
among all weak solutions (`TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution.norm_le`).

This file shows that the weak cokernel of `L_x` vanishes at a plane vortex, with a bounded right
inverse. If `L_x*` is bounded below on test fields, `c ∫ |η|² ≤ ∫ |L_x* η|²` with `c > 0`, there
is a bounded operator `Q` on `L²(ℂ; ℝ⁴)` of norm at most `c^(-1/2)` such that `Q f` is a minimal
weak solution of `L_x y = f` for every `f`
(`TauCeti.Vortex.exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution_of_mul_le`). Thus
`Q f` is the weak solution of least norm, `Q` is uniquely determined, and `Q` is the right
inverse `L_x* (L_x L_x*)⁻¹` on the `L²`-orthogonal complement of the weak kernel. At an actual
vortex with `|α| → 1`, the spectral gap
`exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint` supplies the lower bound
(`TauCeti.Vortex.exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution`). The uniform gap
`exists_pos_forall_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint` over the smooth
vortices of a given degree `m` gives the same for the bound on `Q`: one constant, depending only
on `m`, bounds the norm of `Q` over the whole moduli space `Sym^m ℂ`
(`exists_forall_exists_continuousLinearMap_norm_le_isMinimalGaugeFixedWeakSolution`).

At such a vortex `Q` also respects exponential decay. With `ρ = √(1 + |z|²)` and `|c| < 1/2`,
every weak solution `y` of `L_x y = f` orthogonal to the weak kernel, in particular `y = Q f`,
satisfies `‖exp(c ρ) y‖₂ ≤ K ‖exp(c ρ) f‖₂` with `K` depending only on the vortex and `c`
(`TauCeti.Vortex.exists_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq`). The
weighted coercivity of `L_x L_x*` in `TauCeti.Analysis.PDE.Vortex.WeightedEstimate` gives this for
test fields; here it is transferred to `y`, which is an `L²` limit of values `L_x* η` because it
is orthogonal to the weak kernel. The transfer uses the bounded weights `W / (1 + ε W)`, for which
every weighted quantity of `y` and `f` is finite, and lets `ε → 0` by Fatou's lemma.

The Hilbert space adjoint `Q†` of such a `Q` is the left inverse of `L_x*` vanishing on the weak
kernel: it sends `L_x* η` to `η` for every test field `η`
(`TauCeti.Vortex.adjoint_apply_ae_eq_of_ae_eq_gaugeFixedAdjoint`) and vanishes on the weak kernel
(`TauCeti.Vortex.adjoint_apply_eq_zero_of_integral_inner_gaugeFixedAdjoint_eq_zero`); formally it
is `(L_x L_x*)⁻¹ L_x`. It satisfies the same weighted estimate,
`‖exp(c ρ) Q† g‖₂ ≤ K ‖exp(c ρ) g‖₂` for `|c| < 1/2`
(`TauCeti.Vortex.exists_eLpNorm_exp_mul_smul_adjoint_apply_le`). This is dual to the estimate for
`Q` at the rate `-c`, by `ContinuousLinearMap.eLpNorm_smul_le_of_eLpNorm_smul_adjoint_le`.

The constant `K` depends on the vortex only through its spectral gap `c₀` and a radius `R`
beyond which its squared mass `|α|² / 4` exceeds a fixed `a` with `c² < a ≤ 1/4`
(`TauCeti.Vortex.exists_forall_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq`).
Both are uniform over the smooth vortices of degree `m` whose zeros lie in a fixed disc: the
spectral gap over all of `Sym^m ℂ`, and the radius by the localization of small moduli near the
zeros (`TauCeti.Vortex.exists_forall_lt_normSq_of_forall_mem_norm_le`). So one constant,
depending only on `m`, the radius of the disc and `c`, serves for `Q` and for `Q†` over every
compact window of divisors, collisions of zeros included
(`TauCeti.Vortex.exists_forall_eLpNorm_exp_mul_smul_le_of_forall_mem_norm_le`,
`TauCeti.Vortex.exists_forall_eLpNorm_exp_mul_smul_adjoint_apply_le_of_forall_mem_norm_le`).

These are statements about weak solutions in `L²`. At a bounded field, weak solutions lie in `H¹`
by the elliptic regularity of `TauCeti.Analysis.PDE.Vortex.EllipticRegularity`, so `Q f ∈ H¹`
there. The Fredholm property and the dimension of the kernel of the Sobolev realization of `L_x`
are not proved here.

## Main definitions

* `TauCeti.Vortex.IsGaugeFixedWeakSolution μ x f y`: `y` is a weak solution of `L_x y = f`.
* `TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution μ x f y`: `y` is a weak solution of
  `L_x y = f` orthogonal to the weak solutions of `L_x w = 0`.

## Main results

* `TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution.unique`,
  `TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution.norm_le`: the minimal weak solution is unique
  and has least norm.
* `TauCeti.Vortex.exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution_of_mul_le`: a
  lower bound on `L_x*` gives a bounded weak right inverse of `L_x` orthogonal to its weak kernel.
* `TauCeti.Vortex.exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution`: the weak
  right inverse at a plane vortex with `|α| → 1`.
* `exists_forall_exists_continuousLinearMap_norm_le_isMinimalGaugeFixedWeakSolution`: a bound on
  its norm uniform over the smooth vortices of degree `m`.
* `TauCeti.Vortex.exists_forall_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq`:
  the exponentially weighted `L²` estimate for the weak right inverse, with a constant depending
  only on a spectral gap and an exterior mass.
* `TauCeti.Vortex.exists_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq`: the
  exponentially weighted `L²` estimate for the weak right inverse at such a vortex.
* `TauCeti.Vortex.adjoint_apply_ae_eq_of_ae_eq_gaugeFixedAdjoint`,
  `TauCeti.Vortex.adjoint_apply_eq_zero_of_integral_inner_gaugeFixedAdjoint_eq_zero`: the adjoint
  of the weak right inverse is the left inverse of `L_x*` vanishing on the weak kernel.
* `TauCeti.Vortex.exists_eLpNorm_exp_mul_smul_adjoint_apply_le`: the exponentially weighted `L²`
  estimate for the adjoint.
* `TauCeti.Vortex.exists_forall_eLpNorm_exp_mul_smul_le_of_forall_mem_norm_le`,
  `TauCeti.Vortex.exists_forall_eLpNorm_exp_mul_smul_adjoint_apply_le_of_forall_mem_norm_le`: both
  weighted estimates with one constant over the vortices of degree `m` whose zeros lie in a fixed
  disc.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

namespace TauCeti.Vortex

open MeasureTheory Filter
open scoped ContDiff RealInnerProductSpace Topology NNReal ENNReal

/-! ### Weak solutions -/

section WeakSolution

variable {μ : Measure ℂ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- `y` is a **weak solution** of `L_x y = f`: `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every compactly
supported `C²` test field `η`. -/
def IsGaugeFixedWeakSolution (μ : Measure ℂ) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) : Prop :=
  ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
    ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ

/-- `y` is a **minimal weak solution** of `L_x y = f`: a weak solution which is orthogonal to
every square-integrable weak solution `w` of `L_x w = 0`. At a continuous field it is the weak
solution of least norm (`TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution.norm_le`), and it is
unique (`TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution.unique`). At a plane vortex with
`|α| → 1` it is the value at `f` of a bounded weak right inverse
(`TauCeti.Vortex.exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution`). -/
def IsMinimalGaugeFixedWeakSolution (μ : Measure ℂ) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) : Prop :=
  IsGaugeFixedWeakSolution μ x f y ∧
    ∀ w : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪w z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
      ∫ z, ⟪y z, w z⟫ ∂μ = 0

/-- Unfolding `TauCeti.Vortex.IsGaugeFixedWeakSolution`: `y` is a weak solution of `L_x y = f`
exactly when `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every compactly supported `C²` test field `η`. -/
theorem isGaugeFixedWeakSolution_iff {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} :
    IsGaugeFixedWeakSolution μ x f y ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ :=
  Iff.rfl

/-- A weak solution of `L_x y = f` satisfies `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every compactly
supported `C²` test field `η`. -/
theorem IsGaugeFixedWeakSolution.integral_inner_eq {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (h : IsGaugeFixedWeakSolution μ x f y) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ :=
  h η hη hηc

/-- The weak solutions of `L_x w = 0` are the fields `w` with `∫ ⟪w, L_x* η⟫ = 0` for every
compactly supported `C²` test field `η`. -/
theorem isGaugeFixedWeakSolution_zero_iff {w : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} :
    IsGaugeFixedWeakSolution μ x 0 w ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪w z, gaugeFixedAdjoint x η z⟫ ∂μ = 0 := by
  simp only [IsGaugeFixedWeakSolution, Lp.integral_inner_coeFn_zero_left]

/-- A minimal weak solution of `L_x y = f` is a weak solution orthogonal to every weak solution
of `L_x w = 0`. -/
theorem isMinimalGaugeFixedWeakSolution_iff {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} :
    IsMinimalGaugeFixedWeakSolution μ x f y ↔
      IsGaugeFixedWeakSolution μ x f y ∧
        ∀ w : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ, IsGaugeFixedWeakSolution μ x 0 w →
          ∫ z, ⟪y z, w z⟫ ∂μ = 0 := by
  simp only [IsMinimalGaugeFixedWeakSolution, isGaugeFixedWeakSolution_zero_iff]

/-- A minimal weak solution is a weak solution. -/
theorem IsMinimalGaugeFixedWeakSolution.isGaugeFixedWeakSolution
    {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} (h : IsMinimalGaugeFixedWeakSolution μ x f y) :
    IsGaugeFixedWeakSolution μ x f y :=
  h.1

/-- A minimal weak solution of `L_x y = f` is orthogonal to every weak solution of
`L_x w = 0`. -/
theorem IsMinimalGaugeFixedWeakSolution.integral_inner_eq_zero
    {f y w : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} (h : IsMinimalGaugeFixedWeakSolution μ x f y)
    (hw : IsGaugeFixedWeakSolution μ x 0 w) : ∫ z, ⟪y z, w z⟫ ∂μ = 0 :=
  (isMinimalGaugeFixedWeakSolution_iff.1 h).2 w hw

/-- At a continuous field, weak solutions can be subtracted: if `y` and `y'` are weak solutions
of `L_x y = f` and `L_x y' = f'`, then `y - y'` is a weak solution of `L_x w = f - f'`. -/
theorem IsGaugeFixedWeakSolution.sub [IsFiniteMeasureOnCompacts μ] (hx : Continuous x)
    {f f' y y' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} (h : IsGaugeFixedWeakSolution μ x f y)
    (h' : IsGaugeFixedWeakSolution μ x f' y') :
    IsGaugeFixedWeakSolution μ x (f - f') (y - y') := by
  intro η hη hηc
  -- Both pairings are `L²` inner products with the classes of compactly supported fields.
  have hm : MemLp (gaugeFixedAdjoint x η) 2 μ :=
    (continuous_gaugeFixedAdjoint hx (hη.of_le one_le_two)).memLp_of_hasCompactSupport
      (hasCompactSupport_gaugeFixedAdjoint hηc)
  have hmη : MemLp η 2 μ := hη.continuous.memLp_of_hasCompactSupport hηc
  rw [← L2.inner_toLp _ hm, ← L2.inner_toLp _ hmη, inner_sub_left, inner_sub_left,
    L2.inner_toLp, L2.inner_toLp, L2.inner_toLp, L2.inner_toLp, h η hη hηc, h' η hη hηc]

/-- At a continuous field, the difference of two weak solutions of `L_x y = f` is a weak
solution of `L_x w = 0`. -/
private theorem IsGaugeFixedWeakSolution.forall_integral_inner_sub_eq_zero
    [IsFiniteMeasureOnCompacts μ] (hx : Continuous x)
    {f y y' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} (h : IsGaugeFixedWeakSolution μ x f y)
    (h' : IsGaugeFixedWeakSolution μ x f y') :
    ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪(y' - y) z, gaugeFixedAdjoint x η z⟫ ∂μ = 0 :=
  isGaugeFixedWeakSolution_zero_iff.1 (by simpa only [sub_self] using h'.sub hx h)

/-- **The minimal weak solution has least norm.** At a continuous field, a minimal weak solution
`y` of `L_x y = f` has norm at most that of every weak solution `y'`: indeed
`‖y'‖² = ‖y‖² + ‖y' - y‖²`, since `y' - y` is a weak solution of `L_x w = 0`. -/
theorem IsMinimalGaugeFixedWeakSolution.norm_le [IsFiniteMeasureOnCompacts μ] (hx : Continuous x)
    {f y y' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} (h : IsMinimalGaugeFixedWeakSolution μ x f y)
    (h' : IsGaugeFixedWeakSolution μ x f y') : ‖y‖ ≤ ‖y'‖ := by
  have horth : ⟪y, y' - y⟫ = 0 := by
    rw [L2.inner_def]
    exact h.2 _ (h.1.forall_integral_inner_sub_eq_zero hx h')
  have hsq : ‖y'‖ ^ 2 = ‖y‖ ^ 2 + ‖y' - y‖ ^ 2 := by
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℝ) y (y' - y) horth
    rw [add_sub_cancel] at this
    rw [sq, sq, sq, this]
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [hsq]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- **The minimal weak solution is unique.** At a continuous field, two minimal weak solutions of
`L_x y = f` coincide. -/
theorem IsMinimalGaugeFixedWeakSolution.unique [IsFiniteMeasureOnCompacts μ] (hx : Continuous x)
    {f y y' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} (h : IsMinimalGaugeFixedWeakSolution μ x f y)
    (h' : IsMinimalGaugeFixedWeakSolution μ x f y') : y = y' := by
  have hw := h.1.forall_integral_inner_sub_eq_zero hx h'.1
  have h₁ : ⟪y, y' - y⟫ = 0 := by
    rw [L2.inner_def]
    exact h.2 _ hw
  have h₂ : ⟪y', y' - y⟫ = 0 := by
    rw [L2.inner_def]
    exact h'.2 _ hw
  have : ‖y' - y‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, h₁, h₂, sub_self]
  exact (sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this))).symm

end WeakSolution

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure] {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- The compactly supported `C²` test fields. -/
private abbrev TestField := TestFunction (⊤ : TopologicalSpace.Opens ℂ) (EuclideanSpace ℝ (Fin 4)) 2

/-- The formal adjoint `L_x*` on test fields, with values in `L²`. -/
private noncomputable def gaugeFixedAdjointToLp (μ : Measure ℂ) [μ.IsAddHaarMeasure]
    (hx : Continuous x) : TestField →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ where
  toFun η := (memLp_gaugeFixedAdjoint hx (η.contDiff.of_le (by norm_cast))
    η.hasCompactSupport).toLp (gaugeFixedAdjoint x η)
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

private theorem gaugeFixedAdjointToLp_apply (hx : Continuous x) (η : TestField) :
    gaugeFixedAdjointToLp μ hx η = (memLp_gaugeFixedAdjoint hx (η.contDiff.of_le (by norm_cast))
      η.hasCompactSupport).toLp (gaugeFixedAdjoint x η) :=
  rfl

private theorem inner_gaugeFixedAdjointToLp (hx : Continuous x)
    (u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) (η : TestField) :
    ⟪u, gaugeFixedAdjointToLp μ hx η⟫ = ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ := by
  rw [gaugeFixedAdjointToLp_apply]
  exact L2.inner_toLp u _

/-- **Weak right inverse from a lower bound on the formal adjoint.** Let `x` be a continuous
field and suppose that `c ∫ |η|² ≤ ∫ |L_x* η|²` for every compactly supported `C²` field `η`,
with `c > 0`. Then there is a bounded operator `Q` on `L²(ℂ; ℝ⁴)` with `‖Q‖ ≤ c^(-1/2)` such
that `Q f` is a minimal weak solution of `L_x y = f` for every `f`:

* `Q f` is a weak solution of `L_x y = f`: `∫ ⟪Q f, L_x* η⟫ = ∫ ⟪f, η⟫` for every compactly
  supported `C²` field `η`;
* `Q f` is orthogonal to the weak kernel: `∫ ⟪Q f, u⟫ = 0` for every `u ∈ L²` with
  `∫ ⟪u, L_x* η⟫ = 0` for all such `η`. -/
theorem exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution_of_mul_le
    (hx : Continuous x) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      ‖Q‖ ≤ (√c)⁻¹ ∧ ∀ f, IsMinimalGaugeFixedWeakSolution μ x f (Q f) := by
  set S := gaugeFixedAdjointToLp μ hx
  set ι := (TestFunction.ambientToLp 2 μ : TestField →L[ℝ] _).toLinearMap
  have hS := inner_gaugeFixedAdjointToLp (μ := μ) hx
  have hι (u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) (η : TestField) :
      ⟪u, ι η⟫ = ∫ z, ⟪u z, η z⟫ ∂μ :=
    TestFunction.inner_ambientToLp u η
  -- The gap is the lower bound `√c ‖η‖ ≤ ‖L_x* η‖` in `L²`.
  have hbound (η : TestField) : √c * ‖ι η‖ ≤ ‖S η‖ := by
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [mul_pow, Real.sq_sqrt hc.le, ContinuousLinearMap.coe_coe, TestFunction.norm_ambientToLp_sq,
      gaugeFixedAdjointToLp_apply, MemLp.norm_toLp_sq]
    exact hgap η η.contDiff η.hasCompactSupport
  obtain ⟨Q, hQn, hQK, hQ⟩ := LinearMap.exists_continuousLinearMap_inner_apply_eq_of_mul_norm_le
    S ι (Real.sqrt_pos.2 hc) hbound
  refine ⟨Q, hQn, fun f ↦ ⟨fun η hη hηc ↦ ?_, fun u hu ↦ ?_⟩⟩
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
that `Q f` is a minimal weak solution of `L_x y = f` for every `f ∈ L²`: a weak solution
orthogonal to the weak kernel of `L_x`. In particular the weak cokernel of `L_x` vanishes. By
`TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution.unique`, `Q` is the only such map. -/
theorem exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      ∀ f, IsMinimalGaugeFixedWeakSolution μ x f (Q f) := by
  obtain ⟨c, hc, hgap⟩ :=
    exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := μ) hx hsol hlim
  obtain ⟨Q, -, hQ⟩ :=
    exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution_of_mul_le hx.continuous hc hgap
  exact ⟨Q, hQ⟩

/-- **Uniform weak right inverse over all vortices of degree `m`.** There is `K`, depending only
on `m`, such that at every smooth plane vortex `x` with the degree-`m` end framing there is a
bounded operator `Q` on `L²(ℂ; ℝ⁴)` of norm at most `K` such that `Q f` is a minimal weak
solution of `L_x y = f` for every `f ∈ L²`: a weak solution orthogonal to the weak kernel of
`L_x`. The bound is uniform over the whole noncompact moduli space `Sym^m ℂ`. -/
theorem exists_forall_exists_continuousLinearMap_norm_le_isMinimalGaugeFixedWeakSolution
    (m : ℕ) :
    ∃ K, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) →
      ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        ‖Q‖ ≤ K ∧ ∀ f, IsMinimalGaugeFixedWeakSolution μ x f (Q f) := by
  obtain ⟨c, hc, hgap⟩ :=
    exists_pos_forall_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := μ) m
  exact ⟨(√c)⁻¹, fun x D hx hsol hframe hD ↦
    exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution_of_mul_le hx.continuous hc
      (hgap x D hx hsol hframe hD)⟩

/-! ### The exponentially weighted estimate -/

/-- A square-integrable field orthogonal to the weak kernel of `L_x` is an `L²` limit of values
`L_x* η` on test fields. -/
private theorem exists_integral_norm_sub_gaugeFixedAdjoint_sq_lt (hx : Continuous x)
    {y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hy : ∀ u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
      ∫ z, ⟪y z, u z⟫ ∂μ = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η ∧ HasCompactSupport η ∧
      ∫ z, ‖y z - gaugeFixedAdjoint x η z‖ ^ 2 ∂μ < ε := by
  set S := gaugeFixedAdjointToLp μ hx
  have hS := inner_gaugeFixedAdjointToLp (μ := μ) hx
  have hmem : y ∈ (LinearMap.range S)ᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    have hu' (η : ℂ → EuclideanSpace ℝ (Fin 4)) (hη : ContDiff ℝ 2 η)
        (hηc : HasCompactSupport η) : ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0 := by
      have h := hS u ⟨η, hη, hηc, by simp⟩
      rw [TestFunction.coe_mk] at h
      rw [← h]
      exact Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self S _) hu
    rw [L2.inner_def, ← hy u hu']
    exact integral_congr_ae (ae_of_all _ fun z ↦ real_inner_comm _ _)
  rw [Submodule.orthogonal_orthogonal_eq_closure, ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hmem
  obtain ⟨_, ⟨η, rfl⟩, hd⟩ := hmem (√ε) (Real.sqrt_pos.2 hε)
  refine ⟨η, η.contDiff, η.hasCompactSupport, ?_⟩
  have hn : ∫ z, ‖y z - gaugeFixedAdjoint x η z‖ ^ 2 ∂μ = ‖y - S η‖ ^ 2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub y (S η),
      (memLp_gaugeFixedAdjoint (μ := μ) hx (η.contDiff.of_le (by norm_cast))
        η.hasCompactSupport).coeFn_toLp] with z h₁ h₂
    rw [h₁, Pi.sub_apply, gaugeFixedAdjointToLp_apply, h₂]
  rw [hn]
  rw [dist_eq_norm] at hd
  exact (Real.lt_sqrt (norm_nonneg _)).1 hd

/-- If `y` is a weak solution of `L_x y = f`, the weighted pairing `∫ V² ⟪L_x L_x* η, η⟫` is the
pairing of `L_x* η - y` with `L_x* (V² η)` plus the weighted pairing of `f` with `η`. -/
private theorem integral_sq_mul_inner_gaugeFixedOperator_eq_add
    (hx : ContDiff ℝ 1 x) {y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y 2 μ)
    (hweak : ∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ)
    {V : ℂ → ℝ} (hV : ContDiff ℝ 2 V) {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ 2 η)
    (hηc : HasCompactSupport η) :
    ∫ z, V z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ =
      ∫ z, ⟪gaugeFixedAdjoint x η z - y z,
        gaugeFixedAdjoint x (fun t ↦ V t ^ 2 • η t) z⟫ ∂μ +
      ∫ z, V z ^ 2 * ⟪f z, η z⟫ ∂μ := by
  set H := gaugeFixedAdjoint x (fun t ↦ V t ^ 2 • η t)
  have hVη : ContDiff ℝ 2 (fun t ↦ V t ^ 2 • η t) := (hV.pow 2).smul hη
  have hVηc : HasCompactSupport (fun t ↦ V t ^ 2 • η t) := hηc.smul_left (f := fun t ↦ V t ^ 2)
  have hA := contDiff_gaugeFixedAdjoint hx hη
  have hAc := hasCompactSupport_gaugeFixedAdjoint (x := x) hηc
  have hH : MemLp H 2 μ := memLp_gaugeFixedAdjoint hx.continuous (hVη.of_le (by norm_num)) hVηc
  have hG : MemLp (gaugeFixedAdjoint x η) 2 μ :=
    memLp_gaugeFixedAdjoint hx.continuous (hη.of_le (by norm_num)) hηc
  have hi₁ : Integrable (fun z ↦ ⟪gaugeFixedAdjoint x η z - y z, H z⟫) μ :=
    (hG.sub hy).integrable_inner hH
  have hi₂ : Integrable (fun z ↦ ⟪y z, H z⟫) μ := hy.integrable_inner hH
  -- Integration by parts: `∫ V² ⟪L_x L_x* η, η⟫ = ∫ ⟪L_x* η, L_x* (V² η)⟫`.
  have h₁ : ∫ z, V z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ =
      ∫ z, ⟪gaugeFixedAdjoint x η z, H z⟫ ∂μ := by
    rw [← integral_inner_gaugeFixedOperator hA (hVη.of_le (by norm_num)) (.inl hAc)]
    simp only [real_inner_smul_right]
  have h₂ := hweak _ hVη hVηc
  simp only [real_inner_smul_right] at h₂
  rw [h₁, ← h₂, ← integral_add hi₁ hi₂]
  simp only [inner_sub_left, sub_add_cancel]

/-- For a weight `V` bounded by `B` with logarithmic gradient at most `|c|`,
`∫ |L_x* (V² η)|² ≤ 2 B⁴ ∫ |L_x* η|² + 8 c² B⁴ ∫ |η|²`. -/
private theorem integral_norm_sq_gaugeFixedAdjoint_sq_smul_le
    (hx : ContDiff ℝ 1 x) {V : ℂ → ℝ} (hV : ContDiff ℝ 2 V) {B c : ℝ} (hVB : ∀ z, V z ^ 2 ≤ B ^ 2)
    (hdV : ∀ z, ‖fderiv ℝ V z‖ ^ 2 ≤ c ^ 2 * V z ^ 2) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    ∫ z, ‖gaugeFixedAdjoint x (fun t ↦ V t ^ 2 • η t) z‖ ^ 2 ∂μ ≤
      2 * B ^ 4 * (∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ) +
        8 * c ^ 2 * B ^ 4 * ∫ z, ‖η z‖ ^ 2 ∂μ := by
  have hVη : ContDiff ℝ 2 (fun t ↦ V t ^ 2 • η t) := (hV.pow 2).smul hη
  have hVηc : HasCompactSupport (fun t ↦ V t ^ 2 • η t) := hηc.smul_left (f := fun t ↦ V t ^ 2)
  have hA := contDiff_gaugeFixedAdjoint hx hη
  have hAc := hasCompactSupport_gaugeFixedAdjoint (x := x) hηc
  have hi {g : ℂ → EuclideanSpace ℝ (Fin 4)} (hg : Continuous g) (hgc : HasCompactSupport g) :
      Integrable (fun z ↦ ‖g z‖ ^ 2) μ :=
    (hg.norm.pow 2).integrable_of_hasCompactSupport (hgc.mono fun z hz hzero ↦ hz (by simp [hzero]))
  have iH := hi (continuous_gaugeFixedAdjoint hx.continuous (hVη.of_le (by norm_num)))
    (hasCompactSupport_gaugeFixedAdjoint (x := x) hVηc)
  have iG := hi hA.continuous hAc
  have iη := hi hη.continuous hηc
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iG.const_mul _) (iη.const_mul _)]
  refine integral_mono iH ((iG.const_mul _).add (iη.const_mul _)) fun z ↦ ?_
  have hVz : DifferentiableAt ℝ V z := hV.differentiable (by simp) z
  have hl := gaugeFixedAdjoint_fun_smul (w := fun t ↦ V t ^ 2) x (hVz.pow 2)
    (hη.differentiable (by simp) z)
  have hp : fderiv ℝ (fun t ↦ V t ^ 2) z = (2 * V z) • fderiv ℝ V z := by
    simpa using (hVz.hasFDerivAt.pow 2).fderiv
  have hs := norm_sq_gaugeFixedAdjointSymbol (fderiv ℝ (fun t ↦ V t ^ 2) z) (η z)
  rw [hp, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hs
  rw [hl, hp]
  set σ := gaugeFixedAdjointSymbol ((2 * V z) • fderiv ℝ V z) (η z)
  have ht := norm_add_le (V z ^ 2 • gaugeFixedAdjoint x η z) σ
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at ht
  have hB4 : V z ^ 4 ≤ B ^ 4 := by
    have := pow_le_pow_left₀ (sq_nonneg _) (hVB z) 2
    simpa only [← pow_mul] using this
  -- `‖L_x* (V² η)‖ ≤ V² ‖L_x* η‖ + ‖σ‖`, with `‖σ‖² = 4 V² ‖dV‖² ‖η‖² ≤ 4 c² B⁴ ‖η‖²`.
  have h₁ : (V z ^ 2 * ‖gaugeFixedAdjoint x η z‖) ^ 2 ≤ B ^ 4 * ‖gaugeFixedAdjoint x η z‖ ^ 2 := by
    rw [mul_pow, ← pow_mul]
    exact mul_le_mul_of_nonneg_right hB4 (sq_nonneg _)
  have h₂ : ‖σ‖ ^ 2 ≤ 4 * c ^ 2 * B ^ 4 * ‖η z‖ ^ 2 := by
    rw [hs]
    have := mul_le_mul_of_nonneg_right (hdV z) (by positivity : (0 : ℝ) ≤ 4 * V z ^ 2 * ‖η z‖ ^ 2)
    have h4 := mul_le_mul_of_nonneg_right hB4
      (by positivity : (0 : ℝ) ≤ 4 * c ^ 2 * ‖η z‖ ^ 2)
    nlinarith
  have h₃ := norm_sub_sq_le_two_mul (V z ^ 2 • gaugeFixedAdjoint x η z + σ) 0 σ
  rw [sub_zero, add_sub_cancel_right, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)] at h₃
  linarith

/-- The bookkeeping behind the bounded-weight estimate: real inequalities between the weighted
norms, the pairings and the approximation error `e` combine to the stated bound. -/
private theorem le_of_weighted_energy_inequalities {Y F e s a P Q R h g n Y₀ t δ c₀ B c : ℝ}
    (ht : 0 < t) (hδ : 0 < δ) (hc₀ : 0 < c₀) (hl : a = P + Q) (h₁ : P ≤ t / 2 * h + 1 / (2 * t) * e)
    (h₂ : Q ≤ δ / 2 * s + 1 / (2 * δ) * F) (h₃ : δ * s ≤ a) (h₄ : R ≤ 2 * a + 4 * c ^ 2 * s)
    (h₅ : h ≤ 2 * B ^ 4 * g + 8 * c ^ 2 * B ^ 4 * n) (h₆ : c₀ * n ≤ g)
    (h₇ : g ≤ 2 * e + 2 * Y₀) (h₈ : Y ≤ 2 * B ^ 2 * e + 2 * R) :
    Y ≤ (4 / δ + 8 * c ^ 2 / δ ^ 2) * F +
        (8 + 16 * c ^ 2 / δ) * t * (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) * Y₀ +
      (2 * B ^ 2 + (8 + 16 * c ^ 2 / δ) * t * (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) +
        (8 + 16 * c ^ 2 / δ) / (2 * t)) * e := by
  set D := 2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀
  set E := t / 2 * h + 1 / (2 * t) * e
  -- `E ≤ t D (e + Y₀) + e / (2 t)`, from `h ≤ D g` and `g ≤ 2 e + 2 Y₀`.
  have hn := mul_le_mul_of_nonneg_left h₆ (by positivity : (0 : ℝ) ≤ 8 * c ^ 2 * B ^ 4 / c₀)
  have hcn : 8 * c ^ 2 * B ^ 4 / c₀ * (c₀ * n) = 8 * c ^ 2 * B ^ 4 * n := by field_simp
  have hh := mul_le_mul_of_nonneg_left h₇ (by positivity : (0 : ℝ) ≤ t / 2 * D)
  have hh' := mul_le_mul_of_nonneg_left h₅ (by positivity : (0 : ℝ) ≤ t / 2)
  have hE : E ≤ t * D * e + t * D * Y₀ + 1 / (2 * t) * e := by
    linear_combination hh' + t / 2 * hn + hh - t / 2 * hcn
  -- `δ s ≤ 2 E + F / δ`, so `4 c² s ≤ 4 c² δ⁻¹ (2 E + F / δ)`.
  have hδs : δ * s ≤ 2 * E + F / δ := by linear_combination 2 * (h₃ + hl + h₁ + h₂)
  have hs := mul_le_mul_of_nonneg_left hδs (by positivity : (0 : ℝ) ≤ 4 * c ^ 2 / δ)
  have hκ := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ 8 + 16 * c ^ 2 / δ)
  have hss : 4 * c ^ 2 / δ * (δ * s) = 4 * c ^ 2 * s := by field_simp
  linear_combination h₈ + 2 * h₄ + 4 * hl + 4 * h₁ + 4 * h₂ + 2 * hδs + 2 * hs + hκ - 2 * hss

/-- One approximation step of the bounded-weight estimate. Let `y` be a weak solution of
`L_x y = f` and `V` a weight bounded by `B` with logarithmic gradient at most `|c|`, for which
`L_x L_x*` is weighted-coercive with constant `δ`. Then for every test field `η` and `t > 0`,
`∫ V² |y|²` is at most `(4 / δ + 8 c² / δ²) ∫ V² |f|²` plus errors that are small when `t` is small
and `L_x* η` is close to `y` in `L²`. -/
private theorem integral_sq_mul_norm_sq_le_add_mul_integral_norm_sub_sq
    (hx : ContDiff ℝ 1 x) {y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y 2 μ)
    (hf : MemLp f 2 μ)
    (hweak : ∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c₀ * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ)
    {V : ℂ → ℝ} (hV : ContDiff ℝ 2 V) {B : ℝ} (hVB : ∀ z, V z ^ 2 ≤ B ^ 2) {c : ℝ}
    (hdV : ∀ z, ‖fderiv ℝ V z‖ ^ 2 ≤ c ^ 2 * V z ^ 2) {δ : ℝ} (hδ : 0 < δ)
    (hcoer : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      δ * (∫ z, V z ^ 2 * ‖η z‖ ^ 2 ∂μ) ≤
        ∫ z, V z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ)
    {t : ℝ} (ht : 0 < t) {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ 2 η)
    (hηc : HasCompactSupport η) :
    ∫ z, V z ^ 2 * ‖y z‖ ^ 2 ∂μ ≤
      (4 / δ + 8 * c ^ 2 / δ ^ 2) * (∫ z, V z ^ 2 * ‖f z‖ ^ 2 ∂μ) +
        (8 + 16 * c ^ 2 / δ) * t * (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) *
          (∫ z, ‖y z‖ ^ 2 ∂μ) +
        (2 * B ^ 2 + (8 + 16 * c ^ 2 / δ) * t * (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) +
          (8 + 16 * c ^ 2 / δ) / (2 * t)) *
          ∫ z, ‖y z - gaugeFixedAdjoint x η z‖ ^ 2 ∂μ := by
  set G := gaugeFixedAdjoint x η
  set H := gaugeFixedAdjoint x (fun t ↦ V t ^ 2 • η t)
  have hwt {g : ℂ → EuclideanSpace ℝ (Fin 4)} (hg : MemLp g 2 μ) :=
    hg.integrable_sq_mul_norm_sq hV.continuous.aestronglyMeasurable (ae_of_all _ hVB)
  have hG : MemLp G 2 μ := memLp_gaugeFixedAdjoint hx.continuous (hη.of_le (by norm_num)) hηc
  have hH : MemLp H 2 μ := memLp_gaugeFixedAdjoint hx.continuous
    (((hV.pow 2).smul hη).of_le (by norm_num)) (hηc.smul_left (f := fun t ↦ V t ^ 2))
  have hη₂ : MemLp η 2 μ := hη.continuous.memLp_of_hasCompactSupport hηc
  have iyG : Integrable (fun z ↦ ‖y z - G z‖ ^ 2) μ := (hy.sub hG).norm.integrable_sq
  have iy := hy.norm.integrable_sq
  have iG := hG.norm.integrable_sq
  have hl := integral_sq_mul_inner_gaugeFixedOperator_eq_add hx hy hweak hV hη hηc
  -- The two pairings, by the arithmetic-geometric mean inequality.
  have h₁ : ∫ z, ⟪G z - y z, H z⟫ ∂μ ≤
      t / 2 * (∫ z, ‖H z‖ ^ 2 ∂μ) + 1 / (2 * t) * ∫ z, ‖y z - G z‖ ^ 2 ∂μ := by
    have := integral_mul_inner_le (ν := μ) (w := fun _ ↦ (1 : ℝ)) (G := fun z ↦ G z - y z)
      (η := H) (fun _ ↦ zero_le_one) (by simpa using hH.norm.integrable_sq)
      (by simpa using (hG.sub hy).norm.integrable_sq) ht
    simpa only [one_mul, norm_sub_rev (G _)] using this
  have h₂ := integral_mul_inner_le (ν := μ) (w := fun z ↦ V z ^ 2) (G := f) (η := η)
    (fun z ↦ sq_nonneg _) (hwt hη₂) (hwt hf) hδ
  -- Coercivity, the weighted adjoint energy, and the size of `L_x* (V² η)`.
  have h₃ := hcoer η hη hηc
  have h₄ := integral_sq_mul_norm_sq_gaugeFixedAdjoint_le (μ := μ) hx hη hηc
    (hV.of_le (by norm_num)) hdV
  have h₅ := integral_norm_sq_gaugeFixedAdjoint_sq_smul_le (μ := μ) hx hV hVB hdV hη hηc
  have h₆ := hgap η hη hηc
  -- `|L_x* η|² ≤ 2 |y - L_x* η|² + 2 |y|²` and `V² |y|² ≤ 2 B² |y - L_x* η|² + 2 V² |L_x* η|²`.
  have h₇ : ∫ z, ‖G z‖ ^ 2 ∂μ ≤
      2 * (∫ z, ‖y z - G z‖ ^ 2 ∂μ) + 2 * ∫ z, ‖y z‖ ^ 2 ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (iyG.const_mul _) (iy.const_mul _)]
    refine integral_mono iG ((iyG.const_mul _).add (iy.const_mul _)) fun z ↦ ?_
    have := norm_sub_sq_le_two_mul (G z) 0 (y z)
    rw [sub_zero, zero_sub, norm_neg, norm_sub_rev] at this
    linarith
  have h₈ : ∫ z, V z ^ 2 * ‖y z‖ ^ 2 ∂μ ≤
      2 * B ^ 2 * (∫ z, ‖y z - G z‖ ^ 2 ∂μ) + 2 * ∫ z, V z ^ 2 * ‖G z‖ ^ 2 ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (iyG.const_mul _) ((hwt hG).const_mul _)]
    refine integral_mono (hwt hy) ((iyG.const_mul _).add ((hwt hG).const_mul _)) fun z ↦ ?_
    have h2 := norm_sub_sq_le_two_mul (y z) 0 (G z)
    rw [sub_zero, zero_sub, norm_neg] at h2
    have := mul_le_mul_of_nonneg_left h2 (sq_nonneg (V z))
    have := mul_le_mul_of_nonneg_right (hVB z) (sq_nonneg ‖y z - G z‖)
    linarith
  exact le_of_weighted_energy_inequalities ht hδ hc₀ hl h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈

/-- **The bounded-weight estimate.** Let `y` be a square-integrable weak solution of `L_x y = f`
that is an `L²` limit of values `L_x* η` on test fields, and let `V` be a weight bounded by `B`
with logarithmic gradient at most `|c|`, for which `L_x L_x*` is weighted-coercive with constant
`δ`. Then `∫ V² |y|² ≤ (4 / δ + 8 c² / δ²) ∫ V² |f|²`; the bound `B` does not enter. -/
private theorem integral_sq_mul_norm_sq_le_of_forall_exists_lt
    (hx : ContDiff ℝ 1 x) {y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y 2 μ)
    (hf : MemLp f 2 μ)
    (hweak : ∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ)
    (happrox : ∀ ε > 0, ∃ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η ∧
      HasCompactSupport η ∧ ∫ z, ‖y z - gaugeFixedAdjoint x η z‖ ^ 2 ∂μ < ε)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c₀ * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ)
    {V : ℂ → ℝ} (hV : ContDiff ℝ 2 V) {B : ℝ} (hVB : ∀ z, V z ^ 2 ≤ B ^ 2) {c : ℝ}
    (hdV : ∀ z, ‖fderiv ℝ V z‖ ^ 2 ≤ c ^ 2 * V z ^ 2) {δ : ℝ} (hδ : 0 < δ)
    (hcoer : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      δ * (∫ z, V z ^ 2 * ‖η z‖ ^ 2 ∂μ) ≤
        ∫ z, V z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ) :
    ∫ z, V z ^ 2 * ‖y z‖ ^ 2 ∂μ ≤
      (4 / δ + 8 * c ^ 2 / δ ^ 2) * ∫ z, V z ^ 2 * ‖f z‖ ^ 2 ∂μ := by
  -- Nonnegativity facts used by `positivity` and `nlinarith` below.
  have : 0 ≤ 8 + 16 * c ^ 2 / δ := by positivity
  have : 0 ≤ 2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀ := by positivity
  have : 0 ≤ ∫ z, ‖y z‖ ^ 2 ∂μ := integral_nonneg fun z ↦ by positivity
  -- First let `L_x* η → y` in `L²` at fixed `t > 0`, then let `t → 0`.
  have step (t : ℝ) (ht : 0 < t) : ∫ z, V z ^ 2 * ‖y z‖ ^ 2 ∂μ ≤
      (4 / δ + 8 * c ^ 2 / δ ^ 2) * (∫ z, V z ^ 2 * ‖f z‖ ^ 2 ∂μ) +
        (8 + 16 * c ^ 2 / δ) * t * (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) *
          ∫ z, ‖y z‖ ^ 2 ∂μ := by
    have : 0 ≤ 2 * B ^ 2 + (8 + 16 * c ^ 2 / δ) * t * (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) +
        (8 + 16 * c ^ 2 / δ) / (2 * t) := by positivity
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨η, hη, hηc, he⟩ := happrox (ε / (2 * B ^ 2 + (8 + 16 * c ^ 2 / δ) * t *
      (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) + (8 + 16 * c ^ 2 / δ) / (2 * t) + 1)) (by positivity)
    have h := integral_sq_mul_norm_sq_le_add_mul_integral_norm_sub_sq hx hy hf hweak hc₀ hgap hV
      hVB hdV hδ hcoer ht hη hηc
    have he₀ : 0 ≤ ∫ z, ‖y z - gaugeFixedAdjoint x η z‖ ^ 2 ∂μ :=
      integral_nonneg fun z ↦ by positivity
    have hlt := (lt_div_iff₀ (by positivity)).1 he
    nlinarith
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set M := (8 + 16 * c ^ 2 / δ) * (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) * ∫ z, ‖y z‖ ^ 2 ∂μ
  have : 0 ≤ M := by positivity
  have h := step (ε / (M + 1)) (by positivity)
  have : (8 + 16 * c ^ 2 / δ) * (ε / (M + 1)) * (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) *
      ∫ z, ‖y z‖ ^ 2 ∂μ ≤ ε := by
    rw [show (8 + 16 * c ^ 2 / δ) * (ε / (M + 1)) * (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) *
      ∫ z, ‖y z‖ ^ 2 ∂μ = ε * (M / (M + 1)) by ring]
    exact mul_le_of_le_one_right hε.le ((div_le_one (by positivity)).2 (by linarith))
  linarith

/-- The weighted estimate for the weight `W = exp(c √(b + |z|²))` itself, at a field with
spectral gap `c₀` for which `L_x L_x*` is weighted-coercive with constant `δ` against weights with
logarithmic gradient at most that of `W`. Applying the bounded-weight estimate to the truncations
`W / (1 + W / (n + 1))` and letting `n → ∞` by Fatou's lemma gives, for every square-integrable
weak solution `y` of `L_x y = f` orthogonal to the weak kernel,
`∫ W² |y|² ≤ (4 / δ + 8 c² / δ²) ∫ W² |f|²`, where either side may be infinite. -/
private theorem lintegral_ofReal_exp_sq_mul_norm_sq_le (hx : ContDiff ℝ 1 x)
    {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hweak : ∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ)
    (horth : ∀ u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
      ∫ z, ⟪y z, u z⟫ ∂μ = 0)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c₀ * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ)
    {b c δ : ℝ} (hb₀ : 0 < b) (hδ : 0 < δ)
    (hcoer : ∀ V : ℂ → ℝ, ContDiff ℝ 2 V → (∀ z, 0 ≤ V z) →
      (∀ z, ‖fderiv ℝ V z‖ ≤ |c| * (‖z‖ / √(b + ‖z‖ ^ 2)) * V z) →
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      δ * (∫ z, V z ^ 2 * ‖η z‖ ^ 2 ∂μ) ≤
        ∫ z, V z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (c * √(b + ‖z‖ ^ 2)) ^ 2 * ‖y z‖ ^ 2) ∂μ ≤
      ENNReal.ofReal (4 / δ + 8 * c ^ 2 / δ ^ 2) *
        ∫⁻ z, ENNReal.ofReal (Real.exp (c * √(b + ‖z‖ ^ 2)) ^ 2 * ‖f z‖ ^ 2) ∂μ := by
  have hy := Lp.memLp y
  have hf := Lp.memLp f
  refine lintegral_ofReal_sq_mul_le_of_forall_lintegral_div_one_add_mul_le
    (u := fun z ↦ ‖y z‖ ^ 2)
    (contDiff_exp_mul_sqrt_add_norm_sq (n := 0) c hb₀).continuous.aemeasurable
    ((Lp.aestronglyMeasurable y).norm.pow 2).aemeasurable fun n ↦ ?_
  -- The estimate for the bounded weight `V = W / (1 + W / (n + 1))`.
  have hε : 0 < 1 / ((n : ℝ) + 1) := by positivity
  set V : ℂ → ℝ := fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) /
    (1 + 1 / ((n : ℝ) + 1) * Real.exp (c * √(b + ‖z‖ ^ 2)))
  have hV : ContDiff ℝ 2 V := contDiff_exp_div_one_add_mul_exp c hb₀ hε.le
  have hV₀ (z : ℂ) : 0 ≤ V z := exp_div_one_add_mul_exp_nonneg c hε.le z
  have hVB (z : ℂ) : V z ^ 2 ≤ (1 / (1 / ((n : ℝ) + 1))) ^ 2 :=
    pow_le_pow_left₀ (hV₀ z) (exp_div_one_add_mul_exp_le_one_div c hε z) 2
  have h := integral_sq_mul_norm_sq_le_of_forall_exists_lt hx hy hf hweak
    (fun ε hε ↦ exists_integral_norm_sub_gaugeFixedAdjoint_sq_lt hx.continuous horth hε) hc₀
    hgap hV hVB (fun z ↦ norm_fderiv_sq_le_of_norm_fderiv_le c hb₀.le (hV₀ z)
      (norm_fderiv_exp_div_one_add_mul_exp_le c hb₀ hε.le z)) hδ
    (hcoer V hV hV₀ (norm_fderiv_exp_div_one_add_mul_exp_le c hb₀ hε.le))
  have hwt {g : ℂ → EuclideanSpace ℝ (Fin 4)} (hg : MemLp g 2 μ) :=
    hg.integrable_sq_mul_norm_sq hV.continuous.aestronglyMeasurable (ae_of_all _ hVB)
  rw [← ofReal_integral_eq_lintegral_ofReal (hwt hy) (ae_of_all _ fun z ↦ by positivity)]
  refine (ENNReal.ofReal_le_ofReal h).trans ?_
  rw [ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal (hwt hf) (ae_of_all _ fun z ↦ by positivity)]
  gcongr with z
  exact exp_div_one_add_mul_exp_le_exp c hε.le z

omit [μ.IsAddHaarMeasure] in
/-- From the weight `exp(c √(b + |z|²))` to the weight `exp(c ρ)`, `ρ = √(1 + |z|²)`: the two
are comparable up to the factor `E = exp(|c| √|b - 1|)²` in either direction, so a bound
`∫ exp(c √(b + |z|²))² |y|² ≤ K₀ ∫ exp(c √(b + |z|²))² |f|²` gives
`‖exp(c ρ) y‖₂ ≤ √(E² K₀) ‖exp(c ρ) f‖₂`. -/
private theorem eLpNorm_exp_mul_smul_le_of_lintegral_le {b c K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (h : ∫⁻ z, ENNReal.ofReal (Real.exp (c * √(b + ‖z‖ ^ 2)) ^ 2 * ‖y z‖ ^ 2) ∂μ ≤
      ENNReal.ofReal K₀ *
        ∫⁻ z, ENNReal.ofReal (Real.exp (c * √(b + ‖z‖ ^ 2)) ^ 2 * ‖f z‖ ^ 2) ∂μ) :
    eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) 2 μ ≤
      Real.toNNReal √(Real.exp (|c| * √|b - 1|) ^ 2 * Real.exp (|c| * √|b - 1|) ^ 2 * K₀) *
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ := by
  set E : ℝ := Real.exp (|c| * √|b - 1|) ^ 2
  have hE : 0 ≤ E := by positivity
  set w : ℂ → ℝ := fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2))
  set W : ℂ → ℝ := fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2))
  -- The weights `w` and `W` are comparable.
  have hcmp {u v : ℂ → ℝ} (huv : ∀ z, u z ^ 2 ≤ E * v z ^ 2)
      (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
      ∫⁻ z, ENNReal.ofReal (u z ^ 2 * ‖g z‖ ^ 2) ∂μ ≤
        ENNReal.ofReal E * ∫⁻ z, ENNReal.ofReal (v z ^ 2 * ‖g z‖ ^ 2) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun z ↦ ?_
    rw [← ENNReal.ofReal_mul hE, ← mul_assoc]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (huv z) (sq_nonneg _))
  have hwy := hcmp (u := w) (v := W)
    (fun z ↦ by simpa only [abs_sub_comm 1 b] using sq_exp_mul_sqrt_add_norm_sq_le c 1 b z) y
  have hWf := hcmp (u := W) (v := w) (sq_exp_mul_sqrt_add_norm_sq_le c b 1) f
  -- Convert to `L²` norms.
  have hsm (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
      AEStronglyMeasurable (fun z ↦ w z • g z) μ :=
    ((contDiff_exp_mul_sqrt_add_norm_sq (n := 0) c one_pos).continuous.aestronglyMeasurable).smul
      (Lp.aestronglyMeasurable g)
  rw [eLpNorm_two_smul_eq_lintegral_ofReal_rpow (hsm y),
    eLpNorm_two_smul_eq_lintegral_ofReal_rpow (hsm f)]
  have hK : (Real.toNNReal √(E * E * K₀) : ℝ≥0∞) = ENNReal.ofReal (E * E * K₀) ^ (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← Real.sqrt_eq_rpow, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  rw [hK, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  gcongr
  calc ∫⁻ z, ENNReal.ofReal (w z ^ 2 * ‖y z‖ ^ 2) ∂μ
      ≤ ENNReal.ofReal E * (ENNReal.ofReal K₀ *
          (ENNReal.ofReal E * ∫⁻ z, ENNReal.ofReal (w z ^ 2 * ‖f z‖ ^ 2) ∂μ)) :=
        hwy.trans (by gcongr; exact h.trans (by gcongr))
    _ = ENNReal.ofReal (E * E * K₀) * ∫⁻ z, ENNReal.ofReal (w z ^ 2 * ‖f z‖ ^ 2) ∂μ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hE]
        ring

/-- **The exponentially weighted estimate for the weak right inverse, from a spectral gap and an
exterior mass.** Let `c₀ > 0`, `c² < a ≤ 1/4` and `R` be real numbers, and `ρ(z) = √(1 + |z|²)`.
There is `K`, depending only on `c₀`, `a`, `c` and `R`, with the following property. Let `x` be a
`C¹` vortex whose adjoint has spectral gap `c₀`, `c₀ ∫ |η|² ≤ ∫ |L_x* η|²` on test fields, and
whose squared mass `|α|² / 4` is at least `a` outside the disc of radius `R`. Then every
square-integrable weak solution `y` of `L_x y = f` orthogonal to the weak kernel of `L_x`
satisfies

`‖exp(c ρ) y‖₂ ≤ K ‖exp(c ρ) f‖₂`,

where either side may be infinite. Since `K` does not depend on `x`, the estimate is uniform over
every family of vortices with a common spectral gap and a common radius beyond which the mass
exceeds `a`; for instance over the vortices of degree `m` whose zeros lie in a fixed disc
(`exists_forall_eLpNorm_exp_mul_smul_le_of_forall_mem_norm_le`).

The proof applies the weighted coercivity of `L_x L_x*`
(`exists_pos_forall_mul_integral_sq_mul_norm_sq_le_integral_sq_mul_inner_gaugeFixedOperator`) to
the bounded weights `W / (1 + ε W)`, `W = exp(c √(b + |z|²))`, approximating `y` in `L²` by
values `L_x* η` on test fields, and then lets `ε → 0` by Fatou's lemma. -/
theorem exists_forall_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq
    {c₀ a c : ℝ} (hc₀ : 0 < c₀) (ha : a ≤ 1 / 4) (hca : c ^ 2 < a) (R : ℝ) :
    ∃ K : ℝ≥0, ∀ x : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 1 x →
      (∀ z, equation x z = 0) →
      (∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
        c₀ * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ) →
      (∀ z, R < ‖z‖ → a ≤ x z 2 ^ 2 + x z 3 ^ 2) →
      ∀ f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ) →
      (∀ u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
        ∫ z, ⟪y z, u z⟫ ∂μ = 0) →
      eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) 2 μ ≤
        K * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ := by
  obtain ⟨b, hb, δ, hδ, hcoer⟩ :=
    exists_pos_forall_mul_integral_sq_mul_norm_sq_le_integral_sq_mul_inner_gaugeFixedOperator
      (μ := μ) hc₀ ha hca R
  exact ⟨_, fun x hx hsol hgap hR f y hweak horth ↦
    eLpNorm_exp_mul_smul_le_of_lintegral_le (by positivity)
      (lintegral_ofReal_exp_sq_mul_norm_sq_le hx hweak horth hc₀ hgap (by linarith) hδ
        (hcoer x hx hsol hgap hR))⟩

/-- **The exponentially weighted estimate for the weak right inverse.** Let `x` be a `C¹`
solution of the plane vortex equation with `|α| → 1` at infinity, let `ρ(z) = √(1 + |z|²)` and
`|c| < 1/2`. There is `K` such that every square-integrable weak solution `y` of `L_x y = f`
orthogonal to the weak kernel of `L_x` satisfies

`‖exp(c ρ) y‖₂ ≤ K ‖exp(c ρ) f‖₂`,

where either side may be infinite. Such a `y` is unique
(`LinearMap.eq_of_inner_apply_eq_of_mem_orthogonal`), so it is the value at `f` of the weak right
inverse `Q` of `exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution`, and this is the
weighted output estimate `‖exp(c ρ) Q f‖₂ ≤ K ‖exp(c ρ) f‖₂` for every `f ∈ L²`. For `c > 0` it
says that `Q` maps inputs decaying like `exp(-c ρ)` in `L²` to outputs decaying at the same rate.
This is `exists_forall_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq` with the
spectral gap of the vortex and an exterior mass `a` strictly between `c²` and `1 / 4`. -/
theorem exists_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K : ℝ≥0, ∀ f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ) →
      (∀ u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
        ∫ z, ⟪y z, u z⟫ ∂μ = 0) →
      eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) 2 μ ≤
        K * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ := by
  have hc2 : c ^ 2 < 1 / 4 := by nlinarith [sq_abs c, abs_nonneg c]
  obtain ⟨c₀, hc₀, hgap⟩ :=
    exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := μ) hx hsol hlim
  obtain ⟨R, -, hR⟩ := exists_exterior_lt_mass hlim (a := (c ^ 2 + 1 / 4) / 2) (by linarith)
  obtain ⟨K, hK⟩ := exists_forall_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq
    (μ := μ) (a := (c ^ 2 + 1 / 4) / 2) (c := c) hc₀ (by linarith) (by linarith) R
  exact ⟨K, hK x hx hsol hgap fun z hz ↦ (hR z hz).le⟩

/-! ### The adjoint of the weak right inverse -/

/-- **The adjoint of a weak right inverse is a left inverse of `L_x*`.** Let `Q` be a bounded
operator on `L²(ℂ; ℝ⁴)` such that `Q f` is a weak solution of `L_x y = f` for every `f`. Then its
Hilbert space adjoint `Q†` sends the class of `L_x* η` to the class of `η`, for every compactly
supported `C²` field `η`. -/
theorem adjoint_apply_ae_eq_of_ae_eq_gaugeFixedAdjoint
    {Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hQ : ∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪Q f z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ)
    {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    {v : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} (hv : v =ᵐ[μ] gaugeFixedAdjoint x η) :
    ContinuousLinearMap.adjoint Q v =ᵐ[μ] η := by
  have hη₂ : MemLp η 2 μ := hη.continuous.memLp_of_hasCompactSupport hηc
  suffices ContinuousLinearMap.adjoint Q v = hη₂.toLp η from this ▸ hη₂.coeFn_toLp
  refine ext_inner_right ℝ fun f ↦ ?_
  calc ⟪ContinuousLinearMap.adjoint Q v, f⟫ = ⟪Q f, v⟫ := by
        rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
    _ = ∫ z, ⟪Q f z, gaugeFixedAdjoint x η z⟫ ∂μ := by
        rw [L2.inner_def]
        exact integral_congr_ae (hv.mono fun z hz ↦ by simp only [hz])
    _ = ⟪hη₂.toLp η, f⟫ := by rw [hQ f η hη hηc, real_inner_comm, L2.inner_toLp]

omit [μ.IsAddHaarMeasure] in
/-- **The adjoint of a weak right inverse vanishes on the weak kernel.** Let `Q` be a bounded
operator on `L²(ℂ; ℝ⁴)` whose values are orthogonal to the weak kernel of `L_x`. Then its Hilbert
space adjoint `Q†` vanishes on that kernel. -/
theorem adjoint_apply_eq_zero_of_integral_inner_gaugeFixedAdjoint_eq_zero
    {Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hQ : ∀ f u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
      ∫ z, ⟪Q f z, u z⟫ ∂μ = 0)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hu : ∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) :
    ContinuousLinearMap.adjoint Q u = 0 := by
  refine ext_inner_right ℝ fun f ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm, L2.inner_def]
  exact hQ f u hu

/-- **Weighted estimates pass to the adjoint by duality.** Suppose every square-integrable weak
solution `y` of `L_x y = f` orthogonal to the weak kernel of `L_x` satisfies
`‖exp(-c ρ) y‖₂ ≤ K ‖exp(-c ρ) f‖₂`, with `ρ = √(1 + |z|²)`. Let `Q` be a bounded operator on
`L²(ℂ; ℝ⁴)` such that `Q f` is such a solution for every `f`. Then its Hilbert space adjoint
satisfies `‖exp(c ρ) Q† g‖₂ ≤ K ‖exp(c ρ) g‖₂` for every `g ∈ L²`. -/
private theorem eLpNorm_exp_mul_smul_adjoint_apply_le {c : ℝ} {K : ℝ≥0}
    (hK : ∀ f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ) →
      (∀ u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
        ∫ z, ⟪y z, u z⟫ ∂μ = 0) →
      eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) • y z) 2 μ ≤
        K * eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ)
    {Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hweak : ∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪Q f z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ)
    (horth : ∀ f u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
      ∫ z, ⟪Q f z, u z⟫ ∂μ = 0)
    (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • ContinuousLinearMap.adjoint Q g z) 2 μ ≤
      K * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) 2 μ := by
  have hw : AEStronglyMeasurable (fun z : ℂ ↦ Real.exp (c * √(1 + ‖z‖ ^ 2))) μ :=
    (contDiff_exp_mul_sqrt_add_norm_sq (n := 0) c one_pos).continuous.aestronglyMeasurable
  have h := ContinuousLinearMap.eLpNorm_smul_le_of_eLpNorm_smul_adjoint_le
    (ContinuousLinearMap.adjoint Q) (p := 2) (p' := 2) (q := 2) (q' := 2) ENNReal.ofNat_ne_top
    (ae_of_all _ fun z ↦ (Real.exp_pos (c * √(1 + ‖z‖ ^ 2))).ne') hw (C := K) (fun f ↦ ?_) g
  · simpa using h
  · -- `Q†† = Q`, and `exp(c ρ)⁻¹ = exp(-c ρ)`.
    simpa [ContinuousLinearMap.adjoint_adjoint, ← Real.exp_neg, neg_mul] using
      hK f (Q f) (hweak f) (horth f)

/-- **Exponentially weighted estimate for the adjoint of the weak right inverse.** Let `x` be a
`C¹` solution of the plane vortex equation with `|α| → 1` at infinity, let `ρ = √(1 + |z|²)` and
`|c| < 1/2`. There is `K`, depending only on the vortex and `c`, with the following property. Let
`Q` be a bounded operator on `L²(ℂ; ℝ⁴)` such that `Q f` is a weak solution of `L_x y = f`
orthogonal to the weak kernel of `L_x`, for every `f`, for instance the weak right inverse of
`exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution`. Then its Hilbert space adjoint
`Q†` satisfies

`‖exp(c ρ) Q† g‖₂ ≤ K ‖exp(c ρ) g‖₂`  for every `g ∈ L²`,

where either side may be infinite. By `adjoint_apply_ae_eq_of_ae_eq_gaugeFixedAdjoint` and
`adjoint_apply_eq_zero_of_integral_inner_gaugeFixedAdjoint_eq_zero`, `Q†` is the left inverse of
`L_x*` vanishing on the weak kernel, formally `(L_x L_x*)⁻¹ L_x`. For `c > 0` the estimate says that
`Q†` maps inputs decaying like `exp(-c ρ)` in `L²` to outputs decaying at the same rate. -/
theorem exists_eLpNorm_exp_mul_smul_adjoint_apply_le (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K : ℝ≥0, ∀ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪Q f z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ) →
      (∀ f u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
        ∫ z, ⟪Q f z, u z⟫ ∂μ = 0) →
      ∀ g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • ContinuousLinearMap.adjoint Q g z) 2 μ ≤
          K * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) 2 μ := by
  obtain ⟨K, hK⟩ := exists_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq (μ := μ)
    hx hsol hlim (c := -c) (by rwa [abs_neg])
  exact ⟨K, fun Q hweak horth ↦ eLpNorm_exp_mul_smul_adjoint_apply_le hK hweak horth⟩

/-! ### Uniformity over windows of divisors -/

/-- **The weighted estimate for the weak right inverse, uniformly over a window of divisors.**
For every degree `m`, radius `r` and rate `|c| < 1/2` there is a constant `K` with the following
property, where `ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the degree-`m` end
framing whose zeros lie in the closed disc of radius `r`. Then every square-integrable weak
solution `y` of `L_x y = f` orthogonal to the weak kernel of `L_x`, in particular the value at
`f` of the weak right inverse, satisfies

`‖exp(c ρ) y‖₂ ≤ K ‖exp(c ρ) f‖₂`,

where either side may be infinite. The constant depends only on `m`, `r` and `c`, not on the
vortex or on the position of its zeros in the disc, collisions included. Every compact window
of `Sym ℂ m` lies in such a disc.

The two inputs of `exists_forall_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq`
are uniform here: the spectral gap over all vortices of degree `m`
(`exists_pos_forall_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint`), and a radius
beyond which `|α|²` is close to one for all vortices whose zeros lie in the disc
(`exists_forall_lt_normSq_of_forall_mem_norm_le`). -/
theorem exists_forall_eLpNorm_exp_mul_smul_le_of_forall_mem_norm_le (m : ℕ) (r : ℝ) {c : ℝ}
    (hc : |c| < 1 / 2) :
    ∃ K : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ a ∈ D, ‖a‖ ≤ r) →
      ∀ f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ) →
      (∀ u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
        ∫ z, ⟪y z, u z⟫ ∂μ = 0) →
      eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) 2 μ ≤
        K * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ := by
  have hc2 : c ^ 2 < 1 / 4 := by nlinarith [sq_abs c, abs_nonneg c]
  obtain ⟨c₀, hc₀, hgap⟩ :=
    exists_pos_forall_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := μ) m
  obtain ⟨R, hR⟩ := exists_forall_lt_normSq_of_forall_mem_norm_le m r
    (θ := 2 * c ^ 2 + 1 / 2) (by linarith)
  obtain ⟨K, hK⟩ := exists_forall_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq
    (μ := μ) (a := (c ^ 2 + 1 / 4) / 2) (c := c) hc₀ (by linarith) (by linarith) R
  exact ⟨K, fun x D hx hsol hframe hD hDr ↦ hK x (hx.of_le (by simp)) hsol
    (hgap x D hx hsol hframe hD) fun z hz ↦ by linarith [hR x D hx hsol hframe hD hDr z hz]⟩

/-- **The weighted estimate for the adjoint of the weak right inverse, uniformly over a window of
divisors.** For every degree `m`, radius `r` and rate `|c| < 1/2` there is a constant `K` with the
following property, where `ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the
degree-`m` end framing whose zeros lie in the closed disc of radius `r`, and let `Q` be a bounded
operator on `L²(ℂ; ℝ⁴)` such that `Q f` is a weak solution of `L_x y = f` orthogonal to the weak
kernel of `L_x`, for every `f`. Then its Hilbert space adjoint `Q†`, the left inverse of `L_x*`
vanishing on the weak kernel, satisfies

`‖exp(c ρ) Q† g‖₂ ≤ K ‖exp(c ρ) g‖₂`  for every `g ∈ L²`.

The constant depends only on `m`, `r` and `c`. -/
theorem exists_forall_eLpNorm_exp_mul_smul_adjoint_apply_le_of_forall_mem_norm_le (m : ℕ)
    (r : ℝ) {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ a ∈ D, ‖a‖ ≤ r) →
      ∀ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪Q f z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ) →
      (∀ f u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
        ∫ z, ⟪Q f z, u z⟫ ∂μ = 0) →
      ∀ g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • ContinuousLinearMap.adjoint Q g z) 2 μ ≤
          K * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) 2 μ := by
  obtain ⟨K, hK⟩ := exists_forall_eLpNorm_exp_mul_smul_le_of_forall_mem_norm_le (μ := μ) m r
    (c := -c) (by rwa [abs_neg])
  exact ⟨K, fun x D hx hsol hframe hD hDr Q hweak horth ↦
    eLpNorm_exp_mul_smul_adjoint_apply_le (hK x D hx hsol hframe hD hDr) hweak horth⟩

end TauCeti.Vortex
