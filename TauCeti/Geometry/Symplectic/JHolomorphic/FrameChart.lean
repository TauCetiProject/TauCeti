/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.JHolomorphic.Varying
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.LinearAlgebra.Complex.LinearPart
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Complex.OperatorNorm
import TauCeti.LinearAlgebra.TotallyReal.Extension
import TauCeti.LinearAlgebra.TotallyReal.Frame

/-!
# Frame charts straightening a J-holomorphic disc

Let `J : V → (V →L[ℝ] V)` be a family of endomorphisms of a real normed space `V` and let
`u : ℂ → V` be a curve. When `J` is an almost complex structure and `u` is J-holomorphic,
`du ∘ i = J(u) ∘ du`, McDuff and Salamon straighten `u` near a point `a₀` where `du` is injective
by the chart

`Φ(a, x, y) = u(a) + N x + J(u(a)) (N y)`,

where the *frame* `N : W → V` is a linear map from a real normed space `W` (`Φ = frameChart J u N`).
For `V = ℝ²ⁿ` and `W = ℝⁿ⁻¹` with basis vectors `Z₂, …, Zₙ`, this is
`Φ(a, x + iy) = u(a) + Σ (xⱼ Zⱼ + yⱼ J(u(a)) Zⱼ)` with complex normal coordinates `x + iy`.
The chart sends `ℂ × {0}` onto the curve, `Φ(a, 0, 0) = u(a)`, and its derivative there is
`(δa, δx, δy) ↦ du(a) δa + N δx + J(u(a)) (N δy)` (`TauCeti.hasStrictFDerivAt_frameChart`). The
hypotheses `J(u(a))² = -1` and complex linearity of `du(a)` are assumed only where results need
them, at the single point `a`. Under them this derivative is complex linear from the standard
complex structure `(δa, δx, δy) ↦ (i δa, -δy, δx)` of `ℂ × W × W` to `J(u(a))`
(`TauCeti.isComplexLinear_frameChartDeriv`, and
`TauCeti.IsJHolomorphicAt.isComplexLinearMap_frameChartDeriv` for a curve which is
J-holomorphic in the sense of `TauCeti.IsJHolomorphicAt`): in the chart, `J` is the standard
structure along the straightened curve. When the derivative is bijective, `Φ` is a local
homeomorphism near `(a, 0, 0)` (`TauCeti.exists_openPartialHomeomorph_frameChart`), and it is
`C^n` when `u` and `J ∘ u` are (`TauCeti.contDiffAt_frameChart`).

A frame making the derivative bijective exists whenever `du(a)` is nonzero
(`TauCeti.exists_bijective_frameChartDeriv`). Since `du(a)` is complex linear, its image is the
complex line spanned by `v = du(a) 1` and `J v`; a maximal totally real subspace containing `v`
(`TauCeti.exists_mem_isMaximalTotallyReal`) splits as `ℝ v` plus a subspace `L`, and the inclusion
of `L` is the frame. The basis `{du(a) 1, Z₂, …, Zₙ}` of McDuff and Salamon is a basis of this
maximal totally real subspace.

The frame is constant here, rather than a family `Z(a)` along the curve. A frame which completes
`du(a₀)` at one point completes `du(a)` at nearby points too, by openness of invertibility, so
one frame suffices for the local chart. These are the coordinates in which McDuff and Salamon
compare two J-holomorphic curves through a common point and factor one through the other.

## Main definitions

* `TauCeti.frameChart`: the chart `Φ(a, x, y) = u(a) + N x + J(u(a)) (N y)`.
* `TauCeti.frameStructure`: the standard almost complex structure `(a, x, y) ↦ (i a, -y, x)` on
  `ℂ × W × W`.
* `TauCeti.frameChartDeriv`: the linear model `(a, x, y) ↦ u' a + N x + J₀ (N y)` of the chart.

## Main results

* `TauCeti.hasStrictFDerivAt_frameChart`: the derivative of the chart along `ℂ × {0}`.
* `TauCeti.isComplexLinear_frameChartDeriv`,
  `TauCeti.IsJHolomorphicAt.isComplexLinearMap_frameChartDeriv`: along `ℂ × {0}` the chart pulls
  `J` back to the standard complex structure.
* `TauCeti.exists_bijective_frameChartDeriv`: a frame making the derivative bijective exists.
* `TauCeti.exists_openPartialHomeomorph_frameChart`: the chart is a local homeomorphism near
  `(a, 0, 0)`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.4, Lemma 2.4.2 and the proof of Lemma 2.4.3.
-/

public section

open Complex Module

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The **frame chart** of a curve `u : ℂ → V` for a family of endomorphisms `J` and a frame
`N : W → V`: `Φ(a, x, y) = u(a) + N x + J(u(a)) (N y)`. It sends `ℂ × {0}` onto the curve. When
its linear model `frameChartDeriv` at `(a, 0, 0)` is bijective, the chart is a local homeomorphism
near `(a, 0, 0)`; along `ℂ × {0}` its derivative carries the standard structure to `J(u(a))` when
`J(u(a))² = -1` and `du(a)` is complex linear. -/
def frameChart (J : V → V →L[ℝ] V) (u : ℂ → V) (N : W →L[ℝ] V) (w : ℂ × W × W) : V :=
  u w.1 + N w.2.1 + J (u w.1) (N w.2.2)

variable {J : V → V →L[ℝ] V} {u : ℂ → V} {N : W →L[ℝ] V}

theorem frameChart_def (J : V → V →L[ℝ] V) (u : ℂ → V) (N : W →L[ℝ] V) :
    frameChart J u N = fun w ↦ u w.1 + N w.2.1 + J (u w.1) (N w.2.2) :=
  (rfl)

/-- The frame chart sends `ℂ × {0}` onto the curve. -/
@[simp]
theorem frameChart_zero (a : ℂ) : frameChart J u N (a, 0, 0) = u a := by
  simp [frameChart]

variable (W) in
/-- The standard almost complex structure `(a, x, y) ↦ (i a, -y, x)` on `ℂ × W × W`, the direct sum
of multiplication by `i` on `ℂ` and the doubling structure on `W × W`, in which `x + i y` is the
complex normal coordinate of the frame chart. -/
noncomputable def frameStructure : AlmostComplexStructure (ℂ × W × W) :=
  (AlmostComplexStructure.ofComplexModule ℂ).prod (AlmostComplexStructure.product W)

@[simp]
theorem frameStructure_apply (w : ℂ × W × W) :
    frameStructure W w = (I * w.1, -w.2.2, w.2.1) := by
  simp [frameStructure]

/-- The linear model `(a, x, y) ↦ u' a + N x + J₀ (N y)` of the frame chart: its derivative along
`ℂ × {0}`, for `u' = du(a)` and `J₀ = J(u(a))`. -/
noncomputable def frameChartDeriv (u' : ℂ →L[ℝ] V) (J₀ : V →L[ℝ] V) (N : W →L[ℝ] V) :
    (ℂ × W × W) →L[ℝ] V :=
  u'.coprod (N.coprod (J₀ ∘L N))

@[simp]
theorem frameChartDeriv_apply (u' : ℂ →L[ℝ] V) (J₀ : V →L[ℝ] V) (N : W →L[ℝ] V)
    (w : ℂ × W × W) : frameChartDeriv u' J₀ N w = u' w.1 + (N w.2.1 + J₀ (N w.2.2)) := by
  simp [frameChartDeriv]

/-- **The derivative of the frame chart along the curve.** If `u` and `J ∘ u` are strictly
differentiable at `a`, the frame chart is strictly differentiable at `(a, 0, 0)` with derivative
`(δa, δx, δy) ↦ du(a) δa + N δx + J(u(a)) (N δy)`. -/
theorem hasStrictFDerivAt_frameChart {u' : ℂ →L[ℝ] V} {J' : ℂ →L[ℝ] V →L[ℝ] V} {a : ℂ}
    (hu : HasStrictFDerivAt u u' a) (hJ : HasStrictFDerivAt (fun z ↦ J (u z)) J' a) :
    HasStrictFDerivAt (frameChart J u N) (frameChartDeriv u' (J (u a)) N) (a, 0, 0) := by
  set p : ℂ × W × W := (a, 0, 0)
  have h₁ : HasStrictFDerivAt (fun w : ℂ × W × W ↦ u w.1)
      (u' ∘L ContinuousLinearMap.fst ℝ ℂ (W × W)) p :=
    hu.comp p (hasStrictFDerivAt_fst (p := p))
  have h₂ : HasStrictFDerivAt (fun w : ℂ × W × W ↦ N w.2.1)
      (N ∘L ContinuousLinearMap.fst ℝ W W ∘L ContinuousLinearMap.snd ℝ ℂ (W × W)) p :=
    (N ∘L ContinuousLinearMap.fst ℝ W W ∘L ContinuousLinearMap.snd ℝ ℂ (W × W)).hasStrictFDerivAt
  have h₃ : HasStrictFDerivAt (fun w : ℂ × W × W ↦ N w.2.2)
      (N ∘L ContinuousLinearMap.snd ℝ W W ∘L ContinuousLinearMap.snd ℝ ℂ (W × W)) p :=
    (N ∘L ContinuousLinearMap.snd ℝ W W ∘L ContinuousLinearMap.snd ℝ ℂ (W × W)).hasStrictFDerivAt
  have h₄ : HasStrictFDerivAt (fun w : ℂ × W × W ↦ J (u w.1))
      (J' ∘L ContinuousLinearMap.fst ℝ ℂ (W × W)) p :=
    HasStrictFDerivAt.comp (g := fun z ↦ J (u z)) p hJ (hasStrictFDerivAt_fst (p := p))
  rw [frameChart_def]
  refine ((h₁.add h₂).add (h₄.clm_apply h₃)).congr_fderiv ?_
  ext w <;> simp [p, add_assoc]

/-- The frame chart is `C^n` at every point where `u` and `J ∘ u` are `C^n`. -/
theorem contDiffAt_frameChart {n : WithTop ℕ∞} {w : ℂ × W × W} (hu : ContDiffAt ℝ n u w.1)
    (hJ : ContDiffAt ℝ n (fun z ↦ J (u z)) w.1) : ContDiffAt ℝ n (frameChart J u N) w := by
  have h₁ : ContDiffAt ℝ n (fun w : ℂ × W × W ↦ u w.1) w := hu.comp w contDiffAt_fst
  have h₂ : ContDiffAt ℝ n (fun w : ℂ × W × W ↦ N w.2.1) w :=
    (N ∘L ContinuousLinearMap.fst ℝ W W ∘L ContinuousLinearMap.snd ℝ ℂ (W × W)).contDiff.contDiffAt
  have h₃ : ContDiffAt ℝ n (fun w : ℂ × W × W ↦ N w.2.2) w :=
    (N ∘L ContinuousLinearMap.snd ℝ W W ∘L ContinuousLinearMap.snd ℝ ℂ (W × W)).contDiff.contDiffAt
  have h₄ : ContDiffAt ℝ n (fun w : ℂ × W × W ↦ J (u w.1)) w := hJ.comp w contDiffAt_fst
  rw [frameChart_def]
  exact (h₁.add h₂).add (h₄.clm_apply h₃)

/-- **Along the curve, the frame chart pulls `J` back to the standard structure.** If
`J₀² = -1` and `u'` is complex linear from `i` to `J₀` (the Cauchy–Riemann equation of a
J-holomorphic curve at a point with `J₀ = J(u(a))`), then the linear model of the frame chart is
complex linear from the standard structure of `ℂ × W × W` to `J₀`. -/
theorem isComplexLinear_frameChartDeriv {u' : ℂ →L[ℝ] V} {J₀ : V →L[ℝ] V}
    (hJ₀ : (J₀ : V →ₗ[ℝ] V) ∘ₗ J₀ = -LinearMap.id)
    (hu : IsComplexLinear (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (J₀ : V →ₗ[ℝ] V)
      (u' : ℂ →ₗ[ℝ] V))
    (N : W →L[ℝ] V) :
    IsComplexLinear (frameStructure W).toLinearMap (J₀ : V →ₗ[ℝ] V)
      (frameChartDeriv u' J₀ N : (ℂ × W × W) →ₗ[ℝ] V) := by
  have hJJ (v : V) : J₀ (J₀ v) = -v := by simpa using LinearMap.congr_fun hJ₀ v
  refine isComplexLinear_of_apply fun w ↦ ?_
  have hw : u' (I * w.1) = J₀ (u' w.1) := by simpa using hu.apply w.1
  simp [hw, hJJ, add_comm]

/-- **Along a J-holomorphic curve, the frame chart pulls `J` back to the standard structure.** If
`u` is J-holomorphic at `a` with derivative `u'`, for an almost complex structure `J'` agreeing with
`J` at `u(a)`, then the linear model of the frame chart at `(a, 0, 0)` is complex linear from the
standard structure of `ℂ × W × W` to `J'(u(a))`. -/
theorem IsJHolomorphicAt.isComplexLinearMap_frameChartDeriv {J' : V → AlmostComplexStructure V}
    {a : ℂ} {u' : ℂ →L[ℝ] V}
    (hu : IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ) J' u a)
    (hu' : HasFDerivAt u u' a) (hJ : (J (u a) : V →ₗ[ℝ] V) = (J' (u a)).toLinearMap)
    (N : W →L[ℝ] V) :
    IsComplexLinearMap (frameStructure W) (J' (u a)) (frameChartDeriv u' (J (u a)) N) := by
  obtain ⟨f', hf', hlin⟩ := (isJHolomorphicAt_iff _ _ u a).1 hu
  obtain rfl := hu'.unique hf'
  rw [isComplexLinearMap_iff_isComplexLinear, ← hJ]
  exact isComplexLinear_frameChartDeriv (hJ ▸ (J' (u a)).square_neg) (hJ ▸ hlin) N

/-- **Frames exist.** If `J₀² = -1` and `u'` is complex linear from `i` to `J₀` and nonzero, there
is a subspace `L` whose inclusion is a frame completing `u'`: the linear model
`(a, x, y) ↦ u' a + x + J₀ y` of the frame chart is bijective from `ℂ × L × L` onto `V`. -/
theorem exists_bijective_frameChartDeriv {u' : ℂ →L[ℝ] V} {J₀ : V →L[ℝ] V}
    (hJ₀ : (J₀ : V →ₗ[ℝ] V) ∘ₗ J₀ = -LinearMap.id)
    (hu : IsComplexLinear (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (J₀ : V →ₗ[ℝ] V)
      (u' : ℂ →ₗ[ℝ] V))
    (hu₁ : u' 1 ≠ 0) :
    ∃ L : Submodule ℝ V, Function.Bijective (frameChartDeriv u' J₀ L.subtypeL) := by
  set v := u' 1
  have hJJ (x : V) : J₀ (J₀ x) = -x := by simpa using LinearMap.congr_fun hJ₀ x
  have hJinj : Function.Injective J₀ := fun x y hxy ↦ by simpa [hJJ] using congrArg J₀ hxy
  -- A maximal totally real subspace `L₁` through `v`, and a complement `L` of `ℝ v` in it.
  obtain ⟨L₁, hvL₁, hL₁⟩ := exists_mem_isMaximalTotallyReal hJ₀ v
  obtain ⟨C, hC⟩ := (ℝ ∙ v).exists_isCompl
  set L := C ⊓ L₁
  -- The frame `A (r, x) = r v + x` parametrizes `L₁` injectively.
  set A : (ℝ × L) →ₗ[ℝ] V := (LinearMap.toSpanSingleton ℝ V v).coprod L.subtype
  have hA : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range,
      LinearMap.ker_toSpanSingleton ℝ hu₁, Submodule.ker_subtype, Submodule.prod_bot]
    simpa [LinearMap.range_toSpanSingleton] using hC.disjoint.mono_right inf_le_left
  have hrange : LinearMap.range A = L₁ := by
    rw [LinearMap.range_coprod, LinearMap.range_toSpanSingleton, Submodule.range_subtype,
      ← sup_inf_assoc_of_le C ((Submodule.span_singleton_le_iff_mem v L₁).2 hvL₁), hC.sup_eq_top,
      top_inf_eq]
  have hbij := (hrange ▸ hL₁).bijective_coprod hA (hJinj.comp hA)
  -- The linear model is the doubled frame `A ⊕ J₀ A` after regrouping `ℂ × L × L` as
  -- `(ℝ × L) × (ℝ × L)` by real and imaginary parts.
  let σ : (ℂ × L × L) ≃ₗ[ℝ] (ℝ × L) × (ℝ × L) :=
    (Complex.equivRealProdLm.prodCongr (LinearEquiv.refl ℝ (L × L))).trans
      (LinearEquiv.prodProdProdComm ℝ ℝ ℝ L L)
  have hI : u' I = J₀ v := by simpa [v] using hu.apply 1
  have hcomp :
      ⇑(frameChartDeriv u' J₀ L.subtypeL) = (A.coprod ((J₀ : V →ₗ[ℝ] V).comp A)) ∘ σ := by
    funext w
    simp [A, σ, hI, u'.apply_eq_re_smul_one_add_im_smul_I w.1]
    abel
  exact ⟨L, hcomp ▸ hbij.comp σ.bijective⟩

/-- **The frame chart is a local homeomorphism** at `(a, 0, 0)` when `u` and `J ∘ u` are strictly
differentiable at `a` and the linear model of the chart is bijective. -/
theorem exists_openPartialHomeomorph_frameChart [CompleteSpace V] [CompleteSpace W]
    {u' : ℂ →L[ℝ] V} {J' : ℂ →L[ℝ] V →L[ℝ] V} {a : ℂ} (hu : HasStrictFDerivAt u u' a)
    (hJ : HasStrictFDerivAt (fun z ↦ J (u z)) J' a)
    (hD : Function.Bijective (frameChartDeriv u' (J (u a)) N)) :
    ∃ e : OpenPartialHomeomorph (ℂ × W × W) V, (a, 0, 0) ∈ e.source ∧ ⇑e = frameChart J u N := by
  set D := ContinuousLinearEquiv.ofBijective (frameChartDeriv u' (J (u a)) N)
    (LinearMap.ker_eq_bot.2 hD.1) (LinearMap.range_eq_top.2 hD.2)
  have hΦ : HasStrictFDerivAt (frameChart J u N) (D : (ℂ × W × W) →L[ℝ] V) (a, 0, 0) :=
    hasStrictFDerivAt_frameChart hu hJ
  exact ⟨hΦ.toOpenPartialHomeomorph _, hΦ.mem_toOpenPartialHomeomorph_source,
    hΦ.toOpenPartialHomeomorph_coe⟩

end TauCeti
