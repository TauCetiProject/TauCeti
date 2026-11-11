/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.LinearAlgebra.TotallyReal.Extension
import TauCeti.LinearAlgebra.TotallyReal.Frame

/-!
# Frame charts straightening a J-holomorphic disc

Let `J` be an almost complex structure on an open set of a real normed space `V`, written as a
family `J : V → (V →L[ℝ] V)` of endomorphisms with `J(p)² = -1`, and let `u : ℂ → V` be a
J-holomorphic curve, `du ∘ i = J(u) ∘ du`. McDuff and Salamon straighten `u` near a point `a₀`
where `du` is injective by the chart

`Φ(a, x, y) = u(a) + N x + J(u(a)) (N y)`,

where the *frame* `N : W → V` is a linear map from a real normed space `W` (`Φ = frameChart J u N`).
For `V = ℝ²ⁿ` and `W = ℝⁿ⁻¹` with basis vectors `Z₂, …, Zₙ`, this is
`Φ(a, x + iy) = u(a) + Σ (xⱼ Zⱼ + yⱼ J(u(a)) Zⱼ)` with complex normal coordinates `x + iy`.
The chart sends `ℂ × {0}` onto the curve, `Φ(a, 0, 0) = u(a)`, and its derivative there is
`(δa, δx, δy) ↦ du(a) δa + N δx + J(u(a)) (N δy)` (`TauCeti.hasStrictFDerivAt_frameChart`). This
derivative intertwines the standard complex structure `(δa, δx, δy) ↦ (i δa, -δy, δx)` of
`ℂ × W × W` with `J(u(a))` (`TauCeti.frameChartDeriv_comp_frameStructure`): in the chart, `J` is
the standard structure along the straightened curve. When the derivative is bijective, `Φ` is a
local homeomorphism at `(a, 0, 0)` (`TauCeti.exists_openPartialHomeomorph_frameChart`), and it is
`C^n` when `u` and `J` are (`TauCeti.contDiffAt_frameChart`).

A frame making the derivative bijective exists in finite dimension whenever `du(a)` is nonzero
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
* `TauCeti.frameStructure`: the standard complex structure `(a, x, y) ↦ (i a, -y, x)` on
  `ℂ × W × W`.
* `TauCeti.frameChartDeriv`: the linear model `(a, x, y) ↦ u' a + N x + J₀ (N y)` of the chart.

## Main results

* `TauCeti.hasStrictFDerivAt_frameChart`: the derivative of the chart along `ℂ × {0}`.
* `TauCeti.frameChartDeriv_comp_frameStructure`: along `ℂ × {0}` the chart pulls `J` back to the
  standard complex structure.
* `TauCeti.exists_bijective_frameChartDeriv`: a frame making the derivative bijective exists.
* `TauCeti.exists_openPartialHomeomorph_frameChart`: the chart is a local homeomorphism.

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
`J` is an almost complex structure, `u` is J-holomorphic and the frame completes `du`, it is a local
homeomorphism along the curve in which `J` is the standard structure on `ℂ × {0}`. -/
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
/-- The standard complex structure `(a, x, y) ↦ (i a, -y, x)` on `ℂ × W × W`, in which `x + i y`
is the complex normal coordinate of the frame chart. -/
noncomputable def frameStructure : (ℂ × W × W) →L[ℝ] (ℂ × W × W) :=
  (I • ContinuousLinearMap.id ℝ ℂ).prodMap
    ((-ContinuousLinearMap.snd ℝ W W).prod (ContinuousLinearMap.fst ℝ W W))

@[simp]
theorem frameStructure_apply (w : ℂ × W × W) :
    frameStructure W w = (I * w.1, -w.2.2, w.2.1) := by
  ext <;> simp [frameStructure]

/-- The standard structure squares to `-1`. -/
theorem frameStructure_frameStructure (w : ℂ × W × W) :
    frameStructure W (frameStructure W w) = -w := by
  ext <;> simp [← mul_assoc]

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

/-- The frame chart is `C^n` at every point where `u` is `C^n` and `J` is `C^n` along `u`. -/
theorem contDiffAt_frameChart {n : WithTop ℕ∞} {w : ℂ × W × W} (hu : ContDiffAt ℝ n u w.1)
    (hJ : ContDiffAt ℝ n J (u w.1)) : ContDiffAt ℝ n (frameChart J u N) w := by
  have h₁ : ContDiffAt ℝ n (fun w : ℂ × W × W ↦ u w.1) w := hu.comp w contDiffAt_fst
  have h₂ : ContDiffAt ℝ n (fun w : ℂ × W × W ↦ N w.2.1) w :=
    (N ∘L ContinuousLinearMap.fst ℝ W W ∘L ContinuousLinearMap.snd ℝ ℂ (W × W)).contDiff.contDiffAt
  have h₃ : ContDiffAt ℝ n (fun w : ℂ × W × W ↦ N w.2.2) w :=
    (N ∘L ContinuousLinearMap.snd ℝ W W ∘L ContinuousLinearMap.snd ℝ ℂ (W × W)).contDiff.contDiffAt
  have h₄ : ContDiffAt ℝ n (fun w : ℂ × W × W ↦ J (u w.1)) w := hJ.comp w h₁
  rw [frameChart_def]
  exact (h₁.add h₂).add (h₄.clm_apply h₃)

/-- **Along the curve, the frame chart pulls `J` back to the standard structure.** If
`J₀² = -1` and `u'` is complex linear for `J₀` (`u' (i z) = J₀ (u' z)`, the Cauchy–Riemann equation
of a J-holomorphic curve at a point with `J₀ = J(u(a))`), then the linear model of the frame chart
carries the standard structure of `ℂ × W × W` to `J₀`. -/
theorem frameChartDeriv_comp_frameStructure {u' : ℂ →L[ℝ] V} {J₀ : V →L[ℝ] V}
    (hJ₀ : ∀ v, J₀ (J₀ v) = -v) (hu : ∀ z, u' (I * z) = J₀ (u' z)) (N : W →L[ℝ] V) :
    frameChartDeriv u' J₀ N ∘L frameStructure W = J₀ ∘L frameChartDeriv u' J₀ N := by
  ext w <;> simp [hu, hJ₀, add_comm]

/-- The value of a real-linear map on `ℂ` in terms of its values on `1` and `i`. -/
private theorem apply_eq_re_smul_add_im_smul (u' : ℂ →L[ℝ] V) (z : ℂ) :
    u' z = z.re • u' 1 + z.im • u' I := by
  have hz : z = z.re • (1 : ℂ) + z.im • I := by
    apply Complex.ext <;> simp
  nth_rewrite 1 [hz]
  rw [map_add, map_smul, map_smul]

/-- **Frames exist.** In finite dimension, if `J₀² = -1` and `u'` is complex linear for `J₀` and
nonzero, there is a subspace `L` whose inclusion is a frame completing `u'`: the linear model
`(a, x, y) ↦ u' a + x + J₀ y` of the frame chart is bijective from `ℂ × L × L` onto `V`. -/
theorem exists_bijective_frameChartDeriv [FiniteDimensional ℝ V] {u' : ℂ →L[ℝ] V}
    {J₀ : V →L[ℝ] V} (hJ₀ : ∀ v, J₀ (J₀ v) = -v) (hu : ∀ z, u' (I * z) = J₀ (u' z))
    (hu₁ : u' 1 ≠ 0) :
    ∃ L : Submodule ℝ V, Function.Bijective (frameChartDeriv u' J₀ L.subtypeL) := by
  set v := u' 1
  have hJ : (J₀ : V →ₗ[ℝ] V).comp (J₀ : V →ₗ[ℝ] V) = -LinearMap.id := by
    ext x; simp [hJ₀]
  have hJinj : Function.Injective J₀ := fun x y hxy ↦ by
    simpa [hJ₀] using congrArg J₀ hxy
  -- A maximal totally real subspace `L₁` through `v`, and a complement `L` of `ℝ v` in it.
  obtain ⟨L₁, hvL₁, hL₁⟩ := exists_mem_isMaximalTotallyReal hJ v
  obtain ⟨C, hC⟩ := (ℝ ∙ (⟨v, hvL₁⟩ : L₁)).exists_isCompl
  set L := C.map L₁.subtype
  have hLL₁ : L ≤ L₁ := by simp [L, Submodule.map_subtype_le]
  -- The frame `A (r, x) = r v + x` parametrizes `L₁` injectively.
  set A : (ℝ × L) →ₗ[ℝ] V := (LinearMap.toSpanSingleton ℝ V v).coprod L.subtype
  have hA : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨r, x, hx⟩ h
    obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.1 hx
    have h' : (⟨r • v, L₁.smul_mem r hvL₁⟩ : L₁) = -c := by
      ext; simpa [A, eq_neg_iff_add_eq_zero] using h
    have hmem : c ∈ (ℝ ∙ (⟨v, hvL₁⟩ : L₁)) := by
      rw [← neg_neg c, ← h']
      exact Submodule.neg_mem _ (Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _))
    have hc0 : c = 0 := Submodule.disjoint_def.1 hC.disjoint c hmem hc
    subst hc0
    have hr : r • v = 0 := by simpa using congrArg Subtype.val h'
    simp [(smul_eq_zero.1 hr).resolve_right hu₁]
  have hrange : LinearMap.range A = L₁ := by
    apply le_antisymm
    · rintro _ ⟨⟨r, x⟩, rfl⟩
      exact L₁.add_mem (L₁.smul_mem r hvL₁) (hLL₁ x.2)
    · intro y hy
      obtain ⟨s, hs, c, hcC, hsc⟩ := Submodule.mem_sup.1 (hC.sup_eq_top ▸ Submodule.mem_top :
        (⟨y, hy⟩ : L₁) ∈ (ℝ ∙ (⟨v, hvL₁⟩ : L₁)) ⊔ C)
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hs
      refine ⟨(r, ⟨c, Submodule.mem_map_of_mem hcC⟩), ?_⟩
      simpa [A] using congrArg Subtype.val hsc
  have hJA : Function.Injective ((J₀ : V →ₗ[ℝ] V).comp A) := hJinj.comp hA
  have hbij := (bijective_coprod_iff_isMaximalTotallyReal_range hA hJA).2 (hrange ▸ hL₁)
  -- The linear model is the doubled frame `A ⊕ J₀ A` after regrouping `ℂ × L × L` as
  -- `(ℝ × L) × (ℝ × L)` by real and imaginary parts.
  set σ : (ℂ × L × L) ≃ (ℝ × L) × (ℝ × L) :=
    { toFun := fun w ↦ ((w.1.re, w.2.1), (w.1.im, w.2.2))
      invFun := fun p ↦ (⟨p.1.1, p.2.1⟩, p.1.2, p.2.2)
      left_inv := fun w ↦ by simp
      right_inv := fun p ↦ by simp }
  have hcomp :
      ⇑(frameChartDeriv u' J₀ L.subtypeL) = (A.coprod ((J₀ : V →ₗ[ℝ] V).comp A)) ∘ σ := by
    funext w
    have hI : u' I = J₀ v := by simpa [v] using hu 1
    simp only [frameChartDeriv_apply, Submodule.coe_subtype,
      Function.comp_apply, LinearMap.coprod_apply, LinearMap.coe_comp, ContinuousLinearMap.coe_coe,
      LinearMap.toSpanSingleton_apply, σ, Equiv.coe_fn_mk, A, map_add, map_smul,
      apply_eq_re_smul_add_im_smul u' w.1, hI]
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
