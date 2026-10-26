/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
import TauCeti.Analysis.Calculus.DifferentialForm.Poincare
import TauCeti.Analysis.Calculus.Moser
import TauCeti.Dynamics.Flow.RestPoint
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Darboux's theorem

Let `ω` be a closed differential two-form on an open subset `W` of a finite-dimensional real
normed space `V`, of class `C^r` with `r ≥ 1`, and nondegenerate at a point `x₀ ∈ W`. **Darboux's
theorem** says that near `x₀` the form `ω` is constant in suitable coordinates: there is a `C^r`
diffeomorphism `ψ` of `V` fixing `x₀` with `ψ^* ω = ω(x₀)` on a neighbourhood of `x₀`
(`TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq`). Its inverse is
therefore a chart around `x₀` in which `ω` is the constant form `ω(x₀)`. Choosing a symplectic
basis of the constant nondegenerate form `ω(x₀)` is a separate linear step, which turns these
coordinates into the classical ones with `ω = ∑ dxᵢ ∧ dyᵢ`.

The proof is Moser's deformation argument. The Poincaré lemma on a ball around `x₀` gives a
one-form `α` with `dα = ω - ω(x₀)` and `α(x₀) = 0`. Along the straight-line family
`ωₜ = (1 - t) ω(x₀) + t ω`, which is nondegenerate near `x₀` for all `t ∈ [0, 1]`, the Moser
field `Xₜ` is defined by `ι_{Xₜ} ωₜ = -α` (`TauCeti.exists_contDiffOn_moserField`). It vanishes at
`x₀`, so its time-dependent flow `ψₜ` exists near `x₀` up to time one
(`TauCeti.exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn`), and Moser's identity
(`TauCeti.compContinuousLinearMap_fderiv_eq_of_curryLeft_eq_neg`) gives `ψ₁^* ω = ψ₀^* ω(x₀) =
ω(x₀)` near `x₀`.

Forms are Mathlib's continuous alternating maps, `V [⋀^Fin 2]→L[ℝ] ℝ`, with Mathlib's exterior
derivative `extDeriv`, and the pullback of `ω` along `ψ` at `x` is
`(ω (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x)`. Nondegeneracy of `ω(x₀)` is the statement that
no nonzero vector `v` has `ω(x₀)(v, w) = 0` for every `w`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (Moser's argument and Darboux's theorem).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 22.13 (Darboux's theorem).
-/

public section

open Set Filter Topology Metric
open scoped Manifold

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The Moser data of a closed two-form.** For a closed `C^r` two-form `ω` (`r ≥ 1`) on an
open set `W`, nondegenerate at `x₀ ∈ W`, there are a one-form `α` with `dα = ω - ω(x₀)` near
`x₀`, an open neighbourhood `U ⊆ W` of `x₀`, an open set of times `T ⊇ [0, 1]` and a jointly `C^r`
field `X` on `T × U`, vanishing at `x₀`, with `ι_{X(t, y)} ((1 - t) ω(x₀) + t ω(y)) = -α(y)`. -/
private theorem exists_moserData {ω : V → V [⋀^Fin 2]→L[ℝ] ℝ} {W : Set V} {x₀ : V} {r : ℕ∞}
    (hr : 1 ≤ r) (hW : IsOpen W) (hx₀ : x₀ ∈ W) (hω : ContDiffOn ℝ r ω W)
    (hdω : ∀ x ∈ W, extDeriv ω x = 0) (hnd : ∀ v, (∀ w, ω x₀ ![v, w] = 0) → v = 0) :
    ∃ (α : V → V [⋀^Fin 1]→L[ℝ] ℝ) (T : Set ℝ) (U : Set V) (X : ℝ × V → V),
      IsOpen T ∧ IsOpen U ∧ Icc 0 1 ⊆ T ∧ x₀ ∈ U ∧ U ⊆ W ∧ ContDiffOn ℝ r X (T ×ˢ U) ∧
      (∀ t ∈ T, X (t, x₀) = 0) ∧ (∀ y ∈ U, extDeriv α y = ω y - ω x₀) ∧
      ∀ p ∈ T ×ˢ U, ((1 - p.1) • ω x₀ + p.1 • ω p.2).curryLeft (X p) = -α p.2 := by
  -- A primitive of `ω - ω x₀` on a ball, vanishing at `x₀` (the Poincaré lemma).
  obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.1 hW x₀ hx₀
  have hηc : ∀ y ∈ ball x₀ ρ, extDeriv (fun x ↦ ω x - ω x₀) y = 0 := fun y hy ↦ by
    simpa only [extDeriv, fderiv_sub_const] using hdω y (hρW hy)
  obtain ⟨α, hα, hα₀, hdα⟩ :=
    ((convex_ball x₀ ρ).starConvex (mem_ball_self hρ)).exists_contDiffOn_forall_extDeriv_eq
      isOpen_ball hr ((hω.mono hρW).sub contDiffOn_const) hηc
  -- The forms as bilinear maps, as the Moser field equation takes them.
  let e : (V [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] V →L[ℝ] ℝ :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ)
      (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have he (a : V [⋀^Fin 1]→L[ℝ] ℝ) (m : Fin 1 → V) : e a (m 0) = a m := by
    simp only [e, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply,
      ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply]
    congr 1
    funext i
    rw [Subsingleton.elim i 0]
  let B : V → V →L[ℝ] V →L[ℝ] ℝ := fun y ↦ e ∘L (ω y).curryLeft
  have hBapp (y v w : V) : B y v w = ω y ![v, w] := by
    simpa [B] using he ((ω y).curryLeft v) ![w]
  have hL : (B x₀).IsInvertible := ContinuousLinearMap.isInvertible_of_injective <|
    (injective_iff_map_eq_zero (B x₀)).2 fun v hv ↦
      hnd v fun w ↦ by rw [← hBapp, hv]; rfl
  have hB : ContDiffOn ℝ r B (ball x₀ ρ) := by
    -- The source and target are given explicitly, so that their normed instances are used.
    have hc := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := r) (E := V [⋀^Fin 2]→L[ℝ] ℝ)
      (F := V →L[ℝ] V [⋀^Fin 1]→L[ℝ] ℝ)
      (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := V) (F := ℝ)
        (n := 1)).toContinuousLinearMap
    exact contDiffOn_const.clm_comp (hc.comp_contDiffOn (hω.mono hρW))
  obtain ⟨T, U, X, hT, hU, hTI, hxU, hUB, hX, hXeq⟩ := exists_contDiffOn_moserField hL
    isOpen_ball (mem_ball_self hρ) hB rfl (e.contDiff.comp_contDiffOn hα)
  refine ⟨α, T, U, X, hT, hU, hTI, hxU, hUB.trans hρW, hX,
    fun t ht ↦ ((hXeq (t, x₀) ⟨ht, hxU⟩ 0).1 fun w ↦ by simp [hα₀]).symm,
    fun y hy ↦ hdα y (hUB hy), fun p hp ↦ ?_⟩
  -- Read the bilinear Moser equation back as an equation of one-forms.
  have hp' := (hXeq p hp (X p)).2 rfl
  ext m
  have hm : m = ![m 0] := by
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  rw [hm, ContinuousAlternatingMap.curryLeft_apply_apply, ContinuousAlternatingMap.neg_apply,
    ← he (α p.2) ![m 0]]
  simpa [hBapp] using hp' (m 0)

/-- **Darboux's theorem.** A closed `C^r` two-form `ω` (`r ≥ 1`) on an open subset of a
finite-dimensional real normed space, nondegenerate at `x₀`, is constant in suitable coordinates
near `x₀`: there is a `C^r` diffeomorphism `ψ` of the space fixing `x₀` such that the pullback
`ψ^* ω` equals the constant form `ω(x₀)` on a neighbourhood of `x₀`. -/
theorem exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq
    {ω : V → V [⋀^Fin 2]→L[ℝ] ℝ} {W : Set V} {x₀ : V} {r : ℕ∞} (hr : 1 ≤ r) (hW : IsOpen W)
    (hx₀ : x₀ ∈ W) (hω : ContDiffOn ℝ r ω W) (hdω : ∀ x ∈ W, extDeriv ω x = 0)
    (hnd : ∀ v, (∀ w, ω x₀ ![v, w] = 0) → v = 0) :
    ∃ ψ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ V, ψ x₀ = x₀ ∧
      ∀ᶠ x in 𝓝 x₀, (ω (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x) = ω x₀ := by
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by
    have : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
    exact (lt_of_lt_of_le zero_lt_one this).ne'
  obtain ⟨α, T, U, X, hT, hU, hTI, hxU, hUW, hX, hX₀, hdα, hXeq⟩ :=
    exists_moserData hr hW hx₀ hω hdω hnd
  -- The time-dependent flow of the Moser field.
  obtain ⟨ψ, ψ', hψ, hψ', hψl, hψr, hψ0, hψx₀, hev⟩ :=
    exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn (X := fun t y ↦ X (t, y)) hr hT hU
      hTI hxU hX hX₀
  refine ⟨⟨⟨ψ 1, ψ', hψl, hψr⟩, hψ.contMDiff, hψ'.contMDiff⟩, hψx₀ 1, ?_⟩
  -- Moser's identity along the flow: `ψ₁^* ω = ψ₀^* ω(x₀) = ω(x₀)`.
  filter_upwards [hev] with x hx
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ψ t x ∈ U := (hx t ht).1
  have h := compContinuousLinearMap_fderiv_eq_of_curryLeft_eq_neg (ω₀ := fun _ ↦ ω x₀) (ω₁ := ω)
    (α := α) (ψ := ψ) (X := fun t y ↦ X (t, y)) (x := x)
    (fun t _ ↦ differentiableAt_const _)
    (fun t ht ↦ (hω.differentiableOn hr0).differentiableAt (hW.mem_nhds (hUW (hmem t ht))))
    (fun t _ ↦ by
      rw [extDeriv, fderiv_const_apply,
        ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_zero])
    (fun t ht ↦ hdω _ (hUW (hmem t ht))) (fun t ht ↦ hdα _ (hmem t ht))
    (fun t ht ↦ Filter.mem_of_superset (hU.mem_nhds (hmem t ht)) fun y hy ↦
      hXeq (t, y) ⟨hTI ht, hy⟩)
    (fun t ht ↦ ((hX.differentiableOn hr0).differentiableAt
      ((hT.prod hU).mem_nhds ⟨hTI ht, hmem t ht⟩)).comp (ψ t x)
        ((differentiableAt_const t).prodMk differentiableAt_id))
    (fun t ht ↦ (hx t ht).2.1) (fun t ht ↦ (hx t ht).2.2)
  rw [hψ0, fderiv_id] at h
  refine h.trans ?_
  ext v
  simp

end TauCeti
