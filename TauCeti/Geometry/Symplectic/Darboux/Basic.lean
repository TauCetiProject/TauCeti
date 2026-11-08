/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Analysis.Calculus.DifferentialForm.Poincare
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Analysis.Calculus.Moser
import TauCeti.Dynamics.Flow.RestPoint
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
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

The proof is Moser's deformation argument, which this file states in its local form
(`TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_of_extDeriv_eq`). Let
`ω₀`, `ω₁` be closed two-forms near `x₀` which agree and are nondegenerate at `x₀`, and let `α` be
a one-form with `dα = ω₁ - ω₀` and `α(x₀) = 0`. Along the straight-line family
`ωₜ = (1 - t) ω₀ + t ω₁`, which is nondegenerate near `x₀` for all `t ∈ [0, 1]`, the Moser field
`Xₜ` is defined by `ι_{Xₜ} ωₜ = -α` (`TauCeti.exists_contDiffOn_moserField`). It vanishes wherever
`α` does, in particular at `x₀`, so its time-dependent flow `ψₜ` exists near `x₀` up to time one and
fixes the zeros of `α` (`TauCeti.exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn`), and
Moser's identity (`TauCeti.compContinuousLinearMap_fderiv_eq_of_curryLeft_eq_neg`) gives
`ψ₁^* ω₁ = ψ₀^* ω₀ = ω₀` near `x₀`. For Darboux's theorem, `ω₀` is the constant form `ω(x₀)`,
`ω₁ = ω`, and the Poincaré lemma on a ball around `x₀` supplies `α`. Choosing `α` to vanish along
a submanifold instead gives the relative Darboux theorem, in
`TauCeti.Geometry.Symplectic.Darboux.Relative`.

Forms are Mathlib's continuous alternating maps, `V [⋀^Fin 2]→L[ℝ] ℝ`, with Mathlib's exterior
derivative `extDeriv`, and the pullback of `ω` along `ψ` at `x` is
`(ω (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x)`. Nondegeneracy of `ω(x₀)` is the statement that
no nonzero vector `v` has `ω(x₀)(v, w) = 0` for every `w`.

A pullback identity proved in other coordinates transfers back: if a diffeomorphism `Ψ` pulls
`Θ^* ω₁` back to `Θ^* ω₀` for a partial diffeomorphism `Θ`, then the conjugate `Θ ∘ Ψ ∘ Θ⁻¹` pulls
`ω₁` back to `ω₀`
(`TauCeti.exists_partialDiffeomorph_compContinuousLinearMap_fderiv_eq_of_conj`).

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

/-- **Moser's lemma**, local form. Let `ω₀`, `ω₁` be closed `C^r` two-forms (`r ≥ 1`) on an open
subset `W` of a finite-dimensional real normed space, with `ω₁ - ω₀ = dα` on `W` for a `C^r`
one-form `α` vanishing at `x₀ ∈ W`. If `ω₀` and `ω₁` agree at `x₀` and are nondegenerate there,
then some `C^r` diffeomorphism `ψ` of the space pulls `ω₁` back to `ω₀` on a neighbourhood of `x₀`.
Moreover `ψ` fixes, near `x₀`, every point at which `α` vanishes; in particular `ψ x₀ = x₀`. -/
theorem exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_of_extDeriv_eq
    {ω₀ ω₁ : V → V [⋀^Fin 2]→L[ℝ] ℝ} {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} {W : Set V} {x₀ : V}
    {r : ℕ∞} (hr : 1 ≤ r) (hW : IsOpen W) (hx₀ : x₀ ∈ W) (hω₀ : ContDiffOn ℝ r ω₀ W)
    (hω₁ : ContDiffOn ℝ r ω₁ W) (hα : ContDiffOn ℝ r α W) (hdω₀ : ∀ x ∈ W, extDeriv ω₀ x = 0)
    (hdω₁ : ∀ x ∈ W, extDeriv ω₁ x = 0) (hdα : ∀ x ∈ W, extDeriv α x = ω₁ x - ω₀ x)
    (hα₀ : α x₀ = 0) (heq : ω₁ x₀ = ω₀ x₀) (hnd : ∀ v, (∀ w, ω₀ x₀ ![v, w] = 0) → v = 0) :
    ∃ ψ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ V, (∀ᶠ x in 𝓝 x₀, α x = 0 → ψ x = x) ∧
      ∀ᶠ x in 𝓝 x₀, (ω₁ (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x) = ω₀ x := by
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by
    have : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
    exact (lt_of_lt_of_le zero_lt_one this).ne'
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
  let B₀ : V → V →L[ℝ] V →L[ℝ] ℝ := fun y ↦ ContinuousAlternatingMap.flatL ℝ V ℝ (ω₀ y)
  let B₁ : V → V →L[ℝ] V →L[ℝ] ℝ := fun y ↦ ContinuousAlternatingMap.flatL ℝ V ℝ (ω₁ y)
  have hL : (B₀ x₀).IsInvertible := ContinuousLinearMap.isInvertible_of_injective <|
    (injective_iff_map_eq_zero (B₀ x₀)).2 fun v hv ↦
      hnd v fun w ↦ by rw [← ContinuousAlternatingMap.flatL_apply_apply, hv]; rfl
  -- The source and target of `flatL` are given explicitly, so that their normed instances are used.
  have hflat := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := r) (E := V [⋀^Fin 2]→L[ℝ] ℝ)
    (F := V →L[ℝ] V →L[ℝ] ℝ) (ContinuousAlternatingMap.flatL ℝ V ℝ)
  obtain ⟨T, U, X, hT, hU, hTI, hxU, hUW, hX, hXeq⟩ := exists_contDiffOn_moserField hL hW hx₀
    (hflat.comp_contDiffOn hω₀) (hflat.comp_contDiffOn hω₁) rfl (congrArg _ heq)
    (e.contDiff.comp_contDiffOn hα)
  -- The Moser field vanishes wherever `α` does.
  have hXα (t : ℝ) (ht : t ∈ T) (y : V) (hy : y ∈ U) (hαy : α y = 0) : X (t, y) = 0 :=
    ((hXeq (t, y) ⟨ht, hy⟩ 0).1 fun w ↦ by simp [hαy]).symm
  -- Read the bilinear Moser equation back as an equation of one-forms.
  have hXω (p : ℝ × V) (hp : p ∈ T ×ˢ U) :
      ((1 - p.1) • ω₀ p.2 + p.1 • ω₁ p.2).curryLeft (X p) = -α p.2 := by
    have hp' := (hXeq p hp (X p)).2 rfl
    ext m
    have hm : m = ![m 0] := by
      funext i
      rw [Subsingleton.elim i 0]
      rfl
    rw [hm, ContinuousAlternatingMap.curryLeft_apply_apply, ContinuousAlternatingMap.neg_apply,
      ← he (α p.2) ![m 0]]
    simpa [B₀, B₁] using hp' (m 0)
  -- The time-dependent flow of the Moser field.
  obtain ⟨ψ, ψ', hψ, hψ', hψl, hψr, hψ0, hψfix, hev⟩ :=
    exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn (X := fun t y ↦ X (t, y)) hr hT hU
      hTI hxU hX fun t ht ↦ hXα t ht x₀ hxU hα₀
  refine ⟨⟨⟨ψ 1, ψ', hψl, hψr⟩, hψ.contMDiff, hψ'.contMDiff⟩, ?_, ?_⟩
  · filter_upwards [hU.mem_nhds hxU] with y hy hαy
    exact hψfix y (fun t ht ↦ hXα t ht y hy hαy) 1
  -- Moser's identity along the flow: `ψ₁^* ω₁ = ψ₀^* ω₀ = ω₀`.
  filter_upwards [hev] with x hx
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ψ t x ∈ U := (hx t ht).1
  have h := compContinuousLinearMap_fderiv_eq_of_curryLeft_eq_neg (ω₀ := ω₀) (ω₁ := ω₁)
    (α := α) (ψ := ψ) (X := fun t y ↦ X (t, y)) (x := x)
    (fun t ht ↦ (hω₀.differentiableOn hr0).differentiableAt (hW.mem_nhds (hUW (hmem t ht))))
    (fun t ht ↦ (hω₁.differentiableOn hr0).differentiableAt (hW.mem_nhds (hUW (hmem t ht))))
    (fun t ht ↦ hdω₀ _ (hUW (hmem t ht))) (fun t ht ↦ hdω₁ _ (hUW (hmem t ht)))
    (fun t ht ↦ hdα _ (hUW (hmem t ht)))
    (fun t ht ↦ Filter.mem_of_superset (hU.mem_nhds (hmem t ht)) fun y hy ↦
      hXω (t, y) ⟨hTI ht, hy⟩)
    (fun t ht ↦ ((hX.differentiableOn hr0).differentiableAt
      ((hT.prod hU).mem_nhds ⟨hTI ht, hmem t ht⟩)).comp (ψ t x)
        ((differentiableAt_const t).prodMk differentiableAt_id))
    (fun t ht ↦ (hx t ht).2.1) (fun t ht ↦ (hx t ht).2.2)
  rw [hψ0, fderiv_id] at h
  refine h.trans ?_
  ext v
  simp

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
  -- A primitive of `ω - ω x₀` on a ball, vanishing at `x₀` (the Poincaré lemma).
  obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.1 hW x₀ hx₀
  have hηc : ∀ y ∈ ball x₀ ρ, extDeriv (fun x ↦ ω x - ω x₀) y = 0 := fun y hy ↦ by
    simpa only [extDeriv, fderiv_sub_const] using hdω y (hρW hy)
  obtain ⟨α, hα, hα₀, hdα⟩ :=
    ((convex_ball x₀ ρ).starConvex (mem_ball_self hρ)).exists_contDiffOn_forall_extDeriv_eq
      isOpen_ball hr ((hω.mono hρW).sub contDiffOn_const) hηc
  -- Moser's lemma for the constant form `ω x₀` and `ω`.
  obtain ⟨ψ, hfix, hψ⟩ :=
    exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_of_extDeriv_eq
      (ω₀ := fun _ ↦ ω x₀) hr isOpen_ball (mem_ball_self hρ) contDiffOn_const (hω.mono hρW) hα
      (fun x _ ↦ by
        rw [extDeriv, fderiv_const_apply,
          ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_zero])
      (fun x hx ↦ hdω x (hρW hx)) hdα hα₀ rfl hnd
  exact ⟨ψ, hfix.self_of_nhds hα₀, hψ⟩

/-- **Darboux's theorem, centred inverse form.** In the situation of
`exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq`, subtracting `x₀` from the inverse
of the diffeomorphism gives a `C^r` diffeomorphism `Φ` of the space with `Φ x₀ = 0` such that the
form `ω` is, on an open neighbourhood `V₀ ⊆ W` of `x₀`, the pullback of the constant form `ω(x₀)`
by `Φ`. -/
theorem exists_diffeomorph_centered_forall_mem_eq_compContinuousLinearMap_fderiv
    {ω : V → V [⋀^Fin 2]→L[ℝ] ℝ} {W : Set V} {x₀ : V} {r : ℕ∞} (hr : 1 ≤ r) (hW : IsOpen W)
    (hx₀ : x₀ ∈ W) (hω : ContDiffOn ℝ r ω W) (hdω : ∀ x ∈ W, extDeriv ω x = 0)
    (hnd : ∀ v, (∀ w, ω x₀ ![v, w] = 0) → v = 0) :
    ∃ (Φ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ V) (V₀ : Set V), Φ x₀ = 0 ∧ IsOpen V₀ ∧ x₀ ∈ V₀ ∧
      V₀ ⊆ W ∧ ∀ y ∈ V₀, ω y = (ω x₀).compContinuousLinearMap (fderiv ℝ Φ y) := by
  obtain ⟨ψ, hψx₀, hev⟩ :=
    exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq hr hW hx₀ hω hdω hnd
  have hψsymm : ψ.symm x₀ = x₀ := ψ.symm_apply_eq.2 hψx₀.symm
  have hnhds : {y : V | (ω (ψ (ψ.symm y))).compContinuousLinearMap (fderiv ℝ ψ (ψ.symm y)) =
      ω x₀} ∩ W ∈ 𝓝 x₀ := by
    refine Filter.inter_mem ?_ (hW.mem_nhds hx₀)
    have hcont : ContinuousAt ψ.symm x₀ := ψ.symm.continuous.continuousAt
    rw [ContinuousAt, hψsymm] at hcont
    exact hcont hev
  obtain ⟨V₀, hV₀_sub, hV₀_open, hx₀V₀⟩ := _root_.mem_nhds_iff.1 hnhds
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by
    have : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
    exact (lt_of_lt_of_le zero_lt_one this).ne'
  let Φ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ V :=
    ψ.symm.trans (Diffeomorph.smulAdd r (1 : ℝ) (-x₀) one_ne_zero)
  have hΦ_coe : ⇑Φ = fun y ↦ ψ.symm y - x₀ := by
    ext y
    simp [Φ, sub_eq_add_neg]
  refine ⟨Φ, V₀, by rw [hΦ_coe]; simp [hψsymm], hV₀_open, hx₀V₀, fun y hy ↦ (hV₀_sub hy).2,
    fun y hy ↦ ?_⟩
  have hzy : (ω y).compContinuousLinearMap (fderiv ℝ ψ (ψ.symm y)) = ω x₀ := by
    have := (hV₀_sub hy).1
    simpa only [mem_ofPred_eq, ψ.apply_symm_apply] using this
  rw [hΦ_coe, fderiv_sub_const, ← hzy]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  exact (ψ.fderiv_apply_fderiv_symm_apply hr0 y (v i)).symm

section Conj

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Conjugating a pullback identity by a coordinate change.** Let `Θ` be a `C^r` partial
diffeomorphism from `F` to `E`, and let `Ψ` be a diffeomorphism of `F` which maps an open set
`O ⊆ Θ.source` into `Θ.source` and pulls `Θ^* ω₁` back to `Θ^* ω₀` on `O`. Then the conjugate
`Θ ∘ Ψ ∘ Θ⁻¹`, defined on `Θ '' O`, is a `C^r` partial diffeomorphism of `E` which pulls `ω₁` back
to `ω₀` on its source. -/
theorem exists_partialDiffeomorph_compContinuousLinearMap_fderiv_eq_of_conj
    {ω₀ ω₁ : E → E [⋀^Fin 2]→L[ℝ] ℝ} {r : ℕ∞} (hr : 1 ≤ r)
    (Θ : OpenPartialHomeomorph F E) (hΘ : ContDiffOn ℝ r Θ Θ.source)
    (hΘsymm : ContDiffOn ℝ r Θ.symm Θ.target) (Ψ : F ≃ₘ^r⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ F) {O : Set F}
    (hO : IsOpen O) (hOΘ : O ⊆ Θ.source) (hΨO : MapsTo Ψ O Θ.source)
    (hΨ : ∀ z ∈ O,
      ((ω₁ (Θ (Ψ z))).compContinuousLinearMap (fderiv ℝ Θ (Ψ z))).compContinuousLinearMap
        (fderiv ℝ Ψ z) = (ω₀ (Θ z)).compContinuousLinearMap (fderiv ℝ Θ z)) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E r,
      (∀ z ∈ O, Θ z ∈ Φ.source ∧ Φ (Θ z) = Θ (Ψ z)) ∧
      ∀ x ∈ Φ.source, (ω₁ (Φ x)).compContinuousLinearMap (fderiv ℝ Φ x) = ω₀ x := by
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hr)).ne'
  let Θd : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, E) F E r :=
    PartialDiffeomorph.ofOpenPartialHomeomorph Θ hΘ hΘsymm
  let Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E r :=
    (Θd.restrOpen O hO).symm.trans (Ψ.toPartialDiffeomorph.trans Θd)
  have hΦeq : Φ.toPartialEquiv = ((Θ.toPartialEquiv.restr O).symm).trans
      (Ψ.toEquiv.toPartialEquiv.trans Θ.toPartialEquiv) := by
    simp only [Φ, Θd, PartialDiffeomorph.trans_toPartialEquiv,
      PartialDiffeomorph.symm_toPartialEquiv, OpenPartialHomeomorph.trans_toPartialEquiv,
      PartialDiffeomorph.restrOpen_toPartialEquiv, Diffeomorph.toPartialDiffeomorph_toPartialEquiv,
      PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv,
      PartialDiffeomorph.ofOpenPartialHomeomorph_toPartialEquiv]
  have hΦ (x : E) : Φ x = Θ (Ψ (Θ.symm x)) := by rw [hΦeq]; rfl
  have hΦsrc (x : E) : x ∈ Φ.source ↔
      x ∈ Θ.target ∧ Θ.symm x ∈ O ∧ Ψ (Θ.symm x) ∈ Θ.source := by
    rw [hΦeq]
    simp [and_assoc]
  refine ⟨Φ, fun z hz ↦ ?_, fun x hx ↦ ?_⟩
  · have hzΘ : Θ.symm (Θ z) = z := Θ.left_inv (hOΘ hz)
    rw [hΦsrc, hΦ, hzΘ]
    exact ⟨⟨Θ.map_source (hOΘ hz), hz, hΨO hz⟩, rfl⟩
  obtain ⟨hxt, hxO, hΨx⟩ := (hΦsrc x).1 hx
  have hd (w : F) (hw : w ∈ Θ.source) : HasFDerivAt Θ (fderiv ℝ Θ w) w :=
    ((hΘ.contDiffAt (Θ.open_source.mem_nhds hw)).differentiableAt hr0).hasFDerivAt
  have hdsymm : HasFDerivAt Θ.symm (fderiv ℝ Θ.symm x) x :=
    ((hΘsymm.contDiffAt (Θ.open_target.mem_nhds hxt)).differentiableAt hr0).hasFDerivAt
  have hdΨ : HasFDerivAt Ψ (fderiv ℝ Ψ (Θ.symm x)) (Θ.symm x) :=
    ((contMDiff_iff_contDiff.1 Ψ.contMDiff).differentiable hr0 _).hasFDerivAt
  -- The chain rule for `Φ = Θ ∘ Ψ ∘ Θ⁻¹`, and `dΘ ∘ dΘ⁻¹ = id` since `Θ ∘ Θ⁻¹ = id` near `x`.
  have hΦd : fderiv ℝ Φ x = (fderiv ℝ Θ (Ψ (Θ.symm x))).comp
      ((fderiv ℝ Ψ (Θ.symm x)).comp (fderiv ℝ Θ.symm x)) := by
    rw [show (Φ : E → E) = Θ ∘ Ψ ∘ Θ.symm from funext hΦ]
    exact ((hd _ hΨx).comp x (hdΨ.comp x hdsymm)).fderiv
  have hid : (fderiv ℝ Θ (Θ.symm x)).comp (fderiv ℝ Θ.symm x) = ContinuousLinearMap.id ℝ E := by
    have heq : Θ ∘ Θ.symm =ᶠ[𝓝 x] id :=
      eventually_of_mem (Θ.open_target.mem_nhds hxt) fun w hw ↦ Θ.right_inv hw
    exact (((hd _ (Θ.map_target hxt)).comp x hdsymm).congr_of_eventuallyEq heq.symm).unique
      (hasFDerivAt_id x)
  ext v
  have h := congrArg (fun A : F [⋀^Fin 2]→L[ℝ] ℝ ↦ A (fun i ↦ fderiv ℝ Θ.symm x (v i)))
    (hΨ _ hxO)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def] at h
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hΦd,
    ContinuousLinearMap.comp_apply, hΦ]
  rw [h, Θ.right_inv hxt]
  exact congrArg (ω₀ x) (funext fun i ↦ DFunLike.congr_fun hid (v i))

end Conj

end TauCeti
