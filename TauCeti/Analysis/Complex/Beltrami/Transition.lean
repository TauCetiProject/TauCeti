/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Transition maps between planar isothermal charts

Let `J : ℂ → ℂ →L[ℝ] ℂ` be a field of real-linear endomorphisms of the plane, for instance an
almost complex structure of finite regularity. A planar chart `e : OpenPartialHomeomorph ℂ ℂ` is
*isothermal* for `J` when `j = i` in it: at every point `z` of its source, `e` is real
differentiable and its derivative carries `J z` to multiplication by `I`.

If `e₁` and `e₂` are two such charts and the derivative of `e₁` is invertible, then the
derivative of the transition map `e₁.symm.trans e₂` is `de₂ ∘ de₁⁻¹`, which commutes with
multiplication by `I`. This is the Cauchy–Riemann equation, so the transition map is holomorphic.
No regularity of `J` is needed, and neither is `J z ∘ J z = -1`.

Consequently `e₂ = (e₁.symm.trans e₂) ∘ e₁` on the common source has the regularity of `e₁`: if
`e₁` is `C^n`, so is `e₂` there. If around every point of the source of `e` there is, for each
`m`, an isothermal chart of class `C^m` with invertible derivative, then `e` itself is smooth.
This is how the isothermal chart built for a smooth structure at the lowest regularity is shown
to be smooth.

## Main declarations

* `TauCeti.Beltrami.differentiableOn_symm_trans_of_fderiv_comp`: the transition map between two
  isothermal charts for `J` is holomorphic on its source when the first chart has invertible
  derivative.
* `TauCeti.Beltrami.contDiffOn_inter_of_fderiv_comp`: a second isothermal chart has, on the
  common source, the regularity `C^n` of the first.
* `TauCeti.Beltrami.contDiffOn_infty_of_fderiv_comp`: an isothermal chart that is compared, near
  every point, with isothermal charts of every finite regularity is smooth.

## References

* Dusa McDuff and Dietmar Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Appendix E.
-/

public section

open Complex Set
open scoped ContDiff

namespace TauCeti.Beltrami

variable {J : ℂ → ℂ →L[ℝ] ℂ} {e e₁ e₂ : OpenPartialHomeomorph ℂ ℂ} {w : ℂ}

/-- **Cauchy–Riemann equation for a transition map, pointwise.** Let `z = e₁.symm w`. If `e₂` is
real differentiable at `z`, the derivatives of `e₁` and `e₂` carry `J z` to multiplication by
`I`, and the derivative of `e₁` at `z` is invertible, then the transition map `e₁.symm.trans e₂` is
complex differentiable at `w`. -/
theorem differentiableAt_symm_trans_of_fderiv_comp (hw : w ∈ (e₁.symm.trans e₂).source)
    (hd₂ : DifferentiableAt ℝ e₂ (e₁.symm w))
    (hinv : (fderiv ℝ e₁ (e₁.symm w)).IsInvertible)
    (hJ₁ : ∀ v, fderiv ℝ e₁ (e₁.symm w) (J (e₁.symm w) v) = I * fderiv ℝ e₁ (e₁.symm w) v)
    (hJ₂ : ∀ v, fderiv ℝ e₂ (e₁.symm w) (J (e₁.symm w) v) = I * fderiv ℝ e₂ (e₁.symm w) v) :
    DifferentiableAt ℂ (e₁.symm.trans e₂) w := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hw
  have hd₁ := differentiableAt_of_isInvertible_fderiv hinv
  obtain ⟨L, hL⟩ := hinv
  set z := e₁.symm w
  have hsymm : HasFDerivAt e₁.symm (L.symm : ℂ →L[ℝ] ℂ) w :=
    e₁.hasFDerivAt_symm hw.1 (hL ▸ hd₁.hasFDerivAt)
  have hD := hd₂.hasFDerivAt.comp w hsymm
  refine (hD.complexOfReal_hasFDerivAt ?_).differentiableAt
  -- `L` carries `J z` to multiplication by `I`, so `L⁻¹` carries `I` to `J z`.
  have hLJ' : ∀ v, L (J z v) = I * L v := by simpa [← hL] using hJ₁
  have hLJ : L.symm I = J z (L.symm 1) := L.injective (by simp [hLJ'])
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, smul_eq_mul]
  rw [hLJ, hJ₂]

/-- **Transition maps between isothermal charts are holomorphic.** If `e₂` is real
differentiable on its source, the derivatives of `e₁` and `e₂` carry `J` to multiplication by `I`
on their sources, and the derivative of `e₁` is invertible on its source, then the transition
map `e₁.symm.trans e₂` satisfies the Cauchy–Riemann equation, so it is holomorphic on its
source. -/
theorem differentiableOn_symm_trans_of_fderiv_comp (hd₂ : DifferentiableOn ℝ e₂ e₂.source)
    (hinv : ∀ z ∈ e₁.source, (fderiv ℝ e₁ z).IsInvertible)
    (hJ₁ : ∀ z ∈ e₁.source, ∀ v, fderiv ℝ e₁ z (J z v) = I * fderiv ℝ e₁ z v)
    (hJ₂ : ∀ z ∈ e₂.source, ∀ v, fderiv ℝ e₂ z (J z v) = I * fderiv ℝ e₂ z v) :
    DifferentiableOn ℂ (e₁.symm.trans e₂) (e₁.symm.trans e₂).source := by
  intro w hw
  have hw' := hw
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hw'
  have h₁ : e₁.symm w ∈ e₁.source := e₁.map_target hw'.1
  exact (differentiableAt_symm_trans_of_fderiv_comp hw
    (hd₂.differentiableAt (e₂.open_source.mem_nhds hw'.2)) (hinv _ h₁) (hJ₁ _ h₁)
    (hJ₂ _ hw'.2)).differentiableWithinAt

/-- **Regularity passes between isothermal charts.** Under the hypotheses of
`differentiableOn_symm_trans_of_fderiv_comp`, if `e₁` is of class `C^n` on its source, then `e₂`
is of class `C^n` on the common source: there `e₂` is the holomorphic transition map composed
with `e₁`. -/
theorem contDiffOn_inter_of_fderiv_comp {n : WithTop ℕ∞} (hc₁ : ContDiffOn ℝ n e₁ e₁.source)
    (hd₂ : DifferentiableOn ℝ e₂ e₂.source)
    (hinv : ∀ z ∈ e₁.source, (fderiv ℝ e₁ z).IsInvertible)
    (hJ₁ : ∀ z ∈ e₁.source, ∀ v, fderiv ℝ e₁ z (J z v) = I * fderiv ℝ e₁ z v)
    (hJ₂ : ∀ z ∈ e₂.source, ∀ v, fderiv ℝ e₂ z (J z v) = I * fderiv ℝ e₂ z v) :
    ContDiffOn ℝ n e₂ (e₁.source ∩ e₂.source) := by
  have hT : ContDiffOn ℝ n (e₁.symm.trans e₂) (e₁.symm.trans e₂).source :=
    ((differentiableOn_symm_trans_of_fderiv_comp hd₂ hinv hJ₁ hJ₂).contDiffOn
      (e₁.symm.trans e₂).open_source).restrict_scalars ℝ
  have hmaps : MapsTo e₁ (e₁.source ∩ e₂.source) (e₁.symm.trans e₂).source := by
    intro z hz
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    exact ⟨e₁.map_source hz.1, by rw [mem_preimage, e₁.left_inv hz.1]; exact hz.2⟩
  refine (hT.comp (hc₁.mono inter_subset_left) hmaps).congr fun z hz ↦ ?_
  simp [e₁.left_inv hz.1]

/-- **Smooth bootstrap for isothermal charts.** Let `e` be an isothermal chart for `J`, real
differentiable on its source. Suppose that around every point of its source there is, for every
`m : ℕ`, an isothermal chart for `J` of class `C^m` with invertible derivative. Then `e` is
smooth on its source. -/
theorem contDiffOn_infty_of_fderiv_comp (hd : DifferentiableOn ℝ e e.source)
    (hJ : ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (J z v) = I * fderiv ℝ e z v)
    (h : ∀ z ∈ e.source, ∀ m : ℕ, ∃ e' : OpenPartialHomeomorph ℂ ℂ, z ∈ e'.source ∧
      ContDiffOn ℝ m e' e'.source ∧ (∀ y ∈ e'.source, (fderiv ℝ e' y).IsInvertible) ∧
      ∀ y ∈ e'.source, ∀ v, fderiv ℝ e' y (J y v) = I * fderiv ℝ e' y v) :
    ContDiffOn ℝ ∞ e e.source := by
  refine contDiffOn_infty.2 fun m ↦ contDiffOn_of_locally_contDiffOn fun z hz ↦ ?_
  obtain ⟨e', hz', hc', hinv', hJ'⟩ := h z hz m
  refine ⟨e'.source, e'.open_source, hz', ?_⟩
  rw [inter_comm]
  exact contDiffOn_inter_of_fderiv_comp hc' hd hinv' hJ' hJ

end TauCeti.Beltrami
