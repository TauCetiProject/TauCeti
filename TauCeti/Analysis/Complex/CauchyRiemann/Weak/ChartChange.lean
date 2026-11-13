/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Invariance
public import TauCeti.Analysis.Complex.CauchyRiemann.Weak.TargetChange
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Simultaneous changes of domain and target charts for the weak Cauchy–Riemann equation

The weak equation `TauCeti.IsWeakCauchyRiemannOn p U J η u`, that is
`∂ₛu + J(z, u) ∂ₜu = η(z, u)` weakly on `U ⊆ ℂ`, is the planar coordinate form of the weak
pseudoholomorphic equation. Changing the isothermal chart on the domain by a biholomorphism `φ` and
the chart on the target by a `C¹` diffeomorphism `Ψ` replaces a solution `u` by `Ψ ∘ u ∘ φ`. This
file shows that this change is an equivalence when `J` and `η` are transported along.

For the domain change, `φ` is an open partial homeomorphism of `ℂ`, holomorphic on its source with
nonvanishing derivative `φ' = a + b i`. Its inverse is then holomorphic with derivative `1 / φ'`
(`OpenPartialHomeomorph.hasDerivAt_symm`), so the one-way invariance
`TauCeti.IsWeakCauchyRiemannOn.comp_differentiableOn` applied to `φ.symm` reverses it. The term
`η(φ z, x)` becomes `a η(φ z, x) - b J(φ z, x) η(φ z, x)`. When `J² = -1`, the map
`a + b i ↦ a - b J` is multiplicative, so the two transformations of `η` compose to multiplication
by `φ'(z) · (1 / φ'(z)) = 1`. For the target change the field becomes `Ψ_* J = dΨ ∘ J ∘ dΨ⁻¹`
(`OpenPartialHomeomorph.pullbackEnd` along `Ψ.symm`) and the term becomes `Ψ_* η`
(`VectorField.pullback` along `Ψ.symm`), as in
`TauCeti.isWeakCauchyRiemannOn_iff_openPartialHomeomorph_comp`.

The domain `U` is any subset of the source of `φ`, so half-discs are allowed.

## Main results

* `TauCeti.isWeakCauchyRiemannOn_iff_comp_differentiableOn`: invariance under a biholomorphic
  change of the domain chart, as an equivalence.
* `TauCeti.IsWeakCauchyRiemannOn.comp_chartChange`: `Ψ ∘ u ∘ φ` solves the equation for the
  transported field and term.
* `TauCeti.isWeakCauchyRiemannOn_iff_chartChange`: the combined change is an equivalence.
* Examples: the dilation `φ z = 2 z` with the real-linear target change `Ψ = conj` carries the
  solution `conj` of `∂ₛu + i ∂ₜu = 2` to the solution `z ↦ 2 z` of `∂ₛv - i ∂ₜv = 4`, and
  `conj` itself is not an admissible domain change.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Sections 2.2 and 3.1.
-/

public noncomputable section

open Complex MeasureTheory Set TopologicalSpace
open scoped ComplexConjugate

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] {p : ENNReal} {U : Set ℂ} {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V}
  {u : ℂ → V} {φ : OpenPartialHomeomorph ℂ ℂ}

/-- A holomorphic open partial homeomorphism with nonvanishing derivative has inverse derivative
`1 / φ'` on its target. -/
private theorem hasDerivAt_symm_of_differentiableOn (hφ : DifferentiableOn ℂ φ φ.source)
    (hφ' : ∀ z ∈ φ.source, deriv φ z ≠ 0) {w : ℂ} (hw : w ∈ φ.target) :
    HasDerivAt φ.symm (deriv φ (φ.symm w))⁻¹ w :=
  φ.hasDerivAt_symm hw (hφ' _ (φ.map_target hw))
    (hφ.differentiableAt (φ.open_source.mem_nhds (φ.map_target hw))).hasDerivAt

/-- **Invariance under a biholomorphic change of the domain chart.** Let `φ` be an open partial
homeomorphism of `ℂ`, holomorphic on its source with nonvanishing derivative `φ' = a + b i`, let
`U` be a subset of its source, and let `J(w, u w)` square to `-1` on the interior of `φ '' U`. Then
`u` is a weak solution on `φ '' U` if and only if `u ∘ φ` is a weak solution on `U` for the field
`J ∘ φ` and the term `a η(φ z, x) - b J(φ z, x) η(φ z, x)`. -/
theorem isWeakCauchyRiemannOn_iff_comp_differentiableOn (hφ : DifferentiableOn ℂ φ φ.source)
    (hφ' : ∀ z ∈ φ.source, deriv φ z ≠ 0) (hU : U ⊆ φ.source)
    (hJ : ∀ w ∈ interior (φ '' U), J w (u w) * J w (u w) = -1) :
    IsWeakCauchyRiemannOn p (φ '' U) J η u ↔
      IsWeakCauchyRiemannOn p U (fun z => J (φ z))
        (fun z x => (deriv φ z).re • η (φ z) x - (deriv φ z).im • J (φ z) x (η (φ z) x))
        (fun z => u (φ z)) := by
  have hUt : φ '' U ⊆ φ.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact φ.map_source (hU hz)
  constructor
  · intro h
    refine h.comp_differentiableOn φ.open_source hφ hU (φ.injOn.mono hU)
      (fun z hz => hφ' z (hU hz)) (mapsTo_image _ _) fun z hz => hJ _ ?_
    exact interior_maximal (image_mono interior_subset)
      (φ.isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hU)) ⟨z, hz, rfl⟩
  · intro h
    have hsd : ∀ {w}, w ∈ φ.target → HasDerivAt φ.symm (deriv φ (φ.symm w))⁻¹ w :=
      hasDerivAt_symm_of_differentiableOn hφ hφ'
    have h₂ := h.comp_differentiableOn φ.open_target
      (fun w hw => (hsd hw).differentiableAt.differentiableWithinAt) hUt (φ.symm.injOn.mono hUt)
      (fun w hw => by
        rw [(hsd (hUt hw)).deriv]
        exact inv_ne_zero (hφ' _ (φ.map_target (hUt hw))))
      (by
        rintro _ ⟨z, hz, rfl⟩
        rwa [φ.left_inv (hU hz)])
      (fun w hw => by
        rw [φ.right_inv (hUt (interior_subset hw))]
        exact hJ w hw)
    have h₃ := h₂.congr (v := u) fun w hw => by
      simp only [φ.right_inv (hUt hw)]
    refine (isWeakCauchyRiemannOn_congr_ae ?_ ?_).1 h₃ <;>
      refine (ae_restrict_iff' measurableSet_interior).2 (.of_forall fun w hw => ?_)
    · simp only [φ.right_inv (hUt (interior_subset hw))]
    · have hwt := hUt (interior_subset hw)
      set c := deriv φ (φ.symm w)
      have hc : c ≠ 0 := hφ' _ (φ.map_target hwt)
      have hcc : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
      have hre := congrArg Complex.re hcc
      have him := congrArg Complex.im hcc
      rw [mul_re, one_re] at hre
      rw [mul_im, one_im] at him
      have hJJ (y : V) : J w (u w) (J w (u w) y) = -y := by
        simpa using congrArg (fun T : V →L[ℝ] V => T y) (hJ w hw)
      rw [(hsd hwt).deriv, φ.right_inv hwt, map_sub, map_smul, map_smul, hJJ]
      linear_combination (norm := module) hre • η w (u w) - him • J w (u w) (η w (u w))

/-- **Combined change of domain and target charts.** Under the hypotheses of
`TauCeti.isWeakCauchyRiemannOn_iff_comp_differentiableOn`, let `Ψ` be an open partial homeomorphism
of the target, `C¹` with `C¹` inverse, whose source contains `u (φ '' U)`. If `u` is a weak solution
on `φ '' U`, then `Ψ ∘ u ∘ φ` is a weak solution on `U` for the field `Ψ_* (J ∘ φ)` and the term
`Ψ_* (a η(φ z, ·) - b J(φ z, ·) η(φ z, ·))`, where `φ' = a + b i`. -/
theorem IsWeakCauchyRiemannOn.comp_chartChange [CompleteSpace W] {Ψ : OpenPartialHomeomorph V W}
    (h : IsWeakCauchyRiemannOn p (φ '' U) J η u) (hφ : DifferentiableOn ℂ φ φ.source)
    (hφ' : ∀ z ∈ φ.source, deriv φ z ≠ 0) (hU : U ⊆ φ.source)
    (hJ : ∀ w ∈ interior (φ '' U), J w (u w) * J w (u w) = -1)
    (hΨ : ContDiffOn ℝ 1 Ψ Ψ.source) (hΨs : ContDiffOn ℝ 1 Ψ.symm Ψ.target)
    (huΨ : MapsTo u (φ '' U) Ψ.source) :
    IsWeakCauchyRiemannOn p U (fun z => Ψ.symm.pullbackEnd (J (φ z)))
      (fun z => VectorField.pullback ℝ Ψ.symm
        fun x => (deriv φ z).re • η (φ z) x - (deriv φ z).im • J (φ z) x (η (φ z) x))
      (fun z => Ψ (u (φ z))) :=
  ((isWeakCauchyRiemannOn_iff_comp_differentiableOn hφ hφ' hU hJ).1 h).openPartialHomeomorph_comp
    hΨ hΨs fun _ hz => huΨ (mem_image_of_mem φ hz)

/-- **Chart independence in the plane.** Under the hypotheses of
`TauCeti.IsWeakCauchyRiemannOn.comp_chartChange`, with both target spaces complete, `u` is a weak
solution on `φ '' U` if and only if `Ψ ∘ u ∘ φ` is a weak solution on `U` for the transported field
and term. -/
theorem isWeakCauchyRiemannOn_iff_chartChange [CompleteSpace V] [CompleteSpace W]
    {Ψ : OpenPartialHomeomorph V W} (hφ : DifferentiableOn ℂ φ φ.source)
    (hφ' : ∀ z ∈ φ.source, deriv φ z ≠ 0) (hU : U ⊆ φ.source)
    (hJ : ∀ w ∈ interior (φ '' U), J w (u w) * J w (u w) = -1)
    (hΨ : ContDiffOn ℝ 1 Ψ Ψ.source) (hΨs : ContDiffOn ℝ 1 Ψ.symm Ψ.target)
    (huΨ : MapsTo u (φ '' U) Ψ.source) :
    IsWeakCauchyRiemannOn p (φ '' U) J η u ↔
      IsWeakCauchyRiemannOn p U (fun z => Ψ.symm.pullbackEnd (J (φ z)))
        (fun z => VectorField.pullback ℝ Ψ.symm
          fun x => (deriv φ z).re • η (φ z) x - (deriv φ z).im • J (φ z) x (η (φ z) x))
        (fun z => Ψ (u (φ z))) := by
  rw [isWeakCauchyRiemannOn_iff_comp_differentiableOn hφ hφ' hU hJ]
  exact isWeakCauchyRiemannOn_iff_openPartialHomeomorph_comp hΨ hΨs
    fun _ hz => huΨ (mem_image_of_mem φ hz)

/-! ### Examples -/

/-- **Dilation and conjugation.** Conjugation solves `∂ₛu + i ∂ₜu = 2`. The domain change
`φ z = 2 z` has `φ' = 2`, which doubles the term to `4`, and the real-linear target change
`Ψ = conj` transports `i` to `conj ∘ i ∘ conj = -i` and `4` to `conj 4 = 4`. So
`Ψ ∘ conj ∘ φ`, that is `z ↦ 2 z`, solves `∂ₛv - i ∂ₜv = 4`: indeed `2 - i (2 i) = 4`. -/
example : IsWeakCauchyRiemannOn p univ (fun _ _ => (-I) • ContinuousLinearMap.id ℝ ℂ)
    (fun _ _ => 4) (fun z => 2 * z) := by
  let φ : OpenPartialHomeomorph ℂ ℂ :=
    (Homeomorph.mulLeft₀ (2 : ℂ) two_ne_zero).toOpenPartialHomeomorph
  let Ψ : OpenPartialHomeomorph ℂ ℂ := conjCLE.toHomeomorph.toOpenPartialHomeomorph
  have hφc : (φ : ℂ → ℂ) = fun z => 2 * z := rfl
  have hΨc : (Ψ : ℂ → ℂ) = conjCLE := rfl
  have hΨsc : (Ψ.symm : ℂ → ℂ) = conjCLE := rfl
  have himage : φ '' univ = univ := by
    simp [φ]
  have hd (z : ℂ) : deriv φ z = 2 := by
    rw [hφc]
    simp
  have hconj : IsWeakCauchyRiemannOn p (φ '' univ)
      (fun _ _ => I • ContinuousLinearMap.id ℝ ℂ) (fun _ _ => 2) conj := by
    rw [himage, ← TopologicalSpace.Opens.coe_top]
    refine isWeakCauchyRiemannOn_of_contDiffOn conjCLE.contDiff.contDiffOn fun z _ => ?_
    have hconj : (conj : ℂ → ℂ) = conjCLE := funext fun x => (conjCLE_apply x).symm
    rw [hconj, conjCLE.fderiv]
    norm_num [Complex.ext_iff]
  have h := hconj.comp_chartChange (Ψ := Ψ)
    (by rw [hφc]; exact (differentiable_id.const_mul _).differentiableOn)
    (fun z _ => by rw [hd]; exact two_ne_zero) (subset_univ _)
    (fun w _ => by ext x; simp [← mul_assoc]) (by rw [hΨc]; exact conjCLE.contDiff.contDiffOn)
    (by rw [hΨsc]; exact conjCLE.contDiff.contDiffOn) (fun _ _ => mem_univ _)
  have h' := h.congr (v := fun z => 2 * z) fun z _ => by
    simp [hφc, hΨc]
  refine (isWeakCauchyRiemannOn_congr_ae (.of_forall fun z => ?_) (.of_forall fun z => ?_)).1 h'
  · ext x
    rw [OpenPartialHomeomorph.pullbackEnd_apply, OpenPartialHomeomorph.symm_symm, hΨc, hΨsc,
      conjCLE.fderiv, conjCLE.fderiv]
    simp
  · rw [VectorField.pullback_eq_of_fderiv_eq (M := conjCLE) (by rw [hΨsc, conjCLE.fderiv]), hd]
    norm_num
    exact conjCLE.symm_apply_eq.2 (by rw [conjCLE_apply, map_ofNat])

/-- **Domain changes must be holomorphic.** The identity solves `∂ₛu + i ∂ₜu = 0`, but its
composition with the antiholomorphic chart change `conj` does not, on any nonempty open set. -/
example {Ω : Opens ℂ} (hΩ : (Ω : Set ℂ).Nonempty) :
    IsWeakCauchyRiemannOn p Ω (fun _ _ => I • ContinuousLinearMap.id ℝ ℂ) (fun _ _ => 0) id ∧
      ¬IsWeakCauchyRiemannOn p Ω (fun _ _ => I • ContinuousLinearMap.id ℝ ℂ) (fun _ _ => 0)
        (fun z => id (conj z)) :=
  ⟨isWeakCauchyRiemannOn_id, not_isWeakCauchyRiemannOn_conj hΩ⟩

end TauCeti
