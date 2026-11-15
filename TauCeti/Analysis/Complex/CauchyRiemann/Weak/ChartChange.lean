/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Invariance
public import TauCeti.Analysis.Complex.CauchyRiemann.Weak.TargetChange
import TauCeti.Analysis.Complex.Conformal.LocalDegree
import TauCeti.Analysis.Complex.RealDeriv

/-!
# Simultaneous changes of domain and target charts for the weak Cauchy–Riemann equation

The weak equation `TauCeti.IsWeakCauchyRiemannOn p U J η u`, that is
`∂ₛu + J(z, u) ∂ₜu = η(z, u)` weakly on `U ⊆ ℂ`, is the planar coordinate form of the weak
pseudoholomorphic equation. Changing the isothermal chart on the domain by a biholomorphism `φ` and
the chart on the target by a `C¹` diffeomorphism `Ψ` replaces a solution `u` by `Ψ ∘ u ∘ φ`. This
file shows that this change is an equivalence when `J` and `η` are transported along.

For the domain change, `φ` is an open partial homeomorphism of `ℂ`, holomorphic on its source, with
`φ' = a + b i`; the term `η(φ z, x)` becomes `a η(φ z, x) - b J(φ z, x) η(φ z, x)`, and the change
is an equivalence by `TauCeti.isWeakCauchyRiemannOn_image_iff_comp_openPartialHomeomorph`. For the
target change the field becomes `Ψ_* J = dΨ ∘ J ∘ dΨ⁻¹` (`OpenPartialHomeomorph.pullbackEnd` along
`Ψ.symm`) and the term becomes `Ψ_* η` (`VectorField.pullback` along `Ψ.symm`), as in
`TauCeti.isWeakCauchyRiemannOn_iff_openPartialHomeomorph_comp`.

The domain `U` is any subset of the source of `φ`, so half-discs are allowed.

## Main results

* `TauCeti.IsWeakCauchyRiemannOn.openPartialHomeomorph_comp_comp_openPartialHomeomorph`:
  `Ψ ∘ u ∘ φ` solves the equation for the transported field and term.
* `TauCeti.isWeakCauchyRiemannOn_image_iff_openPartialHomeomorph_comp_comp_openPartialHomeomorph`:
  the combined change is an equivalence.
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
  [NormedSpace ℝ W] {p : ENNReal} {U U' : Set ℂ} {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V}
  {u : ℂ → V} {φ : OpenPartialHomeomorph ℂ ℂ}

/-- **Combined change of domain and target charts.** Let `φ` be an open partial homeomorphism of
`ℂ`, holomorphic on its source, with `φ' = a + b i`, let `U` be a subset of its source mapped by
`φ` into `U'`, and let `J(φ z, u(φ z))` square to `-1` on the interior of `U`. Let `Ψ` be an open
partial homeomorphism of the target, `C¹` with `C¹` inverse, whose source contains `u (φ '' U)`.
If `u` is a weak solution on `U'`, then `Ψ ∘ u ∘ φ` is a weak solution on `U` for the field
`Ψ_* (J ∘ φ)` and the term `Ψ_* (a η(φ z, ·) - b J(φ z, ·) η(φ z, ·))`. -/
theorem IsWeakCauchyRiemannOn.openPartialHomeomorph_comp_comp_openPartialHomeomorph
    [CompleteSpace W] {Ψ : OpenPartialHomeomorph V W} (h : IsWeakCauchyRiemannOn p U' J η u)
    (hφ : DifferentiableOn ℂ φ φ.source) (hU : U ⊆ φ.source) (hmaps : MapsTo φ U U')
    (hJ : ∀ z ∈ interior U, J (φ z) (u (φ z)) * J (φ z) (u (φ z)) = -1)
    (hΨ : ContDiffOn ℝ 1 Ψ Ψ.source) (hΨs : ContDiffOn ℝ 1 Ψ.symm Ψ.target)
    (huΨ : MapsTo (fun z => u (φ z)) U Ψ.source) :
    IsWeakCauchyRiemannOn p U (fun z => Ψ.symm.pullbackEnd (J (φ z)))
      (fun z => VectorField.pullback ℝ Ψ.symm
        fun x => (deriv φ z).re • η (φ z) x - (deriv φ z).im • J (φ z) x (η (φ z) x))
      (fun z => Ψ (u (φ z))) :=
  (h.comp_differentiableOn φ.open_source hφ hU (φ.injOn.mono hU)
    (fun _ hz => deriv_ne_zero_of_injOn hφ φ.open_source φ.injOn (hU hz)) hmaps
    hJ).openPartialHomeomorph_comp hΨ hΨs huΨ

/-- **Chart independence in the plane.** Let `φ` be an open partial homeomorphism of `ℂ`,
holomorphic on its source, with `φ' = a + b i`, let `U` be a subset of its source, and let
`J(w, u w)` square to `-1` on the interior of `φ '' U`. Let `Ψ` be an open partial homeomorphism
between complete spaces, `C¹` with `C¹` inverse, whose source contains `u (φ '' U)`. Then `u` is a
weak solution on `φ '' U` if and only if `Ψ ∘ u ∘ φ` is a weak solution on `U` for the field
`Ψ_* (J ∘ φ)` and the term `Ψ_* (a η(φ z, ·) - b J(φ z, ·) η(φ z, ·))`. -/
theorem isWeakCauchyRiemannOn_image_iff_openPartialHomeomorph_comp_comp_openPartialHomeomorph
    [CompleteSpace V] [CompleteSpace W] {Ψ : OpenPartialHomeomorph V W}
    (hφ : DifferentiableOn ℂ φ φ.source) (hU : U ⊆ φ.source)
    (hJ : ∀ w ∈ interior (φ '' U), J w (u w) * J w (u w) = -1)
    (hΨ : ContDiffOn ℝ 1 Ψ Ψ.source) (hΨs : ContDiffOn ℝ 1 Ψ.symm Ψ.target)
    (huΨ : MapsTo u (φ '' U) Ψ.source) :
    IsWeakCauchyRiemannOn p (φ '' U) J η u ↔
      IsWeakCauchyRiemannOn p U (fun z => Ψ.symm.pullbackEnd (J (φ z)))
        (fun z => VectorField.pullback ℝ Ψ.symm
          fun x => (deriv φ z).re • η (φ z) x - (deriv φ z).im • J (φ z) x (η (φ z) x))
        (fun z => Ψ (u (φ z))) := by
  rw [isWeakCauchyRiemannOn_image_iff_comp_openPartialHomeomorph hφ hU hJ]
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
  let Ψ : OpenPartialHomeomorph ℂ ℂ := conjLIE.toHomeomorph.toOpenPartialHomeomorph
  have hφc : (φ : ℂ → ℂ) = fun z => 2 * z := by
    ext z
    simp [φ]
  have hΨc : (Ψ : ℂ → ℂ) = conj := by
    ext z
    simp [Ψ]
  have hΨsc : (Ψ.symm : ℂ → ℂ) = conj := by
    ext z
    simp [Ψ]
  have hd (z : ℂ) : deriv φ z = 2 := by
    rw [hφc]
    simp
  have h := IsWeakCauchyRiemannOn.openPartialHomeomorph_comp_comp_openPartialHomeomorph (φ := φ)
    (U := univ) (Ψ := Ψ) (isWeakCauchyRiemannOn_conj_two (p := p) (Ω := ⊤))
    (by rw [hφc]; exact (differentiable_id.const_mul _).differentiableOn) (subset_univ _)
    (fun _ _ => trivial) (fun z _ => by ext x; simp [← mul_assoc])
    (by rw [hΨc]; exact conjCLE.contDiff.contDiffOn)
    (by rw [hΨsc]; exact conjCLE.contDiff.contDiffOn) (fun _ _ => mem_univ _)
  have h' := h.congr (v := fun z => 2 * z) fun z _ => by
    simp [hφc, hΨc]
  refine (isWeakCauchyRiemannOn_congr_ae (.of_forall fun z => ?_) (.of_forall fun z => ?_)).1 h'
  · ext x
    rw [OpenPartialHomeomorph.pullbackEnd_apply, OpenPartialHomeomorph.symm_symm, hΨc, hΨsc,
      fderiv_conj, fderiv_conj]
    simp
  · rw [VectorField.pullback_eq_of_fderiv_eq (M := conjCLE) (by rw [hΨsc, fderiv_conj]), hd]
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
