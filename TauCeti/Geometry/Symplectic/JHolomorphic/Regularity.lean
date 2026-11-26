/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Rigidity
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Bootstrap

/-!
# Regularity of `C¹` pseudoholomorphic maps from the plane into a vector space

Let `V` be a finite-dimensional real normed space and `J : V → AlmostComplexStructure V` an almost
complex structure on `V` that is of class `C^ℓ` as a map into `V →L[ℝ] V` on an open set `W`. A
map `u : ℝ × ℝ → V` of class `C¹` on an open set `U`, with values in `W`, that solves the
Cauchy–Riemann equation `∂ₜu = J(u) ∂ₛu` on `U`, is of class `C^ℓ` on `U`
(`TauCeti.contDiffOn_of_isComplexLinearMap_fderiv`). In the complex coordinate
`Complex.equivRealProdCLM` the equation is `∂ₛu + J(u) ∂ₜu = 0`, and regularity of classical
solutions of the nonlinear Cauchy–Riemann equation (`TauCeti.contDiffOn_of_cauchyRiemann`) gives
the regularity.

Limits of rescaled solutions of the Floer equation, the bubbles of Gromov–Floer compactness, are
`C¹` solutions of this equation for the structure frozen at the bubbling point, and their area is
finite. The finite-energy rigidity theorem for planes in a symplectic vector space,
`TauCeti.SymplecticForm.exists_eq_const_of_isComplexLinearMap_of_integrable_norm_fderiv_sq`, needs
`C²` maps, since it rests on Stokes' formula. With a `C²` structure, regularity removes this
assumption: a `C¹` pseudoholomorphic plane of finite energy, for a structure which is `C²` near its
image and tamed by `ω` along it, is constant
(`TauCeti.SymplecticForm.exists_eq_const_of_isComplexLinearMap_of_contDiff_one`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix B.4
  (Theorem B.4.1 and Remark B.4.3, elliptic bootstrapping) and Section 4.5 (finite-energy planes).
-/

public section

open Complex MeasureTheory Set TopologicalSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Regularity of `C¹` pseudoholomorphic maps of the plane.** Let `J` be an almost complex
structure on `V` which is `C^ℓ` on an open set `W`, as a map into `V →L[ℝ] V`. A map `u` of class
`C¹` on an open set `U ⊆ ℝ × ℝ`, with values in `W`, solving the Cauchy–Riemann equation
`∂ₜu = J(u) ∂ₛu` on `U` is of class `C^ℓ` on `U`. -/
theorem contDiffOn_of_isComplexLinearMap_fderiv {J : V → AlmostComplexStructure V}
    {U : Set (ℝ × ℝ)} {W : Set V} {u : ℝ × ℝ → V} {ℓ : ℕ∞} (hU : IsOpen U) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ ℓ (fun x ↦ (J x).toLinearMap.toContinuousLinearMap) W)
    (hu : ContDiffOn ℝ 1 u U) (huW : MapsTo u U W)
    (hCR : ∀ z ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (u z))
      (fderiv ℝ u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ContDiffOn ℝ ℓ u U := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  set Jc : V → V →L[ℝ] V := fun x ↦ (J x).toLinearMap.toContinuousLinearMap
  set Ω : Opens ℂ := ⟨equivRealProdCLM ⁻¹' U, hU.preimage equivRealProdCLM.continuous⟩
  have heΩ : MapsTo equivRealProdCLM Ω U := fun y hy ↦ hy
  have hu' : ContDiffOn ℝ 1 (u ∘ equivRealProdCLM) Ω :=
    hu.comp equivRealProdCLM.contDiff.contDiffOn heΩ
  -- In the complex coordinate the equation reads `∂ₛu + J(u) ∂ₜu = 0`.
  have hCR' : ∀ y ∈ (Ω : Set ℂ), fderiv ℝ (u ∘ equivRealProdCLM) y 1 +
      Jc ((u ∘ equivRealProdCLM) y) (fderiv ℝ (u ∘ equivRealProdCLM) y I) = 0 := by
    intro y hy
    have h := (hCR _ (heΩ hy)).apply_stdComplexLineImag
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [fderiv_comp_equivRealProdCLM_one, fderiv_comp_equivRealProdCLM_I, h]
    simp [Jc]
  have hc : ContDiffOn ℝ ℓ (u ∘ equivRealProdCLM) Ω :=
    contDiffOn_of_cauchyRiemann (J := fun _ ↦ Jc) (η := fun _ _ ↦ 0) (isOpen_univ.prod hW)
      (hJ.comp contDiff_snd.contDiffOn fun q hq ↦ (mem_prod.1 hq).2) contDiffOn_const
      (fun y hy ↦ ⟨mem_univ _, huW (heΩ hy)⟩) (fun y _ a ↦ by simp [Jc]) hu' hCR'
  have hsymm : MapsTo equivRealProdCLM.symm U Ω := fun z hz ↦ by simpa [Ω] using hz
  simpa [Function.comp_def] using hc.comp equivRealProdCLM.symm.contDiff.contDiffOn hsymm

namespace SymplecticForm

/-- **Finite-energy `C¹` pseudoholomorphic planes in a symplectic vector space are constant.** Let
`J` be an almost complex structure on `V` which is `C²` on an open set `W`, as a map into
`V →L[ℝ] V`, and let `u : ℝ × ℝ → V` be a `C¹` solution of the Cauchy–Riemann equation
`∂ₜu = J(u) ∂ₛu` with values in `W` and with `J(u z)` tamed by `ω` at every point. If `‖du‖²` is
integrable over the plane, then `u` is constant. -/
theorem exists_eq_const_of_isComplexLinearMap_of_contDiff_one (ω : SymplecticForm V)
    {J : V → AlmostComplexStructure V} {W : Set V} {u : ℝ × ℝ → V} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun x ↦ (J x).toLinearMap.toContinuousLinearMap) W)
    (hu : ContDiff ℝ 1 u) (huW : ∀ z, u z ∈ W) (htame : ∀ z, ω.Tames (J (u z)))
    (hCR : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (u z))
      (fderiv ℝ u z : ℝ × ℝ →ₗ[ℝ] V))
    (henergy : Integrable fun z ↦ ‖fderiv ℝ u z‖ ^ 2) :
    ∃ c, u = fun _ ↦ c := by
  have hu2 : ContDiff ℝ 2 u := contDiffOn_univ.1 <|
    contDiffOn_of_isComplexLinearMap_fderiv (ℓ := 2) isOpen_univ hW hJ hu.contDiffOn
      (fun z _ ↦ huW z) fun z _ ↦ hCR z
  exact ω.exists_eq_const_of_isComplexLinearMap_of_integrable_norm_fderiv_sq hu2 htame hCR
    henergy

end SymplecticForm

end TauCeti
