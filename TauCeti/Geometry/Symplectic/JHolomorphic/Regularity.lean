/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Rigidity
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Bootstrap
import TauCeti.Geometry.Symplectic.Complex.Line

/-!
# Regularity of `C¹` pseudoholomorphic maps from the plane into a vector space

Let `V` be a finite-dimensional real normed space and `J : V → AlmostComplexStructure V` an almost
complex structure on `V` that is of class `C^ℓ` as a map into `V →L[ℝ] V` on an open set `W`. A
map `u : ℝ × ℝ → V` of class `C¹` on an open set `U`, with values in `W`, that solves the
Cauchy–Riemann equation `∂ₜu = J(u) ∂ₛu` on `U`, is of class `C^ℓ` on `U`
(`TauCeti.contDiffOn_of_isComplexLinearMap_fderiv`). In the complex coordinate
`Complex.equivRealProdCLM` the equation is `∂ₛu + J(u) ∂ₜu = 0`, so the classical solution is a
weak one (`TauCeti.isWeakCauchyRiemannOn_of_contDiffOn`), and interior elliptic bootstrapping
(`TauCeti.contDiffOn_of_isWeakCauchyRiemannOn`) gives the regularity.

Limits of rescaled solutions of the Floer equation, the bubbles of Gromov–Floer compactness, are
`C¹` solutions of this equation for the structure frozen at the bubbling point, and their area is
finite. The finite-energy rigidity theorem for planes in a symplectic vector space,
`TauCeti.SymplecticForm.exists_eq_const_of_isComplexLinearMap_of_integrable_norm_fderiv_sq`, needs
`C²` maps, since it rests on Stokes' formula. With a `C²` structure, regularity removes this
assumption: a `C¹` pseudoholomorphic plane of finite energy, for a structure which is `C²` near its
image and tamed by `ω` along it, is constant
(`TauCeti.SymplecticForm.exists_eq_const_of_isComplexLinearMap_of_contDiff_one`).

This file also provides the corresponding `TauCeti.IsJHolomorphicOn.contDiffOn` and
`TauCeti.IsJHolomorphic.contDiff` corollaries for maps `u : ℂ → V` holomorphic with respect to the
standard complex structure `AlmostComplexStructure.ofComplexModule ℂ`. The manifold-level
smoothness corollaries for `TauCeti.IsPseudoholomorphicOn` and `TauCeti.IsPseudoholomorphic` live
in `TauCeti.Geometry.Symplectic.Manifold.JHolomorphic.Regularity`.

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
  have hweak := isWeakCauchyRiemannOn_of_contDiffOn (p := ⊤) (J := fun _ ↦ Jc)
    (η := fun _ _ ↦ 0) hu' hCR'
  have hc : ContDiffOn ℝ ℓ (u ∘ equivRealProdCLM) Ω :=
    contDiffOn_of_isWeakCauchyRiemannOn (by simp) (isOpen_univ.prod hW)
      (hJ.comp contDiff_snd.contDiffOn fun q hq ↦ (mem_prod.1 hq).2) contDiffOn_const
      (fun y hy ↦ ⟨mem_univ _, huW (heΩ hy)⟩)
      (Filter.Eventually.of_forall fun y ↦ ContinuousLinearMap.ext fun a ↦ by simp [Jc])
      hweak
  have hsymm : MapsTo equivRealProdCLM.symm U Ω := fun z hz ↦ by simpa [Ω] using hz
  simpa [Function.comp_def] using hc.comp equivRealProdCLM.symm.contDiff.contDiffOn hsymm

/-- **Local `C^n` regularity of `C¹` `J`-holomorphic maps on planar open sets.** Let `V` be a
finite-dimensional real normed space, let `W ⊆ V` be an open set on which
`x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap` is `C^n`, and let `u : ℂ → V` be a `C¹` map
on an open set `s ⊆ ℂ` mapping `s` into `W` and satisfying
`IsJHolomorphicOn (fun _ => AlmostComplexStructure.ofComplexModule ℂ) J u s`. Then `u` is `C^n` on
`s` (McDuff–Salamon, Theorem B.4.1 and Remark B.4.3). -/
theorem IsJHolomorphicOn.contDiffOn {n : ℕ∞} {s : Set ℂ} {W : Set V}
    {J : V → AlmostComplexStructure V} {u : ℂ → V}
    (h : IsJHolomorphicOn (fun _ => AlmostComplexStructure.ofComplexModule ℂ) J u s)
    (hs : IsOpen s) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ n (fun x => LinearMap.toContinuousLinearMap (J x).toLinearMap) W)
    (hu : ContDiffOn ℝ 1 u s) (huW : MapsTo u s W) :
    ContDiffOn ℝ n u s := by
  let U : Set (ℝ × ℝ) := equivRealProdCLM.symm ⁻¹' s
  have hU : IsOpen U := hs.preimage equivRealProdCLM.symm.continuous
  have hCR : ∀ z ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J ((u ∘ equivRealProdCLM.symm) z))
      (fderiv ℝ (u ∘ equivRealProdCLM.symm) z : ℝ × ℝ →ₗ[ℝ] V) := by
    intro z hz
    have hz_hol := (h.isJHolomorphicWithinAt hz).isJHolomorphicAt_of_mem_nhds (hs.mem_nhds hz)
    have hf : HasFDerivAt (u ∘ equivRealProdCLM.symm)
        ((fderiv ℝ u (equivRealProdCLM.symm z)).comp equivRealProdCLM.symm.toContinuousLinearMap)
        z :=
      hz_hol.differentiableAt.hasFDerivAt.comp z equivRealProdCLM.symm.hasFDerivAt
    rw [hf.fderiv]
    exact hz_hol.fderiv_isComplexLinear.comp isComplexLinearMap_equivRealProdCLM_symm
  have hc : ContDiffOn ℝ n (u ∘ equivRealProdCLM.symm) U :=
    contDiffOn_of_isComplexLinearMap_fderiv hU hW hJ
      (hu.comp equivRealProdCLM.symm.contDiff.contDiffOn (mapsTo_preimage _ s))
      (huW.comp (mapsTo_preimage _ s)) hCR
  exact (hc.comp equivRealProdCLM.contDiff.contDiffOn
    (fun z hz => by dsimp [U]; rwa [mem_preimage, equivRealProdCLM.symm_apply_apply])).congr
    fun z _ => by dsimp [Function.comp_def]; rw [equivRealProdCLM.symm_apply_apply]

/-- **Global `C^n` regularity of `C¹` `J`-holomorphic maps from `ℂ`.** If `V` is a
finite-dimensional real normed space, `x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap` is
`C^n`, and `u : ℂ → V` is `C¹` and `J`-holomorphic, then `u` is `C^n`. -/
theorem IsJHolomorphic.contDiff {n : ℕ∞}
    {J : V → AlmostComplexStructure V} {u : ℂ → V}
    (h : IsJHolomorphic (fun _ => AlmostComplexStructure.ofComplexModule ℂ) J u)
    (hJ : ContDiff ℝ n (fun x => LinearMap.toContinuousLinearMap (J x).toLinearMap))
    (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ n u :=
  contDiffOn_univ.1 <| (h.isJHolomorphicOn univ).contDiffOn isOpen_univ isOpen_univ
    hJ.contDiffOn hu.contDiffOn (mapsTo_univ u univ)

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
