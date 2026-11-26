/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
import TauCeti.Geometry.Manifold.Complex.Isothermal
import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic.Regularity

/-!
# Smoothness of `C¹` pseudoholomorphic curves from almost complex surfaces

Let `M` be a smooth real surface equipped with a smooth almost complex structure `j`, and let `M'`
be a finite-dimensional smooth manifold without boundary equipped with a smooth almost complex
structure `J`. This file proves that every `C¹` `(j, J)`-holomorphic map `u : M → M'` on an open
subset of `M` is smooth (`C^∞`, McDuff–Salamon, Theorem B.4.1 and Remark B.4.3).

For a general almost complex surface `(M, j)`, pulling `u` back along the isothermal homeomorphism
`TauCeti.IsothermalSurface.homeomorph j` turns `u` into a pseudoholomorphic curve on the complex
curve `TauCeti.IsothermalSurface j`. Comparing with `TauCeti.IsWeakPseudoholomorphicOn`
(`TauCeti.isWeakPseudoholomorphicOn_iff_isPseudoholomorphicOn`) and applying weak interior
regularity (`TauCeti.IsWeakPseudoholomorphicOn.contMDiffOn`), then composing back with
`(TauCeti.IsothermalSurface.homeomorph j).symm`, gives smoothness on `M`.

## Main results

* `TauCeti.IsPseudoholomorphicOn.contMDiffOn`, `TauCeti.IsPseudoholomorphic.contMDiff`: a `C¹`
  pseudoholomorphic map from an open subset (or all) of an almost complex surface `(M, j)` into a
  finite-dimensional smooth almost complex manifold without boundary is smooth.
* `TauCeti.IsPseudoholomorphicOn.contDiffOn`, `TauCeti.IsPseudoholomorphic.contDiff`: the planar
  specializations for maps `ℂ → V` into a finite-dimensional real normed space `V`.
* `TauCeti.contMDiffOn_of_mfderiv_stdComplexLineImag_eq`,
  `TauCeti.contMDiff_of_mfderiv_stdComplexLineImag_eq`: the same for a map of the plane `ℝ × ℝ`
  solving `∂ₜu = J(u) ∂ₛu`, the form in which bubbles of Floer solutions arise.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Theorem B.4.1 and Remark B.4.3).
-/

public noncomputable section

open Complex Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

/-- **Smoothness of `C¹` pseudoholomorphic curves from almost complex surfaces.** Let `M` be a
smooth real surface carrying a smooth almost complex structure `j`, and let `M'` be a
finite-dimensional smooth manifold without boundary carrying a smooth almost complex structure `J`.
If `u : M → M'` is `C¹` and `(j, J)`-holomorphic on an open set `s ⊆ M`, then `u` is smooth on
`s` (McDuff–Salamon, Theorem B.4.1 and Remark B.4.3). -/
theorem IsPseudoholomorphicOn.contMDiffOn
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ∞ M]
    {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) M}
    {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    {J : SmoothAlmostComplexStructure I' M'}
    {s : Set M} {u : M → M'}
    (h : IsPseudoholomorphicOn j J u s) (hs : IsOpen s) (hu : ContMDiffOn 𝓘(ℝ, ℂ) I' 1 u s) :
    ContMDiffOn 𝓘(ℝ, ℂ) I' ∞ u s := by
  let φ := IsothermalSurface.homeomorph j
  have : IsManifold 𝓘(ℂ) ∞ (IsothermalSurface j) := .of_le (by exact_mod_cast le_top)
  have : IsManifold 𝓘(ℝ, ℂ) ∞ (IsothermalSurface j) :=
    (inferInstance : IsManifold 𝓘(ℂ) ∞ (IsothermalSurface j)).restrictScalars ℝ
  have h_comp_c1 : ContMDiffOn 𝓘(ℝ, ℂ) I' 1 (u ∘ φ) (φ ⁻¹' s) :=
    hu.comp ((IsothermalSurface.contMDiff_homeomorph j).contMDiffOn.of_le
      (WithTop.coe_le_coe.2 le_top)) (mapsTo_preimage φ s)
  have h_comp_hol :
      IsPseudoholomorphicOn (SmoothAlmostComplexStructure.ofComplexManifold ℂ (IsothermalSurface j))
        J (u ∘ φ) (φ ⁻¹' s) :=
    h.comp ((IsothermalSurface.isPseudoholomorphic_homeomorph j).isPseudoholomorphicOn (φ ⁻¹' s))
      (mapsTo_preimage φ s)
  have hs_pre : IsOpen (φ ⁻¹' s) := hs.preimage φ.continuous
  have h_comp_smooth : ContMDiffOn 𝓘(ℝ, ℂ) I' ∞ (u ∘ φ) (φ ⁻¹' s) :=
    ((isWeakPseudoholomorphicOn_iff_isPseudoholomorphicOn (ℓ := ⊤) (p := 3) J hs_pre
        h_comp_c1).2 h_comp_hol).contMDiffOn hs_pre (by norm_num)
  exact (h_comp_smooth.comp (IsothermalSurface.contMDiff_homeomorph_symm j).contMDiffOn
    (fun x hx => by simpa [φ] using hx)).congr fun x _ => by simp [φ]

/-- **Smoothness of global `C¹` pseudoholomorphic curves from almost complex surfaces.** If `M`
is a smooth real surface with a smooth almost complex structure `j`, `M'` is a finite-dimensional
smooth manifold without boundary with a smooth almost complex structure `J`, and `u : M → M'` is
`C¹` and `(j, J)`-holomorphic, then `u` is smooth. -/
theorem IsPseudoholomorphic.contMDiff
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ∞ M]
    {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) M}
    {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    {J : SmoothAlmostComplexStructure I' M'}
    {u : M → M'}
    (h : IsPseudoholomorphic j J u) (hu : ContMDiff 𝓘(ℝ, ℂ) I' 1 u) :
    ContMDiff 𝓘(ℝ, ℂ) I' ∞ u :=
  contMDiffOn_univ.1 <|
    (h.isPseudoholomorphicOn univ).contMDiffOn isOpen_univ hu.contMDiffOn

section Planar

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Smoothness of `C¹` pseudoholomorphic maps on planar open sets.** If `j` is a smooth almost
complex structure on `ℂ`, `J` is a smooth almost complex structure on a finite-dimensional real
normed space `V`, and `u : ℂ → V` is `C¹` and `(j, J)`-holomorphic on an open set `s ⊆ ℂ`, then
`u` is smooth on `s`. -/
theorem IsPseudoholomorphicOn.contDiffOn [FiniteDimensional ℝ V]
    {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) ℂ}
    {J : SmoothAlmostComplexStructure 𝓘(ℝ, V) V} {s : Set ℂ} {u : ℂ → V}
    (h : IsPseudoholomorphicOn j J u s) (hs : IsOpen s) (hu : ContDiffOn ℝ 1 u s) :
    ContDiffOn ℝ ∞ u s :=
  contMDiffOn_iff_contDiffOn.1 (h.contMDiffOn hs (contMDiffOn_iff_contDiffOn.2 hu))

/-- **Smoothness of global `C¹` pseudoholomorphic maps from `ℂ`.** If `j` is a smooth almost
complex structure on `ℂ`, `J` is a smooth almost complex structure on a finite-dimensional real
normed space `V`, and `u : ℂ → V` is `C¹` and `(j, J)`-holomorphic, then `u` is smooth. -/
theorem IsPseudoholomorphic.contDiff [FiniteDimensional ℝ V]
    {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) ℂ}
    {J : SmoothAlmostComplexStructure 𝓘(ℝ, V) V} {u : ℂ → V}
    (h : IsPseudoholomorphic j J u) (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ ∞ u :=
  contMDiff_iff_contDiff.1 (h.contMDiff (contMDiff_iff_contDiff.2 hu))

end Planar

section RealPlane

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **`C¹` pseudoholomorphic maps of the plane are smooth.** Let `J₀` be a smooth almost complex
structure on `M`. A map `u : ℝ × ℝ → M` of class `C¹` on an open set `U` which solves the
Cauchy–Riemann equation `∂ₜu = J₀(u) ∂ₛu` on `U` is smooth on `U`. This is
`TauCeti.IsPseudoholomorphicOn.contMDiffOn` for the Riemann surface `ℂ`, read in the real
coordinates `Complex.equivRealProdCLM`. -/
theorem contMDiffOn_of_mfderiv_stdComplexLineImag_eq {J₀ : SmoothAlmostComplexStructure I M}
    {u : ℝ × ℝ → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U)
    (hCR : ∀ z ∈ U, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
      J₀ (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ u U := by
  set e : ℂ ≃L[ℝ] ℝ × ℝ := Complex.equivRealProdCLM
  have he : MapsTo e (e ⁻¹' U) U := fun _ hz ↦ hz
  -- Read `u` on the Riemann surface `ℂ`, where it is pseudoholomorphic.
  have hhol : IsPseudoholomorphicOn (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) J₀
      (u ∘ e) (e ⁻¹' U) := by
    refine isPseudoholomorphicOn_iff.2 fun z hz ↦ ?_
    have hdiff : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (e z) :=
      ((hu _ hz).contMDiffAt (hU.mem_nhds hz)).mdifferentiableAt one_ne_zero
    have hez := isPseudoholomorphic_iff.1 isPseudoholomorphic_equivRealProdCLM z
    exact (((isPseudoholomorphicAt_stdComplexLine_iff J₀ u (e z)).2
      ⟨_, hdiff.hasMFDerivAt, hCR _ hz⟩).comp hez).isPseudoholomorphicWithinAt
  have hsmooth := hhol.contMDiffOn (hU.preimage e.continuous)
    (hu.comp e.contDiff.contMDiff.contMDiffOn he)
  exact (hsmooth.comp e.symm.contDiff.contMDiff.contMDiffOn fun y hy ↦ by simpa using hy).congr
    fun y _ ↦ by simp

/-- **`C¹` pseudoholomorphic planes are smooth.** Let `J₀` be a smooth almost complex structure
on `M`. A `C¹` map `u : ℝ × ℝ → M` solving the Cauchy–Riemann equation `∂ₜu = J₀(u) ∂ₛu` is
smooth. -/
theorem contMDiff_of_mfderiv_stdComplexLineImag_eq {J₀ : SmoothAlmostComplexStructure I M}
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hCR : ∀ z, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
      J₀ (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u :=
  contMDiffOn_univ.1 <|
    contMDiffOn_of_mfderiv_stdComplexLineImag_eq isOpen_univ hu.contMDiffOn fun z _ ↦ hCR z

end RealPlane

end TauCeti
