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
subset of `M` is `C^n` for every `n : ℕ∞` (McDuff–Salamon, Theorem B.4.1).

The case where the domain is a complex curve `(X, ofComplexManifold ℂ X)` is already proved in
`TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic.Regularity`
(`TauCeti.IsPseudoholomorphicOn.contMDiffOn`, `TauCeti.IsPseudoholomorphic.contMDiff`). For a
general almost complex surface `(M, j)`, pulling `u` back along the isothermal homeomorphism
`TauCeti.IsothermalSurface.homeomorph j` turns `u` into a pseudoholomorphic curve on the complex
curve `TauCeti.IsothermalSurface j`, to which `TauCeti.IsPseudoholomorphicOn.contMDiffOn` applies;
composing back with `(TauCeti.IsothermalSurface.homeomorph j).symm` gives smoothness on `M`.

## Main results

* `TauCeti.IsPseudoholomorphicOn.contMDiffOn_almostComplex`,
  `TauCeti.IsPseudoholomorphic.contMDiff_almostComplex`: a `C¹` pseudoholomorphic map from an open
  subset (or all) of an almost complex surface `(M, j)` into a finite-dimensional smooth almost
  complex manifold without boundary is `C^n` for every `n : ℕ∞`.
* `TauCeti.IsPseudoholomorphicOn.contDiffOn`, `TauCeti.IsPseudoholomorphic.contDiff`: the planar
  specializations for maps `ℂ → V` into a finite-dimensional real normed space `V`.

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
If `u : M → M'` is `C¹` and `(j, J)`-holomorphic on an open set `s ⊆ M`, then `u` is `C^n` on `s`
for every `n : ℕ∞` (McDuff–Salamon, Theorem B.4.1). -/
theorem IsPseudoholomorphicOn.contMDiffOn_almostComplex
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ∞ M]
    {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) M}
    {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    {J : SmoothAlmostComplexStructure I' M'}
    {s : Set M} {n : ℕ∞} {u : M → M'}
    (h : IsPseudoholomorphicOn j J u s) (hs : IsOpen s) (hu : ContMDiffOn 𝓘(ℝ, ℂ) I' 1 u s) :
    ContMDiffOn 𝓘(ℝ, ℂ) I' n u s := by
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
  have h_comp_smooth : ContMDiffOn 𝓘(ℝ, ℂ) I' ∞ (u ∘ φ) (φ ⁻¹' s) :=
    h_comp_hol.contMDiffOn (hs.preimage φ.continuous) h_comp_c1
  have h_smooth : ContMDiffOn 𝓘(ℝ, ℂ) I' ∞ u s :=
    (h_comp_smooth.comp (IsothermalSurface.contMDiff_homeomorph_symm j).contMDiffOn
      (fun x hx => by simpa [φ] using hx)).congr fun x _ => by simp [φ]
  exact h_smooth.of_le (WithTop.coe_le_coe.2 le_top)

/-- **Smoothness of global `C¹` pseudoholomorphic curves from almost complex surfaces.** If `M`
is a smooth real surface with a smooth almost complex structure `j`, `M'` is a finite-dimensional
smooth manifold without boundary with a smooth almost complex structure `J`, and `u : M → M'` is
`C¹` and `(j, J)`-holomorphic, then `u` is `C^n` for every `n : ℕ∞`. -/
theorem IsPseudoholomorphic.contMDiff_almostComplex
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ∞ M]
    {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) M}
    {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    {J : SmoothAlmostComplexStructure I' M'}
    {n : ℕ∞} {u : M → M'}
    (h : IsPseudoholomorphic j J u) (hu : ContMDiff 𝓘(ℝ, ℂ) I' 1 u) :
    ContMDiff 𝓘(ℝ, ℂ) I' n u :=
  contMDiffOn_univ.1 <|
    (h.isPseudoholomorphicOn univ).contMDiffOn_almostComplex isOpen_univ hu.contMDiffOn

section Planar

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Smoothness of `C¹` pseudoholomorphic maps on planar open sets.** If `j` is a smooth almost
complex structure on `ℂ`, `J` is a smooth almost complex structure on a finite-dimensional real
normed space `V`, and `u : ℂ → V` is `C¹` and `(j, J)`-holomorphic on an open set `s ⊆ ℂ`, then
`u` is `C^n` on `s` for every `n : ℕ∞`. -/
theorem IsPseudoholomorphicOn.contDiffOn [FiniteDimensional ℝ V]
    {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) ℂ}
    {J : SmoothAlmostComplexStructure 𝓘(ℝ, V) V} {s : Set ℂ} {n : ℕ∞} {u : ℂ → V}
    (h : IsPseudoholomorphicOn j J u s) (hs : IsOpen s) (hu : ContDiffOn ℝ 1 u s) :
    ContDiffOn ℝ n u s :=
  contMDiffOn_iff_contDiffOn.1 (h.contMDiffOn_almostComplex hs (contMDiffOn_iff_contDiffOn.2 hu))

/-- **Smoothness of global `C¹` pseudoholomorphic maps from `ℂ`.** If `j` is a smooth almost
complex structure on `ℂ`, `J` is a smooth almost complex structure on a finite-dimensional real
normed space `V`, and `u : ℂ → V` is `C¹` and `(j, J)`-holomorphic, then `u` is `C^n` for every
`n : ℕ∞`. -/
theorem IsPseudoholomorphic.contDiff [FiniteDimensional ℝ V]
    {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) ℂ}
    {J : SmoothAlmostComplexStructure 𝓘(ℝ, V) V} {n : ℕ∞} {u : ℂ → V}
    (h : IsPseudoholomorphic j J u) (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ n u :=
  contMDiff_iff_contDiff.1 (h.contMDiff_almostComplex (contMDiff_iff_contDiff.2 hu))

end Planar

end TauCeti
