/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Comparison.TorusAction
public import TauCeti.Geometry.Toric.Analytic.Fan.Boundary.Manifold

import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Boundary hypersurfaces in the algebraic–analytic comparison

The ray-indexed boundary components on algebraic complex points are the closures, for the
complex affine-chart topology, of their torus orbits. The algebraic–analytic comparison
restricts to a homeomorphism on each component, with the original subspace topologies.
Pulling back any complex atlas of the analytic component makes this restriction a
biholomorphism. If the analytic inclusion is a smooth embedding, so is the algebraic inclusion.
In particular the algebraic boundary components are closed embedded complex hypersurfaces of
dimension one less than the lattice rank.

The comparison also carries the simultaneous holomorphic coordinate-hyperplane normal form
to algebraic complex points. The analytic hypersurface theorem
`exists_isManifold_analyticBoundaryComponent_isSmoothEmbedding` supplies the component atlas,
and `IsLocalHomeomorph.chartedSpaceComap` transports it. The complex points carry the complex
affine-chart topology throughout.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§2.1 and 3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.2 and 4.1.
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (hΦ : Φ.IsRegular) (ρ : Φ.Ray)

/-- The algebraic–analytic comparison restricted to a ray-indexed boundary component, with
both components carrying their subspace topologies. -/
noncomputable def algebraicAnalyticBoundaryHomeomorph :
    AlgebraicComplexPoint.boundaryComponent Φ ρ ≃ₜ Φ.analyticBoundaryComponent hΦ ρ :=
  (algebraicAnalyticHomeomorph hΦ).sets
    (by simpa only [coe_algebraicAnalyticHomeomorph] using
      (preimage_algebraicAnalyticEquiv_analyticBoundaryComponent hΦ ρ).symm)

/-- Restriction to a boundary component commutes with the inclusions into the ambient spaces. -/
@[simp]
theorem coe_algebraicAnalyticBoundaryHomeomorph_apply
    (x : AlgebraicComplexPoint.boundaryComponent Φ ρ) :
    (algebraicAnalyticBoundaryHomeomorph hΦ ρ x).1 = algebraicAnalyticEquiv hΦ x.1 := by
  simp [algebraicAnalyticBoundaryHomeomorph]

/-- The inverse restricted comparison is the restriction of the inverse ambient comparison. -/
@[simp]
theorem coe_algebraicAnalyticBoundaryHomeomorph_symm_apply
    (x : Φ.analyticBoundaryComponent hΦ ρ) :
    ((algebraicAnalyticBoundaryHomeomorph hΦ ρ).symm x).1 =
      (algebraicAnalyticEquiv hΦ).symm x.1 := by
  simp [algebraicAnalyticBoundaryHomeomorph]

section ComponentAtlas

variable [C : ChartedSpace (Fin (Module.finrank ℤ N - 1) → ℂ)
  (Φ.analyticBoundaryComponent hΦ ρ)]

/-- The complex atlas on an algebraic boundary component pulled back from an atlas on its
analytic counterpart. The topology remains the subspace topology. -/
@[instance_reducible]
noncomputable def algebraicBoundaryComponentChartedSpace :
    ChartedSpace (Fin (Module.finrank ℤ N - 1) → ℂ)
      (AlgebraicComplexPoint.boundaryComponent Φ ρ) :=
  (algebraicAnalyticBoundaryHomeomorph hΦ ρ).isLocalHomeomorph.chartedSpaceComap

/-- An analytic boundary-component manifold atlas induces a manifold atlas of the same
dimension on the corresponding algebraic complex-point component. -/
theorem isManifold_algebraicBoundaryComponent (n : ℕ∞ω)
    [IsManifold 𝓘(ℂ, Fin (Module.finrank ℤ N - 1) → ℂ) n
      (Φ.analyticBoundaryComponent hΦ ρ)] :
    letI := algebraicBoundaryComponentChartedSpace hΦ ρ
    IsManifold 𝓘(ℂ, Fin (Module.finrank ℤ N - 1) → ℂ) n
      (AlgebraicComplexPoint.boundaryComponent Φ ρ) :=
  (algebraicAnalyticBoundaryHomeomorph hΦ ρ).isLocalHomeomorph.isManifold_chartedSpaceComap

/-- The boundary restriction of the algebraic–analytic comparison is a biholomorphism for the
pulled-back component atlas, for every differentiability order. -/
noncomputable def algebraicAnalyticBoundaryDiffeomorph (n : ℕ∞ω) :
    letI := algebraicBoundaryComponentChartedSpace hΦ ρ
    AlgebraicComplexPoint.boundaryComponent Φ ρ ≃ₘ^n⟮
      𝓘(ℂ, Fin (Module.finrank ℤ N - 1) → ℂ),
      𝓘(ℂ, Fin (Module.finrank ℤ N - 1) → ℂ)⟯ Φ.analyticBoundaryComponent hΦ ρ := by
  let := algebraicBoundaryComponentChartedSpace hΦ ρ
  let h := (algebraicAnalyticBoundaryHomeomorph hΦ ρ).isLocalHomeomorph
  exact (h.isLocalDiffeomorph_chartedSpaceComap (n := n)).diffeomorphOfBijective
    (algebraicAnalyticBoundaryHomeomorph hΦ ρ).bijective

/-- The component biholomorphism commutes with the ambient boundary inclusions. -/
@[simp]
theorem coe_algebraicAnalyticBoundaryDiffeomorph_apply (n : ℕ∞ω)
    (x : AlgebraicComplexPoint.boundaryComponent Φ ρ) :
    letI := algebraicBoundaryComponentChartedSpace hΦ ρ
    (algebraicAnalyticBoundaryDiffeomorph hΦ ρ n x).1 = algebraicAnalyticEquiv hΦ x.1 := by
  simp only [algebraicAnalyticBoundaryDiffeomorph, coe_diffeomorphOfBijective,
    coe_algebraicAnalyticBoundaryHomeomorph_apply]

/-- The inverse component biholomorphism commutes with the inverse ambient comparison. -/
@[simp]
theorem coe_algebraicAnalyticBoundaryDiffeomorph_symm_apply (n : ℕ∞ω)
    (x : Φ.analyticBoundaryComponent hΦ ρ) :
    letI := algebraicBoundaryComponentChartedSpace hΦ ρ
    ((algebraicAnalyticBoundaryDiffeomorph hΦ ρ n).symm x).1 =
      (algebraicAnalyticEquiv hΦ).symm x.1 := by
  let := algebraicBoundaryComponentChartedSpace hΦ ρ
  apply (algebraicAnalyticEquiv hΦ).injective
  rw [← coe_algebraicAnalyticBoundaryDiffeomorph_apply hΦ ρ n,
    Diffeomorph.apply_symm_apply, Equiv.apply_symm_apply]

/-- If the analytic boundary-component inclusion is a holomorphic smooth embedding, the
algebraic complex-point inclusion is one too, for the component comparison atlas. -/
theorem isSmoothEmbedding_subtypeVal_boundaryComponent (n : ℕ∞ω)
    [IsManifold 𝓘(ℂ, Fin (Module.finrank ℤ N - 1) → ℂ) n
      (Φ.analyticBoundaryComponent hΦ ρ)]
    (h : letI := Φ.analyticChartedSpace hΦ
      Manifold.IsSmoothEmbedding 𝓘(ℂ, Fin (Module.finrank ℤ N - 1) → ℂ)
        𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n
        (Subtype.val : Φ.analyticBoundaryComponent hΦ ρ → Φ.analyticRealization hΦ)) :
    letI := algebraicComplexPointChartedSpace hΦ
    letI := algebraicBoundaryComponentChartedSpace hΦ ρ
    Manifold.IsSmoothEmbedding 𝓘(ℂ, Fin (Module.finrank ℤ N - 1) → ℂ)
      𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n
      (Subtype.val : AlgebraicComplexPoint.boundaryComponent Φ ρ → Φ.AlgebraicComplexPoint) := by
  let := Φ.analyticChartedSpace hΦ
  let := algebraicComplexPointChartedSpace hΦ
  let := algebraicBoundaryComponentChartedSpace hΦ ρ
  have := Φ.isManifold_analyticRealization hΦ n
  have := isManifold_algebraicComplexPoint hΦ n
  have := isManifold_algebraicBoundaryComponent hΦ ρ n
  refine ⟨?_, IsEmbedding.subtypeVal⟩
  have hi := (TauCeti.isImmersion_comp_diffeomorph
    (algebraicAnalyticBoundaryDiffeomorph hΦ ρ n) h.isImmersion).comp_diffeomorph
      (algebraicAnalyticDiffeomorph hΦ n).symm
  exact hi.congr (funext fun x ↦ by simp)

end ComponentAtlas

/-- Every algebraic complex-point boundary component, with its subspace topology, is a closed
embedded complex hypersurface of dimension `rank N - 1`. Closedness is
`AlgebraicComplexPoint.isClosed_boundaryComponent`; the atlas and embedding are supplied here. -/
theorem exists_isManifold_boundaryComponent_isSmoothEmbedding :
    letI := algebraicComplexPointChartedSpace hΦ
    ∃ C : ChartedSpace (Fin (Module.finrank ℤ N - 1) → ℂ)
        (AlgebraicComplexPoint.boundaryComponent Φ ρ),
      letI := C
      IsManifold 𝓘(ℂ, Fin (Module.finrank ℤ N - 1) → ℂ) ω
          (AlgebraicComplexPoint.boundaryComponent Φ ρ) ∧
        Manifold.IsSmoothEmbedding 𝓘(ℂ, Fin (Module.finrank ℤ N - 1) → ℂ)
          𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) ω
          (Subtype.val : AlgebraicComplexPoint.boundaryComponent Φ ρ →
            Φ.AlgebraicComplexPoint) := by
  obtain ⟨C, hC, hι⟩ := Φ.exists_isManifold_analyticBoundaryComponent_isSmoothEmbedding hΦ ρ
  let := C
  let := hC
  exact ⟨algebraicBoundaryComponentChartedSpace hΦ ρ,
    isManifold_algebraicBoundaryComponent hΦ ρ ω,
    isSmoothEmbedding_subtypeVal_boundaryComponent hΦ ρ ω hι⟩

/-- At every algebraic complex point, one holomorphic coordinate chart simultaneously presents
all boundary components through that point as distinct coordinate hyperplanes. -/
theorem exists_partialDiffeomorph_boundaryComponent_normalForm
    (x : Φ.AlgebraicComplexPoint) (n : ℕ∞ω) :
    letI := algebraicComplexPointChartedSpace hΦ
    ∃ (s : Set Φ.Ray) (j : s ↪ Fin (Module.finrank ℤ N))
      (e : PartialDiffeomorph 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ)
        𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) Φ.AlgebraicComplexPoint
        (Fin (Module.finrank ℤ N) → ℂ) n),
      x ∈ e.source ∧ (∀ ρ, x ∈ AlgebraicComplexPoint.boundaryComponent Φ ρ ↔ ρ ∈ s) ∧
        ∀ y ∈ e.source, ∀ ρ,
          y ∈ AlgebraicComplexPoint.boundaryComponent Φ ρ ↔
            ∃ hρ : ρ ∈ s, e y (j ⟨ρ, hρ⟩) = 0 := by
  let := Φ.analyticChartedSpace hΦ
  let := algebraicComplexPointChartedSpace hΦ
  obtain ⟨s, j, e, hx, hs, he⟩ :=
    Φ.exists_partialDiffeomorph_analyticBoundaryComponent_normalForm hΦ
      (algebraicAnalyticEquiv hΦ x) n
  let d := (algebraicAnalyticDiffeomorph hΦ n).toPartialDiffeomorph
  have hmem (p : Φ.AlgebraicComplexPoint) (ρ : Φ.Ray) :
      p ∈ AlgebraicComplexPoint.boundaryComponent Φ ρ ↔
        algebraicAnalyticEquiv hΦ p ∈ Φ.analyticBoundaryComponent hΦ ρ :=
    (Set.ext_iff.mp (preimage_algebraicAnalyticEquiv_analyticBoundaryComponent hΦ ρ) p).symm
  refine ⟨s, j, d.trans e, ?_, fun ρ ↦ (hmem x ρ).trans (hs ρ), ?_⟩
  · simpa [d, Diffeomorph.toPartialDiffeomorph_toPartialEquiv] using hx
  · intro y hy ρ
    have hy' : algebraicAnalyticEquiv hΦ y ∈ e.source := by
      simpa [d, Diffeomorph.toPartialDiffeomorph_toPartialEquiv] using hy.2
    simpa [d, Diffeomorph.toPartialDiffeomorph_toPartialEquiv] using
      (hmem y ρ).trans (he _ hy' ρ)

end TauCeti.Toric.Fan
