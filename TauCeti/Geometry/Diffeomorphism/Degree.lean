/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Covered
public import TauCeti.Geometry.Manifold.Degree.Homological

/-!
# Covering by diffeomorphisms from the smooth degree of an evaluation map

Let `M` be a compact preconnected Hausdorff manifold of positive dimension `d + 1`, modelled on a
real inner product space `E` and smooth at both `1` and `r`, and let `φ : P → Diff^r(M)` be a
continuous family of diffeomorphisms parametrized by a compact Hausdorff boundaryless `C¹` manifold
`(P, I)` of the same dimension. Given manifold orientations `oP` of `P` and `oM` of `M`, the
homological degree theorem
(`TauCeti.Manifold.Orientation.exists_homologyMap_eq_degreeAtRegularValue_smul`) supplies a
homology class `a ∈ H_{d+1}(P; ℤ)` whose image under `ev_{x₀} ∘ φ : P → M` at any regular value
`y : M` is `(degreeAtRegularValue oP oM (ev_{x₀} ∘ φ) y) • [M]`.

Pushing `a` into `H_{d+1}(Diff^r(M); ℤ)` along `φ` therefore shows that `M` is `ℓ`-covered by
`C^r` diffeomorphisms at `x₀` with `ℓ = degreeAtRegularValue oP oM (ev_{x₀} ∘ φ) y`
(`Manifold.Orientation.isCoveredByDiffeomorphisms_toHomologicalOrientation_of_isRegularValue`).
When `M` is connected, any homological orientation `o` of `M` agrees with `oM` up to sign, and
covering by diffeomorphisms is independent of the orientation, so the same covering integer `ℓ`
holds for every homological orientation `o` of `M`
(`HomologicalOrientation.isCoveredByDiffeomorphisms_of_isRegularValue`). In particular, if
`ev_{x₀} ∘ φ` has nonzero degree at some regular value, then `M` is `ℓ`-covered by diffeomorphisms
for some `ℓ > 0`
(`HomologicalOrientation.exists_isCoveredByDiffeomorphisms_of_degreeAtRegularValue_ne_zero`).

Note that `P` need not be modelled on `E` (or even on an inner product space), and `r : ℕ∞ω` is
unrestricted because `M` carries `[IsManifold 𝓘(ℝ, E) 1 M]` alongside `[IsManifold 𝓘(ℝ, E) r M]`.

## Main results

In the `TauCeti` namespace:

* `Manifold.Orientation.isCoveredByDiffeomorphisms_toHomologicalOrientation_of_isRegularValue`:
  covering by `degreeAtRegularValue` for the homological orientation induced by `oM`.
* `HomologicalOrientation.isCoveredByDiffeomorphisms_of_isRegularValue`: covering by
  `degreeAtRegularValue` for any homological orientation of a connected manifold `M`.
* `HomologicalOrientation.exists_isCoveredByDiffeomorphisms_of_degreeAtRegularValue_ne_zero`:
  nonzero degree at a regular value yields `ℓ`-covering with `ℓ > 0`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3, Definition 6.32 and
  Proposition 6.34.
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M] [IsManifold 𝓘(ℝ, E) 1 M]
  {d : ℕ}
  {P F H : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [TopologicalSpace P] [T2Space P]
  [ChartedSpace H P] [IsManifold I 1 P] [BoundarylessManifold I P] [CompactSpace P]

/-- **Covering by diffeomorphisms from `degreeAtRegularValue`.** If `φ : P → Diff^r(M)` is a
continuous family of diffeomorphisms parametrized by a compact oriented boundaryless `C¹` manifold
`(P, I)` and `y : M` is a regular value of `ev_{x₀} ∘ φ`, then `M` is `ℓ`-covered by `C^r`
diffeomorphisms at `x₀` with `ℓ = degreeAtRegularValue oP oM (ev_{x₀} ∘ φ) y`. -/
theorem Manifold.Orientation.isCoveredByDiffeomorphisms_toHomologicalOrientation_of_isRegularValue
    [PreconnectedSpace M] (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (d + 1)))
    (hE : finrank ℝ E = d + 1) (r : ℕ∞ω) [IsManifold 𝓘(ℝ, E) r M]
    (oP : Manifold.Orientation I P (Fin (d + 1)))
    (φ : C(P, M ≃ₘ^r⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M)) {x₀ y : M}
    (hy : IsRegularValue I 𝓘(ℝ, E) ((Diffeomorph.evalAt x₀).comp φ) y) :
    (oM.toHomologicalOrientation hE).IsCoveredByDiffeomorphisms hE r x₀
      (degreeAtRegularValue oP oM ((Diffeomorph.evalAt x₀).comp φ) y) := by
  obtain ⟨a, ha⟩ := oP.exists_homologyMap_eq_degreeAtRegularValue_smul hE
  refine HomologicalOrientation.IsCoveredByDiffeomorphisms.of_homologyMap φ a ?_
  rw [HomologicalOrientation.mapFundamentalClass_id]
  exact ha oM hy

namespace HomologicalOrientation

/-- **Covering by diffeomorphisms from `degreeAtRegularValue`, for any homological orientation.**
On a compact connected manifold `M`, any homological orientation `o` agrees up to sign with the one
induced by a smooth orientation `oM`, so at any regular value `y` of `ev_{x₀} ∘ φ` the manifold `M`
is `ℓ`-covered by `C^r` diffeomorphisms at `x₀` with
`ℓ = degreeAtRegularValue oP oM (ev_{x₀} ∘ φ) y`. -/
theorem isCoveredByDiffeomorphisms_of_isRegularValue [ConnectedSpace M]
    (o : HomologicalOrientation M E (d + 1)) (hE : finrank ℝ E = d + 1) (r : ℕ∞ω)
    [IsManifold 𝓘(ℝ, E) r M] (oP : Manifold.Orientation I P (Fin (d + 1)))
    (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (d + 1)))
    (φ : C(P, M ≃ₘ^r⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M)) {x₀ y : M}
    (hy : IsRegularValue I 𝓘(ℝ, E) ((Diffeomorph.evalAt x₀).comp φ) y) :
    o.IsCoveredByDiffeomorphisms hE r x₀
      (degreeAtRegularValue oP oM ((Diffeomorph.evalAt x₀).comp φ) y) := by
  have hcov := oM.isCoveredByDiffeomorphisms_toHomologicalOrientation_of_isRegularValue hE r oP φ hy
  rcases HomologicalOrientation.eq_or_eq_neg hE (oM.toHomologicalOrientation hE) o with rfl | rfl
  · exact hcov
  · exact isCoveredByDiffeomorphisms_neg.2 hcov

/-- If `ev_{x₀} ∘ φ` has nonzero degree at some regular value `y`, then `M` is `ℓ`-covered by `C^r`
diffeomorphisms at `x₀` for some `ℓ > 0`. -/
theorem exists_isCoveredByDiffeomorphisms_of_degreeAtRegularValue_ne_zero [ConnectedSpace M]
    (o : HomologicalOrientation M E (d + 1)) (hE : finrank ℝ E = d + 1) (r : ℕ∞ω)
    [IsManifold 𝓘(ℝ, E) r M] (oP : Manifold.Orientation I P (Fin (d + 1)))
    (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (d + 1)))
    (φ : C(P, M ≃ₘ^r⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M)) {x₀ y : M}
    (hy : IsRegularValue I 𝓘(ℝ, E) ((Diffeomorph.evalAt x₀).comp φ) y)
    (hdeg : degreeAtRegularValue oP oM ((Diffeomorph.evalAt x₀).comp φ) y ≠ 0) :
    ∃ ℓ : ℤ, 0 < ℓ ∧ o.IsCoveredByDiffeomorphisms hE r x₀ ℓ :=
  ⟨_, abs_pos.2 hdeg, (o.isCoveredByDiffeomorphisms_of_isRegularValue hE r oP oM φ hy).abs⟩

end HomologicalOrientation

end TauCeti
