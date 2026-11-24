/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Covered
public import TauCeti.Geometry.Manifold.Degree.Homological
import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.LinearEquiv

/-!
# Covering a manifold by diffeomorphisms of prescribed smooth degree

Let `M` be a compact preconnected `(n + 1)`-dimensional `C¹` manifold modelled on a real inner
product space `F`, and let `φ : P → Diff^k(M)` be a continuous family of `C^k` diffeomorphisms
parametrized by a compact oriented boundaryless `(n + 1)`-dimensional `C¹` manifold `(P, I)`
(possibly modelled on a different space `(E, H, I)`, such as a product of spheres). Evaluating `φ`
at a base point `x₀ ∈ M` gives the map `p ↦ φ p x₀ : P → M`.

At any regular value `y` of `p ↦ φ p x₀`, the manifold `M` is `ℓ`-covered by `C^k` diffeomorphisms
for `ℓ = TauCeti.degreeAtRegularValue oP oM (fun p ↦ φ p x₀) y` — at `x₀` for `oM`, and
consequently at every base point `x ∈ M` and for every homological orientation `o` of `M`. In
particular, `M` is always `TauCeti.degree oP oM (fun p ↦ φ p x₀)`-covered by `C^k` diffeomorphisms,
with no `C^∞` hypothesis.

This abstracts the passage from a smooth degree computation on a parameter manifold `P` to
`TauCeti.HomologicalOrientation.IsCoveredByDiffeomorphisms`, as used in
Barraud–Damian–Humilière–Oancea, Proposition 6.34.

## Main results

* `TauCeti.Manifold.Orientation.isCoveredByDiffeomorphisms_degreeAtRegularValue`,
  `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_degreeAtRegularValue`: a family
  `φ : C(P, Diff^k(M))` makes `M` `ℓ`-covered by `C^k` diffeomorphisms for the signed preimage
  count `ℓ` over any regular value of `p ↦ φ p x₀`.
* `TauCeti.Manifold.Orientation.isCoveredByDiffeomorphisms_degree`,
  `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_degree`: `M` is
  `TauCeti.degree oP oM (fun p ↦ φ p x₀)`-covered by `C^k` diffeomorphisms.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3, Definitions 6.26 and 6.32,
  Proposition 6.34.
-/

public section

noncomputable section

open Function Module
open scoped ContDiff Manifold TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

variable {E H P F M : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace P] [ChartedSpace H P] [T2Space P] [CompactSpace P] [IsManifold I 1 P]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace F M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
  [IsManifold 𝓘(ℝ, F) 1 M]
  {n : ℕ} (hF : finrank ℝ F = n + 1) (k : ℕ∞ω) [IsManifold 𝓘(ℝ, F) k M]

/-- **Covering by diffeomorphisms via the signed count at a regular value.** Let
`φ : C(P, Diff^k(M))` be a continuous family of `C^k` diffeomorphisms of `M` parametrized by a
compact oriented boundaryless `C¹` manifold `(P, I, oP)`. For any base point `x₀ : M` and any
regular value `y` of `p ↦ φ p x₀`, the manifold `M` is
`degreeAtRegularValue oP oM (fun p ↦ φ p x₀) y`-covered by `C^k` diffeomorphisms at `x₀`. -/
theorem Manifold.Orientation.isCoveredByDiffeomorphisms_degreeAtRegularValue
    (oM : Manifold.Orientation 𝓘(ℝ, F) M (Fin (n + 1)))
    (oP : Manifold.Orientation I P (Fin (n + 1)))
    (φ : C(P, M ≃ₘ^k⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ M)) {x₀ y : M}
    (hy : IsRegularValue I 𝓘(ℝ, F) (fun p ↦ φ p x₀) y) :
    (oM.toHomologicalOrientation hF).IsCoveredByDiffeomorphisms hF k x₀
      (degreeAtRegularValue oP oM (fun p ↦ φ p x₀) y) := by
  let L : E ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq (oP.card_eq.symm.trans oM.card_eq)
  have heval : ⇑((Diffeomorph.evalAt x₀).comp φ) = fun p ↦ φ p x₀ := by
    ext p
    simp
  have hy' : IsRegularValue (I.transContinuousLinearEquiv L) 𝓘(ℝ, F)
      ((Diffeomorph.evalAt x₀).comp φ) y := by
    rwa [isRegularValue_transContinuousLinearEquiv_left_iff, heval]
  refine .of_mapFundamentalClass
    (((oP.transContinuousLinearEquiv L).toBoundarylessModel).toHomologicalOrientation hF) hF
    (φ.comp (BoundarylessModel.homeomorph (I.transContinuousLinearEquiv L) P).symm) ?_
  rw [← ContinuousMap.comp_assoc, HomologicalOrientation.mapFundamentalClass_id,
    Manifold.Orientation.mapFundamentalClass_toBoundarylessModel_eq_degreeAtRegularValue_smul
      hF (oP.transContinuousLinearEquiv L) oM hy',
    degreeAtRegularValue_transContinuousLinearEquiv, heval]
  rfl

/-- **Orientation- and basepoint-independent covering from a regular value.** On a preconnected
compact manifold `M`, if `y` is a regular value of `p ↦ φ p x₀`, then for every homological
orientation `o` of `M` and every base point `x : M`, `M` is
`degreeAtRegularValue oP oM (fun p ↦ φ p x₀) y`-covered by `C^k` diffeomorphisms at `x`. -/
theorem HomologicalOrientation.isCoveredByDiffeomorphisms_degreeAtRegularValue
    (o : HomologicalOrientation M F (n + 1))
    (oP : Manifold.Orientation I P (Fin (n + 1)))
    (oM : Manifold.Orientation 𝓘(ℝ, F) M (Fin (n + 1)))
    (φ : C(P, M ≃ₘ^k⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ M)) {x₀ y : M}
    (hy : IsRegularValue I 𝓘(ℝ, F) (fun p ↦ φ p x₀) y) (x : M) :
    o.IsCoveredByDiffeomorphisms hF k x (degreeAtRegularValue oP oM (fun p ↦ φ p x₀) y) :=
  ((oM.toHomologicalOrientation hF).isCoveredByDiffeomorphisms_iff_of_preconnectedSpace o x₀ x).1
    (oM.isCoveredByDiffeomorphisms_degreeAtRegularValue hF k oP φ hy)

/-- **Covering by diffeomorphisms via the smooth mapping degree.** Let `φ : C(P, Diff^k(M))` be a
continuous family of `C^k` diffeomorphisms of `M` parametrized by a compact oriented boundaryless
`C¹` manifold `(P, I, oP)`. For any base point `x₀ : M`, `M` is
`degree oP oM (fun p ↦ φ p x₀)`-covered by `C^k` diffeomorphisms at `x₀`. -/
theorem Manifold.Orientation.isCoveredByDiffeomorphisms_degree
    (oM : Manifold.Orientation 𝓘(ℝ, F) M (Fin (n + 1)))
    (oP : Manifold.Orientation I P (Fin (n + 1)))
    (φ : C(P, M ≃ₘ^k⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ M)) (x₀ : M) :
    (oM.toHomologicalOrientation hF).IsCoveredByDiffeomorphisms hF k x₀
      (TauCeti.degree oP oM fun p ↦ φ p x₀) := by
  by_cases h : ∃ y, IsRegularValue I 𝓘(ℝ, F) (fun p ↦ φ p x₀) y
  · rw [degree_eq_degreeAtRegularValue_choose h]
    exact oM.isCoveredByDiffeomorphisms_degreeAtRegularValue hF k oP φ h.choose_spec
  · rw [degree_eq_zero_of_not_exists h]
    exact (oM.toHomologicalOrientation hF).isCoveredByDiffeomorphisms_zero hF k x₀

/-- **Orientation- and basepoint-independent covering via the smooth mapping degree.** On a
preconnected compact manifold `M`, for every homological orientation `o` of `M` and every base point
`x : M`, `M` is `degree oP oM (fun p ↦ φ p x₀)`-covered by `C^k` diffeomorphisms at `x`. -/
theorem HomologicalOrientation.isCoveredByDiffeomorphisms_degree
    (o : HomologicalOrientation M F (n + 1))
    (oP : Manifold.Orientation I P (Fin (n + 1)))
    (oM : Manifold.Orientation 𝓘(ℝ, F) M (Fin (n + 1)))
    (φ : C(P, M ≃ₘ^k⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ M)) (x₀ x : M) :
    o.IsCoveredByDiffeomorphisms hF k x (TauCeti.degree oP oM fun p ↦ φ p x₀) :=
  ((oM.toHomologicalOrientation hF).isCoveredByDiffeomorphisms_iff_of_preconnectedSpace o x₀ x).1
    (oM.isCoveredByDiffeomorphisms_degree hF k oP φ x₀)

end TauCeti
