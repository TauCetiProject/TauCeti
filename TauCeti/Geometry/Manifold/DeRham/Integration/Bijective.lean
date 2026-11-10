/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Integration.Connected
import TauCeti.Geometry.Manifold.ContMDiff.Parametrization

/-!
# Top compactly supported cohomology of a connected oriented manifold

On a connected, oriented, boundaryless, Hausdorff, σ-compact smooth manifold `M` of finite
dimension `n`, integration `∫_M : H^n_c(M) → ℝ` is a linear isomorphism
(`TauCeti.compactlySupportedDeRhamCohomology.bijective_integral`), and `H^n_c(M)` is a line.
Integration is injective under the weaker hypothesis that `M` is preconnected, including the
empty manifold. Under this weaker hypothesis, a compactly supported top form is the exterior
derivative of a compactly supported form exactly when its integral vanishes
(`TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero`). This is the base case
of Poincaré duality in the top degree.

Surjectivity holds without connectedness
(`TauCeti.compactlySupportedDeRhamCohomology.surjective_integral`). For injectivity, every point
has an open neighbourhood `U` diffeomorphic to `ℝⁿ`
(`TauCeti.exists_opens_diffeomorph_euclideanSpace`), on which integration `H^n_c(U) → ℝ` is
injective because `H^n_c(ℝⁿ)` is a line
(`TauCeti.compactlySupportedDeRhamCohomology.bijective_integral_of_diffeomorph_normedSpace`).
The connected-cover theorem
(`TauCeti.compactlySupportedDeRhamCohomology.injective_integral_of_cover`) compares normalized
classes on overlapping coordinate domains and uses preconnectedness and a finite decomposition to
prove injectivity. Applying it to the Euclidean coordinate cover of `M` gives the global result.

Preconnectedness cannot be dropped from injectivity: on a disjoint union of two copies of `ℝⁿ`,
`H^n_c` is two-dimensional.

## Main results

* `TauCeti.compactlySupportedDeRhamCohomology.injective_integral`: integration on `H^n_c(M)` is
  injective on a preconnected manifold, including the empty manifold.
* `TauCeti.compactlySupportedDeRhamCohomology.bijective_integral`: integration on `H^n_c(M)` is
  bijective on a connected manifold.
* `TauCeti.compactlySupportedDeRhamCohomologyIntegralEquiv`: integration as a linear isomorphism
  `H^n_c(M) ≃ₗ[ℝ] ℝ` on a connected manifold.
* `TauCeti.finrank_compactlySupportedDeRhamCohomology_top`: `H^n_c(M)` is one-dimensional on a
  connected manifold.
* `TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero`: on a preconnected
  manifold, including the empty manifold, a compactly supported top form has a compactly
  supported primitive exactly when its integral vanishes.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, section Cohomology with
  Compact Support, the integration isomorphism on top compactly supported cohomology.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §5.
-/

public noncomputable section

open Set Function Module TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] {n : ℕ}

namespace compactlySupportedDeRhamCohomology

/-- **The top compactly supported cohomology of a preconnected manifold.** On a preconnected,
oriented, boundaryless, Hausdorff, σ-compact finite-dimensional smooth manifold, integration
`H^n_c(M) → ℝ` is injective. The empty manifold is included. -/
theorem injective_integral [PreconnectedSpace M] (o : Manifold.Orientation I M (Fin n)) :
    Injective (integral o) := by
  classical
  -- Choose a Euclidean coordinate domain about each point, including when `M` is empty.
  have hcoord (x : M) := exists_opens_diffeomorph_euclideanSpace (n := ⊤)
    (BoundarylessManifold.isInteriorPoint (I := I) (x := x))
  choose U hxU Ψ using hcoord
  let Φ (x : M) : E ≃ₘ⟮𝓘(ℝ, E), I⟯ U x :=
    (toEuclidean (E := E)).toDiffeomorph.trans (Ψ x).some.symm
  have (x : M) : SigmaCompactSpace (U x) :=
    (Φ x).toHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  have hcover : (⊤ : Opens M) ≤ iSup U := by
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hxU x⟩
  -- The cover theorem concerns an open subset; identify `⊤` with the ambient manifold.
  let T : (⊤ : Opens M) ≃ₘ⟮I, I⟯ M := Diffeomorph.ofTop ⊤ rfl
  have : SigmaCompactSpace (⊤ : Opens M) := isClosed_univ.sigmaCompactSpace
  have : PreconnectedSpace (⊤ : Opens M) := Subtype.preconnectedSpace isPreconnected_univ
  have hi := injective_integral_of_cover o U (fun _ ↦ le_top) hcover Φ
  intro a b hab
  exact (equivOfDiffeomorph T n).injective
    (hi (by simpa only [T, integral_equivOfDiffeomorph_ofTop] using hab))

/-- **The top compactly supported cohomology of a connected manifold.** On a connected, oriented,
boundaryless, Hausdorff, σ-compact finite-dimensional smooth manifold, integration
`H^n_c(M) → ℝ` is bijective. -/
theorem bijective_integral [ConnectedSpace M] (o : Manifold.Orientation I M (Fin n)) :
    Bijective (integral o) :=
  ⟨injective_integral o, surjective_integral o⟩

end compactlySupportedDeRhamCohomology

/-- **The top compactly supported cohomology of a connected manifold**: integration as a linear
isomorphism `H^n_c(M) ≃ₗ[ℝ] ℝ`, for a connected, oriented, boundaryless, Hausdorff, σ-compact
finite-dimensional smooth manifold. -/
def compactlySupportedDeRhamCohomologyIntegralEquiv [ConnectedSpace M]
    (o : Manifold.Orientation I M (Fin n)) :
    compactlySupportedDeRhamCohomology I M n ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective _ (compactlySupportedDeRhamCohomology.bijective_integral o)

/-- The isomorphism `H^n_c(M) ≃ₗ[ℝ] ℝ` is integration. -/
@[simp]
theorem compactlySupportedDeRhamCohomologyIntegralEquiv_apply [ConnectedSpace M]
    (o : Manifold.Orientation I M (Fin n)) (x : compactlySupportedDeRhamCohomology I M n) :
    compactlySupportedDeRhamCohomologyIntegralEquiv o x =
      compactlySupportedDeRhamCohomology.integral o x :=
  LinearEquiv.ofBijective_apply _ _

/-- The inverse integration isomorphism constructs a class with the prescribed integral. -/
@[simp]
theorem integral_compactlySupportedDeRhamCohomologyIntegralEquiv_symm [ConnectedSpace M]
    (o : Manifold.Orientation I M (Fin n)) (c : ℝ) :
    compactlySupportedDeRhamCohomology.integral o
      ((compactlySupportedDeRhamCohomologyIntegralEquiv o).symm c) = c :=
  (compactlySupportedDeRhamCohomologyIntegralEquiv o).apply_symm_apply c

/-- Applying the inverse integration isomorphism to a class's integral recovers the class. -/
@[simp]
theorem compactlySupportedDeRhamCohomologyIntegralEquiv_symm_integral [ConnectedSpace M]
    (o : Manifold.Orientation I M (Fin n)) (c : compactlySupportedDeRhamCohomology I M n) :
    (compactlySupportedDeRhamCohomologyIntegralEquiv o).symm
      (compactlySupportedDeRhamCohomology.integral o c) = c :=
  (compactlySupportedDeRhamCohomologyIntegralEquiv o).symm_apply_apply c

/-- On a connected, oriented, boundaryless, Hausdorff, σ-compact finite-dimensional smooth manifold
of dimension `n`, the top compactly supported cohomology `H^n_c(M)` is one-dimensional. -/
theorem finrank_compactlySupportedDeRhamCohomology_top [ConnectedSpace M]
    (o : Manifold.Orientation I M (Fin n)) :
    finrank ℝ (compactlySupportedDeRhamCohomology I M n) = 1 :=
  (compactlySupportedDeRhamCohomologyIntegralEquiv o).finrank_eq.trans (finrank_self ℝ)

/-- **The compactly supported Poincaré lemma in top degree, on a preconnected manifold.** On a
preconnected, oriented, boundaryless, Hausdorff, σ-compact finite-dimensional smooth manifold of
dimension `n`, a compactly supported smooth `n`-form is the exterior derivative of a compactly
supported form if and only if its integral vanishes. The empty manifold is included; in degree
zero, exactness means that the form is zero. -/
theorem mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero [PreconnectedSpace M]
    (o : Manifold.Orientation I M (Fin n)) {φ : SmoothForm I M ℝ n}
    (hφ : φ ∈ compactlySupportedForms I M n) :
    φ ∈ exactCompactlySupportedForms I M n ↔ integralTopForm o φ.1 = 0 := by
  refine ⟨integralTopForm_eq_zero_of_mem_exactCompactlySupportedForms o, fun h ↦ ?_⟩
  let ψ : compactlySupportedClosedForms I M n :=
    ⟨φ, (mem_compactlySupportedClosedForms I).mpr
      ⟨hφ, mem_closedForms_of_finrank_le I (by simpa using o.card_eq.ge) φ⟩⟩
  refine (compactlySupportedDeRhamCohomology.mk_eq_zero_iff I n ψ).mp
    ((injective_iff_map_eq_zero _).mp
      (compactlySupportedDeRhamCohomology.injective_integral o) _ ?_)
  rw [compactlySupportedDeRhamCohomology.integral_mk]
  exact h

end TauCeti
