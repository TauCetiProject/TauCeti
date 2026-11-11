/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Cohomology
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Wedge

/-!
# Naturality of Dolbeault products

Continuous complex-linear coefficient maps preserve paired wedge products on Dolbeault
cohomology whenever they intertwine the coefficient pairings. Holomorphic pullback itself
preserves these products. Thus products
of classes can be transported in both the manifold and coefficient variables without choosing
representatives.

The constructions use the existing generic smooth forms and native categorical cohomology.
No finite-dimensionality, completeness, compactness or connectedness assumptions are needed.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Sections 1.3 and 2.6.
-/

public noncomputable section

open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure Dolbeault

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedAddCommGroup H] [NormedSpace ℂ H]

section Pullback

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace E' M'] [IsManifold 𝓘(ℂ, E') ∞ M']
  {f : M → M'} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ f)
  (hJ : IsPseudoholomorphic (ofComplexManifold E M) (ofComplexManifold E' M') f)

/-- Holomorphic pullback preserves paired wedges of closed type forms. -/
theorem Dolbeault.closedForms.mpullback_wedgeWith (μ : F →L[ℂ] G →L[ℂ] H) (p q r s : ℕ)
    (φ : closedForms E' M' F p q) (ψ : closedForms E' M' G r s) :
    closedForms.mpullback hf hJ (p + r) (q + s) (closedForms.wedgeWith μ p q r s φ ψ) =
      closedForms.wedgeWith μ p q r s
        (closedForms.mpullback hf hJ p q φ) (closedForms.mpullback hf hJ r s ψ) := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [closedForms.coe_mpullback, closedForms.coe_wedgeWith, coe_wedgeWithType,
    SmoothForm.mpullback_cast, SmoothForm.mpullback_wedgeWith]

/-- Holomorphic pullback preserves the product of Dolbeault classes. -/
theorem dolbeaultCohomology.map_wedgeWith (μ : F →L[ℂ] G →L[ℂ] H) (p q r s : ℕ)
    (a : dolbeaultCohomology E' M' F p q) (b : dolbeaultCohomology E' M' G r s) :
    map hf hJ (p + r) (q + s) (wedgeWith μ p q r s a b) =
      wedgeWith μ p q r s (map hf hJ p q a) (map hf hJ r s b) := by
  obtain ⟨φ, rfl⟩ := dolbeaultCohomology.mk_surjective p q a
  obtain ⟨ψ, rfl⟩ := dolbeaultCohomology.mk_surjective r s b
  simp only [dolbeaultCohomology.wedgeWith_mk, dolbeaultCohomology.map_mk,
    closedForms.mpullback_wedgeWith]

end Pullback

section Pairings

variable {F' G' H' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F']
  [NormedAddCommGroup G'] [NormedSpace ℂ G'] [NormedAddCommGroup H'] [NormedSpace ℂ H']

/-- Intertwining coefficient pairings gives naturality of the product of closed type forms. -/
theorem Dolbeault.closedForms.mapCoeff_wedgeWith
    (μ : F →L[ℂ] G →L[ℂ] H) (ν : F' →L[ℂ] G' →L[ℂ] H')
    (L : F →L[ℂ] F') (K : G →L[ℂ] G') (N : H →L[ℂ] H')
    (h : ∀ a b, N (μ a b) = ν (L a) (K b)) (p q r s : ℕ)
    (φ : closedForms E M F p q) (ψ : closedForms E M G r s) :
    closedForms.mapCoeff N (p + r) (q + s) (closedForms.wedgeWith μ p q r s φ ψ) =
      closedForms.wedgeWith ν p q r s
        (closedForms.mapCoeff L p q φ) (closedForms.mapCoeff K r s ψ) := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [closedForms.coe_mapCoeff, closedForms.coe_wedgeWith, coe_wedgeWithType,
    SmoothForm.mapCoeff_cast]
  rw [SmoothForm.mapCoeff_wedgeWith (μ.bilinearRestrictScalars ℝ)
    (ν.bilinearRestrictScalars ℝ) (L.restrictScalars ℝ) (K.restrictScalars ℝ)
    (N.restrictScalars ℝ) h]

/-- A coefficient change preserving the coefficient pairing preserves Dolbeault products. -/
theorem dolbeaultCohomology.mapCoeff_wedgeWith
    (μ : F →L[ℂ] G →L[ℂ] H) (ν : F' →L[ℂ] G' →L[ℂ] H')
    (L : F →L[ℂ] F') (K : G →L[ℂ] G') (N : H →L[ℂ] H')
    (h : ∀ a b, N (μ a b) = ν (L a) (K b)) (p q r s : ℕ)
    (a : dolbeaultCohomology E M F p q) (b : dolbeaultCohomology E M G r s) :
    mapCoeff N (p + r) (q + s) (wedgeWith μ p q r s a b) =
      wedgeWith ν p q r s (mapCoeff L p q a) (mapCoeff K r s b) := by
  obtain ⟨φ, rfl⟩ := dolbeaultCohomology.mk_surjective p q a
  obtain ⟨ψ, rfl⟩ := dolbeaultCohomology.mk_surjective r s b
  simp only [dolbeaultCohomology.wedgeWith_mk, dolbeaultCohomology.mapCoeff_mk,
    closedForms.mapCoeff_wedgeWith μ ν L K N h]

end Pairings

end TauCeti
