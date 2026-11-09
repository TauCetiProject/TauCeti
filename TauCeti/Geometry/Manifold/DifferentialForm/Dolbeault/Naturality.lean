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

Continuous complex-linear coefficient maps induce maps on Dolbeault cohomology. They
commute with holomorphic pullback and preserve paired wedge products whenever they intertwine
the coefficient pairings. Holomorphic pullback itself preserves these products. Thus products
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

namespace Dolbeault.closedForms

/-- Applying a continuous complex-linear map to the coefficients of a closed type form. -/
def mapCoeff (L : F →L[ℂ] G) (p q : ℕ) :
    closedForms E M F p q →ₗ[ℂ] closedForms E M G p q where
  toFun φ := ⟨⟨SmoothForm.mapCoeff (L.restrictScalars ℝ) φ.1.1,
    ((ofComplexManifold E M).mem_typeForms p q _).2
      ((((ofComplexManifold E M).mem_typeForms p q _).1 φ.1.2).mapCoeff
        (fun _ _ ↦ L.map_smul _ _))⟩, by
      rw [mem_closedForms, ← mapCoeff_delBar _ (fun _ _ ↦ L.map_smul _ _),
        (mem_closedForms p q φ.1).1 φ.2, map_zero]⟩
  map_add' _ _ := Subtype.ext <| Subtype.ext <| map_add _ _ _
  map_smul' c φ := Subtype.ext <| Subtype.ext <|
    SmoothForm.mapCoeff_smul_of_map_smul _ (fun _ ↦ L.map_smul c _) φ.1.1

/-- The underlying smooth form is obtained by applying the coefficient map pointwise. -/
@[simp]
theorem coe_mapCoeff (L : F →L[ℂ] G) (p q : ℕ) (φ : closedForms E M F p q) :
    (mapCoeff L p q φ).1.1 = SmoothForm.mapCoeff (L.restrictScalars ℝ) φ.1.1 := (rfl)

/-- The identity coefficient map fixes closed forms. -/
@[simp]
theorem mapCoeff_id (p q : ℕ) :
    mapCoeff (E := E) (M := M) (ContinuousLinearMap.id ℂ F) p q = LinearMap.id := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  apply Subtype.ext
  exact LinearMap.congr_fun SmoothForm.mapCoeff_id φ.1.1

/-- Coefficient changes on closed forms respect composition. -/
theorem mapCoeff_comp (L : F →L[ℂ] G) (K : G →L[ℂ] H) (p q : ℕ) :
    mapCoeff (E := E) (M := M) (K.comp L) p q =
      (mapCoeff K p q).comp (mapCoeff L p q) := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  apply Subtype.ext
  exact LinearMap.congr_fun
    (SmoothForm.mapCoeff_comp (K.restrictScalars ℝ) (L.restrictScalars ℝ)) φ.1.1

/-- Coefficient maps carry exact type forms to exact type forms. -/
theorem mapCoeff_mem_exactForms (L : F →L[ℂ] G) (p q : ℕ)
    (φ : closedForms E M F p q) (hφ : φ.1 ∈ exactForms E M F p q) :
    (mapCoeff L p q φ).1 ∈ exactForms E M G p q := by
  cases q with
  | zero =>
    have hzero : φ.1 = 0 := by simpa using hφ
    have hφzero : φ = 0 := Subtype.ext hzero
    rw [hφzero, map_zero, Submodule.coe_zero]
    exact zero_mem _
  | succ q =>
    obtain ⟨ψ, hψ⟩ := (mem_exactForms_succ p q φ.1).1 hφ
    refine (mem_exactForms_succ p q _).2 ⟨⟨SmoothForm.mapCoeff (L.restrictScalars ℝ) ψ.1,
      ((ofComplexManifold E M).mem_typeForms p q _).2
        ((((ofComplexManifold E M).mem_typeForms p q _).1 ψ.2).mapCoeff
          (fun _ _ ↦ L.map_smul _ _))⟩, ?_⟩
    rw [← mapCoeff_delBar _ (fun _ _ ↦ L.map_smul _ _), hψ, coe_mapCoeff]

end Dolbeault.closedForms

namespace dolbeaultCohomology

/-- The complex-linear map on Dolbeault cohomology induced by a continuous complex-linear
coefficient map. -/
def mapCoeff (L : F →L[ℂ] G) (p q : ℕ) :
    dolbeaultCohomology E M F p q →ₗ[ℂ] dolbeaultCohomology E M G p q :=
  LinearMap.liftOfSurjective (f := mk (E := E) (M := M) (F := F) p q)
    (mk_surjective p q) ⟨(mk p q).comp (closedForms.mapCoeff L p q), by
      intro φ hφ
      rw [LinearMap.mem_ker, LinearMap.comp_apply, mk_eq_zero_iff]
      exact closedForms.mapCoeff_mem_exactForms L p q φ ((mk_eq_zero_iff p q φ).1 hφ)⟩

/-- On a closed representative, the induced coefficient map is its pointwise coefficient map. -/
@[simp]
theorem mapCoeff_mk (L : F →L[ℂ] G) (p q : ℕ) (φ : closedForms E M F p q) :
    mapCoeff L p q (mk p q φ) = mk p q (closedForms.mapCoeff L p q φ) :=
  LinearMap.equivOfSurjective_apply _ _

/-- The identity coefficient map induces the identity on cohomology. -/
@[simp]
theorem mapCoeff_id (p q : ℕ) :
    mapCoeff (E := E) (M := M) (ContinuousLinearMap.id ℂ F) p q = LinearMap.id := by
  apply LinearMap.ext
  intro c
  obtain ⟨φ, rfl⟩ := mk_surjective p q c
  rw [mapCoeff_mk, closedForms.mapCoeff_id, LinearMap.id_apply, LinearMap.id_apply]

/-- Successive coefficient changes induce the coefficient change of the composite. -/
theorem mapCoeff_comp (L : F →L[ℂ] G) (K : G →L[ℂ] H) (p q : ℕ) :
    mapCoeff (E := E) (M := M) (K.comp L) p q =
      (mapCoeff K p q).comp (mapCoeff L p q) := by
  apply LinearMap.ext
  intro c
  obtain ⟨φ, rfl⟩ := mk_surjective p q c
  simp only [LinearMap.comp_apply, mapCoeff_mk, closedForms.mapCoeff_comp]

end dolbeaultCohomology

section Pullback

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace E' M'] [IsManifold 𝓘(ℂ, E') ∞ M']
  {f : M → M'} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ f)
  (hJ : IsPseudoholomorphic (ofComplexManifold E M) (ofComplexManifold E' M') f)

/-- Coefficient change commutes with holomorphic pullback on Dolbeault cohomology. -/
theorem dolbeaultCohomology.map_mapCoeff (L : F →L[ℂ] G) (p q : ℕ)
    (c : dolbeaultCohomology E' M' F p q) :
    map hf hJ p q (mapCoeff L p q c) = mapCoeff L p q (map hf hJ p q c) := by
  obtain ⟨φ, rfl⟩ := dolbeaultCohomology.mk_surjective p q c
  simp only [dolbeaultCohomology.mapCoeff_mk, dolbeaultCohomology.map_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  simp only [closedForms.coe_mpullback, closedForms.coe_mapCoeff]
  exact SmoothForm.mpullback_mapCoeff (L.restrictScalars ℝ) f hf φ.1.1

/-- Holomorphic pullback preserves paired wedges of closed type forms. -/
theorem Dolbeault.closedForms.mpullback_wedgeWith (μ : F →L[ℂ] G →L[ℂ] H) (p q r s : ℕ)
    (φ : closedForms E' M' F p q) (ψ : closedForms E' M' G r s) :
    closedForms.mpullback hf hJ (p + r) (q + s) (closedForms.wedgeWith μ p q r s φ ψ) =
      closedForms.wedgeWith μ p q r s
        (closedForms.mpullback hf hJ p q φ) (closedForms.mpullback hf hJ r s ψ) := by
  apply Subtype.ext
  apply Subtype.ext
  ext x v
  simp only [closedForms.coe_mpullback, closedForms.coe_wedgeWith, coe_wedgeWithType,
    SmoothForm.coe_mpullback, mpullback_apply, SmoothForm.cast_apply]
  have h := congrArg (fun α ↦ α.1 x (v ∘ Fin.cast (by omega)))
    (SmoothForm.mpullback_wedgeWith (μ.bilinearRestrictScalars ℝ) f hf φ.1.1 ψ.1.1)
  rw [SmoothForm.mpullback_apply] at h
  exact h

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
  ext x v
  simp only [closedForms.coe_mapCoeff, closedForms.coe_wedgeWith, coe_wedgeWithType,
    SmoothForm.coe_mapCoeff, RoughForm.mapCoeff_apply, SmoothForm.cast_apply]
  have heq := congrArg (fun α ↦ α.1 x (v ∘ Fin.cast (by omega)))
    (SmoothForm.mapCoeff_wedgeWith (μ.bilinearRestrictScalars ℝ)
      (ν.bilinearRestrictScalars ℝ) (L.restrictScalars ℝ) (K.restrictScalars ℝ)
      (N.restrictScalars ℝ) h φ.1.1 ψ.1.1)
  rw [SmoothForm.coe_mapCoeff, RoughForm.mapCoeff_apply] at heq
  exact heq

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
