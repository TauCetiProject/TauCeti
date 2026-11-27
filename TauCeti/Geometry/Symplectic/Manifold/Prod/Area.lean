/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Global
public import TauCeti.Geometry.Symplectic.Manifold.Prod

/-!
# Areas of surfaces in a product

Let `u : C → S × N` be a smooth map from a compact oriented surface to a product carrying the
product form `pr₁^*σ + pr₂^*τ` (`TauCeti.SmoothTwoForm.prod`). Its area is the sum of the areas
of its two components:

`∫_C u^*(pr₁^*σ + pr₂^*τ) = ∫_C (pr₁ ∘ u)^*σ + ∫_C (pr₂ ∘ u)^*τ`

(`TauCeti.integralTopForm_mpullback_prod`). When `C` is boundaryless and `S` and `N` are connected
oriented boundaryless surfaces, the degree formula computes each term, so

`∫_C u^*(pr₁^*σ + pr₂^*τ) = deg(pr₁ ∘ u) ∫_S σ + deg(pr₂ ∘ u) ∫_N τ`

for compactly supported `σ` and `τ`
(`TauCeti.integralTopForm_mpullback_prod_eq_degree_mul_add_degree_mul`). These formulas give the
areas of spheres in `S × T` for a torus `T`
(`TauCeti.Geometry.Symplectic.Manifold.Torus.SphericalArea`) and in `S² × S²`
(`TauCeti.Geometry.Symplectic.Manifold.Sphere.ProductCurve`).

## Main results

* `TauCeti.integralTopForm_mpullback_prod`: the area of a map to a product is the sum of the areas
  of its components.
* `TauCeti.integralTopForm_mpullback_prod_eq_degree_mul_add_degree_mul`: the area of a map to a
  product of two surfaces is `deg(pr₁ ∘ u) ∫_S σ + deg(pr₂ ∘ u) ∫_N τ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Sections 9.3 and 9.4.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace C] [ChartedSpace H C]
  [IsManifold I ∞ C] [CompactSpace C]

section Prod

variable {E' H' S F H'' N : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ F H''} [TopologicalSpace N] [ChartedSpace H'' N] [IsManifold K ∞ N]

/-- **The area of a map to a product is the sum of the areas of its components.** For a smooth
map `u : C → S × N` from a compact oriented surface and two-forms `σ` on `S` and `τ` on `N`,
`∫_C u^*(pr₁^*σ + pr₂^*τ) = ∫_C (pr₁ ∘ u)^*σ + ∫_C (pr₂ ∘ u)^*τ`. -/
theorem integralTopForm_mpullback_prod (o : Manifold.Orientation I C (Fin 2))
    (σ : SmoothTwoForm J S) (τ : SmoothTwoForm K N) {u : C → S × N}
    (hu : ContMDiff I (J.prod K) ∞ u) :
    integralTopForm o (SmoothForm.mpullback u hu (σ.prod τ)).val =
      integralTopForm o (SmoothForm.mpullback (Prod.fst ∘ u) (contMDiff_fst.comp hu) σ).val +
        integralTopForm o (SmoothForm.mpullback (Prod.snd ∘ u) (contMDiff_snd.comp hu) τ).val := by
  rw [SmoothTwoForm.prod_def, map_add, SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_mpullback, SmoothForm.add_toRoughForm]
  exact integralTopForm_add_of_compactSpace o ((SmoothForm.isSmoothForm _).of_le (by simp))
    ((SmoothForm.isSmoothForm _).of_le (by simp))

end Prod

section Surface

variable [BoundarylessManifold I C] [T2Space C]
  {E₁ H₁ S : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace H₁] {J : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace S] [ChartedSpace H₁ S]
  [IsManifold J ∞ S] [BoundarylessManifold J S] [T2Space S] [SigmaCompactSpace S]
  [ConnectedSpace S]
  {E₂ H₂ N : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace H₂] {K : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace N] [ChartedSpace H₂ N]
  [IsManifold K ∞ N] [BoundarylessManifold K N] [T2Space N] [SigmaCompactSpace N]
  [ConnectedSpace N]

/-- **The area of a surface in a product of two surfaces.** For a smooth map `u : C → S × N` from
a compact oriented boundaryless surface to a product of two connected oriented boundaryless
surfaces, and compactly supported two-forms `σ` on `S` and `τ` on `N`,
`∫_C u^*(pr₁^*σ + pr₂^*τ) = deg(pr₁ ∘ u) ∫_S σ + deg(pr₂ ∘ u) ∫_N τ`. -/
theorem integralTopForm_mpullback_prod_eq_degree_mul_add_degree_mul
    (o : Manifold.Orientation I C (Fin 2)) (o₁ : Manifold.Orientation J S (Fin 2))
    (o₂ : Manifold.Orientation K N (Fin 2)) {σ : SmoothTwoForm J S} {τ : SmoothTwoForm K N}
    (hσ : IsCompact (_root_.tsupport (α := E₁ [⋀^Fin 2]→L[ℝ] ℝ) σ.val))
    (hτ : IsCompact (_root_.tsupport (α := E₂ [⋀^Fin 2]→L[ℝ] ℝ) τ.val))
    {u : C → S × N} (hu : ContMDiff I (J.prod K) ∞ u) :
    integralTopForm o (SmoothForm.mpullback u hu (σ.prod τ)).val =
      degree o o₁ (Prod.fst ∘ u) * integralTopForm o₁ σ.val +
        degree o o₂ (Prod.snd ∘ u) * integralTopForm o₂ τ.val := by
  rw [integralTopForm_mpullback_prod, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback]
  congr 1
  · exact integralTopForm_mpullback_eq_degree_mul o o₁ (contMDiff_fst.comp hu)
      (contMDiff_fst.comp hu).continuous.isProperMap (SmoothForm.isSmoothForm _) hσ
  · exact integralTopForm_mpullback_eq_degree_mul o o₂ (contMDiff_snd.comp hu)
      (contMDiff_snd.comp hu).continuous.isProperMap (SmoothForm.isSmoothForm _) hτ

end Surface

end TauCeti
