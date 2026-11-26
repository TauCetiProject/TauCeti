/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology.PrincipalParts

/-!
# The Mittag-Leffler connecting map

Let `X` be a compact Hausdorff Riemann surface and `D` a divisor on `X`. This file constructs the
**Mittag-Leffler connecting map** `PrincipalParts D → H¹(X, 𝒪_D)`, which sends a Mittag-Leffler
distribution relative to `D` to its obstruction to being the family of principal parts of a
meromorphic function (Forster, §17).

The finite-level connecting maps `principalPartsConnecting (h : D ≤ E)` of the principal-parts
sequences `0 → 𝒪_D → 𝒪_E → 𝒫_{D,E} → 0` are defined on the families of principal parts with
poles bounded by `E`. A Mittag-Leffler distribution `μ` has a *least bounding divisor*
`PrincipalParts.boundingDivisor μ ≥ D`, whose coefficient at `x` is the least pole bound
`LocalPrincipalPart.poleBound D (μ x)` of the local principal part `μ x`. The connecting map is
defined as the finite-level connecting map at this divisor. It is computed by the finite-level
connecting map at every bounding divisor (`mittagLefflerConnecting_eq`), by naturality of the
Čech connecting map along the morphisms of principal-parts sequences
(`principalPartsConnecting_naturality`). No colimit over divisors and no choice of a bounding
divisor are involved.

## Main declarations

* `TauCeti.RiemannSurface.mittagLefflerConnecting`: the connecting map
  `PrincipalParts D →ₗ[ℂ] H¹(X, 𝒪_D)`, with `mittagLefflerConnecting_eq`.
* `TauCeti.RiemannSurface.exact_principalParts_mittagLefflerConnecting`: on a connected surface,
  `𝓜(X) → PrincipalParts D → H¹(X, 𝒪_D)` is exact.
* `TauCeti.RiemannSurface.range_mittagLefflerConnecting`: the image is the union of the kernels of
  the maps `H¹(𝒪_D) → H¹(𝒪_E)` for `D ≤ E`.
* `TauCeti.RiemannSurface.mittagLefflerConnecting_mapOfLE`: naturality in the divisor, and
  `mittagLefflerConnecting_mapOfLE_add_ofPoint`: its form for a point twist `D ≤ D + x`.

Forster's Theorem 17.3, the surjectivity of the connecting map, is
`TauCeti.RiemannSurface.mittagLefflerConnecting_surjective` in
`Divisor/Cohomology/Vanishing.lean`: it needs the vanishing of `H¹(X, 𝒪_E)` for large `E`.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §§16-17.
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open TauCeti.Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

section Cohomology

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X]
  [T2Space X] {D D' E : WeilDivisor X}

open PrincipalParts

/-- The connecting map of a Mittag-Leffler distribution, before linearity is established. -/
private def mittagLefflerConnectingFun (μ : PrincipalParts D) : divisorCechCohomology D 1 :=
  principalPartsConnecting (le_boundingDivisor μ)
    (toBoundedFamily D _ ⟨μ, mem_boundedBy_boundingDivisor μ⟩)

private theorem mittagLefflerConnectingFun_eq (hDE : D ≤ E) (μ : boundedBy D E) :
    mittagLefflerConnectingFun (μ : PrincipalParts D) =
      principalPartsConnecting hDE (toBoundedFamily D E μ) := by
  obtain ⟨μ, hμ⟩ := μ
  have h := principalPartsConnecting_boundedFamilyMap_refl (le_boundingDivisor μ)
    (boundingDivisor_le hDE hμ) (toBoundedFamily D _ ⟨μ, mem_boundedBy_boundingDivisor μ⟩)
  rw [boundedFamilyMap_toBoundedFamily] at h
  simp only [mapOfLE_refl, LinearMap.id_apply] at h
  exact h.symm

variable (D) in
/-- The **Mittag-Leffler connecting map** `PrincipalParts D → H¹(X, 𝒪_D)`: a Mittag-Leffler
distribution relative to `D` is sent to the connecting obstruction of the principal-parts sequence
of its least bounding divisor. -/
def mittagLefflerConnecting : PrincipalParts D →ₗ[ℂ] divisorCechCohomology D 1 where
  toFun := mittagLefflerConnectingFun
  map_add' μ ν := by
    have hDE : D ≤ boundingDivisor μ ⊔ boundingDivisor ν :=
      (le_boundingDivisor μ).trans le_sup_left
    have hμ := boundedBy_mono (le_sup_left (b := boundingDivisor ν))
      (mem_boundedBy_boundingDivisor μ)
    have hν := boundedBy_mono (le_sup_right (a := boundingDivisor μ))
      (mem_boundedBy_boundingDivisor ν)
    have := mittagLefflerConnectingFun_eq hDE (⟨μ, hμ⟩ + ⟨ν, hν⟩ : boundedBy D _)
    rw [map_add, map_add, ← mittagLefflerConnectingFun_eq hDE ⟨μ, hμ⟩,
      ← mittagLefflerConnectingFun_eq hDE ⟨ν, hν⟩] at this
    exact this
  map_smul' a μ := by
    have hDE := le_boundingDivisor μ
    have hμ := mem_boundedBy_boundingDivisor μ
    have := mittagLefflerConnectingFun_eq hDE (a • ⟨μ, hμ⟩ : boundedBy D _)
    rw [map_smul, map_smul, ← mittagLefflerConnectingFun_eq hDE ⟨μ, hμ⟩] at this
    exact this

/-- The Mittag-Leffler connecting map is computed by the principal-parts connecting map of every
bounding divisor `E ≥ D`. -/
theorem mittagLefflerConnecting_eq (hDE : D ≤ E) (μ : boundedBy D E) :
    mittagLefflerConnecting D μ = principalPartsConnecting hDE (toBoundedFamily D E μ) :=
  mittagLefflerConnectingFun_eq hDE μ

/-- **Naturality of the Mittag-Leffler connecting map** in the divisor: projecting principal parts
to `D' ≥ D` corresponds to the map `H¹(𝒪_D) → H¹(𝒪_{D'})`. -/
theorem mittagLefflerConnecting_mapOfLE (h : D ≤ D') (μ : PrincipalParts D) :
    mittagLefflerConnecting D' (mapOfLE h μ) =
      divisorCechCohomologyMapOfLE h 1 (mittagLefflerConnecting D μ) := by
  have hDE : D ≤ boundingDivisor μ ⊔ D' := (le_boundingDivisor μ).trans le_sup_left
  have hμ : μ ∈ boundedBy D (boundingDivisor μ ⊔ D') :=
    boundedBy_mono le_sup_left (mem_boundedBy_boundingDivisor μ)
  rw [mittagLefflerConnecting_eq hDE ⟨μ, hμ⟩,
    ← principalPartsConnecting_naturality hDE le_sup_right h le_rfl,
    boundedFamilyMap_toBoundedFamily, ← mittagLefflerConnecting_eq]

/-- Linear-map form of `mittagLefflerConnecting_mapOfLE`. -/
theorem mittagLefflerConnecting_comp_mapOfLE (h : D ≤ D') :
    mittagLefflerConnecting D' ∘ₗ mapOfLE h =
      divisorCechCohomologyMapOfLE h 1 ∘ₗ mittagLefflerConnecting D :=
  LinearMap.ext (mittagLefflerConnecting_mapOfLE h)

/-- **Point-twist check.** For the inclusion `D ≤ D + x`, projecting principal parts to `D + x`
corresponds to the point-twist cohomology map `H¹(𝒪_D) → H¹(𝒪_{D+x})`. -/
theorem mittagLefflerConnecting_mapOfLE_add_ofPoint (x : X) (μ : PrincipalParts D) :
    mittagLefflerConnecting (D + WeilDivisor.ofPoint x)
        (mapOfLE (WeilDivisor.le_add_ofPoint D x) μ) =
      pointTwistCohomologyMap D x 1 (mittagLefflerConnecting D μ) := by
  rw [mittagLefflerConnecting_mapOfLE, pointTwistCohomologyMap_eq_divisorCechCohomologyMapOfLE]

/-- The **image of the Mittag-Leffler connecting map** is the union of the kernels of the maps
`H¹(𝒪_D) → H¹(𝒪_E)` for `D ≤ E`: a class is a Mittag-Leffler obstruction exactly when it dies
after allowing enough poles. -/
theorem range_mittagLefflerConnecting (D : WeilDivisor X) :
    LinearMap.range (mittagLefflerConnecting D) =
      ⨆ (E : WeilDivisor X) (h : D ≤ E), LinearMap.ker (divisorCechCohomologyMapOfLE h 1) := by
  apply le_antisymm
  · rintro _ ⟨μ, rfl⟩
    have hDE := le_boundingDivisor μ
    refine Submodule.mem_iSup_of_mem (boundingDivisor μ) <| Submodule.mem_iSup_of_mem hDE ?_
    rw [LinearMap.exact_iff.1 (exact_principalPartsConnecting_cohomologyMap hDE),
      mittagLefflerConnecting_eq hDE ⟨μ, mem_boundedBy_boundingDivisor μ⟩]
    exact LinearMap.mem_range_self _ _
  · refine iSup₂_le fun E hDE ↦ ?_
    rw [LinearMap.exact_iff.1 (exact_principalPartsConnecting_cohomologyMap hDE)]
    rintro _ ⟨c, rfl⟩
    obtain ⟨μ, rfl⟩ := (toBoundedFamily D E).surjective c
    exact mittagLefflerConnecting_eq hDE μ ▸ LinearMap.mem_range_self _ _

section Exactness

variable [ConnectedSpace X]

omit [T2Space X] in
/-- The principal parts of the meromorphic function of a global section of `𝒪_E` are its principal
parts as a section. -/
private theorem principalParts_toMeromorphic (s : (divisorSheaf E).obj.obj (op ⊤)) (x : X) :
    MeromorphicFunction.principalParts D
        (divisorSections.toMeromorphic E (divisorSheafSectionsEquiv E ⊤ s)) x =
      (globalPrincipalParts D E s x : LocalPrincipalPart D x) := by
  rw [MeromorphicFunction.principalParts_apply, coe_globalPrincipalParts_apply,
    MeromorphicFunction.toChartGerm_toMeromorphic]

omit [T2Space X] in
/-- If the principal parts of `f` relative to `D` are bounded by `E ≥ D`, then `f` is a global
section of `𝒪_E` and they are its principal parts as a section. -/
private theorem toBoundedFamily_principalParts_mem_range (hDE : D ≤ E) (f : MeromorphicFunction X)
    (hf : MeromorphicFunction.principalParts D f ∈ boundedBy D E) :
    toBoundedFamily D E ⟨_, hf⟩ ∈ LinearMap.range (globalPrincipalParts D E) := by
  have hker : f ∈ LinearMap.ker (MeromorphicFunction.principalParts E) := by
    rwa [LinearMap.mem_ker, ← MeromorphicFunction.mapOfLE_principalParts hDE, ← LinearMap.mem_ker,
      ← boundedBy_eq_ker_mapOfLE]
  rw [MeromorphicFunction.ker_principalParts] at hker
  obtain ⟨s, hs⟩ := hker
  obtain ⟨t, rfl⟩ := (divisorSheafSectionsEquiv E ⊤).surjective s
  subst hs
  refine ⟨t, funext fun x ↦ Subtype.ext ?_⟩
  rw [coe_toBoundedFamily_apply]
  exact (principalParts_toMeromorphic t x).symm

/-- **Exactness of the Mittag-Leffler sequence at the principal parts.** On a compact connected
Riemann surface, a Mittag-Leffler distribution is the family of principal parts of a meromorphic
function if and only if its Mittag-Leffler obstruction in `H¹(X, 𝒪_D)` vanishes. -/
theorem exact_principalParts_mittagLefflerConnecting (D : WeilDivisor X) :
    Function.Exact (MeromorphicFunction.principalParts D) (mittagLefflerConnecting D) := by
  intro μ
  have hDE := le_boundingDivisor μ
  have hμ := mem_boundedBy_boundingDivisor μ
  rw [mittagLefflerConnecting_eq hDE ⟨μ, hμ⟩, exact_principalParts_connecting hDE]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨divisorSections.toMeromorphic _ (divisorSheafSectionsEquiv _ ⊤ s),
      DFinsupp.ext fun x ↦ ?_⟩
    rw [principalParts_toMeromorphic, hs, coe_toBoundedFamily_apply]
  · rintro ⟨f, rfl⟩
    exact toBoundedFamily_principalParts_mem_range hDE f hμ

/-- The Mittag-Leffler obstruction of the principal parts of a meromorphic function vanishes. -/
@[simp]
theorem mittagLefflerConnecting_principalParts (f : MeromorphicFunction X) :
    mittagLefflerConnecting D (MeromorphicFunction.principalParts D f) = 0 :=
  (exact_principalParts_mittagLefflerConnecting D).apply_apply_eq_zero f

end Exactness

end Cohomology

end TauCeti.RiemannSurface
